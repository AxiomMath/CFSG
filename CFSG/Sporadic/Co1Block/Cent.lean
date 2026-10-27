
module

public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Sporadic.Schreier.Co1Chain
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public noncomputable section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative Matrix

@[expose] def brayDagG (t : GL24) (d₁ : List (List ℤ)) : List GL24 := dagG [A₁, A₂, t] d₁

@[expose] def brayEltsG (t : GL24) (d₁ : List (List ℤ)) (bidx : List ℕ) : List GL24 :=
  bidx.map fun j => (brayDagG t d₁).getD (j - 1) 1

@[expose] def brayE (t : GL24) (d₁ : List (List ℤ)) (bidx : List ℕ) : Subgroup GL24 :=
  Subgroup.closure {g | g ∈ brayEltsG t d₁ bidx}

@[expose] def strongDagG (t : GL24) (d₁ : List (List ℤ)) (bidx : List ℕ)
    (d₂ : List (List ℤ)) : List GL24 :=
  dagG (brayEltsG t d₁ bidx) d₂

@[expose] def valHom : GL24 →* Matrix (Fin 24) (Fin 24) (ZMod 2) := Units.coeHom _

theorem valHom_injective : Function.Injective valHom := Units.val_injective

variable {tR : Native.Rows} {t : GL24} {d₁ d₂ : List (List ℤ)} {bidx : List ℕ}
  {base : List ℕ} {gens : List (List ℕ)} {sizes : List ℕ}

theorem centCheck_parts
    (h : Native.centCheckOf tR d₁ bidx d₂ base gens sizes = true) :
    (Native.brayRows tR d₁).2.2 = true ∧
    (CFSG.Sporadic.Co1Schreier.Native.dag (Native.brayElts (Native.brayRows tR d₁) bidx) d₂).2.2 =
      true ∧
    (∀ j ∈ bidx, 3 < j ∧ j ≤ (Native.brayRows tR d₁).1.length) ∧
    (∀ g ∈ Native.brayElts (Native.brayRows tR d₁) bidx,
      CFSG.Sporadic.Co1Schreier.Native.mul g tR = CFSG.Sporadic.Co1Schreier.Native.mul tR g) ∧
    CFSG.Sporadic.Co1Schreier.Native.vTowerOK
      ((CFSG.Sporadic.Co1Schreier.Native.dag (Native.brayElts (Native.brayRows tR d₁) bidx)
        d₂).1.toArray.map (transposeRows 24)) base gens sizes = true := by
  simp only [Native.centCheckOf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rep_brayDag
    (ht : MRep tR t) (h : (Native.brayRows tR d₁).2.2 = true) :
    List.Forall₂ MRep (Native.brayRows tR d₁).1 (brayDagG t d₁) :=
  dag_rep (.cons rep_A₁ (.cons rep_A₂ (.cons ht .nil))) d₁ h

theorem forall₂_map_getD {P : Native.Rows → GL24 → Prop} {rs : List Native.Rows} {gs : List GL24}
    (h : List.Forall₂ P rs gs) (hd : P CFSG.Sporadic.Co1Schreier.Native.one 1) :
    ∀ idx : List ℕ, List.Forall₂ P
      (idx.map fun j => rs.getD (j - 1) CFSG.Sporadic.Co1Schreier.Native.one)
      (idx.map fun j => gs.getD (j - 1) 1)
  | [] => .nil
  | j :: idx => .cons (getD_rep h hd (j - 1)) (forall₂_map_getD h hd idx)

theorem rep_brayElts
    (ht : MRep tR t) (h : (Native.brayRows tR d₁).2.2 = true) :
    List.Forall₂ MRep (Native.brayElts (Native.brayRows tR d₁) bidx) (brayEltsG t d₁ bidx) :=
  forall₂_map_getD (rep_brayDag ht h) MRep.one bidx

theorem brayDag_mem_GA (htG : t ∈ GA) : ∀ g ∈ brayDagG t d₁, g ∈ GA := by
  refine dagG_mem (fun g hg => ?_) d₁
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h <;> rw [h]
  exacts [A₁_mem, A₂_mem, htG]

theorem brayElts_mem_GA (htG : t ∈ GA) : ∀ g ∈ brayEltsG t d₁ bidx, g ∈ GA := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
  exact getD_mem_of_forall (brayDag_mem_GA htG) _

theorem forall₂_mem_left {P : Native.Rows → GL24 → Prop} {rs : List Native.Rows} {gs : List GL24}
    (h : List.Forall₂ P rs gs) {g : GL24} (hg : g ∈ gs) : ∃ r ∈ rs, P r g := by
  induction h with
  | nil => simp at hg
  | cons hab _ ih =>
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨r, hr, hP⟩ := ih hg
      exact ⟨r, List.mem_cons_of_mem _ hr, hP⟩

theorem brayElts_comm (ht : MRep tR t)
    (h : Native.centCheckOf tR d₁ bidx d₂ base gens sizes = true) :
    ∀ g ∈ brayEltsG t d₁ bidx, g * t = t * g := by
  obtain ⟨h1, -, -, h4, -⟩ := centCheck_parts h
  intro g hg
  obtain ⟨r, hr, hrg⟩ := forall₂_mem_left (rep_brayElts ht h1) hg
  have e := h4 r hr
  exact (hrg.mul ht).eq (e ▸ ht.mul hrg)

theorem brayE_le (ht : MRep tR t) (htG : t ∈ GA)
    (h : Native.centCheckOf tR d₁ bidx d₂ base gens sizes = true) :
    brayE t d₁ bidx ≤ GA ⊓ Subgroup.centralizer {t} := by
  rw [brayE, Subgroup.closure_le]
  intro g hg
  exact Subgroup.mem_inf.2 ⟨brayElts_mem_GA htG g hg,
    Subgroup.mem_centralizer_singleton_iff.2 (brayElts_comm ht h g hg)⟩

theorem strongDag_mem : ∀ g ∈ strongDagG t d₁ bidx d₂, g ∈ brayE t d₁ bidx :=
  dagG_mem (fun _ hg => Subgroup.subset_closure hg) d₂

theorem rep_strongDag (ht : MRep tR t)
    (h : Native.centCheckOf tR d₁ bidx d₂ base gens sizes = true) :
    List.Forall₂ MRep
      (CFSG.Sporadic.Co1Schreier.Native.dag (Native.brayElts (Native.brayRows tR d₁) bidx) d₂).1
      (strongDagG t d₁ bidx d₂) := by
  obtain ⟨h1, h2, -⟩ := centCheck_parts h
  exact dag_rep (rep_brayElts ht h1) d₂ h2

theorem forall₂_length {P : Native.Rows → GL24 → Prop} {rs : List Native.Rows} {gs : List GL24}
    (h : List.Forall₂ P rs gs) : rs.length = gs.length := h.length_eq

theorem card_brayE_ge (ht : MRep tR t)
    (h : Native.centCheckOf tR d₁ bidx d₂ base gens sizes = true) :
    ∏ i ∈ Finset.range base.length, sizes.getD i 0 ≤ Nat.card (brayE t d₁ bidx) := by
  obtain ⟨-, -, -, -, h5⟩ := centCheck_parts h
  have hrep := rep_strongDag ht h
  set R := (CFSG.Sporadic.Co1Schreier.Native.dag
    (Native.brayElts (Native.brayRows tR d₁) bidx) d₂).1
  have hsize : (R.toArray.map (transposeRows 24)).size = R.length := by simp
  refine card_ge_of_towerOK (L := fun j => (strongDagG t d₁ bidx d₂).getD j 1)
    (fun j _ => getD_mem_of_forall strongDag_mem j) (fun j hj => ?_) h5
  rw [hsize] at hj
  have e : (R.toArray.map (transposeRows 24)).getD j #[] = transposeRows 24 (R.getD j
      CFSG.Sporadic.Co1Schreier.Native.one) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, List.getD_eq_getElem _ _ hj]
  rw [e]
  exact MRep.actsBy (getD_rep hrep MRep.one j)

end CFSG.Sporadic.Co1Block
