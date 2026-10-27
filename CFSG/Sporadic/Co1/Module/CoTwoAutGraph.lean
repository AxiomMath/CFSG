module

public import CFSG.Sporadic.Co1.Module.CoTwoAutOrbit
public import CFSG.Sporadic.Co2Rank3.AutBound
public import CFSG.Sporadic.Co1.Module.CoTwoAutGraphLit
public import Certificates.Certificate10065
public meta import CFSG.Sporadic.Co2Rank3.Check
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import Certificates.Data.CFSGNative.Co1.CoTwoAutData
public meta import Certificates.Data.CFSGNative.Co1.CoTwoAutOrbit

public section

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.CoTwoAutNative CFSG.Sporadic.Co1.Module.CoTwo
  CFSG.Sporadic.Co2Rank3 Matrix

@[expose, irreducible] noncomputable def vtx (i : Fin 2300) : Vec24 := toVecD 24 (vtxK i.val)

theorem vtx_def (i : Fin 2300) : vtx i = toVecD 24 (vtxK i.val) := by
  unfold vtx
  rfl

theorem vtx_mem_cls_three
    (i : Fin 2300) : vtx i ∈ Pairs.cls 3 := by
  obtain ⟨W, hW⟩ := Certificates.certificate10065
  obtain ⟨hlt, hin, hin'⟩ := lit_vert hW i.val i.isLt
  have e : v₂ + vtx i = toVecD 24 (vtxK i.val ^^^ 2) := by
    rw [vtx_def, toVecD_xor, toVecD_v₂, add_comm]
  constructor
  · show vtx i ∈ MulAction.orbit NativeSporadic.Co1 v₂
    rw [vtx_def, Pairs.orbit_Co1_eq]
    exact (Pairs.inPts_iff _ hlt).1 hin
  · show v₂ + vtx i ∈ MulAction.orbit NativeSporadic.Co1 v₂
    rw [e, Pairs.orbit_Co1_eq]
    exact (Pairs.inPts_iff _ (Nat.xor_lt_two_pow hlt (by norm_num))).1 hin'

theorem vtx_add_ne
    {i j : Fin 2300} (h : i ≠ j) : vtx i + vtx j ≠ 0 ∧ vtx i + vtx j ≠ v₂ := by
  obtain ⟨W, hW⟩ := Certificates.certificate10065
  have key : ∀ a b : Fin 2300, b.val < a.val → vtx a + vtx b ≠ 0 ∧ vtx a + vtx b ≠ v₂ := by
    intro a b hab
    obtain ⟨hne0, hne2⟩ := lit_dist hW a.val a.isLt b.val hab
    obtain ⟨hlta, -, -⟩ := lit_vert hW a.val a.isLt
    obtain ⟨hltb, -, -⟩ := lit_vert hW b.val b.isLt
    have hx : vtxK a.val ^^^ vtxK b.val < 2 ^ 24 := Nat.xor_lt_two_pow hlta hltb
    have e : vtx a + vtx b = toVecD 24 (vtxK a.val ^^^ vtxK b.val) := by
      rw [vtx_def, vtx_def, toVecD_xor]
    refine ⟨fun h0 => hne0 ?_, fun h2 => hne2 ?_⟩
    · rw [e] at h0
      exact toVecD_injective hx (by norm_num) (h0.trans (toVecD_zero 24).symm)
    · rw [e, ← toVecD_v₂] at h2
      exact toVecD_injective hx (by norm_num) h2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
  · rw [add_comm]
    exact key j i hlt
  · exact key i j hlt

theorem vtx_injective : Function.Injective vtx := by
  intro i j h
  by_contra hij
  exact (vtx_add_ne hij).1 (by rw [h, vec_add_self])

theorem vtx_add_ne_v₂ (i j : Fin 2300) : vtx i + vtx j ≠ v₂ := by
  intro h
  by_cases hij : i = j
  · subst hij
    rw [vec_add_self] at h
    exact v₂_ne_zero h.symm
  · exact (vtx_add_ne hij).2 h

theorem mem_cls_one_iff {y : Vec24} :
    y ∈ Pairs.cls 1 ↔ y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      v₂ + y ∈ MulAction.orbit NativeSporadic.Co1 v₄ := Iff.rfl

theorem mem_cls_three_iff {y : Vec24} :
    y ∈ Pairs.cls 3 ↔ y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      v₂ + y ∈ MulAction.orbit NativeSporadic.Co1 v₂ := Iff.rfl

theorem adj_iff_vtx_add_mem
    (i j : Fin 2300) :
    co2Graph.Adj i j ↔ vtx i + vtx j ∈ Tadj := by
  obtain ⟨W, hW⟩ := Certificates.certificate10065
  have e : vtx i + vtx j = toVecD 24 (vtxK i.val) + toVecD 24 (vtxK j.val) := by
    rw [vtx_def, vtx_def]
  rw [e]
  exact lit_adj hW i j

theorem add_v₂_mem_cls_three {ω : Vec24} (hω : ω ∈ Pairs.cls 3) : v₂ + ω ∈ Pairs.cls 3 := by
  obtain ⟨h1, h2⟩ := mem_cls_three_iff.1 hω
  refine mem_cls_three_iff.2 ⟨h2, ?_⟩
  rwa [← add_assoc, vec_add_self, zero_add]

theorem exists_vtx_of_mem_cls_three
    {ω : Vec24} (hω : ω ∈ Pairs.cls 3) :
    ∃ i : Fin 2300, ω = vtx i ∨ ω = v₂ + vtx i := by
  let e : Fin 2300 × Bool → Vec24 := fun p => if p.2 then v₂ + vtx p.1 else vtx p.1
  have hne : ∀ i j : Fin 2300, vtx i + vtx j ≠ v₂ := vtx_add_ne_v₂
  have heq0 : ∀ i j : Fin 2300, vtx i = vtx j → i = j := fun i j h => vtx_injective h
  have hinj : Function.Injective e := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hij
    have hij' : (if b then v₂ + vtx i else vtx i) = (if c then v₂ + vtx j else vtx j) := hij
    cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hij'
    · rw [heq0 i j hij']
    · exfalso
      apply hne i j
      rw [hij', add_assoc, vec_add_self, add_zero]
    · exfalso
      apply hne j i
      rw [← hij', add_assoc, vec_add_self, add_zero]
    · rw [heq0 i j (add_left_cancel hij')]
  have hsub : Set.range e ⊆ Pairs.cls 3 := by
    rintro _ ⟨⟨i, b⟩, rfl⟩
    cases b
    · exact vtx_mem_cls_three i
    · exact add_v₂_mem_cls_three (vtx_mem_cls_three i)
  have hcard : (Pairs.cls 3).ncard ≤ (Set.range e).ncard := by
    have h3 : dat.subSizes[3]! = 4600 := by decide
    rw [Pairs.cls_ncard (by norm_num), h3, ← Set.image_univ,
      Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  have heq : Set.range e = Pairs.cls 3 := Set.eq_of_subset_of_ncard_le hsub hcard
  rw [← heq] at hω
  obtain ⟨⟨i, b⟩, rfl⟩ := hω
  refine ⟨i, ?_⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

end CFSG.Sporadic.Co1.Module.CoTwoAut
