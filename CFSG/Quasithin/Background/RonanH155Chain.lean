module

public import CFSG.Quasithin.Background.RonanH154Base
public import CFSG.Quasithin.Background.HMathieuChain
public import CFSG.Quasithin.Background.RonanH154Vocab
public import CFSG.Quasithin.Background.RonanH155PG2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.RonanH143
  CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154

@[expose] def compA24 (a b : Array ℕ) : Array ℕ :=
  ((List.range 24).map fun i => a[b[i]!]!).toArray

@[expose] def idA24 : Array ℕ := (List.range 24).toArray

theorem getElem!_compA24 (a b : Array ℕ) {i : ℕ} (hi : i < 24) :
    (compA24 a b)[i]! = a[b[i]!]! := by
  have hsz : i < ((List.range 24).map fun i => a[b[i]!]!).toArray.size := by simpa using hi
  rw [compA24, getElem!_pos _ i hsz]
  simp

theorem hasArr_compA24 {σ τ : P24} {a b : Array ℕ} (hσ : HasArr σ a) (hτ : HasArr τ b) :
    HasArr (σ * τ) (compA24 a b) := fun i => by
  rw [getElem!_compA24 a b i.2, Equiv.Perm.mul_apply, hσ, hτ]

theorem hasArr_idA24 : HasArr (1 : P24) idA24 := by
  have h : ∀ i : Fin 24, (i : ℕ) = idA24[(i : ℕ)]! := by decide +kernel
  exact h

@[expose] def arrP2 (s : PG2) : Array ℕ :=
  compA24 (compA24 (koArr s.t.val) (dArrs.getD s.j.val #[])) (if s.ε = 1 then eArr else idA24)

theorem hasArr_toPerm (s : PG2) : HasArr (PG2.toPerm s) (arrP2 s) := by
  have h1 : HasArr (koPerm s.t) (koArr s.t.val) := hasArr_permOfArr (koArr_ok s.t).1
  have h2 : HasArr (dPerm s.j) (dArrs.getD s.j.val #[]) := hasArr_permOfArr (dArrs_ok s.j).1
  have h3 : HasArr (if s.ε = 1 then ePerm else 1) (if s.ε = 1 then eArr else idA24) := by
    split_ifs
    · exact hasArr_ePerm
    · exact hasArr_idA24
  exact hasArr_compA24 (hasArr_compA24 h1 h2) h3

theorem eq_of_hasArr {σ τ : P24} {a : Array ℕ} (hσ : HasArr σ a) (hτ : HasArr τ a) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).trans (hτ i).symm)

@[expose] noncomputable def toPermMog (s : PG2) : ↥mog22plus :=
  ⟨PG2.toPerm s, P2_le_mog22plus_sylw (PG2.toPerm_mem_P2 s)⟩

@[expose] noncomputable def autP2 : PG2 →* MulAut W10 :=
  Rc.comp (PG2.toPermHom.codRestrict mog22plus fun s => P2_le_mog22plus_sylw (PG2.toPerm_mem_P2 s))

theorem autP2_apply (s : PG2) : autP2 s = Rc (toPermMog s) := rfl

@[expose] def actP2 (s : PG2) (m : ℕ) : ℕ := act10 (arrP2 s) m

theorem autP2_toW (s : PG2) (m : ℕ) : autP2 s (toW 10 m) = toW 10 (actP2 s m) :=
  Rc_toW (toPermMog s) (hasArr_toPerm s) m

theorem chainAct_P2 : ChainAct (MaskCoords.std 10) autP2 actP2 where
  spec s m _ := autP2_toW s m
  lt s m _ := act10_lt _ m

theorem actP2_unit_moved_all : PG2.all.all (fun s =>
    s == 1 || (List.range 10).any fun j => actP2 s (2 ^ j) != 2 ^ j) = true := by
  decide +kernel

theorem actP2_unit_moved : ∀ s ∈ PG2.all, s ≠ 1 → ∃ j < 10, actP2 s (2 ^ j) ≠ 2 ^ j := by
  intro s hs hne
  have h := List.all_eq_true.1 actP2_unit_moved_all s hs
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at h
  rcases h with h | ⟨j, hj, hne'⟩
  · exact absurd h hne
  · exact ⟨j, hj, hne'⟩

theorem injective_autP2 : Function.Injective autP2 := by
  rw [injective_iff_map_eq_one]
  intro s hs
  by_contra hne
  obtain ⟨j, hj, hmv⟩ := actP2_unit_moved s (PG2.mem_all s) hne
  have h1 : autP2 s (toW 10 (2 ^ j)) = toW 10 (2 ^ j) := by
    rw [hs, MulAut.one_apply]
  rw [autP2_toW] at h1
  exact hmv (toW_inj (act10_lt _ _) (Nat.pow_lt_pow_right (by norm_num) hj) h1)

theorem isChainSub_rImg {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) :
    IsChainSub autP2 l (rImg Rc A) := by
  intro a
  constructor
  · intro ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨s, hs, hys⟩ := (hAeq _).1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨s, hs, (congrArg Rc (Subtype.ext hys)).trans (autP2_apply s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.2 ⟨toPermMog s,
      Subgroup.mem_subgroupOf.2 ((hAeq _).2 ⟨s, hs, rfl⟩), rfl⟩

theorem rk_eq_of_card {G : Type*} [Group G] {k : ℕ} (h : Nat.card G = 2 ^ k) :
    CFSG.Quasithin.rk G = k := by
  unfold CFSG.Quasithin.rk
  rw [h, padicValNat.prime_pow]

theorem rk_fixV_chain {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {r : ℕ}
    (h : (fixMasks 10 actP2 l).length = 2 ^ r) : CFSG.Quasithin.rk ↥(fixV (rImg Rc A)) = r :=
  rk_eq_of_card ((card_fixV chainAct_P2 (isChainSub_rImg hAeq)).trans h)

theorem card_of_chain (F : List PG2) (hnd : F.Nodup) (B : Subgroup P24)
    (hB : ∀ x : P24, x ∈ B ↔ ∃ s ∈ F, x = PG2.toPerm s) : Nat.card B = F.length := by
  have h1 : (B : Set P24) = PG2.toPerm '' (F.toFinset : Set PG2) := by
    ext x
    simp only [SetLike.mem_coe, hB, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [← SetLike.coe_sort_coe, h1, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ PG2.toPerm_injective, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

end CFSG.Quasithin.RonanH155
