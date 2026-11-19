
module

public import CFSG.Monster.B.TwoA.Base.GeomResBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open scoped IsMulCommutative

attribute [local instance] parAction

theorem finrank_map_mkQ_of_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {N S : Submodule K V} (h : N ≤ S) :
    finrank K ↥(S.map N.mkQ) + finrank K N = finrank K S := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (N.mkQ.comp S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq] at h1
  exact h1

section Interval

variable {G : Type*} [Group G] [Finite G] {E L : Subgroup G} [CFSG.IsElementaryAbelian 2 E]

abbrev quotEL (E L : Subgroup G) [CFSG.IsElementaryAbelian 2 E] : Type _ :=
  Additive E ⧸ subOf E L

theorem finrank_quotEL (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) : finrank (ZMod 2) (quotEL E L) = b - a := by
  have h1 := Submodule.finrank_quotient_add_finrank (subOf E L)
  have h2 : finrank (ZMod 2) (subOf E L) = a := finrank_subOf E hLE hL
  have h3 : finrank (ZMod 2) (Additive E) = b := finrank_additive_of_card hE
  change finrank (ZMod 2) (Additive E ⧸ subOf E L) = b - a
  omega

def quotELEquiv (hLE : L ≤ E) {a b n : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) (hn : b - a = n) : quotEL E L ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_quotEL hLE hE hL, Module.finrank_fin_fun, hn])

def intervalSub (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) (B : Subgroup G) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  ((subOf E B).map (subOf E L).mkQ).map (quotELEquiv hLE hE hL hn : quotEL E L →ₗ[ZMod 2] _)

theorem finrank_intervalSub (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) {B : Subgroup G} (hLB : L ≤ B) (hBE : B ≤ E)
    {d : ℕ} (hB : Nat.card B = 2 ^ (a + d)) :
    finrank (ZMod 2) (intervalSub hLE hE hL hn B) = d := by
  rw [intervalSub, LinearEquiv.finrank_map_eq]
  have h1 := finrank_map_mkQ_of_le ((subOf_le_subOf_iff hLE).2 hLB)
  rw [finrank_subOf E hLE hL, finrank_subOf E hBE hB] at h1
  exact Nat.add_right_cancel (h1.trans (Nat.add_comm a d))

theorem intervalSub_le_iff (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) {B B' : Subgroup G} (hLB : L ≤ B)
    (hBE : B ≤ E) (hLB' : L ≤ B') :
    intervalSub hLE hE hL hn B ≤ intervalSub hLE hE hL hn B' ↔ B ≤ B' := by
  rw [intervalSub, intervalSub, Submodule.map_le_map_iff_of_injective
    (quotELEquiv hLE hE hL hn).injective, ← subOf_le_subOf_iff hBE]
  have hK := (subOf_le_subOf_iff hLE).2 hLB
  have hK' := (subOf_le_subOf_iff hLE).2 hLB'
  constructor
  · intro h
    have h1 := Submodule.comap_mono (f := (subOf E L).mkQ) h
    rwa [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_of_le_right hK,
      sup_of_le_right hK'] at h1
  · exact Submodule.map_mono

def intervalGrp (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) (P : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subgroup G :=
  ofSub E ((P.map ((quotELEquiv hLE hE hL hn).symm : _ →ₗ[ZMod 2] quotEL E L)).comap
    (subOf E L).mkQ)

theorem intervalGrp_le (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) (P : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    intervalGrp hLE hE hL hn P ≤ E := ofSub_le _

theorem le_intervalGrp (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) (P : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    L ≤ intervalGrp hLE hE hL hn P := by
  intro g hg
  refine ⟨hLE hg, ?_⟩
  have h0 : (subOf E L).mkQ (Additive.ofMul ⟨g, hLE hg⟩) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hg
  rw [Submodule.mem_comap, h0]
  exact Submodule.zero_mem _

theorem intervalSub_intervalGrp (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) (P : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    intervalSub hLE hE hL hn (intervalGrp hLE hE hL hn P) = P := by
  rw [intervalSub, intervalGrp, subOf_ofSub,
    Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _), ← Submodule.map_comp,
    ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    Submodule.map_id]

theorem intervalGrp_intervalSub (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) {B : Subgroup G} (hLB : L ≤ B)
    (hBE : B ≤ E) : intervalGrp hLE hE hL hn (intervalSub hLE hE hL hn B) = B := by
  rw [intervalSub, intervalGrp, ← Submodule.map_comp, ← LinearEquiv.coe_trans,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Submodule.map_id,
    Submodule.comap_map_mkQ, sup_of_le_right ((subOf_le_subOf_iff hLE).2 hLB), ofSub_subOf hBE]

theorem natCard_intervalGrp (hLE : L ≤ E) {a b : ℕ} (hE : Nat.card E = 2 ^ b)
    (hL : Nat.card L = 2 ^ a) {n : ℕ} (hn : b - a = n) {P : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {d : ℕ} (hP : finrank (ZMod 2) P = d) :
    Nat.card (intervalGrp hLE hE hL hn P) = 2 ^ (a + d) := by
  have h1 := finrank_map_mkQ_of_le (N := subOf E L)
    (S := (P.map ((quotELEquiv hLE hE hL hn).symm : _ →ₗ[ZMod 2] quotEL E L)).comap
      (subOf E L).mkQ) (fun x hx => by
        have h0 : (subOf E L).mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
        rw [Submodule.mem_comap, h0]
        exact Submodule.zero_mem _)
  rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _),
    LinearEquiv.finrank_map_eq, hP, finrank_subOf E hLE hL] at h1
  rw [intervalGrp, ← (finrank_subOf_iff (ofSub_le _)), subOf_ofSub]
  omega

end Interval

def coType (j : ℕ) : Set ℕ := Set.Icc 1 5 \ {j, j + 1}

theorem coType_subset (j : ℕ) : coType j ⊆ Set.Icc 1 5 := Set.sdiff_subset

theorem Echain_zero : Echain 0 = ⊥ := rfl

theorem Echain_mono' {i k : ℕ} (hik : i ≤ k) (hk : k ≤ 5) : Echain i ≤ Echain k := by
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · rw [Echain_zero]
    exact bot_le
  · exact Echain_mono h1 hik hk

theorem mem_coType {j s : ℕ} : s ∈ coType j ↔ (1 ≤ s ∧ s ≤ 5) ∧ s ≠ j ∧ s ≠ j + 1 := by
  simp only [coType, Set.mem_sdiff, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or]

theorem stdObj_mem_stdSub {s : ℕ} (h1 : 1 ≤ s) (h5 : s ≤ 5) {J : Set ℕ} (hs : s ∈ J) :
    stdObj s h1 h5 ∈ stdSub J := ⟨stdObj_mem s h1 h5, hs⟩

end CFSG.Monster.B.TwoA
