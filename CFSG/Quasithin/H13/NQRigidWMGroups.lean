module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Assembly.LowTwoRank Matrix

section Linear

variable {F : Type} [Field F] [Finite F]

theorem isSimpleGroup_statedSL_two_charTwo [CharP F 2] (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup ↥(StatedSL 2 F) := by
  have : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
    exact ⟨s, hs⟩
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 2) le_rfl (Or.inr h4)).2.1
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
    ext A
    rw [Subgroup.mem_bot]
    constructor
    · intro hA
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      have hr1 : r = 1 := by
        rw [Fintype.card_fin] at hr
        have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
        have h3 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
        have h5 : r + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
        have h6 : r = -1 := eq_neg_of_add_eq_zero_left h5
        rw [h6]
        exact (CharTwo.neg_eq (1 : F))
      apply Subtype.ext
      rw [← hrA, hr1]
      simp
    · rintro rfl
      exact Subgroup.one_mem _
  let e1 : ProjectiveSpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have h1 : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := MulEquiv.isSimpleGroup e1.symm
  exact MulEquiv.isSimpleGroup (specialLinearGroupEquivStatedSL 2 F).symm

theorem not_three_dvd_two_pow_sub_one {m : ℕ} (hm : Odd m) : ¬ 3 ∣ 2 ^ m - 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h : (4 : ℕ) ^ k ≡ 1 ^ k [MOD 3] := Nat.ModEq.pow k (by decide)
  rw [one_pow] at h
  have h1 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h1]
  have h2 : 4 ^ k % 3 = 1 := h
  have h3 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem isSimpleGroup_statedSL_three_odd {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : Odd m) :
    IsSimpleGroup ↥(StatedSL 3 F) := by
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 3) (by norm_num) (Or.inl le_rfl)).2.1
  have hcard : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) = 1 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hF]
    exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_three_dvd_two_pow_sub_one hm)).symm
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 3) F) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hcard
  let e1 : ProjectiveSpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have h1 : IsSimpleGroup (SpecialLinearGroup (Fin 3) F) := MulEquiv.isSimpleGroup e1.symm
  exact MulEquiv.isSimpleGroup (specialLinearGroupEquivStatedSL 3 F).symm

end Linear

section Centralizer

theorem centralizer_eq_one_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    {N : Subgroup X} [N.Normal] (hN : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) {g : X}
    (hg : ∀ n ∈ N, g * n = n * g) : g = 1 := by
  have hC : (centralizer (N : Set X)).Normal := by
    refine ⟨fun c hc x => ?_⟩
    rw [mem_centralizer_iff] at hc ⊢
    intro n hn
    have hn' : x⁻¹ * n * x⁻¹⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn x⁻¹
    have h1 := hc _ hn'
    calc n * (x * c * x⁻¹) = x * ((x⁻¹ * n * x⁻¹⁻¹) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * n * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * n := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (centralizer (N : Set X)) with h | h
  · have : g ∈ centralizer (N : Set X) := mem_centralizer_iff.mpr fun n hn => (hg n hn).symm
    rw [h, mem_bot] at this
    exact this
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hN
    have : a ∈ centralizer (N : Set X) := by rw [h]; trivial
    exact hab (mem_centralizer_iff.mp this b hb).symm

theorem perm_five_center_eq_bot : Subgroup.center (Equiv.Perm (Fin 5)) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_bot]
  refine Equiv.ext fun a => ?_
  by_contra ha
  have ha' : σ a ≠ a := ha
  obtain ⟨c, hca, hcs⟩ : ∃ c : Fin 5, c ≠ a ∧ c ≠ σ a := by
    have key : ∀ x y : Fin 5, ∃ c : Fin 5, c ≠ x ∧ c ≠ y := by decide
    exact key a (σ a)
  have h1 := mem_center_iff.mp hσ (Equiv.swap a c)
  have h2 := congrArg (fun τ : Equiv.Perm (Fin 5) => τ a) h1
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h2
  rw [Equiv.swap_apply_of_ne_of_ne ha' (Ne.symm hcs)] at h2
  exact hca (σ.injective h2.symm)

theorem sign_injective_of_inf_alternating {C : Subgroup (Equiv.Perm (Fin 5))}
    (hC : C ⊓ alternatingGroup (Fin 5) = ⊥) {a b : Equiv.Perm (Fin 5)} (ha : a ∈ C) (hb : b ∈ C)
    (hs : Equiv.Perm.sign a = Equiv.Perm.sign b) : a = b := by
  have h1 : a * b⁻¹ ∈ C ⊓ alternatingGroup (Fin 5) := by
    refine mem_inf.mpr ⟨mul_mem ha (inv_mem hb), ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, mul_inv_cancel]
  rw [hC, mem_bot] at h1
  exact mul_inv_eq_one.mp h1

theorem commute_of_inf_alternating {C : Subgroup (Equiv.Perm (Fin 5))}
    (hC : C ⊓ alternatingGroup (Fin 5) = ⊥) {a b : Equiv.Perm (Fin 5)} (ha : a ∈ C) (hb : b ∈ C) :
    a * b = b * a :=
  sign_injective_of_inf_alternating hC (mul_mem ha hb) (mul_mem hb ha) (by
    rw [map_mul, map_mul, mul_comm])

theorem centralizer_perm_five_eq_bot {N : Subgroup (Equiv.Perm (Fin 5))} [N.Normal]
    (hN : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) (hZ : ∀ z ∈ N, (∀ n ∈ N, z * n = n * z) → z = 1)
    {g : Equiv.Perm (Fin 5)} (hg : ∀ n ∈ N, g * n = n * g) : g = 1 := by
  set C := centralizer (N : Set (Equiv.Perm (Fin 5))) with hCdef
  have hCn : C.Normal := by
    refine ⟨fun c hc x => ?_⟩
    rw [hCdef, mem_centralizer_iff] at hc ⊢
    intro n hn
    have hn' : x⁻¹ * n * x⁻¹⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn x⁻¹
    have h1 := hc _ hn'
    calc n * (x * c * x⁻¹) = x * ((x⁻¹ * n * x⁻¹⁻¹) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * n * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * n := by group
  have hNA : alternatingGroup (Fin 5) ≤ N := by
    have hn : ((N.subgroupOf (alternatingGroup (Fin 5)))).Normal :=
      Subgroup.Normal.subgroupOf inferInstance _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5)))
      with h | h
    · exfalso
      have hinf : N ⊓ alternatingGroup (Fin 5) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx.2⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
          hx.1
        rw [h, mem_bot] at this
        exact congrArg Subtype.val this
      obtain ⟨a, ha, b, hb, hab⟩ := hN
      exact hab (commute_of_inf_alternating hinf ha hb)
    · intro x hx
      have : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [h]
        trivial
      exact this
  have hCA : C ⊓ alternatingGroup (Fin 5) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    exact hZ x (hNA hx.2) fun n hn => (mem_centralizer_iff.mp hx.1 n hn).symm
  have hgC : g ∈ C := mem_centralizer_iff.mpr fun n hn => (hg n hn).symm
  have hcen : g ∈ Subgroup.center (Equiv.Perm (Fin 5)) := by
    rw [mem_center_iff]
    intro x
    have h1 : x * g * x⁻¹ ∈ C := hCn.conj_mem g hgC x
    have h2 := sign_injective_of_inf_alternating hCA h1 hgC (by
      rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign x), mul_assoc, mul_inv_cancel,
        mul_one])
    calc x * g = x * g * x⁻¹ * x := by group
      _ = g * x := by rw [h2]
  rw [perm_five_center_eq_bot, mem_bot] at hcen
  exact hcen

end Centralizer

end CFSG.Quasithin.H13.NQRigid
