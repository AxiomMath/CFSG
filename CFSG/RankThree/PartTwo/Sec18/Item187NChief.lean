module

public import CFSG.RankThree.PartTwo.Sec18.Item187NSection
import Mathlib.GroupTheory.Nilpotent
import CFSG.Permutation.FiveTransitive.CoprimeAutomorphismDisplacement

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

section Chief

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_of_le_normalizer {W : Subgroup G} {x c : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hc : c ∈ W) : x⁻¹ * c * x ∈ W :=
  (Subgroup.mem_normalizer_iff''.mp hx c).mp hc

private theorem inv_mul_mem_of_comm_mem {W : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hc : y * x * y⁻¹ * x⁻¹ ∈ W) :
    (y * x * y⁻¹)⁻¹ * x ∈ W := by
  have e : (y * x * y⁻¹)⁻¹ * x = x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * x := by group
  rw [e]
  exact conj_mem_of_le_normalizer hx (inv_mem hc)

private theorem comm_mem_of_inv_mul_mem {W : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (h : (y * x * y⁻¹)⁻¹ * x ∈ W) :
    y * x * y⁻¹ * x⁻¹ ∈ W := by
  have e : y * x * y⁻¹ * x⁻¹ = x⁻¹⁻¹ * ((y * x * y⁻¹)⁻¹ * x)⁻¹ * x⁻¹ := by group
  rw [e]
  exact conj_mem_of_le_normalizer (inv_mem hx) (inv_mem h)

private theorem le_normalizer_closure {Δ : Subgroup G} {T : Set G}
    (h : ∀ g ∈ Δ, ∀ t ∈ T, g * t * g⁻¹ ∈ Subgroup.closure T) :
    Δ ≤ Subgroup.normalizer ((Subgroup.closure T : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Δ, ∀ x ∈ Subgroup.closure T, g * x * g⁻¹ ∈ Subgroup.closure T := by
    intro g hg x hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure T)
      ?_ ?_ ?_ ?_ hx
    · intro t ht
      exact h g hg t ht
    · show g * 1 * g⁻¹ ∈ Subgroup.closure T
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · intro a b _ _ ha hb
      show g * (a * b) * g⁻¹ ∈ Subgroup.closure T
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    · intro a _ ha
      show g * a⁻¹ * g⁻¹ ∈ Subgroup.closure T
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key g hg x, fun hx => ?_⟩
  have h2 := key g⁻¹ (inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h2

private theorem commutatorElement_eq_one_of_sq {R : Type*} [Group R] {x y : R}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y * (x * y) = 1) : ⁅x, y⁆ = 1 := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  simpa only [mul_assoc] using hxy

private theorem mul_self_mem_of_index_eq_two {Q : Type*} [Group Q] (M : Subgroup Q) [M.Normal]
    (hM : M.index = 2) (a : Q) : a * a ∈ M := by
  have h1 : (a : Q ⧸ M) ^ Nat.card (Q ⧸ M) = 1 := pow_card_eq_one'
  rw [← Subgroup.index_eq_card, hM] at h1
  have h2 : ((a ^ 2 : Q) : Q ⧸ M) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact h1
  have h3 : a ^ 2 ∈ M := (QuotientGroup.eq_one_iff _).mp h2
  rwa [pow_two] at h3

private theorem commutatorElement_mem_of_index_eq_two {Q : Type*} [Group Q] (M : Subgroup Q)
    [M.Normal] (hM : M.index = 2) (a b : Q) : ⁅a, b⁆ ∈ M := by
  have hsq : ∀ c : Q, (c : Q ⧸ M) * c = 1 := fun c => by
    have h := (QuotientGroup.eq_one_iff (c * c)).mpr (mul_self_mem_of_index_eq_two M hM c)
    rwa [QuotientGroup.mk_mul] at h
  have hab := hsq (a * b)
  rw [QuotientGroup.mk_mul] at hab
  have key := commutatorElement_eq_one_of_sq (hsq a) (hsq b) hab
  refine (QuotientGroup.eq_one_iff _).mp ?_
  have hc := map_commutatorElement (QuotientGroup.mk' M) a b
  simp only [QuotientGroup.mk'_apply] at hc
  rw [hc]
  exact key

private theorem exists_index_two_sq_comm {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    {K : Subgroup Q} (hK : K ≠ ⊤) :
    ∃ M : Subgroup Q, K ≤ M ∧ M ≠ ⊤ ∧ (∀ a : Q, a * a ∈ M) ∧ ∀ a b : Q, ⁅a, b⁆ ∈ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Subgroup Q) :=
    Finite.of_injective (fun H : Subgroup Q => (H : Set Q)) SetLike.coe_injective
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨M, hKM, hM⟩ : ∃ M : Subgroup Q, K ≤ M ∧ IsCoatom M := by
    rcases IsCoatomic.eq_top_or_exists_le_coatom K with h | ⟨M, hM, hKM⟩
    · exact absurd h hK
    · exact ⟨M, hKM, hM⟩
  have hidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hQ).mp hM
  haveI : M.Normal := Subgroup.normal_of_index_eq_two hidx
  exact ⟨M, hKM, hM.1, mul_self_mem_of_index_eq_two M hidx,
    commutatorElement_mem_of_index_eq_two M hidx⟩

private theorem stab_of_sections {Γ W₀ W₁ U : Subgroup G} {y : G} (hyΓ : y ∈ Γ)
    (hyodd : Odd (orderOf y)) (hΓ₀ : Γ ≤ Subgroup.normalizer (W₀ : Set G))
    (hΓ₁ : Γ ≤ Subgroup.normalizer (W₁ : Set G)) (hP : IsPGroup 2 W₁) (hW01 : W₀ ≤ W₁)
    (h10 : W₁ ≤ Subgroup.normalizer (W₀ : Set G)) (hUW : U ≤ W₁)
    (hU : W₁ ≤ Subgroup.normalizer (U : Set G))
    (hUy : ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ W₀) (hWy : ∀ x ∈ W₁, y * x * y⁻¹ * x⁻¹ ∈ U) :
    ∀ x ∈ W₁, y * x * y⁻¹ * x⁻¹ ∈ W₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (W₀.subgroupOf W₁).Normal := normal_subgroupOf_of_le_normalizer hW01 h10
  haveI : (U.subgroupOf W₁).Normal := normal_subgroupOf_of_le_normalizer hUW hU
  let N : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁) :=
    (U.subgroupOf W₁).map (QuotientGroup.mk' (W₀.subgroupOf W₁))
  haveI : N.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hQ2 : IsPGroup 2 (↥W₁ ⧸ W₀.subgroupOf W₁) := hP.to_quotient _
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hQ2.to_subgroup N)
  have hcop : (orderOf y).Coprime (Nat.card N) := by
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hyodd)
  let g : ↥Γ := ⟨y, hyΓ⟩
  have hak : (secAct hΓ₀ hΓ₁ g) ^ orderOf y = 1 := by
    have hg : g ^ orderOf y = 1 := Subtype.ext (by simp [g])
    rw [← map_pow, hg, map_one]
  have hyw : ∀ w : ↥W₁, y * (w : G) * y⁻¹ ∈ W₁ := fun w =>
    (Subgroup.mem_normalizer_iff.mp (hΓ₁ hyΓ) (w : G)).mp w.2
  have hact : ∀ w : ↥W₁, secAct hΓ₀ hΓ₁ g (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨y * (w : G) * y⁻¹, hyw w⟩ :=
    fun w => secAct_mk hΓ₀ hΓ₁ g w (hyw w)
  have hfix : ∀ z ∈ N, secAct hΓ₀ hΓ₁ g z = z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    rw [QuotientGroup.mk'_apply, hact u, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact inv_mul_mem_of_comm_mem (h10 u.2) (hUy _ (Subgroup.mem_subgroupOf.mp hu))
  have hquot : ∀ x : ↥W₁ ⧸ W₀.subgroupOf W₁,
      (QuotientGroup.mk' N) (secAct hΓ₀ hΓ₁ g x) = (QuotientGroup.mk' N) x := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    have hz : (⟨y * (w : G) * y⁻¹, hyw w⟩ : ↥W₁)⁻¹ * w ∈ U.subgroupOf W₁ := by
      rw [Subgroup.mem_subgroupOf]
      exact inv_mul_mem_of_comm_mem (hU w.2) (hWy _ w.2)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hact w, QuotientGroup.eq,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact Subgroup.mem_map_of_mem _ hz
  have h1 : secAct hΓ₀ hΓ₁ g = 1 :=
    CFSG.FiveTransitive.CoprimeAutomorphismDisplacement.eq_one_of_quotient N
      (secAct hΓ₀ hΓ₁ g) (orderOf y) hak hcop hfix hquot
  intro x hx
  have hx1 : secAct hΓ₀ hΓ₁ g (QuotientGroup.mk (⟨x, hx⟩ : ↥W₁)) =
      QuotientGroup.mk (⟨x, hx⟩ : ↥W₁) := by
    rw [h1, MulAut.one_apply]
  rw [hact, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx1
  exact comm_mem_of_inv_mul_mem (h10 hx) hx1

private abbrev ChiefAdm (P Γ : Subgroup G) (y : G) (A B : Subgroup G) : Prop :=
  A ≤ B ∧ B ≤ P ∧ Γ ≤ Subgroup.normalizer (A : Set G) ∧ Γ ≤ Subgroup.normalizer (B : Set G) ∧
    B ≤ Subgroup.normalizer (A : Set G) ∧ ∃ x ∈ B, y * x * y⁻¹ * x⁻¹ ∉ A

private theorem le_normalizer_of_comm_mem {W₀ W₁ U : Subgroup G}
    (hcm : ∀ a ∈ W₁, ∀ b ∈ W₁, ⁅a, b⁆ ∈ W₀) (hWU : W₀ ≤ U) (hUW : U ≤ W₁) :
    W₁ ≤ Subgroup.normalizer (U : Set G) := by
  have hconj : ∀ g ∈ W₁, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have e : g * u * g⁻¹ = ⁅g, u⁆ * u := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hWU (hcm g hg u (hUW hu))) hu
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact hconj w hw u hu
  · intro hu
    have h := hconj w⁻¹ (inv_mem hw) _ hu
    have e : w⁻¹ * (w * u * w⁻¹) * w⁻¹⁻¹ = u := by group
    rwa [e] at h

private theorem eq_of_minimal_normal {P Γ W₀ W₁ : Subgroup G} {y : G} (hP : IsPGroup 2 P)
    (hyΓ : y ∈ Γ) (hyodd : Odd (orderOf y)) (hadm : ChiefAdm P Γ y W₀ W₁)
    (hmin : ∀ A B : Subgroup G, ChiefAdm P Γ y A B →
      Nat.card W₁ - Nat.card W₀ ≤ Nat.card B - Nat.card A)
    {U : Subgroup G} (hWU : W₀ ≤ U) (hUW : U ≤ W₁) (hΓU : Γ ≤ Subgroup.normalizer (U : Set G))
    (hU : W₁ ≤ Subgroup.normalizer (U : Set G)) : U = W₀ ∨ U = W₁ := by
  obtain ⟨hW01, hW1P, hΓ0, hΓ1, h10, x₀, hx₀W1, hx₀⟩ := hadm
  by_contra hcon
  push_neg at hcon
  have hc₀ : Nat.card W₀ < Nat.card U :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hWU (Ne.symm hcon.1))
  have hc₁ : Nat.card U < Nat.card W₁ :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hUW hcon.2)
  have hUy : ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ W₀ := by
    by_contra hno
    push_neg at hno
    obtain ⟨u, huU, hu⟩ := hno
    have h1 := hmin W₀ U ⟨hWU, hUW.trans hW1P, hΓ0, hΓU, hUW.trans h10, u, huU, hu⟩
    omega
  have hWy : ∀ x ∈ W₁, y * x * y⁻¹ * x⁻¹ ∈ U := by
    by_contra hno
    push_neg at hno
    obtain ⟨x, hxW, hx⟩ := hno
    have h1 := hmin U W₁ ⟨hUW, hW1P, hΓU, hΓ1, hU, x, hxW, hx⟩
    omega
  exact hx₀ (stab_of_sections hyΓ hyodd hΓ0 hΓ1 (IsPGroup.to_le hP hW1P) hW01 h10 hUW hU
    hUy hWy x₀ hx₀W1)

private theorem sq_comm_mem_of_minimal {P Γ W₀ W₁ : Subgroup G} {y : G} (hP : IsPGroup 2 P)
    (hyΓ : y ∈ Γ) (hyodd : Odd (orderOf y)) (hadm : ChiefAdm P Γ y W₀ W₁)
    (hmin : ∀ A B : Subgroup G, ChiefAdm P Γ y A B →
      Nat.card W₁ - Nat.card W₀ ≤ Nat.card B - Nat.card A) :
    (∀ a ∈ W₁, a * a ∈ W₀) ∧ ∀ a ∈ W₁, ∀ b ∈ W₁, ⁅a, b⁆ ∈ W₀ := by
  obtain ⟨hW01, hW1P, hΓ0, hΓ1, h10, x₀, hx₀W1, hx₀⟩ := hadm
  have hadm' : ChiefAdm P Γ y W₀ W₁ := ⟨hW01, hW1P, hΓ0, hΓ1, h10, x₀, hx₀W1, hx₀⟩
  obtain ⟨T, hT⟩ : ∃ T : Set G, T = {t | t ∈ W₀ ∨ (∃ x ∈ W₁, t = x * x) ∨
      ∃ a ∈ W₁, ∃ b ∈ W₁, t = ⁅a, b⁆} := ⟨_, rfl⟩
  have hmem0 : ∀ t ∈ W₀, t ∈ T := fun t ht => by
    rw [hT, Set.mem_setOf_eq]
    exact Or.inl ht
  have hmemSq : ∀ x ∈ W₁, x * x ∈ T := fun x hx => by
    rw [hT, Set.mem_setOf_eq]
    exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
  have hmemCm : ∀ a ∈ W₁, ∀ b ∈ W₁, ⁅a, b⁆ ∈ T := fun a ha b hb => by
    rw [hT, Set.mem_setOf_eq]
    exact Or.inr (Or.inr ⟨a, ha, b, hb, rfl⟩)
  have hTW1 : T ⊆ (W₁ : Set G) := by
    intro t ht
    rw [hT, Set.mem_setOf_eq] at ht
    rcases ht with ht | ⟨x, hx, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
    · exact hW01 ht
    · exact mul_mem hx hx
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hTnorm : ∀ Δ : Subgroup G, Δ ≤ Subgroup.normalizer (W₀ : Set G) →
      Δ ≤ Subgroup.normalizer (W₁ : Set G) → ∀ g ∈ Δ, ∀ t ∈ T,
        g * t * g⁻¹ ∈ Subgroup.closure T := by
    intro Δ hΔ0 hΔ1 g hg t ht
    rw [hT, Set.mem_setOf_eq] at ht
    rcases ht with ht | ⟨x, hx, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
    · exact Subgroup.subset_closure
        (hmem0 _ ((Subgroup.mem_normalizer_iff.mp (hΔ0 hg) t).mp ht))
    · have e : g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
      rw [e]
      exact Subgroup.subset_closure
        (hmemSq _ ((Subgroup.mem_normalizer_iff.mp (hΔ1 hg) x).mp hx))
    · have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.subset_closure (hmemCm _ ((Subgroup.mem_normalizer_iff.mp (hΔ1 hg) a).mp ha)
        _ ((Subgroup.mem_normalizer_iff.mp (hΔ1 hg) b).mp hb))
  have hΓE : Γ ≤ Subgroup.normalizer ((Subgroup.closure T : Subgroup G) : Set G) :=
    le_normalizer_closure (hTnorm Γ hΓ0 hΓ1)
  have hW1E : W₁ ≤ Subgroup.normalizer ((Subgroup.closure T : Subgroup G) : Set G) :=
    le_normalizer_closure (hTnorm W₁ h10 Subgroup.le_normalizer)
  have hEW1 : Subgroup.closure T ≤ W₁ := (Subgroup.closure_le W₁).mpr hTW1
  have hW0E : W₀ ≤ Subgroup.closure T := fun t ht => Subgroup.subset_closure (hmem0 t ht)
  rcases eq_of_minimal_normal hP hyΓ hyodd hadm' hmin hW0E hEW1 hΓE hW1E with hE0 | hE1
  · have hsq : ∀ a ∈ W₁, a * a ∈ W₀ := fun a ha => by
      have h := Subgroup.subset_closure (hmemSq a ha)
      rwa [hE0] at h
    have hcm : ∀ a ∈ W₁, ∀ b ∈ W₁, ⁅a, b⁆ ∈ W₀ := fun a ha b hb => by
      have h := Subgroup.subset_closure (hmemCm a ha b hb)
      rwa [hE0] at h
    exact ⟨hsq, hcm⟩
  ·
    exfalso
    have hPn : IsPGroup 2 W₁ := IsPGroup.to_le hP hW1P
    have hcW1 : y * x₀ * y⁻¹ * x₀⁻¹ ∈ W₁ :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hΓ1 hyΓ) x₀).mp hx₀W1) (inv_mem hx₀W1)
    have hK : W₀.subgroupOf W₁ ≠ ⊤ := by
      intro htop
      have hmem : (⟨y * x₀ * y⁻¹ * x₀⁻¹, hcW1⟩ : ↥W₁) ∈ W₀.subgroupOf W₁ := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hx₀ (Subgroup.mem_subgroupOf.mp hmem)
    obtain ⟨M, hKM, hMtop, hsqM, hcmM⟩ := exists_index_two_sq_comm hPn hK
    have hcl : Subgroup.closure T ≤ M.map W₁.subtype := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [hT, Set.mem_setOf_eq] at ht
      rcases ht with ht | ⟨x, hx, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
      · exact Subgroup.mem_map.mpr
          ⟨⟨t, hW01 ht⟩, hKM (Subgroup.mem_subgroupOf.mpr ht : (⟨t, hW01 ht⟩ : ↥W₁) ∈
            W₀.subgroupOf W₁), rfl⟩
      · exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * ⟨x, hx⟩, hsqM _, rfl⟩
      · exact Subgroup.mem_map.mpr ⟨⁅(⟨a, ha⟩ : ↥W₁), ⟨b, hb⟩⁆, hcmM _ _, rfl⟩
    have hW1M : W₁ ≤ M.map W₁.subtype := hE1.symm.le.trans hcl
    apply hMtop
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨m, hm, hmq⟩ := Subgroup.mem_map.mp (hW1M q.2)
    have hmq' : m = q := Subtype.ext hmq
    rw [← hmq']
    exact hm

theorem exists_chiefFactor {P Γ : Subgroup G} (hP : IsPGroup 2 P)
    (hΓP : Γ ≤ Subgroup.normalizer (P : Set G)) {y : G} (hyΓ : y ∈ Γ)
    (hyodd : Odd (orderOf y)) (hy : ∃ x ∈ P, y * x * y⁻¹ ≠ x) :
    ∃ W₀ W₁ : Subgroup G, W₀ ≤ W₁ ∧ W₁ ≤ P ∧ Γ ≤ Subgroup.normalizer (W₀ : Set G) ∧
      Γ ≤ Subgroup.normalizer (W₁ : Set G) ∧ W₁ ≤ Subgroup.normalizer (W₀ : Set G) ∧
      (∀ a ∈ W₁, ∀ b ∈ W₁, ⁅a, b⁆ ∈ W₀) ∧ (∀ a ∈ W₁, a * a ∈ W₀) ∧
      (∀ U : Subgroup G, W₀ ≤ U → U ≤ W₁ → Γ ≤ Subgroup.normalizer (U : Set G) →
        U = W₀ ∨ U = W₁) ∧
      ∃ x ∈ W₁, y * x * y⁻¹ * x⁻¹ ∉ W₀ := by
  classical
  have hbot : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g =>
    Subgroup.mem_normalizer_iff.mpr fun h => by simp
  have hex : ∃ n : ℕ, ∃ A B : Subgroup G, ChiefAdm P Γ y A B ∧ Nat.card B - Nat.card A = n := by
    obtain ⟨x, hxP, hx⟩ := hy
    refine ⟨Nat.card P - Nat.card (⊥ : Subgroup G), ⊥, P,
      ⟨bot_le, le_rfl, fun g _ => hbot g, hΓP, fun g _ => hbot g, x, hxP, ?_⟩, rfl⟩
    intro h
    exact hx (mul_inv_eq_one.mp (Subgroup.mem_bot.mp h))
  obtain ⟨W₀, W₁, hadm, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ A B : Subgroup G, ChiefAdm P Γ y A B →
      Nat.card W₁ - Nat.card W₀ ≤ Nat.card B - Nat.card A := by
    intro A B hAB
    rw [hcard]
    exact Nat.find_min' hex ⟨A, B, hAB, rfl⟩
  obtain ⟨hsq, hcm⟩ := sq_comm_mem_of_minimal hP hyΓ hyodd hadm hmin
  obtain ⟨hW01, hW1P, hΓ0, hΓ1, h10, x₀, hx₀W1, hx₀⟩ := hadm
  refine ⟨W₀, W₁, hW01, hW1P, hΓ0, hΓ1, h10, hcm, hsq, ?_, x₀, hx₀W1, hx₀⟩
  intro U hWU hUW hΓU
  exact eq_of_minimal_normal hP hyΓ hyodd ⟨hW01, hW1P, hΓ0, hΓ1, h10, x₀, hx₀W1, hx₀⟩ hmin
    hWU hUW hΓU (le_normalizer_of_comm_mem hcm hWU hUW)

end Chief

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
