module

public import CFSG.Quasithin.EmptyFaithful.S153EN8E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem eq_one_of_three_pow_mul (a n i : ℕ) (h : 3 ^ a * i = 6 * 2 ^ n) (hi : ¬ 3 ∣ i) : a = 1 := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · exfalso
      apply hi
      have : i = 6 * 2 ^ n := by simpa using h
      rw [this]
      exact Dvd.dvd.mul_right (by norm_num) _
    · rfl
  · exfalso
    have h9 : 9 ∣ 6 * 2 ^ n := by
      rw [← h]
      exact Dvd.dvd.mul_right (by
        have : 3 ^ 2 ∣ 3 ^ a := pow_dvd_pow 3 ha
        simpa using this) _
    have hcop : Nat.Coprime 9 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have := hcop.dvd_of_dvd_mul_right h9
    omega

omit [Finite G] in
theorem eq_one_of_cube_of_mem_T {x : G} {T' : Subgroup G} (hT2 : IsPGroup 2 T') (hxT : x ∈ T')
    (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := hT2 ⟨x, hxT⟩
  have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have h3 : orderOf x ∣ Nat.gcd 3 (2 ^ m) := Nat.dvd_gcd h1 h2
  have hcop : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  rw [hcop] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

@[expose] def Jgp (M V₂ : Subgroup G) (d : G) : Subgroup G :=
  (M ⊓ Subgroup.centralizer (V₂ : Set G)) ⊓ Subgroup.centralizer ({d} : Set G)

omit [Finite G] in
theorem mem_Jgp {M V₂ : Subgroup G} {d x : G} :
    x ∈ Jgp M V₂ d ↔ (x ∈ M ∧ x ∈ Subgroup.centralizer (V₂ : Set G)) ∧ x * d = d * x := by
  unfold Jgp
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (h2 d rfl).symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact h2.symm

theorem commutator_mem_Q {x δ : G} (hx : x ∈ M) (hδ : δ ∈ M)
    (hc : barM cx hx * barM cx hδ = barM cx hδ * barM cx hx) :
    x * δ * x⁻¹ * δ⁻¹ ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  have hM : x * δ * x⁻¹ * δ⁻¹ ∈ M := M.mul_mem (M.mul_mem (M.mul_mem hx hδ) (M.inv_mem hx)) (M.inv_mem hδ)
  refine ⟨hM, (barM_eq_one_iff (cx := cx) hM).1 ?_⟩
  show barM cx (M.mul_mem (M.mul_mem (M.mul_mem hx hδ) (M.inv_mem hx)) (M.inv_mem hδ)) = 1
  rw [barM_mul (M.mul_mem (M.mul_mem hx hδ) (M.inv_mem hx)) (M.inv_mem hδ),
    barM_mul (M.mul_mem hx hδ) (M.inv_mem hx), barM_mul hx hδ, barM_inv hx, barM_inv hδ]
  calc barM cx hx * barM cx hδ * (barM cx hx)⁻¹ * (barM cx hδ)⁻¹
      = (barM cx hδ * barM cx hx) * (barM cx hx)⁻¹ * (barM cx hδ)⁻¹ := by rw [hc]
    _ = 1 := by group

section Basic

variable (B : BarModel cx)

include B in
theorem card_M₂ : Nat.card ↥(M ⊓ Subgroup.centralizer (V₁ : Set G)) =
    6 * Nat.card ↥(M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  have hV := cx.c.hyp.elemAbelian
  have hMN := cx.c.hyp.le_normalizer
  have h := inf_centralizer_eq_preI hV hMN B.hS.symm
  rw [B.hV₁] at h
  rw [h, card_preI hV B.hS.L₂_le, B.hS.card_L₂]

theorem isPGroup_Q (c : Chain15358 cx N₁ N₂ g s y t₁) :
    IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
  (cx.hF.sylow_H.2.1 : IsPGroup 2 T).to_le (Q_le_T c)

omit B [Finite G] in
theorem le_normalizer_Q {V : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, B2F.normalizer_le_normalizer_centralizer _ (hMN hx)⟩

include B in
theorem exists_sylow_three (c : Chain15358 cx N₁ N₂ g s y t₁) :
    ∃ R : Subgroup G, R ≤ M ⊓ Subgroup.centralizer (V₁ : Set G) ∧ IsPGroup 3 R ∧
      ¬ 3 ∣ R.relIndex (M ⊓ Subgroup.centralizer (V₁ : Set G)) ∧ Nat.card R = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, -, hRK, hRp, hRi⟩ := S153E.exists_sylow_ge (p := 3) (Q := (⊥ : Subgroup G))
    (K := M ⊓ Subgroup.centralizer (V₁ : Set G))
    (IsPGroup.of_card (p := 3) (n := 0) (by simp)) bot_le
  refine ⟨R, hRK, hRp, hRi, ?_⟩
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  obtain ⟨n, hn⟩ := (isPGroup_Q c).exists_card_eq
  have h1 := Subgroup.relIndex_mul_card R (M ⊓ Subgroup.centralizer (V₁ : Set G))
  rw [inf_eq_left.2 hRK, ha, card_M₂ B, hn] at h1
  have h2 : 3 ^ a * (R.relIndex (M ⊓ Subgroup.centralizer (V₁ : Set G))) = 6 * 2 ^ n := by
    rw [mul_comm]
    exact h1
  have := eq_one_of_three_pow_mul a n _ h2 hRi
  rw [ha, this]
  rfl

end Basic

end S153EN8

end CFSG.Quasithin
