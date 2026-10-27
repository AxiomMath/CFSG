module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NormD
public import CFSG.Quasithin.Vol2.Ch11G2Q8Cartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F] [CharP F 2]

@[expose] def chiT (s : Fˣ × Fˣ) : Ix3 → F
  | .inl i => ![(s.1 : F), s.2, ((s.1 : F) * s.2)⁻¹] i
  | .inr i => ![(s.1 : F)⁻¹, (s.2 : F)⁻¹, (s.1 : F) * s.2] i

theorem g2Act_g2T_apply (s : Fˣ × Fˣ) (w : Ix3 → F) (j : Ix3) :
    g2Act (g2T s) w j = chiT s j * w j := by
  rw [g2Act_g2T]
  rcases j with j | j <;> fin_cases j <;> rfl

omit [CharP F 2] in
theorem chiT_injective {x : Fˣ} (hx1 : (x : F) ≠ 1) (hx2 : (x : F) * x ≠ 1) {j j' : Ix3}
    (h1 : chiT (x, 1) j = chiT (x, 1) j') (h2 : chiT (1, x) j = chiT (1, x) j') : j = j' := by
  have hx0 : (x : F) ≠ 0 := x.ne_zero
  have a1 : (1 : F) ≠ x := fun h => hx1 h.symm
  have a2 : (x : F)⁻¹ ≠ 1 := fun h => hx1 (inv_eq_one.mp h)
  have a3 : (1 : F) ≠ (x : F)⁻¹ := fun h => a2 h.symm
  have a4 : (x : F) ≠ (x : F)⁻¹ := fun h => hx2 (by
    have h' := congrArg (· * (x : F)) h
    simp only [inv_mul_cancel₀ hx0] at h'
    exact h')
  have a5 : (x : F)⁻¹ ≠ x := fun h => a4 h.symm
  rcases j with j | j <;> rcases j' with j' | j' <;> fin_cases j <;> fin_cases j' <;>
    simp [chiT, hx1, a1, a2, a3, a4, a5] at h1 h2 ⊢

theorem eq_of_eigen {x : Fˣ} (hx1 : (x : F) ≠ 1) (hx2 : (x : F) * x ≠ 1) {w : Ix3 → F}
    {μ₁ μ₂ : F} (h1 : g2Act (g2T (x, 1)) w = μ₁ • w) (h2 : g2Act (g2T (1, x)) w = μ₂ • w)
    {j j' : Ix3} (hj : w j ≠ 0) (hj' : w j' ≠ 0) : j = j' := by
  have e1 := congrFun h1 j
  have e1' := congrFun h1 j'
  have e2 := congrFun h2 j
  have e2' := congrFun h2 j'
  simp only [g2Act_g2T_apply, Pi.smul_apply, smul_eq_mul] at e1 e1' e2 e2'
  exact chiT_injective hx1 hx2 ((mul_right_cancel₀ hj e1).trans (mul_right_cancel₀ hj' e1').symm)
    ((mul_right_cancel₀ hj e2).trans (mul_right_cancel₀ hj' e2').symm)

theorem g2T_single (s : Fˣ × Fˣ) (k : Ix3) :
    g2Act (g2T s) (Pi.single k (1 : F)) = chiT s k • Pi.single k 1 := by
  funext j
  rw [g2Act_g2T_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = k
  · subst h
    rfl
  · simp [h]

theorem ht_injective {k k' : Ix3} (h : ht k = ht k') : k = k' :=
  (eq_bv_of_ht h).trans (eq_bv_of_ht rfl).symm

omit [CharP F 2] in
theorem single_mem_stdF (k : Ix3) : Pi.single k (1 : F) ∈ stdF F (ht k + 1) := by
  rw [mem_stdF]
  intro j hj
  rw [Pi.single_apply]
  split_ifs with h
  · subst h
    omega
  · rfl

omit [CharP F 2] in
theorem single_not_mem_stdF (k : Ix3) : Pi.single k (1 : F) ∉ stdF F (ht k) := by
  intro h
  have h1 := (mem_stdF.mp h) k le_rfl
  simp at h1

theorem diag_of_flag_torus [Finite F] (h3 : 2 < Nat.card F) (T : (Ix3 → F) →ₗ[F] (Ix3 → F))
    (hflag : ∀ (i : ℕ) (w : Ix3 → F), w ∈ stdF F i ↔ T w ∈ stdF F i)
    (htor : ∀ s' : Fˣ × Fˣ, ∃ s : Fˣ × Fˣ, ∀ w, T (g2Act (g2T s) w) = g2Act (g2T s') (T w)) :
    ∃ δ : Ix3 → F, (∀ j, δ j ≠ 0) ∧ ∀ w, T w = diagQ δ w := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one h3
  have hx1 : ((Units.mk0 c₀ hc0 : Fˣ) : F) ≠ 1 := hc1
  have hx2 : ((Units.mk0 c₀ hc0 : Fˣ) : F) * (Units.mk0 c₀ hc0 : Fˣ) ≠ 1 := by
    intro h
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h4 : (((Units.mk0 c₀ hc0 : Fˣ) : F) - 1) ^ 2 = 0 := by
      linear_combination h + (1 - ((Units.mk0 c₀ hc0 : Fˣ) : F)) * h2
    exact hx1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4))
  have heig : ∀ (s' : Fˣ × Fˣ) (k : Ix3), ∃ μ : F,
      g2Act (g2T s') (T (Pi.single k 1)) = μ • T (Pi.single k 1) := by
    intro s' k
    obtain ⟨s, hs⟩ := htor s'
    refine ⟨chiT s k, ?_⟩
    rw [← hs, g2T_single, map_smul]
  have hk : ∀ k : Ix3, T (Pi.single k 1) k ≠ 0 := by
    intro k
    have hnot : T (Pi.single k 1) ∉ stdF F (ht k) := fun h =>
      single_not_mem_stdF k ((hflag _ _).mpr h)
    have hin : T (Pi.single k 1) ∈ stdF F (ht k + 1) := (hflag _ _).mp (single_mem_stdF k)
    obtain ⟨j₀, hj₀, hne₀⟩ : ∃ j₀, ht k ≤ ht j₀ ∧ T (Pi.single k 1) j₀ ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hnot (mem_stdF.mpr fun j hj => hh j hj)
    have hj₀k : j₀ = k := by
      apply ht_injective
      have : ¬ (ht k + 1 ≤ ht j₀) := fun h => hne₀ ((mem_stdF.mp hin) j₀ h)
      omega
    rwa [hj₀k] at hne₀
  have hT0 : ∀ k j : Ix3, j ≠ k → T (Pi.single k 1) j = 0 := by
    intro k j hjk
    by_contra hne
    obtain ⟨μ₁, e1⟩ := heig (Units.mk0 c₀ hc0, 1) k
    obtain ⟨μ₂, e2⟩ := heig (1, Units.mk0 c₀ hc0) k
    exact hjk (eq_of_eigen hx1 hx2 e1 e2 hne (hk k))
  refine ⟨fun k => T (Pi.single k 1) k, hk, fun w => ?_⟩
  have hw : w = ∑ k, w k • Pi.single k (1 : F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  funext j
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, diagQ]
  rw [Finset.sum_eq_single j]
  · ring
  · intro k _ hkj
    rw [hT0 k j (Ne.symm hkj), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

@[expose] noncomputable def g2LE (g : ↥(cayleyGroup F)) : (Ix3 → F) ≃ₗ[F] (Ix3 → F) where
  toFun := g2Act g
  invFun := g2Act g⁻¹
  map_add' := map_add (g2Act g)
  map_smul' c x := g2Act_smul g c x
  left_inv := g2Act_inv_apply g
  right_inv := g2Act_apply_inv g

theorem g2LE_apply (g : ↥(cayleyGroup F)) (w : Ix3 → F) : g2LE g w = g2Act g w := rfl

theorem eq_of_conjT (T : (Ix3 → F) ≃ₗ[F] (Ix3 → F)) {γ γ₁ γ₂ : ↥(cayleyGroup F)}
    (h₁ : ∀ w, T (g2Act γ w) = g2Act γ₁ (T w)) (h₂ : ∀ w, T (g2Act γ w) = g2Act γ₂ (T w)) :
    γ₁ = γ₂ :=
  cayley_ext fun v => by
    obtain ⟨w, rfl⟩ := T.surjective v
    rw [← h₁, h₂]

section NormAut

variable (T : (Ix3 → F) ≃ₗ[F] (Ix3 → F))
  (hT : ∀ γ : ↥(cayleyGroup F), ∃ γ' : ↥(cayleyGroup F), ∀ w, T (g2Act γ w) = g2Act γ' (T w))
include hT

@[expose] noncomputable def normAut : ↥(cayleyGroup F) →* ↥(cayleyGroup F) where
  toFun γ := (hT γ).choose
  map_one' := eq_of_conjT T (hT 1).choose_spec fun w => by
    rw [map_one]
    rfl
  map_mul' a b := eq_of_conjT T (hT (a * b)).choose_spec fun w => by
    rw [g2Act_mul_apply, (hT a).choose_spec, (hT b).choose_spec, g2Act_mul_apply]

theorem normAut_spec (γ : ↥(cayleyGroup F)) (w : Ix3 → F) :
    T (g2Act γ w) = g2Act (normAut T hT γ) (T w) :=
  (hT γ).choose_spec w

theorem normAut_eq {γ γ' : ↥(cayleyGroup F)} (h : ∀ w, T (g2Act γ w) = g2Act γ' (T w)) :
    normAut T hT γ = γ' :=
  eq_of_conjT T (normAut_spec T hT γ) h

theorem normAut_injective : Function.Injective (normAut T hT) := fun a b h =>
  cayley_ext fun w => T.injective (by rw [normAut_spec T hT a w, normAut_spec T hT b w, h])

theorem normG2_trans (g : ↥(cayleyGroup F)) :
    ∀ γ : ↥(cayleyGroup F), ∃ γ' : ↥(cayleyGroup F),
      ∀ w, (T.trans (g2LE g)) (g2Act γ w) = g2Act γ' ((T.trans (g2LE g)) w) := fun γ =>
  ⟨g * normAut T hT γ * g⁻¹, fun w => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, g2LE_apply, g2LE_apply,
      normAut_spec T hT γ w, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]⟩

theorem normAut_trans (g γ : ↥(cayleyGroup F)) :
    normAut (T.trans (g2LE g)) (normG2_trans T hT g) γ = g * normAut T hT γ * g⁻¹ :=
  normAut_eq _ _ fun w => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, g2LE_apply, g2LE_apply,
      normAut_spec T hT γ w, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]

theorem map_normAut_U0_eq [Finite F] (hU : ∀ u ∈ U0 F, normAut T hT u ∈ U0 F) :
    (U0 F).map (normAut T hT) = U0 F := by
  have := finite_cayleyGroup (F := F)
  refine Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨u, hu, rfl⟩; exact hU u hu) ?_
  rw [Subgroup.card_map_of_injective (normAut_injective T hT)]

theorem flag_of_normU0 [Finite F] (hU : ∀ u ∈ U0 F, normAut T hT u ∈ U0 F) (i : ℕ)
    (w : Ix3 → F) : w ∈ stdF F i ↔ T w ∈ stdF F i := by
  by_cases hi : 6 ≤ i
  · exact ⟨fun _ => (inF_six _).mono hi, fun _ => (inF_six _).mono hi⟩
  have hUe := map_normAut_U0_eq T hT hU
  set S : Submodule F (Ix3 → F) := (stdF F i).map T.toLinearMap with hS
  have hSst : U0Stable S := by
    rintro u hu _ ⟨y, hy, rfl⟩
    rw [← hUe] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    refine ⟨g2Act u' y, stdF_stable i u' hu' y hy, ?_⟩
    change T (g2Act u' y) = g2Act (normAut T hT u') (T y)
    exact normAut_spec T hT u' y
  have hScard : Nat.card S = Nat.card F ^ i := by
    rw [← card_stdF (by omega : i ≤ 6), hS]
    exact Nat.card_congr (Submodule.equivMapOfInjective _ T.injective _).toEquiv.symm
  have hSeq := eq_stdF_of_card hSst hScard
  constructor
  · intro hw
    rw [← hSeq]
    exact ⟨w, hw, rfl⟩
  · intro hw
    rw [← hSeq] at hw
    obtain ⟨w', hw', he⟩ := hw
    rwa [← T.injective he]

end NormAut

theorem exists_eq_smul_of_normG2 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (T : (Ix3 → F) ≃ₗ[F] (Ix3 → F))
    (hT : ∀ γ : ↥(cayleyGroup F), ∃ γ' : ↥(cayleyGroup F), ∀ w, T (g2Act γ w) = g2Act γ' (T w)) :
    ∃ (c : F) (h : ↥(cayleyGroup F)), c ≠ 0 ∧ ∀ w, T w = c • g2Act h w := by
  have := finite_cayleyGroup (F := F)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn1 : 1 ≤ n := by omega
  have hP2 : IsPGroup 2 ↥((U0 F).map (normAut T hT)) := isPGroup_U0.map _
  have hPi : ¬ 2 ∣ ((U0 F).map (normAut T hT)).index := by
    have hc : Nat.card ↥((U0 F).map (normAut T hT)) = Nat.card ↥(U0 F) :=
      Subgroup.card_map_of_injective (normAut_injective T hT)
    have h1 := ((U0 F).map (normAut T hT)).card_mul_index
    have h2 := (U0 F).card_mul_index
    rw [hc] at h1
    have hidx : ((U0 F).map (normAut T hT)).index = (U0 F).index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
    rw [hidx]
    exact not_two_dvd_index_U0 hF hn1
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow
    (IsPGroup.toSylow isPGroup_U0 (not_two_dvd_index_U0 hF hn1)) (hP2.toSylow hPi)
  rw [IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at hg
  have hT₁n := normG2_trans T hT g⁻¹
  have hU₁ : ∀ u ∈ U0 F, normAut (T.trans (g2LE g⁻¹)) hT₁n u ∈ U0 F := by
    intro u hu
    rw [normAut_trans T hT g⁻¹ u, inv_inv]
    have h1 : normAut T hT u ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (U0 F) := by
      rw [hg]
      exact ⟨u, hu, rfl⟩
    exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp h1
  have hUe₁ := map_normAut_U0_eq (T.trans (g2LE g⁻¹)) hT₁n hU₁
  have hNle : (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))).map
      (normAut (T.trans (g2LE g⁻¹)) hT₁n) ≤ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hiff : ∀ z, z ∈ U0 F ↔ z ∈ (U0 F).map (normAut (T.trans (g2LE g⁻¹)) hT₁n) :=
      fun z => by rw [hUe₁]
    rw [hiff y, hiff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨b * u * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb u).mp hu, by
        rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨u, hu, hu'⟩
      refine ⟨b⁻¹ * u * b, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) u).mp hu
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hu']
        group
  have hNe : (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))).map
      (normAut (T.trans (g2LE g⁻¹)) hT₁n) = Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hNle
      (by rw [Subgroup.card_map_of_injective (normAut_injective (T.trans (g2LE g⁻¹)) hT₁n)])
  have hUB : U0 F ≤ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := Subgroup.le_normalizer
  have hodd : Odd ((U0 F).relIndex (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)))) := by
    have h1 := not_two_dvd_index_U0 hF hn1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      h1 (h.trans (Subgroup.relIndex_dvd_index_of_le hUB)))
  have hE₂ : (torusG F).map (normAut (T.trans (g2LE g⁻¹)) hT₁n) ≤
      Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
    rw [← hNe]
    exact Subgroup.map_mono torusG_le_normalizer
  have hE₂P : U0 F ⊓ (torusG F).map (normAut (T.trans (g2LE g⁻¹)) hT₁n) = ⊥ := by
    apply U0_inf_eq_bot_of_odd
    rw [Subgroup.card_map_of_injective (normAut_injective (T.trans (g2LE g⁻¹)) hT₁n)]
    exact odd_card_torusG hF hn1
  have hE₂s : U0 F ⊔ (torusG F).map (normAut (T.trans (g2LE g⁻¹)) hT₁n) =
      Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
    have h1 : (U0 F ⊔ torusG F).map (normAut (T.trans (g2LE g⁻¹)) hT₁n) =
        U0 F ⊔ (torusG F).map (normAut (T.trans (g2LE g⁻¹)) hT₁n) := by
      rw [Subgroup.map_sup, hUe₁]
    rw [← h1, ← normalizer_U0_eq, hNe]
  obtain ⟨x, hx, hxE⟩ := CFSG.Quasithin.H13.exists_mem_conj_of_complements hUB le_rfl
    isPGroup_U0 hodd torusG_le_normalizer (U0_inf_eq_bot_of_odd (odd_card_torusG hF hn1))
    normalizer_U0_eq.symm hE₂ hE₂P hE₂s
  have hT₂n := normG2_trans (T.trans (g2LE g⁻¹)) hT₁n x⁻¹
  have hU₂ : ∀ u ∈ U0 F, normAut ((T.trans (g2LE g⁻¹)).trans (g2LE x⁻¹)) hT₂n u ∈ U0 F := by
    intro u hu
    rw [normAut_trans (T.trans (g2LE g⁻¹)) hT₁n x⁻¹ u, inv_inv]
    exact (U0 F).mul_mem ((U0 F).mul_mem ((U0 F).inv_mem hx) (hU₁ u hu)) hx
  have htor₂ : ∀ t ∈ torusG F,
      normAut ((T.trans (g2LE g⁻¹)).trans (g2LE x⁻¹)) hT₂n t ∈ torusG F := by
    intro t ht
    rw [normAut_trans (T.trans (g2LE g⁻¹)) hT₁n x⁻¹ t, inv_inv]
    have h1 : normAut (T.trans (g2LE g⁻¹)) hT₁n t ∈
        (torusG F).map (MulAut.conj x).toMonoidHom := by
      rw [← hxE]
      exact ⟨t, ht, rfl⟩
    obtain ⟨t', ht', he⟩ := h1
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show x⁻¹ * (x * t' * x⁻¹) * x = t' by group]
  set T₂ := (T.trans (g2LE g⁻¹)).trans (g2LE x⁻¹) with hT₂
  have htorE : (torusG F).map (normAut T₂ hT₂n) = torusG F :=
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨t, ht, rfl⟩; exact htor₂ t ht)
      (by rw [Subgroup.card_map_of_injective (normAut_injective T₂ hT₂n)])
  have htor : ∀ s' : Fˣ × Fˣ, ∃ s : Fˣ × Fˣ,
      ∀ w, T₂.toLinearMap (g2Act (g2T s) w) = g2Act (g2T s') (T₂.toLinearMap w) := by
    intro s'
    have h1 : g2T s' ∈ (torusG F).map (normAut T₂ hT₂n) := by
      rw [htorE]
      exact ⟨s', rfl⟩
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := h1
    refine ⟨s, fun w => ?_⟩
    change T₂ (g2Act (g2T s) w) = g2Act (g2T s') (T₂ w)
    rw [normAut_spec T₂ hT₂n, hs]
  obtain ⟨δ, hδ, hTδ⟩ := diag_of_flag_torus h3 T₂.toLinearMap
    (flag_of_normU0 T₂ hT₂n hU₂) htor
  obtain ⟨c, s, hc0, hcs⟩ := exists_eq_smul_g2T_of_diag hδ
    (γ₀ := normAut T₂ hT₂n (g2X ![1, 0, 0])) (γ₁ := normAut T₂ hT₂n (g2X ![0, 1, 0]))
    (fun w => by
      rw [← hTδ, ← hTδ]
      exact normAut_spec T₂ hT₂n _ w)
    (fun w => by
      rw [← hTδ, ← hTδ]
      exact normAut_spec T₂ hT₂n _ w)
  refine ⟨c, g * x * g2T s, hc0, fun w => ?_⟩
  have e1 : T₂ w = g2Act x⁻¹ (g2Act g⁻¹ (T w)) := rfl
  have e2 : T w = g2Act g (g2Act x (T₂ w)) := by
    rw [e1, g2Act_apply_inv, g2Act_apply_inv]
  have e3 : T₂ w = c • g2Act (g2T s) w := (hTδ w).trans (hcs w)
  rw [e2, e3, g2Act_smul, g2Act_smul, g2Act_mul_apply, g2Act_mul_apply]

end CFSG.Quasithin.Vol2.Ch11.G2Q8
