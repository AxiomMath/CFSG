module

public import CFSG.RankThree.GF2n.Tim79Model
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Quad

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

theorem Hyp79.exists_split (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {n : ℕ} (D : MulData V (conjSubgroup g V) Q (GaloisField 2 n))
    {τ : G} {a : GaloisField 2 n} (hτH : τ ∈ Q ⊔ conjSubgroup g Q)
    (hτU : τ ∈ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G)) (ha : a ≠ 1)
    (hψτ : ∀ u ∈ conjSubgroup g V, D.ψ (τ * u * τ⁻¹) = a⁻¹ * D.ψ u) {l : G}
    (hl : l ∈ Q ⊓ conjSubgroup g Q) :
    ∃ u ∈ conjSubgroup g V, ∃ l₁ ∈ Q ⊓ conjSubgroup g Q, l = u * l₁ ∧
      τ * l₁ * τ⁻¹ * l₁⁻¹ ∈ V := by
  obtain ⟨hWL, -, -, hcomm⟩ := H.L_facts hgV hgQ
  have h := H.toHyp218 hgV hgQ
  have hVW : V ≤ V ⊔ conjSubgroup g V := le_sup_left
  have hUW : conjSubgroup g V ≤ V ⊔ conjSubgroup g V := le_sup_right
  obtain ⟨v, hv, b, hb, hvb⟩ := h.exists_mul_of_mem_W (hcomm τ hτH l hl)
  have hne : a⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr fun h1 => ha (inv_eq_one.mp h1)
  set u₁ := D.uinv ((a⁻¹ - 1)⁻¹ * D.ψ b) with hu₁def
  have hu₁ : u₁ ∈ conjSubgroup g V := D.uinv_mem _
  have hψu₁ : D.ψ u₁ = (a⁻¹ - 1)⁻¹ * D.ψ b := D.ψ_uinv _
  have hτu₁ : τ * u₁ * τ⁻¹ ∈ conjSubgroup g V := (Subgroup.mem_normalizer_iff.mp hτU u₁).mp hu₁
  have hcu : τ * u₁ * τ⁻¹ * u₁⁻¹ ∈ conjSubgroup g V :=
    Subgroup.mul_mem _ hτu₁ (Subgroup.inv_mem _ hu₁)
  have hc1 : τ * u₁ * τ⁻¹ * u₁⁻¹ * b = 1 := by
    refine D.ψ_inj _ (Subgroup.mul_mem _ hcu hb) ?_
    rw [D.ψ_add _ hcu b hb, D.ψ_add _ hτu₁ _ (Subgroup.inv_mem _ hu₁), hψτ u₁ hu₁,
      map_inv_of_additive D.ψ_add hu₁, hψu₁]
    have e : a⁻¹ * ((a⁻¹ - 1)⁻¹ * D.ψ b) + -((a⁻¹ - 1)⁻¹ * D.ψ b) = D.ψ b := by
      calc a⁻¹ * ((a⁻¹ - 1)⁻¹ * D.ψ b) + -((a⁻¹ - 1)⁻¹ * D.ψ b)
          = ((a⁻¹ - 1) * (a⁻¹ - 1)⁻¹) * D.ψ b := by ring
        _ = D.ψ b := by rw [mul_inv_cancel₀ hne, one_mul]
    rw [e]
    exact CharTwo.add_self_eq_zero _
  have hl₁ : u₁ * l ∈ Q ⊓ conjSubgroup g Q :=
    Subgroup.mul_mem _ (hWL (hUW hu₁)) hl
  refine ⟨u₁⁻¹, Subgroup.inv_mem _ hu₁, u₁ * l, hl₁, by group, ?_⟩
  have hcomm1 : (τ * u₁ * τ⁻¹ * u₁⁻¹) * v = v * (τ * u₁ * τ⁻¹ * u₁⁻¹) :=
    h.W_comm (hUW hcu) (hVW hv) |>.trans rfl
  have huw : u₁ * (v * b) = (v * b) * u₁ :=
    h.W_comm (hUW hu₁) (Subgroup.mul_mem _ (hVW hv) (hUW hb))
  have e1 : τ * (u₁ * l) * τ⁻¹ * (u₁ * l)⁻¹ =
      (τ * u₁ * τ⁻¹ * u₁⁻¹) * (u₁ * ⁅τ, l⁆ * u₁⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1, hvb, huw, show (v * b) * u₁ * u₁⁻¹ = v * b by group, ← mul_assoc, hcomm1, mul_assoc,
    hc1, mul_one]
  exact hv

theorem Hyp79.commute_L_of_fixed (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {n : ℕ} (D : MulData V (conjSubgroup g V) Q (GaloisField 2 n))
    {τ : G} {a : GaloisField 2 n} (hτH : τ ∈ Q ⊔ conjSubgroup g Q)
    (hτQ : τ ∈ Subgroup.normalizer (Q : Set G))
    (hτU : τ ∈ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G)) (ha : a ≠ 1)
    (hψτ : ∀ u ∈ conjSubgroup g V, D.ψ (τ * u * τ⁻¹) = a⁻¹ * D.ψ u)
    (hconj : ∀ y ∈ classGroup V Q D.γ, τ * y * τ⁻¹ ∈ classGroup V Q D.γ)
    (hconj' : ∀ y ∈ classGroup V Q D.γ, τ⁻¹ * y * τ ∈ classGroup V Q D.γ) {x : G}
    (hx : x ∈ classGroup V Q D.γ) (hxU : ∀ u ∈ conjSubgroup g V, x * u = u * x)
    (hfix : ∀ y ∈ classGroup V Q D.γ, τ * y * τ⁻¹ * y⁻¹ ∈ V → x * y = y * x) :
    ∀ l ∈ Q ⊓ conjSubgroup g Q, x * l = l * x := by
  intro l hl
  obtain ⟨u, hu, l₁, hl₁, rfl, hτl₁⟩ := H.exists_split hgV hgQ D hτH hτU ha hψτ hl
  have hQF := H.eq_classGroup_sup_centralizer D ⟨g, rfl⟩ hgQ hgV
  have hC := H.modelCtx D
  have hnorm : Q ⊓ Subgroup.centralizer (classGroup V Q D.γ : Set G) ≤
      Subgroup.normalizer (classGroup V Q D.γ : Set G) :=
    fun w hw => Subgroup.centralizer_le_normalizer _ hw.2
  obtain ⟨y, hy, y', hy', hl₁eq⟩ := exists_mul_of_mem_sup hnorm (hQF.le hl₁.1)
  subst hl₁eq
  have hyQ : y ∈ Q := classGroup_le hC.V_le hy
  have hy'cent : ∀ z ∈ classGroup V Q D.γ, z * y' = y' * z :=
    Subgroup.mem_centralizer_iff.mp hy'.2
  have hA'Q : τ * y' * τ⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hτQ y').mp hy'.1
  have hA'cent : ∀ z ∈ classGroup V Q D.γ, z * (τ * y' * τ⁻¹) = (τ * y' * τ⁻¹) * z := by
    intro z hz
    have h1 := hy'cent _ (hconj' z hz)
    calc z * (τ * y' * τ⁻¹) = τ * ((τ⁻¹ * z * τ) * y') * τ⁻¹ := by group
      _ = τ * (y' * (τ⁻¹ * z * τ)) * τ⁻¹ := by rw [h1]
      _ = (τ * y' * τ⁻¹) * z := by group
  have hA'mem : τ * y' * τ⁻¹ ∈ Q ⊓ Subgroup.centralizer (classGroup V Q D.γ : Set G) :=
    ⟨hA'Q, Subgroup.mem_centralizer_iff.mpr hA'cent⟩
  set w := τ * (y * y') * τ⁻¹ * (y * y')⁻¹ with hw
  have hwV : w ∈ V := hτl₁
  have hzeq : y⁻¹ * w⁻¹ * (τ * y * τ⁻¹) = y' * (τ * y' * τ⁻¹)⁻¹ := by
    simp only [hw]
    group
  have hzQF : y⁻¹ * w⁻¹ * (τ * y * τ⁻¹) ∈ classGroup V Q D.γ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy)
      (Subgroup.inv_mem _ (V_le_classGroup hwV))) (hconj y hy)
  have hzC : y⁻¹ * w⁻¹ * (τ * y * τ⁻¹) ∈
      Q ⊓ Subgroup.centralizer (classGroup V Q D.γ : Set G) := by
    rw [hzeq]
    exact Subgroup.mul_mem _ hy' (Subgroup.inv_mem _ hA'mem)
  have hzV : y⁻¹ * w⁻¹ * (τ * y * τ⁻¹) ∈ V := by
    refine hC.center_le _ hzC.1 fun w' hw' => ?_
    obtain ⟨y₂, hy₂, y₂', hy₂', rfl⟩ := exists_mul_of_mem_sup hnorm (hQF.le hw')
    have h1 : y₂ * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) = (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y₂ :=
      (Subgroup.mem_centralizer_iff.mp hzC.2 y₂ hy₂)
    have h2 : (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y₂' = y₂' * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) :=
      (Subgroup.mem_centralizer_iff.mp hy₂'.2 _ hzQF)
    calc (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * (y₂ * y₂')
        = ((y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y₂) * y₂' := by group
      _ = (y₂ * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹))) * y₂' := by rw [h1]
      _ = y₂ * ((y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y₂') := by group
      _ = y₂ * (y₂' * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹))) := by rw [h2]
      _ = (y₂ * y₂') * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) := by group
  have hτy : τ * y * τ⁻¹ * y⁻¹ ∈ V := by
    have hcz : (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y = y * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) :=
      H.V_central hzV hyQ
    have e : τ * y * τ⁻¹ * y⁻¹ = w * (y * (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y⁻¹) := by group
    rw [e, ← hcz, show (y⁻¹ * w⁻¹ * (τ * y * τ⁻¹)) * y * y⁻¹ = y⁻¹ * w⁻¹ * (τ * y * τ⁻¹) by group]
    exact Subgroup.mul_mem _ hwV hzV
  have hxy : x * y = y * x := hfix y hy hτy
  have hxl₁ : x * (y * y') = (y * y') * x := by
    calc x * (y * y') = (x * y) * y' := by group
      _ = (y * x) * y' := by rw [hxy]
      _ = y * (x * y') := by group
      _ = y * (y' * x) := by rw [hy'cent x hx]
      _ = (y * y') * x := by group
  calc x * (u * (y * y')) = (x * u) * (y * y') := by group
    _ = (u * x) * (y * y') := by rw [hxU u hu]
    _ = u * (x * (y * y')) := by group
    _ = u * ((y * y') * x) := by rw [hxl₁]
    _ = (u * (y * y')) * x := by group

theorem Hyp79.exists_hyperbolic_quadModel (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    ∃ n : ℕ, Nat.card V = 2 ^ n ∧ ∃ D : MulData V (conjSubgroup g V) Q (GaloisField 2 n),
      ∃ M₀ : QuadModel (classGroup V Q D.γ) V (GaloisField 2 n) D.γ,
        ∃ S₁ S₂ : Submodule (GaloisField 2 n) M₀.E, IsCompl S₁ S₂ ∧
          (∀ x ∈ S₁, M₀.Qf x = 0) ∧ ∀ x ∈ S₂, M₀.Qf x = 0 := by
  obtain ⟨n, hVn, D, τ, a, hτM, hτH, hτU, hτo, hao, hγτ, hψτ, -⟩ :=
    H.exists_mulData_torus hgV hgQ
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push Not at hcon
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := H.q4
    omega
  have hKcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hao
    omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    omega
  obtain ⟨M₀, ⟨e₀, ℓ, hπU, hℓt, hBℓ⟩, hclause⟩ := H.exists_quadModel ⟨g, rfl⟩ hgQ hgV D
  have h218 := H.toHyp218 hgV hgQ
  have hτV : τ ∈ Subgroup.normalizer (V : Set G) := h218.M_le_normalizer hτM
  have hτQ : τ ∈ Subgroup.normalizer (Q : Set G) := h218.M_le_normalizer_Q hτM
  obtain ⟨τE, hτE, hτEB, hτEQ⟩ := hclause τ hτM a hγτ
  refine ⟨n, hVn, D, M₀, ?_⟩
  have hU₀cl : conjSubgroup g V ≤ classGroup V Q D.γ :=
    le_classGroup_of_mem (mem_classOf_self D ⟨g, rfl⟩ hgQ hgV)
  have hVU : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgV
  have hu₀U : D.uinv 1 ∈ conjSubgroup g V := D.uinv_mem 1
  have hψu₀ : D.ψ (D.uinv 1) = 1 := D.ψ_uinv 1
  have hu₀cl : D.uinv 1 ∈ classGroup V Q D.γ := hU₀cl hu₀U
  have he₀ : M₀.π (D.uinv 1) = e₀ := by rw [hπU _ hu₀U, hψu₀, one_smul]
  have hu₀sq : D.uinv 1 * D.uinv 1 = 1 :=
    D.ψ_inj _ (Subgroup.mul_mem _ hu₀U hu₀U) (by
      rw [D.ψ_add _ hu₀U _ hu₀U, hψu₀]
      exact CharTwo.add_self_eq_zero 1)
  have he₀ne : e₀ ≠ 0 := by
    intro h0
    rw [← he₀] at h0
    have hu₀V : D.uinv 1 ∈ V := (M₀.π_ker _ hu₀cl).mp h0
    have h1 : D.uinv 1 ∈ V ⊓ conjSubgroup g V := ⟨hu₀V, hu₀U⟩
    rw [hVU, Subgroup.mem_bot] at h1
    rw [h1, D.ψ_one] at hψu₀
    exact zero_ne_one hψu₀
  have hQe₀ : M₀.Qf e₀ = 0 := by
    rw [← he₀, ← M₀.sq_eq _ hu₀cl, pow_two, hu₀sq, D.γ_one]
  have hτe₀ : τE e₀ = a⁻¹ • e₀ := by
    have h1 := (hτE _ hu₀cl).2
    rw [he₀] at h1
    have hmem : τ * D.uinv 1 * τ⁻¹ ∈ conjSubgroup g V :=
      (Subgroup.mem_normalizer_iff.mp hτU _).mp hu₀U
    rw [← h1, hπU _ hmem, hψτ _ hu₀U, hψu₀, mul_one]
  have hconj : ∀ y ∈ classGroup V Q D.γ, τ * y * τ⁻¹ ∈ classGroup V Q D.γ :=
    fun y hy => (hτE y hy).1
  have hγ' : ∀ v ∈ V, D.γ (τ⁻¹ * v * τ⁻¹⁻¹) = a⁻¹ * D.γ v := fun v hv => by
    simpa using gamma_conj_inv hτV ha0 hγτ hv
  have hconj' : ∀ y ∈ classGroup V Q D.γ, τ⁻¹ * y * τ ∈ classGroup V Q D.γ := fun y hy => by
    simpa using conj_mem_classGroup (inv_mem hτV) (inv_mem hτQ) (inv_ne_zero ha0) hγ' hy
  have hpow : ∀ k : ℕ, ∀ y ∈ classGroup V Q D.γ,
      τ ^ k * y * (τ ^ k)⁻¹ ∈ classGroup V Q D.γ ∧
        M₀.π (τ ^ k * y * (τ ^ k)⁻¹) = (τE.toLinearMap ^ k) (M₀.π y) := by
    intro k
    induction k with
    | zero =>
      intro y hy
      simp [hy]
    | succ k ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      have e : τ ^ (k + 1) * y * (τ ^ (k + 1))⁻¹ = τ * (τ ^ k * y * (τ ^ k)⁻¹) * τ⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e]
      obtain ⟨h3, h4⟩ := hτE _ h1
      refine ⟨h3, ?_⟩
      rw [h4, h2, pow_succ', Module.End.mul_apply]
      rfl
  have hτpow : ∀ e : M₀.E,
      (τE.toLinearMap ^ (Nat.card (GaloisField 2 n) - 1)) e = e := by
    intro e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
    have hk : τ ^ (2 ^ n - 1) = 1 := by
      rw [← hτo]
      exact pow_orderOf_eq_one τ
    have h := (hpow (2 ^ n - 1) y hy).2
    rw [hk, inv_one, one_mul, mul_one] at h
    rw [hKcard]
    exact h.symm
  have hsq : (a ^ (Nat.card (GaloisField 2 n) / 2)) ^ 2 = a := by
    haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h2 : Fintype.card (GaloisField 2 n) % 2 = 0 :=
      FiniteField.even_card_iff_char_two.mp (ringChar.eq (GaloisField 2 n) 2)
    rw [← pow_mul, Nat.card_eq_fintype_card, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)]
    exact FiniteField.pow_card a
  have hμ : a ^ (Nat.card (GaloisField 2 n) / 2) ≠ a := by
    intro h
    rw [h] at hsq
    exact ha1 (mul_left_cancel₀ ha0 (by rw [← pow_two, hsq, mul_one]))
  have hfixOf : ∀ x₁ : G, x₁ ∈ classGroup V Q D.γ →
      τE.toLinearMap (M₀.π x₁) = a ^ (Nat.card (GaloisField 2 n) / 2) • M₀.π x₁ →
      ∀ y ∈ classGroup V Q D.γ, τ * y * τ⁻¹ * y⁻¹ ∈ V → x₁ * y = y * x₁ := by
    intro x₁ hx₁ hxμ y hy hτy
    have hπy : τE (M₀.π y) = M₀.π y := by
      have h1 := (hτE y hy).2
      have e : τ * y * τ⁻¹ = (τ * y * τ⁻¹ * y⁻¹) * y := by group
      have h2 : M₀.π (τ * y * τ⁻¹) = M₀.π y := by
        rw [e, M₀.π_mul _ (V_le_classGroup hτy) y hy,
          (M₀.π_ker _ (V_le_classGroup hτy)).mpr hτy, zero_add]
      rw [← h1, h2]
    have h3 := hτEB (M₀.π x₁) (M₀.π y)
    rw [show τE (M₀.π x₁) = a ^ (Nat.card (GaloisField 2 n) / 2) • M₀.π x₁ from hxμ, hπy,
      map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
    have hB : M₀.B (M₀.π x₁) (M₀.π y) = 0 := by
      rcases mul_eq_mul_right_iff.mp h3 with h4 | h4
      · exact absurd h4 hμ
      · exact h4
    have h5 : D.γ ⁅x₁, y⁆ = 0 := by rw [M₀.comm_eq x₁ hx₁ y hy]; exact hB
    exact commutatorElement_eq_one_iff_mul_comm.mp (D.γ_inj _ (M₀.comm_mem x₁ hx₁ y hy) h5)
  have hiso : ∀ x y : M₀.E, M₀.B e₀ x = 0 → M₀.B e₀ y = 0 →
      τE.toLinearMap x = a ^ (Nat.card (GaloisField 2 n) / 2) • x →
      τE.toLinearMap y = a ^ (Nat.card (GaloisField 2 n) / 2) • y → M₀.B x y = 0 := by
    intro x y hx0 hy0 hxμ hyμ
    obtain ⟨x₁, hx₁, rfl⟩ := M₀.π_surj x
    obtain ⟨y₁, hy₁, rfl⟩ := M₀.π_surj y
    have hxQ : x₁ ∈ Q := classGroup_le H.V_le_Q hx₁
    have hyQ : y₁ ∈ Q := classGroup_le H.V_le_Q hy₁
    have hxt : D.t x₁ = 0 := by rw [hℓt x₁ hx₁, ← hBℓ]; exact hx0
    have hyt : D.t y₁ = 0 := by rw [hℓt y₁ hy₁, ← hBℓ]; exact hy0
    have hxU : ∀ u ∈ conjSubgroup g V, x₁ * u = u * x₁ := fun u hu =>
      (Subgroup.mem_centralizer_iff.mp ((D.t_ker x₁ hxQ).mp hxt) u hu).symm
    have hyU : ∀ u ∈ conjSubgroup g V, y₁ * u = u * y₁ := fun u hu =>
      (Subgroup.mem_centralizer_iff.mp ((D.t_ker y₁ hyQ).mp hyt) u hu).symm
    have hxL := H.commute_L_of_fixed hgV hgQ D hτH hτQ hτU ha1 hψτ hconj hconj' hx₁ hxU
      (hfixOf x₁ hx₁ hxμ)
    have hyL := H.commute_L_of_fixed hgV hgQ D hτH hτQ hτU ha1 hψτ hconj hconj' hy₁ hyU
      (hfixOf y₁ hy₁ hyμ)
    have hcom := H.centralizer_L_abelian hgV hgQ x₁ hxQ hxL y₁ hyQ hyL
    rw [← M₀.comm_eq x₁ hx₁ y₁ hy₁, commutatorElement_eq_one_iff_mul_comm.mpr hcom, D.γ_one]
  exact exists_isCompl_totallySingular_of_eigenvector M₀.B M₀.Qf M₀.alt M₀.nondeg M₀.Qf_smul
    M₀.Qf_add τE.toLinearMap a ha0 hτEB hτEQ hτpow e₀ a⁻¹ he₀ne hQe₀ hτe₀ hiso

end CFSG.RankThree.GF2n.Tim79
