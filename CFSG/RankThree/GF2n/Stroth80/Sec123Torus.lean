module

public import CFSG.RankThree.GF2n.Smith81.Lin26Torus

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.torus_model (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hb0 : b ≠ 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {x : G} (hxX : x ∈ Q ⊔ QB B) (hxZ : x ∈ Subgroup.normalizer (Z : Set G))
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) :
    ∃ (a : Kˣ) (T : M₀.E ≃ₗ[K] M₀.E), (∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)) ∧
      (∀ z ∈ Z, γ (x * z * x⁻¹) = (a : K) * γ z) ∧
      (∀ e, M₀.Qf (T e) = (a : K) * M₀.Qf e) ∧ T b = (((a⁻¹ : Kˣ)) : K) • b := by
  classical
  have hxM : x ∈ M := by rw [← hc.hyp.normalizer_Z.1]; exact hxZ
  obtain ⟨σ, a, T, hT1, hTπ, hTγ, hTQ⟩ := h.act x hxM
  obtain ⟨y₀, hy₀B, hy₀Q, hy₀b⟩ := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  have hxy₀ : x * y₀ * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hxB y₀).mp hy₀B
  have hxy₀Q : x * y₀ * x⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hxM).1 y₀ hy₀Q
  obtain ⟨ρ, hρ⟩ := (hB (T b)).mp (by
    rw [← hy₀b, ← hTπ y₀ hy₀Q]
    exact M₀.pi_mem_img hxy₀ hxy₀Q)
  obtain ⟨f, hf⟩ : ∃ f : M₀.E, M₀.B b f = 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ f, M₀.B b f = 0 := by
      intro f
      by_contra hne
      exact hcon ((M₀.B b f)⁻¹ • f) (by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne])
    exact hb0 (M₀.nondeg b h0)
  have hxinvZ : ∀ z ∈ Z, x⁻¹ * z * x ∈ Z := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxZ) z).mp hz
    simpa using this
  have key : ∀ β : K, ρ * β = σ.symm ((a : K)⁻¹ * β) := by
    intro β
    obtain ⟨g, hgQ, hg⟩ := M₀.π_surj (β • f)
    have hBβ : M₀.B b (M₀.π g) = β := by rw [hg, map_smul, hf, smul_eq_mul, mul_one]
    have htc := CFSG.RankThree.GF2n.Smith81.Ctx.torus_comm hc hxX hxZ hxB hy₀B hgQ
    have hz : ⁅y₀, g⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy₀Q hgQ
    have hγz : γ ⁅y₀, g⁆ = β := by rw [M₀.comm_eq y₀ hy₀Q g hgQ, hy₀b, hBβ]
    have hL : γ ⁅x * y₀ * x⁻¹, g⁆ = ρ * β := by
      rw [M₀.comm_eq _ hxy₀Q g hgQ, hTπ y₀ hy₀Q, hy₀b, hρ, map_smul, LinearMap.smul_apply, hBβ,
        smul_eq_mul]
    have hz' : x⁻¹ * ⁅y₀, g⁆ * x ∈ Z := hxinvZ _ hz
    have h2 := hTγ _ hz'
    have e2 : x * (x⁻¹ * ⁅y₀, g⁆ * x) * x⁻¹ = ⁅y₀, g⁆ := by group
    rw [e2, hγz] at h2
    rw [htc] at hL
    rw [hL] at h2
    have h3 : σ (ρ * β) = (a : K)⁻¹ * β :=
      ((inv_mul_eq_iff_eq_mul₀ a.ne_zero).mpr h2).symm
    rw [← h3, RingEquiv.symm_apply_apply]
  have hρ1 : ρ = σ.symm ((a : K)⁻¹) := by simpa using key 1
  have hρ0 : ρ ≠ 0 := by
    rw [hρ1]
    exact (map_ne_zero σ.symm).mpr (inv_ne_zero a.ne_zero)
  have hσs : ∀ β : K, σ.symm β = β := by
    intro β
    have h1 := key β
    rw [map_mul, ← hρ1] at h1
    exact (mul_left_cancel₀ hρ0 h1).symm
  have hσ : ∀ c : K, σ c = c := by
    intro c
    have h1 := hσs (σ c)
    rw [RingEquiv.symm_apply_apply] at h1
    exact h1.symm
  refine ⟨a, AddEquiv.toLinearEquiv T (fun c e => by rw [hT1, hσ c]), hTπ, ?_, ?_, ?_⟩
  · intro z hz
    rw [hTγ z hz, hσ]
  · intro e
    show M₀.Qf (T e) = _
    rw [hTQ, hσ]
  · show T b = _
    rw [hρ, hρ1, hσs]
    simp


theorem GlobalModelData.gamma_inj (h : GlobalModelData M Q Z γ M₀) {z z' : G} (hz : z ∈ Z)
    (hz' : z' ∈ Z) (he : γ z = γ z') : z = z' := by
  have h1 : γ (z⁻¹ * z) = γ z⁻¹ + γ z := h.reg.add _ (Z.inv_mem hz) _ hz
  rw [inv_mul_cancel, h.reg.one] at h1
  have h2 : γ (z⁻¹ * z') = γ z⁻¹ + γ z' := h.reg.add _ (Z.inv_mem hz) _ hz'
  rw [← he, ← h1] at h2
  have := h.reg.inj _ (Z.mul_mem (Z.inv_mem hz) hz') h2
  calc z = z * (z⁻¹ * z') := by rw [this, mul_one]
    _ = z' := by group

theorem Ctx.exists_torusOrd (hc : Ctx M Q Z B) :
    ∃ y : G, y ∈ Q ⊔ QB B ∧ y ∈ M ∧ y ∈ Subgroup.normalizer (B : Set G) ∧
      y ∈ Subgroup.normalizer (Z : Set G) ∧ orderOf y = Nat.card Z - 1 ∧
      ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ v ∈ Z, y ^ i * v = v * y ^ i → v = 1 := by
  classical
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, hb0, hbQ, hB, -, -⟩ := hc.dictB h
  obtain ⟨x, hxX, hxZ, hxB, hreg⟩ := CFSG.RankThree.GF2n.Smith81.Ctx.exists_torus hc
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hxM : x ∈ M := by rw [← hc.hyp.normalizer_Z.1]; exact hxZ
  obtain ⟨a, T, hTπ, hTγ, hTQ, hTb⟩ := hc.torus_model h hb0 hB hxX hxZ hxB
  have hxpowZ : ∀ (j : ℕ), ∀ z ∈ Z, x ^ j * z * (x ^ j)⁻¹ ∈ Z := fun j z hz =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxZ j) z).mp hz
  have hγpow : ∀ (j : ℕ), ∀ z ∈ Z, γ (x ^ j * z * (x ^ j)⁻¹) = (a : K) ^ j * γ z := by
    intro j
    induction j with
    | zero => intro z hz; simp
    | succ j ih =>
      intro z hz
      have e : x ^ (j + 1) * z * (x ^ (j + 1))⁻¹ = x * (x ^ j * z * (x ^ j)⁻¹) * x⁻¹ := by
        rw [pow_succ']; group
      rw [e, hTγ _ (hxpowZ j z hz), ih z hz, pow_succ]
      ring
  obtain ⟨v₀, hv₀Z, hv₀⟩ : ∃ v ∈ Z, v ≠ 1 := by
    have h1 : 1 < Nat.card Z := by omega
    obtain ⟨⟨v, hv⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      ((Subgroup.one_lt_card_iff_ne_bot Z).mp h1)
    exact ⟨v, hv, fun he => hne (Subtype.ext he)⟩
  have hγv₀ : γ v₀ ≠ 0 := fun h0 => hv₀ (h.gamma_inj hv₀Z Z.one_mem (h0.trans h.reg.one.symm))
  have hfix : ∀ j : ℕ, (a : K) ^ j = 1 ↔ ∀ z ∈ Z, x ^ j * z * (x ^ j)⁻¹ = z := by
    intro j
    constructor
    · intro hj z hz
      exact h.gamma_inj (hxpowZ j z hz) hz (by rw [hγpow j z hz, hj, one_mul])
    · intro hj
      have := hγpow j v₀ hv₀Z
      rw [hj v₀ hv₀Z] at this
      exact (mul_right_cancel₀ hγv₀ (by rw [← this, one_mul])).symm
  have hq1 : Nat.card Kˣ = Nat.card Z - 1 := by rw [Nat.card_units, h.card]
  have haqU : a ^ (Nat.card Z - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := a)
    rwa [hq1] at this
  have haq : (a : K) ^ (Nat.card Z - 1) = 1 := by simpa using congrArg Units.val haqU
  have haord : orderOf a = Nat.card Z - 1 := by
    refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun m hm hm0 hm1 => ?_⟩
    · exact haqU
    · have h1 : (a : K) ^ m = 1 := by simpa using congrArg Units.val hm1
      have h2 := (hfix m).mp h1 v₀ hv₀Z
      have h3 : x ^ m * v₀ = v₀ * x ^ m := by
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2
      exact hv₀ (hreg m hm0 hm v₀ hv₀Z h3)
  have hdvd : Nat.card Z - 1 ∣ orderOf x := by
    rw [← haord]
    refine orderOf_dvd_of_pow_eq_one (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (hfix _).mpr fun z hz => by rw [pow_orderOf_eq_one]; simp
  set w : G := x ^ (Nat.card Z - 1) with hw
  have hwX : w ∈ Q ⊔ QB B := Subgroup.pow_mem _ hxX _
  have hwZ : w ∈ Subgroup.normalizer (Z : Set G) := Subgroup.pow_mem _ hxZ _
  have hwB : w ∈ Subgroup.normalizer (B : Set G) := Subgroup.pow_mem _ hxB _
  have hwcZ : ∀ z ∈ Z, w * z * w⁻¹ = z := by
    intro z hz
    have := (hfix (Nat.card Z - 1)).mp haq z hz
    simpa [hw] using this
  have hwcB : ∀ y ∈ B, w * y * w⁻¹ = y := by
    intro y hy
    obtain ⟨aw, Tw, hTπw, hTγw, -, hTbw⟩ := hc.torus_model h hb0 hB hwX hwZ hwB
    have haw : (aw : K) = 1 := by
      have h1 := hTγw v₀ hv₀Z
      rw [hwcZ v₀ hv₀Z] at h1
      exact (mul_right_cancel₀ hγv₀ (by rw [← h1, one_mul])).symm
    have hawu : aw = 1 := Units.ext haw
    rw [hawu] at hTbw
    simp only [inv_one, Units.val_one, one_smul] at hTbw
    have hyQ : y ∈ Q := hc.le hy
    obtain ⟨s, hs⟩ := (hB (M₀.π y)).mp (M₀.pi_mem_img hy hyQ)
    have hwyB : w * y * w⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hwB y).mp hy
    have hwyQ : w * y * w⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M (hw ▸ Subgroup.pow_mem _ hxM _)).1 y hyQ
    have h1 : M₀.π (w * y * w⁻¹) = M₀.π y := by
      rw [hTπw y hyQ, hs, map_smul, hTbw]
    have h2 := (Tim79.QuadModel.pi_eq_iff M₀ hwyQ hyQ).mp h1
    have h3 : (w * y * w⁻¹)⁻¹ * y ∈ Z ⊓ B :=
      ⟨h2, B.mul_mem (B.inv_mem hwyB) hy⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
    calc w * y * w⁻¹ = w * y * w⁻¹ * ((w * y * w⁻¹)⁻¹ * y) := by rw [h3, mul_one]
      _ = y := by group
  have hwC : w ∈ Subgroup.centralizer ((Z ⊔ B : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    obtain ⟨z, hz, y, hy, rfl⟩ := (Ctx.mem_sup_iff hc).mp hu
    have e : w * (z * y) * w⁻¹ = z * y := by
      calc w * (z * y) * w⁻¹ = (w * z * w⁻¹) * (w * y * w⁻¹) := by group
        _ = z * y := by rw [hwcZ z hz, hwcB y hy]
    calc z * y * w = (w * (z * y) * w⁻¹) * w := by rw [e]
      _ = w * (z * y) := by group
  obtain ⟨-, -, -, hC⟩ := hc.inducesSL2
  have hwmem : w ∈ inSubgroup (pCore 2) (Q ⊔ QB B) := by
    rw [← hC]
    exact ⟨hwX, hwC⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ, orderOf w = 2 ^ f := by
    obtain ⟨w', hw', hww'⟩ := Subgroup.mem_map.mp hwmem
    obtain ⟨f, hf⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(Q ⊔ QB B)))) ⟨w', hw'⟩
    refine ⟨f, ?_⟩
    rw [← hww']
    have e1 : orderOf (⟨w', hw'⟩ : ↥(pCore 2 ↥(Q ⊔ QB B))) = orderOf w' :=
      (Subgroup.orderOf_coe _).symm
    have e2 : orderOf ((Q ⊔ QB B).subtype w') = orderOf w' := Subgroup.orderOf_coe w'
    rw [e2, ← e1, hf]
  have hodd : Odd (Nat.card Z - 1) := by
    obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hr
      omega
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    obtain ⟨c, hc'⟩ := (Nat.even_pow.mpr ⟨even_two, hr0⟩ : Even (2 ^ r))
    exact ⟨c - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ f) (Nat.card Z - 1) :=
    Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr hodd)
  have hn : orderOf x = 2 ^ f * (Nat.card Z - 1) := by
    have h1 : orderOf w = orderOf x / (Nat.card Z - 1) := orderOf_pow_of_dvd (by omega) hdvd
    rw [hf] at h1
    rw [h1]
    exact (Nat.div_mul_cancel hdvd).symm
  have h2f : 2 ^ f ∣ orderOf x := ⟨Nat.card Z - 1, hn⟩
  refine ⟨x ^ (2 ^ f), Subgroup.pow_mem _ hxX _, Subgroup.pow_mem _ hxM _,
    Subgroup.pow_mem _ hxB _, Subgroup.pow_mem _ hxZ _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (by positivity) h2f, hn]
    exact Nat.mul_div_cancel_left _ (by positivity)
  · intro i hi0 hi v hv hcomm
    by_contra hv1
    have hγv : γ v ≠ 0 := fun h0 => hv1 (h.gamma_inj hv Z.one_mem (h0.trans h.reg.one.symm))
    have h1 := hγpow (2 ^ f * i) v hv
    have e : x ^ (2 ^ f * i) * v * (x ^ (2 ^ f * i))⁻¹ = v := by
      rw [pow_mul, mul_inv_eq_iff_eq_mul]
      exact hcomm
    rw [e] at h1
    have h2 : (a : K) ^ (2 ^ f * i) = 1 := by
      exact (mul_left_inj' hγv).mp (by rw [one_mul]; exact h1.symm)
    have h3 : Nat.card Z - 1 ∣ 2 ^ f * i := by
      rw [← haord]
      exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h2))
    have h4 : Nat.card Z - 1 ∣ i := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h3)
    have := Nat.le_of_dvd hi0 h4
    omega


theorem torus_gamma_pow {x : G} (hxZ' : x ∈ Subgroup.normalizer (Z : Set G)) {a : K}
    (hTγ : ∀ z ∈ Z, γ (x * z * x⁻¹) = a * γ z) (j : ℕ) :
    ∀ z ∈ Z, x ^ j * z * (x ^ j)⁻¹ ∈ Z ∧ γ (x ^ j * z * (x ^ j)⁻¹) = a ^ j * γ z := by
  induction j with
  | zero => intro z hz; simpa using hz
  | succ j ih =>
    intro z hz
    obtain ⟨ih1, ih2⟩ := ih z hz
    have e : x ^ (j + 1) * z * (x ^ (j + 1))⁻¹ = x * (x ^ j * z * (x ^ j)⁻¹) * x⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hxZ' _).mp ih1, ?_⟩
    rw [hTγ _ ih1, ih2, pow_succ]
    ring

end CFSG.RankThree.GF2n.Stroth80
