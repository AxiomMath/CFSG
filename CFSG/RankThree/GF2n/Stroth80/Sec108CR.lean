module

public import CFSG.RankThree.GF2n.Stroth80.Sec108End

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem eq_one_of_pow_two_pow {K : Type} [Field K] [CharP K 2] {c : K} {k : ℕ}
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : (c - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h1)

private theorem gamma_conj_pow {K : Type} [Field K] {γ : G → K} {x : G}
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) {a : K}
    (hγ : ∀ z ∈ Z, γ (x * z * x⁻¹) = a * γ z) (j : ℕ) :
    ∀ z ∈ Z, γ (x ^ j * z * (x ^ j)⁻¹) = a ^ j * γ z := by
  induction j with
  | zero => intro z _; simp
  | succ j ih =>
    intro z hz
    have hw : x ^ j * z * (x ^ j)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxZ j) z).mp hz
    have e : x ^ (j + 1) * z * (x ^ (j + 1))⁻¹ = x * (x ^ j * z * (x ^ j)⁻¹) * x⁻¹ := by
      rw [pow_succ']; group
    rw [e, hγ _ hw, ih z hz, pow_succ]
    ring

private theorem T_phi (hc : Ctx M Q Z B) (AM : Smith81.Smith23E1.ActionModel M Q Z) {x : G}
    (hx : x ∈ M) {T : AM.M₀.E ≃+ AM.M₀.E}
    (hπ : ∀ v ∈ Q, AM.M₀.π (x * v * x⁻¹) = T (AM.M₀.π v)) (m : ↥(H0 M Z))
    (h : ⁅x, (m : G)⁆ ∈ Q) (e : AM.M₀.E) : T (AM.φ m e) = AM.φ m (T e) := by
  obtain ⟨v, hv, rfl⟩ := AM.M₀.π_surj e
  have hmvQ : (m : G) * v * (m : G)⁻¹ ∈ Q := conj_mem_Q hc.hyp m.2.1 hv
  have hxvQ : x * v * x⁻¹ ∈ Q := conj_mem_Q hc.hyp hx hv
  have hmxvQ : (m : G) * (x * v * x⁻¹) * (m : G)⁻¹ ∈ Q := conj_mem_Q hc.hyp m.2.1 hxvQ
  have hq1 : AM.φ ⟨⁅x, (m : G)⁆, hc.Q_le_H0 h⟩ = 1 := (AM.φ_ker _).mpr h
  have e : x * ((m : G) * v * (m : G)⁻¹) * x⁻¹ =
      ⁅x, (m : G)⁆ * ((m : G) * (x * v * x⁻¹) * (m : G)⁻¹) * ⁅x, (m : G)⁆⁻¹ := by
    rw [commutatorElement_def]; group
  rw [← AM.φ_π m v hv, ← hπ _ hmvQ, e, AM.φ_π ⟨⁅x, (m : G)⁆, hc.Q_le_H0 h⟩ _ hmxvQ, hq1,
    LinearEquiv.coe_one, id_eq, AM.φ_π m _ hxvQ, hπ v hv]

private theorem sigma_eq (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {x : G} (hx : x ∈ M) {σ : AM.K ≃+* AM.K} {T : AM.M₀.E ≃+ AM.M₀.E}
    (hsmul : ∀ (c : AM.K) e, T (c • e) = σ c • T e)
    (hπ : ∀ v ∈ Q, AM.M₀.π (x * v * x⁻¹) = T (AM.M₀.π v)) (hY : ∀ y ∈ Y, ⁅x, y⁆ ∈ Q)
    (c : AM.K) : σ c = c := by
  have hTt : ∀ e, T (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (T e) :=
    T_phi hc AM hx hπ ⟨t, D.t_mem_H0⟩ (hY t D.sit.mem)
  have hTnu : ∀ e, T (D.nu AM e) = D.nu AM (T e) := fun e => by
    rw [D.nu_apply, D.nu_apply, map_sub, hTt]
  obtain ⟨e₀, he₀⟩ : ∃ e₀, D.nu AM e₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact D.nu_ne_zero AM (LinearMap.ext h)
  obtain ⟨y, hy, hyc⟩ := D.exists_root_eq_smul AM c
  have hTy := T_phi hc AM hx hπ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ (hY y hy) (T.symm e₀)
  have hφ : ∀ e, AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ e = e + c • D.nu AM e := fun e => by
    have h := LinearMap.congr_fun hyc e
    simpa using h
  rw [hφ, hφ, map_add, hsmul, hTnu, AddEquiv.apply_symm_apply, add_right_inj] at hTy
  exact sub_eq_zero.mp (smul_left_injective AM.K he₀ (by
    simp only [sub_smul, hTy, sub_self, zero_smul]))

theorem Sec108Data.mem_H0_of_twoElt (D : Sec108Data hc t Y) {x : G} (hx : x ∈ M) {k : ℕ}
    (h2 : x ^ 2 ^ k ∈ Q) (hY : ∀ y ∈ Y, ⁅x, y⁆ ∈ Q) : x ∈ H0 M Z := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  obtain ⟨σ, a, T, hsmul, hπ, hγ, -⟩ := AM.glob.act x hx
  have hσ := sigma_eq D AM hx hsmul hπ hY
  have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 hx
  have hγ' : ∀ z ∈ Z, AM.γ (x * z * x⁻¹) = (a : AM.K) * AM.γ z := fun z hz => by
    rw [hγ z hz, hσ]
  have ha : (a : AM.K) = 1 := by
    obtain ⟨z, hz, hz1⟩ := AM.glob.reg.surj 1
    have h := gamma_conj_pow hxZ hγ' (2 ^ k) z hz
    have hzc : x ^ 2 ^ k * z * (x ^ 2 ^ k)⁻¹ = z := by
      rw [← Z_central hc.hyp hz h2, mul_inv_cancel_right]
    rw [hzc, hz1, mul_one] at h
    exact eq_one_of_pow_two_pow h.symm
  refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hxz : x * z * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hxZ z).mp hz
  have h := AM.glob.reg.eq_of_γ_eq hxz hz (by rw [hγ' z hz, ha, one_mul])
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem Sec108Data.exists_root_of_twoElt (D : Sec108Data hc t Y) {x : G} (hx : x ∈ M) {k : ℕ}
    (h2 : x ^ 2 ^ k ∈ Q) (hR : ∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ Q) :
    ∃ y ∈ Y, x * y⁻¹ ∈ Q := by
  have htLB := D.good.1.mem_LB
  have hx0 : x ∈ H0 M Z := D.mem_H0_of_twoElt hx h2
    (fun y hy => hR y (le_Rt (M := M) (LB M Q B) htLB (D.root_le_LB hy)))
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  set m : ↥(H0 M Z) := ⟨x, hx0⟩ with hm
  have hcomm : ∀ m' : ↥(H0 M Z), (m' : G) ∈ Rt M (LB M Q B) t →
      (∀ e, AM.φ m' (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m' e)) →
      ∀ e, AM.φ m (AM.φ m' e) = AM.φ m' (AM.φ m e) := fun m' hm'R _ e =>
    Sec108Data.phi_comm_of_comm_mem AM (hR _ hm'R) e
  obtain ⟨c, hcU⟩ := D.exists_smul_of_commute AM m hcomm
  have hpow : ∀ j : ℕ, ∀ u ∈ LinearMap.range (D.nu AM), AM.φ (m ^ j) u = c ^ j • u := by
    intro j
    induction j with
    | zero => intro u _; simp
    | succ j ih =>
      intro u hu
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hcU u hu, map_smul, ih u hu, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨e₀, he₀⟩ : ∃ e₀, D.nu AM e₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact D.nu_ne_zero AM (LinearMap.ext h)
  have hc1 : c = 1 := by
    have h1 : AM.φ (m ^ 2 ^ k) = 1 := (AM.φ_ker _).mpr (by simpa [hm] using h2)
    have h2' := hpow (2 ^ k) (D.nu AM e₀) (LinearMap.mem_range_self _ _)
    rw [h1, LinearEquiv.coe_one, id_eq] at h2'
    refine eq_one_of_pow_two_pow (k := k) (smul_left_injective AM.K he₀ ?_)
    simp only [one_smul]
    exact h2'.symm
  obtain ⟨c', hc'⟩ := D.eq_id_add_smul_nu AM m hcomm (fun u hu => by rw [hcU u hu, hc1, one_smul])
  obtain ⟨y, hy, hyc⟩ := D.exists_root_eq_smul AM c'
  refine ⟨y, hy, ?_⟩
  have heq : AM.φ m = AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ :=
    LinearEquiv.toLinearMap_injective (by rw [hc', hyc])
  have h1 : AM.φ (m * (⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ : ↥(H0 M Z))⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact (AM.φ_ker _).mp h1

end CFSG.RankThree.GF2n.Stroth80
