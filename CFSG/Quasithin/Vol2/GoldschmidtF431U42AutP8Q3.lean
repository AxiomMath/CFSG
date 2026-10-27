module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Aut
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R14

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

noncomputable def psl32EquivGL32 :
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      CFSG.QuasithinUnique.Setup.Family.GL32 :=
  ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
    QuotientGroup.quotientBot).trans
    (MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)

theorem Delta_pow_four : ∀ x : DihedralGroup 4 × DihedralGroup 4, x ^ 4 = 1 := by decide +kernel

theorem exp_four_of_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    (hP : ∀ r ∈ (P : Subgroup X), r ^ 4 = 1) :
    ∀ x : X, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1 := by
  classical
  intro x ⟨k, hk⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hk]
    exact ⟨k, rfl⟩
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S P
  have hxP : g * x * g⁻¹ ∈ (P : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨x, hS (Subgroup.mem_zpowers x), by simp [MulAut.conj_apply]⟩
  have h4 := hP _ hxP
  calc x ^ 4 = g⁻¹ * (g * x * g⁻¹) ^ 4 * g := by rw [conj_pow]; group
    _ = 1 := by rw [h4]; group

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section NotL32

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem X_exp_four (h : F55Ctx c R) :
    ∀ x : ↥(cenOf (c.iso.toG fhB)), (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ cenOf (c.iso.toG fhB) := h.hR.1
  have hcR : Nat.card ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, h.hR64]
    norm_num
  have hR2 : IsPGroup 2 ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) :=
    IsPGroup.of_card (n := 6) (by rw [hcR]; norm_num)
  have hidx : ¬ 2 ∣ (R.subgroupOf (cenOf (c.iso.toG fhB))).index := h.hR.2.2
  obtain ⟨e⟩ := h.hD
  refine exp_four_of_sylow (hR2.toSylow hidx) ?_
  intro r hr
  have hr' : (r : G) ∈ R := hr
  have := Delta_pow_four (e ⟨_, hr'⟩)
  rw [← map_pow] at this
  have h5 : (⟨(r : G), hr'⟩ : ↥R) ^ 4 = 1 := e.injective (by rw [this, map_one])
  refine Subtype.ext ?_
  have h6 := congrArg Subtype.val h5
  simpa using h6

theorem Q_not_L32 (h : F55Ctx c R) {Q : Subgroup ↥(cenOf (c.iso.toG fhB))} [Q.Normal]
    (hQi : Q.index = 8)
    (hQc : Q = Subgroup.closure {x : ↥(cenOf (c.iso.toG fhB)) | Odd (orderOf x)})
    (e : ↥Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ cenOf (c.iso.toG fhB) := h.hR.1
  have hcR : Nat.card ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, h.hR64]
    norm_num
  have hR2 : IsPGroup 2 ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) :=
    IsPGroup.of_card (n := 6) (by rw [hcR]; norm_num)
  have hidx : ¬ 2 ∣ (R.subgroupOf (cenOf (c.iso.toG fhB))).index := h.hR.2.2
  let e' : ↥Q ≃* CFSG.QuasithinUnique.Setup.Family.GL32 := e.trans psl32EquivGL32
  have hQ168 : Nat.card ↥Q = 168 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32
  have hK8 := ker_card_eight Q e' hQ168 hQi (X_exp_four c h)
  set φ : ↥(cenOf (c.iso.toG fhB)) →* MulAut ↥Q := MulAut.conjNormal with hφ
  set K := φ.ker with hK
  have hK2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [hK8]; norm_num)
  have hKR : K ≤ R.subgroupOf (cenOf (c.iso.toG fhB)) :=
    IsPGroup.le_sylow_of_normal hK2 (hR2.toSylow hidx)
  have hker : ∀ k ∈ K, ∀ q : ↥Q, k * (q : ↥(cenOf (c.iso.toG fhB))) * k⁻¹ = q := by
    intro k hk q
    have h1 : φ k = 1 := hk
    have h2 : ((φ k q : ↥Q) : ↥(cenOf (c.iso.toG fhB))) = k * (q : ↥(cenOf (c.iso.toG fhB))) *
        k⁻¹ := rfl
    rw [← h2, h1]
    rfl
  have hKC : K.map (cenOf (c.iso.toG fhB)).subtype ≤ C1G c R := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨hKR hk, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hgX : g ∈ cenOf (c.iso.toG fhB) := E1G_le_cen c (B1G_le_E1G c hg)
    have hgQ : (⟨g, hgX⟩ : ↥(cenOf (c.iso.toG fhB))) ∈ Q := by
      have hg' : g ∈ oddCl (cenOf (c.iso.toG fhB)) := by
        rw [B1G_eq_oddCl] at hg
        exact oddCl_mono (E1G_le_cen c) hg
      obtain ⟨hgc, hq⟩ := oddCl_subtype (H := cenOf (c.iso.toG fhB)) hg'
      rw [hQc]
      exact hq
    have := congrArg Subtype.val (hker k hk ⟨_, hgQ⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc g * (k : G) = ((k : G) * g * (k : G)⁻¹) * k := by rw [this]
      _ = (k : G) * g := by group
  have hKcard : Nat.card ↥(K.map (cenOf (c.iso.toG fhB)).subtype) = 8 := by
    rw [Subgroup.card_map_of_injective (cenOf (c.iso.toG fhB)).subtype_injective, hK8]
  have hKeq : K.map (cenOf (c.iso.toG fhB)).subtype = C1G c R :=
    Subgroup.eq_of_le_of_card_ge hKC (by rw [hKcard, (decomp_R c h).1])
  have hz : z ∈ K.map (cenOf (c.iso.toG fhB)).subtype := by
    rw [hKeq]
    exact z_mem_C1G c h
  obtain ⟨k, hk, hkz⟩ := hz
  have hQE : Q.map (cenOf (c.iso.toG fhB)).subtype ≤ E1G c := by
    rintro _ ⟨q, hq, rfl⟩
    have hqz : (q : G) ∈ cenOf z := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have := congrArg Subtype.val (hker k hk ⟨q, hq⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      have hkz' : ((k : ↥(cenOf (c.iso.toG fhB))) : G) = z := hkz
      rw [hkz'] at this
      calc (q : G) * z = (z * (q : G) * z⁻¹) * z := by rw [this]
        _ = z * (q : G) := by group
    rw [c.cenOf_z] at hqz
    exact ⟨hqz, q.2⟩
  have hdvd := Subgroup.card_dvd_of_le hQE
  rw [Subgroup.card_map_of_injective (cenOf (c.iso.toG fhB)).subtype_injective, hQ168,
    card_E1G c] at hdvd
  omega

end NotL32

end CFSG.Quasithin.H13.F431.U42Aut
