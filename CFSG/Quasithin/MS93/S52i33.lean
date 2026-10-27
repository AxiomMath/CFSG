module

public import CFSG.Quasithin.MS93.S33LamH
public import CFSG.Quasithin.MS93.S5BExcl
public import CFSG.Quasithin.MS93.S5ASp
public import CFSG.Quasithin.MS93.S33LamF

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S33
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem conj_data_of_not_le (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal))
    (hn : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ critR _ (baseA _) α')
    {g : (puAmalgam h.le).Universal} (hgα : g • baseA (puAmalgam h.le) = α')
    (hgβ : g • baseB (puAmalgam h.le) = geo _ α' (baseA _) 1)
    (hμ : IsCritical (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _))
    (hgeo : geo (puAmalgam h.le) (baseA _) (g⁻¹ • baseA _) 1 = baseB _) :
    pre h.le (ZM _ (g⁻¹ • baseA _)) ≤ T ∧
      pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ T ∧
      pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤
        Subgroup.centralizer ((⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA _))⁆ : Subgroup G) :
          Set G) ∧
      ¬ ⁅Uq M T L, pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)⁆ ≤
        ⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA _))⁆ ∧
      (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ (g⁻¹ • baseA _)) ∧
      (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') =
        (Qv _ (g⁻¹ • baseA (puAmalgam h.le))).relIndex (ZM (puAmalgam h.le) (baseA _)) := by
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hYY' : Y = (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id Y]
    congr 1
    ext x
    simp
  have hR : critR (puAmalgam h.le) (baseA _) α' =
      (critR (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [critR, critR, Subgroup.map_commutator, ← zm_smul, ← zm_smul, hgμ, hgα]
  have hET : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ T :=
    pre_le_of_le_imM h (zm_le_imM_T h hμ hgeo)
  have hY'T : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ imM h.le T := by
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
      rw [hYY'] at hY
      exact hY ⟨y, hy, rfl⟩
    rw [← hgβ, qv_smul, puAmalgam.qv_baseB] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  have hYqT : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ T := pre_le_of_le_imM h hY'T
  have hY'im : imM h.le (pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)) =
      Y.map (MulAut.conj g⁻¹).toMonoidHom :=
    imM_pre h.le (hY'T.trans (imM_mono h.le h.le))
  have hcomm := imM_commutator_pre h hμ hET
  refine ⟨hET, hYqT, ?_, ?_, ?_, ?_⟩
  · refine pre_le_centralizer h.le ((commutator_le_left_of_le_normalizer
      ((pre_le h.le _).trans (le_normalizer_Uq h.le_normalizer))).trans
        ((Uq_le_Z0q h.L_le).trans (Z0q_le M T))) ?_
    rw [hcomm]
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈
        Subgroup.centralizer (critR (puAmalgam h.le) (baseA _) α' : Set _) := by
      rw [hYY'] at hYR
      exact hYR ⟨y, hy, rfl⟩
    rw [hR, PU.centralizer_map_mulEquiv] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  · intro hle
    apply hn
    have h1 : ⁅ZM (puAmalgam h.le) (baseA _), Y.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
        critR (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _) := by
      have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
      rw [hZ, ← hY'im, ← imM_commutator h.le (Z0q_le M T) (pre_le h.le _),
        commutator_Z0q_eq h hYqT, ← hcomm]
      exact imM_mono h.le hle
    have h2 : ⁅ZM (puAmalgam h.le) α', Y⁆ =
        ⁅ZM (puAmalgam h.le) (baseA _), Y.map (MulAut.conj g⁻¹).toMonoidHom⁆.map
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_commutator, ← hYY', ← zm_smul, hgα]
    rw [h2, hR]
    exact Subgroup.map_mono h1
  · have e1 : Qv (puAmalgam h.le) α' =
        (Qv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← hgα, qv_smul]
    have e2 : ZM (puAmalgam h.le) (baseA _) =
        (ZM (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← zm_smul, hgμ]
    rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  · have e3 : Qv (puAmalgam h.le) (baseA _) =
        (Qv (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← qv_smul, hgμ]
    have e4 : ZM (puAmalgam h.le) α' =
        (ZM (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← hgα, zm_smul]
    rw [e4, e3, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem hat_of_not_le (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L 1 F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal))
    (hn : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ critR _ (baseA _) α')
    (hΛ : 4 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _))) :
    ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
      ∃ t₃ ∈ Qv _ (geo _ α' (baseA _) 1),
      (∀ t ∈ ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal),
        (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
      t₁ * t₂⁻¹ ∉ Qv _ α' ∧
      ZM _ (baseA _) ⊔ Qv _ α' =
        Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ∧
      Qv _ (geo _ α' (baseA _) 1) ⊓
          Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) ⊔
        Qv _ α' = Subgroup.closure ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ∧
      ¬ Y ≤ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := S5.IsSp4Data.charP hd
  obtain ⟨g, hgα, hgβ, hμ, hgeo⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨hET, hYT, hYR', hYn, hrel₁, hrel₂⟩ :=
    conj_data_of_not_le h hY hYR hn hgα hgβ hμ hgeo
  have hnatM : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) a false 1 := by
    have := hd.2.2.2
    rwa [← h.Uq_inf_Zq] at this
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnatM
  have hAβ := isCoordAct_of_natSp hβα
  have hEA : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ M := pre_le h.le _
  set Γ := ((pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))).subgroupOf M).map a with hΓ
  have hΓcard : Nat.card Γ = (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) := by
    rw [hΓ, card_image_eq_relIndex h le_rfl (natCoordOf β hβ hβker hAβ) hEA, hrel₁,
      relIndex_qv_zm_eq h hμ]
  have hq : Nat.card F = 2 := by rw [S5.IsSp4Data.nat_card_eq hd, pow_one]
  rcases shapes_at h hc hμ hrel₁ hrel₂ le_rfl hnatM hEA le_rfl hnatM (pre_le h.le _) with
    ⟨-, -, hP, -⟩ | ⟨-, -, hfix, -⟩
  · rw [hP, ← Nat.card_eq_fintype_card, hq] at hΛ
    norm_num at hΛ
  obtain ⟨hEab, hE2, hUE, -, -⟩ := pre_zm_props h hμ
  have hΓq : 4 ≤ Nat.card Γ := by rw [hΓcard]; exact hΛ
  have hYA : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ M := hYT.trans h.le
  obtain ⟨-, hCM, hlift⟩ := Sp4L.sp4Lift_of_nat h (k := 1) le_rfl hd.2.1 hd.2.2.1 hd.2.2.2
  have hCfix : ∀ x ∈ M, ∀ z ∈ Uq M T L ⊓ Zq M L, x * z * x⁻¹ = z := by
    intro x hx z hz
    rw [h.Uq_inf_Zq, hCM] at hz
    rw [Subgroup.mem_centralizer_iff.mp hz.2 x hx, mul_inv_cancel_right]
  obtain ⟨hq', p, p', hp, hp', hpp, hΓeq⟩ := lam_core h le_rfl hβ hβker hAβ (k := 1) le_rfl
    hd.2.1 h.L_le hd.2.2.1 hCfix hEA hEab hE2 hUE
    (by rw [hd.2.1, show ((2 : ℕ) ^ 1) ^ 2 = 4 by norm_num]; exact hΓq) hfix hYA hYR' hYn
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  have hq2 := commSp_le_fixSp_of_quadratic h le_rfl hβ hβker hAβ hEA hEab hUE
  obtain ⟨hl, -, hcf⟩ := line_of_quadratic hΓ2 hq2 hfix
  have hl' : MSP.IsLine (MSP.commSp Γ) := hcf ▸ hl
  obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, hi₁, hi₂, hi₃, h12, hsupE, hsup3, hYnot⟩ :=
    lam_triple h le_rfl hβ hβker hAβ hlift hq h.le hET hEab hUE hp hp' hpp hΓeq hΓq hl' hYT hYR'
      hYn
  exact hat_of_pre h hgα hgβ hμ hET (hET ht₁) (hET ht₂) ht₃.1 hi₁ hi₂ hi₃ h12 hsupE hsup3 hYnot

theorem false_of_not_le_of_two_le (h : PUHyp M T L) {k : ℕ} (hk2 : 2 ≤ k) {F : Type} [Field F]
    [Fintype F] (hcard : Fintype.card F = 2 ^ k) {α : ↥L →* ↥(StatedSp 2 F)}
    (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal))
    (hn : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ critR _ (baseA _) α')
    (hΛ : 2 ^ (2 * k) ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hF4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  obtain ⟨g, hgα, hgβ, hμ, hgeo⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨hET, hYT, hYR, hYn, hrel₁, hrel₂⟩ := conj_data_of_not_le h hY hYR hn hgα hgβ hμ hgeo
  obtain ⟨hLV, -, β, hβ, hβker, hβα⟩ := hnat
  have hβα' := isCoordAct_of_natSp hβα
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  set A := coordGroup β (StatedSp 2 F) M hMV with hAdef
  have hAM : A ≤ M := fun a ha => ha.1
  have hAV : A ≤ Subgroup.normalizer (Uq M T L : Set G) := hAM.trans hMV
  obtain ⟨αA, hAβ⟩ := exists_coordHom hAV hβ fun a ha => by
    obtain ⟨-, γ, hγ⟩ := ha
    exact ⟨γ, hγ⟩
  have hLA : L ≤ A := fun l hl => ⟨h.L_le hl, α ⟨l, hl⟩, hβα' ⟨l, hl⟩⟩
  have hαL : ∀ l : ↥L, αA ⟨l, hLA l.2⟩ = α l := fun l =>
    MSP.mat_injective (IsCoordAct.matrix_eq hβ (hAV (hLA l.2)) (hAβ ⟨l, hLA l.2⟩) (hβα' l))
  have hαA : Function.Surjective αA := fun γ => by
    obtain ⟨l, rfl⟩ := hα γ
    exact ⟨⟨l, hLA l.2⟩, hαL l⟩
  have hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z := by
    intro a ha z hz
    obtain ⟨l, hl⟩ := hα (αA ⟨a, ha⟩)
    have h1 : αA (⟨a, ha⟩ * (⟨l, hLA l.2⟩ : ↥A)⁻¹) = 1 := by
      rw [map_mul, map_inv, hαL, hl, mul_inv_cancel]
    have hk := centralizer_of_eq_one h hAM hβ hβker hAβ h1
    have hkz := Subgroup.mem_centralizer_iff.mp hk z hz.1
    have hlz := Subgroup.mem_centralizer_iff.mp hz.2.2 l l.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hkz
    calc a * z * a⁻¹ = (a * (l : G)⁻¹) * ((l : G) * z * (l : G)⁻¹) * (a * (l : G)⁻¹)⁻¹ := by
          group
      _ = (a * (l : G)⁻¹) * z * (a * (l : G)⁻¹)⁻¹ := by rw [hlz, mul_inv_cancel_right]
      _ = z := by rw [← hkz, mul_inv_cancel_right]
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  have hEA : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ A := fun e he =>
    ⟨pre_le h.le _ he, exists_sp4_mat_of_isCritical h hα hβ hβker hβα' hcard hF4 hμ e he⟩
  have hE'A : pre h.le (ZM _ α') ≤ A := fun e he =>
    ⟨pre_le h.le _ he, exists_sp4_mat_of_isCritical h hα hβ hβker hβα' hcard hF4 hc' e he⟩
  have hnatA := isSumOfNaturalModulesVia_of_coord hAV inf_le_left β hβ hβker hAβ
  set Γ := ((pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))).subgroupOf A).map αA with hΓ
  have hcard2 : Fintype.card F ^ 2 = 2 ^ (2 * k) := by rw [hcard, ← pow_mul, mul_comm]
  have hΓcard : Nat.card Γ = (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) := by
    rw [hΓ, card_image_eq_relIndex h hAM (natCoordOf β hβ hβker hAβ) hEA, hrel₁,
      relIndex_qv_zm_eq h hμ]
  rcases shapes_at h hc hμ hrel₁ hrel₂ hAM hnatA hEA hAM hnatA hE'A with
    ⟨-, -, hP, -⟩ | ⟨-, -, hfix, -⟩
  · rw [hP, hcard] at hΛ
    have : 2 ^ k < 2 ^ (2 * k) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hEab, hE2, hUE, -, -⟩ := pre_zm_props h hμ
  have hΓq : Fintype.card F ^ 2 ≤ Nat.card Γ := by rw [hΓcard, hcard2]; exact hΛ
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  have hq := commSp_le_fixSp_of_quadratic h hAM hβ hβker hAβ hEA hEab hUE
  obtain ⟨hl, -, hcf⟩ := line_of_quadratic hΓ2 hq hfix
  have hl0 : MSP.commSp Γ ≠ ⊥ := by
    rw [hcf]
    intro h0
    have := hl.1
    rw [h0, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hl0
  have hYA : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ A := by
    intro y hy
    have hyT := hYT hy
    have hyM : y ∈ M := h.le hyT
    obtain ⟨f, hf⟩ := exists_isCoordAct_sp h hβ hβker hyM
    obtain ⟨f', hf'⟩ := exists_isCoordAct_sp h hβ hβker (inv_mem hyM)
    obtain ⟨σ, hσ⟩ := exists_semilinear_sp hα hLV hβ hβα' (hMV hyM) (h.le_normalizer hyM) hf hf'
    have hfixR : ∀ w ∈ MSP.commSp Γ, f w = w := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := (mem_commSp_iff_crd h hAM hβ hβker hAβ hEA w).1 hw
      exact fix_of_mem_centralizer' (hYR hy) hf hu
    have hσid : ∀ c : F, σ c = c := by
      intro c
      have h1 := hσ c v₀
      rw [hfixR _ (Submodule.smul_mem _ c hv₀), hfixR _ hv₀] at h1
      have h2 : (σ c - c) • v₀ = 0 := by rw [sub_smul, ← h1, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv₀0)
    have hlin : ∀ (c : F) (v : MSP.V4 F), f (c • v) = c • f v := fun c v => by
      rw [hσ, hσid]
    obtain ⟨e, he⟩ := h.isPGroup ⟨y, hyT⟩
    have he' : y ^ 2 ^ e = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    obtain ⟨γ, hγ⟩ := exists_sp4_of_linear hα hLV hβ hβα' (hMV hyM) (h.le_normalizer hyM) hf hf'
      hlin he'
    exact ⟨hyM, γ, hγ⟩
  obtain ⟨hq2, -⟩ := lam_core h hAM hβ hβker hAβ (by omega) hcard hLA hαA hCfix hEA hEab hE2 hUE
    hΓq hfix hYA hYR hYn
  rw [Nat.card_eq_fintype_card] at hq2
  omega

theorem commutator_zHat_le_critR_of_sq (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F]
    [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hΛ : (2 ^ k) ^ 2 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)))
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal)) :
    ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤ critR _ (baseA _) α' := by
  by_cases hn : ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ critR _ (baseA _) α'
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans hn
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, hidx, h12n, h12, hCY, hYn⟩ :=
      hat_of_not_le h hd hc hY hYR hn (by simpa using hΛ)
    have ht : S5.IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ :=
      ⟨ht₁, ht₂, ht₃, hidx t₁ (by simp), hidx t₂ (by simp), hidx t₃ (by simp), h12n, h12, hCY⟩
    exact (Subgroup.commutator_mono (le_inf hY hYR) le_rfl).trans
      (S5B.commutator_zHat_le_critR h hc ht (ht.not_mem_of_not_le (le_inf hY hYR) hYn))
  · have hα : Function.Surjective (a.comp (Subgroup.inclusion h.L_le)) := by
      intro y
      have hy : y ∈ (L.subgroupOf M).map a :=
        (S5B.map_L_eq_top h hd hk).symm ▸ Subgroup.mem_top y
      obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, rfl⟩
    have hnat := S5B.isSumOfNaturalModulesVia_restrict h.L_le hd.2.2.2
    rw [← h.Uq_inf_Zq] at hnat
    exact (false_of_not_le_of_two_le h hk hd.2.1 hα hnat hc hY hYR hn
      (by rw [pow_mul']; exact hΛ)).elim

end CFSG.Quasithin.MS93.S52i
