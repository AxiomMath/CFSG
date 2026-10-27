module

public import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.S33LamP

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_coordHom {A V : Subgroup G} (hAV : A ≤ Subgroup.normalizer (V : Set G))
    {F : Type} [Field F] {β : ↥V →* Multiplicative (Fin 1 → MSP.V4 F)}
    (hβ : Function.Surjective β)
    (hA : ∀ a ∈ A, ∃ γ : MSP.Sp4 F, IsCoordAct β a (MSP.mat γ).mulVec) :
    ∃ α : ↥A →* MSP.Sp4 F, ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec := by
  choose φ hφ using fun a : ↥A => hA a a.2
  have huniq : ∀ (a : ↥A) (γ : MSP.Sp4 F), IsCoordAct β a (MSP.mat γ).mulVec → φ a = γ :=
    fun a γ hγ => MSP.mat_injective (IsCoordAct.matrix_eq hβ (hAV a.2) (hφ a) hγ)
  refine ⟨{ toFun := φ
            map_one' := huniq 1 1 (by rw [MSP.mat_one]; exact isCoordAct_one_mulVec)
            map_mul' := fun a b => huniq (a * b) (φ a * φ b) ?_ }, hφ⟩
  have := (hφ a).mul (hAV b.2) (hφ b)
  convert this using 1
  funext x
  simp [MSP.mat_mul, Matrix.mulVec_mulVec]

variable [Finite G] {M T L : Subgroup G}

theorem lam_false_of_two_le (h : PUHyp M T L) {k : ℕ} (hk2 : 2 ≤ k) {F : Type} [Field F]
    [Fintype F] (hcard : Fintype.card F = 2 ^ k) {α : ↥L →* ↥(StatedSp 2 F)}
    (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    {α' : Vtx (puAmalgam h.le)} {Y : Subgroup (puAmalgam h.le).Universal} (hyp : S33Hyp h α' Y)
    (hΛ : 2 ^ (2 * k) ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hF4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hc := hyp.1
  obtain ⟨g, hgα, hgβ, hμ, hgeo⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨hET, hYT, hYR, hYn, hrel₁, hrel₂⟩ := conj_data h hyp hgα hgβ hμ hgeo
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

theorem mem_commutator_of_perfect (h : PUHyp M T L) {α : ↥M →* MSP.Sp4 (ZMod 2)}
    (hall : ∀ m : ↥M, ∃ l : ↥L, α m = α ⟨l, h.L_le l.2⟩) (m : ↥M) :
    α m ∈ commutator (MSP.Sp4 (ZMod 2)) := by
  obtain ⟨l, hl⟩ := hall m
  rw [hl]
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  let φ : ↥L →* MSP.Sp4 (ZMod 2) := α.comp (Subgroup.inclusion h.L_le)
  have hl' : l ∈ commutator ↥L := by
    rw [hperf.commutator_eq_top]
    exact Subgroup.mem_top l
  have h1 : φ l ∈ (commutator ↥L).map φ := Subgroup.mem_map_of_mem φ hl'
  rw [commutator_def, Subgroup.map_commutator] at h1
  rw [commutator_def]
  exact Subgroup.commutator_mono le_top le_top h1

theorem lam_weak_of_one (h : PUHyp M T L)
    {N : Subgroup ↥L} (hA6 : IsAltNaturalSection L (Uq M T L) (Uq M T L ⊓ Zq M L) N 6)
    {α' : Vtx (puAmalgam h.le)} {Y : Subgroup (puAmalgam h.le).Universal} (hyp : S33Hyp h α' Y)
    (hΛ : 2 ^ (2 * 1) ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _))) :
    ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
      (∀ t ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal),
        (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
      t₁ * t₂⁻¹ ∉ Qv _ α' ∧
      ZM _ (baseA _) ⊔ Qv _ α' =
        Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
  have hc := hyp.1
  obtain ⟨g, hgα, hgβ, hμ, hgeo⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨hET, hYT, hYR, hYn, hrel₁, hrel₂⟩ := conj_data h hyp hgα hgβ hμ hgeo
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨α, hnatM, hcase⟩ := sp4Two_of_altNaturalSection h.L_le h.le_normalizer hMV
    (le_normalizer_Uq_inf_Zq h) inf_le_left hA6
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnatM
  have hAβ := isCoordAct_of_natSp hβα
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  have hEA : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ M := pre_le h.le _
  set Γ := ((pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))).subgroupOf M).map α with hΓ
  have hΓcard : Nat.card Γ = (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) := by
    rw [hΓ, card_image_eq_relIndex h le_rfl (natCoordOf β hβ hβker hAβ) hEA, hrel₁,
      relIndex_qv_zm_eq h hμ]
  rcases shapes_at h hc hμ hrel₁ hrel₂ le_rfl hnatM hEA le_rfl hnatM (pre_le h.le _) with
    ⟨-, -, hP, -⟩ | ⟨-, -, hfix, -⟩
  · rw [hP, ZMod.card] at hΛ
    norm_num at hΛ
  obtain ⟨hEab, hE2, hUE, -, -⟩ := pre_zm_props h hμ
  have hΓq : 4 ≤ Nat.card Γ := by rw [hΓcard]; simpa using hΛ
  have hYA : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ M := hYT.trans h.le
  rcases hcase with hsurj | hall
  ·
    have hnat' := hnatM
    rw [h.Uq_inf_Zq] at hnat'
    obtain ⟨-, hCM, hlift⟩ := Sp4L.sp4Lift_of_nat h (k := 1) le_rfl (by rw [ZMod.card]; rfl)
      hsurj hnat'
    have hCfix : ∀ a ∈ M, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z := by
      intro a ha z hz
      rw [h.Uq_inf_Zq, hCM] at hz
      rw [Subgroup.mem_centralizer_iff.mp hz.2 a ha, mul_inv_cancel_right]
    obtain ⟨hq, p, p', hp, hp', hpp, hΓeq⟩ := lam_core h le_rfl hβ hβker hAβ (k := 1) le_rfl
      (by rw [ZMod.card]; rfl) h.L_le hsurj hCfix hEA hEab hE2 hUE
      (by rw [ZMod.card]; exact hΓq) hfix hYA hYR hYn
    obtain ⟨t₁, ht₁, t₂, ht₂, hi₁, hi₂, h12, hsup⟩ :=
      lam_pair h le_rfl hβ hβker hAβ hlift hq hEA hET hp hp' hpp hΓeq hΓq
    exact weak_of_pre h hgα hgβ hμ (hET ht₁) (hET ht₂) hi₁ hi₂ h12 hsup
  ·
    exact (lam_alt h le_rfl hβ hβker hAβ (mem_commutator_of_perfect h hall) hEA hEab hE2 hUE hΓq
      hfix hYA hYR hYn).elim

theorem s33lw_holds : S33LW := by
  intro G _ _ M T L h _ k hk α' Y hyp hΛ
  rcases hk with ⟨rfl, N, hA6⟩ | ⟨hk2, F, _, _, α, hcard, hα, hnat⟩
  · exact ⟨rfl, lam_weak_of_one h hA6 hyp hΛ⟩
  · exact (lam_false_of_two_le h hk2 hcard hα hnat hyp hΛ).elim

theorem s33w_of_bad (h32 : S32) (h38 : S38) (hBad : S33Bad) :
    S33w :=
  s33w_of h32 h38 hBad s33lw_holds

end CFSG.Quasithin.MS93.S33
