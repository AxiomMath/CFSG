module

public import CFSG.LocalAnalysis.StandardType.GGF4N2NbrReflection
public import CFSG.LocalAnalysis.StandardType.GGF4N2OmegaKPositions
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.StandardType

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm

theorem exists_blockGamma_of_inv_trace
    (β : MulAut (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)))
    {g : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)} (hβ : β g = g⁻¹)
    (h0 : Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 0)
    (h1 : Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 1)
    (hinv : Matrix.trace ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
        Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2))) :
    ∃ (C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) (δ : ℕ), δ ≤ 1 ∧
      β = N2KFieldCoefficient.blockGamma C δ := by
  obtain ⟨A, σ, ε, hε, hβeq⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (n := 4) (K := GaloisField 2 2)
      (by norm_num) β
  have htr : Matrix.trace ((β g : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
      σ (Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2))) := by
    rw [hβeq, MulAut.mul_apply, MulAut.mul_apply, trace_slConjugation, trace_slFieldAut]
    interval_cases ε
    · rw [pow_zero, MulAut.one_apply]
    · rw [pow_one, trace_slGraphAut, hinv]
  rw [hβ, hinv] at htr
  have hσ : σ = RingEquiv.refl (GaloisField 2 2) :=
    ringEquiv_eq_refl_of_fix (GaloisField.card 2 2 (by norm_num)) σ h0 h1 htr.symm
  refine ⟨A, ε, hε, ?_⟩
  rw [hβeq, hσ, show slFieldAut (Fin 4) (GaloisField 2 2) (RingEquiv.refl (GaloisField 2 2)) = 1
    from map_one _, mul_one]
  rfl

theorem exists_blockGamma_on_subgroup_of_inv_trace
    {G : Type} [Group G] {J : Subgroup G}
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2))
    {t : G} (htJ : t ∈ Subgroup.normalizer (J : Set G))
    {w : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)}
    (htw : t * (eJ.symm w : G) * t⁻¹ = (eJ.symm w : G)⁻¹)
    (h0 : Matrix.trace (w : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 0)
    (h1 : Matrix.trace (w : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 1)
    (hinv : Matrix.trace ((w⁻¹ : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
        Matrix.trace (w : Matrix (Fin 4) (Fin 4) (GaloisField 2 2))) :
    ∃ (C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) (δ : ℕ), δ ≤ 1 ∧
      ∀ z : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
        t * (eJ.symm z : G) * t⁻¹ =
          (eJ.symm (N2KFieldCoefficient.blockGamma C δ z) : G) := by
  let φJ : MulAut J := J.normalizerMonoidHom ⟨t, htJ⟩
  have hφJ : ∀ j : J, ((φJ j : J) : G) = t * (j : G) * t⁻¹ := fun j =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨t, htJ⟩ j
  let β : MulAut (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :=
    eJ.symm.trans (φJ.trans eJ)
  have hβ : ∀ z, β z = eJ (φJ (eJ.symm z)) := fun _ => rfl
  have hβw : β w = w⁻¹ := by
    rw [hβ]
    have hφw : φJ (eJ.symm w) = (eJ.symm w)⁻¹ := by
      apply Subtype.ext
      rw [hφJ, Subgroup.coe_inv]
      exact htw
    rw [hφw, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨C, δ, hδ, hβC⟩ := exists_blockGamma_of_inv_trace β hβw h0 h1 hinv
  refine ⟨C, δ, hδ, fun z => ?_⟩
  have hz : N2KFieldCoefficient.blockGamma C δ z = eJ (φJ (eJ.symm z)) := by
    rw [← hβC]
    exact hβ z
  have hz' : (eJ.symm (N2KFieldCoefficient.blockGamma C δ z) : J) = φJ (eJ.symm z) := by
    rw [hz, MulEquiv.symm_apply_apply]
  rw [hz', hφJ]

private theorem sgnAut_zero_one_two (f : Fin 3 → Multiplicative (ZMod 5)) :
    SpCoord.sgnAut 0 (SpCoord.sgnAut 1 (SpCoord.sgnAut 2 f)) = f⁻¹ := by
  funext j
  fin_cases j <;> simp [SpCoord.sgnAut_apply]

section Minus

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical2 Module Multiplicative


theorem ggF4N2_minus_inverter
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    {z : G} {Y : Subgroup G} (hzY : GGNbr 5 B x D J z Y)
    (hY : GGCentralImage .POmegaMinus 4 2 Y) :
    ∃ t ∈ Y, (∀ c ∈ Bs ⊓ Y, t * c * t⁻¹ = c⁻¹) ∧
      t ∈ Subgroup.normalizer (Bs : Set G) ∧ t ∈ Subgroup.normalizer (J : Set G) ∧
      t * z * t⁻¹ = z ∧
      ∃ htD : t ∈ Subgroup.normalizer (D : Set G),
        orderOf (D.normalizerMonoidHom ⟨t, htD⟩) = 2 := by
  classical
  have mem_norm : ∀ {H : Subgroup G} {s : G}, (∀ h ∈ H, s * h * s⁻¹ ∈ H) →
      (∀ h ∈ H, s⁻¹ * h * s ∈ H) → s ∈ Subgroup.normalizer (H : Set G) := by
    intro H s h₁ h₂
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨h₁ h, fun hh => ?_⟩
    have hc := h₂ _ hh
    rwa [show s⁻¹ * (s * h * s⁻¹) * s = h by group] at hc
  have conj_sup : ∀ {H K M : Subgroup G} {s : G}, (∀ h ∈ H, s * h * s⁻¹ ∈ M) →
      (∀ k ∈ K, s * k * s⁻¹ ∈ M) → ∀ g ∈ H ⊔ K, s * g * s⁻¹ ∈ M := by
    intro H K M s hH hK
    have hle : H ⊔ K ≤ M.comap (MulAut.conj s : G →* G) :=
      sup_le (fun h hh => by simpa [MulAut.conj_apply] using hH h hh)
        (fun k hk => by simpa [MulAut.conj_apply] using hK k hk)
    intro g hg
    simpa [MulAut.conj_apply] using hle hg
  let F := GaloisField 2 2
  let b : F := (minusCoeffs 2 2).1
  let c : F := (minusCoeffs 2 2).2
  have hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 2
  obtain ⟨e⟩ := ggN2OrthDerived_model_of_centralImage hY
  have hF : Nat.card F = 4 := by simpa using GaloisField.card 2 2 (by decide)
  have hV : finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 8 := by simp
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (by norm_num : 4 ≤ 4) hbc
  obtain ⟨τ, -, hτP, -, hsgn, -⟩ := ggF4N2OmegaK_internal_torus hR hzY hL hY hF hV hQ hT e
  obtain ⟨w₀, hw₀⟩ := hsgn 0
  obtain ⟨w₁, hw₁⟩ := hsgn 1
  obtain ⟨w₂, hw₂⟩ := hsgn 2
  let tY : Y := w₀ * w₁ * w₂
  have htτ : ∀ f, tY * τ f * tY⁻¹ = (τ f)⁻¹ := by
    intro f
    calc tY * τ f * tY⁻¹ = w₀ * (w₁ * (w₂ * τ f * w₂⁻¹) * w₁⁻¹) * w₀⁻¹ := by
          simp only [tY]
          group
      _ = τ (SpCoord.sgnAut 0 (SpCoord.sgnAut 1 (SpCoord.sgnAut 2 f))) := by
          rw [hw₂, hw₁, hw₀]
      _ = (τ f)⁻¹ := by rw [sgnAut_zero_one_two, map_inv]
  let t : G := (tY : G)
  have htY : t ∈ Y := tY.2
  have hinv : ∀ c ∈ Bs ⊓ Y, t * c * t⁻¹ = c⁻¹ := by
    intro c hc
    have hcP : (⟨c, hc.2⟩ : Y) ∈ (Bs ⊓ Y).subgroupOf Y := Subgroup.mem_subgroupOf.mpr hc
    rw [← hτP] at hcP
    obtain ⟨f, hf⟩ := hcP
    have h := congrArg Subtype.val (htτ f)
    rw [hf] at h
    simpa [t] using h
  have hinv' : ∀ c ∈ Bs ⊓ Y, t⁻¹ * c * t = c⁻¹ := by
    intro c hc
    have h := hinv c⁻¹ ((Bs ⊓ Y).inv_mem hc)
    rw [inv_inv] at h
    calc t⁻¹ * c * t = t⁻¹ * (t * c⁻¹ * t⁻¹) * t := by rw [h]
      _ = c⁻¹ := by group
  have hYC : Subgroup.zpowers z ≤ Subgroup.centralizer (Y : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hzY.1]
    exact inf_le_right
  have hzc : ∀ g ∈ Subgroup.zpowers z, t * g = g * t := fun g hg =>
    Subgroup.mem_centralizer_iff.mp (hYC hg) t htY
  have hzfix : ∀ g ∈ Subgroup.zpowers z, t * g * t⁻¹ = g := fun g hg => by
    rw [hzc g hg, mul_inv_cancel_right]
  have hzfix' : ∀ g ∈ Subgroup.zpowers z, t⁻¹ * g * t = g := fun g hg => by
    rw [mul_assoc, ← hzc g hg, inv_mul_cancel_left]
  have hBs : B = Bs := ggF4N2_B_eq_Bs hR hL
  have hzBs : z ∈ Bs := hBs ▸ hzY.1.2.1
  have hZBs : Subgroup.zpowers z ≤ Bs := Subgroup.zpowers_le.mpr hzBs
  obtain ⟨hsplit, -⟩ := ggF4N2OmegaK_Bstar_split hR hzY hL hY
  have htBs : t ∈ Subgroup.normalizer (Bs : Set G) := by
    refine mem_norm (fun g hg => ?_) (fun g hg => ?_)
    · rw [hsplit] at hg ⊢
      refine conj_sup (fun h hh => ?_) (fun h hh => ?_) g hg
      · rw [hzfix h hh]
        exact (le_sup_left : Subgroup.zpowers z ≤ _) hh
      · rw [hinv h hh]
        exact (le_sup_right : Bs ⊓ Y ≤ _) ((Bs ⊓ Y).inv_mem hh)
    · rw [hsplit] at hg ⊢
      have := conj_sup (s := t⁻¹) (M := Subgroup.zpowers z ⊔ (Bs ⊓ Y))
        (fun h hh => ?_) (fun h hh => ?_) g hg
      · simpa using this
      · rw [inv_inv, hzfix' h hh]
        exact (le_sup_left : Subgroup.zpowers z ≤ _) hh
      · rw [inv_inv, hinv' h hh]
        exact (le_sup_right : Bs ⊓ Y ≤ _) ((Bs ⊓ Y).inv_mem hh)
  obtain ⟨a, haD, haO, hspan, hpoint⟩ := ggF4N2OmegaK_plane_basis hR hzY hL hY
  have hDBs : D ≤ Bs := by
    simpa only [hBs] using (hR.1.2.2.1 : LargeEvenStdSubPre 5 B x L D J).1
  have haBY : (a : G) ∈ Bs ⊓ Y := ⟨hDBs haD, a.2⟩
  have hABY : Subgroup.zpowers (a : G) ≤ Bs ⊓ Y := Subgroup.zpowers_le.mpr haBY
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    refine mem_norm (fun g hg => ?_) (fun g hg => ?_)
    · rw [hspan] at hg ⊢
      refine conj_sup (fun h hh => ?_) (fun h hh => ?_) g hg
      · rw [hzfix h hh]
        exact (le_sup_left : Subgroup.zpowers z ≤ _) hh
      · rw [hinv h (hABY hh)]
        exact (le_sup_right : Subgroup.zpowers (a : G) ≤ _) ((Subgroup.zpowers _).inv_mem hh)
    · rw [hspan] at hg ⊢
      have := conj_sup (s := t⁻¹) (M := Subgroup.zpowers z ⊔ Subgroup.zpowers (a : G))
        (fun h hh => ?_) (fun h hh => ?_) g hg
      · simpa using this
      · rw [inv_inv, hzfix' h hh]
        exact (le_sup_left : Subgroup.zpowers z ≤ _) hh
      · rw [inv_inv, hinv' h (hABY hh)]
        exact (le_sup_right : Subgroup.zpowers (a : G) ≤ _) ((Subgroup.zpowers _).inv_mem hh)
  have htt : D ≤ Subgroup.centralizer ({t * t} : Set G) := by
    rw [hspan]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hzc z (Subgroup.mem_zpowers z)
      calc z * (t * t) = t * z * t := by rw [← mul_assoc, ← h]
        _ = t * t * z := by rw [mul_assoc, ← h, ← mul_assoc]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hinv _ haBY
      have e1 : t * (a : G) = (a : G)⁻¹ * t := by
        calc t * (a : G) = t * (a : G) * t⁻¹ * t := by group
          _ = (a : G)⁻¹ * t := by rw [h1]
      have e2 : t * (a : G)⁻¹ = (a : G) * t := by
        calc t * (a : G)⁻¹ = (t * (a : G) * t⁻¹)⁻¹ * t := by group
          _ = (a : G) * t := by rw [h1, inv_inv]
      calc (a : G) * (t * t) = (a : G) * t * t := by group
        _ = t * (a : G)⁻¹ * t := by rw [e2]
        _ = t * ((a : G)⁻¹ * t) := by group
        _ = t * (t * (a : G)) := by rw [e1]
        _ = t * t * (a : G) := by group
  let φ : MulAut D := D.normalizerMonoidHom ⟨t, htD⟩
  have hφ2 : φ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hd := Subgroup.mem_centralizer_singleton_iff.mp (htt d.2)
    calc t * (t * (d : G) * t⁻¹) * t⁻¹ = (t * t) * (d : G) * (t * t)⁻¹ := by group
      _ = (d : G) := by rw [← hd, mul_inv_cancel_right]
  have hφ1 : φ ≠ 1 := by
    intro h
    have h' := congrArg (fun ψ : MulAut D => ((ψ ⟨a, haD⟩ : D) : G)) h
    simp only [MulAut.one_apply, φ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
    rw [hinv _ haBY] at h'
    have ha2 : (a : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h']
      exact inv_mul_cancel _
    have hdvd := orderOf_dvd_of_pow_eq_one ha2
    rw [Subgroup.orderOf_coe, haO] at hdvd
    norm_num at hdvd
  have hcent : ∀ k ∈ Y, (k ∈ Subgroup.centralizer ({x} : Set G) ↔ (a : G) * k = k * (a : G)) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hp := hpoint ⟨k, hk⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hp
    constructor
    · intro hkx
      have hfix : x * k * x⁻¹ = k := by rw [← hkx, mul_inv_cancel_right]
      rw [hfix] at hp
      calc (a : G) * k = (a : G) * k * (a : G)⁻¹ * (a : G) := by group
        _ = k * (a : G) := by rw [← hp]
    · intro hak
      have hfix : (a : G) * k * (a : G)⁻¹ = k := by rw [hak, mul_inv_cancel_right]
      rw [hfix] at hp
      calc k * x = x * k * x⁻¹ * x := by rw [hp]
        _ = x * k := by group
  have hta : t * (a : G) * t⁻¹ = (a : G)⁻¹ := hinv _ haBY
  have hta' : t⁻¹ * (a : G) * t = (a : G)⁻¹ := hinv' _ haBY
  have hconjC : ∀ s : G, s ∈ Y → s * (a : G) * s⁻¹ = (a : G)⁻¹ →
      ∀ k ∈ Y ⊓ Subgroup.centralizer ({x} : Set G),
        s * k * s⁻¹ ∈ Y ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro s hsY hsa k hk
    have hkY : s * k * s⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hsY hk.1) (Y.inv_mem hsY)
    refine ⟨hkY, (hcent _ hkY).mpr ?_⟩
    have hak := (hcent k hk.1).mp hk.2
    have hak' : (a : G)⁻¹ * k = k * (a : G)⁻¹ := (Commute.inv_left hak).eq
    have ha_eq : s * (a : G)⁻¹ * s⁻¹ = (a : G) := by
      calc s * (a : G)⁻¹ * s⁻¹ = (s * (a : G) * s⁻¹)⁻¹ := by group
        _ = (a : G) := by rw [hsa, inv_inv]
    calc (a : G) * (s * k * s⁻¹) = (s * (a : G)⁻¹ * s⁻¹) * (s * k * s⁻¹) := by rw [ha_eq]
      _ = s * ((a : G)⁻¹ * k) * s⁻¹ := by group
      _ = s * (k * (a : G)⁻¹) * s⁻¹ := by rw [hak']
      _ = (s * k * s⁻¹) * (s * (a : G)⁻¹ * s⁻¹) := by group
      _ = (s * k * s⁻¹) * (a : G) := by rw [ha_eq]
  have htC : t ∈ Subgroup.normalizer
      ((Y ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    mem_norm (hconjC t htY hta)
      (fun k hk => by
        have := hconjC t⁻¹ (Y.inv_mem htY) (by rw [inv_inv]; exact hta') k hk
        rwa [inv_inv] at this)
  have hJlayer := ggF4N2OmegaK_J_layer hR hzY hL hY
  have htJ : t ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htC ⊢
    rw [← hJlayer, ← largeEvenLayer_map_of_injective _ (MulAut.conj t).injective, htC]
  exact ⟨t, htY, hinv, htBs, htJ, hzfix z (Subgroup.mem_zpowers z), htD,
    orderOf_eq_prime hφ2 hφ1⟩

theorem ggF4N2_nbrReflectionAt_of_minus
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2))
    {g : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)} (hgBs : (eJ.symm g : G) ∈ Bs)
    (h0 : Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 0)
    (h1 : Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 1)
    (hinv : Matrix.trace ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
        Matrix.trace (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)))
    {z : G} {Y : Subgroup G} (hzY : GGNbr 5 B x D J z Y)
    (hY : GGCentralImage .POmegaMinus 4 2 Y) :
    GGF4N2NbrReflectionAt Bs D J Y z eJ := by
  obtain ⟨t, htY, htinv, htBs, htJ, htz, htD⟩ := ggF4N2_minus_inverter hR hL hzY hY
  have hJY : J ≤ Y := ggF4N2J_le_omega_neighbor hR hzY hL hY
  have htw : t * (eJ.symm g : G) * t⁻¹ = (eJ.symm g : G)⁻¹ :=
    htinv _ ⟨hgBs, hJY (eJ.symm g).2⟩
  obtain ⟨C, δ, hδ, hβC⟩ :=
    exists_blockGamma_on_subgroup_of_inv_trace eJ htJ htw h0 h1 hinv
  exact ⟨t, htY, htBs, htJ, htz, htD, C, δ, hδ, hβC⟩

end Minus

end CFSG.StandardType

end
