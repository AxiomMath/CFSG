module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCGen
public import CFSG.LocalAnalysis.WeakClosure81.W16LCCentral
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBBar
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIc

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private lemma w16l_conj_mem_centralizer {I A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (I : Set G)) {x : G}
    (hx : x ∈ Subgroup.centralizer (I : Set G)) {a : G} (ha : a ∈ A) :
    a * x * a⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  have hai : a⁻¹ * i * a ∈ I := by
    simpa using (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha)) i).1 hi
  calc i * (a * x * a⁻¹)
      = a * ((a⁻¹ * i * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * i * a)) * a⁻¹ := by
          rw [Subgroup.mem_centralizer_iff.1 hx _ hai]
    _ = (a * x * a⁻¹) * i := by group

theorem IsMinFam16.comm_centralizer_le (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    ∀ x ∈ H ⊓ Subgroup.centralizer (iSub16 V H : Set G),
      ∀ k ∈ CFSG.Quasithin.conjClosure V H, x * k * x⁻¹ * k⁻¹ ∈ iSub16 V H := by
  let C : Subgroup G := H ⊓ Subgroup.centralizer (iSub16 V H : Set G)
  change ∀ x ∈ C, ∀ k ∈ CFSG.Quasithin.conjClosure V H,
    x * k * x⁻¹ * k⁻¹ ∈ iSub16 V H
  have hF : Fam16 M U S H := hH.1
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hV0_le_I : V₀ ≤ iSub16 V H :=
    (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hF hV)).trans
      (CFSG.Quasithin.le_conjClosure (V ⊓ pCoreOf 2 H) H)
  have hI_norm_H : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hU_le_I : U ≤ iSub16 V H := by
    calc U ≤ U ⊔ V₀ := le_sup_left
      _ = V ⊓ pCoreOf 2 H := (Cex16.inf_pCoreOf_eq h1 h5 hS h hF hV).symm
      _ ≤ iSub16 V H := CFSG.Quasithin.le_conjClosure _ _
  have hbase : ∀ x ∈ C, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ iSub16 V H := by
    intro x hx v hv
    have hxC : x ∈ Subgroup.centralizer (iSub16 V H : Set G) := hx.2
    have hxV0 : x ∈ Subgroup.centralizer (V₀ : Set G) :=
      Subgroup.centralizer_le hV0_le_I hxC
    have hxM : x ∈ M := by
      have hxN : x ∈ Subgroup.normalizer (V₀ : Set G) :=
        Subgroup.centralizer_le_normalizer _ hxV0
      rwa [h.hyp.normalizer₀] at hxN
    have hxNV : x ∈ Subgroup.normalizer (V : Set G) := by
      rw [h.hyp.h6.normalizer_eq]
      exact hxM
    have hxvV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxNV v).1 hv
    have hcommV : x * v * x⁻¹ * v⁻¹ ∈ V := V.mul_mem hxvV (V.inv_mem hv)
    have hvxC : v * x * v⁻¹ ∈ Subgroup.centralizer (iSub16 V H : Set G) :=
      w16l_conj_mem_centralizer hI_norm_H hxC (hVH hv)
    have hcommC : x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (iSub16 V H : Set G) := by
      rw [show x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) by group]
      refine Subgroup.mul_mem _ hxC ?_
      rw [show v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hvxC
    have hmem : x * v * x⁻¹ * v⁻¹ ∈ V ⊓ Subgroup.centralizer (iSub16 V H : Set G) :=
      ⟨hcommV, hcommC⟩
    rw [Cex16.inf_centralizer_iSub16_eq h1 h5 hS h hF hV] at hmem
    exact (sup_le hU_le_I hV0_le_I) hmem
  have hgen : ∀ x ∈ (C : Set G), ∀ y ∈ {y : G | ∃ g ∈ H, ∃ v ∈ V, g * v * g⁻¹ = y},
      ⁅x, y⁆ ∈ iSub16 V H := by
    intro x hx y hy
    obtain ⟨g, hg, v, hv, rfl⟩ := hy
    have hgx : g⁻¹ * x * g ∈ C :=
      ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx.1) hg,
        by simpa using w16l_conj_mem_centralizer hI_norm_H hx.2 (H.inv_mem hg)⟩
    have hcomm : ⁅g⁻¹ * x * g, v⁆ ∈ iSub16 V H := hbase _ hgx v hv
    have hconj : g * ⁅g⁻¹ * x * g, v⁆ * g⁻¹ ∈ iSub16 V H :=
      (Subgroup.mem_normalizer_iff.1 (hI_norm_H hg) _).1 hcomm
    have heq : ⁅x, g * v * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, v⁆ * g⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [heq]
    exact hconj
  have hX : Subgroup.closure (C : Set G) ≤ Subgroup.normalizer (iSub16 V H : Set G) := by
    rw [Subgroup.closure_eq]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hY : Subgroup.closure {y : G | ∃ g ∈ H, ∃ v ∈ V, g * v * g⁻¹ = y} ≤
      Subgroup.normalizer (iSub16 V H : Set G) :=
    (IsMinFam16.conjClosure_le_H h hH).trans hI_norm_H
  have hCK : ⁅C, CFSG.Quasithin.conjClosure V H⁆ ≤ iSub16 V H := by
    have h := TauCeti.commutator_closure_closure_le (X := (C : Set G))
      (Y := {y : G | ∃ g ∈ H, ∃ v ∈ V, g * v * g⁻¹ = y}) (N := iSub16 V H) hX hY hgen
    rw [Subgroup.closure_eq] at h
    exact h
  intro x hx k hk
  have h := Subgroup.commutator_le.mp hCK x hx k hk
  simpa only [commutatorElement_def] using h

theorem IsMinFam16.pCore_le_center_bar (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ) :
    ∀ N : Subgroup X, N.Normal → IsPGroup 2 N →
      N ≤ Subgroup.center X ∧
        N ⊓ SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V = ⊥ := by
  intro N hNnormal hN2
  have hF : Fam16 M U S H := hH.1
  have hK_le_H : CFSG.Quasithin.conjClosure V H ≤ H := IsMinFam16.conjClosure_le_H h hH
  have hKH_norm : H ≤ Subgroup.normalizer (CFSG.Quasithin.conjClosure V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure V H
  let P : Subgroup ↥(CFSG.Quasithin.conjClosure V H) := N.comap φ
  have hPnormal : P.Normal := hNnormal.comap φ
  have hI2 : IsPGroup 2 (iSub16 V H) := (Cex16.isElemAbelian_iSub16 h1 hS h hH.1).isPGroup
  have hker : IsPGroup 2 φ.ker := by
    have heq : φ.ker = (iSub16 V H).subgroupOf (CFSG.Quasithin.conjClosure V H) := by
      ext k
      rw [MonoidHom.mem_ker, hφ.ker_iff k, Subgroup.mem_subgroupOf]
    rw [heq]
    exact hI2.of_equiv (Subgroup.subgroupOfEquivOfLe (iSub16_le_conjClosure V H)).symm
  have hP2 : IsPGroup 2 P := IsPGroup.comap_of_ker_isPGroup hN2 φ hker
  have hPle : P ≤ CFSG.pCore 2 ↥(CFSG.Quasithin.conjClosure V H) := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hPnormal, hP2⟩
  have hpCore_le : pCoreOf 2 (CFSG.Quasithin.conjClosure V H) ≤ pCoreOf 2 H :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hK_le_H hKH_norm
  have hPmap : P.map (CFSG.Quasithin.conjClosure V H).subtype ≤
      pCoreOf 2 (CFSG.Quasithin.conjClosure V H) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.map_mono hPle
  have hNcenter : N ≤ Subgroup.center X := by
    have hA_le : (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V : Set X) ⊆
        Subgroup.centralizer (N : Set X) := by
      intro a ha
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro n hn
      obtain ⟨k, hkV, hkφ⟩ := SevenK.mem_barSub.mp ha
      obtain ⟨p, hpφ⟩ := hφ.surjective n
      have hpP : p ∈ P := by
        rw [Subgroup.mem_comap, hpφ]
        exact hn
      have hpCore : (p : G) ∈ pCoreOf 2 (CFSG.Quasithin.conjClosure V H) :=
        hPmap (Subgroup.mem_map_of_mem (CFSG.Quasithin.conjClosure V H).subtype hpP)
      have hcommI : (p : G) * (k : G) * (p : G)⁻¹ * (k : G)⁻¹ ∈ iSub16 V H :=
        Cex16.comm_mem_iSub16_of_mem_pCoreOf h1 h5 hS h hF hV hpCore
          (CFSG.Quasithin.le_conjClosure V H hkV)
      have hcommφ : ⁅φ p, φ k⁆ = 1 := by
        rw [← map_commutatorElement]
        refine (hφ.ker_iff ⁅p, k⁆).mpr ?_
        have heq : ((⁅p, k⁆ : ↥(CFSG.Quasithin.conjClosure V H)) : G) =
            (p : G) * (k : G) * (p : G)⁻¹ * (k : G)⁻¹ := by
          rw [commutatorElement_def]
          rfl
        rw [heq]
        exact hcommI
      rw [← hpφ, ← hkφ]
      exact commutatorElement_eq_one_iff_mul_comm.mp hcommφ
    haveI : (Subgroup.centralizer (N : Set X)).Normal := Subgroup.normal_centralizer
    have htop : (⊤ : Subgroup X) ≤ Subgroup.centralizer (N : Set X) := by
      rw [← (IsMinFam16.normalClosure_barSub h1 hS h hH hV hφ).1]
      exact Subgroup.normalClosure_le_normal hA_le
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro x
    exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top x)) n hn).symm
  refine ⟨hNcenter, ?_⟩
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨haN, haA⟩ := ha
  obtain ⟨k, hkV, hkφ⟩ := SevenK.mem_barSub.mp haA
  have hkP : k ∈ P := by
    rw [Subgroup.mem_comap, hkφ]
    exact haN
  have hkCore : (k : G) ∈ pCoreOf 2 (CFSG.Quasithin.conjClosure V H) :=
    hPmap (Subgroup.mem_map_of_mem (CFSG.Quasithin.conjClosure V H).subtype hkP)
  have hk_inf : (k : G) ∈ V ⊓ pCoreOf 2 H := ⟨hkV, hpCore_le hkCore⟩
  rw [Cex16.inf_pCoreOf_eq h1 h5 hS h hF hV] at hk_inf
  have hU_le_I : U ≤ iSub16 V H := by
    calc U ≤ U ⊔ V₀ := le_sup_left
      _ = V ⊓ pCoreOf 2 H := (Cex16.inf_pCoreOf_eq h1 h5 hS h hF hV).symm
      _ ≤ iSub16 V H := CFSG.Quasithin.le_conjClosure _ _
  have hV0_le_I : V₀ ≤ iSub16 V H :=
    (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hF hV)).trans
      (CFSG.Quasithin.le_conjClosure _ _)
  have hkI : (k : G) ∈ iSub16 V H := (sup_le hU_le_I hV0_le_I) hk_inf
  have hk1 : φ k = 1 := (hφ.ker_iff k).mpr hkI
  rw [← hkφ, hk1]
  exact Subgroup.mem_bot.mpr rfl

section Certified


theorem IsMinFam16.ker_barTheta_central (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ)
    {ρ : X →* LGL 2 D.W}
    (hρ : ∀ k : ↥(CFSG.Quasithin.conjClosure V H),
      ρ (φ k) = D.ρ (IsMinFam16.inclK h hH k))
    {θ : X →* hatX D V}
    (hθ : ∀ k : ↥(CFSG.Quasithin.conjClosure V H), θ (φ k) = IsMinFam16.kToHatX h hH D k) :
    θ.ker ≤ Subgroup.center X ∧
      ((QuotientGroup.mk' (Subgroup.center (hatX D V))).comp θ).ker ≤ Subgroup.center X := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hK_le_H : CFSG.Quasithin.conjClosure V H ≤ H := IsMinFam16.conjClosure_le_H h hH
  have hgen : Subgroup.closure {x : X | x * x = 1} = ⊤ :=
    (IsMinFam16.normalClosure_barSub h1 hS h hH hV hφ).2
  have hO2 : CFSG.pCore 2 X ≤ Subgroup.center X :=
    (IsMinFam16.pCore_le_center_bar h1 h5 hS h hH hV hφ (CFSG.pCore 2 X)
      (CFSG.pCore_normal (p := 2) (G := X)) (CFSG.pCore_isPGroup (p := 2) (G := X))).1
  have hkToHatX : ∀ k : ↥(CFSG.Quasithin.conjClosure V H),
      IsMinFam16.kToHatX h hH D k = QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))
        (⟨D.ρ (IsMinFam16.inclK h hH k),
          D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩⟩ : ↥(hatK D V)) := fun _ => rfl
  have hρker_center : ρ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, hk⟩ := hφ.surjective x
    obtain ⟨k', hk'⟩ := hφ.surjective y
    have hρ1 : D.ρ (IsMinFam16.inclK h hH k) = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      rw [← hk, hρ k] at h
      exact h
    have hkC : (k : G) ∈ Subgroup.centralizer (iSub16 V H : Set G) := by
      have hh := (D.ρ_eq_one_iff (IsMinFam16.inclK h hH k)).mp hρ1
      have h' : (IsMinFam16.inclK h hH k : G) = (k : G) := Subgroup.coe_inclusion _ k
      rw [h'] at hh
      exact hh
    have hcommI := IsMinFam16.comm_centralizer_le h1 h5 hS h hH hV (k : G)
      ⟨hK_le_H k.2, hkC⟩ k' k'.2
    have hcommφ : ⁅φ k, φ k'⁆ = 1 := by
      rw [← map_commutatorElement]
      refine (hφ.ker_iff ⁅k, k'⁆).mpr ?_
      have heq : ((⁅k, k'⁆ : ↥(CFSG.Quasithin.conjClosure V H)) : G) =
          (k : G) * (k' : G) * (k : G)⁻¹ * (k' : G)⁻¹ := by
        rw [commutatorElement_def]
        rfl
      rw [heq]
      exact hcommI
    rw [← hk, ← hk']
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommφ).symm
  have hρker_θ : ρ.ker ≤ θ.ker := by
    intro x hx
    obtain ⟨k, hk⟩ := hφ.surjective x
    have hρ1 : D.ρ (IsMinFam16.inclK h hH k) = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      rw [← hk, hρ k] at h
      exact h
    rw [MonoidHom.mem_ker, ← hk, hθ k, hkToHatX k]
    have hsub : (⟨D.ρ (IsMinFam16.inclK h hH k),
        D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩⟩ : ↥(hatK D V)) = 1 :=
      Subtype.ext hρ1
    rw [hsub, map_one]
  have htwo : ∀ r ∈ θ.ker, ∃ a : ℕ, r ^ 2 ^ a ∈ ρ.ker := by
    intro r hr
    obtain ⟨k, hk⟩ := hφ.surjective r
    have hθ1 : IsMinFam16.kToHatX h hH D k = 1 := by
      have h := hr
      rw [← hk, MonoidHom.mem_ker, hθ k] at h
      exact h
    have hmem : (⟨D.ρ (IsMinFam16.inclK h hH k),
        D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩⟩ : ↥(hatK D V)) ∈
        CFSG.pCore 2 ↥(hatK D V) := by
      rw [hkToHatX k, QuotientGroup.mk'_apply] at hθ1
      exact (QuotientGroup.eq_one_iff _).mp hθ1
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥(hatK D V)) ⟨_, hmem⟩
    refine ⟨a, ?_⟩
    have ha' : (D.ρ (IsMinFam16.inclK h hH k)) ^ 2 ^ a = 1 := by
      have h := congrArg (fun z : ↥(CFSG.pCore 2 ↥(hatK D V)) =>
        ((z : ↥(hatK D V)) : LGL 2 D.W)) ha
      simpa using h
    rw [MonoidHom.mem_ker, ← hk, map_pow, hρ k]
    exact ha'
  have hcommθ : ∀ r ∈ θ.ker, ∀ l : X, ⁅r, l⁆ ∈ θ.ker := by
    intro r hr l
    rw [MonoidHom.mem_ker] at hr ⊢
    rw [map_commutatorElement, hr, commutatorElement_one_left]
  have hθker_center : θ.ker ≤ Subgroup.center X :=
    w16l_central_layers (N := ρ.ker) (R₁ := θ.ker) (R₂ := θ.ker)
      hgen hO2 hρker_center (inferInstance : θ.ker.Normal) hρker_θ htwo le_rfl
      (fun r hr => ⟨1, odd_one, by simpa using hr⟩) hcommθ
  refine ⟨hθker_center, ?_⟩
  set R₂ : Subgroup X := ((QuotientGroup.mk' (Subgroup.center (hatX D V))).comp θ).ker with hR₂
  have hZodd : Odd (Nat.card (Subgroup.center (hatX D V))) :=
    odd_card_center_of_pCore_eq_bot
      (IsMinFam16.barSituation_hat h1 h5 hS h hH hV D).pCore_eq_bot
  have hθ_le_R₂ : θ.ker ≤ R₂ := by
    intro r hr
    rw [MonoidHom.mem_ker] at hr ⊢
    rw [MonoidHom.comp_apply, hr, map_one]
  have hR₂_center : ∀ r ∈ R₂, θ r ∈ Subgroup.center (hatX D V) := by
    intro r hr
    have hr' : (QuotientGroup.mk' (Subgroup.center (hatX D V))) (θ r) = 1 := by
      have h := MonoidHom.mem_ker.mp hr
      rwa [MonoidHom.comp_apply] at h
    rw [QuotientGroup.mk'_apply] at hr'
    exact (QuotientGroup.eq_one_iff (θ r)).mp hr'
  have hR₂odd : ∀ r ∈ R₂, ∃ m : ℕ, Odd m ∧ r ^ m ∈ θ.ker := by
    intro r hr
    refine ⟨Nat.card (Subgroup.center (hatX D V)), hZodd, ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    have hpow : (θ r) ^ Nat.card (Subgroup.center (hatX D V)) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        (Subgroup.orderOf_dvd_natCard (Subgroup.center (hatX D V)) (hR₂_center r hr))
    exact hpow
  have hR₂comm : ∀ r ∈ R₂, ∀ l : X, ⁅r, l⁆ ∈ θ.ker := by
    intro r hr l
    rw [MonoidHom.mem_ker]
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hR₂_center r hr) (θ l)).symm
  exact w16l_central_layers (N := ρ.ker) (R₁ := θ.ker) (R₂ := R₂)
    hgen hO2 hρker_center (inferInstance : θ.ker.Normal) hρker_θ htwo hθ_le_R₂ hR₂odd hR₂comm

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
