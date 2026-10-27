module

public import CFSG.Quasithin.H13.NQCatOddLinearThreeRankOne
public import CFSG.Quasithin.H13.NQCatDegreeThree
public import CFSG.LieType.SteinbergBROddLinearThreeInvolution
public import CFSG.LieType.SteinbergBRPrimeLinearTwoSylow
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Quasithin CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_sylow_le_comap {G Q : Type*} [Group G] [Group Q] [Finite G] (φ : G →* Q)
    (hφ : Function.Surjective φ) (T : Sylow 2 Q) {M : Subgroup Q} (hTM : (T : Subgroup Q) ≤ M) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ M.comap φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective φ hφ
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Q (P₀.mapSurjective hφ) T
  obtain ⟨g, rfl⟩ := hφ c
  refine ⟨g • P₀, ?_⟩
  rw [CFSG.LieType.Chevalley.coe_smul_sylow_eq_map]
  rintro _ ⟨y, hy, rfl⟩
  apply hTM
  rw [← hc, CFSG.LieType.Chevalley.coe_smul_sylow_eq_map, Sylow.coe_mapSurjective]
  refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
  simp [MulAut.conj_apply]

variable {F : Type} [Field F] [Finite F]

theorem prime_linear_three_positive_two_core_actual_rank_one_equality
    (hI : OddLinearThreeInvolutionSylowStructure F) {p : ℕ} [hp : Fact p.Prime]
    (hFp : Nat.card F = p) (hp5 : 5 ≤ p) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ scalars 3 F) (T : Sylow 2 (SL3 F ⧸ D)) {B : Subgroup (SL3 F ⧸ D)}
    (hB : B ∈ cComp (B ⊔ (T : Subgroup (SL3 F ⧸ D))))
    (hO2 : CFSG.pCore 2 ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))) ≠ ⊥) {t : SL3 F ⧸ D}
    (htT : t ∈ (T : Subgroup (SL3 F ⧸ D))) (htZ : ∀ x ∈ (T : Subgroup (SL3 F ⧸ D)), x * t = t * x)
    (ht2 : orderOf t = 2) :
    B = (CFSG.perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D)))).map
        (centralizer ({t} : Set (SL3 F ⧸ D))).subtype ∧
      ∃ z : SL3 F, orderOf z = 2 ∧ QuotientGroup.mk' D z = t ∧
        (∀ w : SL3 F, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
        B = (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) ∧
        Set.InjOn (QuotientGroup.mk' D) (preservingFixing
          (minusSpace (matrixAction F z).toLinearMap) (plusSpace (matrixAction F z).toLinearMap)) ∧
        Nonempty (↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Odd (Nat.card F) := by
    rw [hFp]
    exact hp.out.odd_of_ne_two (by omega)
  have hq : 5 ≤ Nat.card F := hFp ▸ hp5
  obtain ⟨hBL, z, hz, hzt, huniq, hL, hinj, ⟨eL⟩⟩ :=
    odd_linear_three_positive_two_core_rank_one_containment hI hF hq D hD T hB hO2 htT htZ ht2
  suffices hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ≤ Nat.card B by
    have hBeq := eq_of_le_of_card_ge hBL (by rw [Nat.card_congr eL.toEquiv]; exact hcard)
    exact ⟨hBeq, z, hz, hzt, huniq, hBeq.trans hL, hinj,
      ⟨(MulEquiv.subgroupCongr hBeq).trans eL⟩⟩
  subst hzt
  have hDc : D ≤ center (SL3 F) := hD.trans (scalars_le_center 3 F)
  have hfin2 := (matrixAction_finrank F hF z hz).1
  let b := Module.finBasisOfFinrankEq F (minusSpace (matrixAction F z).toLinearMap) hfin2
  let cE := CFSG.LieType.SteinbergBR.OddLinearThreeInv.coordEquiv b
  have : Finite (GL (Fin 2) F) := Finite.of_injective _ Units.val_injective
  have : Finite (minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) := Finite.of_equiv _ cE.symm.toEquiv
  have hMC : B ⊔ (T : Subgroup (SL3 F ⧸ D)) ≤
      centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)) := by
    refine sup_le (hBL.trans (map_subtype_le _)) fun x hx => ?_
    rw [mem_centralizer_singleton_iff]
    exact htZ x hx
  have hBC : B ≤ centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)) := le_sup_left.trans hMC
  have hTC : (T : Subgroup (SL3 F ⧸ D)) ≤
      centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)) := le_sup_right.trans hMC
  set Ct := centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)) with hCt
  set φ := matrixQuotientCentralizer F hF D z hz with hφ
  have hφs : Function.Surjective φ := matrixQuotientCentralizer_surjective F hF D hDc z hz
  set H := ((B ⊔ (T : Subgroup (SL3 F ⧸ D))).subgroupOf Ct).comap φ with hH
  set Bt := (B.subgroupOf Ct).comap φ with hBt
  set C := (CFSG.perfectResidual Bt).map Bt.subtype with hC
  have hB'perf : ⁅B.subgroupOf Ct, B.subgroupOf Ct⁆ = B.subgroupOf Ct := by
    apply Subgroup.map_injective Ct.subtype_injective
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hBC, perfect_of_mem_cComp hB]
  have hCB : C.map φ = B.subgroupOf Ct := map_perfectResidual_comap_eq φ hφs hB'perf
  have hCperf : ⁅C, C⁆ = C := by
    have h1 : Group.IsPerfect (CFSG.perfectResidual Bt) :=
      (CFSG.perfect_residual_characterization (G := Bt)).2.2.1
    rw [Subgroup.isPerfect_iff] at h1
    rw [hC, ← Subgroup.map_commutator, h1]
  have hCBt : C ≤ Bt := map_subtype_le _
  have hBtH : Bt ≤ H :=
    comap_mono fun x hx => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))
  have hCsub : C.subgroupOf Bt = CFSG.perfectResidual Bt :=
    Subgroup.comap_map_eq_self_of_injective Bt.subtype_injective _
  have hCN : (C.subgroupOf Bt).Normal := by
    rw [hCsub]
    exact Subgroup.normal_of_characteristic _
  have hCnorm : ∀ g ∈ Bt, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    have h1 : (⟨c, hCBt hc⟩ : ↥Bt) ∈ C.subgroupOf Bt := mem_subgroupOf.mpr hc
    have h2 := mem_subgroupOf.mp (hCN.conj_mem _ h1 ⟨g, hg⟩)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hTM' : ((T.subtype hTC : Sylow 2 Ct) : Subgroup Ct) ≤
      (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subgroupOf Ct := by
    rw [Sylow.coe_subtype]
    exact fun x hx => mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hx))
  obtain ⟨P, hPH⟩ := exists_sylow_le_comap φ hφs (T.subtype hTC) hTM'
  have hcEs : Function.Surjective cE.toMonoidHom := cE.surjective
  have hSH : ((P.mapSurjective hcEs : Sylow 2 (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F)) ≤
      H.map cE.toMonoidHom := by
    rw [Sylow.coe_mapSurjective]
    exact map_mono hPH
  have hCH : C.map cE.toMonoidHom ≤ H.map cE.toMonoidHom := map_mono (hCBt.trans hBtH)
  have hCne : C.map cE.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hC0 : C = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ cE.injective).mp hbot
    apply ne_bot_of_mem_cComp hB
    have h1 : B.subgroupOf Ct = ⊥ := by rw [← hCB, hC0, Subgroup.map_bot]
    rw [← map_subgroupOf_eq_of_le hBC, h1, Subgroup.map_bot]
  have hCperf' : ⁅C.map cE.toMonoidHom, C.map cE.toMonoidHom⁆ = C.map cE.toMonoidHom := by
    rw [← Subgroup.map_commutator, hCperf]
  have hBM : (B.subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D)))).IsSubnormal :=
    (mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hB)).2.2.1
  have hρmem : ∀ x : ↥(H.map cE.toMonoidHom),
      ((φ (cE.symm (x : GL (Fin 2) F)) : Ct) : SL3 F ⧸ D) ∈ B ⊔ (T : Subgroup (SL3 F ⧸ D)) := by
    intro x
    obtain ⟨a, ha, hax⟩ := x.2
    rw [← hax, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact mem_subgroupOf.mp ha
  let ρ : ↥(H.map cE.toMonoidHom) →* ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))) :=
    (Ct.subtype.comp (φ.comp (cE.symm.toMonoidHom.comp
      (H.map cE.toMonoidHom).subtype))).codRestrict _ hρmem
  have hρ : (B.subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D)))).comap ρ =
      (Bt.map cE.toMonoidHom).subgroupOf (H.map cE.toMonoidHom) := by
    ext x
    rw [mem_comap, mem_subgroupOf, mem_subgroupOf]
    constructor
    · intro hx
      refine ⟨cE.symm (x : GL (Fin 2) F), ?_, by simp⟩
      exact mem_subgroupOf.mpr hx
    · rintro ⟨a, ha, hax⟩
      have : cE.symm (x : GL (Fin 2) F) = a := by
        rw [← hax, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      change ((φ (cE.symm (x : GL (Fin 2) F)) : Ct) : SL3 F ⧸ D) ∈ B
      rw [this]
      exact mem_subgroupOf.mp ha
  have hK : ((Bt.map cE.toMonoidHom).subgroupOf (H.map cE.toMonoidHom)).IsSubnormal := by
    rw [← hρ]
    exact hBM.comap ρ
  have hHK : ((C.map cE.toMonoidHom).subgroupOf (H.map cE.toMonoidHom)).subgroupOf
      ((Bt.map cE.toMonoidHom).subgroupOf (H.map cE.toMonoidHom)) |>.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, hcn⟩ := hn
    have hg := g.2
    rw [mem_subgroupOf] at hg
    obtain ⟨g₀, hg₀, hg₀g⟩ := hg
    refine ⟨g₀ * c * g₀⁻¹, hCnorm g₀ hg₀ c hc, ?_⟩
    simp only [map_mul, map_inv, hcn, hg₀g, Subgroup.coe_mul, Subgroup.coe_inv]
  have hsub : ((C.map cE.toMonoidHom).subgroupOf (H.map cE.toMonoidHom)).IsSubnormal :=
    Subgroup.IsSubnormal.trans
      (fun x hx => by
        rw [mem_subgroupOf] at hx ⊢
        exact map_mono hCBt hx)
      hHK.isSubnormal hK
  have hSL := (CFSG.LieType.prime_linear_two_full_sylow_perfect_subnormal_equality hFp hp5
    ⟨_, hSH⟩ hCH hCne hCperf' hsub).1
  have hinjC : Function.Injective (φ.comp C.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hker : a.1 ∈ φ.ker := MonoidHom.mem_ker.mpr ha
    obtain ⟨c, hc3, -, hac⟩ := (matrixQuotientCentralizer_mem_ker_iff hF hDc hz).mp hker
    have hdet : LinearEquiv.det (a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
        minusSpace (matrixAction F z).toLinearMap) = 1 := by
      have h1 : cE (a : _) ∈ C.map cE.toMonoidHom := ⟨a, a.2, rfl⟩
      rw [hSL] at h1
      obtain ⟨s, hs⟩ := h1
      rw [← CFSG.LieType.SteinbergBR.OddLinearThreeInv.det_coordEquiv b, ← hs]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact s.2
    rw [hac, minus_scalar_det F hF z hz c] at hdet
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, hdet, inv_one, one_mul]
    apply Subtype.ext
    rw [hac, hc1, OneMemClass.coe_one]
    refine LinearEquiv.ext fun v => ?_
    simp [LinearEquiv.smulOfUnit]
  have hcardC : Nat.card C = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← card_map_of_injective (f := cE.toMonoidHom) cE.injective, hSL,
      MonoidHom.range_eq_map, card_map_of_injective
        Matrix.SpecialLinearGroup.toGL_injective, card_top]
  have hcardB : Nat.card B = Nat.card C := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv, ← hCB]
    have h1 : C.map φ = (φ.comp C.subtype).range := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hinjC).toEquiv.symm]
  rw [hcardB, hcardC]

end CFSG.Quasithin.H13.NQCat
