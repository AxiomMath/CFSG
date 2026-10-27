module

public import CFSG.RankThree.GF2n.Smith81.SubConfigHolds
public import CFSG.RankThree.GF2n.Smith81.InspE45
public import CFSG.RankThree.GF2n.Smith81.S81E5Point
public import CFSG.RankThree.GF2n.Smith81.S81G2D6
public import CFSG.RankThree.GF2n.Smith81.S81HE4Field
public import CFSG.RankThree.GF2n.Smith81.S81HE4Iso
public import CFSG.RankThree.GF2n.Smith81.S81HE4Norm
public import CFSG.RankThree.GF2n.Smith81.S81HO12Graph
public import CFSG.RankThree.GF2n.Stroth80.Sec12Certified
public import CFSG.RankThree.GF2n.Stroth80.Sec34ClassicalProof
public import CFSG.GroupTheory.Fitting.SimpleNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXField

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Blueprint CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

section Transport

private theorem map_mem_normalizer_of_isPGroup {G Y : Type*} [Group G] [Finite G] [Group Y]
    [Finite Y] {L Q A : Subgroup G} (φ : L →* Y) (hφ : ∀ s : L, φ s = 1 ↔ (s : G) ∈ Q)
    (hQ : IsPGroup 2 Q) (hAL : A ≤ L)
    (hN : ∀ S : Subgroup G, A ≤ S → S ≤ L → IsPGroup 2 S → ∀ s ∈ L,
      s ∈ Subgroup.normalizer (S : Set G) → s ∈ Subgroup.normalizer (A : Set G))
    {S' : Subgroup Y} (hAS' : (A.subgroupOf L).map φ ≤ S') (hS' : IsPGroup 2 S') (s : L)
    (hs : φ s ∈ Subgroup.normalizer (S' : Set Y)) :
    φ s ∈ Subgroup.normalizer (((A.subgroupOf L).map φ : Subgroup Y) : Set Y) := by
  have hker : φ.ker = Q.comap L.subtype := by
    ext u
    rw [MonoidHom.mem_ker, hφ]
    rfl
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact hQ.comap_of_injective L.subtype Subtype.val_injective
  have hS2 : IsPGroup 2 ((S'.comap φ).map L.subtype) :=
    (hS'.comap_of_ker_isPGroup φ hker2).map L.subtype
  have hAS : A ≤ (S'.comap φ).map L.subtype := fun y hy =>
    ⟨⟨y, hAL hy⟩, hAS' ⟨⟨y, hAL hy⟩, hy, rfl⟩, rfl⟩
  have hsS : (s : G) ∈ Subgroup.normalizer (((S'.comap φ).map L.subtype : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨u, hu, rfl⟩ := hn
    refine ⟨s * u * s⁻¹, ?_, rfl⟩
    change φ (s * u * s⁻¹) ∈ S'
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hs (φ u)).mp (Subgroup.mem_comap.1 hu)
  have hsA := hN _ hAS (Subgroup.map_subtype_le _) hS2 (s : G) s.2 hsS
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨s * u * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hsA (u : G)).mp (Subgroup.mem_subgroupOf.1 hu)

end Transport

section Reduction

theorem lgenBar_eq_fstar_E4_of (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (hSt : Stroth1980Rel) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hb : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h4 : InCaseE4 M Q Z B)
    [(Q.subgroupOf (H0 M Z)).Normal] :
    bar (H0 M Z) Q (Lgen M (LB M Q B)) = generalizedFitting (SubCfgGroup M Q Z) := by
  have hTac := eTacitE4_of_genByB hGen G M Q Z B hb hc h4
  obtain ⟨t, hD, hE4⟩ := h4
  obtain ⟨hN, f, hf, hLF⟩ :=
    lieModel_of_caseE4_recursion hb (hSt _ hb.1) SubCfg.subConfigE4Statement_holds hc hD hE4
  have hS : IsSimpleGroup (FStar (SubCfgGroup M Q Z)) := Timmesfeld.isSimpleGroup_of_lieModel hLF
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hf] at hq4
      norm_num at hq4
    · exact h
  have hFv := Insp.factorization_two_card_of_lieModel hf1
    (by simp [Insp.TimmesfeldTag] : Insp.TimmesfeldTag .POmegaPlus 6 f) hLF
  have hsyl : Smith219Arith.sylowExp .POmegaPlus 6 = 30 := rfl
  rw [hsyl] at hFv
  have h4F : 4 ∣ Nat.card (FStar (SubCfgGroup M Q Z)) := by
    have h := Nat.ordProj_dvd (Nat.card (FStar (SubCfgGroup M Q Z))) 2
    rw [hFv] at h
    exact (pow_dvd_pow 2 (by nlinarith : 2 ≤ f * 30)).trans h
  have hC := Insp.centralizer_fstar_eq_bot hS h4F
  haveI : (generalizedFitting (SubCfgGroup M Q Z)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := SubCfgGroup M Q Z)).2
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ Nonempty (FStar (SubCfgGroup M Q Z) ≃*
        matrixProjectiveDerived (coordinateQuadPlus 6 K)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨GaloisField 2 f, inferInstance, inferInstance, inferInstance,
      GaloisField.card 2 f (by omega),
      CFSG.ComponentClassification.Burgoyne.DX.exists_galois_coordinatePlus
        (LieModel.statedClassicalModel hLF (by decide))⟩
  have hLH := Br37.Lgen_LB_le_H0 hc.ctx
  have hLM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.ctx.LB_le_M
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  have hw : Width Q Z 16 := by simpa [Width] using hE4.1
  have hQ2 : IsPGroup 2 Q := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := f * 33) ?_
    rw [hE4.1, hf, ← pow_mul]
  have hNorm : (bar (H0 M Z) Q (Lgen M (LB M Q B))).Normal := by
    have hn : ((Lgen M (LB M Q B)).subgroupOf (H0 M Z)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2
        ((inf_le_left : H0 M Z ≤ M).trans (Lgen_normalizes M _))
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hne : bar (H0 M Z) Q (Lgen M (LB M Q B)) ≠ ⊥ := by
    intro h
    have htL : t ∈ Lgen M (LB M Q B) := le_Lgen_self M _ hD.2.1
    have hmem : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨t, hLH htL⟩ ∈
        bar (H0 M Z) Q (Lgen M (LB M Q B)) := ⟨⟨t, hLH htL⟩, htL, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hD.2.2.1 hmem
  have hFG := GroupTheory.generalizedFitting_le_of_normal hS hNorm hne
  have hpt : ∀ A : Subgroup G, Ctx M Q Z A →
      Nat.card (LB M Q A) = Nat.card Q * Nat.card Z ^ 15 ∧
        CQt Q Z (LB M Q A) = ((A ⊔ Z : Subgroup G) : Set G) ∧
        LB M Q A ≤ Lgen M (LB M Q B) := by
    intro A hA
    obtain ⟨hno, hgen⟩ := hTac A hA
    obtain ⟨-, hCQt, hLBcard, -⟩ := stroth_3_5 h34 hA hw (by norm_num) hno hgen
    exact ⟨by simpa using hLBcard, hCQt, LB_le_Lgen_of_tacit h34 hc hTac hA⟩
  have hbarcard : ∀ A : Subgroup G, Ctx M Q Z A →
      Nat.card (bar (H0 M Z) Q (LB M Q A)) = Nat.card Z ^ 15 := by
    intro A hA
    obtain ⟨hcard, -, hLBle⟩ := hpt A hA
    have hbar : Nat.card (bar (H0 M Z) Q (LB M Q A)) * Nat.card Q = Nat.card (LB M Q A) :=
      bar_card_mul_card_of_le le_sup_left (hLBle.trans hLH)
    rw [hcard] at hbar
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hbar, mul_comm])
  have hiso : ∀ A : Subgroup G, Ctx M Q Z A → ∀ a ∈ bar (H0 M Z) Q (LB M Q A),
      MulAut.congr e (MulAut.conjNormal a) ∈
        (isometryConjugationHom (coordinateQuadPlus 6 K)).range := by
    intro A hA a ha
    refine mem_range_isometryConjugationHom_of_card hC hf1 hK e ?_ ?_ ha
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hA.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hx)
    · rw [hbarcard A hA, hf, ← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hgen_le : ∀ P : Subgroup (SubCfgGroup M Q Z),
      (∀ A : Subgroup G, Ctx M Q Z A → bar (H0 M Z) Q (LB M Q A) ≤ P) →
      bar (H0 M Z) Q (Lgen M (LB M Q B)) ≤ P := by
    intro P hP
    have hP' : Lgen M (LB M Q B) ≤ (P.comap (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)))).map
        (H0 M Z).subtype := by
      refine Br37.Lgen_le_of fun m hm x hx => ?_
      have hxH : x ∈ H0 M Z := hLH (Br37.conj_le_Lgen hm hx)
      rw [← hc.ctx.LB_conj hm] at hx
      exact ⟨⟨x, hxH⟩, hP _ (hc.ctx.conj_of_mem hm) ⟨⟨x, hxH⟩, hx, rfl⟩, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hP' (Subgroup.mem_subgroupOf.1 hx)
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hY : ∀ y ∈ bar (H0 M Z) Q (Lgen M (LB M Q B)), MulAut.congr e (MulAut.conjNormal y) ∈
      (isometryConjugationHom (coordinateQuadPlus 6 K)).range := fun y hy =>
    hgen_le (((isometryConjugationHom (coordinateQuadPlus 6 K)).range).comap
      ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)) (fun A hA a ha => hiso A hA a ha) hy
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadPlus 6 K (by norm_num)
  obtain ⟨ψ, hψinj, hψO, hOψ, hψF⟩ := OrthModel.exists_isometric_model hnd hT3 hC e hFG hY
  let ρ : Lgen M (LB M Q B) →* bar (H0 M Z) Q (Lgen M (LB M Q B)) :=
    ((QuotientGroup.mk' (Q.subgroupOf (H0 M Z))).comp (Subgroup.inclusion hLH)).codRestrict _
      fun s => ⟨Subgroup.inclusion hLH s, s.2, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨(x : G), hx⟩, rfl⟩
  let φ := ψ.comp ρ
  have hφker : ∀ s, φ s = 1 ↔ (s : G) ∈ Q := by
    intro s
    have h1 : φ s = 1 ↔ ρ s = 1 := by
      change ψ (ρ s) = 1 ↔ _
      rw [← map_one ψ, hψinj.eq_iff]
    rw [h1, ← Subtype.coe_inj]
    change QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) (Subgroup.inclusion hLH s) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hHO : φ.range ≤ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 6 K) := by
    rintro _ ⟨s, rfl⟩
    exact hψO _
  have hOH : ⁅TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 6 K),
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 6 K)⁆ ≤ φ.range := by
    intro h hh
    obtain ⟨y, rfl⟩ := hOψ hh
    obtain ⟨s, rfl⟩ := hρ y
    exact ⟨s, rfl⟩
  obtain ⟨K', _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨T, hTe, -⟩ := exists_T_Lgen hc.ctx hg
  haveI : Finite ((Fin (2 * 6) → K) ≃ₗ[K] (Fin (2 * 6) → K)) :=
    Finite.of_injective (fun g : (Fin (2 * 6) → K) ≃ₗ[K] (Fin (2 * 6) → K) =>
      (g : (Fin (2 * 6) → K) → Fin (2 * 6) → K)) DFunLike.coe_injective
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hf]
    exact hq4
  have hV : Module.finrank K (Fin (2 * 6) → K) = 2 * 5 + 2 := by simp
  have hLBF : ∀ A : Subgroup G, Ctx M Q Z A →
      bar (H0 M Z) Q (LB M Q A) ≤ generalizedFitting (SubCfgGroup M Q Z) := by
    intro A hA
    obtain ⟨hcard, hCQt, hLBle⟩ := hpt A hA
    have hE2 : ∀ x ∈ ((LB M Q A).subgroupOf (Lgen M (LB M Q B))).map φ, x * x = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, hφker, Subgroup.coe_mul, ← pow_two]
      exact hA.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hu)
    have hEk : Nat.card ↥(((LB M Q A).subgroupOf (Lgen M (LB M Q B))).map φ) =
        Nat.card K ^ 15 := by
      have key : Nat.card (LB M Q A) =
          Nat.card Q * Nat.card ↥(((LB M Q A).subgroupOf (Lgen M (LB M Q B))).map φ) :=
        card_eq_card_mul_card_map_of_ker (S := LB M Q A) φ hφker hQLg le_sup_left hLBle
      rw [hcard] at key
      rw [hK, ← hf]
      exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos key).symm
    have hEO := OrthGraph.le_commutator_of_normalizer hK4 hnd hV hHO hOH
      (Subgroup.map_le_range φ _) hE2 hEk fun S' hES' _ hS' h hh hhS' => by
        obtain ⟨s, rfl⟩ := hh
        exact map_mem_normalizer_of_isPGroup φ hφker hQ2 hLBle
          (fun S hAS hSL hS2 x hx hxS =>
            mem_normalizer_LB_of_isPGroup hg hA hCQt hLM T hTe hAS hSL hS2 hx hxS)
          hES' hS' s hhS'
    rintro _ ⟨x, hx, rfl⟩
    have hxL : (x : G) ∈ Lgen M (LB M Q B) := hLBle (Subgroup.mem_subgroupOf.1 hx)
    exact hψF (ρ ⟨(x : G), hxL⟩) (hEO ⟨⟨(x : G), hxL⟩, Subgroup.mem_subgroupOf.1 hx, rfl⟩)
  exact le_antisymm (hgen_le _ hLBF) hFG

theorem exists_lgen_hom_EAut0_E4_of (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (hSt : Stroth1980Rel) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hb : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h4 : InCaseE4 M Q Z B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
      ∃ θ : Lgen M (LB M Q B) →* D6Spin.EAut0 K,
        Function.Surjective θ ∧ ∀ s, θ s = 1 ↔ (s : G) ∈ Q := by
  obtain ⟨t, hD, hE4⟩ := h4
  obtain ⟨hN, f, hf, hLF⟩ :=
    lieModel_of_caseE4_recursion hb (hSt _ hb.1) SubCfg.subConfigE4Statement_holds hc hD hE4
  haveI := hN
  have hEq := lgenBar_eq_fstar_E4_of h34 hGen hSt hb hc ⟨t, hD, hE4⟩
  obtain ⟨K, _, _, _, hK, ⟨g⟩⟩ := D6Spin.exists_equiv_LamW_of_lieModel hLF
  have hLH := Br37.Lgen_LB_le_H0 hc.ctx
  set ρ : ↥(Lgen M (LB M Q B)) →* SubCfgGroup M Q Z :=
    (QuotientGroup.mk' (Q.subgroupOf (H0 M Z))).comp (Subgroup.inclusion hLH) with hρ
  have hρF : ∀ s, ρ s ∈ generalizedFitting (SubCfgGroup M Q Z) := fun s => by
    rw [← hEq]
    exact ⟨Subgroup.inclusion hLH s, s.2, rfl⟩
  set ρ' := ρ.codRestrict _ hρF
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK.trans hf.symm,
    (D6Spin.lamWEquivEAut0 K).toMonoidHom.comp (g.toMonoidHom.comp ρ'), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := (D6Spin.lamWEquivEAut0 K).surjective y
    obtain ⟨u, rfl⟩ := g.surjective x
    have hu : (u : SubCfgGroup M Q Z) ∈ bar (H0 M Z) Q (Lgen M (LB M Q B)) := by
      rw [hEq]
      exact u.2
    obtain ⟨v, hv, hvu⟩ := hu
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [← hx]
    change (D6Spin.lamWEquivEAut0 K) (g (ρ' ⟨v, hv⟩)) = _
    congr 2
    exact Subtype.ext hvu
  · intro s
    change (D6Spin.lamWEquivEAut0 K) (g (ρ' s)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← Subtype.coe_inj]
    change ρ s = 1 ↔ _
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl

end Reduction

section Certified

theorem exists_lgen_hom_EAut0_E4 (hSt : Stroth1980Rel)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hb : Smith1981Below (Nat.card G))
    (hc : SmithECfg M Q Z B) (h4 : InCaseE4 M Q Z B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
      ∃ θ : Lgen M (LB M Q B) →* D6Spin.EAut0 K,
        Function.Surjective θ ∧ ∀ s, θ s = 1 ↔ (s : G) ∈ Q :=
  exists_lgen_hom_EAut0_E4_of stroth34Statement_unconditional strothGenByBStatement_certified hSt
    hb hc h4

end Certified

end CFSG.RankThree.GF2n.Smith81
