module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeen
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Central

theorem ggCenterQuotEquiv_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem ggLieModel_psl_two_four_of_alt {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : LieModel Y .PSL 2 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hK, ⟨e.trans e5.symm⟩⟩

end Central

section Image

variable {G : Type} [Group G]

theorem ggAutK_image_component {E₀ K M C L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ C)
    (hL₁K : L₁ ≤ K) (hL₁M : L₁ ≤ M) (hH₀C : E₀ ⊔ (K ⊓ M) ≤ C) (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hEK : E₀ ≤ Subgroup.normalizer (K : Set G)) {W' : Type} [Group W'] [Finite W']
    (π : ↥(E₀ ⊔ K) →* W') (hπ : Function.Surjective π)
    (hker : π.ker ≤ ((E₀ ⊔ (K ⊓ M)) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf (E₀ ⊔ K)) :
    IsComponentOf ((L₁.subgroupOf (E₀ ⊔ K)).map π)
        (((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π ⊓ CFSG.generalizedFitting W') ∧
      Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃*
        ↥((L₁.subgroupOf (E₀ ⊔ K)).map π) ⧸
          Subgroup.center ↥((L₁.subgroupOf (E₀ ⊔ K)).map π)) := by
  have hL₁H₀ : L₁ ≤ E₀ ⊔ (K ⊓ M) := (le_inf hL₁K hL₁M).trans le_sup_right
  have hcomp : IsComponentOf L₁ (E₀ ⊔ (K ⊓ M)) :=
    ⟨hL₁H₀, ggIsSubnormal_of_le_of_le hL₁.2.1 hL₁H₀ hH₀C, hL₁.2.2⟩
  have hH₀W₀ : E₀ ⊔ (K ⊓ M) ≤ E₀ ⊔ K := sup_le_sup_left inf_le_left E₀
  have hcomp' := ggIsComponentOf_subgroupOf hcomp hH₀W₀
  have hkerC : ∀ w : ↥(E₀ ⊔ K), π w = 1 → (w : G) ∈ Subgroup.centralizer (K : Set G) :=
    fun w hw => (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).2
  have hnotker : ¬ L₁.subgroupOf (E₀ ⊔ K) ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hL₁ fun a ha c hc => ?_
    have haW : a ∈ E₀ ⊔ K := (hL₁K.trans le_sup_right) ha
    have haC := hkerC ⟨a, haW⟩ (hle (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, haW⟩ : ↥(E₀ ⊔ K)) ∈ L₁.subgroupOf (E₀ ⊔ K)))
    exact (Subgroup.mem_centralizer_iff.mp haC c (hL₁K hc)).symm
  have hcompH := ggIsComponentOf_map π hcomp' hnotker
  have hKW : K ≤ E₀ ⊔ K := le_sup_right
  have hKn : (K.subgroupOf (E₀ ⊔ K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKW]
    intro h k hh hk
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := (sup_le hEK Subgroup.le_normalizer) hk
    exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
  have hKcW : IsComponentOf K (E₀ ⊔ K) := ⟨hKW, ggIsSubnormal_of_normal hKW hKn, hKq⟩
  have hKcomp : CFSG.IsComponent (K.subgroupOf (E₀ ⊔ K)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKW).mp hKcW
  have hKnotker : ¬ K.subgroupOf (E₀ ⊔ K) ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hKcW fun a ha c hc => ?_
    have haC := hkerC ⟨a, hKW ha⟩ (hle (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, hKW ha⟩ : ↥(E₀ ⊔ K)) ∈ K.subgroupOf (E₀ ⊔ K)))
    exact (Subgroup.mem_centralizer_iff.mp haC c hc).symm
  have hKbar : CFSG.IsComponent ((K.subgroupOf (E₀ ⊔ K)).map π) :=
    ⟨CFSG.LocalCores.isQuasisimple_map hKcomp.1 π hKnotker, (hKn.map π hπ).isSubnormal⟩
  have hKF : (K.subgroupOf (E₀ ⊔ K)).map π ≤ CFSG.generalizedFitting W' :=
    (CFSG.LocalCores.component_le_layer hKbar).trans le_sup_right
  have hLK : (L₁.subgroupOf (E₀ ⊔ K)).map π ≤ (K.subgroupOf (E₀ ⊔ K)).map π :=
    Subgroup.map_mono fun w hw =>
      Subgroup.mem_subgroupOf.mpr (hL₁K (Subgroup.mem_subgroupOf.mp hw))
  have hle : (L₁.subgroupOf (E₀ ⊔ K)).map π ≤
      ((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π ⊓ CFSG.generalizedFitting W' :=
    le_inf hcompH.1 (hLK.trans hKF)
  refine ⟨⟨hle, ggIsSubnormal_of_le_of_le hcompH.2.1 hle inf_le_left, hcompH.2.2⟩, ?_⟩
  have hL₁W : L₁ ≤ E₀ ⊔ K := hL₁K.trans le_sup_right
  set φ : ↥L₁ →* W' := π.comp (Subgroup.inclusion hL₁W)
  have hφmem : ∀ l : ↥L₁, φ l ∈ (L₁.subgroupOf (E₀ ⊔ K)).map π := fun l =>
    ⟨Subgroup.inclusion hL₁W l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  set φ' : ↥L₁ →* ↥((L₁.subgroupOf (E₀ ⊔ K)).map π) := φ.codRestrict _ hφmem
  have hφ' : Function.Surjective φ' := by
    rintro ⟨y, w, hw, rfl⟩
    refine ⟨⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩, Subtype.ext ?_⟩
    rfl
  have hkerφ : φ'.ker ≤ Subgroup.center ↥L₁ := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : π (Subgroup.inclusion hL₁W l) = 1 := congrArg Subtype.val hl
    have hlC := hkerC _ h1
    rw [Subgroup.mem_center_iff]
    intro l'
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hlC l' (hL₁K l'.2))
  have hperf : Group.IsPerfect ↥L₁ :=
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL₁.2.2).1
  exact ggCenterQuotEquiv_of_surjective hperf φ' hφ' hkerφ

end Image

section Table

theorem ggSixSeventeen_not_fusionException {G : Type} [Group G]
    {p : ℕ} {t : StatedLieTag} {f : ℕ} {L₁ : Subgroup G} (hnex : ¬ GGSixSeventeenExcluded p t f L₁)
    {W' : Type} [Group W'] [Finite W'] {H E C : Subgroup W'}
    (hC : IsComponentOf C (H ⊓ CFSG.generalizedFitting W'))
    (he : Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* ↥C ⧸ Subgroup.center ↥C)) :
    ¬ GGFusionException p H E := by
  obtain ⟨e⟩ := he
  rintro (⟨-, -, hnc⟩ | ⟨hp5, -, hall⟩ |
      ⟨-, ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨-, -, hnc⟩ | ⟨-, -, hnc⟩⟩ |
      ⟨hp5, -, hall⟩)
  · exact hnc C hC
  · obtain ⟨e5⟩ := hall C hC
    exact hnex (Or.inr (Or.inl ⟨hp5, Or.inl (ggLieModel_psl_two_four_of_alt (e.trans e5))⟩))
  · exact hnex (Or.inl ⟨hp3, Or.inr (Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC)))⟩)
  · exact hnex (Or.inl ⟨hp3, Or.inl (lieModel_of_mulEquiv' e.symm (hall C hC))⟩)
  · obtain ⟨e6⟩ := hall C hC
    exact hnex (Or.inl ⟨hp3, Or.inr (Or.inl ⟨e.trans e6⟩)⟩)
  · exact hnc C hC
  · exact hnc C hC
  · exact hnex (Or.inr (Or.inl ⟨hp5, Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC))⟩))

end Table

section Inputs

@[expose] def GGSixAutKHypRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∃ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m ⊓
              Subgroup.centralizer (K : Set G)).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteenRest p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

theorem ggSixSeventeenAutKInput_of_rest (hR : GGSixAutKHypRestInput) :
    GGSixSeventeenAutKInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ hpair K hK hLK hKM
  obtain ⟨m, hm, hEC, W', _, _, π, hπ, hker, hrest⟩ :=
    hR G p B Bs x L D J t n f ψ hctx s1 b hpair.1 hpair.2.1 L₁ hpair.2.2.1 K hK hLK hKM
  refine ⟨m, hm, hEC, W', inferInstance, inferInstance, π, hπ, hker, hrest, ?_⟩
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1
        (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := hfusE.1
  have hH₀C : D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ ggM p B x L D J) ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    sup_le (le_inf hEM hEC) (le_inf inf_le_right (inf_le_left.trans hK.1))
  obtain ⟨hC, he⟩ := ggAutK_image_component hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C
    hK.2.2 hnorm π hπ hker
  exact ggSixSeventeen_not_fusionException hpair.2.2.2 hC he

theorem ggSixLemmaSixSeventeenInput_of_rest
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixAutKHypRestInput)
    (hW : GGSixSeventeenWitnessInputFor fun _ => True)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput :=
  ggSixLemmaSixSeventeenInput_of_schreier hSch hKF (ggSixSeventeenAutKInput_of_rest hR) hW
    h610 h611 h612 h613t hlin

end Inputs

end CFSG.StandardType
