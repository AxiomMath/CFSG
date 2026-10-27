module

public import CFSG.RankThree.GF2n.Tim81.FStarSimple
public import CFSG.RankThree.PartOne.S12.Sec15Final
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.GH74.EvenRank
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec15Final
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

structure Sec8SylowData (M : Subgroup G) : Prop where
  exists_sylow : ∃ T : Sylow 2 G, (T : Subgroup G) ≤ M ∧
    ∀ M' : Subgroup G, IsMaximalTwoLocal M' → (T : Subgroup G) ≤ M' → M' = M

structure Sec8ReductionConclusion (M : Subgroup G) : Prop where
  sylow : Sec8SylowData M
  outcome : (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
      Nonempty (G ≃* projSU 3 2 n) ∨ Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (G ≃* projSp 2 (GaloisField 2 n)))) ∨
    (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
    ∀ R : Subgroup G, IsPGroup 2 R → ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = R

theorem sec8_reduction [Finite G] [IsSimpleGroup G] (hPU : PushingUpCorollary)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G) (hchar : IsCharacteristicPType G 2)
    {M V : Subgroup G} (h : Hyp M V) (hempty : ∀ H : Subgroup G, ¬ IsHMember M V H) :
    Sec8ReductionConclusion M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMtop : M ≠ ⊤ := by
    intro htop
    obtain ⟨R, hR1, hR2, hRM⟩ := h.maxLocal.1
    have hnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp (hRM.symm.trans htop)
    haveI : R.Normal := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with hbot | hwhole
    · exact hR1 hbot
    · have hpambient : IsPGroup 2 G := by
        rw [hwhole] at hR2
        exact hR2.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent G := hpambient.isNilpotent
      have hcomm : ∀ a b : G, a * b = b * a :=
        IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable G)
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hcomm a b)
  obtain ⟨T, hTM, hQT⟩ := h.exists_sylow_le_M
  have hMT : ∀ M' : Subgroup G, IsMaximalTwoLocal M' → (T : Subgroup G) ≤ M' → M' ≤ M := by
    intro M' hM' hTM'
    by_contra hM'M
    have hO2ne : inSubgroup (pCore 2) M' ≠ ⊥ := by
      obtain ⟨R, hR1, hR2, hRM'⟩ := hM'.1
      intro hbot
      have hRle : R ≤ inSubgroup (pCore 2) M' := by
        refine Tim78.le_inSubgroup_pCore ?_ ?_ hR2
        · rw [hRM']; exact Subgroup.le_normalizer
        · rw [hRM']
      exact hR1 (le_bot_iff.mp (hRle.trans_eq hbot))
    have hH : IsHMember M V M' :=
      ⟨hO2ne, (inf_le_left : Pc M V ≤ _).trans (hQT.trans hTM'), hM'M⟩
    exact hempty M' hH
  have hMTeq : ∀ M' : Subgroup G, IsMaximalTwoLocal M' → (T : Subgroup G) ≤ M' → M' = M := by
    intro M' hM' hTM'
    have hle := hMT M' hM' hTM'
    by_contra hne
    exact hM'.2 M (lt_of_le_of_ne hle hne) h.maxLocal.1
  have hT₁ : ∀ T₁ : Subgroup G, T₁ ≠ ⊥ → T₁ ≤ pushingUpS (T : Subgroup G) →
      (T₁.subgroupOf (pushingUpS (T : Subgroup G))).Characteristic →
        Subgroup.normalizer (T₁ : Set G) ≤ M := by
    intro T₁ hT₁1 hT₁S hT₁char
    have hT₁2 : IsPGroup 2 T₁ := (T.isPGroup'.to_le (pushingUpS_le _)).to_le hT₁S
    have hXT₁ : (T : Subgroup G) ≤ Subgroup.normalizer (T₁ : Set G) :=
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pushingUpS _)).trans
        (normalizer_le_normalizer_of_characteristic hT₁S hT₁char)
    exact normalizer_le_of_forall_maximal hT₁1 hT₁2 hXT₁
      (fun M' hM' => (hMTeq M' hM'.1 hM'.2).le)
  have hT₂ : ∀ T₂ : Subgroup G, T₂ ≠ ⊥ → T₂ ≤ omegaOneCenterIn (T : Subgroup G) →
      Subgroup.centralizer (T₂ : Set G) ≤ M := by
    intro T₂ hT₂1 hT₂le
    have hT₂2 : IsPGroup 2 T₂ :=
      T.isPGroup'.to_le (hT₂le.trans (omegaOneCenterIn_le _))
    have hY : (T : Subgroup G) ≤
        Subgroup.centralizer (omegaOneCenterIn (T : Subgroup G) : Set G) :=
      fun t ht => Subgroup.mem_centralizer_iff.mpr fun _ hz =>
        ((mem_omegaOneCenterIn_iff.mp hz).2.1 t ht).symm
    have hYT₂ : (T : Subgroup G) ≤ Subgroup.normalizer (T₂ : Set G) :=
      hY.trans ((Subgroup.centralizer_le (fun x hx => hT₂le hx)).trans
        (Subgroup.centralizer_le_normalizer _))
    have hCnorm : Subgroup.centralizer (T₂ : Set G) ≤
        Subgroup.normalizer (T₂ : Set G) :=
      Subgroup.centralizer_le_normalizer (T₂ : Set G)
    exact hCnorm.trans (normalizer_le_of_forall_maximal hT₂1 hT₂2 hYT₂
      (fun M' hM' => (hMTeq M' hM'.1 hM'.2).le))
  refine ⟨⟨T, hTM, hMTeq⟩, ?_⟩
  exact hPU G
    (CFSG.ComponentClassification.CatalogueKProper.kProper_of_isKProper hK)
    (CFSG.GH74.isCharTwoType_iff.mpr hchar) T M hMtop hT₁ hT₂

end CFSG.RankThree.GF2n.Tim81
