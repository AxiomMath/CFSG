module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6CommAux1
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.GroupTheory.PCoreSurjective
import CFSG.GroupTheory.CommutatorMemSubgroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
public import CFSG.Adapters.LieModelSimple
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c6_comm (D : Data G) {K P X : Subgroup G} (hK : K ∈ calC D.M)
    (hKN : D.M ≤ normalizer (K : Set G)) {n : ℕ} (hn : 1 < n) (hU : IsU4 (Bar2 K) n)
    (hT : ∀ {P' X' R' : Subgroup (Bar2 K)}, IsParabolicTwo (Bar2 K) P' → X' = F07.DerInf P' →
      IsL2 (Bar2 X') (2 * n) → X' ≤ R' → R' = ⊤ ∨ R' ≤ P')
    (hP : ParabolicOf K P) (hX : X = F07.DerInf P) (hL2 : IsL2 (Bar2 X) (2 * n))
    (hXp : pCoreOf 2 X ≠ ⊥) : ∀ A ∈ F09.Inv9' D.M X 3, ⁅A, X⁆ ≤ pCoreOf 2 A := by
  intro A hA
  obtain ⟨hAM, hA3, hXA⟩ := hA
  have hPK : P ≤ K := hP.2.1
  have hXK : X ≤ K := hX ▸ (Subgroup.map_subtype_le _).trans hPK
  have hKsub : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hAK : A ≤ normalizer (K : Set G) := hAM.trans hKN
  set B : Subgroup G := A ⊓ K with hB_def
  have hBA : B ≤ A := inf_le_left
  have hBK : B ≤ K := inf_le_right
  have hB3 : ¬ 3 ∣ Nat.card B := fun h => hA3 (h.trans (Subgroup.card_dvd_of_le hBA))
  have hXB : X ≤ normalizer (B : Set G) :=
    (le_inf hXA (hXK.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAB : A ≤ normalizer (B : Set G) :=
    (le_inf Subgroup.le_normalizer hAK).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAXB : ⁅A, X⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [h]
      exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hXA hx) a⁻¹).1 (A.inv_mem ha))
    · rw [commutatorElement_def]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAK ha) x).1 (hXK hx))
        (K.inv_mem (hXK hx))
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Bb : Subgroup (Bar2 K) := (B.subgroupOf K).map π
  let Pb : Subgroup (Bar2 K) := (P.subgroupOf K).map π
  let Xb : Subgroup (Bar2 K) := (X.subgroupOf K).map π
  have hXb_eq : Xb = F07.DerInf Pb := by
    have h1 := CFSG.perfectResidual_subtype_subgroupOf P K hPK
    have hXsub : X.subgroupOf K =
        (perfectResidual ↥(P.subgroupOf K)).map (P.subgroupOf K).subtype := by
      rw [← h1, hX]
      rfl
    change (X.subgroupOf K).map π = F07.DerInf ((P.subgroupOf K).map π)
    rw [hXsub]
    exact SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map π (P.subgroupOf K)
  have hL2b : IsL2 (Bar2 Xb) (2 * n) := by
    let g : ↥(X.subgroupOf K) →* ↥Xb :=
      (π.comp (X.subgroupOf K).subtype).codRestrict Xb
        (fun z => Subgroup.mem_map_of_mem π z.2)
    have hgsurj : Function.Surjective g := by
      intro y
      have hy : (y : Bar2 K) ∈ (X.subgroupOf K).map π := y.2
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
    have hgker : g.ker = (CFSG.pCore 2 ↥K).comap (X.subgroupOf K).subtype := by
      ext z
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      constructor
      · intro hz
        have h1 : π (z : ↥K) = 1 := congrArg Subtype.val hz
        exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) (z : ↥K)).mp h1
      · intro hz
        apply Subtype.ext
        have h2 : (z : ↥K) ∈ π.ker := by
          rw [show π.ker = CFSG.pCore 2 ↥K from QuotientGroup.ker_mk' _]
          exact hz
        exact (MonoidHom.mem_ker).1 h2
    have hg2 : IsPGroup 2 g.ker := by
      rw [hgker]
      exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2)) _
        (Subgroup.subtype_injective _)
    let eX : ↥(X.subgroupOf K) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
    let f : ↥X →* ↥Xb := g.comp eX.symm.toMonoidHom
    have hfsurj : Function.Surjective f := hgsurj.comp eX.symm.surjective
    have hf2 : IsPGroup 2 f.ker := by
      have hker : f.ker = g.ker.comap eX.symm.toMonoidHom := by
        ext x
        rw [Subgroup.mem_comap, MonoidHom.mem_ker]
        rfl
      rw [hker]
      exact IsPGroup.comap_of_injective hg2 _ eX.symm.injective
    obtain ⟨eBar⟩ :=
      CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hfsurj hf2
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar hL2
  have hPb : IsParabolicTwo (Bar2 K) Pb := hP.2.2
  have hTres : Bb ⊔ Xb = ⊤ ∨ Bb ⊔ Xb ≤ Pb := hT hPb hXb_eq hL2b le_sup_right
  have hXBK : X.subgroupOf K ≤ Subgroup.normalizer (B.subgroupOf K : Set ↥K) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
    rw [show ((z * b * z⁻¹ : ↥K) : G) = (z : G) * (b : G) * (z : G)⁻¹ by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]]
    exact (Subgroup.mem_normalizer_iff.mp (hXB hzX) (b : G))
  have hXbN : Xb ≤ Subgroup.normalizer (Bb : Set (Bar2 K)) :=
    (Subgroup.map_mono hXBK).trans (Subgroup.le_normalizer_map π)
  have hcardB : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  have h3K : 3 ∣ Nat.card (Bar2 K) := by
    have h3Xb : 3 ∣ Nat.card (Bar2 Xb) := three_dvd_card_of_isL2 hL2b
    have h1 : 3 ∣ Nat.card ↥Xb :=
      h3Xb.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥Xb))
    have h2 : 3 ∣ Nat.card ↥(⊤ : Subgroup (Bar2 K)) :=
      h1.trans (Subgroup.card_dvd_of_le (le_top : Xb ≤ ⊤))
    simpa using h2
  have hBBb : ⁅Bb, Xb⁆ ≤ pCoreOf 2 Bb := by
    rcases hTres with htop | hle
    · have hBn : Bb.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (by
        rw [← htop]
        exact sup_le Subgroup.le_normalizer hXbN))
      haveI : Bb.Normal := hBn
      haveI : IsSimpleGroup (Bar2 K) :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
      rcases Subgroup.Normal.eq_bot_or_eq_top Bb with hbot | htp
      · rw [hbot]; simp
      · exfalso
        have h3B : 3 ∣ Nat.card (B.subgroupOf K) := by
          have h3Bb : 3 ∣ Nat.card Bb := by rw [htp, Subgroup.card_top]; exact h3K
          exact h3Bb.trans (Subgroup.card_map_dvd (B.subgroupOf K) π)
        rw [hcardB] at h3B
        exact hB3 h3B
    · have hBbPb : Bb ≤ Pb := le_trans le_sup_left hle
      have hXbPb : Xb ≤ Pb := le_trans le_sup_right hle
      have hXb_norm_Pb : (Xb.subgroupOf Pb).Normal := by
        have h1 : (F07.DerInf Pb).subgroupOf Pb = perfectResidual ↥Pb := by
          change Subgroup.comap Pb.subtype
            ((perfectResidual ↥Pb).map Pb.subtype) = perfectResidual ↥Pb
          exact Subgroup.comap_map_eq_self_of_injective Pb.subtype_injective _
        rw [hXb_eq, h1]
        haveI : (perfectResidual ↥Pb).Characteristic :=
          CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic (G := ↥Pb)
        exact inferInstance
      have hBbNormXb : Bb ≤ Subgroup.normalizer (Xb : Set (Bar2 K)) :=
        hBbPb.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hXbPb).mp hXb_norm_Pb)
      have h1 : ⁅Bb, Xb⁆ ≤ Bb ⊓ Xb := by
        rw [Subgroup.commutator_le]
        intro b hb x hx
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h : x * b⁻¹ * x⁻¹ ∈ Bb :=
            (Subgroup.mem_normalizer_iff.mp (hXbN hx) b⁻¹).1 (Bb.inv_mem hb)
          simpa only [commutatorElement_def, mul_assoc] using Bb.mul_mem hb h
        · have h : b * x * b⁻¹ ∈ Xb :=
            (Subgroup.mem_normalizer_iff.mp (hBbNormXb hb) x).1 hx
          simpa only [commutatorElement_def, mul_assoc] using Xb.mul_mem h (Xb.inv_mem hx)
      have hBinf : Bb ⊓ Xb ≤ pCoreOf 2 Xb := by
        have hN : ((Bb ⊓ Xb).subgroupOf Xb).Normal := by
          refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
          exact (le_inf hXbN Subgroup.le_normalizer).trans
            Subgroup.inf_normalizer_le_normalizer_inf
        have hmapN : (((Bb ⊓ Xb).subgroupOf Xb).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb))).Normal :=
          hN.map _ (QuotientGroup.mk'_surjective _)
        have hmap3 : ¬ 3 ∣ Nat.card (((Bb ⊓ Xb).subgroupOf Xb).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb))) := by
          intro h
          exact hB3 (by
            have h1 : 3 ∣ Nat.card ↥(Bb ⊓ Xb) := by
              have heq : Nat.card ↥((Bb ⊓ Xb).subgroupOf Xb) = Nat.card ↥(Bb ⊓ Xb) :=
                Nat.card_congr
                  (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bb ⊓ Xb ≤ Xb)).toEquiv
              have h' : 3 ∣ Nat.card ↥((Bb ⊓ Xb).subgroupOf Xb) :=
                h.trans (Subgroup.card_map_dvd ((Bb ⊓ Xb).subgroupOf Xb)
                  (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb)))
              rwa [heq] at h'
            have h2 : 3 ∣ Nat.card ↥Bb :=
              h1.trans (Subgroup.card_dvd_of_le (inf_le_left : Bb ⊓ Xb ≤ Bb))
            have h3 : 3 ∣ Nat.card (B.subgroupOf K) :=
              h2.trans (Subgroup.card_map_dvd (B.subgroupOf K) π)
            rwa [hcardB] at h3)
        haveI : IsSimpleGroup (Bar2 Xb) :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2b
        rcases Subgroup.Normal.eq_bot_or_eq_top
          (((Bb ⊓ Xb).subgroupOf Xb).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb))) with
          hbot | htp
        · have hle : (Bb ⊓ Xb).subgroupOf Xb ≤ CFSG.pCore 2 ↥Xb := by
            intro z hz
            have hz' : (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb)) z ∈
                (((Bb ⊓ Xb).subgroupOf Xb).map
                  (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb))) :=
              Subgroup.mem_map_of_mem _ hz
            rw [hbot, Subgroup.mem_bot] at hz'
            exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Xb) z).mp hz'
          calc Bb ⊓ Xb = ((Bb ⊓ Xb).subgroupOf Xb).map Xb.subtype :=
                (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
            _ ≤ (CFSG.pCore 2 ↥Xb).map Xb.subtype := Subgroup.map_mono hle
            _ = pCoreOf 2 Xb := rfl
        · exfalso
          have : 3 ∣ Nat.card (((Bb ⊓ Xb).subgroupOf Xb).map
              (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb))) := by
            rw [htp, Subgroup.card_top]
            exact three_dvd_card_of_isL2 hL2b
          exact hmap3 this
      have hXbChar : Bb ≤ Subgroup.normalizer (pCoreOf 2 Xb : Set (Bar2 K)) :=
        hBbNormXb.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Xb)
      have hN2 : ((Bb ⊓ pCoreOf 2 Xb).subgroupOf Bb).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
        exact (le_inf Subgroup.le_normalizer hXbChar).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have h2 : Bb ⊓ pCoreOf 2 Xb ≤ pCoreOf 2 Bb :=
        CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hN2
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Xb).to_le inf_le_right)
      exact h1.trans ((le_inf inf_le_left hBinf).trans h2)
  have hBXW : ⁅B, X⁆ ≤ pCoreOf 2 B := by
    have hCB : ⁅B.subgroupOf K, X.subgroupOf K⁆ ≤ B.subgroupOf K := by
      rw [Subgroup.commutator_le]
      intro b hb x hx
      rw [Subgroup.mem_subgroupOf] at hb hx ⊢
      have hxb : (x : G) * (b : G)⁻¹ * (x : G)⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hXB hx) (b : G)⁻¹).1 (B.inv_mem hb)
      rw [show ((⁅b, x⁆ : ↥K) : G) = (b : G) * ((x : G) * (b : G)⁻¹ * (x : G)⁻¹) by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group]
      exact B.mul_mem hb hxb
    have hstep : ⁅B.subgroupOf K, X.subgroupOf K⁆ ≤ CFSG.Open.pCoreOf 2 (B.subgroupOf K) :=
      s16c6_le_pCoreOf_of_map_le π (QuotientGroup.mk'_surjective _)
        (by rw [show π.ker = CFSG.pCore 2 ↥K from QuotientGroup.ker_mk' _]
            exact CFSG.pCore_isPGroup)
        hCB (by rw [Subgroup.map_commutator]; exact hBBb)
    have hmap2 : (CFSG.Open.pCoreOf 2 (B.subgroupOf K)).map K.subtype ≤ pCoreOf 2 B := by
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 ?_ ?_ ?_
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
        exact CFSG.LieType.BorelTits.pCoreOf_le 2 (B.subgroupOf K) hy
      · have hNB : (CFSG.Open.pCoreOf 2 (B.subgroupOf K)).map K.subtype ≤ B :=
          (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 (B.subgroupOf K))).trans
            (le_of_eq (Subgroup.map_subgroupOf_eq_of_le hBK))
        have hnorm : B.subgroupOf K ≤ Subgroup.normalizer
            (CFSG.Open.pCoreOf 2 (B.subgroupOf K) : Set ↥K) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (B.subgroupOf K)
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr ?_
        have h3 := (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map K.subtype)
        rwa [Subgroup.map_subgroupOf_eq_of_le hBK] at h3
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (B.subgroupOf K)).map K.subtype
    calc ⁅B, X⁆ = (⁅B.subgroupOf K, X.subgroupOf K⁆).map K.subtype := by
          rw [Subgroup.map_commutator]
          rw [Subgroup.map_subgroupOf_eq_of_le hBK, Subgroup.map_subgroupOf_eq_of_le hXK]
      _ ≤ (CFSG.Open.pCoreOf 2 (B.subgroupOf K)).map K.subtype := Subgroup.map_mono hstep
      _ ≤ pCoreOf 2 B := hmap2
  have hperfx : ⁅X, X⁆ = X := by
    rw [hX]
    change ⁅(perfectResidual ↥P).map P.subtype, (perfectResidual ↥P).map P.subtype⁆ =
      (perfectResidual ↥P).map P.subtype
    exact Subgroup.isPerfect_iff.mp
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map P)
  have hsimpleX : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have h3X : 3 ∣ Nat.card (Bar2 X) := three_dvd_card_of_isL2 hL2
  have hXopp : Opp 3 X = X := s16c6_opp3_eq_self hperfx hsimpleX h3X
  have hWnorm : A ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
    hAB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B)
  have hXWnorm : X ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
    hXB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B)
  have hcop3 : ∀ a ∈ A, ∀ x ∈ X, ⁅x, a⁆ ∈ pCoreOf 2 B := by
    intro a ha x hx
    have hYle : Opp 3 X ≤ CFSG.GroupTheory.commMemSubgroup X (pCoreOf 2 B) hXWnorm a := by
      change Subgroup.closure {y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = 3 ^ k} ≤
        CFSG.GroupTheory.commMemSubgroup X (pCoreOf 2 B) hXWnorm a
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyX, k, hk⟩
      exact (CFSG.GroupTheory.mem_commMemSubgroup hXWnorm a y).mpr
        ⟨hyX, s16c6_commutatorElement_mem_of_pow3 hBA
          (CFSG.LieType.BorelTits.pCoreOf_le 2 B) hWnorm hXA hXB hXWnorm hAXB hBXW hB3
          hyX hk ha⟩
    have hXle : X ≤ CFSG.GroupTheory.commMemSubgroup X (pCoreOf 2 B) hXWnorm a := by
      intro x hx
      exact hYle (hXopp.symm ▸ hx)
    exact ((CFSG.GroupTheory.mem_commMemSubgroup hXWnorm a x).mp (hXle hx)).2
  have hAXW : ⁅A, X⁆ ≤ pCoreOf 2 B := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_le.mpr (fun x hx a ha => hcop3 a ha x hx)
  exact hAXW.trans (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hBA hAB)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
