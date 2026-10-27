module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofD
public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofCQ
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

@[expose] def KS156J2Norm : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ z : Γ, z ≠ 1 →
      (∃ S : Sylow 3 Γ, z ∈ (S : Subgroup Γ) ∧
        (S : Subgroup Γ) ≤ Subgroup.centralizer ({z} : Set Γ)) →
      ∀ R : Subgroup (MulAut Γ), IsPGroup 2 R →
        (Subgroup.centralizer ({z} : Set Γ)).map (MulAut.conj : Γ →* MulAut Γ) ≤
          Subgroup.normalizer (R : Set (MulAut Γ)) →
        R = ⊥

@[expose] def Step156CQFaith (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c₀, d} → F ≠ Subgroup.zpowers d →
        ∃ (f : G) (Lf : Subgroup G), F = Subgroup.zpowers f ∧ Lf ∈ lA A f ∧
          Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) ⊓
            Sec4.thetaQuotCentralizer Lf = ⊥

@[expose] noncomputable def Step156CQFaithR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQFaith A (lB A)

namespace Proof156

theorem thetaQuotMulAut_eq_conj {L : Subgroup G} {y : G} (hy : y ∈ L) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨y, Subgroup.le_normalizer hy⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨y, hy⟩) := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) q
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  change ((L.normalizerMonoidHom ⟨y, Subgroup.le_normalizer hy⟩ x : ↥L) :
    ↥L ⧸ aschbacherSolvableCore 3 ↥L) = _
  congr 1

theorem exists_cover_eq_centralizer_of_six
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A)
    {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A))
    (h6 : Sec4.IsTripleCover (↥X ⧸ CFSG.pCore 2 ↥X) (alternatingGroup (Fin 6)))
    (hc : c ∈ Late.sectionCentralizer A X (CFSG.Open.pCoreOf 2 X)) :
    ∃ (D : Subgroup G) (z : ↥L ⧸ aschbacherSolvableCore 3 ↥L), D ≤ X ⊓ L ∧ z ≠ 1 ∧
      (∃ S' : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L), z ∈ (S' : Subgroup _) ∧
        (S' : Subgroup _) ≤
          Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) ∧
      (D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
        Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  have hq2 : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
  have htype : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥X ⧸ CFSG.pCore 2 ↥X) (alternatingGroup (Fin 6)) := Or.inr h6
  obtain ⟨d, hdA, hd1, hd3c, hcent⟩ := exists_d_of_mem_sectionCentralizer h hJ h142 hX htype hc
  have hθO := inSubgroup_theta_eq_pCoreOf_of_type hq2 htype
  have hXq := isQuasisimple_theta_of_type hq2 htype
  have htype' := type_theta_of_type hq2 htype
  have hX3 := three_dvd_card_quot_center_of_type hXq htype'
  rw [← hθO] at hcent hc
  have hcC := mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX hc
  have hdsc : d ∈ Late.sectionCentralizer A X (inSubgroup (aschbacherSolvableCore 3) X) := by
    rw [hcent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hdC := mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX hdsc
  have hAnc := not_le_thetaQuotCentralizer_of_subset_closure hA hS13.mem_A hdA hcent.le
  have hcov := le_inf_sup_theta_of_item142 h hJ h142 hAX hX.2.2.1 hXq hX3 hcC hAnc
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := hd3c
  have hdXL : d ∈ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAX hS13.le_normalizer hdA
  have hW := map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  have hW' := map_inf_centralizer_eq_top inf_le_left hdXL hd3 hdC hW
  obtain ⟨D', hD'W, hD'p, hD'top⟩ := exists_isPerfect_cover hXq.1 hW'
  have hD'X : D' ≤ X := hD'W.trans (inf_le_left.trans inf_le_left)
  have hD'L : D' ≤ L := hD'W.trans (inf_le_left.trans inf_le_right)
  have hD'd : D' ≤ Subgroup.centralizer ({d} : Set G) := hD'W.trans inf_le_right
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set z : ↥L ⧸ θ := ρ ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine ⟨S3.mapSurjective (QuotientGroup.mk'_surjective θ), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  have hD'z : (D'.subgroupOf L).map ρ ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyd : (y : G) * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hD'd (Subgroup.mem_subgroupOf.mp hy))
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyd
  have h6' : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) := by
    rcases htype' with he | h6'
    · exfalso
      obtain ⟨e⟩ := he
      have h1 := card_of_isTripleCover h6
      rw [card_alternatingGroup_six] at h1
      have h2 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) =
          Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
          (theta_eq_pCore_two_of_type hq2 htype)).toEquiv
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five, h1] at h2
      norm_num at h2
    · exact h6'
  have hdvd := card_dvd_card_map_of_cover hXq (isPGroup_center_of_type hXq (Or.inr h6'))
    (isPGroup_theta_of_j2 h hJ) hD'X hD'L hD'top
  rw [card_of_isTripleCover h6', card_alternatingGroup_six] at hdvd
  obtain ⟨hZc, hZ3, hZn, ⟨eA⟩⟩ :=
    KFacts.KS14.j2_centralizer_quotient Sec4.Sporadic.rank3II_4_15 hJ hz1 hzc
  have hC1080 : Nat.card (Subgroup.centralizer ({z} : Set (↥L ⧸ θ))) = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set (↥L ⧸ θ))))
    rw [Nat.card_congr eA.toEquiv, KFacts.KS14.card_alternatingGroup_six, hZ3] at h
    exact h
  have hFle : Nat.card ((D'.subgroupOf L).map ρ) ≤ 1080 :=
    hC1080 ▸ Subgroup.card_le_of_le hD'z
  have hpos : 0 < Nat.card ((D'.subgroupOf L).map ρ) := Nat.card_pos
  have hF1080 : Nat.card ((D'.subgroupOf L).map ρ) = 1080 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hFle hpos ⊢
    have hk1 : k = 1 := by
      rcases k with _ | _ | k
      · omega
      · rfl
      · omega
    rw [hk1, mul_one]
  refine ⟨D', z, le_inf hD'X hD'L, hz1, hzc, ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hD'z (by rw [hC1080, hF1080])

end Proof156

theorem step156CQPoint_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h142 : Item142AllS14)
    (hK : KS156J2Norm) (hF : Step156CQFaith A (lB A)) : Step156CQPoint A (lB A) := by
  intro Y hY htype c₀ L₀ d X₁ D hΩ hLN h6 M hM F hFΩ hFcd hFd
  obtain ⟨f, Lf, hFf, hLf, hJf, hfaith⟩ := hF Y hY htype c₀ L₀ d X₁ D hΩ hLN h6 M hM F hFΩ hFcd hFd
  have hfΩ : Subgroup.zpowers f ∈ omegaA A := hFf ▸ hFΩ
  have hf : Sec14Std G A f Lf := { h with zpowers_mem_omegaA := hfΩ, mem_lA := hLf }
  have hX4 : X₁ ∈ scriptY4 A (lB A) := D.mem_x.1
  have hfF : f ∈ F := hFf ▸ Subgroup.mem_zpowers f
  have hfsc : f ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact hFcd hfF
  obtain ⟨D', z, hD'XL, hz1, hzc, hD'img⟩ :=
    exists_cover_eq_centralizer_of_six hf hJf (h142 G A f Lf hf) hX4 h6 hfsc
  have hCF : Subgroup.centralizer (F : Set G) = Subgroup.centralizer ({f} : Set G) := by
    rw [hFf]
    exact KFacts.KS14.centralizer_zpowers_eq f
  have hCN : Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (Lf : Set G) :=
    hCF ▸ centralizer_le_normalizer_of_j2 hf hJf
  set U := CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) with hU
  have hUN : U ≤ Subgroup.normalizer (Lf : Set G) := inf_le_right.trans hCN
  set φ : ↥(Subgroup.normalizer (Lf : Set G)) →* MulAut (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) :=
    (Sec4.thetaQuotMulAut ↥Lf).comp Lf.normalizerMonoidHom with hφ
  set R := (U.subgroupOf (Subgroup.normalizer (Lf : Set G))).map φ with hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_left
  have hR2 : IsPGroup 2 R :=
    (hU2.comap_of_injective (Subgroup.normalizer (Lf : Set G)).subtype
      (Subgroup.normalizer (Lf : Set G)).subtype_injective).map φ
  have hXM : X₁ ≤ M := fun x hx => hM.2 (Subgroup.mem_sup_left (D.le_x hx))
  have hMQ : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hRN : (Subgroup.centralizer ({z} : Set (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf))).map
      (MulAut.conj : (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) →* MulAut _) ≤
      Subgroup.normalizer (R : Set (MulAut (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf))) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun a ha r hr => ?_
    obtain ⟨g, hg, rfl⟩ := ha
    rw [← hD'img] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    obtain ⟨q, hq, rfl⟩ := hr
    have hyL : (y : G) ∈ Lf := y.2
    have hyD : (y : G) ∈ D' := Subgroup.mem_subgroupOf.mp hy
    have hyX : (y : G) ∈ X₁ := (hD'XL hyD).1
    have hyN : (y : G) ∈ Subgroup.normalizer (Lf : Set G) := Subgroup.le_normalizer hyL
    have hφy : φ ⟨y, hyN⟩ = MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lf) y) :=
      thetaQuotMulAut_eq_conj hyL
    have hqU : (q : G) ∈ U := Subgroup.mem_subgroupOf.mp hq
    have hyqU : (y : G) * q * (y : G)⁻¹ ∈ U := by
      have hyC : (y : G) ∈ Subgroup.centralizer (F : Set G) := by
        rw [hCF]
        exact (Sec6.le_centralizer_of_mem_thetaComponentsAt hLf.1) hyL
      refine Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hMQ (hXM hyX)) _).mp (Subgroup.mem_inf.mp hqU).1, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyC (Subgroup.mem_inf.mp hqU).2)
        (Subgroup.inv_mem _ hyC)
    refine ⟨⟨(y : G) * q * (y : G)⁻¹, hUN hyqU⟩, Subgroup.mem_subgroupOf.mpr hyqU, ?_⟩
    have he : (⟨(y : G) * q * (y : G)⁻¹, hUN hyqU⟩ : ↥(Subgroup.normalizer (Lf : Set G))) =
        ⟨y, hyN⟩ * q * ⟨y, hyN⟩⁻¹ := Subtype.ext rfl
    rw [he, map_mul, map_mul, map_inv, hφy]
  have hRbot : R = ⊥ := hK _ hJf z hz1 hzc R hR2 hRN
  have hUC : U ≤ Sec4.thetaQuotCentralizer Lf := by
    intro u hu
    have h1 : φ ⟨u, hUN hu⟩ ∈ R := ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at h1
    exact ⟨⟨u, hUN hu⟩, MonoidHom.mem_ker.mpr h1, rfl⟩
  rw [← inf_eq_left.mpr hUC]
  exact hfaith

theorem step156CQR_of_faith
    (h142 : Item142AllS14) (hA6 : Step156CQA6R)
    (hΩ : Step156CQOmegaR) (hK : KS156J2Norm) (hF : Step156CQFaithR) : Step156CQR :=
  step156CQR_of h142 hA6 hΩ
    (fun G _ _ A c L hR => step156CQPoint_of hR.toSec14Std h142 hK (hF G A c L hR))

end CFSG.RankThree.PartTwo.Sec15
