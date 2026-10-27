module

public import CFSG.RankThree.PartTwo.Sec15.Item1423ProofCent
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1423

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec6 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem center_thetaQuot_eq_bot {K : Type*} [Group K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) :
    Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ := by
  have hmax := (solvable_prime_complement_core_characterization
    (H := K ⧸ aschbacherSolvableCore 3 K) Nat.prime_three).2.2.2.1
  have hle := hmax (Subgroup.center _) inferInstance
    (Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x))
    (fun h => h3 ((h.trans (Subgroup.card_subgroup_dvd_card _)).trans
      (Subgroup.card_quotient_dvd_card _)))
  rwa [theta_quotient_core_and_ranks.1, le_bot_iff] at hle

theorem suzukiModel_thetaQuot (hSz : KFacts.KPSz) {M X K : Subgroup G} (hM : SectionFourHyp M)
    (hXM : X ≤ M) (hX3 : ¬ 3 ∣ Nat.card X) (hK : K ∈ thetaComponentsIn X) :
    ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (K ⧸ aschbacherSolvableCore 3 K) 2 f := by
  have hKX : K ≤ X := le_of_mem_thetaComponentsIn hK
  have hK3 : ¬ 3 ∣ Nat.card K := fun h => hX3 (h.trans (Subgroup.card_dvd_of_le hKX))
  have hKq := isQuasisimple_of_mem_thetaComponentsIn1423 hK
  have hZ := center_thetaQuot_eq_bot hK3
  set Kb := K ⧸ aschbacherSolvableCore 3 K
  have hsimple : IsSimpleGroup Kb := by
    have := hKq.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hnab : ∃ a b : Kb, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hKq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have h3 : ¬ 3 ∣ Nat.card Kb := fun h => hK3 (h.trans (Subgroup.card_quotient_dvd_card _))
  have hKM : K ≤ M := hKX.trans hXM
  set e := (Subgroup.subgroupOfEquivOfLe hKM).symm
  set φ : Kb ≃* ↥(K.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf M) :=
    QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)
  have hs' : IsSimpleGroup (↥(K.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf M)) :=
    φ.symm.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := hM.kGroup (K.subgroupOf M) (aschbacherSolvableCore 3 ↥(K.subgroupOf M)) hs'
  exact hSz Kb hnab ⟨i, ⟨φ.trans f⟩⟩ h3

theorem le_thetaQuotCentralizer_of_item142 (h45 : Sec4.Item4_5)
    (hSz : KFacts.KPSz) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {hAab : IsMulCommutative A} {hcA : c ∈ A} (h142 : Item142 A (lB A) c L hAab hcA)
    {E X : Subgroup G} (hEA : E = ⁅E, A⁆) (hEL : E ≤ L)
    (hX : X ∈ invariantPiSubgroups ⊤ A (piCompl 3)) (hEX : E ≤ X) (hXA : X ⊔ A ≠ ⊤)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn X) : E ≤ thetaQuotCentralizer K := by
  have hD := h.toSec13Data
  set M := X ⊔ A with hMdef
  have hX3 : ¬ 3 ∣ Nat.card X := (isPiSubgroup_piCompl_iff Nat.prime_three X).mp hX.2.1
  have hXM : X ≤ M := le_sup_left
  have hAM : A ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.2
  have hXnorm : (X.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr hMN
  have hM4 : SectionFourHyp M := h.toTheoremFourHyp.sectionFourHyp hXA
  have hA45 : ∀ K' ∈ thetaComponentsIn M, A ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM4 hAM hD.isElemAbelian
      ⟨3, le_rfl, by rw [hD.card_eq]; norm_num⟩
  have hKM : K ∈ thetaComponentsIn M :=
    mem_thetaComponentsIn_of_isSubnormal hK hXM hXnorm.isSubnormal
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hA45 K hKM
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := by
    rw [hEA, Subgroup.commutator_le]
    intro e he a ha
    have heM : e⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer (M.inv_mem (hXM (hEX he)))
    have hK' := map_conj_mem_thetaComponentsIn1423 heM hKM
    have h1 : K.map (MulAut.conj a⁻¹).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAK (A.inv_mem ha))
    have h2 : (K.map (MulAut.conj e⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        K.map (MulAut.conj e⁻¹).toMonoidHom :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA45 _ hK' ha)
    have h3 := map_conj_map_conj_inv K e
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (MulAut.conj ⁅e, a⁆).toMonoidHom = ((MulAut.conj e).toMonoidHom.comp
        ((MulAut.conj a).toMonoidHom.comp (MulAut.conj e⁻¹).toMonoidHom)).comp
          (MulAut.conj a⁻¹).toMonoidHom := by
      ext y
      simp [commutatorElement_def, MulAut.conj_apply, mul_assoc]
    change K.map (MulAut.conj ⁅e, a⁆).toMonoidHom = K
    rw [hcomp, ← Subgroup.map_map, h1, ← Subgroup.map_map, ← Subgroup.map_map, h2, h3]
  obtain ⟨f, hf⟩ := suzukiModel_thetaQuot hSz hM4 hXM hX3 hK
  set ρ := (thetaQuotMulAut K).comp K.normalizerMonoidHom with hρ
  have hmemC : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)), ρ ⟨g, hg⟩ = 1 →
      g ∈ thetaQuotCentralizer K := fun g hg h1 => ⟨⟨g, hg⟩, h1, rfl⟩
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  have hEc : ∀ e ∈ E, e * c = c * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hEL he))
  by_cases hcK : c ∈ thetaQuotCentralizer K
  swap
  ·
    set A' := A.subgroupOf (Subgroup.normalizer (K : Set G)) with hA'
    have hρc : ρ ⟨c, hcN⟩ ≠ 1 := fun h1 => hcK (hmemC c hcN h1)
    have hA3 : ∀ x ∈ A', x ^ 3 = 1 := fun x hx =>
      Subtype.ext (by simpa using hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp hx))
    have hcard := KFacts.KP7.card_map_dvd_three hf ρ hA3
    have hle : Subgroup.zpowers (ρ ⟨c, hcN⟩) ≤ A'.map ρ :=
      Subgroup.zpowers_le.mpr ⟨⟨c, hcN⟩, Subgroup.mem_subgroupOf.mpr hcA, rfl⟩
    have heq : A'.map ρ = Subgroup.zpowers (ρ ⟨c, hcN⟩) := by
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      have h1 : Nat.card (Subgroup.zpowers (ρ ⟨c, hcN⟩)) ∣ Nat.card (A'.map ρ) :=
        Subgroup.card_dvd_of_le hle
      have h2 : Nat.card (Subgroup.zpowers (ρ ⟨c, hcN⟩)) ≠ 1 := by
        rw [Nat.card_zpowers]
        exact fun h => hρc (orderOf_eq_one_iff.mp h)
      rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h3 | h3
      · rw [h3] at h1
        exact absurd (Nat.dvd_one.mp h1) h2
      · rw [h3] at h1 ⊢
        rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h4 | h4
        · exact absurd h4 h2
        · exact h4.ge
    rw [hEA, Subgroup.commutator_le]
    intro e he a ha
    have heN : e ∈ Subgroup.normalizer (K : Set G) := hEK he
    have haN : a ∈ Subgroup.normalizer (K : Set G) := hAK ha
    have hea : ⁅e, a⁆ ∈ Subgroup.normalizer (K : Set G) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem heN haN) (inv_mem heN)) (inv_mem haN)
    refine hmemC _ hea ?_
    have hcomm : (⟨⁅e, a⁆, hea⟩ : Subgroup.normalizer (K : Set G)) =
        ⁅(⟨e, heN⟩ : Subgroup.normalizer (K : Set G)),
          (⟨a, haN⟩ : Subgroup.normalizer (K : Set G))⁆ :=
      rfl
    rw [hcomm, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have haz : ρ ⟨a, haN⟩ ∈ A'.map ρ := ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [heq] at haz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
    rw [← hk]
    have hec : Commute (ρ ⟨e, heN⟩) (ρ ⟨c, hcN⟩) := by
      have h1 : (⟨e, heN⟩ : Subgroup.normalizer (K : Set G)) * ⟨c, hcN⟩ =
          ⟨c, hcN⟩ * ⟨e, heN⟩ := Subtype.ext (hEc e he)
      change ρ ⟨e, heN⟩ * ρ ⟨c, hcN⟩ = ρ ⟨c, hcN⟩ * ρ ⟨e, heN⟩
      rw [← map_mul, ← map_mul, h1]
    exact (hec.zpow_right k).eq
  ·
    set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
    have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
    have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
    have hKle := le_inf_centralizer_sup_theta hcK hc3
    have hθN : K ≤ Subgroup.normalizer (θK : Set G) := le_normalizer_theta K
    set D := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) with hDdef
    have hKD : K ≤ D ⊔ θK := le_perfectResidual_sup hKp (inf_le_left.trans hθN) hKle
    have hDp : Group.IsPerfect D := isPerfect_inSubgroup_perfectResidual _
    have hDK : D ≤ K ⊓ Subgroup.centralizer ({c} : Set G) := Subgroup.map_subtype_le _
    have hD3 : ¬ 3 ∣ Nat.card D := fun h3 =>
      hX3 (h3.trans (Subgroup.card_dvd_of_le ((hDK.trans inf_le_left).trans
        (le_of_mem_thetaComponentsIn hK))))
    have hAC : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      hD.A_le_centralizer.trans Subgroup.le_normalizer
    have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
      (le_inf hAK hAC |>.trans Subgroup.inf_normalizer_le_normalizer_inf).trans
        (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
          _)
    have hDL := commutator_le_theta_of_item142 h h142 hDp (hDK.trans inf_le_right) hD3 hAD
    have hDE : ⁅D, E⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L :=
      (Subgroup.commutator_mono le_rfl hEL).trans hDL
    have hKEK : ⁅K, E⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hEK
    have hEθ : E ≤ Subgroup.normalizer (θK : Set G) := hEK.trans (normalizer_le_normalizer_theta K)
    have hDθ : D ≤ Subgroup.normalizer (θK : Set G) := (hDK.trans inf_le_left).trans hθN
    have hKE : ⁅K, E⁆ ≤ θK ⊔ ⁅D, E⁆ := by
      calc ⁅K, E⁆ ≤ ⁅D ⊔ θK, E⁆ := Subgroup.commutator_mono hKD le_rfl
        _ ≤ ⁅D, E⁆ ⊔ θK := commutator_sup_le_of_le_normalizer hDθ hEθ
        _ = θK ⊔ ⁅D, E⁆ := sup_comm _ _
    have hDEK : ⁅D, E⁆ ≤ K :=
      (Subgroup.commutator_mono (hDK.trans inf_le_left) le_rfl).trans hKEK
    have := (theta_solvable_and_not_dvd L).1
    have hsol : Group.IsSolvable (θK ⊔ ⁅D, E⁆ : Subgroup G) :=
      CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer (hDEK.trans hθN)
        (theta_solvable_and_not_dvd K).1
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDE)
          (Subgroup.inclusion_injective hDE))
    have hKEs : Group.IsSolvable (⁅K, E⁆ : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKE)
        (Subgroup.inclusion_injective hKE)
    have hKE3 : ¬ 3 ∣ Nat.card (⁅K, E⁆ : Subgroup G) := fun h3 =>
      hX3 (h3.trans (Subgroup.card_dvd_of_le (hKEK.trans (le_of_mem_thetaComponentsIn hK))))
    have hKEθ : ⁅K, E⁆ ≤ θK :=
      le_theta_of_normal hKEK (le_normalizer_commutator_left K E) hKEs hKE3
    exact (commutator_le_theta_iff hEK).mp hKEθ

end CFSG.RankThree.PartTwo.Sec15.Proof1423
