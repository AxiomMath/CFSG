module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEighteenLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyOneC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Main
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec3
public import CFSG.GH74.Uniqueness.Section6AGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieKMax
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorData
public import CFSG.GroupTheory.SylowCommutatorJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

theorem pow_eq_one_of_isZModSq {A : Subgroup G} {n : ℕ} (hA : IsZModSq A n) :
    ∀ a ∈ A, a ^ (2 ^ n - 1) = 1 := by
  obtain ⟨e⟩ := hA
  intro a ha
  have hx : ∀ {m : ℕ} (x : Multiplicative (ZMod m × ZMod m)), x ^ m = 1 := fun x => by
    rw [← toAdd_eq_zero, toAdd_pow]
    ext <;> simp
  have hx := hx (e ⟨a, ha⟩)
  have h1 : (⟨a, ha⟩ : A) ^ (2 ^ n - 1) = 1 := e.injective (by rw [map_pow, hx, map_one])
  simpa using congrArg Subtype.val h1

open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp in
theorem exists_sylow_J_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
    {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) (h5 : P19_16_5 D Dsub)
    (h19 : R19_19At D V₀ V p L A t B r Y N Dsub H S h) (hB : K_L2_oddAbelianBorel)
    {d : ℕ} {K J : Fin d → Subgroup G} (hfam : IsDynkinComponentFamily D Dsub d K J)
    (k : Fin d) (hAJ : A ≤ normalizer (J k : Set G)) (hJp : ⁅J k, J k⁆ = J k)
    (hJq : CFSG.Open.IsQuasisimple (Bar2 (J k))) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P (J k) ∧ A ≤ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (J k)
  by_cases hc : ⁅J k, A⁆ ≤ pCoreOf 2 (J k)
  · refine ⟨P₀, hP₀, CFSG.AGLEmbedding.le_normalizer_sylowTwo_of_commutator_le hP₀.le
      (hc.trans ?_)⟩
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.le_of_normal_isPGroup_of_isSylowOf hP₀
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have heq : ⁅J k, A⁆ = J k := CFSG.Quasithin.SBc13.commutator_eq_of_not_le_pCore hJp
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJq) hAJ hc
  have hLcal : L ∈ calC D.M := S17.calLp_subset_calC D p h.ctx.hyp.hL
  have hJM : J k ≤ D.M := by
    rw [hfam.2.2.2.2 k]
    exact (S17.oUpperTwo_le _).trans ((hfam.1 k).2.1.trans inf_le_right)
  have hJI : J k ≤ IOf D p L := by
    rw [← heq]
    exact (commutator_mono le_rfl h.ctx.hA).trans
      (le_normalizer_iff_commutator_le_right.mp (hJM.trans (le_normalizer_IOf D hLcal)))
  rcases h19.2 h5 d K J hfam k hJI with ⟨-, -, -, hL2, -⟩ | ⟨-, he | he, -⟩
  · exact hB G (J k) A (S17.nOf L) hL2 hAJ (isMulCommutative_of_isZModSq h.ctx.hAcard)
      (odd_card_of_ctx19_10 h.ctx) (pow_eq_one_of_isZModSq h.ctx.hAcard)
  all_goals exact absurd hJq (TensorAux.not_isQuasisimple_of_comm
    fun x y => he.some.injective (by rw [map_mul, map_mul, mul_comm]))

theorem gap19_21_borel_of_K (D : Data G) (hL : K_19_21_levi) (hB : K_L2_oddAbelianBorel) :
    Gap19_21_borel D := by
  intro V₀ V p L A t B r Y N Dsub H S h h17 h5 h19 d K J i hfam _hJi h191
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hL2i, -⟩ := h191
  obtain ⟨hd2, hKJ, hodd⟩ := hL G D.M Dsub h.hD.1.2.2 h5.1 h5.2 h.hO2 d K J hfam i (S17.nOf L)
    (three_le_nOf_of_setting1910 h.ctx.h1910) hL2i
  set O := pCoreOf 2 (Dsub ⊓ D.M) with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOn : Dsub ⊓ D.M ≤ normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hAinf : A ≤ normalizer ((Dsub ⊓ D.M : Subgroup G) : Set G) :=
    le_normalizer_inf_of_ctx D h.ctx h17
  have hAO : A ≤ normalizer (O : Set G) :=
    hAinf.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx
  have hAK : ∀ k, A ≤ normalizer (K k : Set G) := fun k a ha =>
    hodd a (hAinf ha) (Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A ha)) k
  have hKJn : ∀ k, normalizer (K k : Set G) ≤ normalizer (J k : Set G) := fun k => by
    rw [hfam.2.2.2.2 k, S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
    exact CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure _
  have hKn : ∀ k, Dsub ⊓ D.M ≤ normalizer (K k : Set G) := fun k =>
    (normal_subgroupOf_iff_le_normalizer (hfam.1 k).2.1).mp (hfam.1 k).2.2.1
  have hJK : ∀ k, J k ≤ K k := fun k => by
    rw [hfam.2.2.2.2 k]
    exact S17.oUpperTwo_le _
  have hOP : ∀ k (P : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 2 P (K k) → O ≤ P := fun k P hP =>
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.le_of_normal_isPGroup_of_isSylowOf hP
      (hfam.1 k).1 ((hfam.1 k).2.1.trans hOn) hO2
  have hPk : ∀ k, ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P (K k) ∧
      A ≤ normalizer (P : Set G) := by
    intro k
    obtain ⟨Q, hQ, hAQ⟩ := exists_sylow_J_of_ctx D h h5 h19 hB hfam k
      ((hAK k).trans (hKJn k)) (hKJ k).1 (hKJ k).2.1
    refine ⟨Q ⊔ O, ?_, (le_inf hAQ hAO).trans (inf_normalizer_le_normalizer_sup _ _)⟩
    have hQO : IsPGroup 2 ↥(Q ⊔ O) := hQ.isPGroup.to_sup_of_normal_right' hO2
      (hQ.le.trans ((hJK k).trans ((hfam.1 k).2.1.trans hOn)))
    have hRK : Q ⊔ O ≤ normalizer (J k : Set G) :=
      sup_le (hQ.le.trans le_normalizer) ((hfam.1 k).1.trans (le_normalizer.trans (hKJn k)))
    have := CFSG.GH74.Uniqueness.Section6A.isSylowOf_sup_of_le Nat.prime_two hRK hQO hQ
      le_sup_left
    rwa [← sup_assoc, sup_eq_left.mpr hQ.le, ← (hKJ k).2.2] at this
  have hOopp : O ≤ Opp 2 (Dsub ⊓ D.M) := CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two hO2
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hK0 : (⨆ k, K k) = Opp 2 (Dsub ⊓ D.M) := by
    rw [hfam.2.2.1, sup_eq_left.mpr hOopp]
  suffices hsyl : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P (⨆ k, K k) ∧
      A ≤ normalizer (P : Set G) by
    obtain ⟨P, hP, hAP⟩ := hsyl
    rw [hK0] at hP
    exact ⟨P, CFSG.GroupTheory.isSylowOf_of_isSylowOf_pElementSubgroup hP, hAP⟩
  have hd : d = 1 ∨ d = 2 := by
    have := i.pos
    omega
  rcases hd with rfl | rfl
  · obtain ⟨P, hP, hAP⟩ := hPk 0
    refine ⟨P, ?_, hAP⟩
    rwa [iSup_unique K]
  · obtain ⟨P₀, hP₀, hAP₀⟩ := hPk 0
    obtain ⟨P₁, hP₁, hAP₁⟩ := hPk 1
    refine ⟨P₀ ⊔ P₁, ?_, (le_inf hAP₀ hAP₁).trans (inf_normalizer_le_normalizer_sup _ _)⟩
    have hsup : (⨆ k, K k) = K 0 ⊔ K 1 := by
      apply le_antisymm
      · exact iSup_le fun k => by fin_cases k <;> simp
      · exact sup_le (le_iSup K 0) (le_iSup K 1)
    rw [hsup]
    have hc01 : ⁅K 0, K 1⁆ ≤ O := hfam.2.1 0 1 (by decide)
    have hcore : pCoreOf 2 (K 0) ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (hfam.1 0).2.1)
      ((hKn 0).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    have hOsyl := CFSG.GroupTheory.isSylowOf_inf_of_commutator_le hO2 (hfam.1 0).1 (hfam.1 1).1
      hc01 hcore
    have hinf : P₀ ⊓ P₁ = O :=
      hOsyl.eq_of_le (le_inf (hOP 0 P₀ hP₀) (hOP 1 P₁ hP₁)) (inf_le_inf hP₀.le hP₁.le)
        (hP₀.isPGroup.to_inf_left)
    refine CFSG.ComponentClassification.GMS78.isSylowOf_sup_of_inf ((hfam.1 0).2.1.trans (hKn 1))
      hP₀ hP₁ ?_ (hinf ▸ hOsyl)
    rw [le_normalizer_iff_commutator_le_right]
    exact (commutator_mono hP₀.le hP₁.le).trans (hc01.trans (hOP 1 P₁ hP₁))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
