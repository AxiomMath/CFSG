module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenB8Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineNormal
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.GroupTheory.PerfectSylowCommutator
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Blueprint Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def barTwoEquivOTwoQuot (K : Subgroup G) :
    Bar2 K ≃* CFSG.Quasithin.oTwoQuot ↥K :=
  QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)

theorem nonempty_psl_oTwoQuot_of_isL2 {K : Subgroup G} {f : ℕ} (h : IsL2 (Bar2 K) f) :
    Nonempty (CFSG.Quasithin.oTwoQuot ↥K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
  have hf : 1 ≤ f := le_trans (by norm_num)
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 h)
  exact CFSG.Quasithin.H13.nonempty_equiv_psl_of_lieModel hf
    (CFSG.Blueprint.LieModel.of_mulEquiv (barTwoEquivOTwoQuot K) h)

theorem isRankOneField_oTwoQuot_of_isL2 {K : Subgroup G} {f : ℕ}
    (h : IsL2 (Bar2 K) f) : IsRankOneField (CFSG.Quasithin.oTwoQuot ↥K) f :=
  Or.inl (nonempty_psl_oTwoQuot_of_isL2 h)

theorem isRankOneField_oTwoQuot_of_isSz {K : Subgroup G} {f : ℕ}
    (h : IsSz (Bar2 K) f) : IsRankOneField (CFSG.Quasithin.oTwoQuot ↥K) f := by
  have h' : CFSG.Blueprint.LieModel (CFSG.Quasithin.oTwoQuot ↥K) .twistedB2 0 2 f :=
    CFSG.Blueprint.LieModel.of_mulEquiv (barTwoEquivOTwoQuot K) h
  obtain ⟨-, hSuz⟩ := CFSG.Blueprint.LieModel.suzukiModel h'
  obtain ⟨a, -, hf, he⟩ :=
    CFSG.ComponentClassification.GMS78.exists_mulEquiv_sz_of_suzukiModel hSuz
  exact Or.inr ⟨a, hf, he⟩

theorem IsRankOneField.isRankOneListed {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : IsRankOneField X f) : CFSG.Quasithin.IsRankOneListed X := by
  rcases h with e | ⟨a, hf', e⟩
  · exact Or.inl ⟨f, hf, e⟩
  · exact Or.inr (Or.inl ⟨a, e⟩)

theorem Ctx23L.borelOf_le_N {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) (hSzAut : KSzTwoAut) (hD2337 : D2337 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {m : ℕ} (hm2 : 2 ≤ m) (hshape : IsSz (Bar2 K) m ∨ ∃ e : ℕ, IsL2 (Bar2 K) (2 ^ e * m))
    {A₀ : Subgroup G} (hA₀ : A₀ ≤ K ⊓ Subgroup.normalizer (D.T : Set G))
    (hA₀card : Nat.card A₀ = 2 ^ m - 1) :
    CFSG.Quasithin.borelOf K D.T ≤ c.N := by
  rcases hshape with hSz | ⟨e, hL2⟩
  · exact (borelOf_le_normalizer_T_of_isSz hSzAut hK hKn hSz).trans
      (Ctx23L.normalizer_T_le_N c h1930 h4 h3 hPush)
  · exact hD2337 h1930 c h3 K hK hKn e m hm2 hL2 A₀ hA₀ hA₀card

private theorem hyp111At_of_shape_left {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {f : ℕ} (hKf : IsL2 (Bar2 K) f ∨ IsSz (Bar2 K) f) :
    CFSG.Quasithin.Hyp111At K c.L D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ D.M := CFSG.Open.IsSubnormal.le hK.1
  have hMleNK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hN3 : CFSG.Quasithin.borelOf c.L D.T ≤
      Subgroup.normalizer (D.T : Set G) ⊓ D.M :=
    Ctx23L.normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c
  have hN3M : CFSG.Quasithin.borelOf c.L D.T ≤ D.M :=
    fun x hx => (Subgroup.mem_inf.mp (hN3 hx)).2
  have hlisted : CFSG.Quasithin.IsRankOneListed (CFSG.Quasithin.oTwoQuot ↥K) := by
    rcases hKf with hL2 | hSz
    · exact IsRankOneField.isRankOneListed (le_trans (by norm_num)
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 hL2))
        (isRankOneField_oTwoQuot_of_isL2 hL2)
    · exact IsRankOneField.isRankOneListed (le_trans (by norm_num)
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_odd_three_le_of_isSz hSz).2)
        (isRankOneField_oTwoQuot_of_isSz hSz)
  refine ⟨inferInstance, D.sylowM.isPGroup, D.sylowM.le.trans hMleNK, ?_, hlisted, ?_, ?_⟩
  · exact CFSG.ABGLocalTools.isSylowOf_iff.mp
      (D.sylowM.inf_of_le_normalizer hKM hMleNK)
  · exact hN3M.trans hMleNK
  · refine CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le
      (D.standing.charTwo D.M D.maxLocal.1) (sup_le (sup_le hKM D.sylowM.le) hN3M) ?_
    exact (uc22p22e_pCoreOf_le_T D).trans
      ((le_sup_right : D.T ≤ K ⊔ D.T).trans le_sup_left)

private theorem hyp111At_of_shape_right {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D)
    {K : Subgroup G} (hDK : CFSG.Quasithin.borelOf K D.T ≤ c.N) :
    CFSG.Quasithin.Hyp111At c.L K D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : (c.L.subgroupOf c.N).Normal := Ctx23L.normal_L_N D Ch h4 h23 h208 h1930 c
  have hLleN : c.L ≤ c.N :=
    (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)
  have hTleN : D.T ≤ c.N :=
    (le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)
  have hNleNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleN).mp hLN
  have hL2n : IsL2 (Bar2 c.L) (CFSG.Open.pRank 2 D.Z) := (h23 h1930 c).2.1
  have hOTN : CFSG.Open.pCoreOf 2 c.N ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp
        (D.sylowG.of_le (Ctx23L.N_mem_calMOf_T c).2 le_top))
  refine ⟨inferInstance, D.sylowM.isPGroup, c.hL.1.1, ?_, ?_, hDK.trans hNleNL, ?_⟩
  · exact CFSG.ABGLocalTools.isSylowOf_iff.mp
      ((D.sylowG.of_le c.hL.1.1 le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl)
  · exact IsRankOneField.isRankOneListed (le_trans (by norm_num)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 hL2n))
      (isRankOneField_oTwoQuot_of_isL2 hL2n)
  · refine CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le
      (D.standing.charTwo c.N (Ctx23L.N_mem_calMOf_T c).1.1)
      (sup_le (sup_le hLleN hTleN) hDK) ?_
    exact hOTN.trans ((le_sup_right : D.T ≤ c.L ⊔ D.T).trans le_sup_left)

private theorem le_N_of_pCoreOf_ne_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {K : Subgroup G} (hne : CFSG.Open.pCoreOf 2 (K ⊔ c.L ⊔ D.T) ≠ ⊥) : K ≤ c.N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := CFSG.Open.pCoreOf 2 (K ⊔ c.L ⊔ D.T)
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ c.L ⊔ D.T)
  have hPne : P ≠ ⊥ := hne
  have hPLT : K ⊔ c.L ⊔ D.T ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ c.L ⊔ D.T)
  have hLT : c.L ⊔ D.T ≤ Subgroup.normalizer (P : Set G) :=
    (sup_le ((le_sup_right : c.L ≤ K ⊔ c.L).trans le_sup_left) le_sup_right).trans hPLT
  have hNle : Subgroup.normalizer (P : Set G) ≤ c.N := by
    have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hPne, hP2, rfl⟩
    obtain ⟨M', hM'max, hle⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le hloc
    have hM'mem : M' ∈ calMOf (c.L ⊔ D.T) := ⟨hM'max, hLT.trans hle⟩
    have hM' : M' = c.N := by
      rw [c.hN] at hM'mem
      simpa using hM'mem
    exact hle.trans (le_of_eq hM')
  exact (((le_sup_left : K ≤ K ⊔ c.L).trans le_sup_left).trans hPLT).trans hNle

private theorem false_of_commutator_two_pow {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {f : ℕ} (hKf : IsL2 (Bar2 K) f ∨ IsSz (Bar2 K) f) {a : G} (haK : a ∈ K) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r)
    (hKN : K ≤ c.N) (hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G))
    (hLN : (c.L.subgroupOf c.N).Normal) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hthin : F08.Thin8 K := thin8_of_isL2_or_isSz hKf
  have hrdvdK : r ∣ Nat.card K := by
    have h := Subgroup.orderOf_dvd_natCard K haK
    rwa [har] at h
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨Pr, hPrK, hPrr, g, hg, x, hx, hcomm⟩ :=
    CFSG.GroupTheory.exists_commutator_ne_one_of_perfect hK.2.1 hrdvdK
  have hgK : g ∈ K := hg.1
  have hgN : g ∈ c.N := hKN hgK
  have hgNZ : g ∈ Subgroup.normalizer (Pr : Set G) := hg.2
  have hxK : x ∈ K := hPrK hx
  have hxN : x ∈ c.N := hKN hxK
  have hgZ : g ∈ Subgroup.centralizer (D.Z : Set G) := hKCZ hgK
  have hxZ : x ∈ Subgroup.centralizer (D.Z : Set G) := hKCZ hxK
  have hcommK : g * x * g⁻¹ * x⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hgK hxK) (K.inv_mem hgK)) (K.inv_mem hxK)
  obtain ⟨i, hi⟩ := Ctx23L.exists_orderOf_commutator_eq_two_pow D Ch c h1930 h4 h23 h847
    hLN hK hthin hgN hxN hgZ hxZ hcommK
  have hcommPr : g * x * g⁻¹ * x⁻¹ ∈ Pr :=
    Pr.mul_mem ((Subgroup.mem_normalizer_iff.mp hgNZ x).1 hx) (Pr.inv_mem hx)
  obtain ⟨k, hk⟩ := hPrr.exists_card_eq
  have hdvdPow : 2 ^ i ∣ r ^ k := by
    rw [← hk]
    exact hi ▸ Subgroup.orderOf_dvd_natCard Pr hcommPr
  have h2i1 : 2 ^ i = 1 := by
    have hcop : Nat.Coprime (2 ^ i) (r ^ k) :=
      Nat.Coprime.pow i k (Nat.coprime_two_left.mpr (hr.odd_of_ne_two hr2))
    exact hcop.eq_one_of_dvd hdvdPow
  have hcomm1 : g * x * g⁻¹ * x⁻¹ = 1 := by
    rw [← orderOf_eq_one_iff, hi, h2i1]
  exact hcomm hcomm1

private theorem pCoreOf_eq_bot_of_shape {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D)
    (h847 : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {f : ℕ} (hKf : IsL2 (Bar2 K) f ∨ IsSz (Bar2 K) f)
    {a : G} (haK : a ∈ K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r) :
    CFSG.Open.pCoreOf 2 (K ⊔ c.L ⊔ D.T) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hKN : K ≤ c.N := le_N_of_pCoreOf_ne_bot c hne
  have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
  have hLN : (c.L.subgroupOf c.N).Normal := Ctx23L.normal_L_N D Ch h4 h23 h208 h1930 c
  exact false_of_commutator_two_pow c h1930 h4 h23 h847 hK hKf haK hr hr2 har hKN hKCZ hLN

theorem Ctx23L.wbn_hyp_of_D {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D)
    (h847 : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {f : ℕ} (hKf : IsL2 (Bar2 K) f ∨ IsSz (Bar2 K) f)
    {a : G} (haK : a ∈ K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r)
    (hDK : CFSG.Quasithin.borelOf K D.T ≤ c.N) :
    CFSG.Quasithin.Hyp111 K c.L D.T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hyp111At_of_shape_left c h1930 h4 h23 hK hKn hKf,
    hyp111At_of_shape_right c h1930 h4 h23 h208 hDK,
    pCoreOf_eq_bot_of_shape c h1930 h4 h23 h208 h847 hK hKf haK hr hr2 har⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
