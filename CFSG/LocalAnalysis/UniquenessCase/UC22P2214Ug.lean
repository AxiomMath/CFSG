module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rx
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_borel_of_elt_faith (D : Data G)
    (Ch : Choice2011 G) (hV : S22_V D Ch) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKV : ¬ K ≤ centralizer (c.V : Set G)) {n : ℕ}
    (hshape : Shape2214 (↥(mbarImage D.M c.V K) ⧸ center ↥(mbarImage D.M c.V K)) n)
    (hfix : ∀ K' ∈ conjSetOf D.M K, c.B0 ≤ normalizer (K' : Set G))
    (hfaith : ∀ b ∈ c.B0, b ≠ 1 →
      ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', b * k * b⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G))
    {a : G} (ha : a ∈ c.B0)
    {r : ℕ} (hr : r.Prime) (hao : orderOf a = r) (hrn : n < r) (hr5 : 5 ≤ r) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y),
      Nonempty (Y ≃* (↥(mbarImage D.M c.V K) ⧸ center ↥(mbarImage D.M c.V K))) ∧
      ∃ S : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧
        r ∣ Nat.card ↥(normalizer (S : Set Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    exact hr.ne_one hao.symm
  obtain ⟨K', hK', k, hk, hkV⟩ := hfaith a ha ha1
  have hK'C := uc22p2214_calC_of_mem_conjSetOf hK hK'
  have hK'V := uc22p2214_not_le_centralizer_of_mem_conjSetOf c.hVM hKV hK'
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have hcomp := uc22br4_isComponentOf_mbarImage D.M c.V K' c.hVM hO2 hK'C hK'V
  have hfixK' := hfix K' hK'
  obtain ⟨g, hg, rfl⟩ := hK'
  have hKb' : mbarImage D.M c.V (K.map (MulAut.conj g).toMonoidHom) =
      (mbarImage D.M c.V K).map
        (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : MBar D.M c.V)).toMonoidHom :=
    uc22br4_mbarImage_map_conj D.M c.V K ⟨g, hg⟩
  let e1 : ↥(mbarImage D.M c.V K) ≃*
      ↥(mbarImage D.M c.V (K.map (MulAut.conj g).toMonoidHom)) :=
    ((mbarImage D.M c.V K).equivMapOfInjective _ (MulAut.conj _).injective).trans
      (MulEquiv.subgroupCongr hKb'.symm)
  obtain ⟨e2⟩ := uc22p2214_quotCenter_congr e1
  have hshape' := uc22p2214_shape_of_mulEquiv e2 hshape
  obtain ⟨-, hB0c, -, -, -, -, -, -, -, hperm, -⟩ := c.hB0
  have hTp : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hYs := uc22p2214_isSolvable_sup (uc22p2214_odd_card_B0 D c) hB0c hTp hperm
  have hYbs : Group.IsSolvable ↥(mbarImage D.M c.V (c.B0 ⊔ D.T)) :=
    uc22p2214_isSolvable_mbarImage hYs (sup_le c.hBM hTM)
  have hTbS : CFSG.ABGLocalTools.IsSylowOf 2 (mbarImage D.M c.V D.T) ⊤ :=
    uc22p22r_isSylowOf_mbarImage D.sylowM
  have hS₀ := uc22p2214_isSylowOf_inf hTbS hcomp.2.1
  have hS₀Y : mbarImage D.M c.V D.T ⊓ mbarImage D.M c.V (K.map (MulAut.conj g).toMonoidHom) ≤
      mbarImage D.M c.V (c.B0 ⊔ D.T) :=
    inf_le_left.trans (uc22p2214_mbarImage_mono le_sup_right)
  have haM : a ∈ D.M := c.hBM ha
  have haY : (QuotientGroup.mk ⟨a, haM⟩ : MBar D.M c.V) ∈ mbarImage D.M c.V (c.B0 ⊔ D.T) :=
    uc22p2214_mbarImage_mono le_sup_left (uc22p2214_mem_mbarImage haM ha)
  have haN := uc22p2214_mk_mem_normalizer (V := c.V) haM (hfixK' ha)
  have hkM : k ∈ D.M := uc22p22a_le_of_isSubnormal hK'C.1 hk
  have hkb := uc22p2214_mem_mbarImage (V := c.V) hkM hk
  have hnt : (QuotientGroup.mk ⟨a, haM⟩ : MBar D.M c.V) * QuotientGroup.mk ⟨k, hkM⟩ *
      (QuotientGroup.mk ⟨a, haM⟩)⁻¹ * (QuotientGroup.mk ⟨k, hkM⟩)⁻¹ ≠ 1 := by
    intro h1
    apply hkV
    have h2 : (QuotientGroup.mk (⟨a, haM⟩ * ⟨k, hkM⟩ * ⟨a, haM⟩⁻¹ * ⟨k, hkM⟩⁻¹ : ↥D.M) :
        MBar D.M c.V) = 1 := by
      rw [← h1]
      rfl
    exact (uc22br_gt_mk_eq_one_iff c.hVM _).1 h2
  have habr : (QuotientGroup.mk ⟨a, haM⟩ : MBar D.M c.V) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h3 : (⟨a, haM⟩ : ↥D.M) ^ r = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hao, pow_orderOf_eq_one]; rfl)
    rw [h3, QuotientGroup.mk_one]
  have hab1 : (QuotientGroup.mk ⟨a, haM⟩ : MBar D.M c.V) ≠ 1 := by
    intro h4
    apply hnt
    rw [h4]
    group
  have habo := orderOf_eq_prime habr hab1
  obtain ⟨S, hS, x, hxN, hxo⟩ := uc22p2214_cartan hcomp.2.2 hr
    (fun α hα => uc22p2214_shape_inn hshape' hr hrn hr5 hα)
    (fun S hS Y hSY hY => uc22p2214_shape_solv hshape' hS hSY hY) hS₀ hS₀Y hYbs haY haN habo
    ⟨_, hkb, hnt⟩
  refine ⟨_, inferInstance, inferInstance, ⟨e2.symm⟩, S, hS, ?_⟩
  have h5 : orderOf (⟨x, hxN⟩ : ↥(normalizer (S : Set _))) = r := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  exact h5 ▸ orderOf_dvd_natCard _

theorem uc22p2214_main_faith (D : Data G) (Ch : Choice2011 G)
    (h17 : S21_17 D Ch) (hn : SpU3NotList D) (hV : S22_V D Ch)
    (h846 : F08.R846 D) (h1930 : H1930 D) (c : Ctx22b D Ch) (hn3 : 3 ≤ c.n) (hm6 : c.n ≠ 6)
    {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hcl : (IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧
        (conjSetOf D.M K).ncard = 2))
    (hfaith : ∀ b ∈ c.B0, b ≠ 1 →
      ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', b * k * b⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G)) :
    c.n ≤ n := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hKV, hq, hshape, hfix, -⟩ := uc22p2214_case_data D Ch h17 hn hV h1930 c hKC hcl
  have hn1 : 1 ≤ n := uc22p2214_one_le_of_shape hshape
  obtain ⟨a, ha, r, hao, hpp, hmr⟩ :=
    uc22p22i_exists_prim_prime_elt (by omega : 2 ≤ c.n) hm6 c.hpi
  have hr : r.Prime := hpp.1
  have hr5 : 5 ≤ r := by
    by_contra h5
    have h4 : r = 4 := by omega
    rw [h4] at hr
    exact absurd hr (by decide)
  have hrn : n < r := by omega
  have hprim : ¬ r ∣ 2 ^ n - 1 := hpp.2.2 n (by omega) hlt
  obtain ⟨Y, _, _, ⟨e⟩, S, hS, hrN⟩ := uc22p2214_borel_of_elt_faith D Ch hV h1930 c hKC
    hKV hshape hfix hfaith ha hr hao hrn hr5
  have hr2 : r ≠ 2 := by omega
  rcases hcl with ⟨hsp, -⟩ | ⟨hsu, -⟩ | ⟨hL | hSz, -⟩
  · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
    obtain ⟨e'⟩ := uc22p2214_quotCenter_of_simple hq
    exact hprim (uc22p2214_borel_prime_Sp4
      (CFSG.Blueprint.LieModel.of_mulEquiv (e'.trans e.symm) hsp) hS hr hr2 hrN)
  · rcases uc22p2214_borel_prime_U3 (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hsu.2) hS hr hr2
      hrN with h1 | h1
    · exact hprim h1
    · exact uc22p2214_false_of_sp D Ch h1930 c hr
        (h846 K hKC n (uc22p22a_shape_su3 D c hKC hsu) r hr (by omega) h1) ha hao
  · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    obtain ⟨e'⟩ := uc22p2214_quotCenter_of_simple hq
    exact hprim (uc22p2214_borel_prime_L2
      (CFSG.Blueprint.LieModel.of_mulEquiv (e'.trans e.symm) hL) hS hr hr2 hrN)
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    obtain ⟨e'⟩ := uc22p2214_quotCenter_of_simple hq
    exact hprim (uc22p2214_borel_prime_Sz
      (CFSG.Blueprint.LieModel.of_mulEquiv (e'.trans e.symm) hSz) hS hr hr2 hrN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
