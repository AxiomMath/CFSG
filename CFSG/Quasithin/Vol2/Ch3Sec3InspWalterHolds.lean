module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalter
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterJ1
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterEven
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterOdd
public import CFSG.Walter.FinalNative
public import CFSG.Walter.W67.Section6.Lemma65
public import CFSG.Walter.Ree.Thompson2.BaseGrp
public import CFSG.LocalAnalysis.SectionRank.SmallRee
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.Quasithin.H13.S3320

open CFSG.QuasithinUnique CFSG.Walter CFSG.Open
open scoped MatrixGroups

theorem walter_split
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) (hP : IsMulCommutative (P : Subgroup G)) :
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel G .twistedG2 3 f) ∨
    Nonempty (G ≃* walterJ1) := by
  have hR := Ree.reeIdentNative Ree.T2.baseExists
  have hT := W67.theorem_of_reeIdentNative (W67.prop_6_6_of W67.prop_4_1 W67.prop_5_6
    (W67.lemma_6_2_of W67.prop_4_1 W67.prop_5_6) W67.lemma_6_5) hR
  rcases walter_structure (jrStrongHyp_of_open hT j1RecogHyp jtThreeHyp) G hnonab P hP with
    hL2 | hR' | hJ
  · rcases hL2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨hR'⟩ := hR'
    obtain ⟨a, K, _, _, _, ha, hK, -, ⟨e⟩⟩ := hR G hR'
    exact Or.inr (Or.inr (Or.inl ⟨2 * a + 1, ⟨a, rfl⟩, by omega,
      reeTitsModel_of_mulEquiv_reeGamma a ha K hK e⟩))
  · exact Or.inr (Or.inr (Or.inr hJ))

theorem le_pRank_of_psl2 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} [hp : Fact p.Prime]
    (hf : 0 < f) (eY : Y ≃* PSL(2, GaloisField p f)) : f ≤ CFSG.pRank p Y := by
  classical
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  let P : Sylow p (PSL(2, GaloisField p f)) := Classical.choice Sylow.nonempty
  obtain ⟨eP⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hK P
  set E : Subgroup Y := (P : Subgroup (PSL(2, GaloisField p f))).map eY.symm.toMonoidHom with hE
  let eE : Multiplicative (GaloisField p f) ≃* ↥E :=
    eP.trans (Subgroup.equivMapOfInjective _ eY.symm.toMonoidHom eY.symm.injective)
  have hEl : IsElementaryAbelian p ↥E :=
    { is_comm := ⟨fun a b => by
        apply eE.symm.injective
        rw [map_mul, map_mul, mul_comm]⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
        apply eE.symm.injective
        rw [map_pow, map_one, ← ofAdd_toAdd (eE.symm g), ← ofAdd_nsmul, nsmul_eq_mul,
          CharP.cast_eq_zero, zero_mul, ofAdd_zero] }
  have hcard : Nat.card ↥E = p ^ f := by
    rw [← Nat.card_congr eE.toEquiv]
    exact hK
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card hp.out.one_lt E hEl hcard

theorem inspWalter3320_holds
    : InspWalter3320 := by
  intro Q _ _ Y S H hYn hYs hYna hC hSQT hS hab hSH ⟨e⟩ q hq hHq
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hYs
  have hT : IsPGroup 2 (S.subgroupOf Y) :=
    hS.2.1.comap_of_injective Y.subtype Y.subtype_injective
  have hTidx : ¬ 2 ∣ (S.subgroupOf Y).index := by
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    have hSodd := hS.2.2
    rw [h3] at hSodd
    exact fun h => hSodd (h.trans (relIndex_dvd_index_of_normal' S))
  let P : Sylow 2 ↥Y := hT.toSylow hTidx
  have hP : IsMulCommutative (P : Subgroup ↥Y) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hab _ a.2 _ b.2))⟩⟩
  rcases walter_split ↥Y hYna P hP with ⟨f, hf, ⟨eY⟩⟩ | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨eY⟩⟩ |
      ⟨f, -, hf3, hRee⟩ | ⟨⟨eJ⟩⟩
  · exact (not_L2even hC hf eY hS hab hSH e).elim
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    have hfodd : f % 2 = 1 := by
      by_contra hev
      obtain ⟨k, rfl⟩ : 2 ∣ f := by omega
      obtain ⟨j, hj⟩ := Nat.eight_dvd_sq_sub_one_of_odd hpodd
      have h1 : p ^ 2 % 8 = 1 := by
        have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
        omega
      have h2 : p ^ (2 * k) % 8 = 1 := by
        rw [pow_mul, Nat.pow_mod, h1, one_pow]
        rfl
      omega
    rcases (by omega : f = 1 ∨ 3 ≤ f) with rfl | hf3
    · rw [pow_one] at h5 h8
      exact join_eq_top_of_L2prime hC hp2 h5 h8 eY hS hab hSH e hq hHq
    · exfalso
      have h1 := le_pRank_of_psl2 hf eY
      have h2 := hSQT p hp.out hp2
      omega
  · exfalso
    obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.smallReeModel_rank hRee
    have h2 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hSQT) 3 Nat.prime_three
      (by norm_num)
    omega
  · exact (not_J1 hC eJ hS hab hSH e).elim

end CFSG.Quasithin.H13.S3320
