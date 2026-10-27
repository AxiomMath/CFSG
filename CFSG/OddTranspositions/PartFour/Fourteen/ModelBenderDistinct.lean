module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.CGT.Timmesfeld75.BenderInputs3
import CFSG.Adapters.StatedSmallProjOrders
import CFSG.Walter.PSL2Facts.Even
import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

private theorem card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  have hs : Polynomial.IsSplittingField (ZMod 2) (GaloisField 2 0)
      (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)) :=
    inferInstanceAs (Polynomial.IsSplittingField (ZMod 2)
      (Polynomial.SplittingField (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2))) _)
  have h := hs.adjoin_rootSet
  rw [pow_zero, pow_one, sub_self, Polynomial.rootSet_zero, Algebra.adjoin_empty] at h
  have hbij : Function.Bijective (algebraMap (ZMod 2) (GaloisField 2 0)) :=
    ⟨(algebraMap (ZMod 2) (GaloisField 2 0)).injective, fun x =>
      Algebra.mem_bot.mp (h ▸ Algebra.mem_top)⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_zmod]

private theorem exists_card_galoisField_two (n : ℕ) :
    ∃ m, 1 ≤ m ∧ Nat.card (GaloisField 2 n) = 2 ^ m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, le_rfl, card_galoisField_two_zero⟩
  · exact ⟨n, hn, GaloisField.card 2 n hn.ne'⟩

private theorem orderOf_ne_four_of_psl2Model (n : ℕ) (g : PSL2Model n) : orderOf g ≠ 4 := by
  intro hg
  obtain ⟨m, -, hF⟩ := exists_card_galoisField_two n
  have hp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨φ⟩ := External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  have hgQ : g ∈ (Q : Subgroup (PSL2Model n)) := hQ (Subgroup.mem_zpowers g)
  obtain ⟨a, ha⟩ := φ.surjective ⟨g, hgQ⟩
  have ha2 : a ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  have hsq : (⟨g, hgQ⟩ : ↥Q) ^ 2 = 1 := by rw [← ha, ← map_pow, ha2, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hsq)
  rw [hg] at hdvd
  omega

private theorem exists_orderOf_eq_four_suzukiMatrixGroup {a : ℕ} (ha : 1 ≤ a) :
    ∃ x : SuzukiMatrixGroup a, orderOf x = 4 := by
  let K := PFAppendixIII.BinaryGaloisField (2 * a + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (a + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (a + 1)) := fun x =>
    iterateFrobeniusEquiv_def K 2 (a + 1) x
  obtain ⟨-, -, -, -, ⟨x, hx⟩, -⟩ := External.huppert_blackburn_XI_3_1 a (by omega) pi
    (External.binaryGaloisField_tits_formula_sq a pi hpi)
  have hle : Subgroup.closure {A | ∃ u v : K, A = SuzukiRootGL a u v} ≤ SuzukiMatrixGroup a :=
    Subgroup.closure_mono fun _ ⟨u, v, h⟩ => Or.inl ⟨u, v, h⟩
  exact ⟨Subgroup.inclusion hle x, by
    rw [orderOf_injective _ (Subgroup.inclusion_injective hle), hx]⟩

private theorem two_pow_mul_ne_card_psu3 {m f : ℕ} (hm : 1 ≤ m) (hf : 1 ≤ f) :
    2 ^ m * ((2 ^ m) ^ 2 - 1) * Nat.gcd 3 (2 ^ f + 1) ≠
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
  intro h
  set g := Nat.gcd 3 (2 ^ f + 1)
  have hg : 1 ≤ g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hL : Odd (((2 ^ m) ^ 2 - 1) * g) :=
    (Timmesfeld.Orders.odd_pow_sub_one (a := 2) hm (by norm_num)).mul
      (Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _))
  have hR : Odd (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
    (Timmesfeld.Orders.odd_pow_sub_one (a := 2) hf (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_add_one (a := 3) hf (by norm_num))
  have hmf : m = 3 * f := by
    refine Timmesfeld.Orders.eq_of_two_pow_mul_odd hL hR ?_
    rw [← mul_assoc, h, ← pow_mul, mul_comm f 3]
  subst hmf
  rw [mul_comm 3 f, pow_mul, mul_assoc] at h
  have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
  set q := 2 ^ f
  have hq : 2 ≤ q := le_self_pow₀ (by norm_num) (by omega)
  have h1 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2] at h'
  have hg' : (1 : ℤ) ≤ g := by exact_mod_cast hg
  nlinarith [pow_pos (by positivity : (0 : ℤ) < q) 5]

theorem false_of_mulEquiv_psu3Model_of_mulEquiv_psl2Model {X : Type} [Group X] {f n : ℕ}
    (hf : 2 ≤ f) (e : X ≃* PSU3Model f) (e' : X ≃* PSL2Model n) : False := by
  have hU := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
    (CFSG.CGT.Timmesfeld75.statedClassicalModel_psu3_of_mulEquiv hf e)
  obtain ⟨m, hm, hF⟩ := exists_card_galoisField_two n
  rw [Nat.card_congr (e'.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo).toEquiv,
    CFSG.GorensteinWalter.sl2_card_formula, hF] at hU
  exact two_pow_mul_ne_card_psu3 hm (by omega) hU

theorem false_of_isSz_of_mulEquiv_psl2Model {X : Type} [Group X] {f n : ℕ}
    (h : CFSG.Quasithin.IsSz f X) (e' : X ≃* PSL2Model n) : False := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  obtain ⟨x, hx⟩ := exists_orderOf_eq_four_suzukiMatrixGroup ha
  let φ := (e.trans
    (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).symm.trans e'
  exact orderOf_ne_four_of_psl2Model n (φ x) (by rw [MulEquiv.orderOf_eq, hx])

end CFSG.OddTranspositions.PartFour
