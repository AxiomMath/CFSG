module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423G2Dec
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.G2TypeA
import CFSG.RankThree.PartTwo.Sec4.RonanK423Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.DataGlue
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
import CFSG.RankThree.PartTwo.Sec4.E27.FixG2Model

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423.G2

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
  CFSG.AGLEmbeddingD2.Wilson.Census423Three CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

theorem layerData_of_threeA {X : Type} [Group X] [Finite X] {b : X} (h : ThreeA b) :
    LayerData b := by
  set C : Subgroup X := Subgroup.centralizer ({b} : Set X) with hCdef
  haveI : Group.IsPerfect ↥C := h.1.1
  have hCC : ⁅C, C⁆ = C := Subgroup.commutator_eq_self
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hCC.symm) h.1,
    fun z hz => ⟨1, ?_⟩, ⊥, fun a ha a' ha' => ?_, fun a ha r hr => ?_, ?_⟩
  · set φ : ↥⁅C, C⁆ ≃* ↥C := MulEquiv.subgroupCongr hCC with hφ
    have hφz : φ z ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz y']
    have h3 : ((φ z : ↥C) : X) ^ 3 = 1 := h.2 _ (φ z).2 fun c hc =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hφz ⟨c, hc⟩)).symm
    have h4 : φ z ^ 3 = 1 := Subtype.ext h3
    have h5 : z ^ 3 = 1 := φ.injective (by rw [map_pow, h4, map_one])
    rwa [pow_one]
  · rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp ha']
  · rw [Subgroup.mem_bot.mp ha, one_mul, mul_one]
  · rw [hCC, sup_bot_eq]

theorem threeA_of_short
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ThreeA z := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hp : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  rcases three_dvd_card_sub_one_or_add_one (K := K) (by rw [hK2]; norm_num) with h31 | h3
  · exact threeA_of_split h31 hzS hz3 hz1
  · refine ⟨KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hK4 hzS hz3 hz1, ?_⟩
    obtain ⟨L, _, _, _, -, hdeg, -⟩ := exists_quadratic_ext' K
    have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
    obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hK h3 hdeg hzS hz3 hz1
    have hL : Nat.card L = (2 ^ f) ^ 2 := by rw [natCard_quadratic hdeg, hK]
    have h3' : 3 ∣ 2 ^ f + 1 := by rwa [hK] at h3
    have hc := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSU_three hL h3'
    exact exp_three_of_center _ e (by rw [hc])

theorem layerData_of_cube
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {b : adjointGroup .G2 K} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    LayerData b := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hp : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨g, hg⟩ : ∃ g : adjointGroup .G2 K,
      g * b * g⁻¹ ∈ g2ShortSL2 K ∨ g * b * g⁻¹ ∈ g2LongSL2 K := by
    rcases three_dvd_card_sub_one_or_add_one (K := K) (by rw [hK2]; norm_num) with h31 | h3
    · exact g2ThreeConjSL2_split h31 hb3 hb1
    · exact KS11Lie7Proof.g2ThreeConjSL2Minus_holds K h3 hK4 b hb3 hb1
  have hb3' : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3, mul_one, mul_inv_cancel]
  have hb1' : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by simpa [mul_inv_eq_one] using h)
  refine LayerData.of_mulEquiv (MulAut.conj g) ?_
  rw [MulAut.conj_apply]
  rcases hg with hS | hM
  · exact layerData_of_threeA (threeA_of_short hf hK hS hb3' hb1')
  · exact layerData_of_long hK2 hK4 hM hb3' hb1'

theorem g2_gen_of_plane
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {D : Subgroup (adjointGroup .G2 K)}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) :
    (⊤ : Subgroup (adjointGroup .G2 K)) ≤
      Subgroup.closure {x : adjointGroup .G2 K | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x} := by
  let q0 : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hq0 : q0.card = Nat.card K := by
    rw [TauCeti.PrimePower.card_def]
    exact hK.symm
  have hv : (TauCeti.LieTypeIndex.G2 q0).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      simp only [TauCeti.LieTypeIndex.inStandardRange_iff]
      omega
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  have hA : CFSG.Open.IsElemAbelian 3 D :=
    ⟨⟨⟨fun a b => Subtype.ext (hDc a a.2 b b.2)⟩⟩, hDexp⟩
  exact (E27.g2_plane_closure q0 rfl hv hq0.symm D hA (by rw [hD9]; norm_num)).ge

theorem alphaVanishes_of_g2
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hq : CFSG.IsQuasisimple ↥(adjointGroup .G2 K))
    (hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥) {D : Subgroup (adjointGroup .G2 K)}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) : AlphaVanishes ↥(adjointGroup .G2 K) D := by
  have hL : ∀ b ∈ D, b ≠ 1 → LayerData b := fun b hb hb1 =>
    layerData_of_cube hf hK (hDexp b hb) hb1
  refine alphaVanishes_of_derived hq hZ hDc hDexp hD9 (fun b hb hb1 => (hL b hb hb1).1)
    (fun b hb hb1 => (hL b hb hb1).2.1) (fun b hb hb1 => ?_)
    (g2_gen_of_plane hf hK hDc hDexp hD9)
  obtain ⟨A, hAc, hAR, hAC⟩ := (hL b hb hb1).2.2
  exact centralizer_le_derived_sup hb hDc hAc hAR hAC

end CFSG.RankThree.PartTwo.Sec4.RonanK423.G2

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.AGLEmbeddingD2.Wilson.Census423Three

theorem census423_of_g2
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : Blueprint.ChevalleyExceptionalModel X .G2 2 f) (hq : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : Census423 X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hX
  have hq3 : 3 ≤ 2 ^ f := hadm.2.2.2
  have hf : 2 ≤ f := by
    rcases Nat.lt_or_ge f 2 with hlt | hge
    · have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact hge
  have hZK := center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let e' : X ≃* adjointGroup .G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot)
  haveI : Finite ↥(adjointGroup .G2 K) := Finite.of_equiv X e'.toEquiv
  exact census423_of_equiv_alpha e' fun D hDc hDexp hD9 =>
    G2.alphaVanishes_of_g2 hf hK (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq) hZK hDc hDexp
      hD9

end CFSG.RankThree.PartTwo.Sec4.RonanK423
