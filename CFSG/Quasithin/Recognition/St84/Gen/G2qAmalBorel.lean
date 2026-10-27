module

public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

structure G2qCoord (L S : Subgroup G) (f : ℕ) where
  F : Type
  field : Field F
  fintype : Fintype F
  card : Nat.card F = 2 ^ f
  α : ↥L →* SL(2, F)
  surj : Function.Surjective α
  ker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L
  memS : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F

structure G2qCoordRight (L S : Subgroup G) (f : ℕ) extends G2qCoord L S f where
  nat : IsNatSecOf L (centerOf (pCoreOf 2 L)) ⊥ α
  W : Subgroup G
  center_le : centerOf (pCoreOf 2 L) ≤ W
  le_pCoreOf : W ≤ pCoreOf 2 L
  card_W : Nat.card W = 2 ^ (3 * f)
  commutator_le : ⁅W, L⁆ ≤ centerOf (pCoreOf 2 L)
  natW : IsNatSecOf L (pCoreOf 2 L) W α

private theorem one_le_of_g2q (hD : G2qLocalData L1 L2 S f) : 1 ≤ f := by
  obtain ⟨F, hField, hFintype, hFcard, -⟩ := hD.nat_right
  letI := hField
  letI := hFintype
  have htwo : 2 ≤ Fintype.card F := Fintype.one_lt_card
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hFcard
  omega

theorem G2qLocalData.le_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f) (hf : 1 ≤ f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) : S ≤ L1 := by
  have hcard : Nat.card ↥(S ⊓ L1) = Nat.card ↥S := by
    rw [IsSylowTwoOf.card_eq hH.h1.sylow, twoPart_of_isL2Quot hf h1 hD.card_left,
      show 5 * f + f = 6 * f by ring, hD.card_S]
  exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]))

theorem G2qLocalData.le_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f) (hf : 1 ≤ f)
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L2 := by
  have hcard : Nat.card ↥(S ⊓ L2) = Nat.card ↥S := by
    rw [IsSylowTwoOf.card_eq hH.h2.sylow, twoPart_of_isL2Quot hf h2 hD.card_right,
      show 5 * f + f = 6 * f by ring, hD.card_S]
  exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]))

private theorem g2q_isSylowTwoOf_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) : IsSylowTwoOf S L1 :=
  isSylowTwoOf_of_card_eq (hD.le_left hH (one_le_of_g2q hD) h1) hH.h1.pgroup
    (by rw [hD.card_S, twoPart_of_isL2Quot (one_le_of_g2q hD) h1 hD.card_left,
      show 5 * f + f = 6 * f by ring])

private theorem g2q_isSylowTwoOf_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : IsSylowTwoOf S L2 :=
  isSylowTwoOf_of_card_eq (hD.le_right hH (one_le_of_g2q hD) h2) hH.h2.pgroup
    (by rw [hD.card_S, twoPart_of_isL2Quot (one_le_of_g2q hD) h2 hD.card_right,
      show 5 * f + f = 6 * f by ring])

namespace G2qLocalData

theorem exists_coordLeft (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) : Nonempty (G2qCoord L1 S f) := by
  classical
  have hsyl := g2q_isSylowTwoOf_left hH hD h1
  obtain ⟨e⟩ := h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf0 : f ≠ 0 := by have h := one_le_of_g2q hD; omega
  haveI hFin : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  haveI hChar : CharP (GaloisField 2 f) 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let π : ↥L1 →* oTwoQuot ↥L1 := QuotientGroup.mk' (CFSG.pCore 2 ↥L1)
  let α₀ : ↥L1 →* SL(2, GaloisField 2 f) :=
    (pslMulEquivSL (F := GaloisField 2 f)).toMonoidHom.comp (e.toMonoidHom.comp π)
  have hα₀app : ∀ x : ↥L1,
      α₀ x = pslMulEquivSL (F := GaloisField 2 f) (e (π x)) := fun _ => rfl
  have hα₀ : Function.Surjective α₀ :=
    (pslMulEquivSL (F := GaloisField 2 f)).surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hq : ∀ x : ↥L1, π x = 1 ↔ (x : G) ∈ pCoreOf 2 L1 := fun x =>
    (QuotientGroup.eq_one_iff x).trans (CFSG.mem_openPCoreOf_iff x).symm
  have hiff : ∀ x : ↥L1, α₀ x = 1 ↔ π x = 1 := by
    intro x
    rw [hα₀app]
    constructor
    · intro h
      have h2 : e (π x) = 1 :=
        (pslMulEquivSL (F := GaloisField 2 f)).injective (by rw [h, map_one])
      exact e.injective (by rw [h2, map_one])
    · intro h
      rw [h, map_one, map_one]
  have hker₀ : ∀ x : ↥L1, α₀ x = 1 ↔ (x : G) ∈ pCoreOf 2 L1 :=
    fun x => (hiff x).trans (hq x)
  have hker : α₀.ker = CFSG.pCore 2 ↥L1 := by
    ext x
    rw [MonoidHom.mem_ker]
    exact (hker₀ x).trans (CFSG.mem_openPCoreOf_iff x)
  obtain ⟨X, hX⟩ := exists_conj_mem_iff hsyl α₀ hα₀ hker
  let α : ↥L1 →* SL(2, GaloisField 2 f) := (MulAut.conj X).toMonoidHom.comp α₀
  have hαapp : ∀ x : ↥L1, α x = X * α₀ x * X⁻¹ := fun _ => rfl
  have hα : Function.Surjective α := (MulAut.conj X).surjective.comp hα₀
  have hker' : ∀ x : ↥L1, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L1 := by
    intro x
    have h1' : α x = 1 ↔ α₀ x = 1 := by
      rw [hαapp]
      constructor
      · intro h
        calc α₀ x = X⁻¹ * (X * α₀ x * X⁻¹) * X := by group
          _ = 1 := by rw [h]; group
      · intro h
        rw [h]
        group
    rw [h1']
    exact hker₀ x
  refine ⟨⟨GaloisField 2 f, inferInstance, inferInstance, hFcard, α, hα, hker',
    fun x => ?_⟩⟩
  rw [hαapp]
  exact hX x

theorem exists_coordRight (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : Nonempty (G2qCoordRight L2 S f) := by
  classical
  obtain ⟨F₀, hF₀, hFin, hcard0, α₀, hα₀, hker₀, hnat₀, W, hcW, hWQ, hWcard, hWcomm,
    hnatW₀⟩ := hD.nat_right
  letI := hF₀
  letI := hFin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card F₀ = 2 ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hcard0
  haveI : CharP F₀ 2 := charP_of_card_eq_prime_pow hcard0
  have hmem : ∀ x : ↥L2, α₀ x = 1 ↔ (x : G) ∈ pCoreOf 2 L2 := by
    intro x
    rw [← MonoidHom.mem_ker, hker₀, CFSG.mem_openPCoreOf_iff x]
  have hker : α₀.ker = CFSG.pCore 2 ↥L2 := by
    ext x
    rw [MonoidHom.mem_ker]
    exact (hmem x).trans (CFSG.mem_openPCoreOf_iff x)
  obtain ⟨X, hX⟩ := exists_conj_mem_iff (g2q_isSylowTwoOf_right hH hD h2) α₀ hα₀ hker
  let α : ↥L2 →* SL(2, F₀) := (MulAut.conj X).toMonoidHom.comp α₀
  have hαapp : ∀ x : ↥L2, α x = X * α₀ x * X⁻¹ := fun _ => rfl
  have hα : Function.Surjective α := (MulAut.conj X).surjective.comp hα₀
  have hnat : IsNatSecOf L2 (centerOf (pCoreOf 2 L2)) ⊥ α := isNatSecOf_comp_conj hnat₀ X
  have hnatW : IsNatSecOf L2 (pCoreOf 2 L2) W α := isNatSecOf_comp_conj hnatW₀ X
  have hker' : ∀ x : ↥L2, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L2 := by
    intro x
    have h1' : α x = 1 ↔ α₀ x = 1 := by
      rw [hαapp]
      constructor
      · intro h
        calc α₀ x = X⁻¹ * (X * α₀ x * X⁻¹) * X := by group
          _ = 1 := by rw [h]; group
      · intro h
        rw [h]
        group
    rw [h1']
    exact hmem x
  refine ⟨⟨⟨F₀, hF₀, hFin, hcard, α, hα, hker', fun x => ?_⟩, hnat, W, hcW, hWQ, hWcard,
    hWcomm, hnatW⟩⟩
  rw [hαapp]
  exact hX x

end G2qLocalData

private theorem le_borelOf_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) : S ≤ borelOf L1 S := by
  rw [borelOf_eq_inf_of_le (hD.le_left hH (one_le_of_g2q hD) h1)]
  exact le_inf (hD.le_left hH (one_le_of_g2q hD) h1) Subgroup.le_normalizer

private theorem le_borelOf_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ borelOf L2 S := by
  rw [borelOf_eq_inf_of_le (hD.le_right hH (one_le_of_g2q hD) h2)]
  exact le_inf (hD.le_right hH (one_le_of_g2q hD) h2) Subgroup.le_normalizer

private theorem borelOf_right_le_normalizer_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    borelOf L2 S ≤ Subgroup.normalizer (borelOf L1 S : Set G) := by
  intro b hb
  have hbS := mem_normalizer_of_mem_borelOf (hD.le_right hH (one_le_of_g2q hD) h2) hb
  rw [borelOf_eq_inf_of_le (hD.le_left hH (one_le_of_g2q hD) h1)]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hH.h1.borel_le hb, Subgroup.le_normalizer hbS⟩

private theorem borelOf_left_le_normalizer_right (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    borelOf L1 S ≤ Subgroup.normalizer (borelOf L2 S : Set G) := by
  intro b hb
  have hbS := mem_normalizer_of_mem_borelOf (hD.le_left hH (one_le_of_g2q hD) h1) hb
  rw [borelOf_eq_inf_of_le (hD.le_right hH (one_le_of_g2q hD) h2)]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hH.h2.borel_le hb, Subgroup.le_normalizer hbS⟩

theorem G2qLocalData.bigB_eq_sup (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) :
    bigB L1 L2 S = borelOf L1 S ⊔ borelOf L2 S := by
  rw [bigB]
  exact sup_eq_left.mpr ((le_borelOf_left hH hD h1).trans le_sup_left)

theorem G2qLocalData.bigB_le_normalizer (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) ⊓ Subgroup.normalizer (L2 : Set G) ⊓
      Subgroup.normalizer (S : Set G) := by
  have hSL1 : S ≤ L1 := hD.le_left hH (one_le_of_g2q hD) h1
  have hSL2 : S ≤ L2 := hD.le_right hH (one_le_of_g2q hD) h2
  refine sup_le (sup_le ?_ ?_) ?_
  · intro b hb
    exact ⟨⟨Subgroup.le_normalizer (borelOf_le L1 S hb), hH.h2.borel_le hb⟩,
      mem_normalizer_of_mem_borelOf hSL1 hb⟩
  · intro b hb
    exact ⟨⟨hH.h1.borel_le hb, Subgroup.le_normalizer (borelOf_le L2 S hb)⟩,
      mem_normalizer_of_mem_borelOf hSL2 hb⟩
  · intro s hs
    exact ⟨⟨hH.h1.normalizes hs, hH.h2.normalizes hs⟩, Subgroup.le_normalizer hs⟩

theorem G2qLocalData.card_borelOf_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) :
    Nat.card (borelOf L1 S) = 2 ^ (6 * f) * (2 ^ f - 1) := by
  classical
  have hS1 : S ≤ L1 := hD.le_left hH (one_le_of_g2q hD) h1
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  letI := c1.field
  letI := c1.fintype
  rw [card_eq_card_mul_card_of_alpha c1.α c1.surj c1.ker (borelOf_le L1 S)
    (hH.pCoreOf_le_left.trans (le_borelOf_left hH hD h1)) (borel c1.F)
    (mem_borelOf_iff_alpha_mem_borel hS1 c1.α c1.surj c1.memS), hD.card_left, card_borel,
    c1.card, show 6 * f = 5 * f + f by ring, pow_add, mul_assoc]

theorem G2qLocalData.card_borelOf_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    Nat.card (borelOf L2 S) = 2 ^ (6 * f) * (2 ^ f - 1) := by
  classical
  have hS2 : S ≤ L2 := hD.le_right hH (one_le_of_g2q hD) h2
  obtain ⟨c2⟩ := hD.exists_coordRight hH h2
  letI := c2.field
  letI := c2.fintype
  rw [card_eq_card_mul_card_of_alpha c2.α c2.surj c2.ker (borelOf_le L2 S)
    (hH.pCoreOf_le_right.trans (le_borelOf_right hH hD h2)) (borel c2.F)
    (mem_borelOf_iff_alpha_mem_borel hS2 c2.α c2.surj c2.memS), hD.card_right, card_borel,
    c2.card, show 6 * f = 5 * f + f by ring, pow_add, mul_assoc]

private theorem centerOf_pCoreOf_left_comm (hD : G2qLocalData L1 L2 S f) {z : G}
    (hz : z ∈ centerOf (pCoreOf 2 L1)) {y : G} (hy : y ∈ L1) : y * z = z * y := by
  rw [hD.center_left] at hz
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y hy

theorem G2qLocalData.centerOf_pCoreOf_left_le_right (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    centerOf (pCoreOf 2 L1) ≤ centerOf (pCoreOf 2 L2) := by
  classical
  have hS1 : S ≤ L1 := hD.le_left hH (one_le_of_g2q hD) h1
  have hS2 : S ≤ L2 := hD.le_right hH (one_le_of_g2q hD) h2
  have hZleS : centerOf (pCoreOf 2 L1) ≤ S :=
    (show centerOf (pCoreOf 2 L1) ≤ pCoreOf 2 L1 from inf_le_left).trans hH.pCoreOf_le_left
  have hP2 : L2 ⊔ S ⊔ borelOf L1 S = L2 ⊔ bigB L1 L2 S := by
    rw [show L2 ⊔ S = L2 from sup_eq_left.mpr hS2]
    refine le_antisymm ?_ ?_
    · refine sup_le le_sup_left ?_
      exact (le_sup_left.trans le_sup_left).trans le_sup_right
    · refine sup_le le_sup_left ?_
      rw [bigB]
      exact sup_le (sup_le le_sup_right ((borelOf_le L2 S).trans le_sup_left))
        (hS2.trans le_sup_left)
  have hcore : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 :=
    pCoreOf_sup_bigB_right_of_le hH hS1 hS2
  intro z hz
  have hzP : z ∈ L2 ⊔ S ⊔ borelOf L1 S :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (hZleS hz))
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) : Set G) := by
    rw [hP2, hcore]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      centerOf_pCoreOf_left_comm hD hz (hS1 (hH.pCoreOf_le_right hy))
  have hzQ2 : z ∈ pCoreOf 2 L2 := by
    have hz2 : z ∈ pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) := hH.h2.charTwo ⟨hzP, hzC⟩
    rwa [hP2, hcore] at hz2
  exact Subgroup.mem_inf.mpr ⟨hzQ2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    centerOf_pCoreOf_left_comm hD hz (hS1 (hH.pCoreOf_le_right hy))⟩

theorem G2qLocalData.borelOf_inf_borelOf (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    borelOf L1 S ⊓ borelOf L2 S = S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := one_le_of_g2q hD
  have hS1 : S ≤ L1 := hD.le_left hH (one_le_of_g2q hD) h1
  obtain ⟨c2⟩ := hD.exists_coordRight hH h2
  letI := c2.field
  letI := c2.fintype
  obtain ⟨β, -, hβker, hβeq⟩ := c2.nat
  have hZQ : centerOf (pCoreOf 2 L1) ≤ centerOf (pCoreOf 2 L2) :=
    hD.centerOf_pCoreOf_left_le_right hH h1 h2
  refine le_antisymm ?_ (le_inf (le_borelOf_left hH hD h1) (le_borelOf_right hH hD h2))
  rintro d ⟨hd1, hd2⟩
  have hdL1 : d ∈ L1 := borelOf_le L1 S hd1
  have hdL2 : d ∈ L2 := borelOf_le L2 S hd2
  have hZnt : Nontrivial ↥(Subgroup.center ↥(pCoreOf 2 L1)) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hD.special_left.2.2]
    have hlt : 2 ^ 0 < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simpa using hlt
  obtain ⟨z', hz'1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(pCoreOf 2 L1)))
  have hzQ1 : ((z' : ↥(pCoreOf 2 L1)) : G) ∈ pCoreOf 2 L1 := (z' : ↥(pCoreOf 2 L1)).2
  have hz : ((z' : ↥(pCoreOf 2 L1)) : G) ∈ centerOf (pCoreOf 2 L1) := by
    refine Subgroup.mem_inf.mpr ⟨hzQ1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg (fun w : ↥(pCoreOf 2 L1) => (w : G))
      (Subgroup.mem_center_iff.mp z'.2 ⟨y, hy⟩)
  have hz1 : ((z' : ↥(pCoreOf 2 L1)) : G) ≠ 1 := by
    intro h
    exact hz'1 (Subtype.ext (Subtype.ext h))
  have hzZ2 : ((z' : ↥(pCoreOf 2 L1)) : G) ∈ centerOf (pCoreOf 2 L2) := hZQ hz
  set z : G := ((z' : ↥(pCoreOf 2 L1)) : G) with hzdef
  set v : Fin 2 → c2.F := Multiplicative.toAdd (β ⟨z, hzZ2⟩) with hvdef
  have hv : v ≠ 0 := by
    intro h0
    apply hz1
    have hzZne : (⟨z, hzZ2⟩ : ↥(centerOf (pCoreOf 2 L2))) = 1 := by
      have hmem : (⟨z, hzZ2⟩ : ↥(centerOf (pCoreOf 2 L2))) ∈ β.ker := by
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd (β ⟨z, hzZ2⟩) = 0
        rw [← hvdef, h0]
      rw [hβker] at hmem
      simpa using hmem
    exact congrArg (fun y : ↥(centerOf (pCoreOf 2 L2)) => (y : G)) hzZne
  have hfixS : ∀ x : ↥L2, (x : G) ∈ S →
      (c2.α x : Matrix (Fin 2) (Fin 2) c2.F) *ᵥ v = v := by
    intro x hx
    have hzs : ((⟨z, hzZ2⟩ : ↥(centerOf (pCoreOf 2 L2))) : G) = (x : G) * z * (x : G)⁻¹ := by
      show z = (x : G) * z * (x : G)⁻¹
      rw [centerOf_pCoreOf_left_comm hD hz (hS1 hx)]
      group
    exact (hβeq x ⟨z, hzZ2⟩ ⟨z, hzZ2⟩ hzs).symm
  have hv1 : v 1 = 0 := mulVec_apply_one_eq_zero c2.surj c2.memS hfixS
  have hv0 : v 0 ≠ 0 := by
    intro h0
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact hv1
  set A : SL(2, c2.F) := c2.α ⟨d, hdL2⟩ with hAdef
  have hfixA : (A : Matrix (Fin 2) (Fin 2) c2.F) *ᵥ v = v := by
    have hdz : ((⟨z, hzZ2⟩ : ↥(centerOf (pCoreOf 2 L2))) : G) = d * z * d⁻¹ := by
      show z = d * z * d⁻¹
      rw [centerOf_pCoreOf_left_comm hD hz hdL1]
      group
    exact (hβeq ⟨d, hdL2⟩ ⟨z, hzZ2⟩ ⟨z, hzZ2⟩ hdz).symm
  exact (c2.memS ⟨d, hdL2⟩).mpr (mem_utri_of_mulVec_eq_self hfixA hv0 hv1)

private theorem normal_subgroupOf_bigB (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    (S.subgroupOf (bigB L1 L2 S)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer ((hD.bigB_le_normalizer hH h1 h2).trans inf_le_right)

theorem G2qLocalData.commutator_mem_of_mem_bigB (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    ∀ x ∈ bigB L1 L2 S, ∀ y ∈ bigB L1 L2 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
  classical
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  obtain ⟨c2⟩ := hD.exists_coordRight hH h2
  letI := c1.field
  letI := c1.fintype
  letI := c2.field
  letI := c2.fintype
  have hSL1 : S ≤ L1 := hD.le_left hH (one_le_of_g2q hD) h1
  have hSL2 : S ≤ L2 := hD.le_right hH (one_le_of_g2q hD) h2
  have hB₁ := mem_borelOf_iff_alpha_mem_borel hSL1 c1.α c1.surj c1.memS
  have hB₂ := mem_borelOf_iff_alpha_mem_borel hSL2 c2.α c2.surj c2.memS
  have h11 : ∀ x ∈ borelOf L1 S, ∀ y ∈ borelOf L1 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    exact commutator_mem_of_alpha_mem_borel c1.α c1.memS
      ((hB₁ ⟨x, borelOf_le L1 S hx⟩).mp hx) ((hB₁ ⟨y, borelOf_le L1 S hy⟩).mp hy)
  have h22 : ∀ x ∈ borelOf L2 S, ∀ y ∈ borelOf L2 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    exact commutator_mem_of_alpha_mem_borel c2.α c2.memS
      ((hB₂ ⟨x, borelOf_le L2 S hx⟩).mp hx) ((hB₂ ⟨y, borelOf_le L2 S hy⟩).mp hy)
  have hN21 := borelOf_right_le_normalizer_left hH hD h1 h2
  have hN12 := borelOf_left_le_normalizer_right hH hD h1 h2
  have h12 : ∀ x ∈ borelOf L1 S, ∀ y ∈ borelOf L2 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    rw [← hD.borelOf_inf_borelOf hH h1 h2]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hN21 hy) x⁻¹).mp (inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hx h
    · have h := (Subgroup.mem_normalizer_iff.mp (hN12 hx) y).mp hy
      exact mul_mem h (inv_mem hy)
  have h21 : ∀ x ∈ borelOf L2 S, ∀ y ∈ borelOf L1 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    have h := inv_mem (h12 y hy x hx)
    have e : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
    rwa [e] at h
  haveI := normal_subgroupOf_bigB hH hD h1 h2
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  intro x hx y hy
  have hx' : x ∈ borelOf L1 S ⊔ borelOf L2 S := by rw [← hD.bigB_eq_sup hH h1]; exact hx
  have hy' : y ∈ borelOf L1 S ⊔ borelOf L2 S := by rw [← hD.bigB_eq_sup hH h1]; exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hN21).mp hx'
  obtain ⟨c, hc, e, he, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hN21).mp hy'
  refine (commute_mk_iff_commutator_mem (S := S) (⟨a, hB1B ha⟩ * ⟨b, hB2B hb⟩ : ↥(bigB L1 L2 S))
    (⟨c, hB1B hc⟩ * ⟨e, hB2B he⟩)).mp ?_
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  have hac := (commute_mk_iff_commutator_mem ⟨a, hB1B ha⟩ ⟨c, hB1B hc⟩).mpr (h11 a ha c hc)
  have hae := (commute_mk_iff_commutator_mem ⟨a, hB1B ha⟩ ⟨e, hB2B he⟩).mpr (h12 a ha e he)
  have hbc := (commute_mk_iff_commutator_mem ⟨b, hB2B hb⟩ ⟨c, hB1B hc⟩).mpr (h21 b hb c hc)
  have hbe := (commute_mk_iff_commutator_mem ⟨b, hB2B hb⟩ ⟨e, hB2B he⟩).mpr (h22 b hb e he)
  exact (hac.mul_right hae).mul_left (hbc.mul_right hbe)

theorem G2qLocalData.card_bigB (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    Nat.card (bigB L1 L2 S) = 2 ^ (6 * f) * ((2 ^ f - 1) * (2 ^ f - 1)) := by
  have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (borelOf_right_le_normalizer_left hH hD h1 h2)
  have hsup : borelOf L2 S ⊔ borelOf L1 S = bigB L1 L2 S := by
    rw [hD.bigB_eq_sup hH h1, sup_comm]
  have hinf : borelOf L2 S ⊓ borelOf L1 S = S := by
    rw [inf_comm, hD.borelOf_inf_borelOf hH h1 h2]
  rw [hsup, hinf, hD.card_S, hD.card_borelOf_left hH h1, hD.card_borelOf_right hH h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ (6 * f) by positivity)
  rw [h]
  ring

theorem G2qLocalData.exists_hall_bigB (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    ∃ H : Subgroup G, H ≤ bigB L1 L2 S ∧ S ⊔ H = bigB L1 L2 S ∧ S ⊓ H = ⊥ ∧
      Nat.card H = (2 ^ f - 1) * (2 ^ f - 1) ∧ ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  have hf : 1 ≤ f := one_le_of_g2q hD
  have hodd1 : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega : f ≠ 0)) odd_one
  have hodd : Odd ((2 ^ f - 1) * (2 ^ f - 1)) := hodd1.mul hodd1
  have hcop : Nat.Coprime (2 ^ (6 * f)) ((2 ^ f - 1) * (2 ^ f - 1)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
    (hD.bigB_le_normalizer hH h1 h2).trans inf_le_right
  obtain ⟨H, hHB, hsup, hcard⟩ := exists_sup_eq_of_coprime (N := S) (X := bigB L1 L2 S)
    le_sup_right hBN ((2 ^ f - 1) * (2 ^ f - 1))
    (by rw [hD.card_bigB hH h1 h2, hD.card_S]) (by rw [hD.card_S]; exact hcop)
  have hinf : S ⊓ H = ⊥ := Subgroup.inf_eq_bot_of_coprime (by rw [hD.card_S, hcard]; exact hcop)
  refine ⟨H, hHB, hsup, hinf, hcard, fun a ha b hb => ?_⟩
  have h1' : a * b * a⁻¹ * b⁻¹ ∈ S ⊓ H := Subgroup.mem_inf.mpr
    ⟨hD.commutator_mem_of_mem_bigB hH h1 h2 a (hHB ha) b (hHB hb),
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at h1'
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1')

theorem G2qLocalData.torus_left_of_hall (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S)
    (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    Nat.card ↥(H ⊓ L1) = 2 ^ f - 1 ∧
      Nat.card ↥(H ⊓ trivOTwoQuot L1) = 2 ^ f - 1 ∧
      (H ⊓ L1) ⊔ (H ⊓ trivOTwoQuot L1) = H ∧ (H ⊓ trivOTwoQuot L1) ⊓ L1 = ⊥ ∧
      L1 ⊔ bigB L1 L2 S = L1 ⊔ (H ⊓ trivOTwoQuot L1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkpos : 0 < 2 ^ f - 1 := by
    have h1' : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  have hS1 : S ≤ L1 := hD.le_left hH (one_le_of_g2q hD) h1
  have hNB := hD.bigB_le_normalizer hH h1 h2
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  obtain ⟨hBLeq, -, hcardT⟩ := hall_inf_card (L := L1) (H := H) (U := S)
    (B := bigB L1 L2 S) (a := 2 ^ (6 * f)) (c := 2 ^ f - 1)
    hS1 hHB hSH hB1B (hNB.trans inf_le_right) hSinfH (hD.card_borelOf_left hH h1)
    hD.card_S (by positivity)
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  letI := c1.field
  letI := c1.fintype
  haveI : CharP c1.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c1.card])
  have hF4 : 4 ≤ Nat.card c1.F := by
    rw [c1.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hNB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) ⊓
      Subgroup.normalizer (pCoreOf 2 L1 : Set G) ⊓ Subgroup.normalizer (S : Set G) :=
    le_inf (le_inf ((hNB.trans inf_le_left).trans inf_le_left)
      hH.bigB_le_normalizer_pCoreOf_left) (hNB.trans inf_le_right)
  exact exists_torus_of_hall (L := L1) (H := H) (k := 2 ^ f - 1) (m := 2 ^ f - 1)
    (F := c1.F) hS1 hHB hSinfH hHcomm hNB1 hH.pCoreOf_le_left hSH hBLeq hcardT
    hHcard hkpos (by rw [c1.card]) hF4 c1.α c1.surj c1.ker c1.memS

theorem G2qLocalData.torus_right_of_hall (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S)
    (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    Nat.card ↥(H ⊓ L2) = 2 ^ f - 1 ∧
      Nat.card ↥(H ⊓ trivOTwoQuot L2) = 2 ^ f - 1 ∧
      (H ⊓ L2) ⊔ (H ⊓ trivOTwoQuot L2) = H ∧ (H ⊓ trivOTwoQuot L2) ⊓ L2 = ⊥ ∧
      L2 ⊔ bigB L1 L2 S = L2 ⊔ (H ⊓ trivOTwoQuot L2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkpos : 0 < 2 ^ f - 1 := by
    have h1' : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  have hS2 : S ≤ L2 := hD.le_right hH (one_le_of_g2q hD) h2
  have hNB := hD.bigB_le_normalizer hH h1 h2
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  obtain ⟨hBLeq, -, hcardT⟩ := hall_inf_card (L := L2) (H := H) (U := S)
    (B := bigB L1 L2 S) (a := 2 ^ (6 * f)) (c := 2 ^ f - 1)
    hS2 hHB hSH hB2B (hNB.trans inf_le_right) hSinfH (hD.card_borelOf_right hH h2)
    hD.card_S (by positivity)
  obtain ⟨c2⟩ := hD.exists_coordRight hH h2
  letI := c2.field
  letI := c2.fintype
  haveI : CharP c2.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c2.card])
  have hF4 : 4 ≤ Nat.card c2.F := by
    rw [c2.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hNB2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) ⊓
      Subgroup.normalizer (pCoreOf 2 L2 : Set G) ⊓ Subgroup.normalizer (S : Set G) :=
    le_inf (le_inf ((hNB.trans inf_le_left).trans inf_le_right)
      hH.bigB_le_normalizer_pCoreOf_right) (hNB.trans inf_le_right)
  exact exists_torus_of_hall (L := L2) (H := H) (k := 2 ^ f - 1) (m := 2 ^ f - 1)
    (F := c2.F) hS2 hHB hSinfH hHcomm hNB2 hH.pCoreOf_le_right hSH hBLeq hcardT
    hHcard hkpos (by rw [c2.card]) hF4 c2.α c2.surj c2.ker c2.memS

theorem G2qLocalData.exists_torus_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    ∃ H₀ : Subgroup G, H₀ ≤ bigB L1 L2 S ∧ (∀ a ∈ H₀, ∀ b ∈ H₀, a * b = b * a) ∧
      Nat.card H₀ = 2 ^ f - 1 ∧ (∀ h ∈ H₀, ∀ x ∈ L2, h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L2) ∧
      H₀ ⊓ L2 = ⊥ ∧ L2 ⊔ bigB L1 L2 S = L2 ⊔ H₀ := by
  obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hD.exists_hall_bigB hH h1 h2
  obtain ⟨-, hcard, -, hinf, hsupeq⟩ :=
    hD.torus_right_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  refine ⟨H ⊓ trivOTwoQuot L2, inf_le_left.trans hHB, ?_, hcard, ?_, hinf, hsupeq⟩
  · intro a ha b hb
    exact hHcomm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1
  · intro h hh x hx
    exact (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).2 x hx

end CFSG.Quasithin.F112R.St84

end
