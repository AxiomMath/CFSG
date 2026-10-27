module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Main
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralizingLayerLift
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.QuasithinUnique.I32 CFSG.QuasithinUnique.Id2519

local notation "𝒪(" X ")" => CFSG.Open.componentClassificationOddCore X

theorem twoComponent_le_oddLayerOf {X : Type} [Group X] [Finite X] {t : X} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) {C : Subgroup X} (hC : C = Subgroup.centralizer ({t} : Set X))
    {L : Subgroup X} (hLC : L ≤ C) (hL : TwoComponents.IsTwoComponent (L.subgroupOf C)) :
    L ≤ oddLayerOf X := by
  classical
  let π : X →* X ⧸ 𝒪(X) := QuotientGroup.mk' 𝒪(X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective 𝒪(X)
  have hker : Odd (Nat.card π.ker) := by
    rw [show π.ker = 𝒪(X) from QuotientGroup.ker_mk' 𝒪(X)]
    exact OddCore.odd_card X
  have hcore : CFSG.Open.componentClassificationOddCore (X ⧸ 𝒪(X)) = ⊥ :=
    OddCore.quotient_corefree X
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hs2 : π t * π t = 1 := by rw [← map_mul, ht2, map_one]
  let s : X ⧸ 𝒪(X) := π t
  let Cb : Subgroup (X ⧸ 𝒪(X)) := Subgroup.centralizer ({s} : Set (X ⧸ 𝒪(X)))
  have hCmap : C.map π = Cb := by
    rw [hC]
    exact OddKernelInvolutions.image_centralizer π hπ hker t hord
  let φ : ↥C →* ↥Cb := (π.comp C.subtype).codRestrict Cb (fun c => by
    rw [← hCmap]
    exact Subgroup.mem_map_of_mem π c.2)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : X ⧸ 𝒪(X)) ∈ C.map π := by rw [hCmap]; exact y.2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hφker : Odd (Nat.card φ.ker) := by
    have hkerEq : φ.ker = (π.domRestrict C).ker := by
      ext element
      change φ element = 1 ↔ π element.val = 1
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkerEq]
    exact OddKernel.odd_card_restriction_kernel π hker C
  let L' : Subgroup ↥C := L.subgroupOf C
  let Lc : Subgroup ↥Cb := L'.map φ
  have hLc : TwoComponents.IsTwoComponent Lc :=
    OddKernelTwoComponents.image φ hφsurj hφker L' hL
  let Lb : Subgroup (X ⧸ 𝒪(X)) := Lc.map Cb.subtype
  have hLbπ : Lb = L.map π := by
    ext y
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l.1, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨φ ⟨l, hLC hl⟩, ⟨⟨l, hLC hl⟩, hl, rfl⟩, rfl⟩
  have hlayer : Lb ≤ Layer.subgroup (X ⧸ 𝒪(X)) :=
    CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
      CFSG.ClassicalInvolution.l2PrimeBalance hcore hs2 rfl hLc
  intro l hl
  have hmem : π l ∈ Lb := by
    rw [hLbπ]
    exact Subgroup.mem_map_of_mem π hl
  exact hlayer hmem

theorem isSolvable_of_card_dvd_forty_eight {Y : Type*} [Group Y] [Finite Y]
    (h : Nat.card Y ∣ 48) : Group.IsSolvable Y := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card Y).primeFactors ⊆ Nat.primeFactors 48 :=
    Nat.primeFactors_mono h (by norm_num)
  have h48 : Nat.primeFactors 48 = {2, 3} := by
    have h' : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [h', Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [h48] at hsub
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem isSolvable_mulAut_of_isElemAbelian {X : Type} [Group X] [Finite X] (Q : Subgroup X)
    (hQ : CFSG.Assembly.IsElemAbelian 3 Q) (hcard : Nat.card Q ≤ 9) :
    Group.IsSolvable (MulAut Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel : CFSG.IsElementaryAbelian 3 Q :=
    { toIsMulCommutative := hQ.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z =>
        Subtype.ext (by simpa using hQ.2 z z.2) }
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hQ)
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.LinAlg.exists_coords (p := 3) Q hn
  have hinj := CFSG.RankThree.PartOne.LinAlg.coordGL_injective f
  have h1 : Nat.card (MulAut Q) ∣ Nat.card (GL (Fin n) (ZMod 3)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 : Nat.card (GL (Fin n) (ZMod 3)) ∣ 48 := by
    rw [Matrix.card_GL_field]
    interval_cases n <;> simp [Fin.prod_univ_two, ZMod.card]
  exact isSolvable_of_card_dvd_forty_eight (h1.trans h2)

theorem commutator_eq_bot_of_perfect_of_elemAbelian {X : Type} [Group X] [Finite X]
    {P Q : Subgroup X} [Q.Normal] (hP : Group.IsPerfect P)
    (hQ : CFSG.Assembly.IsElemAbelian 3 Q) (hcard : Nat.card Q ≤ 9) : ⁅P, Q⁆ = ⊥ := by
  have hsolv := isSolvable_mulAut_of_isElemAbelian Q hQ hcard
  let κ : ↥P →* MulAut ↥Q := (MulAut.conjNormal : X →* MulAut ↥Q).comp P.subtype
  have hperf : Group.IsPerfect ↥κ.range := Group.IsPerfect.range κ
  have hsubs : Subsingleton ↥κ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥κ.range (Group.isSolvable_of_isSolvable_injective
      (Subgroup.subtype_injective κ.range))
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro p hp q hq
  have h1 : κ ⟨p, hp⟩ = 1 := by
    have : (⟨κ ⟨p, hp⟩, ⟨_, rfl⟩⟩ : ↥κ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 : ((κ ⟨p, hp⟩ ⟨q, hq⟩ : ↥Q) : X) = q := by rw [h1]; rfl
  have h3 : p * q * p⁻¹ = q := h2
  rw [Subgroup.mem_bot, commutatorElement_def]
  calc p * q * p⁻¹ * q⁻¹ = q * q⁻¹ := by rw [h3]
    _ = 1 := mul_inv_cancel q

end CFSG.Quasithin.SBd19F
