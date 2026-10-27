module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetPairDistribution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCommutingPairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetPairIncidence
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinHighFiber
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise BigOperators

namespace CFSG.GorensteinWalter

universe u

/-!
# Identity (8): `3·b₄ + b₂ = 6·k²`

The aggregate commuting-pair count over the outside involutions of `Ĥ`
(`12·k²`) is partitioned over the non-base `Ĥ`-cosets.  By the local
distribution theorem each fibre contributes `2` ordered pairs when it has
two involutions and `6` when it has four, so the total is `2·b₂ + 6·b₄`;
dividing by two gives identity (8).
-/

/-- The outside involutions of `Ĥ`, with the coset projection used by the
aggregate commuting-pair incidence. -/
private abbrev InvOutType {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Type u :=
  {z : G // IsInvolution z ∧ z ∉ c.Hhat}

private abbrev fiberProj {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) :
    InvOutType c → G ⧸ c.Hhat :=
  fun z => cosetInvolution_proj c.Hhat (z : G)

/-- The non-base cosets of `Ĥ`. -/
private abbrev Nonbase {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Type u :=
  {ω : G ⧸ c.Hhat // ω ≠ cosetInvolution_base c.Hhat}

/-- The involutions of `Ĥ` lying in the non-base coset `ω`. -/
private abbrev Fiber {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G)
    (ω : G ⧸ c.Hhat) : Type u :=
  {z : InvOutType c // fiberProj c z = ω}

/-- Ordered commuting pairs of distinct involutions in the coset `ω`. -/
private abbrev PairFiber {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G)
    (ω : G ⧸ c.Hhat) : Type u :=
  {p : Fiber c ω × Fiber c ω // p.1 ≠ p.2 ∧ Commute (p.1.1 : G) (p.2.1 : G)}

/-- An element of a non-base fibre is outside `Ĥ`: membership in `Ĥ`
would force the coset to be the base coset. -/
private lemma fiber_mem_out {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    {z : G} (hzI : IsInvolution z)
    (hzcos : cosetInvolution_proj c.Hhat z = cosetInvolution_proj c.Hhat y) :
    z ∉ c.Hhat := by
  intro hz
  apply hyH
  have hybase : cosetInvolution_proj c.Hhat y = cosetInvolution_base c.Hhat := by
    rw [← hzcos]
    change QuotientGroup.mk (z⁻¹) = QuotientGroup.mk ((1 : G)⁻¹)
    apply (QuotientGroup.eq (s := c.Hhat)).mpr
    simpa using hz
  change QuotientGroup.mk (y⁻¹) = QuotientGroup.mk ((1 : G)⁻¹) at hybase
  have hmem : (y⁻¹)⁻¹ * (1 : G)⁻¹ ∈ c.Hhat :=
    (QuotientGroup.eq (s := c.Hhat)).mp hybase
  simpa using hmem

/-- A non-base fibre with representative `y` is equivalent to the local
coset fibre used by the distribution theorems. -/
private def fiberEquiv {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G)
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (ω : G ⧸ c.Hhat) (hω : cosetInvolution_proj c.Hhat y = ω) :
    Fiber c ω ≃ cosetFiber c y where
  toFun := fun z => ⟨(z.1 : G), z.1.2.1, by
    change cosetInvolution_proj c.Hhat (z.1 : G) = cosetInvolution_proj c.Hhat y
    rw [hω]
    exact z.2⟩
  invFun := fun z => ⟨⟨(z : G), z.2.1, fiber_mem_out c hy hyH z.2.1 z.2.2⟩, by
    change cosetInvolution_proj c.Hhat (z : G) = ω
    rw [← hω]
    exact z.2.2⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl

/-- The generic coset fibre has the same cardinality as the source
coset-involution fibre over the projection of `y`. -/
private lemma cosetFiber_card_eq_cosetInvolution_fiber
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) {y : G} :
    Nat.card (cosetFiber c y) =
      Nat.card (cosetInvolution_fiber c.Hhat
        (cosetInvolution_proj c.Hhat y)) := by
  let f : cosetFiber c y →
      cosetInvolution_fiber c.Hhat (cosetInvolution_proj c.Hhat y) :=
    fun z => ⟨(z : G), z.2.1, z.2.2⟩
  let g : cosetInvolution_fiber c.Hhat (cosetInvolution_proj c.Hhat y) →
      cosetFiber c y :=
    fun z => ⟨(z.1 : G), z.2.1, z.2.2⟩
  have hfg : Function.LeftInverse f g := by
    intro z
    apply Subtype.ext
    rfl
  have hgf : Function.RightInverse f g := by
    intro z
    apply Subtype.ext
    rfl
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 : g (f a) = g (f b) := congrArg g h
    simpa [hgf] using h1
  have hfsurj : Function.Surjective f := by
    intro b
    exact ⟨g b, hfg b⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)

/-- Once all fibres of size at least five vanish, every individual fibre
has size at most four. -/
private lemma involution_fiber_bound_of_vanishing
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G)
    (hvan : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0)
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat) :
    Nat.card {x : G // x ∈ invertedElements c.Hhat y} ≤ 4 := by
  classical
  by_contra hle
  let n : ℕ := Nat.card {x : G // x ∈ invertedElements c.Hhat y}
  have hge : 5 ≤ n := by omega
  have hb0 : cosetInvolution_b c.Hhat n = 0 := hvan n hge
  have hfib : Nat.card (cosetInvolution_fiber c.Hhat
      (cosetInvolution_proj c.Hhat y)) = n := by
    calc
      Nat.card (cosetInvolution_fiber c.Hhat
          (cosetInvolution_proj c.Hhat y)) =
          Nat.card (cosetFiber c y) :=
            (cosetFiber_card_eq_cosetInvolution_fiber c).symm
      _ = Nat.card {x : G // x ∈ invertedElements c.Hhat y} :=
            Nat.card_congr (cosetFiber_equiv_inverted c hy hyH)
      _ = n := by rfl
  have hyn : y ∈ firstCaseJ c n := by
    refine ⟨hy, hyH, ?_⟩
    change firstCaseCosetInvolutions c y = n
    rw [firstCase_coset_fiber_card_eq c hy]
    exact hfib
  have hnonempty : 0 < Nat.card {x : G // x ∈ firstCaseJ c n} :=
    Finite.card_pos_iff.mpr ⟨⟨y, hyn⟩⟩
  have hzero : Nat.card {x : G // x ∈ firstCaseJ c n} = 0 := by
    rw [firstCase_J_n_card c n, hb0]
    simp
  omega

/-- The local distribution over a non-base fibre, with the bound supplied
by the vanishing of the large fibres. -/
private theorem pairFiber_card_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hvan : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0)
    (ω : Nonbase c) :
    Nat.card (PairFiber c ω.1) =
      if Nat.card (Fiber c ω.1) = 2 then 2
      else if Nat.card (Fiber c ω.1) = 4 then 6 else 0 := by
  classical
  by_cases hc0 : Nat.card (Fiber c ω.1) = 0
  · let : Fintype (Fiber c ω.1) := Fintype.ofFinite _
    have : IsEmpty (Fiber c ω.1) :=
      Fintype.card_eq_zero_iff.mp (by simpa [Nat.card_eq_fintype_card] using hc0)
    have : IsEmpty (PairFiber c ω.1) := ⟨fun p => isEmptyElim p.1.1⟩
    rw [hc0]
    simp
  · have hne : Nonempty (Fiber c ω.1) :=
      Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hc0)
    rcases hne with ⟨z⟩
    let y : G := (z.1 : G)
    have hy : IsInvolution y := z.1.2.1
    have hyH : y ∉ c.Hhat := z.1.2.2
    have hω : cosetInvolution_proj c.Hhat y = ω.1 := by
      simpa [y] using z.2
    let eF : Fiber c ω.1 ≃ cosetFiber c y := fiberEquiv c hy hyH ω.1 hω
    have hbound : Nat.card {x : G // x ∈ invertedElements c.Hhat y} ≤ 4 :=
      involution_fiber_bound_of_vanishing c hvan hy hyH
    have hlocal_y := firstCase_klein_coset_pair_card_eq
      hmin c hfirst hklein hy hyH hbound
    have hpair_card : Nat.card (PairFiber c ω.1) =
        Nat.card (cosetCommPair c y) := by
      let ePair : PairFiber c ω.1 ≃ cosetCommPair c y :=
        { toFun := fun p =>
            ⟨(eF p.1.1, eF p.1.2), ⟨by
              intro h
              apply p.2.1
              exact eF.injective h,
              by simpa [eF, fiberEquiv] using p.2.2⟩⟩
          invFun := fun p =>
            ⟨(eF.symm p.1.1, eF.symm p.1.2), ⟨by
              intro h
              apply p.2.1
              exact eF.symm.injective h,
              by simpa [eF, fiberEquiv] using p.2.2⟩⟩
          left_inv := by
            intro p
            apply Subtype.ext
            apply Prod.ext
            · apply Subtype.ext
              simp [eF, fiberEquiv]
            · apply Subtype.ext
              simp [eF, fiberEquiv]
          right_inv := by
            intro p
            apply Subtype.ext
            apply Prod.ext
            · apply Subtype.ext
              simp [eF, fiberEquiv]
            · apply Subtype.ext
              simp [eF, fiberEquiv] }
      exact Nat.card_congr ePair
    have hcard_eq : Nat.card (Fiber c ω.1) =
        Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
      calc
        Nat.card (Fiber c ω.1) = Nat.card (cosetFiber c y) := Nat.card_congr eF
        _ = Nat.card {x : G // x ∈ invertedElements c.Hhat y} :=
              Nat.card_congr (cosetFiber_equiv_inverted c hy hyH)
    calc
      Nat.card (PairFiber c ω.1) = Nat.card (cosetCommPair c y) := hpair_card
      _ = (if Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 2 then 2
           else if Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 4 then 6
           else 0) := hlocal_y
      _ = (if Nat.card (Fiber c ω.1) = 2 then 2
           else if Nat.card (Fiber c ω.1) = 4 then 6 else 0) := by
            rw [hcard_eq]

/-- The non-base fibre cardinals agree with the generic coset fibre
cardinals, hence the fibre-size subtype is exactly `bₙ`. -/
private lemma fiberCard_subtype_eq_coset_b
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) (n : ℕ) :
    Nat.card {ω : Nonbase c // Nat.card (Fiber c ω.1) = n} =
      cosetInvolution_b c.Hhat n := by
  classical
  let Ω : Type u := G ⧸ c.Hhat
  let π : G → Ω := cosetInvolution_proj c.Hhat
  let base : Ω := cosetInvolution_base c.Hhat
  have hcard (ω : Nonbase c) :
      Nat.card (Fiber c ω.1) = Nat.card (involutionFiber π ω.1) := by
    let f : Fiber c ω.1 → involutionFiber π ω.1 := fun z =>
      ⟨(z.1 : G), z.1.2.1, by
        change π (z.1 : G) = ω.1
        exact z.2⟩
    let g : involutionFiber π ω.1 → Fiber c ω.1 := fun z =>
      ⟨⟨(z.1 : G), z.2.1, by
        intro hz
        apply ω.2
        have hbase : π (z.1 : G) = base := by
          change QuotientGroup.mk ((z.1 : G)⁻¹) = QuotientGroup.mk ((1 : G)⁻¹)
          apply (QuotientGroup.eq (s := c.Hhat)).mpr
          simpa using (c.Hhat.inv_mem hz)
        exact z.2.2.symm.trans hbase⟩, by
        change π (z.1 : G) = ω.1
        exact z.2.2⟩
    have hfg : Function.LeftInverse f g := by
      intro z
      apply Subtype.ext
      rfl
    have hgf : Function.RightInverse f g := by
      intro z
      apply Subtype.ext
      rfl
    have hfinj : Function.Injective f := by
      intro a b h
      have h1 : g (f a) = g (f b) := congrArg g h
      simpa [hgf] using h1
    have hfsurj : Function.Surjective f := by
      intro b
      exact ⟨g b, hfg b⟩
    exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  let eSub : {ω : Nonbase c // Nat.card (Fiber c ω.1) = n} ≃
      {ω : Ω // ω ≠ base ∧ Nat.card (involutionFiber π ω) = n} :=
    { toFun := fun ω => ⟨ω.1.1, ω.1.2, by
        have hc := hcard ω.1
        rw [← hc]
        exact ω.2⟩
      invFun := fun ω => ⟨⟨ω.1, ω.2.1⟩, by
        have hc := hcard ⟨ω.1, ω.2.1⟩
        rw [hc]
        exact ω.2.2⟩
      left_inv := by intro ω; rfl
      right_inv := by intro ω; rfl }
  calc
    Nat.card {ω : Nonbase c // Nat.card (Fiber c ω.1) = n} =
        Nat.card {ω : Ω // ω ≠ base ∧ Nat.card (involutionFiber π ω) = n} :=
          Nat.card_congr eSub
    _ = cosetInvolution_b c.Hhat n := by
      rw [cosetInvolution_b_card]

/-- The sum of the local commuting-pair counts over the non-base cosets
is `2·b₂ + 6·b₄`. -/
private theorem sum_pairFiber_cards
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hvan : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0) :
    Nat.card (Σ ω : Nonbase c, PairFiber c ω.1) =
      2 * cosetInvolution_b c.Hhat 2 + 6 * cosetInvolution_b c.Hhat 4 := by
  classical
  let : Fintype (Nonbase c) := Fintype.ofFinite _
  have hlocal : ∀ ω : Nonbase c, Nat.card (PairFiber c ω.1) =
      (if Nat.card (Fiber c ω.1) = 2 then 2 else 0) +
      (if Nat.card (Fiber c ω.1) = 4 then 6 else 0) := by
    intro ω
    have h := pairFiber_card_eq hmin c hfirst hklein hvan ω
    by_cases h2 : Nat.card (Fiber c ω.1) = 2 <;>
      by_cases h4 : Nat.card (Fiber c ω.1) = 4 <;> simp [h, h2, h4]
  calc
    Nat.card (Σ ω : Nonbase c, PairFiber c ω.1) =
        ∑ ω : Nonbase c, Nat.card (PairFiber c ω.1) := Nat.card_sigma
    _ = ∑ ω : Nonbase c,
          ((if Nat.card (Fiber c ω.1) = 2 then 2 else 0) +
           (if Nat.card (Fiber c ω.1) = 4 then 6 else 0)) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact hlocal ω
    _ = (∑ ω : Nonbase c, if Nat.card (Fiber c ω.1) = 2 then 2 else 0) +
        (∑ ω : Nonbase c, if Nat.card (Fiber c ω.1) = 4 then 6 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = 2 * Nat.card {ω : Nonbase c // Nat.card (Fiber c ω.1) = 2} +
        6 * Nat.card {ω : Nonbase c // Nat.card (Fiber c ω.1) = 4} := by
          have h2sum :
              (∑ ω : Nonbase c, if Nat.card (Fiber c ω.1) = 2 then 2 else 0) =
                2 * Nat.card {ω : Nonbase c // Nat.card (Fiber c ω.1) = 2} := by
            rw [Nat.card_eq_fintype_card]
            calc
              (∑ ω : Nonbase c, if Nat.card (Fiber c ω.1) = 2 then 2 else 0) =
                  2 * ∑ ω : Nonbase c,
                  if Nat.card (Fiber c ω.1) = 2 then 1 else 0 := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro ω _
                    by_cases h : Nat.card (Fiber c ω.1) = 2 <;> simp [h]
              _ = 2 *
                  (Finset.univ.filter fun ω : Nonbase c =>
                    Nat.card (Fiber c ω.1) = 2).card := by
                    rw [Finset.sum_boole]
                    simp
              _ = 2 * Fintype.card {ω : Nonbase c //
                    Nat.card (Fiber c ω.1) = 2} := by
                    rw [Fintype.card_subtype]
          have h4sum :
              (∑ ω : Nonbase c, if Nat.card (Fiber c ω.1) = 4 then 6 else 0) =
                6 * Nat.card {ω : Nonbase c // Nat.card (Fiber c ω.1) = 4} := by
            rw [Nat.card_eq_fintype_card]
            calc
              (∑ ω : Nonbase c, if Nat.card (Fiber c ω.1) = 4 then 6 else 0) =
                  6 * ∑ ω : Nonbase c,
                  if Nat.card (Fiber c ω.1) = 4 then 1 else 0 := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro ω _
                    by_cases h : Nat.card (Fiber c ω.1) = 4 <;> simp [h]
              _ = 6 *
                  (Finset.univ.filter fun ω : Nonbase c =>
                    Nat.card (Fiber c ω.1) = 4).card := by
                    rw [Finset.sum_boole]
                    simp
              _ = 6 * Fintype.card {ω : Nonbase c //
                    Nat.card (Fiber c ω.1) = 4} := by
                    rw [Fintype.card_subtype]
          rw [h2sum, h4sum]
    _ = 2 * cosetInvolution_b c.Hhat 2 + 6 * cosetInvolution_b c.Hhat 4 := by
          rw [fiberCard_subtype_eq_coset_b c 2, fiberCard_subtype_eq_coset_b c 4]

/-- Source identity (8): `3·b₄ + b₂ = 6·k²`, from the global commuting-pair
count `12·k²` and the local distribution `2·b₂ + 6·b₄`. -/
public theorem firstCase_klein_identity_eight
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (K : Subgroup G) (b0 b1 b2 b3 b4 : ℕ)
    (hHcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} = 3 + 2 * Nat.card K)
    (hHhatcount : Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} = 3 + 6 * Nat.card K)
    (hJn : ∀ n : ℕ, n ≤ 4 →
      Nat.card {x : G // x ∈ firstCaseJ c n} =
        n * firstCaseBn b0 b1 b2 b3 b4 n)
    (h7 : ∀ (n : ℕ) (y : G) (X : Subgroup G),
      4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
      Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
      Nat.card c.U = Nat.card X ∧ Nat.card X = 3 ∧ n = 4 ∧
        (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
         let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
         (N.subgroupOf D).index = 6)) :
    3 * b4 + b2 = 6 * (Nat.card K) ^ 2 := by
  classical
  have hvan : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0 :=
    firstCase_klein_high_fiber_vanish_of_restrictionSeven hmin c hfirst hklein h7
  have hJ2card : Nat.card {x : G // x ∈ firstCaseJ c 2} =
      2 * cosetInvolution_b c.Hhat 2 := firstCase_J_n_card c 2
  have hJ2b : Nat.card {x : G // x ∈ firstCaseJ c 2} =
      2 * firstCaseBn b0 b1 b2 b3 b4 2 := by
    simpa using hJn 2 (by norm_num)
  have hb2' : 2 * cosetInvolution_b c.Hhat 2 = 2 * b2 := by
    rw [← hJ2card, hJ2b]
    rfl
  have hb2 : cosetInvolution_b c.Hhat 2 = b2 := by omega
  have hJ4card : Nat.card {x : G // x ∈ firstCaseJ c 4} =
      4 * cosetInvolution_b c.Hhat 4 := firstCase_J_n_card c 4
  have hJ4b : Nat.card {x : G // x ∈ firstCaseJ c 4} =
      4 * firstCaseBn b0 b1 b2 b3 b4 4 := by
    simpa using hJn 4 (by norm_num)
  have hb4' : 4 * cosetInvolution_b c.Hhat 4 = 4 * b4 := by
    rw [← hJ4card, hJ4b]
    rfl
  have hb4 : cosetInvolution_b c.Hhat 4 = b4 := by omega
  have htotal : Nat.card
      (Sigma fun s : {s : G // IsInvolution s ∧ s ∈ c.Hhat ∧
          s ∉ twoCoreOf c.Hhat} =>
        {z : G // IsInvolution z ∧ z ∉ c.Hhat ∧ Commute (s : G) z}) =
      12 * (Nat.card K) ^ 2 :=
    firstCase_klein_external_commuting_pair_card
      hmin c hfirst hklein hHcount hHhatcount
  have hsum : Nat.card (Σ ω : Nonbase c, PairFiber c ω.1) =
      2 * cosetInvolution_b c.Hhat 2 + 6 * cosetInvolution_b c.Hhat 4 :=
    sum_pairFiber_cards hmin c hfirst hklein hvan
  obtain ⟨eInc⟩ := firstCase_klein_commuting_pair_coset_incidence hmin c hklein
  have hEq : 12 * (Nat.card K) ^ 2 =
      2 * cosetInvolution_b c.Hhat 2 + 6 * cosetInvolution_b c.Hhat 4 := by
    calc
      12 * (Nat.card K) ^ 2 = Nat.card
          (Sigma fun s : {s : G // IsInvolution s ∧ s ∈ c.Hhat ∧
              s ∉ twoCoreOf c.Hhat} =>
            {z : G // IsInvolution z ∧ z ∉ c.Hhat ∧ Commute (s : G) z}) :=
            htotal.symm
      _ = Nat.card (Σ ω : Nonbase c, PairFiber c ω.1) := Nat.card_congr eInc
      _ = 2 * cosetInvolution_b c.Hhat 2 + 6 * cosetInvolution_b c.Hhat 4 := hsum
  have hEq' : 12 * (Nat.card K) ^ 2 = 2 * b2 + 6 * b4 := by
    rw [hb2, hb4] at hEq
    exact hEq
  omega

end CFSG.GorensteinWalter
