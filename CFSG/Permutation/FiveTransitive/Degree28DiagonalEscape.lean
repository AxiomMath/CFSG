module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace FiveTransitive.Degree28DiagonalEscape

private def centralizerSingletonEquiv
    {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃*
      Subgroup.centralizer ({e x} : Set K) where
  toFun z := ⟨e z, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz :=
      Subgroup.mem_centralizer_singleton_iff.mp z.prop
    simpa using congrArg e hz⟩
  invFun z := ⟨e.symm z, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz :=
      Subgroup.mem_centralizer_singleton_iff.mp z.prop
    simpa using congrArg e.symm hz⟩
  left_inv z := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

private theorem nat_card_centralizer_eq_of_mulEquiv
    {G K : Type*} [Group G] [Group K] [Finite G] [Finite K]
    (e : G ≃* K) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set K)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) :=
  Nat.card_congr (centralizerSingletonEquiv e x).symm.toEquiv

private def alternatingCentralizerEquivSignKernel
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : alternatingGroup X) :
    Subgroup.centralizer ({g} : Set (alternatingGroup X)) ≃*
      (Equiv.Perm.sign.domRestrict
        (Subgroup.centralizer ({(g : Equiv.Perm X)} :
          Set (Equiv.Perm X)))).ker where
  toFun z := by
    let c : Subgroup.centralizer
        ({(g : Equiv.Perm X)} : Set (Equiv.Perm X)) :=
      ⟨(z : alternatingGroup X), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp z.prop)⟩
    refine ⟨c, ?_⟩
    rw [MonoidHom.mem_ker]
    simpa [c] using Equiv.Perm.mem_alternatingGroup.mp z.1.2
  invFun z := by
    let a : alternatingGroup X :=
      ⟨(z.1 : Equiv.Perm X), by
        rw [Equiv.Perm.mem_alternatingGroup]
        exact MonoidHom.mem_ker.mp z.2⟩
    refine ⟨a, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp z.1.2
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

private theorem two_mul_nat_card_alternating_centralizer
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : alternatingGroup X)
    (hodd :
      ¬Subgroup.centralizer
          ({(g : Equiv.Perm X)} : Set (Equiv.Perm X)) ≤
        alternatingGroup X) :
    2 * Nat.card
          (Subgroup.centralizer
            ({g} : Set (alternatingGroup X))) =
      Nat.card
        (Subgroup.centralizer
          ({(g : Equiv.Perm X)} : Set (Equiv.Perm X))) := by
  let C := Subgroup.centralizer
    ({(g : Equiv.Perm X)} : Set (Equiv.Perm X))
  let f : C →* ℤˣ := Equiv.Perm.sign.domRestrict C
  obtain ⟨c, hcC, hcOdd⟩ := SetLike.not_le_iff_exists.mp hodd
  have hcSignNe : Equiv.Perm.sign c ≠ 1 := by
    intro hc
    apply hcOdd
    exact Equiv.Perm.mem_alternatingGroup.mpr hc
  have hcSignNeg : Equiv.Perm.sign c = (-1 : ℤˣ) :=
    (Int.units_eq_one_or (Equiv.Perm.sign c)).resolve_left hcSignNe
  have hfSurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with hu | hu
    · refine ⟨1, ?_⟩
      simpa [hu]
    · refine ⟨⟨c, hcC⟩, ?_⟩
      simpa [f, hu] using hcSignNeg
  have hindex : f.ker.index = 2 := by
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hfSurj]
    norm_num [Nat.card_eq_fintype_card]
  have hkernelCard :
      Nat.card f.ker =
        Nat.card
          (Subgroup.centralizer
            ({g} : Set (alternatingGroup X))) := by
    exact Nat.card_congr
      (alternatingCentralizerEquivSignKernel g).symm.toEquiv
  have hindexCard := f.ker.index_mul_card
  rw [hindex, hkernelCard] at hindexCard
  simpa only [C, Nat.mul_comm] using hindexCard

private theorem nat_card_perm_centralizer_threeCycle_degree_seven
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 7)
    {g : Equiv.Perm X} (hg : g.IsThreeCycle) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) = 72 := by
  rw [Equiv.Perm.nat_card_centralizer, hg.cycleType, hX]
  norm_num

private theorem nat_card_alternating_centralizer_threeCycle_degree_seven
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 7)
    (g : alternatingGroup X)
    (hg : (g : Equiv.Perm X).IsThreeCycle) :
    Nat.card
      (Subgroup.centralizer ({g} : Set (alternatingGroup X))) = 36 := by
  have hodd :
      ¬Subgroup.centralizer
          ({(g : Equiv.Perm X)} : Set (Equiv.Perm X)) ≤
        alternatingGroup X := by
    intro hle
    have hcard :=
      Equiv.Perm.card_le_of_centralizer_le_alternating hle
    rw [hg.cycleType, hX] at hcard
    norm_num at hcard
  have hhalf := two_mul_nat_card_alternating_centralizer g hodd
  rw [nat_card_perm_centralizer_threeCycle_degree_seven hX hg] at hhalf
  omega

private theorem cycleType_eq_two_threeCycles_of_order_three_of_not_threeCycle
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 7)
    {g : Equiv.Perm X} (horder : orderOf g = 3)
    (hnot : ¬g.IsThreeCycle) :
    g.cycleType = {3, 3} := by
  have hprime : Nat.Prime (orderOf g) := by
    rw [horder]
    norm_num
  obtain ⟨n, hn⟩ :=
    Equiv.Perm.cycleType_prime_order hprime
  rw [horder] at hn
  have hle := g.sum_cycleType_le
  rw [hn, hX] at hle
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hle
  have hnLe : n ≤ 1 := by omega
  interval_cases n
  · exfalso
    apply hnot
    rw [← card_support_eq_three_iff, ← g.sum_cycleType, hn]
    norm_num
  · simpa using hn

private theorem nat_card_alternating_centralizer_nonThreeCycle_order_three_degree_seven
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 7)
    (g : alternatingGroup X)
    (horder : orderOf g = 3)
    (hnot : ¬(g : Equiv.Perm X).IsThreeCycle) :
    Nat.card
      (Subgroup.centralizer ({g} : Set (alternatingGroup X))) = 9 := by
  have horderPerm : orderOf (g : Equiv.Perm X) = 3 := by
    simpa using horder
  have hcycle : (g : Equiv.Perm X).cycleType = {3, 3} :=
    cycleType_eq_two_threeCycles_of_order_three_of_not_threeCycle
      hX horderPerm hnot
  have hfull :
      Nat.card
        (Subgroup.centralizer
          ({(g : Equiv.Perm X)} : Set (Equiv.Perm X))) = 18 := by
    rw [Equiv.Perm.nat_card_centralizer, hcycle, hX]
    norm_num
  have hodd :
      ¬Subgroup.centralizer
          ({(g : Equiv.Perm X)} : Set (Equiv.Perm X)) ≤
        alternatingGroup X := by
    intro hle
    have hcount :=
      Equiv.Perm.count_le_one_of_centralizer_le_alternating hle 3
    rw [hcycle] at hcount
    norm_num at hcount
  have hhalf := two_mul_nat_card_alternating_centralizer g hodd
  rw [hfull] at hhalf
  omega

private theorem alternating_mulEquiv_preserves_threeCycle_degree_seven
    {X Y : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (hX : Fintype.card X = 7)
    (hY : Fintype.card Y = 7)
    (e : alternatingGroup X ≃* alternatingGroup Y)
    (g : alternatingGroup X)
    (hg : (g : Equiv.Perm X).IsThreeCycle) :
    ((e g : alternatingGroup Y) : Equiv.Perm Y).IsThreeCycle := by
  by_contra hnot
  have horder : orderOf (e g) = 3 := by
    calc
      orderOf (e g) = orderOf g := e.orderOf_eq g
      _ = orderOf (g : Equiv.Perm X) :=
        (Subgroup.orderOf_coe g).symm
      _ = 3 := hg.orderOf
  have hcardSource :=
    nat_card_alternating_centralizer_threeCycle_degree_seven hX g hg
  have hcardTarget :=
    nat_card_alternating_centralizer_nonThreeCycle_order_three_degree_seven
      hY (e g) horder hnot
  have hcardEq := nat_card_centralizer_eq_of_mulEquiv e g
  omega

private theorem simple_equal_card_lift_or_diagonal
    (L A B : Type*) [Group L] [Group A] [Group B]
    [Finite L] [Finite A] [Finite B] [IsSimpleGroup A]
    (f : L →* A) (t : L →* B)
    (hf : Function.Surjective f)
    (ht : Function.Surjective t)
    (hcard : Nat.card A = Nat.card B) :
    (∀ a : A, ∃ l : L, f l = a ∧ t l = 1) ∨
      ∃ e : B ≃* A, ∀ l : L, e (t l) = f l := by
  let M : Subgroup A := t.ker.map f
  letI : M.Normal :=
    Subgroup.Normal.map (inferInstance : t.ker.Normal) f hf
  rcases (inferInstance : M.Normal).eq_bot_or_eq_top with hM | hM
  · right
    have hker : t.ker ≤ f.ker := by
      intro l hl
      have hflM : f l ∈ M := by
        exact ⟨l, hl, rfl⟩
      rw [hM] at hflM
      exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hflM)
    let eHom : B →* A := t.liftOfSurjective ht ⟨f, hker⟩
    have heApply (l : L) : eHom (t l) = f l := by
      simp [eHom]
    have heSurj : Function.Surjective eHom := by
      intro a
      obtain ⟨l, rfl⟩ := hf a
      exact ⟨t l, heApply l⟩
    have heBij : Function.Bijective eHom :=
      heSurj.bijective_of_nat_card_le (by omega)
    let e : B ≃* A := MulEquiv.ofBijective eHom heBij
    exact ⟨e, fun l => heApply l⟩
  · left
    intro a
    have haM : a ∈ M := by
      rw [hM]
      exact Subgroup.mem_top a
    obtain ⟨l, hlt, hlf⟩ := haM
    exact ⟨l, hlf, MonoidHom.mem_ker.mp hlt⟩

theorem exists_lift_threeCycle_both_of_surjective_alternating
    {F C : Type*}
    [Fintype F] [DecidableEq F]
    [Fintype C] [DecidableEq C]
    (hF : Fintype.card F = 7)
    (hC : Fintype.card C = 7)
    (L : Type*) [Group L] [Finite L]
    (f : L →* alternatingGroup F)
    (t : L →* alternatingGroup C)
    (hf : Function.Surjective f)
    (ht : Function.Surjective t) :
    ∃ l : L,
      ((f l : alternatingGroup F) : Equiv.Perm F).IsThreeCycle ∧
      ((t l : alternatingGroup C) : Equiv.Perm C).IsThreeCycle := by
  classical
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card, hF]
      norm_num)
  letI : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hF]; norm_num)
  letI : Nontrivial C :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hC]; norm_num)
  have hcard :
      Nat.card (alternatingGroup F) =
        Nat.card (alternatingGroup C) := by
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hF, hC]
  let eF : Fin 3 ↪ F :=
    Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (by
        rw [Fintype.card_fin, hF]
        norm_num))
  let eC : Fin 3 ↪ C :=
    Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (by
        rw [Fintype.card_fin, hC]
        norm_num))
  let qPerm : Equiv.Perm F :=
    Equiv.swap (eF 0) (eF 1) * Equiv.swap (eF 0) (eF 2)
  let bPerm : Equiv.Perm C :=
    Equiv.swap (eC 0) (eC 1) * Equiv.swap (eC 0) (eC 2)
  have heF01 : eF 0 ≠ eF 1 := eF.injective.ne (by decide)
  have heF02 : eF 0 ≠ eF 2 := eF.injective.ne (by decide)
  have heF12 : eF 1 ≠ eF 2 := eF.injective.ne (by decide)
  have heC01 : eC 0 ≠ eC 1 := eC.injective.ne (by decide)
  have heC02 : eC 0 ≠ eC 2 := eC.injective.ne (by decide)
  have heC12 : eC 1 ≠ eC 2 := eC.injective.ne (by decide)
  have hqThree : qPerm.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      heF01 heF02 heF12
  have hbThree : bPerm.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      heC01 heC02 heC12
  let q : alternatingGroup F :=
    ⟨qPerm, hqThree.mem_alternatingGroup⟩
  let b : alternatingGroup C :=
    ⟨bPerm, hbThree.mem_alternatingGroup⟩
  rcases simple_equal_card_lift_or_diagonal
      L (alternatingGroup F) (alternatingGroup C)
      f t hf ht hcard with hproduct | hdiagonal
  · obtain ⟨v, hv⟩ := ht b
    obtain ⟨w, hfw, htw⟩ :=
      hproduct (q * (f v)⁻¹)
    refine ⟨w * v, ?_, ?_⟩
    · have hfv : f (w * v) = q := by
        rw [map_mul, hfw]
        simp
      simpa only [hfv, q] using hqThree
    · have htv : t (w * v) = b := by
        rw [map_mul, htw, one_mul, hv]
      simpa only [htv, b] using hbThree
  · obtain ⟨e, he⟩ := hdiagonal
    obtain ⟨v, hv⟩ := ht b
    refine ⟨v, ?_, ?_⟩
    · have hev : e b = f v := by
        simpa only [hv] using he v
      have hebThree :
          ((e b : alternatingGroup F) : Equiv.Perm F).IsThreeCycle :=
        alternating_mulEquiv_preserves_threeCycle_degree_seven
          hC hF e b (by simpa only [b] using hbThree)
      simpa only [← hev] using hebThree
    · simpa only [hv, b] using hbThree

theorem degree28_fixed_points_exceed_cycle_count
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    {g : Equiv.Perm X}
    (horder : orderOf g = 3)
    (hsupport : g.support.card ≤ 18) :
    g.cycleType.card < Fintype.card (Function.fixedPoints g) := by
  have hprime : Nat.Prime (orderOf g) := by
    rw [horder]
    norm_num
  obtain ⟨r, hr⟩ := Equiv.Perm.cycleType_prime_order hprime
  have hcycleType :
      g.cycleType = Multiset.replicate g.cycleType.card 3 := by
    rw [hr, horder]
    simp
  have hsum : g.cycleType.sum = 3 * g.cycleType.card := by
    rw [hcycleType]
    simp [Nat.mul_comm]
  have hsupportEq : g.support.card = 3 * g.cycleType.card := by
    rw [← g.sum_cycleType, hsum]
  have hfixed :
      Fintype.card (Function.fixedPoints g) = 28 - g.support.card := by
    rw [Equiv.Perm.card_fixedPoints, g.sum_cycleType, hX]
  omega

end FiveTransitive.Degree28DiagonalEscape

end CFSG
