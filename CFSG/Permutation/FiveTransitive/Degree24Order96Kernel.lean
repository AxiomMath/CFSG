module

public import CFSG.Permutation.FiveTransitive.Degree24Order96Normalizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem conj_eq_or_eq_inv_of_mem_normalizer_zpowers_order_three
    {T : Type} [Group T] [Fintype T]
    (u t : T)
    (huOrder : orderOf u = 3)
    (ht : t ∈ Subgroup.normalizer
      (Subgroup.zpowers u : Set T)) :
    MulAut.conj t u = u ∨
      MulAut.conj t u = u⁻¹ := by
  classical
  let R : Subgroup T := Subgroup.zpowers u
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, huOrder]
  have hconjMem : MulAut.conj t u ∈ R := by
    change t * u * t⁻¹ ∈ R
    exact
      (Subgroup.mem_normalizer_iff.mp ht u).mp
        (Subgroup.mem_zpowers u)
  let uR : R :=
    ⟨u, Subgroup.mem_zpowers u⟩
  let vR : R :=
    ⟨MulAut.conj t u, hconjMem⟩
  have huROrder : orderOf uR = 3 := by
    calc
      orderOf uR = orderOf u := (Subgroup.orderOf_coe _).symm
      _ = 3 := huOrder
  have hvROrder : orderOf vR = 3 := by
    calc
      orderOf vR = orderOf (MulAut.conj t u) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf u := (MulAut.conj t).orderOf_eq _
      _ = 3 := huOrder
  rcases
      eq_one_or_eq_or_eq_inv_of_card_eq_three
        R hRcard uR huROrder vR with
    hvOne | hvSame | hvInv
  · rw [hvOne, orderOf_one] at hvROrder
    norm_num at hvROrder
  · exact Or.inl (congrArg Subtype.val hvSame)
  · exact Or.inr (congrArg Subtype.val hvInv)

theorem eq_of_sameCycle_of_fixed_of_inverts_order_three
    {X : Type} [Fintype X] [DecidableEq X]
    (u t : Equiv.Perm X)
    (huOrder : orderOf u = 3)
    (hinverts : MulAut.conj t u = u⁻¹)
    {x y : X}
    (hxSupport : x ∈ u.support)
    (hySupport : y ∈ u.support)
    (htx : t x = x)
    (hty : t y = y)
    (hxy : u.SameCycle x y) :
    x = y := by
  classical
  have hinverts' : t * u * t⁻¹ = u⁻¹ := hinverts
  have htu : t * u = u⁻¹ * t :=
    mul_inv_eq_iff_eq_mul.mp hinverts'
  have huCube : u ^ 3 = 1 := by
    rw [← huOrder]
    exact pow_orderOf_eq_one u
  have hnotImage
      (a b : X)
      (haSupport : a ∈ u.support)
      (hta : t a = a)
      (htb : t b = b)
      (hab : u a = b) :
      False := by
    have htuPoint :=
      congrArg (fun q : Equiv.Perm X => q a) htu
    have hub : u⁻¹ a = b := by
      simpa only [Equiv.Perm.mul_apply, hta, htb,
        hab] using htuPoint.symm
    have huEq : u a = u⁻¹ a := hab.trans hub.symm
    have huSquareFix : (u ^ 2) a = a := by
      have happly :=
        congrArg (fun z : X => u z) huEq
      calc
        (u ^ 2) a = u (u a) := by
          rfl
        _ = u (u⁻¹ a) := happly
        _ = a := u.apply_symm_apply a
    have huSquareInv : (u ^ 2)⁻¹ = u := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [pow_succ] using huCube
    have huFix : u a = a := by
      have hinvFix :=
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
          huSquareFix (-1)
      change (u ^ 2)⁻¹ a = a at hinvFix
      rwa [huSquareInv] at hinvFix
    exact Equiv.Perm.mem_support.mp haSupport huFix
  obtain ⟨i, hi⟩ := hxy
  let R : Subgroup (Equiv.Perm X) :=
    Subgroup.zpowers u
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, huOrder]
  let uR : R :=
    ⟨u, Subgroup.mem_zpowers u⟩
  have huROrder : orderOf uR = 3 := by
    calc
      orderOf uR = orderOf u :=
        (Subgroup.orderOf_coe _).symm
      _ = 3 := huOrder
  rcases
      eq_one_or_eq_or_eq_inv_of_card_eq_three
        R hRcard uR huROrder (uR ^ i) with
    hpowOne | hpowU | hpowInv
  · have hpowOne' := congrArg Subtype.val hpowOne
    rw [Subgroup.coe_zpow] at hpowOne'
    rw [hpowOne'] at hi
    exact hi
  · have hpowU' := congrArg Subtype.val hpowU
    rw [Subgroup.coe_zpow] at hpowU'
    rw [hpowU'] at hi
    exact (hnotImage x y hxSupport htx hty hi).elim
  · have hpowInv' := congrArg Subtype.val hpowInv
    rw [Subgroup.coe_zpow] at hpowInv'
    rw [hpowInv'] at hi
    have huy : u y = x := by
      calc
        u y = u (u⁻¹ x) :=
          congrArg (fun z : X => u z) hi.symm
        _ = x := u.apply_symm_apply x
    exact (hnotImage y x hySupport hty htx huy).elim

theorem twelve_le_support_of_inverts_order_three_of_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (u t : Equiv.Perm X)
    (huOrder : orderOf u = 3)
    (huSupport : u.support.card = 18)
    (hinverts : MulAut.conj t u = u⁻¹)
    (hfix : ∀ x : X, u x = x → t x = x) :
    12 ≤ t.support.card := by
  classical
  have htSupportSubset : t.support ⊆ u.support := by
    intro x hxt
    by_contra hxu
    exact Equiv.Perm.mem_support.mp hxt
      (hfix x (Equiv.Perm.notMem_support.mp hxu))
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order
      (by rw [huOrder]; norm_num)
  have hsum := u.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, huOrder, huSupport] at hsum
  have hmSix : m + 1 = 6 := by
    omega
  have hcycleFactorCard :
      Fintype.card u.cycleFactorsFinset = 6 := by
    have hcard :=
      congrArg Multiset.card
        (Equiv.Perm.cycleType_def u)
    rw [hm, Multiset.card_replicate, hmSix] at hcard
    simpa using hcard.symm
  let B : Type := ↥(u.support \ t.support)
  let cycleMap :
      B → u.cycleFactorsFinset :=
    fun x =>
      ⟨u.cycleOf x.1,
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
          (Finset.mem_sdiff.mp x.2).1⟩
  have hcycleMapInjective :
      Function.Injective cycleMap := by
    intro x y hxy
    apply Subtype.ext
    apply
      eq_of_sameCycle_of_fixed_of_inverts_order_three
        u t huOrder hinverts
    · exact (Finset.mem_sdiff.mp x.2).1
    · exact (Finset.mem_sdiff.mp y.2).1
    · exact Equiv.Perm.notMem_support.mp
        (Finset.mem_sdiff.mp x.2).2
    · exact Equiv.Perm.notMem_support.mp
        (Finset.mem_sdiff.mp y.2).2
    · apply
        (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
          (Finset.mem_sdiff.mp x.2).1
          (Finset.mem_sdiff.mp y.2).1).mpr
      exact congrArg Subtype.val hxy
  have hBcardLe :
      Fintype.card B ≤
        Fintype.card u.cycleFactorsFinset :=
    Fintype.card_le_of_injective cycleMap
      hcycleMapInjective
  have hdiffLe :
      (u.support \ t.support).card ≤ 6 := by
    dsimp only [B] at hBcardLe
    rw [Fintype.card_coe, hcycleFactorCard] at hBcardLe
    exact hBcardLe
  have hcardPartition :=
    Finset.card_sdiff_add_card_eq_card htSupportSubset
  rw [huSupport] at hcardPartition
  omega

theorem order96_cyclic_orderThree_fixed_action_kernel_data
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96) :
    let U := OrderPrimeSupportElements X P 3 18
    ∃ u : U,
      let R : Subgroup P := Subgroup.zpowers (u.1 : P)
      let F : Set X := MulAction.fixedPoints R X
      let N : Subgroup P := Subgroup.normalizer (R : Set P)
      let ρ : N →* Equiv.Perm F := MulAction.toPermHom N F
      Nat.card U = 226688 ∧
        Nat.card N = 4320 ∧
        ρ.range = ⊤ ∧
        Nat.card ρ.ker = 6 ∧
        ∃ t : ρ.ker,
          orderOf t = 2 ∧
            ∀ x : F, ((t : ρ.ker) : N) • x = x := by
  classical
  dsimp
  obtain ⟨u, hUcard, hNcard, hRange⟩ :=
    order96_cyclic_orderThree_normalizer_extremal_data
      X P hcard h5 hnotAlt s hs hHcard
  let R : Subgroup P := Subgroup.zpowers (u.1 : P)
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P := Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F := MulAction.toPermHom N F
  have hFcard : Nat.card F = 6 := by
    obtain ⟨hFcard, _⟩ :=
      order96_cyclic_orderThree_normalizer_fixed_action
        X P hcard h5 s hs hHcard u
    exact hFcard
  have hRangeCard : Nat.card ρ.range = 720 := by
    rw [show ρ.range = ⊤ by
      simpa only [R, F, N, ρ] using hRange]
    rw [Subgroup.card_top, Nat.card_perm, hFcard]
    norm_num
  have hKerProduct :
      Nat.card ρ.ker * Nat.card ρ.range = Nat.card N := by
    have hproduct := ρ.ker.card_mul_index
    rw [Subgroup.index_ker] at hproduct
    exact hproduct
  have hKerCard : Nat.card ρ.ker = 6 := by
    rw [hRangeCard, show Nat.card N = 4320 by
      simpa only [R, F, N] using hNcard] at hKerProduct
    omega
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨t, htOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := ρ.ker) 2 (by
      rw [hKerCard]
      norm_num)
  refine ⟨u, hUcard, ?_, ?_, hKerCard, t, htOrder, ?_⟩
  · simpa only [R, F, N] using hNcard
  · simpa only [R, F, N, ρ] using hRange
  · intro x
    have htKer : ρ (t : N) = 1 := t.prop
    change (ρ (t : N)) x = x
    rw [htKer]
    rfl

end FiveTransitive.Degree24

end CFSG
