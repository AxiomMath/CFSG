module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer
public import CFSG.Permutation.FiveTransitive.SymmetricCommutator
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.TwoPrimeCycleCentralizer

open MulAction FixedNormalizerAction Degree28ThirteenCentralizer

theorem double_cycle_centralizer_card
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : ℕ) (hcard : Fintype.card Y = 2 * p)
    {g : Equiv.Perm Y} (htype : g.cycleType = {p,p}) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm Y))) = 2 * p ^ 2 := by
  rw [Equiv.Perm.nat_card_centralizer,htype,hcard]
  norm_num [Nat.two_mul,Nat.mul_two,pow_two]

private theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hf : f ≤ 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (hn : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (hcycleType : (u : Equiv.Perm X).cycleType = {p,p}) :
    Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set P)) ∣ 2 * p ^ 2 := by
  classical
  let g : Equiv.Perm X := u
  have hgsupport : g.support.card = 2 * p := by
    rw [← g.sum_cycleType, hcycleType]
    simp [Nat.two_mul]
  let C : Subgroup P :=
    Subgroup.centralizer (Subgroup.zpowers u : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapInjective :
      Function.Injective baseMap := by
    intro a b hab
    exact C.subtype_injective
      (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((q.prop u (Subgroup.mem_zpowers u)).symm)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hsupportMapMem :
      ∀ q : C, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap q (g x.1) =
      g (baseMap q x.1)
    have hcomm : Commute (baseMap q) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)))
      hsupportMapMem
  have hsupportCentMapInjective :
      Function.Injective supportCentMap := by
    intro a b hab
    by_contra habNe
    let w : C := a * b⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      exact habNe (mul_inv_eq_one.mp hw)
    have hwSupportCentOne :
        supportCentMap w = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hwSupportOne :
        supportMap w = 1 :=
      congrArg Subtype.val hwSupportCentOne
    let wP : P := w
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwSupportSubset :
        wPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      exact
        Equiv.Perm.mem_support.mp hx
          (hwFixSupport x hxg)
    have hwSupportCard :
        wPerm.support.card ≤ f := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ = f := by
          rw [Finset.card_compl, hcard, hgsupport]
          omega
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    have hm := HighDegreeManningSupport.degree_le_two_mul_support
      P hn h5 hnotAlt wP.prop hwPermNe
    change Fintype.card X ≤ 2 * wPerm.support.card at hm
    rw [hcard] at hm
    omega
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportTypeCard :
      Fintype.card g.support = 2 * p := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 2 * p ^ 2 := by
    exact double_cycle_centralizer_card p hsupportTypeCard
      (hgSupportCycleType.trans hcycleType)
  have hCdvdSupport : Nat.card C ∣ 2 * p ^ 2 := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  exact hCdvdSupport

theorem three_dvd_centralizer_card
    {G F : Type*} [Group G] [Finite G] [Finite F]
    (Q : Subgroup G) [IsCyclic Q]
    (k : ℕ) (hk : k = 3 ∨ k = 4) (hF : Nat.card F = k)
    (rho : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hrho : Function.Surjective rho) :
    3 ∣ Nat.card (Subgroup.centralizer (Q : Set G)) := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let D := C.subgroupOf N
  have hAlt := SymmetricCommutator.alternating_le_centralizer_image Q rho hrho
  have hdiv : Nat.card (alternatingGroup F) ∣ Nat.card D :=
    (Subgroup.card_dvd_of_le hAlt).trans (D.card_map_dvd rho)
  have hD : Nat.card D = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (Q : Set G))).toEquiv
  have hthree : 3 ∣ Nat.card (alternatingGroup F) := by
    rw [nat_card_alternatingGroup,hF]
    rcases hk with rfl | rfl <;> norm_num [Nat.factorial]
  rw [hD] at hdiv
  exact hthree.trans hdiv

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (hcycleType : (u : Equiv.Perm X).cycleType = {p,p})
    (hfixed : Nat.card (Fixed (X := X) (Subgroup.zpowers u)) = f)
    (himage : Image (X := X) (Subgroup.zpowers u) = ⊤) : False := by
  let Q := Subgroup.zpowers u
  let rho := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hrho : Function.Surjective rho := MonoidHom.range_eq_top.mp himage
  have hthree := three_dvd_centralizer_card Q f hf hfixed rho hrho
  have hd := hthree.trans (centralizer_card_dvd p f (by omega) P hcard
    (by omega) h5 hnotAlt u hcycleType)
  have hpnot : ¬ 3 ∣ p := by
    intro h
    have hh := (Nat.dvd_prime hp).mp h
    omega
  rcases Nat.prime_three.dvd_mul.mp hd with h | h
  · norm_num at h
  · exact hpnot (Nat.prime_three.dvd_of_dvd_pow h)

end FiveTransitive.TwoPrimeCycleCentralizer

end CFSG
