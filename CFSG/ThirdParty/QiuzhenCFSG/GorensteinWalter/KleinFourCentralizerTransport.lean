module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Complement
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transporting the Klein-four centralizer argument under conjugation

The abstract no-Klein-four dihedral endpoint is transported along an
inner automorphism to a conjugate splitting/nonsplitting torus.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

public theorem isKleinFour_map_mulEquiv
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) (hV : IsKleinFour V) (e : G ≃* G) :
    IsKleinFour (V.map e.toMonoidHom) := by
  let eV : V ≃* V.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective V e.toMonoidHom e.injective
  exact {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hV.exponent_two
  }

public theorem isKleinFour_map_mulEquiv_cross
    {G H : Type*} [Group G] [Group H]
    (V : Subgroup G) (hV : IsKleinFour V) (e : G ≃* H) :
    IsKleinFour (V.map e.toMonoidHom) := by
  let eV : V ≃* V.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective V e.toMonoidHom e.injective
  exact {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hV.exponent_two
  }

public theorem centralizer_map_le_of_conj
    {G : Type u} [Group G]
    (A V : Subgroup G) (g : G)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    (V.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      Subgroup.centralizer
        ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Subgroup.mem_map.mp hy with ⟨v, hv, hvy⟩
  rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, hqa⟩
  rw [← hvy, ← hqa]
  change (MulAut.conj g⁻¹) a0 * (MulAut.conj g⁻¹) v =
    (MulAut.conj g⁻¹) v * (MulAut.conj g⁻¹) a0
  have hvcomm : v * a0 = a0 * v :=
    ((Subgroup.mem_centralizer_iff.mp (hVleC hv)) a0 ha0).symm
  calc
    (MulAut.conj g⁻¹) a0 * (MulAut.conj g⁻¹) v =
        (MulAut.conj g⁻¹) (a0 * v) := by
          simp only [MulAut.conj_apply]
          group
    _ = (MulAut.conj g⁻¹) (v * a0) := by rw [hvcomm]
    _ = (MulAut.conj g⁻¹) v * (MulAut.conj g⁻¹) a0 := by
          simp only [MulAut.conj_apply]
          group

public theorem centralizer_map_le_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A V : Subgroup G) (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    V.map e.toMonoidHom ≤
      Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup H) : Set H) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Subgroup.mem_map.mp hy with ⟨v, hv, hvy⟩
  rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, hqa⟩
  rw [← hvy, ← hqa]
  have hvcomm : a0 * v = v * a0 :=
    (Subgroup.mem_centralizer_iff.mp (hVleC hv)) a0 ha0
  simpa [e.map_mul] using congrArg e hvcomm

public theorem no_kleinFour_centralizes_odd_cyclic_of_conjugate_torus
    {G : Type u} [Group G] [Finite G]
    (A V : Subgroup G) (g : G) (U : Subgroup G) (w : G)
    (hAne : A ≠ ⊥)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hAt : A ≤ U.map (MulAut.conj g).toMonoidHom)
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer
      ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) =
        U ⊔ Subgroup.zpowers w)
    (hVK : IsKleinFour V) (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  let A0 : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom
  let V0 : Subgroup G := V.map (MulAut.conj g⁻¹).toMonoidHom
  let eA : A ≃* A0 :=
    Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective
  have hA0ne : A0 ≠ ⊥ := by
    intro hbot
    have hcardA : Nat.card A = Nat.card A0 := Nat.card_congr eA.toEquiv
    have hone : Nat.card A = 1 := by
      rw [hcardA, hbot]
      simp
    have hgt : 1 < Nat.card A :=
      (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
    omega
  have hA0rot : A0 ≤ U := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haT : a ∈ U.map (MulAut.conj g).toMonoidHom := hAt ha
    rcases Subgroup.mem_map.mp haT with ⟨u, hu, hua⟩
    rw [← hua]
    simpa [MulAut.conj_apply, mul_assoc, inv_mul_cancel] using hu
  have hA0odd : ∀ x : G, x ∈ A0 → Odd (orderOf x) := by
    intro x hx
    obtain ⟨a, ha_eq⟩ := eA.surjective ⟨x, hx⟩
    have hax : (MulAut.conj g⁻¹) (a : G) = x :=
      congrArg Subtype.val ha_eq
    have hordA : Odd (orderOf (a : G)) := hAodd (a : G) a.2
    have hsc : SemiconjBy (g⁻¹) (a : G) x := by
      change g⁻¹ * (a : G) = x * g⁻¹
      rw [← hax]
      simp [MulAut.conj_apply, mul_assoc]
    have hord_eq : orderOf x = orderOf (a : G) :=
      (SemiconjBy.orderOf_eq (g⁻¹) (x := (a : G)) (y := x) hsc).symm
    simpa [hord_eq] using hordA
  have hV0K : IsKleinFour V0 :=
    isKleinFour_map_mulEquiv V hVK (MulAut.conj g⁻¹)
  have hV0leC : V0 ≤ Subgroup.centralizer (A0 : Set G) := by
    simpa [A0, V0] using centralizer_map_le_of_conj A V g hVleC
  exact no_kleinFour_centralizes_odd_rotation_of_normalizer
    U A0 V0 w hA0ne hA0rot hA0odd hUcyc hwU hwsq hwinv hN hV0K hV0leC

public theorem center_eq_bot_perm_fin4 :
    Subgroup.center (Equiv.Perm (Fin 4)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  exact (by
    decide +kernel :
      ∀ x : Equiv.Perm (Fin 4),
        x ∈ Subgroup.center (Equiv.Perm (Fin 4)) → x = 1)

public theorem center_eq_bot_alternatingGroup_four :
    Subgroup.center (alternatingGroup (Fin 4)) = ⊥ := by
  exact alternatingGroup.center_eq_bot (by norm_num)

public theorem center_eq_bot_alternatingGroup_five :
    Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
  exact alternatingGroup.center_eq_bot (by norm_num)

public theorem no_kleinFour_of_isPGroup_odd
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) (hVK : IsKleinFour V)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hVp : IsPGroup p V) :
    False := by
  rcases hVp.exists_card_eq with ⟨n, hn⟩
  have h4 : Nat.card V = 4 := hVK.card_four
  rw [h4] at hn
  have hp_dvd4 : p ∣ 4 := by
    cases n with
    | zero => simp at hn
    | succ n =>
        exact ⟨p ^ n, by
          rw [hn, pow_succ, Nat.mul_comm]⟩
  have hp_le4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp_dvd4
  have hp_ge2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  interval_cases p <;> norm_num at *

public theorem pGroup_le_kernel_of_complement
    {M : Type u} [Group M] [Finite M]
    (N A C : Subgroup M)
    (hNnormal : N.Normal)
    (hcomp : N.IsComplement' C)
    {p : ℕ} [Fact p.Prime] (hAp : IsPGroup p A)
    (hcop : Nat.Coprime p (Nat.card C)) :
    A ≤ N := by
  let : N.Normal := hNnormal
  intro a ha
  let q : M →* M ⧸ N := QuotientGroup.mk' N
  rcases hAp.exists_card_eq with ⟨k, hk⟩
  have horder_dvd : orderOf a ∣ Nat.card A := by
    have hzle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
    have hcard : Nat.card (Subgroup.zpowers a) ∣ Nat.card A :=
      Subgroup.card_dvd_of_le hzle
    rw [show orderOf a = Nat.card (Subgroup.zpowers a) by
      exact (Nat.card_zpowers a).symm]
    exact hcard
  rw [hk] at horder_dvd
  have hcop_pow : Nat.Coprime (p ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left k hcop
  have hcop_ord : Nat.Coprime (orderOf a) (Nat.card C) :=
    hcop_pow.of_dvd_left horder_dvd
  let eQ : M ⧸ N ≃* C := hcomp.symm.QuotientMulEquiv
  have hcard : Nat.card (M ⧸ N) = Nat.card C := Nat.card_congr eQ.toEquiv
  have hqord_dvd : orderOf (q a) ∣ Nat.card (M ⧸ N) :=
    orderOf_dvd_natCard (q a)
  have hqord_dvd_C : orderOf (q a) ∣ Nat.card C := by
    simpa [hcard] using hqord_dvd
  have hmap_ord : orderOf (q a) ∣ orderOf a := orderOf_map_dvd q a
  have hqord1 : orderOf (q a) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_ord hmap_ord hqord_dvd_C
  have hqa_one : q a = 1 := orderOf_eq_one_iff.mp hqord1
  exact (QuotientGroup.eq_one_iff (N := N) a).mp hqa_one

/-- In a complement `N ⋊ C` with `p` coprime to `|C|`, a Klein four that
centralizes a nontrivial `p`-subgroup and lies inside the kernel `N` is
impossible. -/
public theorem no_kleinFour_of_pGroup_subgroup
    {M : Type u} [Group M] [Finite M]
    (N V : Subgroup M)
    {p : ℕ} [Fact p.Prime]
    (hNp : IsPGroup p N)
    (hpodd : Odd p)
    (hVleN : V ≤ N) (hVK : IsKleinFour V) :
    False := by
  let VN : Subgroup N := V.subgroupOf N
  have hVNp : IsPGroup p VN := hNp.to_subgroup VN
  have hVp : IsPGroup p V :=
    hVNp.of_equiv (Subgroup.subgroupOfEquivOfLe hVleN)
  exact no_kleinFour_of_isPGroup_odd V hVK hpodd hVp

public theorem no_kleinFour_subgroup_of_isCyclic
    {G : Type u} [Group G]
    (M V : Subgroup G) (hVK : IsKleinFour V) (hVM : V ≤ M)
    (hMcyc : IsCyclic M) :
    False := by
  let : IsCyclic M := hMcyc
  have hnot : ¬ IsCyclic (↥V) :=
    @IsKleinFour.not_isCyclic (↥V) _ hVK
  exact hnot (Subgroup.isCyclic_of_le hVM)

public theorem no_kleinFour_subgroup_of_dihedral_odd
    {G : Type u} [Group G] [Finite G]
    (M V : Subgroup G) (z : ℕ)
    (hVK : IsKleinFour V) (hVM : V ≤ M)
    (hMdihedral : Nonempty (M ≃* DihedralGroup z)) (hzodd : Odd z) :
    False := by
  have hMcard : Nat.card M = 2 * z := by
    have h := Nat.card_congr (hMdihedral.some.toEquiv)
    rw [DihedralGroup.nat_card] at h
    exact h
  have hdvd : Nat.card V ∣ Nat.card M := Subgroup.card_dvd_of_le hVM
  rw [hVK.card_four, hMcard] at hdvd
  rcases hzodd with ⟨k, hk⟩
  rw [hk] at hdvd
  omega

public theorem v4_le_kernel_of_fixedPointFree
    {M : Type u} [Group M] [Finite M]
    (N A V C : Subgroup M)
    (hNnormal : N.Normal)
    (hdisj : Disjoint N C) (hjoin : N ⊔ C = ⊤)
    (hAne : A ≠ ⊥) (hA_leN : A ≤ N)
    (hNab : ∀ x : M, x ∈ N → ∀ y : M, y ∈ N → x * y = y * x)
    (hVleC : V ≤ Subgroup.centralizer (A : Set M))
    (hfree : ∀ c : M, c ∈ C → c ≠ 1 →
      ∀ a : M, a ∈ A → a ≠ 1 → c * a * c⁻¹ ≠ a) :
    V ≤ N := by
  let : N.Normal := hNnormal
  have hcomp : N.IsComplement' C := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
    intro g
    have hg : g ∈ (N : Set M) * (C : Set M) := by
      rw [← Subgroup.normal_mul N C, hjoin]
      trivial
    rcases hg with ⟨n, hn, c, hc, hnc⟩
    exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩
  intro v hv
  have hvM : v ∈ (N : Set M) * (C : Set M) := by
    rw [← Subgroup.normal_mul N C, hjoin]
    trivial
  rcases hvM with ⟨n, hn, c, hc, hnc⟩
  have hnc' : n * c = v := hnc
  have hc_cent : ∀ a : M, a ∈ A → c * a = a * c := by
    intro a ha
    have haN : a ∈ N := hA_leN ha
    have hncent : n * a = a * n := hNab n hn a haN
    have hvcent : v * a = a * v :=
      ((Subgroup.mem_centralizer_iff.mp (hVleC hv)) a ha).symm
    calc
      c * a = n⁻¹ * (v * a) := by
        rw [← hnc']
        group
      _ = n⁻¹ * (a * v) := by rw [hvcent]
      _ = a * c := by
        rw [← hnc']
        calc
          n⁻¹ * (a * (n * c)) = (n⁻¹ * a * n) * c := by group
          _ = (n⁻¹ * n * a) * c := by
            have h1 : n⁻¹ * a * n * c = n⁻¹ * (a * n) * c := by group
            rw [h1, ← hncent]
            group
          _ = a * c := by group
  have hc_one : c = 1 := by
    by_contra hcne
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have haA : (a : M) ∈ A := a.2
    have ha_ne : (a : M) ≠ 1 := by
      intro h
      exact ha (Subtype.ext h)
    have hcaeq : c * (a : M) * c⁻¹ = (a : M) := by
      calc
        c * (a : M) * c⁻¹ = (a : M) * c * c⁻¹ := by
          rw [hc_cent (a : M) haA]
        _ = (a : M) := by group
    exact hfree c hc hcne (a : M) haA ha_ne hcaeq
  rw [← hnc', hc_one]
  simpa using hn

public theorem frobenius_complement_has_no_v4_centralizer
    {M : Type u} [Group M] [Finite M]
    (N A V C : Subgroup M)
    {p : ℕ} [Fact p.Prime]
    (hNnormal : N.Normal)
    (hdisj : Disjoint N C) (hjoin : N ⊔ C = ⊤)
    (hNp : IsPGroup p N) (hpodd : Odd p)
    (hAp : IsPGroup p A)
    (hcop : Nat.Coprime p (Nat.card C))
    (hAne : A ≠ ⊥)
    (hNab : ∀ x : M, x ∈ N → ∀ y : M, y ∈ N → x * y = y * x)
    (hVK : IsKleinFour V) (hVleC : V ≤ Subgroup.centralizer (A : Set M))
    (hfree : ∀ c : M, c ∈ C → c ≠ 1 →
      ∀ a : M, a ∈ A → a ≠ 1 → c * a * c⁻¹ ≠ a) :
    False := by
  let : N.Normal := hNnormal
  have hcomp : N.IsComplement' C := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
    intro g
    have hg : g ∈ (N : Set M) * (C : Set M) := by
      rw [← Subgroup.normal_mul N C, hjoin]
      trivial
    rcases hg with ⟨n, hn, c, hc, hnc⟩
    exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩
  have hA_leN : A ≤ N :=
    pGroup_le_kernel_of_complement N A C hNnormal hcomp hAp hcop
  have hVleN : V ≤ N :=
    v4_le_kernel_of_fixedPointFree N A V C hNnormal hdisj hjoin
      hAne hA_leN hNab hVleC hfree
  exact no_kleinFour_of_pGroup_subgroup N V hNp hpodd hVleN hVK

end CFSG.GorensteinWalter
