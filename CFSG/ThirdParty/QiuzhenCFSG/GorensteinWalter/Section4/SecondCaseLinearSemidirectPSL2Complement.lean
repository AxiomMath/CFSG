module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimePrimeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearSemidirectComplement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open BenderSuzuki.MatrixGroups
open scoped Pointwise

/-- The defining-characteristic normal subgroup in a Dickson semidirect
subgroup is a normal complement to the normalizer of a selected coprime
prime-order subgroup lying in the cyclic complement. -/
public theorem secondCase_linear_semidirect_psl2_normal_complement
    {F : Type u} [Field F] [Finite F]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f) (hpne : p ≠ r)
    (H : Subgroup (PSL2MatrixGroup F))
    (N C X : Subgroup H)
    (hNnormal : N.Normal)
    (hNelem : IsElementaryAbelian r N)
    (hNcard_dvd : Nat.card N ∣ Nat.card F)
    (hCcyc : IsCyclic C) (hdisj : Disjoint N C)
    (hjoin : N ⊔ C = ⊤) (hXleC : X ≤ C)
    (hXcard : Nat.card X = p) (hXne : X ≠ ⊥)
    (hNcyc : IsCyclic (Subgroup.normalizer (X : Set H))) :
    N.Normal ∧
      Subgroup.normalizer (X : Set H) = C ∧
      N ⊓ Subgroup.normalizer (X : Set H) = ⊥ ∧
      N ⊔ Subgroup.normalizer (X : Set H) = ⊤ ∧
      Nat.card N ∣ Nat.card F := by
  let : IsElementaryAbelian r N := hNelem
  have hNnorm : ∀ n : H, n ∈ N →
      n ∈ Subgroup.normalizer (X : Set H) → n = 1 := by
    intro n hn hnorm
    by_contra hn1
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    have hx : (x : H) ∈ X := x.property
    have hnN : (⟨n, hn⟩ : N) ≠ 1 := by
      intro h
      apply hn1
      exact congrArg Subtype.val h
    have hnexp : Monoid.exponent N ∣ r :=
      IsElementaryAbelian.exponent_dvd_p r N
    have hnpow : (⟨n, hn⟩ : N) ^ r = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hnexp) _
    have hnorderN : orderOf (⟨n, hn⟩ : N) = r :=
      orderOf_eq_prime hnpow hnN
    have hnorder : orderOf (n : H) = r := by
      calc
        orderOf (n : H) = orderOf (⟨n, hn⟩ : N) :=
          Subgroup.orderOf_coe (⟨n, hn⟩ : N)
        _ = r := hnorderN
    have hxne : (x : H) ≠ 1 := by
      intro h
      apply hx1
      exact Subtype.ext h
    have hxdiv : orderOf (x : H) ∣ Nat.card X :=
      Subgroup.orderOf_dvd_natCard X hx
    have hxorder : orderOf (x : H) = p := by
      apply orderOf_eq_prime
      · have hdiv : orderOf (x : H) ∣ p := by simpa [hXcard] using hxdiv
        rw [← orderOf_dvd_iff_pow_eq_one]
        exact hdiv
      · exact hxne
    let nN : Subgroup.normalizer (X : Set H) := ⟨n, hnorm⟩
    let xN : Subgroup.normalizer (X : Set H) :=
      ⟨(x : H), Subgroup.le_normalizer hx⟩
    have hcommN : nN * xN = xN * nN := by
      exact hNcyc.isMulCommutative.is_comm.comm _ _
    have hcomm : n * (x : H) = (x : H) * n := congrArg Subtype.val hcommN
    have hcommAmbient :
        Commute (H.subtype n) (H.subtype (x : H)) := by
      change H.subtype n * H.subtype (x : H) =
        H.subtype (x : H) * H.subtype n
      exact congrArg H.subtype hcomm
    have hnorderAmbient : orderOf (H.subtype n) = r := by
      exact (orderOf_injective H.subtype H.subtype_injective n).trans hnorder
    have hxorderAmbient : orderOf (H.subtype (x : H)) = p := by
      exact (orderOf_injective H.subtype H.subtype_injective (x : H)).trans hxorder
    exact (psl2_no_commuting_distinct_prime_order
      (F := F) (r := r) (p := p) hFcard hpne
      (a := H.subtype n) (b := H.subtype (x : H))
      (haorder := hnorderAmbient) (hborder := hxorderAmbient)
      (hcomm := hcommAmbient)).elim
  have hbase := normal_complement_of_semidirect_cyclic_normalizer
    N C X hNnormal hCcyc hdisj hjoin hXleC hNnorm
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, ?_⟩
  exact hNcard_dvd

end CFSG.GorensteinWalter
