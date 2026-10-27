module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InvariantOddPSubgroupCentralized
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvariantOddPSubgroupCentralized
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise
open Matrix
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups

universe u

/-- A nontrivial odd-prime-power subgroup cannot be both inverted and
centralized by the same involution. -/
public theorem no_nontrivial_oddP_inverted_centralized
    {G : Type u} [Group G] [Finite G]
    (s : G) (X : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hinv : BenderGlauberman.IsInvertedBy s X)
    (hcent : X ≤ Subgroup.centralizer ({s} : Set G))
    (hXp : IsPGroup p X) (hpodd : Odd p) (hXne : X ≠ ⊥) :
    False := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have hlt : 1 < Fintype.card X := by
    rw [← Nat.card_eq_fintype_card]
    exact (Subgroup.one_lt_card_iff_ne_bot X).mpr hXne
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : X)
  let x : G := (w : G)
  have hxmem : x ∈ X := w.property
  have hinvx : s * x * s⁻¹ = x⁻¹ := hinv x hxmem
  have hcomm : x * s = s * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hcent hxmem))
  have hcentx : s * x * s⁻¹ = x := by
    calc
      s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hcomm]
      _ = x := by group
  have hx_inv : x = x⁻¹ := by
    exact hcentx.symm.trans hinvx
  have hsq : x * x = 1 := by
    have hpar : x * x = x * x⁻¹ := by
      congr 2
    calc
      x * x = x * x⁻¹ := hpar
      _ = 1 := by group
  have hord2 : orderOf w ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hsq
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hXp) w
  have hord_odd : Odd (orderOf w) := by
    rw [hk]
    exact hpodd.pow
  have hord1 : orderOf w = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hord_odd.not_two_dvd_nat (by rw [h])
  have hw1 : w = 1 := orderOf_eq_one_iff.mp hord1
  exact hwne hw1

public theorem pgl2_no_inverted_oddP_centralized
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup (PGL2 K)) (hPp : IsPGroup p P)
    {t : PGL2 K} (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set (PGL2 K)) ≤
      Subgroup.normalizer (P : Set (PGL2 K)))
    (hPinvByT : BenderGlauberman.IsInvertedBy t P)
    (hPne : P ≠ ⊥) :
    False := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hPcent : P ≤ Subgroup.centralizer ({t} : Set (PGL2 K)) :=
    pgl2_invariant_oddP_subgroup_centralized K hK hcard p hp hpodd P hPp ht hPinv
  exact no_nontrivial_oddP_inverted_centralized t P hPinvByT hPcent hPp hpodd hPne

public theorem psl2_no_inverted_oddP_centralized
    {F : Type u} [Field F] [Finite F]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f) (hrodd : Odd r) (hpodd : Odd p)
    (P : Subgroup (PSL2MatrixGroup F)) (hPp : IsPGroup p P)
    {t : PSL2MatrixGroup F} (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) ≤
      Subgroup.normalizer (P : Set (PSL2MatrixGroup F)))
    (hPinvByT : BenderGlauberman.IsInvertedBy t P)
    (hPne : P ≠ ⊥) :
    False := by
  have hPcent : P ≤ Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) :=
    psl2_invariant_oddP_subgroup_centralized hFcard hrodd hpodd P hPp ht hPinv
  exact no_nontrivial_oddP_inverted_centralized t P hPinvByT hPcent hPp hpodd hPne

end CFSG.GorensteinWalter
