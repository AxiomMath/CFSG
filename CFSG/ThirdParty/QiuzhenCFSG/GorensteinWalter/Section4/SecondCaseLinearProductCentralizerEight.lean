module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The product-centralizer has enough `2`-part

For a reflection `r` commuting with the distinguished involution `t`, the
product `tr` is an involution.  Fusion of involutions sends `tr` to `t`, so a
conjugate of the fixed dihedral Sylow lies in `C_G(tr)`.  When the dihedral
parameter is at least two this proves `8 ∣ |C_G(tr)|`, the hypothesis needed
for the source's product-centralizer conjugator.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The centralizer of the product of two distinct commuting involutions has
cardinality divisible by eight. -/
public theorem secondCase_linear_product_centralizer_card_dvd_eight
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    {r : G} (hrI : IsInvolution r) (htr : Commute c.t r)
    (hrte : r ≠ c.t) (hm2 : 2 ≤ c.m) :
    8 ∣ Nat.card (Subgroup.centralizer ({c.t * r} : Set G)) := by
  have hprodI : IsInvolution (c.t * r) := by
    constructor
    · intro h
      apply hrte
      calc
        r = 1 * r := by simp
        _ = (c.t * r) * r := by rw [h]
        _ = c.t * (r * r) := by group
        _ = c.t := by
          rw [show r * r = 1 by simpa [pow_two] using hrI.2]
          simp
    · rw [pow_two]
      calc
        (c.t * r) * (c.t * r) = c.t * (r * c.t) * r := by group
        _ = c.t * (c.t * r) * r := by rw [htr.eq]
        _ = (c.t * c.t) * (r * r) := by group
        _ = 1 := by
          rw [show c.t * c.t = 1 by
              simpa [pow_two] using c.t_involution.2,
            show r * r = 1 by simpa [pow_two] using hrI.2]
          simp
  obtain ⟨g, hg⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin (c.t * r) c.t
      hprodI c.t_involution
  let C : Subgroup G := Subgroup.centralizer ({c.t * r} : Set G)
  let Q : Subgroup G := (c.S : Subgroup G).map
    (MulAut.conj g⁻¹).toMonoidHom
  have hQleC : Q ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsH : s ∈ c.H := centralizerSetup_S_le_H c hs
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff] at hsH
    have hst : (s : G) * c.t = c.t * (s : G) :=
      (hsH c.t (by simp)).symm
    change (g⁻¹ * (s : G) * (g⁻¹)⁻¹) * (c.t * r) =
      (c.t * r) * (g⁻¹ * (s : G) * (g⁻¹)⁻¹)
    simp only [inv_inv]
    have hback : g⁻¹ * c.t * g = c.t * r := by
      calc
        g⁻¹ * c.t * g = g⁻¹ * (g * (c.t * r) * g⁻¹) * g := by rw [hg]
        _ = c.t * r := by group
    calc
      (g⁻¹ * (s : G) * g) * (c.t * r) =
          (g⁻¹ * (s : G) * g) * (g⁻¹ * c.t * g) := by rw [hback]
      _ = g⁻¹ * ((s : G) * c.t) * g := by group
      _ = g⁻¹ * (c.t * (s : G)) * g := by rw [hst]
      _ = (g⁻¹ * c.t * g) * (g⁻¹ * (s : G) * g) := by group
      _ = (c.t * r) * (g⁻¹ * (s : G) * g) := by rw [hback]
  have hQcard : Nat.card Q = Nat.card (c.S : Subgroup G) := by
    dsimp [Q]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hScard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
    rcases c.dihedralEquiv with ⟨e⟩
    calc
      Nat.card (c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) :=
        Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ c.m := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
  have h8S : 8 ∣ Nat.card (c.S : Subgroup G) := by
    rw [hScard]
    let n : ℕ := c.m - 2
    have hn : c.m = 2 + n := by
      dsimp [n]
      omega
    refine ⟨2 ^ n, ?_⟩
    rw [hn, pow_add]
    ring
  have h8Q : 8 ∣ Nat.card Q := by rw [hQcard]; exact h8S
  exact h8Q.trans (Subgroup.card_dvd_of_le hQleC)

end CFSG.GorensteinWalter
