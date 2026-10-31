module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreNormalizer

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An odd-order subgroup of `H = U·S` is contained in `U`. -/
public theorem oddOrder_subgroup_le_U_of_H_eq_US
    {G : Type u} [Group G] [Finite G]
    (U S H : Subgroup G)
    (hUS : U ⊔ S = H)
    (hUnorm : IsNormalIn U H)
    (hS2 : IsPGroup 2 S)
    (X : Subgroup G)
    (hXH : X ≤ H)
    (hXodd : Odd (Nat.card X)) :
    X ≤ U := by
  intro x hx
  exact element_le_U_of_odd_order U S H hUS hUnorm hS2 (hXH hx) (by
    have hdvd : orderOf x ∣ Nat.card X :=
      Subgroup.orderOf_dvd_natCard X hx
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat hXodd hdvd))

/-- In the A₇ normal-extension package, the ambient odd core `O = O(M)`
centralizes `S`, lies in `H`, and is odd; hence it lies in `B = C_U(S)`. -/
public theorem oddCore_le_centralizer_U_of_H_eq_US
    {G : Type u} [Group G] [Finite G]
    (U S H B O : Subgroup G)
    (hHUS : U ⊔ S = H)
    (hUnorm : IsNormalIn U H)
    (hS2 : IsPGroup 2 S)
    (hSleH : S ≤ H)
    (hB : B = U ⊓ Subgroup.centralizer (S : Set G))
    (hOleH : O ≤ H)
    (hOodd : Odd (Nat.card O))
    (hOcentS : O ≤ Subgroup.centralizer (S : Set G)) :
    O ≤ B := by
  have hOU : O ≤ U :=
    oddOrder_subgroup_le_U_of_H_eq_US U S H hHUS hUnorm hS2 O hOleH hOodd
  intro x hx
  rw [hB]
  exact Subgroup.mem_inf.mpr ⟨hOU hx, hOcentS hx⟩

/-- An odd-order subgroup pointwise inverted by an involution and also
pointwise centralized by it is trivial. -/
public theorem oddOrder_subgroup_eq_bot_of_inverted_and_centralized
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) (t : G)
    (hXodd : Odd (Nat.card X))
    (hXcent : X ≤ Subgroup.centralizer ({t} : Set G))
    (hXinv : ∀ x : G, x ∈ X → t * x * t⁻¹ = x⁻¹) :
    X = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hfix : t * x * t⁻¹ = x := by
    have hcomm : x * t = t * x :=
      (Subgroup.mem_centralizer_iff.mp (hXcent hx)) t (by simp) |>.symm
    calc
      t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [hcomm]
      _ = x := by group
  have hxinv : x⁻¹ = x := hXinv x hx |>.symm.trans hfix
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := congrArg (fun z : G => z * x) hxinv.symm
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
  have hordX : orderOf x ∣ Nat.card X :=
    Subgroup.orderOf_dvd_natCard X hx
  have hordOdd : Odd (orderOf x) := Odd.of_dvd_nat hXodd hordX
  have hord1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hordOdd.not_two_dvd_nat (by rw [h])
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp hord1

/-- An odd-order subgroup pointwise inverted by an involution is disjoint
from any subgroup pointwise centralized by that involution. -/
public theorem oddOrder_subgroup_inf_centralized_eq_bot
    {G : Type u} [Group G] [Finite G]
    (X C : Subgroup G) (t : G)
    (hXodd : Odd (Nat.card X))
    (hCcent : C ≤ Subgroup.centralizer ({t} : Set G))
    (hXinv : ∀ x : G, x ∈ X → t * x * t⁻¹ = x⁻¹) :
    X ⊓ C = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxX : x ∈ X := (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ C := (Subgroup.mem_inf.mp hx).2
  have hxCent : X ⊓ C ≤ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    exact hCcent (Subgroup.mem_inf.mp hy).2
  have hxInv : ∀ y : G, y ∈ X ⊓ C → t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    exact hXinv y (Subgroup.mem_inf.mp hy).1
  have hbot : X ⊓ C = ⊥ :=
    oddOrder_subgroup_eq_bot_of_inverted_and_centralized
      (X ⊓ C) t (by
        have hcard : Nat.card (X ⊓ C : Subgroup G) ∣ Nat.card X :=
          Subgroup.card_dvd_of_le (inf_le_left : X ⊓ C ≤ X)
        exact Odd.of_dvd_nat hXodd hcard)
      hxCent hxInv
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [hbot] at hx
    exact hx
  exact Subgroup.mem_bot.mp hxbot

/-- In the Bender--Glauberman notation, `B = C_U(S)` is literally the
centralizer of the Sylow subgroup `S` inside `U`. -/
public theorem B_eq_centralizer_U
    {G : Type u} [Group G] [Finite G]
    (c : BenderGlauberman.Hyp11 G) :
    c.B = c.U ⊓ Subgroup.centralizer ((c.S : Subgroup G) : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Subgroup.Normalizes (c.S : Subgroup G) c.U :=
    BenderGlauberman.S4_instNormalizesS
  apply le_antisymm
  · intro x hx
    have hxU : x ∈ c.U := BenderGlauberman.mem_U_of_mem_B_s4 c hx
    have hxC : x ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hfix := BenderGlauberman.b_mem_fixedSubgroup_s4 c hx
      have hfix' : (⟨s, hs⟩ : ↥(c.S : Subgroup G)) •
          (⟨x, hxU⟩ : ↥c.U) = (⟨x, hxU⟩ : ↥c.U) := by
        exact (BenderGlauberman.mem_fixedSubgroup_iff (c.S : Subgroup G) c.U
          (⟨x, hxU⟩ : ↥c.U)).mp hfix (⟨s, hs⟩ : ↥(c.S : Subgroup G))
      have h := congrArg Subtype.val hfix'
      change s * x * s⁻¹ = x at h
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using h)
    exact Subgroup.mem_inf.mpr ⟨hxU, hxC⟩
  · intro x hx
    have hxU : x ∈ c.U := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    have hfix : (⟨x, hxU⟩ : ↥c.U) ∈
        BenderGlauberman.fixedSubgroup (c.S : Subgroup G) c.U := by
      rw [BenderGlauberman.mem_fixedSubgroup_iff (c.S : Subgroup G) c.U
        (⟨x, hxU⟩ : ↥c.U)]
      intro s
      apply Subtype.ext
      have hxs : x * (s : G) = (s : G) * x := by
        exact ((Subgroup.mem_centralizer_iff.mp hxC) (s : G) s.2).symm
      calc
        (s : G) * x * (s : G)⁻¹ = (x * (s : G)) * (s : G)⁻¹ := by rw [hxs]
        _ = x := by group
    exact BenderGlauberman.mem_B_of_fixed_s4 c hfix

end CFSG.GorensteinWalter
