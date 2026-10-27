module

public import CFSG.Quasithin.Recognition.F112Crit.PermBound.Averaging
public import CFSG.Quasithin.Recognition.F112Crit.PermBound.Count

public section

namespace CFSG.Quasithin.F112Crit.PermBound

open GaloisDescent

variable {H : Type*} [Group H] {Ω : Type*} [MulAction H Ω] {M : Type*} [AddCommGroup M]
  [DistribMulAction H M]

theorem two_pow_le_card_commSub [Finite Ω] [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (hLodd : L ≤ Subgroup.closure {h : H | h ∈ L ∧ Odd (orderOf h)})
    (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Nat.card Ω))
    {ω₀ : Ω} {U : Subgroup H} (hUL : U ≤ L) (hU2 : IsPGroup 2 U) (hUfix : ∀ u ∈ U, u • ω₀ = ω₀)
    (hUtrans : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → ∃ u ∈ U, u • μ = ν)
    (V : Ω → AddSubgroup M) (hV : ∀ l ∈ L, ∀ μ : Ω, ∀ v ∈ V μ, l • v ∈ V (l • μ))
    (hVsup : ⨆ μ, V μ = ⊤)
    (hstab : ∀ μ : Ω, ∀ l ∈ L, l • μ = μ → ∃ k : ℕ, ∀ v ∈ V μ, (l ^ 2 ^ k) • v = v)
    {z : H} (hz : z * z = 1) (hzL : ∀ l ∈ L, z * l * z⁻¹ ∈ L) (hK : commL M L ≠ ⊥) :
    2 ^ ((Nat.card Ω - Nat.card (MulAction.fixedBy Ω z)) / 2) ≤
      Nat.card (commSub (DistribMulAction.toAddEquiv M z)) := by
  obtain ⟨X, c, hXL, -, hcK, hcX, hcfix, hcz, hXK⟩ :=
    exists_avg h2 hLodd htrans hodd V hV hVsup hstab hz hzL hK ω₀
  exact two_pow_le_of_avg h2 htrans hodd hUL hU2 hUfix hUtrans hz hzL hXL hcK hcX hcfix hcz hXK

end CFSG.Quasithin.F112Crit.PermBound

end
