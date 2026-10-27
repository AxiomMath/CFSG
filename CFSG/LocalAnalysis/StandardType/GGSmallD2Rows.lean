module

public import CFSG.LocalAnalysis.StandardType.GGSmallD2Ctx
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
  {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}

namespace GGSmallD2Ctx

theorem false_of_slpm (X : GGSmallD2Ctx p N A T AT)
    (hsl : ∀ g : ↥T ≃ₗ[ZMod p] ↥T, g ∈ AT ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) :
    False := by
  classical
  haveI : Module.Finite (ZMod p) ↥T := X.finite_T
  let σ : ↥T ≃ₗ[ZMod p] ↥T := LinearEquiv.neg (ZMod p)
  have hσ2 : σ * σ = 1 := by
    ext v
    simp [σ, LinearEquiv.mul_apply]
  have hσdet : LinearEquiv.det σ = 1 ∨ LinearEquiv.det σ = -1 := by
    have h2 : ((LinearEquiv.det σ : ZMod p)) ^ 2 = 1 := by
      have h1 : LinearEquiv.det σ * LinearEquiv.det σ = 1 := by
        rw [← map_mul, hσ2, map_one]
      have h2' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h1
      simpa [pow_two] using h2'
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  exact X.false_of_neg_mem ((hsl σ).mpr hσdet)

theorem false_of_orth (X : GGSmallD2Ctx p N A T AT) {Q : QuadraticForm (ZMod p) ↥T}
    (hA : ∀ g, g ∈ AT ↔ ZS.IsIsom p Q g) : False := by
  have hneg : (LinearEquiv.neg (ZMod p) : ↥T ≃ₗ[ZMod p] ↥T) ∈ AT :=
    (hA _).mpr (fun v => by
      simpa [LinearEquiv.neg_apply] using (QuadraticMap.map_neg Q v))
  exact X.false_of_neg_mem hneg

theorem false_of_gmmn (X : GGSmallD2Ctx p N A T AT) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) ↥T) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (hA : AT = ZS.gmmn p f i₀ i₁ ζ) : False := by
  have hd : Module.finrank (ZMod p) ↥T = n := by
    simpa using Module.finrank_eq_card_basis f
  have hn : 2 ≤ n := by
    have hN := X.N_ge
    rcases X.finrank_T with h | h <;> omega
  exact X.not_isImprimitiveOnV (hA.symm ▸ ZS.isImprimitiveOnV_gmmn hn f i₀ i₁ ζ)

theorem false_of_g2mmn (X : GGSmallD2Ctx p N A T AT) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) ↥T) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (hA : AT = ZS.g2mmn p f i₀ i₁ ζ) : False := by
  have hd : Module.finrank (ZMod p) ↥T = n := by
    simpa using Module.finrank_eq_card_basis f
  have hn : 2 ≤ n := by
    have hN := X.N_ge
    rcases X.finrank_T with h | h <;> omega
  exact X.not_isImprimitiveOnV (hA.symm ▸ ZS.isImprimitiveOnV_g2mmn hn f i₀ i₁ ζ)

theorem false_of_exc (X : GGSmallD2Ctx p N A T AT) (k : ZS.ExcRow)
    (hcen : Nat.card ↥(Subgroup.center ↥AT) = k.cen) : False := by
  classical
  have hcen2 : 2 ∣ k.cen := by cases k <;> decide
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥AT) := by
    rw [hcen]
    exact hcen2
  have hcen_ne : Nat.card ↥(Subgroup.center ↥AT) ≠ 0 := by
    rw [hcen]
    cases k <;> decide
  haveI : Finite ↥(Subgroup.center ↥AT) := Nat.finite_of_card_ne_zero hcen_ne
  obtain ⟨z, hzord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥AT)) 2 h2dvd
  have hzne : z ≠ 1 := by
    intro hz1
    rw [hz1, orderOf_one] at hzord
    omega
  let zg : ↥T ≃ₗ[ZMod p] ↥T := (z.1 : ↥AT)
  have hz : zg ∈ AT := by
    simpa [zg] using z.1.2
  have hzz : zg * zg = 1 := by
    have hz2c : z * z = 1 := by rw [← pow_two, ← hzord, pow_orderOf_eq_one]
    have hz2AT : (z.1 : ↥AT) * (z.1 : ↥AT) = 1 := by
      have h := congrArg (fun w : ↥(Subgroup.center ↥AT) => (w : ↥AT)) hz2c
      simpa using h
    have h := congrArg (fun g : ↥AT => (g : ↥T ≃ₗ[ZMod p] ↥T)) hz2AT
    simpa [zg] using h
  have hz1 : zg ≠ 1 := by
    intro hz1'
    apply hzne
    apply Subtype.ext
    apply Subtype.ext
    simpa [zg] using hz1'
  have hzc : ∀ q ∈ AT, zg * q = q * zg := by
    intro q hq
    have h := (Subgroup.mem_center_iff.mp z.2) (⟨q, hq⟩ : ↥AT)
    have h' := congrArg (fun g : ↥AT => (g : ↥T ≃ₗ[ZMod p] ↥T)) h
    simpa [zg] using h'.symm
  exact X.false_of_central hz hzc hzz hz1

end GGSmallD2Ctx

end CFSG.StandardType

end
