module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentPsuNo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentUnitDual
import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUAlg
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open

open scoped Matrix

theorem e9c7Free_statedSU {n q : ℕ} (hn : n = 4 ∨ n = 5) {F : Type} [Field F] [Finite F]
    (σ : F →+* F) (hσ : ∀ a, σ a = a ^ q) (hF : Nat.card F = q ^ 2) (hq3 : q % 3 = 1)
    (h7 : ¬ 7 ∣ q) (h7' : ¬ 7 ∣ q ^ 2 - 1) : E9C7Free ↥(StatedSU n q F) := by
  let eφ : GL (Fin n) F ≃* ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F))
  let φ : GL (Fin n) F →* ((Fin n → F) ≃ₗ[F] (Fin n → F)) := eφ.toMonoidHom
  have hφinj : Function.Injective φ := eφ.injective
  have hφcoe : ∀ A : GL (Fin n) F,
      ((φ A : (Fin n → F) ≃ₗ[F] (Fin n → F)) : (Fin n → F) →ₗ[F] (Fin n → F)) =
        Matrix.toLin' A := by
    intro A
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)) A) :
      (Fin n → F) →ₗ[F] (Fin n → F)) = Matrix.toLin' A
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply']
  let U : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) := (StatedSU n q F).map φ
  let ψ : ↥(StatedSU n q F) →* ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
    φ.comp (StatedSU n q F).subtype
  have hψinj : Function.Injective ψ := hφinj.comp (StatedSU n q F).subtype_injective
  have hnV : Module.finrank F (Fin n → F) = 4 ∨ Module.finrank F (Fin n → F) = 5 := by
    rw [Module.finrank_fin_fun]
    exact hn
  have hZsq : ∀ x : ZMod 7, x ^ 2 + 1 ≠ 0 := by decide
  have h7q2 : ¬ 7 ∣ q ^ 2 := fun h => h7 (Nat.Prime.dvd_of_dvd_pow Nat.prime_seven h)
  have h7q2p1 : ¬ 7 ∣ q ^ 2 + 1 := by
    intro h
    have hZ : ((q ^ 2 + 1 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) 7).mpr h
    have hZ' : (q : ZMod 7) ^ 2 + 1 = 0 := by simpa using hZ
    exact hZsq (q : ZMod 7) hZ'
  have hQ7 : ¬ 7 ∣ Nat.card F ∧ ¬ 7 ∣ Nat.card F - 1 ∧ ¬ 7 ∣ Nat.card F + 1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hF]; exact h7q2
    · rw [hF]; exact h7'
    · rw [hF]; exact h7q2p1
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3card : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have hq3mod : q ≡ 1 [MOD 3] := by simpa [Nat.ModEq] using hq3
    have hsq : q ^ 2 ≡ 1 [MOD 3] := by simpa using hq3mod.pow 2
    exact hsq.symm.dvd'
  obtain ⟨ζ, hζord⟩ := exists_prime_orderOf_dvd_card' 3 h3card
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζord]; exact pow_orderOf_eq_one ζ
  have hζ3F : (ζ : F) ^ 3 = 1 := by
    have h := congrArg (fun u : Fˣ => (u : F)) hζ3
    simpa using h
  have hζ1F : (ζ : F) ≠ 1 := by
    intro h
    have hζ1 : ζ = 1 := Units.ext h
    rw [hζ1, orderOf_one] at hζord
    exact absurd hζord (by norm_num)
  have hq_eq : q = 3 * (q / 3) + 1 := by
    have h := Nat.mod_add_div q 3
    omega
  have hζqF : (ζ : F) ^ q = (ζ : F) := by
    rw [hq_eq, pow_add, pow_mul, hζ3F, one_pow, one_mul, pow_one]
  set ω : F := (ζ : F) with hωdef
  have hω3 : ω ^ 3 = 1 := by rw [hωdef]; exact hζ3F
  have hω1 : ω ≠ 1 := by rw [hωdef]; exact hζ1F
  have hωq : ω ^ q = ω := by rw [hωdef]; exact hζqF
  have hdual : ∀ g ∈ U, g ^ 3 = 1 →
      Module.finrank F ↥(LinearMap.ker ((g : (Fin n → F) →ₗ[F] (Fin n → F)) - ω • 1)) =
        Module.finrank F ↥(LinearMap.ker
          ((g : (Fin n → F) →ₗ[F] (Fin n → F)) - ω ^ 2 • 1)) := by
    intro g hg _
    change g ∈ (StatedSU n q F).map φ at hg
    obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp hg
    rw [← hAg]
    have hAprop : ((A : Matrix (Fin n) (Fin n) F).map (fun x : F => x ^ q))ᵀ *
        (A : Matrix (Fin n) (Fin n) F) = 1 := by
      have h :=
        (CFSG.HardMathSupport.Foote.ModuleExclusions.unitary_of_mem_statedSU σ hσ hA).1
      rwa [← show (fun x : F => x ^ q) = ⇑σ from funext fun x => (hσ x).symm] at h
    have h := finrank_ker_unitary_eq (n := n) (q := q) σ hσ hAprop hω3 hωq
    rwa [hφcoe A]
  intro a b r hrel
  have hx : ψ a ∈ U := by
    change ψ a ∈ (StatedSU n q F).map φ
    exact Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩
  have hy : ψ b ∈ U := by
    change ψ b ∈ (StatedSU n q F).map φ
    exact Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩
  exact psu_no_e9c7 (F := F) (V := Fin n → F) hnV hQ7 ω hω3 hω1 U hdual
    (ψ a) (ψ b) (ψ r) hx hy (E9C7Rel.map ψ hψinj hrel)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
