module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.RankThree.GroupTheory.SteinbergCEPlaneNormalizerCentralizes

public section

namespace CFSG.LocalAnalysis

open scoped IsMulCommutative

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [Group E] [IsElementaryAbelian p E]

@[expose] noncomputable def mulAutToGL (b : Module.Basis (Fin 2) (ZMod p) (Additive E)) :
    MulAut E →* GL (Fin 2) (ZMod p) :=
  MonoidHom.toHomUnits
    { toFun := fun σ => LinearMap.toMatrix b b
        ((MulEquiv.toAdditive σ).toAddMonoidHom.toZModLinearMap p)
      map_one' := by
        rw [← LinearMap.toMatrix_id b]
        congr 1
      map_mul' := fun σ τ => by
        rw [← LinearMap.toMatrix_mul]
        congr 1 }

theorem mulAutToGL_injective (b : Module.Basis (Fin 2) (ZMod p) (Additive E)) :
    Function.Injective (mulAutToGL (E := E) b) := by
  intro σ τ h
  have h1 := congrArg Units.val h
  change LinearMap.toMatrix b b _ = LinearMap.toMatrix b b _ at h1
  have h2 := (LinearMap.toMatrix b b).injective h1
  apply MulEquiv.ext
  intro x
  have h3 := LinearMap.congr_fun h2 (Additive.ofMul x)
  exact h3

theorem rank_two_elementary_action_index {B : Type*} [Group B] [Finite B] (hB : IsPGroup p B)
    (hE : Nat.card E = p ^ 2) (ρ : B →* MulAut E) :
    (ρ.ker.index = 1 ∨ ρ.ker.index = p) ∧
      ∀ r : ℕ, 1 ≤ r → IsElementaryAbelian p B → Nat.card B = p ^ r →
        IsElementaryAbelian p ρ.ker ∧ p ^ (r - 1) ≤ Nat.card ρ.ker := by
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero _ hp.out.ne_zero)
  have hdim : Module.finrank (ZMod p) (Additive E) = 2 := by
    have : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    rw [Nat.card_zmod] at h
    change Nat.card E = _ at h
    rw [hE] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hdim
  have hrange : Nat.card ρ.range ∣ p := by
    have hR : IsPGroup p ρ.range := by
      rw [MonoidHom.range_eq_map]
      exact (hB.to_subgroup ⊤).map ρ
    have hPg : IsPGroup p (ρ.range.map (mulAutToGL b)) := hR.map _
    have h := CFSG.RankThree.GroupTheory.card_dvd_prime_of_isPGroup_GL_two
      (k := ZMod p) (Nat.card_zmod p) hPg
    rwa [Subgroup.card_map_of_injective (mulAutToGL_injective b)] at h
  have hidx : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have h1 : ρ.ker.index = 1 ∨ ρ.ker.index = p := by
    rw [hidx]
    exact (Nat.dvd_prime hp.out).mp hrange
  refine ⟨h1, fun r hr hBel hBcard => ⟨?_, ?_⟩⟩
  · have hcomm : IsMulCommutative ρ.ker := ⟨⟨fun x y => Subtype.ext (hBel.1.1.comm x y)⟩⟩
    have hexp : Monoid.exponent ρ.ker ∣ p := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => Subtype.ext ?_
      rw [Subgroup.coe_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hBel.exponent_dvd_p x
    exact ⟨hexp⟩
  · have h2 := Subgroup.card_mul_index ρ.ker
    rw [hBcard] at h2
    rcases h1 with h | h
    · rw [h, mul_one] at h2
      rw [h2]
      exact Nat.pow_le_pow_right hp.out.pos (Nat.sub_le r 1)
    · rw [h] at h2
      have h3 : p ^ r = p ^ (r - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel hr]
      rw [h3] at h2
      exact (Nat.eq_of_mul_eq_mul_right hp.out.pos h2).ge

end CFSG.LocalAnalysis
