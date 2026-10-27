module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut
public import CFSG.GroupTheory.InvolutionPair

public noncomputable section

namespace CFSG.StandardType.QTwoOrthogonalCav

open Module Multiplicative
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open SpCoord

theorem four_dvd_fixed_of_full_data
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {E : Subgroup (V ≃ₗ[K] V)}
    (hEΩ : E ≤ orthDerived Q) (Δ : OrthTorus.TBJOmData Q 3 E n)
    (f₀ : Fin n → Multiplicative (ZMod 3))
    (h6 : 6 ≤ finrank K (fixedSpace (Δ.τ f₀))) :
    4 ∣ Nat.card (ggAutomizer (supportedFixedDerived Q (Δ.τ f₀)) E) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  let C := Fin n → Multiplicative (ZMod 3)
  let κ : C ≃* E := (MonoidHom.ofInjective Δ.τ_inj).trans
    (MulEquiv.subgroupCongr Δ.τ_range)
  let H : Subgroup (MulAut C) :=
    (ggAutomizer (supportedFixedDerived Q (Δ.τ f₀)) E).map (MulAut.congr κ.symm).toMonoidHom
  obtain ⟨i, k, l, hi, hk, hl, hik, hil, hkl⟩ :=
    full_data_exists_three_zero hQ hdim Δ f₀ h6
  have hmem : ∀ a b : Fin n, a ≠ b → toAdd (f₀ a) = 0 → toAdd (f₀ b) = 0 →
      (sgnAut a : MulAut C) * sgnAut b ∈ H := by
    intro a b hab ha hb
    obtain ⟨g, hg, hact⟩ := Δ.blockZ_dinv (by decide) hQ hEΩ f₀ (by omega) hab ha hb
    apply (mem_map_congr_ggAutomizer_iff E (supportedFixedDerived Q (Δ.τ f₀)) κ _).mpr
    refine ⟨g, hg, fun f => ?_⟩
    change g * Δ.τ f * g⁻¹ = Δ.τ (NbrOrth.dinv a b f)
    exact hact f
  let u : H := ⟨sgnAut i * sgnAut k, hmem i k hik hi hk⟩
  let v : H := ⟨sgnAut i * sgnAut l, hmem i l hil hi hl⟩
  have hc : ∀ a b : Fin n, Commute (sgnAut a : MulAut C) (sgnAut b) :=
    fun a b => sgnAut_mul_comm a b
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    change (sgnAut i * sgnAut k : MulAut C) * (sgnAut i * sgnAut k) = 1
    rw [← pow_two, (hc i k).mul_pow, sgnAut_sq, sgnAut_sq, one_mul]
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    change (sgnAut i * sgnAut l : MulAut C) * (sgnAut i * sgnAut l) = 1
    rw [← pow_two, (hc i l).mul_pow, sgnAut_sq, sgnAut_sq, one_mul]
  have huv : u * v = v * u := by
    apply Subtype.ext
    exact (((hc i i).mul_right (hc i l)).mul_left
      ((hc k i).mul_right (hc k l))).eq
  have htest : ∀ j : Fin n,
      (Pi.mulSingle j (ofAdd (1 : ZMod 3)) : C) ≠
        (Pi.mulSingle j (ofAdd (1 : ZMod 3)) : C)⁻¹ := by
    intro j hj
    have he : (1 : ZMod 3) = -1 := by
      simpa using congrArg (fun f : C => toAdd (f j)) hj
    exact (by decide : (1 : ZMod 3) ≠ -1) he
  let dk : C := Pi.mulSingle k (ofAdd (1 : ZMod 3))
  let dl : C := Pi.mulSingle l (ofAdd (1 : ZMod 3))
  have huAct : u.val dk = dk⁻¹ := by
    change (sgnAut i * sgnAut k : MulAut C) (Pi.mulSingle k (ofAdd (1 : ZMod 3))) =
      (Pi.mulSingle k (ofAdd (1 : ZMod 3)))⁻¹
    rw [MulAut.mul_apply, sgnAut_mulSingle_self, map_inv, sgnAut_mulSingle_of_ne hik.symm]
  have hvAct : v.val dk = dk := by
    change (sgnAut i * sgnAut l : MulAut C) (Pi.mulSingle k (ofAdd (1 : ZMod 3))) =
      Pi.mulSingle k (ofAdd (1 : ZMod 3))
    rw [MulAut.mul_apply, sgnAut_mulSingle_of_ne hkl, sgnAut_mulSingle_of_ne hik.symm]
  have hvAct' : v.val dl = dl⁻¹ := by
    change (sgnAut i * sgnAut l : MulAut C) (Pi.mulSingle l (ofAdd (1 : ZMod 3))) =
      (Pi.mulSingle l (ofAdd (1 : ZMod 3)))⁻¹
    rw [MulAut.mul_apply, sgnAut_mulSingle_self, map_inv, sgnAut_mulSingle_of_ne hil.symm]
  have hu1 : u ≠ 1 := by
    intro hu
    have he := congrArg (fun w : H => w.val dk) hu
    change u.val dk = dk at he
    rw [huAct] at he
    exact htest k he.symm
  have hv1 : v ≠ 1 := by
    intro hv
    have he := congrArg (fun w : H => w.val dl) hv
    change v.val dl = dl at he
    rw [hvAct'] at he
    exact htest l he.symm
  have hne : u ≠ v := by
    intro h
    have he := congrArg (fun w : H => w.val dk) h
    rw [huAct, hvAct] at he
    exact htest k he.symm
  have hfour : 4 ∣ Nat.card H := by
    have hcard := CFSG.GroupTheory.card_closure_pair_eq_four hu2 hv2 huv hu1 hv1 hne
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  change 4 ∣ Nat.card ((ggAutomizer (supportedFixedDerived Q (Δ.τ f₀)) E).map
    (MulAut.congr κ.symm).toMonoidHom) at hfour
  rwa [Subgroup.card_map_of_injective (MulAut.congr κ.symm).injective] at hfour

end CFSG.StandardType.QTwoOrthogonalCav

end
