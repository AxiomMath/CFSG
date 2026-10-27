module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Assembly

theorem pPrimeCore_eq_bot_of_centralizers {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} (hE : IsElemAbelian p E) (hE2 : Nat.card E = p ^ 2) {R : Subgroup G}
    (hR : ¬ p ∣ Nat.card R) (hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R)
    (hC : ∀ e ∈ E, e ≠ 1 → R ⊓ Subgroup.centralizer {e} = ⊥) : R = ⊥ := by
  classical
  haveI : IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Subtype.ext
        simpa using hE.2 (x : G) x.2 }
  have hEnorm : E ≤ Subgroup.normalizer (R : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff'']
    intro r
    constructor
    · intro hr
      simpa using hER e⁻¹ (E.inv_mem he) r hr
    · intro hr
      have h := hER e he (e⁻¹ * r * e) hr
      have heq : e * (e⁻¹ * r * e) * e⁻¹ = r := by group
      rwa [heq] at h
  letI : MulDistribMulAction E R :=
    MulDistribMulAction.compHom R (R.normalizerMonoidHom.comp (Subgroup.inclusion hEnorm))
  have hact : ∀ (a : E) (x : R), ((a • x : R) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := E) (H := R)
    hE2.ge hR
  have hall : (⨆ (a : E) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) R) ≤ ⊥ := by
    refine iSup₂_le fun a ha x hx => ?_
    rw [Subgroup.mem_bot]
    have h1 := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have h2 : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
      simpa [hact a x] using congrArg (fun z : R => (z : G)) h1
    have hax : (a : G) * (x : G) = (x : G) * (a : G) := mul_inv_eq_iff_eq_mul.mp h2
    have hmem : (x : G) ∈ R ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hax.symm⟩
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    rw [hC (a : G) a.2 haG] at hmem
    exact Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)
  have htopbot : (⊤ : Subgroup R) = ⊥ := by
    rw [← hgen]
    exact le_antisymm hall bot_le
  rw [Subgroup.eq_bot_iff_forall]
  intro r hr
  have h1 : (⟨r, hr⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
  rw [htopbot] at h1
  simpa using congrArg (fun z : R => (z : G)) (Subgroup.mem_bot.mp h1)

end CFSG.StandardType.SporadicShape
