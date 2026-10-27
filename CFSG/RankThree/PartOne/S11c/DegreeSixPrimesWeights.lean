module

public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.DegreeSixInduction

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped IsMulCommutative

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem commute_of_isElementaryAbelian_of_normalizes [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0) {R P : Subgroup (Module.End k V)ˣ} [Finite R] [IsElementaryAbelian 2 R]
    {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P) (hVp : Module.finrank k V < p)
    (hPR : P ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ)) :
    ∀ a ∈ P, ∀ r ∈ R, a * r = r * a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (P ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ)) := ⟨hPR⟩
  let _ : CommGroup R := IsMulCommutative.instCommGroup
  let _ : Module (ZMod 2) (Additive R) := IsElementaryAbelian.isVectorSpace 2
  have : Fintype R := Fintype.ofFinite R
  have : Finite (Module.Dual (ZMod 2) (Additive R)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive R) => (f : Additive R → ZMod 2))
      DFunLike.coe_injective
  have : Fintype (Module.Dual (ZMod 2) (Additive R)) := Fintype.ofFinite _
  let ρ : Representation k R V := (Units.coeHom (Module.End k V)).comp R.subtype
  let φ : P →* MulAut R := MulDistribMulAction.toMulAut P R
  have hφ : ∀ (a : P) (r : R), (((φ a) r : R) : (Module.End k V)ˣ) = a * r * a⁻¹ := fun a r => by
    simp [φ]
  have hφinv : ∀ (a : P) (r : R), ((((φ a)⁻¹) r : R) : (Module.End k V)ˣ) = a⁻¹ * r * a := by
    intro a r
    rw [← map_inv, hφ]
    simp
  let _ : MulAction P (Module.Dual (ZMod 2) (Additive R)) :=
    { smul := fun a χ => dualAct (φ a) χ
      one_smul := fun χ => by
        change dualAct (φ 1) χ = χ
        rw [map_one, dualAct_one]
      mul_smul := fun a b χ => by
        change dualAct (φ (a * b)) χ = dualAct (φ a) (dualAct (φ b) χ)
        rw [map_mul, dualAct_mul] }
  have hsmul : ∀ (a : P) (χ : Module.Dual (ZMod 2) (Additive R)),
      a • χ = dualAct (φ a) χ := fun _ _ => rfl
  have hmem : ∀ (a : P) (χ : Module.Dual (ZMod 2) (Additive R)) (v : V),
      v ∈ signWeightSpace ρ χ →
        (((a : (Module.End k V)ˣ)) : Module.End k V) v ∈ signWeightSpace ρ (a • χ) := by
    intro a χ v hv
    rw [mem_signWeightSpace] at hv ⊢
    intro r
    rw [hsmul, dualAct_ofMul]
    have hv' := hv ((φ a)⁻¹ r)
    have hconj : (r : (Module.End k V)ˣ) * a = a * (((φ a)⁻¹ r : R) : (Module.End k V)ˣ) := by
      rw [hφinv, InvMemClass.coe_inv]
      group
    have h1 : ρ r ((((a : (Module.End k V)ˣ)) : Module.End k V) v) =
        (((a : (Module.End k V)ˣ)) : Module.End k V)
          (ρ ((φ a)⁻¹ r) v) := by
      change (((r : (Module.End k V)ˣ) : Module.End k V) *
        (((a : (Module.End k V)ˣ)) : Module.End k V)) v =
        ((((a : (Module.End k V)ˣ)) : Module.End k V) *
          (((((φ a)⁻¹ r : R) : (Module.End k V)ˣ)) : Module.End k V)) v
      rw [← Units.val_mul, ← Units.val_mul, hconj]
    rw [h1, hv', map_smul]
  have hne : ∀ (a : P) (χ : Module.Dual (ZMod 2) (Additive R)),
      signWeightSpace ρ χ ≠ ⊥ → signWeightSpace ρ (a • χ) ≠ ⊥ := by
    intro a χ hχ
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    intro hbot
    have h1 := hmem a χ v hv
    rw [hbot, Submodule.mem_bot] at h1
    apply hv0
    have h3 : ((((a : (Module.End k V)ˣ))⁻¹ : (Module.End k V)ˣ) : Module.End k V)
        ((((a : (Module.End k V)ˣ)) : Module.End k V) v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    rw [← h3, h1, map_zero]
  have hcard : Fintype.card {χ : Module.Dual (ZMod 2) (Additive R) // signWeightSpace ρ χ ≠ ⊥} ≤
      Module.finrank k V := (iSupIndep_signWeightSpace ρ h2).subtype_ne_bot_le_finrank
  have hfix : ∀ χ : Module.Dual (ZMod 2) (Additive R), signWeightSpace ρ χ ≠ ⊥ →
      ∀ a : P, a • χ = χ := by
    intro χ hχ
    have hsub : MulAction.orbit P χ ⊆ {ψ | signWeightSpace ρ ψ ≠ ⊥} := by
      rintro _ ⟨a, rfl⟩
      exact hne a χ hχ
    obtain ⟨e, he⟩ := hP.card_orbit χ
    have hle : Nat.card (MulAction.orbit P χ) ≤ Module.finrank k V :=
      calc Nat.card (MulAction.orbit P χ) ≤ Nat.card {ψ | signWeightSpace ρ ψ ≠ ⊥} :=
            Nat.card_mono (Set.toFinite _) hsub
        _ = Fintype.card {χ : Module.Dual (ZMod 2) (Additive R) // signWeightSpace ρ χ ≠ ⊥} :=
            Nat.card_eq_fintype_card
        _ ≤ Module.finrank k V := hcard
    have he0 : e = 0 := by
      by_contra hne0
      have := Nat.le_self_pow hne0 p
      omega
    rw [he0, pow_zero, Nat.card_eq_one_iff_unique] at he
    obtain ⟨hsub1, -⟩ := he
    intro a
    exact congrArg Subtype.val (hsub1.elim ⟨a • χ, a, rfl⟩ ⟨χ, MulAction.mem_orbit_self χ⟩)
  intro a ha r hr
  have key : ∀ (χ : Module.Dual (ZMod 2) (Additive R)), ∀ v ∈ signWeightSpace ρ χ,
      (a : Module.End k V) v ∈ signWeightSpace ρ χ := by
    intro χ v hv
    by_cases hχ : signWeightSpace ρ χ = ⊥
    · rw [hχ, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · have h := hmem ⟨a, ha⟩ χ v hv
      rwa [hfix χ hχ ⟨a, ha⟩] at h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply LinearMap.ext
  intro v
  have hv : v ∈ ⨆ χ, signWeightSpace ρ χ := by
    rw [iSup_signWeightSpace_eq_top ρ h2]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (signWeightSpace ρ)
    (motive := fun w => ((a : Module.End k V) * (r : Module.End k V)) w =
      ((r : Module.End k V) * (a : Module.End k V)) w) hv (fun χ w hw => ?_) ?_
    (fun x y hx hy => ?_)
  · have hr1 := (mem_signWeightSpace ρ χ w).mp hw ⟨r, hr⟩
    have hr2 := (mem_signWeightSpace ρ χ _).mp (key χ w hw) ⟨r, hr⟩
    change (a : Module.End k V) ((r : Module.End k V) w) =
      (r : Module.End k V) ((a : Module.End k V) w)
    have hr1' : (r : Module.End k V) w = _ := hr1
    have hr2' : (r : Module.End k V) ((a : Module.End k V) w) = _ := hr2
    rw [hr2', hr1', map_smul]
  · simp
  · simp only [map_add, hx, hy]

end CFSG.RankThree.PartOne.DegreeSixInduction
