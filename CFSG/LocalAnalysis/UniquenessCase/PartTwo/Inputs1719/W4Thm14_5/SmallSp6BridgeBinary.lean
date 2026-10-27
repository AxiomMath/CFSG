module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgePlacement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeRootTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open CFSG.Open Module Representation Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Theory.Representation
open scoped TensorProduct MatrixGroups

variable {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k]

omit [Finite K] in
private theorem factorsFinrankLe_extend_standard_blocks
    [Fintype K] [CharP k 2] [IsAlgClosed k] [Algebra (ZMod 2) k] {e : ℕ}
    (hK : Fintype.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W)
    {z : StatedSp 2 K} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hsmall : finrank (ZMod 2) (LinearMap.range
      (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) < 3 * e) (b : Bool) :
    FactorsFinrankLe ((extendScalars k ρ).comp
      ((spEmbed Fin.succ (Fin.succ_injective 2)).comp (rootBlock b))) 2 := by
  classical
  let : Algebra (ZMod 2) K := (ZMod.castHom (dvd_refl 2) K).toAlgebra
  let ε := spEmbed (K := K) Fin.succ (Fin.succ_injective 2)
  let τ : Representation (ZMod 2) (antiSp K) W :=
    ρ.comp (ε.comp (antiSpEquiv K).toMonoidHom)
  let z' : antiSp K := (antiSpEquiv K).symm z
  have hz' : z' * z' = 1 := by rw [← map_mul, hz, map_one]
  have hz'1 : z' ≠ 1 := fun h => hz1 ((antiSpEquiv K).symm.injective
    (h.trans (map_one _).symm))
  have hsmallτ : finrank (ZMod 2) (LinearMap.range (τ z' - 1)) < 3 * e := by
    have heq : τ z' = ρ (ε z) := by
      dsimp only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, z']
      rw [MulEquiv.apply_symm_apply]
    have hfr : finrank (ZMod 2) (LinearMap.range (τ z' - 1)) =
        finrank (ZMod 2) (LinearMap.range (ρ (ε z) - 1)) :=
      congrArg (fun a : W →ₗ[ZMod 2] W =>
        finrank (ZMod 2) (LinearMap.range (a - 1))) heq
    exact hfr.trans_lt hsmall
  have h := factorsFinrankLe_extend_root_of_displacement_lt (k := k)
    hK he τ hz' hz'1 hsmallτ b
  have hcomp : τ.comp ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)) =
      ρ.comp (ε.comp (rootBlock b)) := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro w
    simp [τ]
  rw [hcomp] at h
  exact h

omit [Finite K] [CharP K 2] in
private theorem factorsFinrankLe_extend_comp_conj
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Algebra (ZMod 2) k]
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) (g : StatedSp 3 K)
    (R : Subgroup (StatedSp 3 K))
    (h : FactorsFinrankLe ((extendScalars k
      (ρ.comp (MulAut.conj g⁻¹).toMonoidHom)).comp R.subtype) 2) :
    FactorsFinrankLe ((extendScalars k ρ).comp R.subtype) 2 := by
  let σ : Representation (ZMod 2) (StatedSp 3 K) W :=
    ρ.comp (MulAut.conj g⁻¹).toMonoidHom
  let β : Representation.Equiv σ ρ :=
    Representation.Equiv.mk (repLinEquiv ρ g) fun a => by
      apply LinearMap.ext
      intro w
      change ρ g (ρ (g⁻¹ * a * g) w) = ρ a (ρ g w)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
  let f := extendScalars_map k β.toIntertwiningMap
  let fR : IntertwiningMap ((extendScalars k σ).comp R.subtype)
      ((extendScalars k ρ).comp R.subtype) :=
    ⟨f.toLinearMap, fun r => f.isIntertwining' r⟩
  have hf : Function.Surjective fR :=
    LinearMap.baseChange_surjective k β.toLinearEquiv.surjective
  exact factorsFinrankLe_of_surjective fR hf h

theorem factorsFinrankLe_all_roots
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (StatedSp 3 K) V)
    (h : ∀ b : Bool, FactorsFinrankLe (ρ.comp
      ((spEmbed Fin.succ (Fin.succ_injective 2)).comp (rootBlock b))) 2) (i : Fin 3) :
    FactorsFinrankLe (ρ.comp
      ((spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i).subtype) 2 := by
  obtain ⟨g, ι, hι, hrange⟩ := exists_conj_rootSL2_range (K := K) i
  let R := (spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i
  let ψ := (spEmbed Fin.succ (Fin.succ_injective 2)).comp ι
  have hψ : FactorsFinrankLe (ρ.comp ψ) 2 := by
    rcases hι with hι | hι
    · simpa [ψ, hι, rootBlock] using h false
    · simpa [ψ, hι, rootBlock] using h true
  have hmem : ∀ x : SL(2, K), g⁻¹ * ψ x * g ∈ R := by
    intro x
    have hx : ψ x ∈ R.map (MulAut.conj g).toMonoidHom :=
      hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
    obtain ⟨r, hr, heq⟩ := hx
    have heq' : g * r * g⁻¹ = ψ x := heq
    rw [← heq']
    simpa [mul_assoc] using hr
  let π : SL(2, K) →* R :=
    (((MulAut.conj g⁻¹).toMonoidHom).comp ψ).codRestrict R fun x => hmem x
  have hπ : Function.Surjective π := by
    intro r
    have hx : g * (r : StatedSp 3 K) * g⁻¹ ∈ ψ.range := by
      rw [hrange]
      exact ⟨r, r.2, rfl⟩
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, Subtype.ext ?_⟩
    change g⁻¹ * ψ x * g = r
    rw [hx]
    group
  have hcomp : R.subtype.comp π = (MulAut.conj g⁻¹).toMonoidHom.comp ψ := rfl
  have hconj := factorsFinrankLe_comp_conj ρ ψ g⁻¹ hψ
  apply factorsFinrankLe_of_comp_surjective (ρ.comp R.subtype) π hπ
  simpa only [MonoidHom.comp_assoc, hcomp] using hconj

theorem factorsFinrankLe_binary_all_roots
    [Fintype K] [CharP k 2] [IsAlgClosed k] {e : ℕ}
    (hK : Fintype.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [Algebra (ZMod 2) k]
    {y : StatedSp 3 K} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ y - 1)) < 3 * e)
    (hρ : Function.Injective ρ) (i : Fin 3) :
    FactorsFinrankLe ((extendScalars k ρ).comp
      ((spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i).subtype) 2 := by
  classical
  let : Algebra (ZMod 2) K := (ZMod.castHom (dvd_refl 2) K).toAlgebra
  let π : StatedSp 3 K →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := repLinEquiv ρ
      map_one' := repLinEquiv_one ρ
      map_mul' := repLinEquiv_mul ρ }
  have hπ : Function.Injective π := by
    intro a b hab
    apply hρ
    ext w
    exact congrArg (fun f : W ≃ₗ[ZMod 2] W => f w) hab
  obtain ⟨g, z, hg⟩ := exists_conj_eq_spEmbed_of_dispRank_lt
    (by rwa [Nat.card_eq_fintype_card]) he π hπ hy hsmall
  have hz : z * z = 1 := by
    apply spEmbed_injective (Fin.succ_injective 2)
    rw [map_mul, map_one, ← hg]
    calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy, mul_one, mul_inv_cancel]
  have hz1 : z ≠ 1 := by
    intro hz1
    rw [hz1, map_one] at hg
    apply hy1
    have heq := congrArg (fun a : StatedSp 3 K => g⁻¹ * a * g) hg
    simpa [mul_assoc] using heq
  let σ : Representation (ZMod 2) (StatedSp 3 K) W :=
    ρ.comp (MulAut.conj g⁻¹).toMonoidHom
  let ε := spEmbed (K := K) Fin.succ (Fin.succ_injective 2)
  have hsmallσ : finrank (ZMod 2) (LinearMap.range (σ (ε z) - 1)) < 3 * e := by
    have heq : g⁻¹ * ε z * g = y := by rw [← hg]; group
    have hlin : σ (ε z) = ρ y := by
      change ρ (g⁻¹ * ε z * g) = ρ y
      rw [heq]
    have hfr : finrank (ZMod 2) (LinearMap.range (σ (ε z) - 1)) =
        finrank (ZMod 2) (LinearMap.range (ρ y - 1)) :=
      congrArg (fun a : W →ₗ[ZMod 2] W =>
        finrank (ZMod 2) (LinearMap.range (a - 1))) hlin
    exact hfr.trans_lt hsmall
  have hblocks : ∀ b : Bool, FactorsFinrankLe ((extendScalars k σ).comp
      (ε.comp (rootBlock b))) 2 := fun b =>
    factorsFinrankLe_extend_standard_blocks hK he σ hz hz1 hsmallσ b
  have hroots := factorsFinrankLe_all_roots (extendScalars k σ) hblocks i
  exact factorsFinrankLe_extend_comp_conj ρ g _ hroots


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
