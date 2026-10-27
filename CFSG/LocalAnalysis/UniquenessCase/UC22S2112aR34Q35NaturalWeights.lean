module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalBlocks
public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Γ : Type*} [Group Γ]

private lemma glRep_injective_apply (g : GL ι K) :
    Function.Injective (glRep (AlgebraicClosure K) g) := by
  have hleft : Function.LeftInverse (glRep (AlgebraicClosure K) g⁻¹)
      (glRep (AlgebraicClosure K) g) := by
    intro v
    have h : glRep (AlgebraicClosure K) g⁻¹ * glRep (AlgebraicClosure K) g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    exact congrArg
      (fun T : Module.End (AlgebraicClosure K) (ι → AlgebraicClosure K) => T v) h
  exact Function.LeftInverse.injective hleft

private lemma glRep_map_ne_bot (g : GL ι K)
    {p : Submodule (AlgebraicClosure K) (ι → AlgebraicClosure K)} (hp : p ≠ ⊥) :
    p.map (glRep (AlgebraicClosure K) g) ≠ ⊥ := by
  have hmapinj : Function.Injective (Submodule.map (glRep (AlgebraicClosure K) g)) :=
    Submodule.map_injective_of_injective (glRep_injective_apply (K := K) g)
  intro hbot
  exact hp (hmapinj (by rw [hbot, Submodule.map_bot]))

private lemma two_pow_cast_ne_zero (hK : ringChar K ≠ 2) (n : ℕ) :
    ((2 ^ n : ℕ) : AlgebraicClosure K) ≠ 0 := by
  have h2 : (2 : AlgebraicClosure K) ≠ 0 := by
    have hchar : ringChar (AlgebraicClosure K) ≠ 2 := by
      rw [← Algebra.ringChar_eq K (AlgebraicClosure K)]
      exact hK
    exact Ring.two_ne_zero hchar
  rw [Nat.cast_pow]
  exact pow_ne_zero n h2

theorem exists_blocks_of_not_le_scalars [Finite Γ] (hK : ringChar K ≠ 2) (ρ : Γ →* GL ι K)
    {A : Subgroup Γ} [A.Normal] (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : IsPGroup 2 A)
    (hns : ¬ A ≤ (StatedScalars ι K).comap ρ) :
    ∃ (κ : Type) (W : κ → Submodule (AlgebraicClosure K) (ι → AlgebraicClosure K)),
      Nontrivial κ ∧ iSupIndep W ∧ (⨆ i, W i = ⊤) ∧ (∀ i, W i ≠ ⊥) ∧
      ∀ g : Γ, ∀ i, ∃ j, (W i).map (glRep (AlgebraicClosure K) (ρ g)) = W j := by
  classical
  let L := AlgebraicClosure K
  let E := ι → L
  let f : A → Module.End L E := fun a => glRep L (ρ a)
  have hι : Nonempty ι := by
    by_contra hempty
    have hempty' : IsEmpty ι := not_nonempty_iff.mp hempty
    apply hns
    intro a _
    have hρa : ρ a = 1 := by
      apply Units.ext
      funext i
      exact (hempty'.false i).elim
    show ρ a ∈ (Matrix.GeneralLinearGroup.scalar ι).range
    refine ⟨1, ?_⟩
    rw [map_one]
    exact hρa.symm
  have hss : ∀ a : A, (f a).IsFinitelySemisimple := by
    intro a
    obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hA2 a
    have hnΓ : (a : Γ) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hnρ : (ρ a) ^ (2 ^ n) = 1 := by rw [← map_pow, hnΓ, map_one]
    have hf : f a ^ (2 ^ n) = 1 := by
      change glRep L (ρ a) ^ (2 ^ n) = 1
      rw [← map_pow, hnρ, map_one]
    exact CFSG.ABGLocalTools.isFinitelySemisimple_of_pow_eq_one hf (two_pow_cast_ne_zero hK n)
  have hcomm : ∀ a b : A, Commute (f a) (f b) := by
    intro a b
    show f a * f b = f b * f a
    change glRep L (ρ a) * glRep L (ρ b) = glRep L (ρ b) * glRep L (ρ a)
    calc
      glRep L (ρ a) * glRep L (ρ b) = glRep L (ρ a * ρ b) :=
        (map_mul (glRep L) (ρ a) (ρ b)).symm
      _ = glRep L (ρ b * ρ a) := by
        congr 1
        simpa only [map_mul] using congrArg ρ (hA a a.2 b b.2)
      _ = glRep L (ρ b) * glRep L (ρ a) := map_mul (glRep L) (ρ b) (ρ a)
  have hdecomp := CFSG.ABGLocalTools.iSupIndep_iInf_eigenspace_and_iSup_eq_top f hcomm hss
  let V : (A → L) → Submodule L E := fun χ => ⨅ a, (f a).eigenspace (χ a)
  let κ := {W : Submodule L E // W ≠ ⊥ ∧ ∃ χ : A → L, W = V χ}
  let W : κ → Submodule L E := fun i => i.1
  let χi : κ → A → L := fun i => Classical.choose i.2.2
  have hχi : ∀ i, W i = V (χi i) := fun i => Classical.choose_spec i.2.2
  have hχinj : Function.Injective χi := by
    intro i j hij
    apply Subtype.ext
    change W i = W j
    rw [hχi i, hχi j, hij]
  have hind : iSupIndep W := by
    have hW_eq : W = fun i => V (χi i) := funext hχi
    rw [hW_eq]
    exact hdecomp.1.comp hχinj
  have htop : ⨆ i : κ, W i = ⊤ := by
    rw [← hdecomp.2]
    refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun χ => ?_)
    · rw [hχi i]
      exact le_iSup V (χi i)
    · by_cases hχ : V χ = ⊥
      · have hχ' : (⨅ a, (f a).eigenspace (χ a)) = ⊥ := hχ
        change (⨅ a, (f a).eigenspace (χ a)) ≤ ⨆ i, W i
        rw [hχ']
        exact bot_le
      · exact le_iSup W ⟨V χ, hχ, χ, rfl⟩
  have hne : ∀ i : κ, W i ≠ ⊥ := fun i => i.2.1
  have hntriv : Nontrivial κ := by
    by_contra hsingle
    rw [not_nontrivial_iff_subsingleton] at hsingle
    have htop_ne_bot : (⊤ : Submodule L E) ≠ ⊥ := by
      intro h
      have hmem : (Pi.single hι.some (1 : L) : E) ∈ (⊥ : Submodule L E) := by
        rw [← h]
        exact Submodule.mem_top
      have hzero : (Pi.single hι.some (1 : L) : E) = 0 := (Submodule.mem_bot L).mp hmem
      have h1 : (1 : L) = 0 := by
        have := congrFun hzero hι.some
        simp at this
      exact one_ne_zero h1
    have hκne : Nonempty κ := by
      have hnot : ¬ ∀ χ : A → L, V χ = ⊥ := by
        intro hall
        have hbot : (⨆ χ : A → L, V χ) = ⊥ := iSup_eq_bot.mpr hall
        rw [hdecomp.2] at hbot
        exact htop_ne_bot hbot
      rw [not_forall] at hnot
      obtain ⟨χ, hχ⟩ := hnot
      exact ⟨⟨V χ, hχ, χ, rfl⟩⟩
    obtain ⟨i₀⟩ := hκne
    have htopW : W i₀ = ⊤ := by
      have hsup : ⨆ i : κ, W i = W i₀ := by
        refine le_antisymm (iSup_le fun i => ?_) (le_iSup W i₀)
        rw [hsingle.allEq i i₀]
      rw [← htop, hsup]
    have hVtop : V (χi i₀) = ⊤ := by
      rw [← hχi i₀, htopW]
    have hscalar : ∀ a : A, f a = (χi i₀ a) • (1 : Module.End L E) := by
      intro a
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ V (χi i₀) := by rw [hVtop]; exact Submodule.mem_top
      have hv' : v ∈ ⨅ b, (f b).eigenspace (χi i₀ b) := hv
      have hmem : v ∈ (f a).eigenspace (χi i₀ a) :=
        (Submodule.mem_iInf (fun b => (f b).eigenspace (χi i₀ b))).mp hv' a
      rw [Module.End.mem_eigenspace_iff] at hmem
      simpa using hmem
    have hmatrix : ∀ a : Γ, a ∈ A → ρ a ∈ (Matrix.GeneralLinearGroup.scalar ι).range := by
      intro a ha
      let ca : L := χi i₀ ⟨a, ha⟩
      have hfa : f ⟨a, ha⟩ = ca • (1 : Module.End L E) := hscalar ⟨a, ha⟩
      have hcol : ∀ j : ι, (ρ a : Matrix ι ι K).map (algebraMap K L) *ᵥ (Pi.single j (1 : L)) =
          ca • (Pi.single j (1 : L)) := by
        intro j
        have h := congrArg (fun T : Module.End L E => T (Pi.single j (1 : L))) hfa
        rw [show f ⟨a, ha⟩ (Pi.single j (1 : L)) =
              (ρ a : Matrix ι ι K).map (algebraMap K L) *ᵥ Pi.single j (1 : L) by
            rw [glRep_apply]] at h
        simpa using h
      have hM' : (ρ a : Matrix ι ι K).map (algebraMap K L) = ca • (1 : Matrix ι ι L) := by
        ext i j
        have h := congrFun (hcol j) i
        rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply] at h
        by_cases hij : i = j
        · subst hij
          simpa using h
        · rw [Pi.single_eq_of_ne hij, smul_zero] at h
          rw [h, Matrix.smul_apply, Matrix.one_apply, if_neg hij, smul_zero]
      let c : K := (ρ a : Matrix ι ι K) hι.some hι.some
      have hdiag : algebraMap K L c = ca := by
        have h := congrFun (congrFun hM' hι.some) hι.some
        simpa [c, ca, Matrix.map_apply] using h
      have hMK : (ρ a : Matrix ι ι K) = c • (1 : Matrix ι ι K) := by
        have hmap : (c • (1 : Matrix ι ι K)).map (algebraMap K L) =
            (ρ a : Matrix ι ι K).map (algebraMap K L) := by
          rw [hM']
          ext i j
          rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.smul_apply,
            Matrix.one_apply]
          by_cases hij : i = j <;> simp [hij, hdiag]
        exact (Matrix.map_injective (algebraMap K L).injective hmap).symm
      have hunit : IsUnit (ρ a : Matrix ι ι K) := (ρ a).isUnit
      have h01 : (0 : Matrix ι ι K) ≠ 1 := by
        intro h
        have := congrFun (congrFun h hι.some) hι.some
        simp at this
      have hc : c ≠ 0 := by
        intro hc0
        have hM0 : (ρ a : Matrix ι ι K) = 0 := by rw [hMK, hc0, zero_smul]
        obtain ⟨u, hu⟩ := hunit
        have hu0 : (↑u : Matrix ι ι K) = 0 := hu.trans hM0
        have hone : (↑u : Matrix ι ι K) * (↑(u⁻¹) : Matrix ι ι K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [hu0, zero_mul] at hone
        exact h01 hone
      refine ⟨Units.mk0 c hc, ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      show Matrix.scalar ι c = (ρ a : Matrix ι ι K)
      rw [hMK, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    exact hns fun a ha => hmatrix a ha
  have hperm : ∀ g : Γ, ∀ i : κ, ∃ j : κ, (W i).map (glRep L (ρ g)) = W j := by
    intro g i
    let χ : A → L := χi i
    have hχ : W i = V χ := hχi i
    have hχne : V χ ≠ ⊥ := by rw [← hχ]; exact i.2.1
    have hmemA : ∀ a : A, g⁻¹ * (a : Γ) * g ∈ A := fun a =>
      by simpa using Subgroup.Normal.conj_mem (H := A) ‹A.Normal› (a : Γ) a.2 g⁻¹
    have hmemA' : ∀ a : A, g * (a : Γ) * g⁻¹ ∈ A := fun a =>
      Subgroup.Normal.conj_mem ‹A.Normal› (a : Γ) a.2 g
    let χ' : A → L := fun a => χ ⟨g⁻¹ * (a : Γ) * g, hmemA a⟩
    have hχ'' : (fun a : A => χ' ⟨g * (a : Γ) * g⁻¹, hmemA' a⟩) = χ := by
      funext a
      apply congrArg χ
      apply Subtype.ext
      group
    have hle : (V χ).map (glRep L (ρ g)) ≤ V χ' := by
      rintro v ⟨u, hu, rfl⟩
      have hu' : u ∈ ⨅ a, (f a).eigenspace (χ a) := hu
      change glRep L (ρ g) u ∈ ⨅ a, (f a).eigenspace (χ' a)
      rw [Submodule.mem_iInf]
      intro a
      rw [Module.End.mem_eigenspace_iff]
      have hconj : glRep L (ρ a) * glRep L (ρ g) =
          glRep L (ρ g) * glRep L (ρ (g⁻¹ * (a : Γ) * g)) := by
        rw [← map_mul (glRep L) (ρ a) (ρ g),
          ← map_mul (glRep L) (ρ g) (ρ (g⁻¹ * (a : Γ) * g))]
        congr 1
        rw [← map_mul ρ (a : Γ) g, ← map_mul ρ g (g⁻¹ * (a : Γ) * g)]
        congr 1
        group
      have hstep : f a (glRep L (ρ g) u) =
          glRep L (ρ g) (f ⟨g⁻¹ * (a : Γ) * g, hmemA a⟩ u) := by
        exact congrArg (fun T : Module.End L E => T u) hconj
      have hua : f ⟨g⁻¹ * (a : Γ) * g, hmemA a⟩ u =
          χ ⟨g⁻¹ * (a : Γ) * g, hmemA a⟩ • u :=
        (Module.End.mem_eigenspace_iff).mp
          ((Submodule.mem_iInf (fun b => (f b).eigenspace (χ b))).mp hu'
            ⟨g⁻¹ * (a : Γ) * g, hmemA a⟩)
      rw [hstep, hua, map_smul]
    have hle' : (V χ').map (glRep L (ρ g⁻¹)) ≤ V χ := by
      rintro v ⟨u, hu, rfl⟩
      have hu' : u ∈ ⨅ a, (f a).eigenspace (χ' a) := hu
      change glRep L (ρ g⁻¹) u ∈ ⨅ a, (f a).eigenspace (χ a)
      rw [Submodule.mem_iInf]
      intro a
      rw [Module.End.mem_eigenspace_iff]
      have hconj : glRep L (ρ a) * glRep L (ρ g⁻¹) =
          glRep L (ρ g⁻¹) * glRep L (ρ (g * (a : Γ) * g⁻¹)) := by
        rw [← map_mul (glRep L) (ρ a) (ρ g⁻¹),
          ← map_mul (glRep L) (ρ g⁻¹) (ρ (g * (a : Γ) * g⁻¹))]
        congr 1
        rw [← map_mul ρ (a : Γ) g⁻¹, ← map_mul ρ g⁻¹ (g * (a : Γ) * g⁻¹)]
        congr 1
        group
      have hstep : f a (glRep L (ρ g⁻¹) u) =
          glRep L (ρ g⁻¹) (f ⟨g * (a : Γ) * g⁻¹, hmemA' a⟩ u) := by
        exact congrArg (fun T : Module.End L E => T u) hconj
      have hua : f ⟨g * (a : Γ) * g⁻¹, hmemA' a⟩ u =
          χ' ⟨g * (a : Γ) * g⁻¹, hmemA' a⟩ • u :=
        (Module.End.mem_eigenspace_iff).mp
          ((Submodule.mem_iInf (fun b => (f b).eigenspace (χ' b))).mp hu'
            ⟨g * (a : Γ) * g⁻¹, hmemA' a⟩)
      have hχa : χ' ⟨g * (a : Γ) * g⁻¹, hmemA' a⟩ = χ a := congrFun hχ'' a
      rw [hstep, hua, map_smul, hχa]
    have hle_rev : V χ' ≤ (V χ).map (glRep L (ρ g)) := by
      intro v hv
      have hmem : glRep L (ρ g⁻¹) v ∈ V χ := hle' (Submodule.mem_map_of_mem hv)
      refine Submodule.mem_map.mpr ⟨glRep L (ρ g⁻¹) v, hmem, ?_⟩
      have hcomp : glRep L (ρ g) * glRep L (ρ g⁻¹) = 1 := by
        rw [← map_mul, map_inv, mul_inv_cancel, map_one]
      simp
    have heq : (V χ).map (glRep L (ρ g)) = V χ' := le_antisymm hle hle_rev
    have hne' : V χ' ≠ ⊥ := by
      rw [← heq]
      exact glRep_map_ne_bot (ρ g) hχne
    refine ⟨⟨V χ', hne', χ', rfl⟩, ?_⟩
    rw [hχ]
    exact heq
  exact ⟨κ, W, hntriv, hind, htop, hne, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
