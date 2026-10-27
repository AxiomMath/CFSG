module

public import CFSG.Quasithin.Background.SmithB45HM22Ind
public import CFSG.Quasithin.Background.SmithB45HM22Check

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat Module Matrix

theorem closure_g1_g2 : Subgroup.closure ({g1, g2} : Set ↥hatM22Γ₀) = ⊤ := by
  have h : Subgroup.closure
      ((Subtype.val : ↥hatM22Γ₀ → Matrix.GeneralLinearGroup (Fin 6) FieldFour) ⁻¹'
        {hatM22G1, hatM22G2}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [← h]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h1 | h1)
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

theorem forall_of_gens (p : ↥hatM22Γ₀ → Prop) (h1 : p 1) (hg : ∀ b, p (genb b))
    (hmul : ∀ g h, p g → p h → p (g * h)) : ∀ g, p g := by
  refine forall_of_closure closure_g1_g2 p h1 ?_ hmul
  rintro s (rfl | rfl)
  · exact hg false
  · exact hg true

section Rep

variable {W : Type*} [AddCommGroup W] [Module FieldFour W]
  (ρ : Representation FieldFour ↥hatM22Γ₀ W)

theorem inv_of_gens {U : Submodule FieldFour W} (hU : ∀ b, ∀ u ∈ U, ρ (genb b) u ∈ U) :
    ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
  refine forall_of_gens (fun g => ∀ u ∈ U, ρ g u ∈ U) (fun u hu => by simpa using hu) hU ?_
  intro g h hg hh u hu
  rw [map_mul, Module.End.mul_apply]
  exact hg _ (hh u hu)

theorem irredFam_of_isIrreducible [hρ : ρ.IsIrreducible] :
    IrredFam (fun b => ρ (genb b)) := by
  intro U hU
  let S : Subrepresentation ρ := ⟨U, fun g u hu => inv_of_gens ρ hU g u hu⟩
  rcases hρ.eq_bot_or_eq_top S with h0 | h0
  · left
    exact congrArg Subrepresentation.toSubmodule h0
  · right
    exact congrArg Subrepresentation.toSubmodule h0

variable {d : ℕ} {X : ↥hatH →* Matrix (Fin d) (Fin d) FieldFour} {blk : List ℤ → PM}

theorem frobMap_surjective [hρ : ρ.IsIrreducible]
    (hblk : ∀ (w : List ℤ) (hw : wordΓ w ∈ hatH), PM.toMat d d (blk w) = X (Blk.hOf hw))
    (ψ : (Fin d → FieldFour) →ₗ[FieldFour] W)
    (hψ : ∀ (h : ↥hatH) (y : Fin d → FieldFour), ψ (X h *ᵥ y) = ρ h (ψ y)) (hψ0 : ψ ≠ 0) :
    Function.Surjective (frobMap ρ ψ) := by
  rw [← LinearMap.range_eq_top]
  have hinv : ∀ b, ∀ u ∈ LinearMap.range (frobMap ρ ψ), ρ (genb b) u ∈
      LinearMap.range (frobMap ρ ψ) := by
    rintro b _ ⟨x, rfl⟩
    exact ⟨_, frobMap_gen ρ hblk ψ hψ b x⟩
  let S : Subrepresentation ρ := ⟨LinearMap.range (frobMap ρ ψ),
    fun g u hu => inv_of_gens ρ hinv g u hu⟩
  have hS : S ≠ ⊥ := by
    intro h0
    apply hψ0
    apply LinearMap.ext
    intro y
    have hy : ψ y ∈ S.toSubmodule := by
      refine ⟨fun j => ?_, ?_⟩
      · exact (if (finProdFinEquiv.symm j).1 = (0 : Fin 22) then y (finProdFinEquiv.symm j).2
          else 0)
      · rw [frobMap_block ρ ψ (s := 0) (by norm_num) _ y]
        · rw [tΓ_zero, map_one, Module.End.one_apply]
        · intro k c
          simp only [Equiv.symm_apply_apply]
          by_cases hk : k = 0
          · subst hk
            simp
          · have hk' : (k : ℕ) ≠ 0 := fun e => hk (Fin.ext e)
            simp [hk, hk']
    rw [h0] at hy
    exact (Submodule.mem_bot _).mp hy
  have := (hρ.eq_bot_or_eq_top S).resolve_left hS
  exact congrArg Subrepresentation.toSubmodule this

theorem jh_induced [ρ.IsIrreducible] [Nontrivial W]
    (hblk : ∀ (w : List ℤ) (hw : wordΓ w ∈ hatH), PM.toMat d d (blk w) = X (Blk.hOf hw))
    (ψ : (Fin d → FieldFour) →ₗ[FieldFour] W)
    (hψ : ∀ (h : ↥hatH) (y : Fin d → FieldFour), ψ (X h *ᵥ y) = ρ h (ψ y)) (hψ0 : ψ ≠ 0)
    {P Pi : PM} {ns : List ℕ} {stds₁ stds₂ : List PM}
    (hflag : flagOK (22 * d) (indP blk d false) (indP blk d true) P Pi ns stds₁ stds₂ = true)
    (hns0 : nsF ns 0 = 0) (hnsN : nsF ns (ns.length - 1) = 22 * d)
    (hmono : ∀ i < ns.length - 1, nsF ns i < nsF ns (i + 1))
    (hirr : ∀ i < ns.length - 1, IrredFam (pairOf (nsF ns (i + 1) - nsF ns i) (stds₁.getD i [])
      (stds₂.getD i []))) :
    ∃ i < ns.length - 1, ∃ Ψ : (Fin (nsF ns (i + 1) - nsF ns i) → FieldFour) ≃ₗ[FieldFour] W,
      ∀ (b : Bool) (s : Fin (nsF ns (i + 1) - nsF ns i) → FieldFour),
        Ψ (PM.toMat _ _ ((if b then stds₂ else stds₁).getD i []) *ᵥ s) = ρ (genb b) (Ψ s) := by
  obtain ⟨hP, hPi, hPPi, hb1, hb2⟩ := flagOK_parts hflag
  set N := 22 * d with hN
  let T : Bool → PM := fun b => PM.mul Pi (PM.mul (indP blk d b) P)
  have hT : ∀ b, PM.toMat N N (T b) =
      PM.toMat N N Pi * PM.toMat N N (indP blk d b) * PM.toMat N N P := by
    intro b
    simp only [T]
    rw [PM.toMat_mul _ _ hPi (by rw [PM.length_mul]; exact hP),
      PM.toMat_mul _ _ (length_indP blk d b) hP, Matrix.mul_assoc]
  have hblock : ∀ b, blockOK (T b) ns (if b then stds₂ else stds₁) = true := by
    intro b
    cases b
    · exact hb1
    · exact hb2
  let g : Bool → ((Fin N → FieldFour) →ₗ[FieldFour] (Fin N → FieldFour)) :=
    fun b => Matrix.toLin' (PM.toMat N N (T b))
  have hPPi' : PM.toMat N N Pi * PM.toMat N N P = 1 := mul_eq_one_comm.mp hPPi
  let φ : (Fin N → FieldFour) →ₗ[FieldFour] W :=
    (frobMap ρ ψ).comp (Matrix.toLin' (PM.toMat N N P))
  have hφ : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := frobMap_surjective ρ hblk ψ hψ hψ0 w
    refine ⟨PM.toMat N N Pi *ᵥ x, ?_⟩
    change frobMap ρ ψ (PM.toMat N N P *ᵥ (PM.toMat N N Pi *ᵥ x)) = _
    rw [Matrix.mulVec_mulVec, hPPi, Matrix.one_mulVec]
  have hφeq : ∀ b v, φ (g b v) = ρ (genb b) (φ v) := by
    intro b v
    change frobMap ρ ψ (PM.toMat N N P *ᵥ (PM.toMat N N (T b) *ᵥ v)) =
      ρ (genb b) (frobMap ρ ψ (PM.toMat N N P *ᵥ v))
    rw [hT, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPPi, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact frobMap_gen ρ hblk ψ hψ b _
  have hWne : (⊤ : Submodule FieldFour W) ≠ ⊥ := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    intro h
    have : w ∈ (⊤ : Submodule FieldFour W) := Submodule.mem_top
    rw [h] at this
    exact hw ((Submodule.mem_bot _).mp this)
  have hle : ∀ i, i + 1 ≤ ns.length - 1 → nsF ns (i + 1) ≤ N := by
    intro i hi
    rw [← hnsN]
    exact ns_mono' hmono (i + 1) (ns.length - 1) hi le_rfl
  obtain ⟨i, hi, Ψ, hΨ⟩ := jordanHolder_step (K := FieldFour) (nsF ns) (ns.length - 1) hns0
    hnsN hmono g (fun j hj b v hv => flagSub_inv_of_blockOK (hblock b) hns0 hmono hj hv)
    (fun j hj => by
      have hbl : ∀ b, blockW FieldFour N (nsF ns j) (nsF ns (j + 1) - nsF ns j) (g b) =
          pairOf (nsF ns (j + 1) - nsF ns j) (stds₁.getD j []) (stds₂.getD j []) b := by
        intro b
        rw [blockW_eq_of_blockOK (hblock b) hj (hle j hj) (hmono j hj).le]
        cases b <;> rfl
      have h := hirr j hj
      intro U hU
      exact h U fun b u hu => (hbl b) ▸ hU b u hu)
    (fun b => ρ (genb b)) (irredFam_of_isIrreducible ρ) hWne φ hφ hφeq
  refine ⟨i, hi, Ψ, fun b s => ?_⟩
  have h1 := hΨ b s
  rw [blockW_eq_of_blockOK (hblock b) hi (hle i hi) (hmono i hi).le] at h1
  exact h1

end Rep

end CFSG.Quasithin.HM22
