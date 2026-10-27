module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestMatrix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial

namespace SLNSRest

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
  {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem exists_sl_of_innerDiag (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F - 1) {b : G} (hbp : b ^ p = 1)
    (hb : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b⁻¹) :
    ∃ X : Matrix.SpecialLinearGroup (Fin (m + 1)) F, X ^ p = 1 ∧ b = ψ X := by
  obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker hb
  have hbp' : b⁻¹ ^ p = 1 := by rw [inv_pow, hbp, inv_one]
  obtain ⟨A', hA'p, hA'⟩ := OrdPRest.exists_pow_eq_one hker hA hbp'
    fun c _ => OrdPNS.exists_pow_eq hp hpF c
  have hdet : (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 :=
    OrdPNS.det_eq_one_of_pow_eq_one hp hpF (by rw [← Units.val_pow_eq_pow_val, hA'p, Units.val_one])
  set X : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ⟨A', hdet⟩ with hX
  have hXGL : Matrix.SpecialLinearGroup.toGL X = A' := Units.ext rfl
  have hXp : X ^ p = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, hXGL, hA'p, map_one]
  refine ⟨X, hXp, ?_⟩
  have hconj : ∀ u, InnerDiagA.conjSL A' u = X * u * X⁻¹ := by
    intro u
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, hXGL]
  have hmem : (ψ X)⁻¹ * b ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have h1 := hA' u
    rw [inv_inv, hconj, map_mul, map_mul, map_inv] at h1
    calc ψ u * ((ψ X)⁻¹ * b) = (ψ X)⁻¹ * (ψ X * ψ u * (ψ X)⁻¹) * b := by group
      _ = (ψ X)⁻¹ * (b * ψ u * b⁻¹) * b := by rw [h1]
      _ = (ψ X)⁻¹ * b * ψ u := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

omit [CharP F 2] in
theorem commute_of_map_eq (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F - 1) {X Y : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hXp : X ^ p = 1) (h : ψ X * ψ Y = ψ Y * ψ X) : X * Y = Y * X := by
  set z := (Y * X)⁻¹ * (X * Y) with hz
  have hzk : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, h, inv_mul_cancel]
  have hzc := hker hzk
  have hXY : X * Y = Y * X * z := by rw [hz]; group
  have hconj : Y⁻¹ * X * Y = X * z := by
    calc Y⁻¹ * X * Y = Y⁻¹ * (X * Y) := by group
      _ = Y⁻¹ * (Y * X * z) := by rw [hXY]
      _ = X * z := by group
  have hzp : z ^ p = 1 := by
    have h1 : (Y⁻¹ * X * Y) ^ p = (X * z) ^ p := by rw [hconj]
    have h2 : (Y⁻¹ * X * Y) ^ p = Y⁻¹ * X ^ p * Y := by
      have := _root_.conj_pow (a := Y⁻¹) (b := X) (i := p)
      rwa [inv_inv] at this
    have h3 : (X * z) ^ p = X ^ p * z ^ p :=
      (Commute.mul_pow (Subgroup.mem_center_iff.mp hzc X) p)
    rw [h2, h3, hXp, mul_one, inv_mul_cancel, one_mul] at h1
    exact h1.symm
  have hz1 : z = 1 := by
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzc
    have hcp : c ^ p = 1 := by
      have h1 := congrArg (fun t : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
        (t : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 0) hzp
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, one_apply_eq, ← hc] at h1
      rwa [scalar_apply, diagonal_pow, diagonal_apply_eq] at h1
    have hc1 := OrdPNS.eq_one_of_pow_eq_one hp hpF hcp
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  rw [hXY, hz1, mul_one]

end SLNSRest

section Inputs

theorem ggSLNonsplitFrameInput_holds : GGSLNonsplitFrameInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx s1 hns
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hX : ∀ b : Bs, ∃ X : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
      X ^ p = 1 ∧ (b : G) = ψ X := fun b =>
    SLNSRest.exists_sl_of_innerDiag hm hker hCψ hp hpF (hctx.2.1.2.1.2 b b.2)
      (hctx.2.2.2.2.2.2.1.2 _ (Bs.inv_mem b.2))
  choose X hXp hXb using hX
  have hXc : ∀ b c : Bs, X b * X c = X c * X b := fun b c =>
    SLNSRest.commute_of_map_eq hker hp hpF (hXp b) (by
      have h := TableB.IsElemAbelian.comm hctx.2.1.2.1 b.2 c.2
      rw [hXb b, hXb c] at h
      exact h)
  obtain ⟨e, s, r, C, hC, ε, A₀, hCp, hCunit, hframe⟩ :=
    NSFrame.exists_nsFrame hp hpF hpK
      (Set.range fun b : Bs => (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
      (by
        rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
        change (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X c : _) =
          (X c : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X b : _)
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hXc])
      (by
        rintro _ ⟨b, rfl⟩
        rw [← Matrix.SpecialLinearGroup.coe_pow, hXp, Matrix.SpecialLinearGroup.coe_one])
  refine ⟨e, s, r, C, hC, ε, A₀, hCp, hCunit, fun b hb => ?_⟩
  obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
  refine ⟨k, ?_⟩
  have h1 : X ⟨b, hb⟩ * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
  have h2 : X ⟨b, hb⟩ = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
    rw [← h1, mul_inv_cancel_right]
  exact (hXb ⟨b, hb⟩).trans (congrArg ψ h2)

theorem ggSixRootFusionSLRepNonsplitInput_of_twoBlock (h2 : GGNSTwoBlockPermInput) :
    GGSixRootFusionSLRepNonsplitInput :=
  ggSixRootFusionSLRepNonsplitInput_of_frame ggSLNonsplitFrameInput_holds h2

end Inputs

end CFSG.StandardType
