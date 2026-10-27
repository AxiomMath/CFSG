module

public import CFSG.Quasithin.Background.F7TwoInvL3Inner
public import CFSG.Quasithin.Background.F7TwoInvL3Graph
public import CFSG.Quasithin.Background.Harris.KFact2d.F6Common

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem invAutGen_of_statedPSL3
    {L : Type} [Group L] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : StatedClassicalModel L .PSL 3 p 1) :
    ∀ φ : MulAut L, φ * φ = 1 → φ ≠ 1 → InvAutGen L φ := by
  intro φ hφ2 hφ1
  obtain ⟨hnt, hs⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity L 3 p 1 h
  have hfin : Finite L := CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
  obtain ⟨e⟩ : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p)) := by
    obtain ⟨-, F, hF, hFin, hcard, ⟨eK⟩⟩ := h
    let _ : Fintype F := Fintype.ofFinite F
    let _ : Fintype (ZMod p) := Fintype.ofFinite (ZMod p)
    have hc : Fintype.card F = Fintype.card (ZMod p) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, pow_one, Nat.card_zmod]
    exact ⟨eK.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
          (FiniteField.ringEquivOfCardEq hc) (Fin 3)))⟩
  let θ : SpecialLinearGroup (Fin 3) (ZMod p) →* L :=
    e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod p))))
  have hθ : Function.Surjective θ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hθk : θ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod p)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod p))) x = 1 :=
      (MulEquiv.map_eq_one_iff e.symm).mp hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := ZMod p) (n := 3) le_rfl
  have hnonab : ∃ x y : L, x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    let _ : CommGroup L := { ‹Group L› with mul_comm := hcomm }
    have hker : (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) ≤ θ.ker := by
      rw [← hperf.commutator_eq_top]
      exact Abelianization.commutator_subset_ker θ
    obtain ⟨a, b, hab⟩ := exists_pair_ne L
    obtain ⟨x, rfl⟩ := hθ a
    obtain ⟨y, rfl⟩ := hθ b
    exact hab ((MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))).trans
      (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top y))).symm)
  have hcl := CFSG.Quasithin.Background.Harris.KFact2d.linClass_zmod_all (p := p) hp2
  obtain ⟨α, g, φf, ε, hα, hf⟩ := hcl L θ hθ hθk φ
  have hφf : φf = RingEquiv.refl _ := Subsingleton.elim _ _
  subst hφf
  have hmap : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (RingEquiv.refl (ZMod p)).mapMatrix M = M := fun M => by ext; rfl
  have hgg : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hαα : α.comp α = MonoidHom.id _ :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.lift_comp_self_eq_id hθk
      (σ := φ) (fun x => by
        have := MulEquiv.congr_fun hφ2 x
        simpa using this) hα
  have hααx : ∀ x, α (α x) = x := fun x => DFunLike.congr_fun hαα x
  have hα' : ∀ x, φ (θ x) = θ (α x) := fun x => (hα x).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  cases ε
  ·
    have hfm : ∀ x : SpecialLinearGroup (Fin 3) (ZMod p),
        ((α x : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * (x : Matrix (Fin 3) (Fin 3) (ZMod p)) *
            ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      intro x
      simpa [hmap] using hf x
    have hsq := sq_scalar_of_inner_lift (g : Matrix (Fin 3) (Fin 3) (ZMod p))
      ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) hgg hgg' (fun x => by
        have h1 : ((α (α x) : SpecialLinearGroup (Fin 3) (ZMod p)) :
            Matrix (Fin 3) (Fin 3) (ZMod p)) = (x : Matrix (Fin 3) (Fin 3) (ZMod p)) :=
          congrArg (fun y : SpecialLinearGroup (Fin 3) (ZMod p) =>
            (y : Matrix (Fin 3) (Fin 3) (ZMod p))) (hααx x)
        rw [hfm, hfm] at h1
        exact h1)
    exact invAutGen_of_inner_lift h2 hodd hs hnonab θ hθ hφ2 hφ1 α hα' _ _ hgg hfm hsq
  ·
    have hfm : ∀ x : SpecialLinearGroup (Fin 3) (ZMod p),
        ((α x : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
            (((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) :
              Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ *
            ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      intro x
      simpa [hmap] using hf x
    exact invAutGen_of_graph_lift hp2 hs hnonab θ hθ hφ2 hφ1 α hα' hααx _ _ hgg hgg' hfm

end CFSG.Quasithin.F7Two
