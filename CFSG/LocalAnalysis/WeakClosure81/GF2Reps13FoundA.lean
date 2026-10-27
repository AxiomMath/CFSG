module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private abbrev w16g_phiHom (b : MulAut W) : W →* W :=
  MonoidHom.mk' (fun w => b w * w⁻¹) (by
    intro x y
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    ac_rfl)

private theorem w16g_phiHom_apply (b : MulAut W) (w : W) : w16g_phiHom b w = b w * w⁻¹ :=
  rfl

private theorem w16g_phi_gen (A B : Subgroup (MulAut W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {b : MulAut W} (hb : b ∈ B) {a : MulAut W} (ha : a ∈ A)
    {U : Subgroup W} {u : W} (hu : u ∈ U) :
    w16g_phiHom b (a u * u⁻¹) ∈ commSub (commSub U B) A := by
  have hbu : w16g_phiHom b u ∈ commSub U B :=
    Subgroup.subset_closure ⟨b, hb, u, hu, (w16g_phiHom_apply b u).symm⟩
  have heq : w16g_phiHom b (a u * u⁻¹) = w16g_phiHom a (w16g_phiHom b u) := by
    have hab : a (b u) = b (a u) := by
      simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f u) (hcomm a ha b hb)
    simp only [w16g_phiHom_apply, map_mul, map_inv, mul_inv_rev, inv_inv]
    rw [hab]
    simp only [mul_assoc]
    rw [mul_left_comm ((a u)⁻¹) u ((b u)⁻¹), mul_comm ((a u)⁻¹) ((b u)⁻¹),
      mul_left_comm ((b u)⁻¹) u ((a u)⁻¹)]
  rw [heq]
  exact Subgroup.subset_closure
    ⟨a, ha, w16g_phiHom b u, hbu, (w16g_phiHom_apply a (w16g_phiHom b u)).symm⟩

private theorem w16g_commSub_le (A B : Subgroup (MulAut W)) (hAB : ⁅A, B⁆ = ⊥) (U : Subgroup W) :
    commSub (commSub U A) B ≤ commSub (commSub U B) A := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB) ha) b hb).symm
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨b, hb, c, hc, rfl⟩
  rw [commSub] at hc
  exact Subgroup.closure_induction
    (p := fun c _ => w16g_phiHom b c ∈ commSub (commSub U B) A)
    (fun x hx => by
      obtain ⟨a, ha, u, hu, hxu⟩ := hx
      rw [← hxu]
      exact w16g_phi_gen A B hcomm hb ha hu)
    (by simp [w16g_phiHom])
    (fun x y _ _ ihx ihy => by
      rw [map_mul]
      exact (commSub (commSub U B) A).mul_mem ihx ihy)
    (fun x _ ihx => by
      rw [map_inv]
      exact (commSub (commSub U B) A).inv_mem ihx)
    hc

theorem s13_commSub_comm (A B : Subgroup (MulAut W)) (hAB : ⁅A, B⁆ = ⊥) (U : Subgroup W) :
    commSub (commSub U A) B = commSub (commSub U B) A :=
  le_antisymm (w16g_commSub_le A B hAB U)
    (w16g_commSub_le B A (by rw [Subgroup.commutator_comm]; exact hAB) U)

private theorem w16g_mem_perfect_chain (R : Subgroup (MulAut W)) (hR : ⁅R, R⁆ = R)
    (Y₀ Y₁ Y : Subgroup W) (h1 : commSub Y₁ R ≤ Y₀) (h2 : commSub Y R ≤ Y₁)
    {r : MulAut W} (hr : r ∈ R) {y : W} (hy : y ∈ Y) : r y * y⁻¹ ∈ Y₀ := by
  haveI : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  let θ : ↥R →* W ⧸ Y₀ :=
    { toFun := fun s => QuotientGroup.mk ((s : MulAut W) y * y⁻¹)
      map_one' := by simp
      map_mul' := by
        intro s t
        have ht : (t : MulAut W) y * y⁻¹ ∈ Y₁ :=
          h2 (Subgroup.subset_closure ⟨(t : MulAut W), t.2, y, hy, rfl⟩)
        have hs : (s : MulAut W) ((t : MulAut W) y * y⁻¹) *
            ((t : MulAut W) y * y⁻¹)⁻¹ ∈ Y₀ :=
          h1 (Subgroup.subset_closure ⟨(s : MulAut W), s.2, _, ht, rfl⟩)
        have hquot : ((s : MulAut W) ((t : MulAut W) y * y⁻¹) : W ⧸ Y₀) =
            (((t : MulAut W) y * y⁻¹ : W) : W ⧸ Y₀) := by
          rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
          exact hs
        have hEq1 : ((s * t : ↥R) : MulAut W) y * y⁻¹ =
            (s : MulAut W) ((t : MulAut W) y * y⁻¹) *
              ((s : MulAut W) y * y⁻¹) := by
          rw [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          group
        show QuotientGroup.mk (((s * t : ↥R) : MulAut W) y * y⁻¹) =
          QuotientGroup.mk ((s : MulAut W) y * y⁻¹) *
            QuotientGroup.mk ((t : MulAut W) y * y⁻¹)
        rw [hEq1, QuotientGroup.mk_mul, hquot]
        exact mul_comm _ _ }
  have hmem : (⟨r, hr⟩ : ↥R) ∈ θ.ker :=
    Abelianization.commutator_subset_ker θ Group.IsPerfect.mem_commutator
  have hθ : θ ⟨r, hr⟩ = 1 := MonoidHom.mem_ker.mp hmem
  have h1' : QuotientGroup.mk (r y * y⁻¹) = (1 : W ⧸ Y₀) := by
    show θ ⟨r, hr⟩ = 1
    exact hθ
  exact (QuotientGroup.eq_one_iff (r y * y⁻¹)).mp h1'

theorem s13_perfect_chain (R : Subgroup (MulAut W)) (hR : ⁅R, R⁆ = R) (Y₀ Y₁ Y : Subgroup W)
    (h1 : commSub Y₁ R ≤ Y₀) (h2 : commSub Y R ≤ Y₁) : commSub Y R ≤ Y₀ := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨r, hr, y, hy, rfl⟩
  exact w16g_mem_perfect_chain R hR Y₀ Y₁ Y h1 h2 hr hy

end CFSG.LocalAnalysis.WeakClosure81
