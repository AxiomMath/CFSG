module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CenterProofFast
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.StandardType.F4ExplicitPos.CenterCheckFast
variable {K : Type} [Field K] [CharP K 2]

def Bsub
    (K : Type) [Field K] : Subgroup (adjointGroup .F4 K) where
  carrier := {g | ∀ u w : RootModule Tag.F4 K,
    Bf K (((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) u)
      (((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) w) = Bf K u w}
  one_mem' := by intro u w; simp
  mul_mem' := by
    intro g h hg hh u w
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]
    rw [hg, hh]
  inv_mem' := by
    intro g hg u w
    have e : ∀ x : RootModule Tag.F4 K,
        (((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K))
          ((((g : ModGL .F4 K)⁻¹ : ModGL .F4 K) : Module.End K
            (RootModule Tag.F4 K)) x)) = x := fun x => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have h := hg
      ((((g : ModGL .F4 K)⁻¹ : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) u)
      ((((g : ModGL .F4 K)⁻¹ : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) w)
    rw [e, e] at h
    exact h.symm

theorem Bf_inv_all
    (g : adjointGroup .F4 K) (u w : RootModule Tag.F4 K) :
    Bf K (((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) u)
      (((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) w) = Bf K u w := by
  have hsub : (⊤ : Subgroup (adjointGroup .F4 K)) ≤ Bsub K := by
    set S : Set (ModGL .F4 K) := {g | ∃ (i : Fin Tag.F4.rank) (c : K),
      (g : Module.End K (RootModule Tag.F4 K)) = xOp .F4 K i c ∨
        (g : Module.End K (RootModule Tag.F4 K)) = yOp .F4 K i c} with hSdef
    have hcl : Subgroup.closure
        (((↑) : adjointGroup .F4 K → ModGL .F4 K) ⁻¹' S) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [← hcl, Subgroup.closure_le]
    rintro h ⟨i, c, hg | hg⟩
    · have hm : h ∈ Bsub K := by
        intro u w
        show Bf K (((h : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) u)
          (((h : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) w) = Bf K u w
        rw [show ((h : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) = xOp .F4 K i c
          from hg]
        exact xOp_Bf i c u w
      exact hm
    · have hm : h ∈ Bsub K := by
        intro u w
        show Bf K (((h : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) u)
          (((h : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) w) = Bf K u w
        rw [show ((h : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) = yOp .F4 K i c
          from hg]
        exact yOp_Bf i c u w
      exact hm
  exact hsub (Subgroup.mem_top g) u w

theorem center_adjointGroup_F4_charTwo_eq_bot :
    Subgroup.center (adjointGroup .F4 K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  set M : Module.End K (RootModule Tag.F4 K) :=
    ((z : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K)) with hMdef
  have hcx : ∀ i : Fin Tag.F4.rank, Commute M (xOp .F4 K i 1) := by
    intro i
    have h := Subgroup.mem_center_iff.1 hz
      ⟨xUnit .F4 K i 1, xUnit_mem_adjointGroup i 1⟩
    have h' := congrArg (fun g : adjointGroup .F4 K =>
      ((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K))) h
    simp only [Subgroup.coe_mul, Units.val_mul, coe_xUnit] at h'
    exact h'.symm
  have hcy : ∀ i : Fin Tag.F4.rank, Commute M (yOp .F4 K i 1) := by
    intro i
    have h := Subgroup.mem_center_iff.1 hz
      ⟨yUnit .F4 K i 1, yUnit_mem_adjointGroup i 1⟩
    have h' := congrArg (fun g : adjointGroup .F4 K =>
      ((g : ModGL .F4 K) : Module.End K (RootModule Tag.F4 K))) h
    simp only [Subgroup.coe_mul, Units.val_mul, coe_yUnit] at h'
    exact h'.symm
  have hcomm : ∀ g, g < 8 → Commute M (f4Gen K g) := by
    intro g hg
    cases h : f4GenY g
    · simpa [f4Gen, h] using hcx (f4GenI g)
    · simpa [f4Gen, h] using hcy (f4GenI g)
  obtain ⟨a, ha⟩ : ∃ a : K, M = a • (1 : Module.End K (RootModule Tag.F4 K)) :=
    ⟨_, eq_smul_one_of_commute_f4Gen M hcomm⟩
  have hB : Bf K (M (posVec Tag.F4 K 0)) (M (posVec Tag.F4 K 1)) =
      Bf K (posVec Tag.F4 K 0) (posVec Tag.F4 K 1) := by
    have := Bf_inv_all z (posVec Tag.F4 K 0) (posVec Tag.F4 K 1)
    simpa [hMdef] using this
  rw [ha] at hB
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hB
  rw [Bf_smul_left, Bf_smul_right, Bf_basis (by norm_num) (by norm_num),
    gramZ_zero_one, Int.cast_one, mul_one] at hB
  have haa : a * a = 1 := by simpa using hB
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : (a + 1) * (a + 1) = 0 := by
    have e : (a + 1) * (a + 1) = a * a + (a + a) + 1 := by ring
    rw [e, haa]
    have haa2 : a + a = 0 := by rw [← two_mul, h2, zero_mul]
    rw [haa2]
    have : (1 : K) + 0 + 1 = 0 := by rw [add_zero, ← two_mul, h2, zero_mul]
    exact this
  have ha1 : a = 1 := by
    have hz1 : a + 1 = 0 := mul_self_eq_zero.mp hsq
    rw [eq_neg_of_add_eq_zero_left hz1]
    exact neg_eq_of_add_eq_zero_left (by rw [← two_mul, h2, zero_mul])
  have hM1 : M = 1 := by rw [ha, ha1, one_smul]
  exact Subtype.ext (Units.ext hM1)

end CFSG.StandardType.F4ExplicitPos.CenterProofFast

end

end
