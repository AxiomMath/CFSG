module

public import CFSG.Monster.Existence.TwoPoint.B433CoverInst

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.YGroups CFSG.YGroups.DCE.B433
open CFSG.Certificates.CosetEnumeration (evalWord)

@[expose] noncomputable def xU : ℕ → U433 := nodeProd (yGen 4 3 3) (yGen 4 3 3 10)

theorem xU_zero : xU 0 = 1 := nodeProd_zero _ _

theorem xU_one : xU 1 = yGen 4 3 3 10 := nodeProd_one _ _

theorem xU_eq {j : ℕ} (hj : 0 < j) (hj' : j < 23) :
    xU j = xU (nodeParent j) *
      (evalWord (yGen 4 3 3) (nodeWord j) * yGen 4 3 3 10 *
        (evalWord (yGen 4 3 3) (nodeWord j))⁻¹) :=
  nodeProd_eq _ _ hj hj'

theorem xU_eq_evalWord (j : ℕ) : xU j = evalWord (yGen 4 3 3) (nodeLetters j) :=
  nodeProd_eq_evalWord rfl (fun l _ => yGen_mul_self 4 3 3 l) j

theorem map_xU {G : Type*} [Group G] (f : U433 →* G) (j : ℕ) :
    f (xU j) = nodeProd (fun l => f (yGen 4 3 3 l)) (f (yGen 4 3 3 10)) j :=
  nodeProd_map f _ _ j

theorem map_xU_of_gen {G : Type*} [Group G] (f : U433 →* G) (gen : ℕ → G)
    (h : ∀ l ≤ 10, f (yGen 4 3 3 l) = gen l) (j : ℕ) :
    f (xU j) = nodeProd gen (gen 10) j := by
  rw [map_xU, ← h 10 le_rfl]
  exact nodeProd_congr (fun l hl => h l hl.le) _ j

theorem qB_xU (j : ℕ) : qB (xU j) = xB j := by
  rw [xU, nodeProd_map, xB]
  exact nodeProd_congr (fun l hl => (psi_yGen hl).symm) _ j

theorem psiU_range_eq_closure :
    psiU.range = Subgroup.closure (yGen 4 3 3 '' Set.Iio 10) := by
  have h : (⊤ : Subgroup (YGroup 4 3 2)) = Subgroup.closure (yGen 4 3 2 '' Set.Iio 10) := by
    simpa [ngen] using (closure_yGen 4 3 2).symm
  rw [MonoidHom.range_eq_map, h, MonoidHom.map_closure, Set.image_image]
  exact congrArg Subgroup.closure (Set.image_congr fun c hc => psiU_yGen hc)

theorem u433_cover_of_cover
    (hcov : ∀ g : B433, ∃ l < 23, ∃ a ∈ psi.range, ∃ b ∈ psi.range, g = a * xB l * b)
    (g : U433) :
    ∃ l < 23, ∃ a ∈ psiU.range, ∃ b ∈ psiU.range,
      ∃ f ∈ Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433),
        g = a * xU l * b * f := by
  obtain ⟨l, hl, a, ⟨a0, rfl⟩, b, ⟨b0, rfl⟩, hg⟩ := hcov (qB g)
  refine ⟨l, hl, psiU a0, ⟨a0, rfl⟩, psiU b0, ⟨b0, rfl⟩, (psiU a0 * xU l * psiU b0)⁻¹ * g,
    ?_, by group⟩
  rw [← QuotientGroup.eq_one_iff (N := Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} :
    Set U433))]
  change qB ((psiU a0 * xU l * psiU b0)⁻¹ * g) = 1
  rw [map_mul, map_inv, map_mul, map_mul, qB_xU, hg]
  show (psi a0 * xB l * psi b0)⁻¹ * (psi a0 * xB l * psi b0) = 1
  exact inv_mul_cancel _

end CFSG.Monster.Existence.B433Cover
