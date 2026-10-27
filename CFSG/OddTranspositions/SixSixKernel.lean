module

public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

attribute [local instance] blockKernel_normal

theorem exists_mem_D_centralizes_alpha (hC : HypothesisC D) :
    ∃ b ∈ D, ∀ a ∈ hC.alpha, Commute a b := by
  obtain ⟨e, -, hEe, -⟩ := hC.hE
  have heE : e ∈ hC.E := hEe ▸ OddLocal.self_mem_orbitIn (D := D) hC.d e
  rw [← hC.DalphaStar_alpha] at heE
  obtain ⟨β, hβ, heβ⟩ := heE
  obtain ⟨-, hβD, -, hcomm⟩ := mem_Dalpha_iff.mp hβ
  exact ⟨e, hβD heβ, fun a ha => hcomm a ha e heβ⟩

theorem le_closure_alpha_of_le_normalizer (hC : HypothesisC D) {M : Subgroup G} [hMn : M.Normal]
    (hMs : IsSimpleGroup M) (hMc : Subgroup.centralizer (M : Set G) = ⊥)
    (hMα : M ≤ Subgroup.normalizer hC.alpha) : M ≤ Subgroup.closure hC.alpha := by
  classical
  set L : Subgroup G := Subgroup.closure hC.alpha ⊓ M
  have hLn : (L.subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, M.mul_mem (M.mul_mem m.2 hx.2) (M.inv_mem m.2)⟩
    have hm : (m : G) ∈ Subgroup.normalizer hC.alpha := hMα m.2
    have key : ∀ y ∈ Subgroup.closure hC.alpha,
        (m : G) * y * (m : G)⁻¹ ∈ Subgroup.closure hC.alpha := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        have h := (Subgroup.mem_normalizer_iff_conj_image_eq.mp hm)
        exact Subgroup.subset_closure (h ▸ Set.mem_image_of_mem (fun x => (m : G) * x * (m : G)⁻¹) hy)
      | one => simp
      | mul y z _ _ ihy ihz =>
        have : (m : G) * (y * z) * (m : G)⁻¹ =
            ((m : G) * y * (m : G)⁻¹) * ((m : G) * z * (m : G)⁻¹) := by group
        rw [this]; exact Subgroup.mul_mem _ ihy ihz
      | inv y _ ihy =>
        have : (m : G) * y⁻¹ * (m : G)⁻¹ = ((m : G) * y * (m : G)⁻¹)⁻¹ := by group
        rw [this]; exact Subgroup.inv_mem _ ihy
    exact key _ hx.1
  rcases hLn.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hd := hC.d_mem_alpha
    have hdD : hC.d ∈ D := hC.isBlock_alpha.subset hd
    have hcent : hC.d ∈ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hmem : m * hC.d * m⁻¹ * hC.d⁻¹ ∈ L := by
        have h := (Subgroup.mem_normalizer_iff_conj_image_eq.mp (hMα hm))
        refine ⟨Subgroup.mul_mem _ (Subgroup.subset_closure
          (h ▸ Set.mem_image_of_mem (fun x => m * x * m⁻¹) hd))
          (Subgroup.inv_mem _ (Subgroup.subset_closure hd)), ?_⟩
        have h1 : hC.d * m⁻¹ * hC.d⁻¹ ∈ M := hMn.conj_mem _ (M.inv_mem hm) _
        have : m * hC.d * m⁻¹ * hC.d⁻¹ = m * (hC.d * m⁻¹ * hC.d⁻¹) := by group
        rw [this]; exact M.mul_mem hm h1
      have h1 : (⟨_, hmem.2⟩ : M) ∈ L.subgroupOf M := by
        rw [Subgroup.mem_subgroupOf]; exact hmem
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : m * hC.d * m⁻¹ * hC.d⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : m * hC.d = hC.d * m := by
        calc m * hC.d = (m * hC.d * m⁻¹ * hC.d⁻¹) * (hC.d * m) := by group
          _ = hC.d * m := by rw [h2, one_mul]
      exact h3
    rw [hMc, Subgroup.mem_bot] at hcent
    exact hC.setup.oddT.ne_one hdD hcent
  · intro m hm
    have : (⟨m, hm⟩ : M) ∈ L.subgroupOf M := htop ▸ Subgroup.mem_top _
    exact ((Subgroup.mem_subgroupOf).mp this).1

end CFSG.OddTranspositions
