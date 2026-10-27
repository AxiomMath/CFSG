module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Defs
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem w183_sp_congr {J E : Subgroup G} (M : ModDataE J E) {S S' : Subgroup G}
    (h : S ⊓ E = S' ⊓ E) : M.sp S = M.sp S' := by
  ext w
  rw [M.mem_sp, M.mem_sp, h]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1_zs_eq (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    packZsU D H M = fixSub (M.img D.T) := by
  rw [packZsU, M.fixSub_img x.hyp.hyp171.2.1]
  refine w183_sp_congr M ?_
  apply le_antisymm
  · intro z hz
    obtain ⟨hzΩ, hzE⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2
      ⟨CFSG.Quasithin.A4.centerOf_le_centralizer D.T
        (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf D.T hzΩ), hzE⟩
  · intro z hz
    obtain ⟨hzC, hzE⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_closure_of_mem
      (s := {x : G | x ∈ centerOf D.T ∧ x ^ 2 = 1})
      ⟨Subgroup.mem_inf.2
        ⟨x.hyp.pCoreOf_le_T (x.hyp.eOmegaZ_le_pCoreOf hzE), hzC⟩,
        x.hyp.isElemAbelian_eOmegaZ.2 z hzE⟩, hzE⟩

theorem br1_zs_gen (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    (⨆ y ∈ M.img H, conjSub y (packZsU D H M)) = ⊤ := by
  have htop : M.sp (eOmegaZ H D.T) = ⊤ := by
    refine le_antisymm le_top ?_
    intro w _
    obtain ⟨e, he, rfl⟩ := M.ι_surj w
    exact M.mem_sp.mpr ⟨e, ⟨he, he⟩, rfl⟩
  refine le_antisymm le_top ?_
  rw [← htop]
  intro w hw
  obtain ⟨e, he, rfl⟩ := M.mem_sp.mp hw
  have key : ∀ g ∈ eOmegaZ H D.T,
      M.ι g ∈ (⨆ y ∈ M.img H, conjSub y (packZsU D H M)) := by
    intro g hg
    rw [eOmegaZ, CFSG.Quasithin.conjClosure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨h, hh, z, hz, rfl⟩ := hx
        have hzE : z ∈ eOmegaZ H D.T := Hyp183.omegaOneCenterOf_le_eOmegaZ H D.T hz
        have hzZ : M.ι z ∈ packZsU D H M := M.mem_sp.mpr ⟨z, ⟨hz, hzE⟩, rfl⟩
        have hmem : M.ρ ⟨h, hh⟩ (M.ι z) ∈ conjSub (M.ρ ⟨h, hh⟩) (packZsU D H M) := by
          rw [CFSG.Quasithin.G11.conjSub, Submodule.mem_map]
          exact ⟨M.ι z, hzZ, rfl⟩
        have himg : M.ρ ⟨h, hh⟩ ∈ M.img H := M.mem_img.mpr ⟨⟨h, hh⟩, hh, rfl⟩
        rw [← M.ρ_ι ⟨h, hh⟩ z hzE]
        exact Submodule.mem_iSup_of_mem _
          (Submodule.mem_iSup_of_mem himg hmem)
    | one =>
        rw [M.ι_one]
        exact Submodule.zero_mem _
    | mul a b ha hb iha ihb =>
        rw [M.ι_mul a ha b hb]
        exact Submodule.add_mem _ iha ihb
    | inv a ha iha =>
        rw [M.ι_inv ha]
        exact Submodule.neg_mem _ iha
  exact key e he.1

theorem br1_zs_nofix (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ w ∈ packZsU D H M, w ≠ 0 → ∃ y ∈ M.img H, y w ≠ w := by
  intro w hw hw0
  rw [packZsU, M.mem_sp] at hw
  obtain ⟨z, ⟨hzΩ, hzE⟩, rfl⟩ := hw
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := x.hyp.isElemAbelian_eOmegaZ.2 z hzE
  have hzT : z ∈ D.T := CFSG.Quasithin.A4.omegaOneCenterOf_le D.T hzΩ
  have hzC : z ∈ Subgroup.centralizer (D.T : Set G) :=
    CFSG.Quasithin.A4.centerOf_le_centralizer D.T
      (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf D.T hzΩ)
  have hz1 : z ≠ 1 := by
    intro h1
    apply hw0
    rw [h1, M.ι_one]
  by_contra hcon
  have hfix : ∀ y ∈ M.img H, y (M.ι z) = M.ι z := by
    intro y hy
    by_contra hyne
    exact hcon ⟨y, hy, hyne⟩
  have hcomm : ∀ a ∈ H, a * z = z * a := by
    intro a ha
    have hy : M.ρ ⟨a, ha⟩ ∈ M.img H := M.mem_img.mpr ⟨⟨a, ha⟩, ha, rfl⟩
    have hfy := hfix _ hy
    have hιeq : M.ι (a * z * a⁻¹) = M.ι z := by
      rw [← M.ρ_ι ⟨a, ha⟩ z hzE]
      exact hfy
    have hn : a * z * a⁻¹ ∈ eOmegaZ H D.T :=
      (Subgroup.mem_normalizer_iff.1 (Hyp183.normalizer_eOmegaZ H D.T ha) z).1 hzE
    have heq : a * z * a⁻¹ = z := M.ι_injOn hn hzE hιeq
    calc a * z = (a * z * a⁻¹) * a := by group
      _ = z * a := by rw [heq]
  obtain ⟨hcent, -⟩ := x.hyp.setting.central x.hyp.ne_bot z hzT
    (fun t ht => (Subgroup.mem_centralizer_iff.mp hzC t ht).symm)
    (orderOf_eq_prime hz2 hz1)
  apply x.hyp.notLe
  intro a ha
  exact hcent (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha))

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
