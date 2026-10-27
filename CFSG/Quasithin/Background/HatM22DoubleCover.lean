module

public import CFSG.GroupTheory.PerfectCentralExtensionUnique
public import CFSG.Quasithin.Background.SmithB45HM22Cover

public section

namespace CFSG.Quasithin.HatM22

open Subgroup

theorem hatM22Q_ker_le_center :
    CFSG.Quasithin.HM22.hatM22Q.ker ≤ Subgroup.center ↥hatM22Γ₀ := by
  intro g hg
  have hg' : hatM22Act g = 1 := by
    have h : CFSG.Quasithin.HM22.hatM22Q g = 1 := hg
    exact congrArg Subtype.val h
  rcases (mem_ker_hatM22Act_iff g).1 hg' with rfl | rfl | rfl
  · exact one_mem _
  · exact hatM22Z_mem_center
  · exact Subgroup.pow_mem _ hatM22Z_mem_center 2

theorem isCyclic_ker_of_perfect
    {D : Type} [Group D] [Finite D]
    (hD : Group.IsPerfect D) (f : D →* ↥hatM22Γ₀)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center D) : IsCyclic f.ker := by
  let g : D →* ↥CFSG.Blueprint.NativeSporadic.M22 := CFSG.Quasithin.HM22.hatM22Q.comp f
  have hg : Function.Surjective g := CFSG.Quasithin.HM22.hatM22Q_surjective.comp hf
  have hgker : g.ker ≤ Subgroup.center D := by
    intro x hx
    have hx' : f x ∈ CFSG.Quasithin.HM22.hatM22Q.ker := hx
    have hxZ : f x ∈ Subgroup.center ↥hatM22Γ₀ := hatM22Q_ker_le_center hx'
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hD f hf hker]
    exact hxZ
  obtain ⟨hcyc, -⟩ :=
    CFSG.Sporadic.Recognition.CoverCyclic.ker_cyclic_dvd_of_bounds
      (CFSG.Quasithin.HM22.isPresentation_m22)
      CFSG.Sporadic.Recognition.M22Multiplier.m22Comm
      (CFSG.Sporadic.Recognition.M22Multiplier.lift_m22CommWord
        CFSG.Sporadic.Recognition.M22Multiplier.m22TabCheck_eq_true)
      (N := 12)
      (CFSG.Sporadic.Recognition.M22Multiplier.lift_m22B11
        CFSG.Sporadic.Recognition.M22Multiplier.m22TabCheck_eq_true)
      CFSG.Sporadic.Recognition.M22Multiplier.cover_bounds
      (by norm_num [CFSG.Sporadic.Mathieu.card_M22]) g hg hgker
  have hle : f.ker ≤ g.ker := by
    intro x hx
    show CFSG.Quasithin.HM22.hatM22Q (f x) = 1
    rw [MonoidHom.mem_ker.mp hx, map_one]
  haveI : IsCyclic ↥(g.ker) := hcyc
  exact Subgroup.isCyclic_of_le hle

theorem exists_mulEquiv_over_hatM22Γ₀
    {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C']
    (hC : Group.IsPerfect C) (hC' : Group.IsPerfect C') (π : C →* ↥hatM22Γ₀)
    (π' : C' →* ↥hatM22Γ₀) (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hker : π.ker ≤ Subgroup.center C) (hker' : π'.ker ≤ Subgroup.center C')
    (hcard : Nat.card π.ker = 2) (hcard' : Nat.card π'.ker = 2) :
    ∃ θ : C ≃* C', ∀ c, π' (θ c) = π c :=
  CFSG.GroupTheory.exists_mulEquiv_comp_eq_of_card_ker_eq_two hC hC' π π' hπ hπ' hker hker'
    hcard hcard' (fun D _ _ hD f hf hker => isCyclic_ker_of_perfect hD f hf hker)

end CFSG.Quasithin.HatM22
