module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwoOutcome
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.K133X

open CFSG Subgroup CFSG.ComponentClassification

theorem isCharacteristicP_two_of_oddCore_noComponent {M : Type*} [Group M] [Finite M]
    (hcore : CFSG.oddCore M = ⊥) (hcomp : ∀ B : Subgroup M, ¬ IsComponent B) :
    IsCharacteristicP 2 M := by
  have h1 : pPrimeCore 2 M = ⊥ :=
    ((CFSG.pPrimeCore_eq_piCore M 2).trans (CFSG.oddCore_eq_piCore M).symm).trans hcore
  have h2 : layer M = ⊥ := by
    have : {K : Subgroup M | IsComponent K} = ∅ := Set.eq_empty_of_forall_notMem hcomp
    simp only [CFSG.layer.eq_sSup]
    rw [this, sSup_empty]
  exact isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot M 2 h1 h2

theorem oddCore_eq_bot_of_pPrimeCore_two {G : Type*} [Group G] (h : CFSG.pPrimeCore 2 G = ⊥) :
    CFSG.oddCore G = ⊥ :=
  ((CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm).trans h

theorem oddCore_centralizer_eq_bot_of_innerModel {X C : Type} [Group X] [Group C] (θ : X ≃* C)
    (hZ : Subgroup.center C = ⊥)
    (h : ∀ H : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ H →
      ∀ α ∈ (MulAut.conj : C →* MulAut C).range, orderOf α = 2 →
        CFSG.pPrimeCore 2 ↥(H ⊓ Subgroup.centralizer ({α} : Set (MulAut C))) = ⊥)
    {z : X} (hz : orderOf z = 2) : CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  set ρ : X →* MulAut C := (MulAut.conj : C →* MulAut C).comp θ.toMonoidHom with hρ
  have hcinj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := DFunLike.congr_fun hg y
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = g * y * g⁻¹ * g * 1 := by rw [h1]; group
        _ = g * y := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  have hinj : Function.Injective ρ := hcinj.comp θ.injective
  have hrange : ρ.range = (MulAut.conj : C →* MulAut C).range := by
    rw [hρ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 θ.surjective, Subgroup.map_top]
  have hα : ρ z ∈ (MulAut.conj : C →* MulAut C).range := ⟨θ z, rfl⟩
  have hα2 : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz]
  have h1 := h ρ.range hrange.ge (ρ z) hα hα2
  exact UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (UnbalancedCatalog.EvenCatalog.centralizerMapEquiv hinj z).symm
    (oddCore_eq_bot_of_pPrimeCore_two h1)

theorem center_eq_bot_of_simple_of_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center X := h1 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem center_eq_bot_of_mulEquiv {X C : Type*} [Group X] [Group C] (θ : X ≃* C)
    (h : Subgroup.center X = ⊥) : Subgroup.center C = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  have : θ.symm c ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have := hc (θ y)
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  rw [h, Subgroup.mem_bot] at this
  have h2 := congrArg θ this
  rwa [MulEquiv.apply_symm_apply, map_one] at h2

end CFSG.RankThree.PartOne.K133X
