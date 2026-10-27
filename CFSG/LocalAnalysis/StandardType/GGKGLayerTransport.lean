module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerDefs

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance 100] commutatorElement

private lemma isQuasisimple_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.IsQuasisimple G) : CFSG.IsQuasisimple H := by
  have he : Subgroup.map (e.toMonoidHom : G →* H) (Subgroup.center G) = Subgroup.center H :=
    Subgroup.map_center_eq e
  have hq : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
    QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he
  refine ⟨?_, ?_, ?_⟩
  · haveI : Group.IsPerfect G := hG.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact (MulEquiv.isSimpleGroup_congr hq).mp hG.2.1
  · obtain ⟨a, b, hab⟩ := hG.2.2
    refine ⟨hq a, hq b, fun hcon => hab ?_⟩
    exact hq.injective (by rw [map_mul hq a b, map_mul hq b a, hcon])

theorem ggLayerOf_comap {R S : Type} [Group R] [Group S] (Θ : R →* S)
    (hΘ : Function.Injective Θ) {X : Subgroup R} {F : Subgroup S}
    (h : GGLayerOf (X.map Θ) F) : GGLayerOf X (F.comap Θ) := by
  obtain ⟨hFle, hFnorm, hFq, hFmax⟩ := h
  have hFrange : F ≤ Θ.range := le_trans hFle (Subgroup.map_le_range Θ X)
  have hmap : (F.comap Θ).map Θ = F := Subgroup.map_comap_eq_self hFrange
  have hle : F.comap Θ ≤ X := by
    intro y hy
    have hyX : Θ y ∈ X.map Θ := hFle (show Θ y ∈ F from hy)
    rcases Subgroup.mem_map.mp hyX with ⟨x, hxX, hxeq⟩
    rw [← hΘ hxeq]
    exact hxX
  have hnorm : ((F.comap Θ).subgroupOf X).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hn
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    have hn' : (⟨Θ (n : R), by
        rw [Subgroup.mem_map]; exact ⟨(n : R), n.2, rfl⟩⟩ : X.map Θ) ∈
        F.subgroupOf (X.map Θ) := hn
    have key := hFnorm.conj_mem _ hn' (⟨Θ (g : R), by
        rw [Subgroup.mem_map]; exact ⟨(g : R), g.2, rfl⟩⟩ : X.map Θ)
    rw [Subgroup.mem_subgroupOf] at key
    simpa [map_mul, map_inv] using key
  have e' : ↥(F.comap Θ) ≃* ↥F :=
    (Subgroup.equivMapOfInjective (F.comap Θ) Θ hΘ).trans (MulEquiv.subgroupCongr hmap)
  have hq : CFSG.IsQuasisimple ↥(F.comap Θ) :=
    isQuasisimple_of_mulEquiv e'.symm hFq
  have hmax : ∀ P : Subgroup R, P ≤ X → ⁅P, P⁆ = P → P ≤ F.comap Θ := by
    intro P hP hPperf
    rw [← Subgroup.map_le_iff_le_comap]
    refine hFmax (P.map Θ) (Subgroup.map_mono hP) ?_
    rw [← Subgroup.map_commutator, hPperf]
  exact ⟨hle, hnorm, hq, hmax⟩

theorem mulAut_eq_of_comp_eq {L R : Type} [Group L] [Group R] (ψ : L →* R)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) {σ τ : MulAut L}
    (h : ∀ l, ψ (σ l) = ψ (τ l)) : σ = τ := by
  let d : L →* L :=
    { toFun := fun l => (τ l)⁻¹ * σ l
      map_one' := by simp
      map_mul' := fun l m => by
        have hmem : (τ l)⁻¹ * σ l ∈ Subgroup.center L := by
          apply hker
          rw [MonoidHom.mem_ker, map_mul, map_inv, h l]
          exact inv_mul_cancel _
        have hcomm : ∀ g : L, g * ((τ l)⁻¹ * σ l) = ((τ l)⁻¹ * σ l) * g :=
          Subgroup.mem_center_iff.mp hmem
        have h1 : (τ (l * m))⁻¹ * σ (l * m) = (τ m)⁻¹ * ((τ l)⁻¹ * σ l) * σ m := by
          rw [map_mul, map_mul, mul_inv_rev]
          group
        rw [h1]
        calc
          (τ m)⁻¹ * ((τ l)⁻¹ * σ l) * σ m
              = (τ m)⁻¹ * (((τ l)⁻¹ * σ l) * σ m) := by group
          _ = (τ m)⁻¹ * (σ m * ((τ l)⁻¹ * σ l)) := by rw [hcomm (σ m)]
          _ = ((τ m)⁻¹ * σ m) * ((τ l)⁻¹ * σ l) := by group
          _ = ((τ l)⁻¹ * σ l) * ((τ m)⁻¹ * σ m) := by rw [hcomm ((τ m)⁻¹ * σ m)] }
  have hdmem : ∀ l, d l ∈ Subgroup.center L := by
    intro l
    apply hker
    rw [MonoidHom.mem_ker]
    change ψ ((τ l)⁻¹ * σ l) = 1
    rw [map_mul, map_inv, h l]
    exact inv_mul_cancel _
  have hdcomm : ∀ a b : L, d ⁅a, b⁆ = 1 := by
    intro a b
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hdmem a) (d b)).symm
  have hle : commutator L ≤ d.ker := by
    change ⁅(⊤ : Subgroup L), ⊤⁆ ≤ d.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    exact hdcomm a b
  have htop : (⊤ : Subgroup L) ≤ d.ker := by
    rw [← hperf]
    exact hle
  have hkereq : d.ker = ⊤ := top_le_iff.mp htop
  refine MulEquiv.ext fun l => ?_
  have hl : d l = 1 := by
    have : l ∈ d.ker := by rw [hkereq]; exact Subgroup.mem_top l
    rwa [MonoidHom.mem_ker] at this
  change (τ l)⁻¹ * σ l = 1 at hl
  calc
    σ l = τ l * ((τ l)⁻¹ * σ l) := by group
    _ = τ l := by rw [hl, mul_one]

theorem isCyclic_center_of_equiv {E F : Type} [Group E] [Group F] (e : E ≃* F)
    (h : ∀ (N : Type) [Group N] [Finite N] (π : N →* F), Function.Surjective π →
      π.ker ≤ Subgroup.center N → commutator N = ⊤ → IsCyclic (Subgroup.center N))
    (N : Type) [Group N] [Finite N] (π : N →* E) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center N) (hperf : commutator N = ⊤) :
    IsCyclic (Subgroup.center N) := by
  refine h N (e.toMonoidHom.comp π) ?_ ?_ hperf
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := hπ y
    exact ⟨z, rfl⟩
  · rw [MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective]
    exact hker

end CFSG.StandardType.KGL

end
