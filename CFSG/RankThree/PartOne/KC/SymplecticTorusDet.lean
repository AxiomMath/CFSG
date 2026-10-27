module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial

theorem mem_iSup_inf_ker_of_comm {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ L i → y ∈ L j → Commute x y)
    {A : ι → Type*} [∀ i, CommGroup (A i)] (D : ∀ i, G →* A i)
    (hD : ∀ i j, i ≠ j → ∀ g ∈ L j, D i g = 1) {c : G} (hc : c ∈ ⨆ i, L i)
    (h1 : ∀ i, D i c = 1) : c ∈ ⨆ i, L i ⊓ (D i).ker := by
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hc
  obtain ⟨f, rfl⟩ := hc
  have hΦ : Subgroup.noncommPiCoprod hcomm f = Finset.univ.noncommProd (fun j => (f j : G))
      (fun j _ k _ hjk => hcomm hjk _ _ (f j).2 (f k).2) := rfl
  have hf : ∀ i, (f i : G) ∈ L i ⊓ (D i).ker := by
    intro i
    refine ⟨(f i).2, ?_⟩
    have h2 := Finset.map_noncommProd Finset.univ (fun j => (f j : G))
      (fun j _ k _ hjk => hcomm hjk _ _ (f j).2 (f k).2) (D i)
    rw [← hΦ, Finset.noncommProd_eq_prod, Finset.prod_eq_single i
      (fun j _ hj => hD i j (Ne.symm hj) _ (f j).2) (fun h => absurd (Finset.mem_univ i) h)] at h2
    show D i (f i : G) = 1
    rw [← h2]
    exact h1 i
  have hS : Pairwise fun i j => ∀ x y : G, x ∈ L i ⊓ (D i).ker → y ∈ L j ⊓ (D j).ker →
      Commute x y := fun i j hij x y hx hy => hcomm hij x y hx.1 hy.1
  let f' : ∀ i, (L i ⊓ (D i).ker : Subgroup G) := fun i => ⟨(f i : G), hf i⟩
  have : Subgroup.noncommPiCoprod hcomm f = Subgroup.noncommPiCoprod hS f' := rfl
  rw [this, ← Subgroup.noncommPiCoprod_range (hcomm := hS)]
  exact ⟨f', rfl⟩

theorem isQuasisimple_comap_of_le_range {G N : Type*} [Group G] [Group N] {f : G →* N}
    (hf : Function.Injective f) {L : Subgroup N} (hL : L ≤ f.range)
    (h : CFSG.IsQuasisimple L) : CFSG.IsQuasisimple (L.comap f) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((((L.comap f).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL))).symm) h

theorem comap_commutator_of_le_range {G N : Type*} [Group G] [Group N] {f : G →* N}
    (hf : Function.Injective f) {A B : Subgroup N} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    ⁅A, B⁆.comap f = ⁅A.comap f, B.comap f⁆ := by
  rw [← Subgroup.comap_map_eq_self_of_injective hf ⁅A.comap f, B.comap f⁆,
    Subgroup.map_commutator, Subgroup.map_comap_eq_self hA, Subgroup.map_comap_eq_self hB]

section Similitude

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem blockDetHom_eq_one_of_fix {a : K[X]} {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ gl_centralizer x)
    (h : ∀ v ∈ primaryComponent (x : Module.End K V) a, (g : Module.End K V) v = v) :
    blockDetHom x a ⟨g, hg⟩ = 1 := by
  have h1 : blockRestrict x a ⟨g, hg⟩ = 1 := blockGL_ext fun v hv => by
    rw [blockApply_blockRestrict, blockApply_one]
    exact h v hv
  change blockGLDet (x : Module.End K V) a (blockRestrict x a ⟨g, hg⟩) = 1
  rw [h1, map_one]

omit [FiniteDimensional K V] in
theorem conj_mem_supportedUnitary_of_similitude {S : Set K[X]}
    {m g : LinearMap.GeneralLinearGroup K V} (hm : m ∈ gl_centralizer x) {μ : K}
    (hμ : ∀ u v, B ((m : Module.End K V) u) ((m : Module.End K V) v) = μ * B u v)
    (hg : g ∈ supportedUnitary B x S) : m * g * m⁻¹ ∈ supportedUnitary B x S := by
  have hgC : g ∈ gl_centralizer x := hg.1.2
  have hmi : m⁻¹ ∈ gl_centralizer x := inv_mem hm
  have hmm : ∀ u : V, (m : Module.End K V) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) u) = u := fun u => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
    rfl
  refine ⟨⟨?_, mul_mem (mul_mem hm hgC) hmi⟩, fun b hb hbS v hv => ?_⟩
  · show m * g * m⁻¹ ∈ sesqUnitaryGroup B
    rw [mem_sesqUnitaryGroup]
    intro u v
    have h1 := (mem_sesqUnitaryGroup.mp hg.1.1) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) u) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    have h2 := hμ (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) u)
      (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    rw [hmm, hmm] at h2
    change B ((m : Module.End K V) ((g : Module.End K V) (((m⁻¹ :
      LinearMap.GeneralLinearGroup K V) : Module.End K V) u)))
      ((m : Module.End K V) ((g : Module.End K V) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) v))) = B u v
    rw [hμ, h1, ← h2]
  · have hc : Commute (((m⁻¹ : LinearMap.GeneralLinearGroup K V)) : Module.End K V)
        (x : Module.End K V) := mem_gl_centralizer.mp hmi
    have h1 := apply_mem_primaryComponent hc hv
    have h2 := hg.2 b hb hbS _ h1
    change (m : Module.End K V) ((g : Module.End K V) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) v)) = v
    rw [h2, hmm]

omit [FiniteDimensional K V] in
theorem conj_mem_specialBlock_of_similitude {a : K[X]} {m g : LinearMap.GeneralLinearGroup K V}
    (hm : m ∈ gl_centralizer x) {μ : K}
    (hμ : ∀ u v, B ((m : Module.End K V) u) ((m : Module.End K V) v) = μ * B u v)
    (hg : g ∈ specialBlock B x a) : m * g * m⁻¹ ∈ specialBlock B x a := by
  obtain ⟨hs, hgc, hdet⟩ := mem_specialBlock.mp hg
  refine mem_specialBlock.mpr ⟨conj_mem_supportedUnitary_of_similitude hm hμ hs,
    mul_mem (mul_mem hm hgc) (inv_mem hm), ?_⟩
  have : (⟨m * g * m⁻¹, mul_mem (mul_mem hm hgc) (inv_mem hm)⟩ : gl_centralizer x) =
      ⟨m, hm⟩ * ⟨g, hgc⟩ * ⟨m, hm⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hdet, mul_one, mul_comm, inv_mul_cancel]

end Similitude

end CFSG.RankThree.PartOne.KCSpComm
