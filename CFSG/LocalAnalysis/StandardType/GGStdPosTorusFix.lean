module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosTorus
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggStdPos_conj_mem_ggTorus_of_actsAs {K : Type*} [Group K] {D : UniversalRootDatum K}
    {h m : K} {w : (coxeterMatrix D.isFiniteType).Group} (hh : h ∈ ggTorus D)
    (hm : ActsAs D m w) : m * h * m⁻¹ ∈ ggTorus D := by
  refine Subgroup.mem_iInf.mpr fun δ => Subgroup.mem_iInf.mpr fun hδ => ?_
  have hδ' : weylAction D.isFiniteType w⁻¹ δ ∈ D.roots := weylAction_mem_roots _ _ hδ
  have hN : h ∈ Subgroup.normalizer (D.rootGroup (weylAction D.isFiniteType w⁻¹ δ) : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh _) hδ'
  rw [mem_normalizer_iff_map_conj, mul_assoc, map_conj_mul, map_conj_mul, hm.inv δ hδ,
    mem_normalizer_iff_map_conj.mp hN, hm _ hδ', weylAction_apply_inv_apply]

theorem ggStdPos_psi_mem_centralizer {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G}
    (hBs : GGKGPosStdPos D ψ Bs) : ∀ h ∈ ggTorus D, ψ h ∈ Subgroup.centralizer (Bs : Set G) := by
  have hT := ggStdPos_ggTorus_eq hct hext hBU
  have hab := LieType.TitsSimplicity.iSup_le_centralizer_iSup hext
  suffices hle : ⨆ i, H i ≤ (Subgroup.centralizer (Bs : Set G)).comap ψ by
    intro h hh
    rw [hT] at hh
    exact hle hh
  refine iSup_le fun i y hy => ?_
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨hp, hhp, hpz⟩ := hBs b hb _ (single_mem_roots i)
  obtain ⟨hm, hhm, hmz⟩ := hBs b hb _ (neg_single_mem_roots i)
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  have hΦ := PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
  have hpos := hE.param _ (single_mem_roots i)
  have hneg := hE.param _ (neg_single_mem_roots i)
  have hN : hp⁻¹ * hm ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (mul_mem (inv_mem hhp) hhm) _)
      (neg_single_mem_roots i)
  have hmem : ∀ c, ∃ c', x (-Pi.single i 1) c' =
      hp⁻¹ * hm * x (-Pi.single i 1) c * (hp⁻¹ * hm)⁻¹ := fun c =>
    (hneg.1 _).mp ((Subgroup.mem_normalizer_iff.mp hN _).mp ((hneg.1 _).mpr ⟨c, rfl⟩))
  choose φ' hφ' using hmem
  obtain ⟨d, hd⟩ : ∃ d, d = b⁻¹ * ψ hp := ⟨_, rfl⟩
  have hconj : ∀ z, d⁻¹ * ψ z * d = (ψ hp)⁻¹ * (b * ψ z * b⁻¹) * ψ hp := by
    intro z
    rw [hd]
    group
  have hu : ∀ c, d⁻¹ * (ψ.comp φ) (sl2Upper c) * d = (ψ.comp φ) (sl2Upper c) := by
    intro c
    rw [MonoidHom.comp_apply, hφu, hconj, hpz _ ((hpos.1 _).mpr ⟨c, rfl⟩), ← map_inv,
      ← map_mul, ← map_mul]
    congr 1
    group
  have hl : ∀ c, d⁻¹ * (ψ.comp φ) (sl2Lower c) * d = (ψ.comp φ) (sl2Lower (φ' c)) := by
    intro c
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl, hconj,
      hmz _ ((hneg.1 _).mpr ⟨c, rfl⟩), hφ', ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hfix := PsiDiag.eq_of_conj_sl2 (ψ.comp φ) hΦ hu hl
  have hL : rankOne D.rootGroup i ≤ (Subgroup.centralizer ({d} : Set G)).comap ψ := by
    refine sup_le (fun z hz => ?_) fun z hz => ?_
    · obtain ⟨c, rfl⟩ := (hpos.1 z).mp hz
      rw [PsiDiag.mem_fix_iff]
      have h1 := hu c
      rwa [MonoidHom.comp_apply, hφu] at h1
    · obtain ⟨c, rfl⟩ := (hneg.1 z).mp hz
      rw [PsiDiag.mem_fix_iff]
      have h1 := hl c
      rwa [hfix c, MonoidHom.comp_apply, hφl] at h1
  have hdy : d⁻¹ * ψ y * d = ψ y := (PsiDiag.mem_fix_iff ψ).mp (hL (hct.H_le i hy))
  have hpy : y * hp = hp * y :=
    Subgroup.mem_centralizer_iff.mp (hab (hT ▸ hhp)) y (le_iSup H i hy)
  have hb' : b = ψ hp * d⁻¹ := by
    rw [hd]
    group
  rw [hb']
  calc ψ hp * d⁻¹ * ψ y = ψ hp * (d⁻¹ * ψ y * d) * d⁻¹ := by group
    _ = ψ (hp * y) * d⁻¹ := by rw [hdy, map_mul]
    _ = ψ y * (ψ hp * d⁻¹) := by rw [← hpy, map_mul, mul_assoc]

end CFSG.StandardType

end
