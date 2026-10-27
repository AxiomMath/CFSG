module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardCoreCent
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenHeartNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct altAct_inv_apply)
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
  (coreHeart coreHeart_surjective toAdd_coreHeart_permAct)
open CFSG.RankThree.PartTwo.Sec19.SolEven (normalizerIsSym_six altAct_eq_iff)

@[expose] def s16c11_v1_coreA : Subgroup (MulAut ↥(G6.coreMod 6)) :=
  ((G6.coreAct 6).comp (alternatingGroup (Fin 6)).subtype).range

private theorem s16c11_v1_coreA_mem_iff {x : MulAut ↥(G6.coreMod 6)} :
    x ∈ s16c11_v1_coreA ↔ ∃ a : ↥(alternatingGroup (Fin 6)),
      G6.coreAct 6 (a : Equiv.Perm (Fin 6)) = x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (show x ∈
      ((G6.coreAct 6).comp (alternatingGroup (Fin 6)).subtype).range from hx)
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact show x ∈ ((G6.coreAct 6).comp (alternatingGroup (Fin 6)).subtype).range from
      MonoidHom.mem_range.mpr ⟨a, ha⟩

private theorem s16c11_v1_permAct_allOnes_BA (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    G6.permAct n σ (G6.allOnes n) = G6.allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  rfl

private theorem s16c11_v1_coreAct_of_mem_natKer_BA {n : ℕ} {k : ↥(G6.coreMod n)}
    (hk : k ∈ G6.natKer n) (σ : Equiv.Perm (Fin n)) : G6.coreAct n σ k = k := by
  apply Subtype.ext
  rw [G6.coreAct_coe]
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hk)
  have hkz : (k : G6.PermMod n) = G6.allOnes n ^ z := hz.symm
  rw [hkz, map_zpow, s16c11_v1_permAct_allOnes_BA]
  rfl

private theorem s16c11_v1_toAdd_coreHeart_coreAct (n : ℕ) (γ : Equiv.Perm (Fin n))
    (m : ↥(G6.coreMod n)) :
    Multiplicative.toAdd (coreHeart n (G6.coreAct n γ m)) =
      altAct γ (Multiplicative.toAdd (coreHeart n m)) :=
  toAdd_coreHeart_permAct (n := n) γ m

private theorem s16c11_v1_natKer_map_of_mem_normalizer {u : MulAut ↥(G6.coreMod 6)}
    (hu : u ∈ Subgroup.normalizer (s16c11_v1_coreA : Set (MulAut ↥(G6.coreMod 6)))) :
    (G6.natKer 6).map u.toMonoidHom = G6.natKer 6 := by
  have hfix : ∀ k ∈ G6.natKer 6, u k ∈ G6.natKer 6 := by
    intro k hk
    refine s16c11_v1_coreA_fixed (n := 6) (by norm_num) (m := u k) ?_
    intro a ha
    have hain : G6.coreAct 6 a ∈ s16c11_v1_coreA :=
      s16c11_v1_coreA_mem_iff.mpr ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨a', ha'⟩ := s16c11_v1_coreA_mem_iff.mp
      ((Subgroup.mem_normalizer_iff''.mp hu (G6.coreAct 6 a)).mp hain)
    have h1 : (u⁻¹ * G6.coreAct 6 a * u) k = k := by
      rw [← ha', s16c11_v1_coreAct_of_mem_natKer_BA hk (a' : Equiv.Perm (Fin 6))]
    calc G6.coreAct 6 a (u k)
        = u ((u⁻¹ * G6.coreAct 6 a * u) k) := by
          simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
      _ = u k := by rw [h1]
  have hfixinv : ∀ k ∈ G6.natKer 6, u⁻¹ k ∈ G6.natKer 6 := by
    intro k hk
    refine s16c11_v1_coreA_fixed (n := 6) (by norm_num) (m := u⁻¹ k) ?_
    intro a ha
    have hain : G6.coreAct 6 a ∈ s16c11_v1_coreA :=
      s16c11_v1_coreA_mem_iff.mpr ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨a', ha'⟩ := s16c11_v1_coreA_mem_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hu (G6.coreAct 6 a)).mp hain)
    have h1 : (u * G6.coreAct 6 a * u⁻¹) k = k := by
      rw [← ha', s16c11_v1_coreAct_of_mem_natKer_BA hk (a' : Equiv.Perm (Fin 6))]
    calc G6.coreAct 6 a (u⁻¹ k)
        = u⁻¹ ((u * G6.coreAct 6 a * u⁻¹) k) := by
          simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      _ = u⁻¹ k := by rw [h1]
  apply le_antisymm
  · rintro - ⟨k, hk, rfl⟩
    exact hfix k hk
  · intro k hk
    exact Subgroup.mem_map.mpr ⟨u⁻¹ k, hfixinv k hk, by simp⟩

theorem s16c11_v1_coreAct_range_normalizer :
    Subgroup.normalizer (s16c11_v1_coreA : Set (MulAut ↥(G6.coreMod 6))) =
      (G6.coreAct 6).range := by
  have hle : (G6.coreAct 6).range ≤
      Subgroup.normalizer (s16c11_v1_coreA : Set (MulAut ↥(G6.coreMod 6))) := by
    intro x hx
    obtain ⟨π, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨a, ha⟩ := s16c11_v1_coreA_mem_iff.mp hh
      rw [← ha]
      refine s16c11_v1_coreA_mem_iff.mpr
        ⟨⟨π * (a : Equiv.Perm (Fin 6)) * π⁻¹, ?_⟩, ?_⟩
      · exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ a.2 π
      · simp only [map_mul, map_inv]
    · intro hh
      obtain ⟨a, ha⟩ := s16c11_v1_coreA_mem_iff.mp hh
      refine s16c11_v1_coreA_mem_iff.mpr
        ⟨⟨π⁻¹ * (a : Equiv.Perm (Fin 6)) * π, ?_⟩, ?_⟩
      · exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ a.2 π⁻¹
      · rw [map_mul, map_mul, map_inv, ha]
        group
  apply le_antisymm
  · intro g hg
    have hKmap := s16c11_v1_natKer_map_of_mem_normalizer hg
    obtain ⟨γ, hγ⟩ := s16c11_v1_coreHeart_induced (n := 6) (by norm_num) g hKmap
    have hγnorm : ∀ σ ∈ alternatingGroup (Fin 6),
        ∃ σ' ∈ alternatingGroup (Fin 6), ∀ v, γ (altAct σ v) = altAct σ' (γ v) := by
      intro σ hσ
      have hconj : g * G6.coreAct 6 σ * g⁻¹ ∈ s16c11_v1_coreA :=
        (Subgroup.mem_normalizer_iff.mp hg (G6.coreAct 6 σ)).mp
          (s16c11_v1_coreA_mem_iff.mpr ⟨⟨σ, hσ⟩, rfl⟩)
      obtain ⟨σ', hσ'⟩ := s16c11_v1_coreA_mem_iff.mp hconj
      refine ⟨(σ' : Equiv.Perm (Fin 6)), σ'.2, fun v => ?_⟩
      obtain ⟨m, hm⟩ := coreHeart_surjective 6 (Multiplicative.ofAdd v)
      have hv : v = Multiplicative.toAdd (coreHeart 6 m) := by rw [hm, toAdd_ofAdd]
      have hgm : G6.coreAct 6 (σ' : Equiv.Perm (Fin 6)) (g m) =
          g (G6.coreAct 6 σ m) := by
        have h := congrArg (fun (u : MulAut ↥(G6.coreMod 6)) => u (g m)) hσ'
        simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h
      rw [hv, ← s16c11_v1_toAdd_coreHeart_coreAct (n := 6) σ m, ← hγ (G6.coreAct 6 σ m),
        ← hγ m, ← hgm]
      exact s16c11_v1_toAdd_coreHeart_coreAct (n := 6) (σ' : Equiv.Perm (Fin 6)) (g m)
    obtain ⟨π, hπ⟩ := normalizerIsSym_six γ hγnorm
    let g₁ : MulAut ↥(G6.coreMod 6) := (G6.coreAct 6 π)⁻¹ * g
    have hg₁mem : g₁ ∈ Subgroup.normalizer
        (s16c11_v1_coreA : Set (MulAut ↥(G6.coreMod 6))) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle (MonoidHom.mem_range.mpr ⟨π, rfl⟩))) hg
    have hfix₁ : ∀ m : ↥(G6.coreMod 6), coreHeart 6 (g₁ m) = coreHeart 6 m := by
      intro m
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd (coreHeart 6 ((G6.coreAct 6 π)⁻¹ (g m))) =
        Multiplicative.toAdd (coreHeart 6 m)
      rw [← map_inv (G6.coreAct 6) π,
        s16c11_v1_toAdd_coreHeart_coreAct (n := 6) π⁻¹ (g m), hγ m,
        hπ (Multiplicative.toAdd (coreHeart 6 m))]
      exact altAct_inv_apply π _
    have hcomm : ∀ σ : ↥(alternatingGroup (Fin 6)), ∀ x : ↥(G6.coreMod 6),
        g₁ (G6.coreAct 6 (σ : Equiv.Perm (Fin 6)) x) =
          G6.coreAct 6 (σ : Equiv.Perm (Fin 6)) (g₁ x) := by
      intro σ x
      have hconj : g₁ * G6.coreAct 6 (σ : Equiv.Perm (Fin 6)) * g₁⁻¹ ∈ s16c11_v1_coreA :=
        (Subgroup.mem_normalizer_iff.mp hg₁mem
          (G6.coreAct 6 (σ : Equiv.Perm (Fin 6)))).mp
            (s16c11_v1_coreA_mem_iff.mpr ⟨σ, rfl⟩)
      obtain ⟨σ', hσ'⟩ := s16c11_v1_coreA_mem_iff.mp hconj
      have hrel : ∀ y, G6.coreAct 6 (σ' : Equiv.Perm (Fin 6)) (g₁ y) =
          g₁ (G6.coreAct 6 (σ : Equiv.Perm (Fin 6)) y) := by
        intro y
        have h := congrArg (fun (u : MulAut ↥(G6.coreMod 6)) => u (g₁ y)) hσ'
        simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h
      have hσ'eq : (σ' : Equiv.Perm (Fin 6)) = (σ : Equiv.Perm (Fin 6)) := by
        refine (altAct_eq_iff (n := 6) (by norm_num)).mp fun v => ?_
        obtain ⟨y, hy⟩ := coreHeart_surjective 6 (Multiplicative.ofAdd v)
        have hv : v = Multiplicative.toAdd (coreHeart 6 y) := by rw [hy, toAdd_ofAdd]
        have hstep : G6.coreAct 6 (σ' : Equiv.Perm (Fin 6)) y =
            g₁ (G6.coreAct 6 (σ : Equiv.Perm (Fin 6)) (g₁⁻¹ y)) := by
          have h := hrel (g₁⁻¹ y)
          rwa [MulAut.apply_inv_self] at h
        rw [hv, ← s16c11_v1_toAdd_coreHeart_coreAct (n := 6) (σ' : Equiv.Perm (Fin 6)) y, hstep,
          hfix₁, s16c11_v1_toAdd_coreHeart_coreAct (n := 6) (σ : Equiv.Perm (Fin 6)) (g₁⁻¹ y),
          ← hfix₁ (g₁⁻¹ y), MulAut.apply_inv_self]
      rw [← hrel x, hσ'eq]
    have hg₁1 : g₁ = 1 := s16c11_v1_coreAct_centralizer (n := 6) (by norm_num) g₁ hcomm
    have hthis : (G6.coreAct 6 π)⁻¹ * g = 1 := hg₁1
    have hg_eq : g = G6.coreAct 6 π := by
      calc g = (G6.coreAct 6 π) * ((G6.coreAct 6 π)⁻¹ * g) := by group
        _ = G6.coreAct 6 π := by rw [hthis, mul_one]
    exact MonoidHom.mem_range.mpr ⟨π, hg_eq.symm⟩
  · exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
