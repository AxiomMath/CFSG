module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.StandardType CFSG.Open

private theorem rckHD_mem_roots_of_ggLongRoot {K : Type*} [Group K]
    {D : UniversalRootDatum K} {β : Fin D.rank → ℤ} (hβ : GGLongRoot D β) :
    β ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hβ
  exact CFSG.LieType.RootSystem.weylAction_mem_roots D.isFiniteType w hγ₀

private theorem rckHD_spin_cent {m : ℕ} (hm : 3 ≤ m) {F : Type} [Field F]
    {β : Fin m → ℤ} (hβ : β ∈ (Spin.plusDatum m F hm).roots) :
    ∀ x ∈ Spin.plusRootGroup m F hm β, x ≠ 1 →
      Subgroup.centralizer ({x} : Set (spinGroup (Spin.quadPlus m F))) ≤
        Subgroup.centralizer
          ((Spin.plusRootGroup m F hm β) : Set (spinGroup (Spin.quadPlus m F))) := by
  intro x hx hx1 k hk
  obtain ⟨i, j, hij, s, t, _, hgroup⟩ := Spin.exists_plusRootGroup_eq (K := F) hm hβ
  have hx' : x ∈ ((Spin.plusFrame m F hm).longRoot hij s t).range := by
    rw [← hgroup]; exact hx
  obtain ⟨c₀, hc₀⟩ := hx'
  set N : CliffordAlgebra (Spin.quadPlus m F) :=
    CliffordAlgebra.ι (Spin.quadPlus m F) ((Spin.plusFrame m F hm).vec i s) *
      CliffordAlgebra.ι (Spin.quadPlus m F) ((Spin.plusFrame m F hm).vec j t) with hN
  have hxrepr : (x : CliffordAlgebra (Spin.quadPlus m F)) = 1 + c₀.toAdd • N := by
    rw [← hc₀]
    change ((Spin.plusFrame m F hm).longRoot hij s t
        (Multiplicative.ofAdd c₀.toAdd) : CliffordAlgebra (Spin.quadPlus m F)) =
      1 + c₀.toAdd • N
    simp only [Spin.HypFrame.coe_longRoot, hN]
  have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.mp hk
  have hk_alg : Commute (k : CliffordAlgebra (Spin.quadPlus m F))
      (x : CliffordAlgebra (Spin.quadPlus m F)) :=
    hkx.map (Submonoid.subtype (spinGroup (Spin.quadPlus m F)))
  have hxc₀ : Commute (k : CliffordAlgebra (Spin.quadPlus m F)) (1 + c₀.toAdd • N) := by
    rwa [hxrepr] at hk_alg
  have hc₀ne : c₀.toAdd ≠ 0 := by
    intro h
    exact hx1 (Subtype.ext (by rw [hxrepr, h, zero_smul, add_zero]; rfl))
  have hL5 : ∀ c : F, Commute (k : CliffordAlgebra (Spin.quadPlus m F)) (1 + c • N) :=
    fun c => commute_one_add_smul_of_ne_zero hc₀ne hxc₀ c
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hgroup] at hy
  obtain ⟨c, rfl⟩ := hy
  have hyrepr : (((Spin.plusFrame m F hm).longRoot hij s t c) :
        CliffordAlgebra (Spin.quadPlus m F)) = 1 + c.toAdd • N := by
    change ((Spin.plusFrame m F hm).longRoot hij s t
        (Multiplicative.ofAdd c.toAdd) : CliffordAlgebra (Spin.quadPlus m F)) =
      1 + c.toAdd • N
    simp only [Spin.HypFrame.coe_longRoot, hN]
  have hcomm : Commute (k : CliffordAlgebra (Spin.quadPlus m F))
      (((Spin.plusFrame m F hm).longRoot hij s t c) : CliffordAlgebra (Spin.quadPlus m F)) := by
    rw [hyrepr]; exact hL5 c.toAdd
  exact (Commute.of_map (f := Submonoid.subtype (spinGroup (Spin.quadPlus m F)))
    (Submonoid.subtype_injective _) hcomm).symm

private theorem rckHD_trivialUniversal (β : Fin 0 → ℤ) :
    RCKLemmaHCent trivialUniversal β := by
  intro x hx hx1
  haveI : Subsingleton trivialUniversal.K := by
    change Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
    infer_instance
  exact absurd (Subsingleton.elim x 1) hx1

theorem rck_lemmaHC_D
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaPlus m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .POmegaPlus m g).D β) :
    RCKLemmaHCent (ggU .POmegaPlus m g) β := by
  by_cases hm : 3 ≤ m
  · generalize hM : ggU .POmegaPlus m g = M at β hβ ⊢
    have hM' : M = ⟨spinGroup (Spin.quadPlus m (GaloisField 2 g)),
        Spin.plusDatum m (GaloisField 2 g) hm⟩ := by
      rw [← hM]
      simp only [ggU, lieUniversal, dif_pos hm]
    subst hM'
    exact rckHD_spin_cent hm (rckHD_mem_roots_of_ggLongRoot hβ)
  · generalize hM : ggU .POmegaPlus m g = M at β hβ ⊢
    have hM' : M = trivialUniversal := by
      rw [← hM]
      simp only [ggU, lieUniversal, dif_neg hm]
    subst hM'
    exact rckHD_trivialUniversal β

end CFSG.StandardType.RCKC1
