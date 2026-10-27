module

public import CFSG.LocalAnalysis.WeakClosure81.W18Ctx
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def vInH (V H : Subgroup G) (g : G) : Subgroup G := conjSubgroup V g ⊓ H

@[expose] def Gam188 (V H E : Subgroup G) (i k : ℕ) (g : G) : Prop :=
  Gam183 V H E i g ∧
    E3.mQuot (vInH V H g) (vInH V H g ⊓ Subgroup.centralizer (E : Set G)) ≤ k

theorem vInH_mul {V H : Subgroup G} (g : G) {y : G} (hy : y ∈ H) :
    vInH V H (g * y) = conjSubgroup (vInH V H g) y := by
  unfold vInH
  rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup,
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hy)]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

@[expose] noncomputable def iStar (x : Ctx188 D V₀ V H i j) : ℕ :=
  mBar D.M V₀ V x.hyp.setting.isElemAbelian - i - 1

theorem iStar_pos (x : Ctx188 D V₀ V H i j) : 0 < x.iStar := by
  have h1 := x.bound
  have h2 := x.two_le
  unfold iStar
  omega

theorem iStar_add_lt (x : Ctx188 D V₀ V H i j) :
    x.iStar + i < mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
  have h1 := x.bound
  have h2 := x.two_le
  unfold iStar
  omega

theorem comm_le {k : ℕ} (x : Ctx188 D V₀ V H i j)
    (hk : k + i < mBar D.M V₀ V x.hyp.setting.isElemAbelian) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {B : Subgroup G} (hBD : B ≤ vInH V H g)
    (hB : E3.mQuot (vInH V H g) B ≤ k) :
    ⁅eOmegaZ H D.T ⊓ Subgroup.centralizer (B : Set G), vInH V H g⁆ ≤
      eOmegaZ H D.T ⊓ conjSubgroup V₀ g :=
  x.hyp.comm_centralizer_le_conj x.h162 x.mbar inf_le_left inf_le_right hBD
    (lt_of_le_of_lt (add_le_add hB hg.1) hk)

theorem quadratic {k : ℕ} (x : Ctx188 D V₀ V H i j)
    (hk : k + i < mBar D.M V₀ V x.hyp.setting.isElemAbelian) {g : G}
    (hg : Gam188 V H (eOmegaZ H D.T) i k g) :
    ⁅⁅eOmegaZ H D.T, vInH V H g⁆, vInH V H g⁆ = ⊥ :=
  x.hyp.quadratic_of_lt x.h162 x.mbar inf_le_left inf_le_right
    (lt_of_le_of_lt (add_le_add hg.2 hg.1.1) hk)

theorem inf_ne_bot {k : ℕ} (x : Ctx188 D V₀ V H i j)
    (hk : k + i < mBar D.M V₀ V x.hyp.setting.isElemAbelian) {g : G}
    (hg : Gam188 V H (eOmegaZ H D.T) i k g) :
    eOmegaZ H D.T ⊓ conjSubgroup V₀ g ≠ ⊥ := by
  have hcomm := x.comm_le hk hg.1
    (B := vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) inf_le_left hg.2
  obtain ⟨d, hdDg, hdc⟩ : ∃ d ∈ vInH V H g,
      d ∉ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    by_contra h
    apply hg.1.2
    intro d hd
    by_contra hd'
    exact h ⟨d, hd, hd'⟩
  have he : ∃ e, e ∈ eOmegaZ H D.T ∧ e * d ≠ d * e := by
    by_contra h
    apply hdc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    by_contra hed
    exact h ⟨e, he, hed⟩
  obtain ⟨e, heE, hed⟩ := he
  have heB : e ∈ eOmegaZ H D.T ⊓ Subgroup.centralizer
      ((vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) : Subgroup G) :
        Set G) :=
    ⟨heE, Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hb.2 e heE).symm⟩
  have hmem : ⁅e, d⁆ ∈ ⁅eOmegaZ H D.T ⊓ Subgroup.centralizer
      ((vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) : Subgroup G) :
        Set G), vInH V H g⁆ :=
    Subgroup.commutator_mem_commutator heB hdDg
  intro hbot
  have h1 : ⁅e, d⁆ = 1 := by
    have hmem' := hcomm hmem
    rw [hbot] at hmem'
    simpa using hmem'
  exact hed ((commutatorElement_eq_one_iff_mul_comm).1 h1)

end Ctx188

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem conj_eq_of_inf_ne_bot (h : Hyp183 D V₀ V H i) {g g' : G}
    (hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' ≠ ⊥) :
    conjSubgroup V₀ g = conjSubgroup V₀ g' ∧ conjSubgroup V g = conjSubgroup V g' := by
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := (h.setting.ti₀ h.ne_bot).1
  have h0 : conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' = ⊥ ∨
      conjSubgroup V₀ g' = conjSubgroup V₀ g := by
    have ht := inf_conj_eq_bot_or_eq_conj hTI g (g⁻¹ * g')
    rwa [conjSubgroup_conjSubgroup, ← mul_assoc, mul_inv_cancel, one_mul] at ht
  rcases h0 with hbot | heq
  · exact absurd hbot hne
  have hV0 : conjSubgroup V₀ g = conjSubgroup V₀ g' := heq.symm
  have hmem : g * g'⁻¹ ∈ Subgroup.normalizer (V₀ : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    rw [← conjSubgroup_conjSubgroup, hV0, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one]
  rw [h.setting.normalizer₀ h.ne_bot] at hmem
  have hmemV : g * g'⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    rwa [h.setting.normalizer_eq]
  refine ⟨hV0, ?_⟩
  have hVV : conjSubgroup V (g * g'⁻¹) = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hmemV
  have ht := congrArg (fun X => conjSubgroup X g') hVV
  rwa [conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one] at ht

end Hyp183

namespace Gam188

variable {D : Data G} {V₀ V H : Subgroup G} {i j k : ℕ}

theorem conj {E : Subgroup G} (hE : H ≤ normalizer (E : Set G)) {g y : G} (hy : y ∈ H)
    (hg : Gam188 V H E i k g) : Gam188 V H E i k (g * y) := by
  have hHy : conjSubgroup H y = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hy)
  have hEy : conjSubgroup E y = E :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hE hy)
  have hCy : conjSubgroup (Subgroup.centralizer (E : Set G)) y =
      Subgroup.centralizer (E : Set G) := by
    rw [E3.conjSubgroup_centralizer, hEy]
  have hDy : vInH V H (g * y) = conjSubgroup (vInH V H g) y := vInH_mul g hy
  have hVy : conjSubgroup V (g * y) = conjSubgroup (conjSubgroup V g) y :=
    (conjSubgroup_conjSubgroup V g y).symm
  have hDinf : conjSubgroup V (g * y) ⊓ H = conjSubgroup (conjSubgroup V g ⊓ H) y := by
    rw [hVy, E3.conjSubgroup_inf, hHy]
  have hDstar : conjSubgroup (vInH V H g) y ⊓ Subgroup.centralizer (E : Set G) =
      conjSubgroup (vInH V H g ⊓ Subgroup.centralizer (E : Set G)) y := by
    rw [E3.conjSubgroup_inf, hCy]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hDinf, hVy, E3.mQuot_conjSubgroup]
    exact hg.1.1
  · intro hle
    apply hg.1.2
    rw [hDinf, ← hCy] at hle
    exact (E3.conjSubgroup_le_conjSubgroup_iff y).mp hle
  · rw [hDy, hDstar, E3.mQuot_conjSubgroup]
    exact hg.2

end Gam188

end CFSG.LocalAnalysis.WeakClosure81

end
