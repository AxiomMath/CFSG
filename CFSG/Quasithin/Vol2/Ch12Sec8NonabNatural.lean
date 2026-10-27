module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen
public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Background.G2Omega4PlusModel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.Om4Model
open scoped commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

theorem commutator_mem_inf_of_mem_pCoreOf {a b : G} (ha : a ∈ pCoreOf 2 (L ⊔ uOfL22 T M))
    (hb : b ∈ pCoreOf 2 (L ⊔ uOfL22 T M)) :
    a * b * a⁻¹ * b⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
  obtain ⟨w, hw, x, hx, rfl⟩ := h.exists_mul_of_mem_pCoreOf_sup hU hg ha
  obtain ⟨w', hw', x', hx', rfl⟩ := h.exists_mul_of_mem_pCoreOf_sup hU hg hb
  have hEN := h.sup_le_normalizer_inf_rconj_wOfU hU hg
  have hcE : ∀ i ∈ L ⊔ uOfL22 T M, ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      i * e * i⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g := fun i hi e he =>
    (Subgroup.mem_normalizer_iff.mp (hEN hi) e).mp he
  have hSI : pCoreOf 2 (L ⊔ uOfL22 T M) ≤ L ⊔ uOfL22 T M := pCoreOf_le 2 _
  have hwI : w ∈ L ⊔ uOfL22 T M := hSI (h.wOfU_le_pCoreOf hU hg hw)
  have hw'I : w' ∈ L ⊔ uOfL22 T M := hSI (h.wOfU_le_pCoreOf hU hg hw')
  have hVE : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := by
    rw [h.wOfU_inf_rconj_eq hU hg]
    exact h.VZ_le_inf_rconj hU hg
  have hZE : quasithinOmegaOneCenter T ≤ wOfU T M ⊓ rconj (wOfU T M) g :=
    h.omegaOneCenter_le_inf_rconj hU hg
  have hww : ⁅w, w'⁆ ∈ wOfU T M ⊓ rconj (wOfU T M) g :=
    hZE (h.commutator_mem_omegaOneCenter (wOfU_le_uOfL22 T M hw) (wOfU_le_uOfL22 T M hw'))
  have hxx : ⁅x, x'⁆ ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
    have hxUg : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hx
    have hx'Ug : x' ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hx'
    exact hVE (h.commutator_rconj_uOfL22_mem_VZ hU hg hxUg hx'Ug)
  have hwx : ∀ w ∈ wOfU T M, ∀ x ∈ rconj (wOfU T M) g,
      ⁅w, x⁆ ∈ wOfU T M ⊓ rconj (wOfU T M) g := fun w hw x hx =>
    h.commutator_wOfU_rconj_le hU hg (Subgroup.commutator_mem_commutator hw hx)
  have hxw : ⁅x, w'⁆ ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
    have := (wOfU T M ⊓ rconj (wOfU T M) g).inv_mem (hwx w' hw' x hx)
    rwa [commutatorElement_inv] at this
  have e : w * x * (w' * x') * (w * x)⁻¹ * (w' * x')⁻¹ =
      (w * ⁅x, w'⁆ * w⁻¹ * ⁅w, w'⁆) * (w' * (w * ⁅x, x'⁆ * w⁻¹ * ⁅w, x'⁆) * w'⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (wOfU T M ⊓ rconj (wOfU T M) g).mul_mem
    ((wOfU T M ⊓ rconj (wOfU T M) g).mul_mem (hcE w hwI _ hxw) hww)
    (hcE w' hw'I _ ((wOfU T M ⊓ rconj (wOfU T M) g).mul_mem (hcE w hwI _ hxx)
      (hwx w hw x' hx')))

theorem mul_self_mem_inf_of_mem_pCoreOf {a : G} (ha : a ∈ pCoreOf 2 (L ⊔ uOfL22 T M)) :
    a * a ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
  obtain ⟨w, hw, x, hx, rfl⟩ := h.exists_mul_of_mem_pCoreOf_sup hU hg ha
  have hEN := h.sup_le_normalizer_inf_rconj_wOfU hU hg
  have hcE : ∀ i ∈ L ⊔ uOfL22 T M, ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      i * e * i⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g := fun i hi e he =>
    (Subgroup.mem_normalizer_iff.mp (hEN hi) e).mp he
  have hSI : pCoreOf 2 (L ⊔ uOfL22 T M) ≤ L ⊔ uOfL22 T M := pCoreOf_le 2 _
  have hwI : w ∈ L ⊔ uOfL22 T M := hSI (h.wOfU_le_pCoreOf hU hg hw)
  have hVE : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := by
    rw [h.wOfU_inf_rconj_eq hU hg]
    exact h.VZ_le_inf_rconj hU hg
  have hZE : quasithinOmegaOneCenter T ≤ wOfU T M ⊓ rconj (wOfU T M) g :=
    h.omegaOneCenter_le_inf_rconj hU hg
  have hww : w * w ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
    have := h.sq_mem_omegaOneCenter (wOfU_le_uOfL22 T M hw)
    rw [pow_two] at this
    exact hZE this
  have hxx : x * x ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
    have hxUg : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hx
    have h1 := (h.l2Setting128 hU).rconj_sq_mem hxUg
    have h2 := (h.l2Setting128 hU).V₁_le_rconj_V hg.mem h1
    rw [pow_two] at h2
    exact hVE h2
  have hxw : ⁅x, w⁆ ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
    have := (wOfU T M ⊓ rconj (wOfU T M) g).inv_mem
      (h.commutator_wOfU_rconj_le hU hg (Subgroup.commutator_mem_commutator hw hx))
    rwa [commutatorElement_inv] at this
  have e : w * x * (w * x) = (w * ⁅x, w⁆ * w⁻¹) * (w * w) * (x * x) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (wOfU T M ⊓ rconj (wOfU T M) g).mul_mem
    ((wOfU T M ⊓ rconj (wOfU T M) g).mul_mem (hcE w hwI _ hxw) hww) hxx

theorem quotSetting : QuotSetting (L ⊔ uOfL22 T M) (pCoreOf 2 (L ⊔ uOfL22 T M))
    (wOfU T M ⊓ rconj (wOfU T M) g) where
  S₂_le := inf_le_left.trans (h.wOfU_le_pCoreOf hU hg)
  Sx_le := pCoreOf_le 2 _
  nS := fun _ hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hx) y).mp hy
  nS₂ := fun _ hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (h.sup_le_normalizer_inf_rconj_wOfU hU hg hx) y).mp hy
  abel := fun _ ha _ hb => h.commutator_mem_inf_of_mem_pCoreOf hU hg ha hb
  sq := fun _ ha => h.mul_self_mem_inf_of_mem_pCoreOf hU hg ha

end

end Hyp1281Two

end CFSG.Quasithin
