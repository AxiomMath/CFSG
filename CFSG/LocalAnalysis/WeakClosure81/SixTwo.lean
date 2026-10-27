module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp62 (M V₀ V : Subgroup G) : Prop where
  isElemAbelian : IsElemAbelian 2 V
  normalizer_eq : Subgroup.normalizer (V : Set G) = M
  le : V₀ ≤ V
  normal : M ≤ Subgroup.normalizer (V₀ : Set G)
  normalizer_le : ∀ X : Subgroup G, X ≤ V₀ → X ≠ ⊥ → Subgroup.normalizer (X : Set G) ≤ M

namespace Hyp62

theorem le_M {M V₀ V : Subgroup G} (h : Hyp62 M V₀ V) : V ≤ M := by
  rw [← h.normalizer_eq]
  exact Subgroup.le_normalizer

theorem le_normalizer {M V₀ V : Subgroup G} (h : Hyp62 M V₀ V) :
    V ≤ Subgroup.normalizer (V₀ : Set G) :=
  h.le_M.trans h.normal

theorem le_stabTil {M V₀ V : Subgroup G} (h : Hyp62 M V₀ V) {g : G} {D : Subgroup G}
    (hD : D ≤ conjSubgroup V g ⊓ M) : D ≤ stabTil V₀ V :=
  le_inf ((hD.trans inf_le_right).trans (le_of_eq h.normalizer_eq.symm))
    ((hD.trans inf_le_right).trans h.normal)

end Hyp62

@[expose] noncomputable def preCTilde (V₀ V D : Subgroup G) (hV : IsElemAbelian 2 V) :
    Subgroup G :=
  preTil V₀ V hV (fixV (barSub V₀ V hV D))

theorem preCTilde_le (V₀ V D : Subgroup G) (hV : IsElemAbelian 2 V) :
    preCTilde V₀ V D hV ≤ V :=
  preTil_le V₀ V hV _

theorem le_preCTilde {V₀ V D : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀V : V₀ ≤ V) :
    V₀ ≤ preCTilde V₀ V D hV := by
  intro x hx
  rw [preCTilde, mem_preTil]
  refine ⟨IntMod.mk hV ⟨x, hV₀V hx⟩, rfl, ?_⟩
  rw [mem_fixV]
  rintro φ hφ
  obtain ⟨d, -, rfl⟩ := (mem_barSub V₀ V hV D φ).1 hφ
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
  have hdN : (d : G) ∈ Subgroup.normalizer (V₀ : Set G) := stabTil_le_normalizer₀ V₀ V d.2
  have hconj : (d : G) * x * (d : G)⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hdN x).1 hx
  exact V₀.mul_mem hconj (V₀.inv_mem hx)

theorem mem_preCTilde_iff {V₀ V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hD : D ≤ stabTil V₀ V) {u : G} (hu : u ∈ V) :
    u ∈ preCTilde V₀ V D hV ↔ ∀ d ∈ D, ⁅u, d⁆ ∈ V₀ := by
  rw [preCTilde, mem_preTil_iff_of_mem V₀ V hV _ hu, mem_fixV]
  constructor
  · intro h d hd
    have hφ := h (actTil V₀ V hV ⟨d, hD hd⟩)
      (actTil_mem_barSub V₀ V hV (X := D) (g := d) hd (hD hd))
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hφ
    change d * u * d⁻¹ * u⁻¹ ∈ V₀ at hφ
    have hconj : ⁅u, d⁆ = ⁅d, u⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [hconj]
    exact V₀.inv_mem hφ
  · intro h φ hφ
    obtain ⟨d, hdD, rfl⟩ := (mem_barSub V₀ V hV D φ).1 hφ
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    change (d : G) * u * (d : G)⁻¹ * u⁻¹ ∈ V₀
    have hdu : ⁅(d : G), u⁆ ∈ V₀ := by
      have h1 := h (d : G) hdD
      have hconj : ⁅u, (d : G)⁆ = ⁅(d : G), u⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [hconj] at h1
      simpa using V₀.inv_mem h1
    simpa only [commutatorElement_def] using hdu

theorem rMV_le_mQuot (M V X : Subgroup G) (hX : X ≤ V)
    (hC : ¬ Subgroup.centralizer (X : Set G) ≤ M) :
    rMV M V ≤ (E3.mQuot V X : ℕ∞) :=
  iInf₂_le X ⟨hX, hC⟩

theorem centralizer_le_of_mQuot_lt_rMV {M V X : Subgroup G} (hX : X ≤ V)
    (h : (E3.mQuot V X : ℕ∞) < rMV M V) :
    Subgroup.centralizer (X : Set G) ≤ M := by
  by_contra hc
  exact absurd (rMV_le_mQuot M V X hX hc) (not_le.2 h)

theorem rMV_conj {M V : Subgroup G} (h : Subgroup.normalizer (V : Set G) = M) (g : G) :
    rMV (conjSubgroup M g) (conjSubgroup V g) = rMV M V := by
  have h' : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup M g := by
    rw [← conjSubgroup_normalizer V g, h]
  rw [rMV_eq_rParam h', E3.rParam_conj, ← rMV_eq_rParam h]

theorem conjSubgroup_commElt (W : Subgroup G) (t g : G) :
    conjSubgroup (commElt W t) g = commElt (conjSubgroup W g) (g⁻¹ * t * g) := by
  unfold commElt conjSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨g⁻¹ * w * g, ⟨w, hw, ?_⟩, ?_⟩
    · show (MulAut.conj g⁻¹) w = g⁻¹ * w * g
      rw [MulAut.conj_apply, inv_inv]
    · show (MulAut.conj g⁻¹) (w⁻¹ * t⁻¹ * w * t) = _
      rw [MulAut.conj_apply, inv_inv]
      group
  · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨w⁻¹ * t⁻¹ * w * t, ⟨w, hw, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem conjSubgroup_centralizer_singleton (t g : G) :
    conjSubgroup (Subgroup.centralizer ({t} : Set G)) g =
      Subgroup.centralizer ({g⁻¹ * t * g} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g⁻¹ * t * g) = g⁻¹ * (g * x * g⁻¹ * t) * g := by group
      _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * t * g) * x := by group
  · intro h
    calc (g * x * g⁻¹) * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [h]
      _ = t * (g * x * g⁻¹) := by group

theorem conjSubgroup_le_centralizer_singleton_iff (W : Subgroup G) (t g : G) :
    conjSubgroup W g⁻¹ ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set G) ↔
      W ≤ Subgroup.centralizer ({t} : Set G) := by
  constructor
  · intro h w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : g * w * g⁻¹ ∈ conjSubgroup W g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
      rwa [this]
    have h1 := h hmem
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have : g * (w * t) * g⁻¹ = g * (t * w) * g⁻¹ := by
      calc g * (w * t) * g⁻¹ = (g * w * g⁻¹) * (g * t * g⁻¹) := by group
        _ = (g * t * g⁻¹) * (g * w * g⁻¹) := h1
        _ = g * (t * w) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  · intro h y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mem_conjSubgroup_iff] at hy
    have hy' : g⁻¹ * y * g ∈ W := by simpa only [inv_inv] using hy
    have h1 := h hy'
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    calc y * (g * t * g⁻¹) = g * ((g⁻¹ * y * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * t * g⁻¹) * y := by group

theorem mem_propN_conj_forward {P : Subgroup G → Prop} {n : ℕ} {M V U : Subgroup G} {g : G}
    (h : U ∈ propN P n (conjSubgroup M g) (conjSubgroup V g)) :
    conjSubgroup U g⁻¹ ∈ propN (fun Z => P (conjSubgroup Z g)) n M V := by
  obtain ⟨hUV, t, ht, h2, W, hWV, hmW, hUW, hWt, hPW⟩ := h
  refine ⟨?_, g * t * g⁻¹, ?_, ?_, conjSubgroup W g⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · have := conjSubgroup_mono_left g⁻¹ hUV
    rwa [conjSubgroup_conj_inv] at this
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mem_conjSubgroup_iff.1 ht.1
    · rw [← conjSubgroup_centralizer U g⁻¹, mem_conjSubgroup_inv_iff]
      have : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [this]
      exact ht.2
  · obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    have hord : orderOf (g * t * g⁻¹) = orderOf t :=
      (SemiconjBy.orderOf_eq g (show SemiconjBy g t (g * t * g⁻¹) from by
        rw [SemiconjBy]; group)).symm
    rw [hord, hk]
  · have := conjSubgroup_mono_left g⁻¹ hWV
    rwa [conjSubgroup_conj_inv] at this
  · have hm := mQuot_conjSubgroup (conjSubgroup V g) W g⁻¹
    rw [conjSubgroup_conj_inv] at hm
    rw [hm]
    exact hmW
  · exact conjSubgroup_mono_left g⁻¹ hUW
  · intro hWc
    exact hWt ((conjSubgroup_le_centralizer_singleton_iff W t g).1 hWc)
  · show P (conjSubgroup (commElt (conjSubgroup W g⁻¹) (g * t * g⁻¹)) g)
    rw [conjSubgroup_commElt, conjSubgroup_inv_conj]
    have : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rw [this]
    exact hPW

theorem propB_conj {M Z : Subgroup G} (g : G) :
    PropB (conjSubgroup M g) (conjSubgroup Z g) ↔ PropB M Z := by
  unfold PropB
  rw [← conjSubgroup_centralizer Z g, conjSubgroup_le_conjSubgroup_iff]

theorem propD_conj {M Z : Subgroup G} (g : G) :
    PropD (conjSubgroup M g) (conjSubgroup Z g) ↔ PropD M Z := by
  unfold PropD
  constructor
  · intro h x hx
    have hz : g⁻¹ * x * g ∈ conjSubgroup Z g := by
      rw [mem_conjSubgroup_iff]
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [this]
    have h1 := h _ hz
    rw [← conjSubgroup_centralizer_singleton x g, conjSubgroup_le_conjSubgroup_iff] at h1
    exact h1
  · intro h z hz
    rw [mem_conjSubgroup_iff] at hz
    have h1 := h _ hz
    have h2 : Subgroup.centralizer ({z} : Set G) =
        conjSubgroup (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) g := by
      rw [conjSubgroup_centralizer_singleton (g * z * g⁻¹) g]
      congr 1
      group
    rw [h2, conjSubgroup_le_conjSubgroup_iff]
    exact h1

theorem rankThreeGamma_conjSubgroup (k p : ℕ) (Z : Subgroup G) (g : G) :
    rankThreeGamma k p (conjSubgroup Z g) = conjSubgroup (rankThreeGamma k p Z) g := by
  unfold rankThreeGamma conjSubgroup
  exact CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj g⁻¹ Z

theorem propC_conj {M Z : Subgroup G} (g : G) :
    PropC (conjSubgroup M g) (conjSubgroup Z g) ↔ PropC M Z := by
  unfold PropC
  constructor
  · rintro ⟨x, hx, hle⟩
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · intro h
      exact hx (mem_conjSubgroup_iff.2 h)
    · have hle' := conjSubgroup_mono_left g⁻¹ hle
      rw [rankThreeGamma_conjSubgroup, conjSubgroup_conj_inv] at hle'
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at hle'
      simpa only [mul_assoc] using hle'
  · rintro ⟨x, hx, hle⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · intro h
      apply hx
      rw [mem_conjSubgroup_iff] at h
      have h' : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [h'] at h
    · rw [rankThreeGamma_conjSubgroup]
      have hxy : conjSubgroup (conjSubgroup M g) (g⁻¹ * x * g) =
          conjSubgroup (conjSubgroup M x) g := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
        congr 1
        group
      rw [hxy]
      exact conjSubgroup_mono_left g hle

theorem propN_congr {P Q : Subgroup G → Prop} (h : ∀ Z, P Z ↔ Q Z) (n : ℕ) (M V : Subgroup G) :
    propN P n M V = propN Q n M V := by
  ext U
  constructor
  · rintro ⟨h1, t, ht, h2, W, h3, h4, h5, h6, h7⟩
    exact ⟨h1, t, ht, h2, W, h3, h4, h5, h6, (h _).1 h7⟩
  · rintro ⟨h1, t, ht, h2, W, h3, h4, h5, h6, h7⟩
    exact ⟨h1, t, ht, h2, W, h3, h4, h5, h6, (h _).2 h7⟩

theorem mem_calBn_conj {n : ℕ} {M V U : Subgroup G} {g : G}
    (h : U ∈ calBn n (conjSubgroup M g) (conjSubgroup V g)) :
    conjSubgroup U g⁻¹ ∈ calBn n M V := by
  have h1 := mem_propN_conj_forward (P := PropB (conjSubgroup M g)) h
  rw [propN_congr (fun Z => propB_conj g) n M V] at h1
  exact h1

theorem mem_calCn_conj {n : ℕ} {M V U : Subgroup G} {g : G}
    (h : U ∈ calCn n (conjSubgroup M g) (conjSubgroup V g)) :
    conjSubgroup U g⁻¹ ∈ calCn n M V := by
  have h1 := mem_propN_conj_forward (P := PropC (conjSubgroup M g)) h
  rw [propN_congr (fun Z => propC_conj g) n M V] at h1
  exact h1

theorem mem_calDn_conj {n : ℕ} {M V U : Subgroup G} {g : G}
    (h : U ∈ calDn n (conjSubgroup M g) (conjSubgroup V g)) :
    conjSubgroup U g⁻¹ ∈ calDn n M V := by
  have h1 := mem_propN_conj_forward (P := PropD (conjSubgroup M g)) h
  rw [propN_congr (fun Z => propD_conj g) n M V] at h1
  exact h1

theorem betaN_conj_le (n : ℕ) (M V : Subgroup G) (g : G) :
    betaN n (conjSubgroup M g) (conjSubgroup V g) ≤ betaN n M V := by
  change (⨅ U ∈ calBn n (conjSubgroup M g) (conjSubgroup V g),
      (E3.mQuot (conjSubgroup V g) U : ℕ∞)) ≤
    (⨅ U ∈ calBn n M V, (E3.mQuot V U : ℕ∞))
  refine le_iInf₂ fun U hU => ?_
  have hU' : U ∈ calBn n (conjSubgroup (conjSubgroup M g) g⁻¹)
      (conjSubgroup (conjSubgroup V g) g⁻¹) := by
    rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv]
  have h1 : conjSubgroup U g ∈ calBn n (conjSubgroup M g) (conjSubgroup V g) := by
    have := mem_calBn_conj (M := conjSubgroup M g) (V := conjSubgroup V g) (g := g⁻¹) hU'
    simpa only [inv_inv] using this
  have h2 : betaN n (conjSubgroup M g) (conjSubgroup V g) ≤
      (E3.mQuot (conjSubgroup V g) (conjSubgroup U g) : ℕ∞) :=
    iInf₂_le (conjSubgroup U g) h1
  have hm : E3.mQuot (conjSubgroup V g) (conjSubgroup U g) = E3.mQuot V U :=
    mQuot_conjSubgroup V U g
  rwa [hm] at h2

theorem betaN_conj (n : ℕ) (M V : Subgroup G) (g : G) :
    betaN n (conjSubgroup M g) (conjSubgroup V g) = betaN n M V := by
  refine le_antisymm (betaN_conj_le n M V g) ?_
  have := betaN_conj_le n (conjSubgroup M g) (conjSubgroup V g) g⁻¹
  rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv] at this

theorem gammaN_conj_le (n : ℕ) (M V : Subgroup G) (g : G) :
    gammaN n (conjSubgroup M g) (conjSubgroup V g) ≤ gammaN n M V := by
  change (⨅ U ∈ calCn n (conjSubgroup M g) (conjSubgroup V g),
      (E3.mQuot (conjSubgroup V g) U : ℕ∞)) ≤
    (⨅ U ∈ calCn n M V, (E3.mQuot V U : ℕ∞))
  refine le_iInf₂ fun U hU => ?_
  have hU' : U ∈ calCn n (conjSubgroup (conjSubgroup M g) g⁻¹)
      (conjSubgroup (conjSubgroup V g) g⁻¹) := by
    rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv]
  have h1 : conjSubgroup U g ∈ calCn n (conjSubgroup M g) (conjSubgroup V g) := by
    have := mem_calCn_conj (M := conjSubgroup M g) (V := conjSubgroup V g) (g := g⁻¹) hU'
    simpa only [inv_inv] using this
  have h2 : gammaN n (conjSubgroup M g) (conjSubgroup V g) ≤
      (E3.mQuot (conjSubgroup V g) (conjSubgroup U g) : ℕ∞) :=
    iInf₂_le (conjSubgroup U g) h1
  have hm : E3.mQuot (conjSubgroup V g) (conjSubgroup U g) = E3.mQuot V U :=
    mQuot_conjSubgroup V U g
  rwa [hm] at h2

theorem gammaN_conj (n : ℕ) (M V : Subgroup G) (g : G) :
    gammaN n (conjSubgroup M g) (conjSubgroup V g) = gammaN n M V := by
  refine le_antisymm (gammaN_conj_le n M V g) ?_
  have := gammaN_conj_le n (conjSubgroup M g) (conjSubgroup V g) g⁻¹
  rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv] at this

theorem deltaN_conj_le (n : ℕ) (M V : Subgroup G) (g : G) :
    deltaN n (conjSubgroup M g) (conjSubgroup V g) ≤ deltaN n M V := by
  change (⨅ U ∈ calDn n (conjSubgroup M g) (conjSubgroup V g),
      (E3.mQuot (conjSubgroup V g) U : ℕ∞)) ≤
    (⨅ U ∈ calDn n M V, (E3.mQuot V U : ℕ∞))
  refine le_iInf₂ fun U hU => ?_
  have hU' : U ∈ calDn n (conjSubgroup (conjSubgroup M g) g⁻¹)
      (conjSubgroup (conjSubgroup V g) g⁻¹) := by
    rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv]
  have h1 : conjSubgroup U g ∈ calDn n (conjSubgroup M g) (conjSubgroup V g) := by
    have := mem_calDn_conj (M := conjSubgroup M g) (V := conjSubgroup V g) (g := g⁻¹) hU'
    simpa only [inv_inv] using this
  have h2 : deltaN n (conjSubgroup M g) (conjSubgroup V g) ≤
      (E3.mQuot (conjSubgroup V g) (conjSubgroup U g) : ℕ∞) :=
    iInf₂_le (conjSubgroup U g) h1
  have hm : E3.mQuot (conjSubgroup V g) (conjSubgroup U g) = E3.mQuot V U :=
    mQuot_conjSubgroup V U g
  rwa [hm] at h2

theorem deltaN_conj (n : ℕ) (M V : Subgroup G) (g : G) :
    deltaN n (conjSubgroup M g) (conjSubgroup V g) = deltaN n M V := by
  refine le_antisymm (deltaN_conj_le n M V g) ?_
  have := deltaN_conj_le n (conjSubgroup M g) (conjSubgroup V g) g⁻¹
  rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv] at this

theorem mQuot_inf_centralizer_le_mSub {V₀ V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hDV : D ≤ Subgroup.normalizer (V : Set G)) (hV₀V : V₀ ≤ V)
    (hV₀N : V ≤ Subgroup.normalizer (V₀ : Set G))
    {u : G} (hu : u ∈ V) (huD : ∀ d ∈ D, ⁅u, d⁆ ∈ V₀) :
    E3.mQuot D (D ⊓ Subgroup.centralizer ({u} : Set G)) ≤ mSub V₀ := by
  haveI : Subgroup.Normalizes D V := ⟨hDV⟩
  let x : V := ⟨u, hu⟩
  have hstab : MulAction.stabilizer ↥D x =
      (D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D := by
    ext d
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨d.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (d : G) * u * (d : G)⁻¹ = u := by
        have := congrArg (fun y : V => (y : G)) h
        simpa [x] using this
      calc (d : G) * u = (d : G) * u * (d : G)⁻¹ * (d : G) := by group
        _ = u * (d : G) := by rw [h1]
    · intro h
      obtain ⟨-, hc⟩ := h
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      apply Subtype.ext
      simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      calc (d : G) * u * (d : G)⁻¹ = ((d : G) * u) * (d : G)⁻¹ := rfl
        _ = (u * (d : G)) * (d : G)⁻¹ := by rw [hc]
        _ = u := by group
  have hcard : Nat.card (MulAction.orbit ↥D x) ≤ Nat.card V₀ := by
    let f : MulAction.orbit ↥D x → V₀ := fun y => ⟨u⁻¹ * (y : V), by
      obtain ⟨d, hd⟩ := MulAction.mem_orbit_iff.1 y.2
      have hy : ((y : V) : G) = (d : G) * u * (d : G)⁻¹ := by
        rw [← hd, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      rw [hy]
      have hdu : ⁅u, (d : G)⁆ ∈ V₀ := huD (d : G) d.2
      have hconj : u⁻¹ * ((d : G) * u * (d : G)⁻¹) = u⁻¹ * ⁅u, (d : G)⁆⁻¹ * u := by
        rw [commutatorElement_def]; group
      rw [hconj]
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.1 (hV₀N (V.inv_mem hu)) ⁅u, (d : G)⁆⁻¹).1
          (V₀.inv_mem hdu)⟩
    refine Nat.card_le_card_of_injective f fun y y' h => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (a := u⁻¹) (Subtype.ext_iff.1 h)
  have hidx : (D ⊓ Subgroup.centralizer ({u} : Set G)).relIndex D =
      Nat.card (MulAction.orbit ↥D x) := by
    show ((D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D).index =
      Nat.card (MulAction.orbit ↥D x)
    rw [← hstab, MulAction.index_stabilizer]
    exact (Nat.card_coe_set_eq _).symm
  have hV₀pg : IsPGroup 2 V₀ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hV₀V hV)
  calc E3.mQuot D (D ⊓ Subgroup.centralizer ({u} : Set G))
      = padicValNat 2 ((D ⊓ Subgroup.centralizer ({u} : Set G)).relIndex D) := rfl
    _ = padicValNat 2 (Nat.card (MulAction.orbit ↥D x)) := by rw [hidx]
    _ ≤ Nat.log 2 (Nat.card (MulAction.orbit ↥D x)) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (Nat.card V₀) := Nat.log_mono_right hcard
    _ = Nat.log 2 (2 ^ mSub V₀) := by rw [card_eq_two_pow_mSub hV₀pg]
    _ = mSub V₀ := Nat.log_pow (by norm_num) _


theorem pRank_bot_eq_zero : CFSG.Open.pRank 2 (⊥ : Subgroup G) = 0 := by
  have h : CFSG.Open.pRank 2 (⊥ : Subgroup G) ≤ 0 :=
    CFSG.SectionRank.pRank_le one_lt_two fun E hE _ => by
      have hEbot : E = ⊥ := le_bot_iff.1 hE
      subst hEbot
      simp
  omega

theorem rankThreeGamma_le_of_normalizer_le {M V₀ Z : Subgroup G}
    (h : ∀ X : Subgroup G, X ≤ V₀ → X ≠ ⊥ → Subgroup.normalizer (X : Set G) ≤ M)
    (hZ : Z ≤ V₀) : rankThreeGamma 1 2 Z ≤ M := by
  unfold rankThreeGamma GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQZ, hk, rfl⟩
  by_cases hQ : Q = ⊥
  · subst hQ
    rw [pRank_bot_eq_zero] at hk
    omega
  · exact h Q (hQZ.trans hZ) hQ

theorem commutatorElement_inv_inv_mem {V₀ : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (V₀ : Set G)) (hb : b ∈ Subgroup.normalizer (V₀ : Set G))
    (h : ⁅a, b⁆ ∈ V₀) : ⁅a⁻¹, b⁻¹⁆ ∈ V₀ := by
  have h1 : ⁅b, a⁆ ∈ V₀ := by
    have hinv : ⁅a, b⁆⁻¹ ∈ V₀ := V₀.inv_mem h
    rwa [show ⁅b, a⁆ = ⁅a, b⁆⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
  have h2 : ⁅a⁻¹, b⁆ ∈ V₀ := by
    have hmem := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha) ⁅b, a⁆).1 h1
    have heq : a⁻¹ * ⁅b, a⁆ * (a⁻¹)⁻¹ = ⁅a⁻¹, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rwa [heq] at hmem
  have h3 : ⁅a⁻¹, b⁻¹⁆ ∈ V₀ := by
    have hba : ⁅b, a⁻¹⁆ ∈ V₀ := by
      have hinv : ⁅a⁻¹, b⁆⁻¹ ∈ V₀ := V₀.inv_mem h2
      rwa [show ⁅b, a⁻¹⁆ = ⁅a⁻¹, b⁆⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
    have hmem := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) ⁅b, a⁻¹⁆).1 hba
    have heq : b⁻¹ * ⁅b, a⁻¹⁆ * (b⁻¹)⁻¹ = ⁅a⁻¹, b⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rwa [heq] at hmem
  exact h3

theorem commElt_le_of_commutator_mem {V₀ W : Subgroup G} {t : G}
    (hW : W ≤ Subgroup.normalizer (V₀ : Set G)) (ht : t ∈ Subgroup.normalizer (V₀ : Set G))
    (h : ∀ w ∈ W, ⁅t, w⁆ ∈ V₀) : commElt W t ≤ V₀ := by
  rw [commElt, Subgroup.closure_le]
  rintro x ⟨w, hw, rfl⟩
  have hwt : ⁅w, t⁆ ∈ V₀ := by
    have hinv : ⁅t, w⁆⁻¹ ∈ V₀ := V₀.inv_mem (h w hw)
    rwa [show ⁅w, t⁆ = ⁅t, w⁆⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
  have := commutatorElement_inv_inv_mem (hW hw) ht hwt
  simpa [commutatorElement_def] using this

theorem six_two_one {M V₀ V D : Subgroup G} (h : Hyp62 M V₀ V) {g : G}
    (hD : D ≤ conjSubgroup V g ⊓ M)
    (hr : ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) < rMV M V) :
    preCTilde V₀ V D h.isElemAbelian ≤ conjSubgroup M g := by
  intro u hu
  have huV : u ∈ V := preCTilde_le V₀ V D h.isElemAbelian hu
  have huD : ∀ d ∈ D, ⁅u, d⁆ ∈ V₀ :=
    (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) huV).1 hu
  have hDV : D ≤ Subgroup.normalizer (V : Set G) :=
    (hD.trans inf_le_right).trans (le_of_eq h.normalizer_eq.symm)
  have hCD : D ⊓ Subgroup.centralizer ({u} : Set G) ≤
      conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G) :=
    le_inf (inf_le_left.trans (hD.trans inf_le_left)) inf_le_right
  have hbound : E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)) ≤
      E3.mQuot (conjSubgroup V g) D + mSub V₀ := by
    calc E3.mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G))
        ≤ E3.mQuot (conjSubgroup V g) (D ⊓ Subgroup.centralizer ({u} : Set G)) :=
          E3.mQuot_mono hCD
      _ = E3.mQuot D (D ⊓ Subgroup.centralizer ({u} : Set G)) +
            E3.mQuot (conjSubgroup V g) D :=
          E3.mQuot_add inf_le_left (hD.trans inf_le_left)
      _ ≤ mSub V₀ + E3.mQuot (conjSubgroup V g) D :=
          Nat.add_le_add_right
            (mQuot_inf_centralizer_le_mSub h.isElemAbelian hDV h.le h.le_normalizer huV huD) _
      _ = E3.mQuot (conjSubgroup V g) D + mSub V₀ := Nat.add_comm _ _
  have hlt : (E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)) : ℕ∞) < rMV M V :=
    lt_of_le_of_lt (by exact_mod_cast hbound) hr
  have hcent := centralizer_le_of_mQuot_lt_rMV (M := conjSubgroup M g) (V := conjSubgroup V g)
    inf_le_left (by
      rw [← rMV_conj h.normalizer_eq g] at hlt
      exact hlt)
  have humem : u ∈ Subgroup.centralizer
      ((conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
  exact hcent humem


theorem six_two_two {M V₀ V D : Subgroup G} (h : Hyp62 M V₀ V) {g : G}
    (hD : D ≤ conjSubgroup V g ⊓ M)
    (hr : ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) < rMV M V)
    (hcase : ¬ conjSubgroup V g ≤ M ∨
      ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) <
        gammaN (E3.mQuot (conjSubgroup V g) D) M V) :
    ⁅preCTilde V₀ V D h.isElemAbelian, D⁆ = ⊥ := by
  set U := preCTilde V₀ V D h.isElemAbelian with hUdef
  have hU_Mg : U ≤ conjSubgroup M g := six_two_one h hD hr
  have hDV : D ≤ Subgroup.normalizer (V : Set G) :=
    (hD.trans inf_le_right).trans (le_of_eq h.normalizer_eq.symm)
  have hcommV₀ : ⁅U, D⁆ ≤ V₀ := by
    rw [Subgroup.commutator_le]
    intro u hu d hd
    exact (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD)
      (preCTilde_le V₀ V D h.isElemAbelian hu)).1 hu d hd
  by_contra hne
  have hex : ∃ u ∈ U, ∃ d ∈ D, ⁅u, d⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine le_bot_iff.1 ?_
    rw [Subgroup.commutator_le]
    intro u hu d hd
    rw [Subgroup.mem_bot]
    exact hcon u hu d hd
  obtain ⟨u, hu, d, hd, hne1⟩ := hex
  have huV : u ∈ V := preCTilde_le V₀ V D h.isElemAbelian hu
  have huD : ∀ e ∈ D, ⁅u, e⁆ ∈ V₀ :=
    (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) huV).1 hu
  rcases hcase with hcase1 | hcase2
  · have hcommVg : ⁅U, D⁆ ≤ conjSubgroup V g := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haN : a ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
        have h1 : conjSubgroup M g = Subgroup.normalizer (conjSubgroup V g : Set G) := by
          rw [← conjSubgroup_normalizer V g, h.normalizer_eq]
        exact h1 ▸ hU_Mg ha
      have hbV : b ∈ conjSubgroup V g := (hD hb).1
      rw [commutatorElement_def]
      exact (conjSubgroup V g).mul_mem ((Subgroup.mem_normalizer_iff.1 haN b).1 hbV)
        ((conjSubgroup V g).inv_mem hbV)
    have hVg_cent : conjSubgroup V g ≤
        Subgroup.centralizer ((⁅U, D⁆ : Subgroup G) : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (B2F.isElemAbelian_comm (isElemAbelian_conjSubgroup h.isElemAbelian g) hv
        (hcommVg hx)).symm
    exact hcase1 (hVg_cent.trans ((Subgroup.centralizer_le_normalizer _).trans
      (h.normalizer_le _ hcommV₀ hne)))
  · have hgM : g ∉ M := by
      intro hg
      apply hne1
      have hgN : g ∈ Subgroup.normalizer (V : Set G) := by rwa [h.normalizer_eq]
      have hVg : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.2 hgN
      have hdV : d ∈ V := by
        have := (hD hd).1
        rwa [hVg] at this
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact B2F.isElemAbelian_comm h.isElemAbelian huV hdV
    have hU'cal : D ⊓ Subgroup.centralizer ({u} : Set G) ∈
        calCn (E3.mQuot (conjSubgroup V g) D) (conjSubgroup M g) (conjSubgroup V g) := by
      refine ⟨?_, u, ?_, ?_, D, ?_, ?_, ?_, ?_, ?_⟩
      · exact inf_le_left.trans (hD.trans inf_le_left)
      · refine Subgroup.mem_inf.2 ⟨hU_Mg hu, ?_⟩
        refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
        exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
      · have h2 : u ^ 2 = 1 := h.isElemAbelian.2 u huV
        have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h2
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
        · exact ⟨0, by simp [h1]⟩
        · exact ⟨1, by simp [h1]⟩
      · exact hD.trans inf_le_left
      · exact le_rfl
      · exact inf_le_left
      · intro hDc
        apply hne1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hDc hd)).symm
      · refine ⟨g⁻¹, ?_, ?_⟩
        · intro hg'
          apply hgM
          have h1 : g⁻¹ ∈ M := by
            have := mem_conjSubgroup_iff.1 hg'
            simpa using this
          simpa using M.inv_mem h1
        · have hMg : conjSubgroup (conjSubgroup M g) g⁻¹ = M := conjSubgroup_conj_inv M g
          rw [hMg]
          exact rankThreeGamma_le_of_normalizer_le h.normalizer_le
            (commElt_le_of_commutator_mem ((hD.trans inf_le_right).trans h.normal)
              (h.le_normalizer huV) huD)
    have hmq : E3.mQuot (conjSubgroup V g) (D ⊓ Subgroup.centralizer ({u} : Set G)) ≤
        E3.mQuot (conjSubgroup V g) D + mSub V₀ := by
      calc E3.mQuot (conjSubgroup V g) (D ⊓ Subgroup.centralizer ({u} : Set G))
          = E3.mQuot D (D ⊓ Subgroup.centralizer ({u} : Set G)) +
              E3.mQuot (conjSubgroup V g) D :=
            E3.mQuot_add inf_le_left (hD.trans inf_le_left)
        _ ≤ mSub V₀ + E3.mQuot (conjSubgroup V g) D :=
            Nat.add_le_add_right
              (mQuot_inf_centralizer_le_mSub h.isElemAbelian hDV h.le h.le_normalizer huV huD) _
        _ = E3.mQuot (conjSubgroup V g) D + mSub V₀ := Nat.add_comm _ _
    have hle : gammaN (E3.mQuot (conjSubgroup V g) D) M V ≤
        ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) := by
      have h2 : gammaN (E3.mQuot (conjSubgroup V g) D) (conjSubgroup M g) (conjSubgroup V g) ≤
          (E3.mQuot (conjSubgroup V g) (D ⊓ Subgroup.centralizer ({u} : Set G)) : ℕ∞) :=
        iInf₂_le _ hU'cal
      rw [gammaN_conj (E3.mQuot (conjSubgroup V g) D) M V g] at h2
      exact h2.trans (by exact_mod_cast hmq)
    exact absurd hcase2 (not_lt.2 hle)


theorem six_two_three {M V₀ V D : Subgroup G} (h : Hyp62 M V₀ V) {g : G}
    (hD : D ≤ conjSubgroup V g ⊓ M)
    (hr : ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) < rMV M V)
    (hVg : ¬ V ≤ conjSubgroup M g)
    (hβ : (E3.mQuot (conjSubgroup V g) D : ℕ∞) <
      betaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V) :
    ⁅V ⊓ Subgroup.centralizer (D : Set G), conjSubgroup V g ⊓ M⁆ = ⊥ := by
  set B := conjSubgroup V g ⊓ M with hBdef
  set CV := V ⊓ Subgroup.centralizer (D : Set G) with hCVdef
  have hU_Mg : preCTilde V₀ V D h.isElemAbelian ≤ conjSubgroup M g := six_two_one h hD hr
  by_contra hne
  have hex : ∃ c ∈ CV, ∃ b ∈ B, ⁅c, b⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine le_bot_iff.1 ?_
    rw [Subgroup.commutator_le]
    intro c hc b hb
    rw [Subgroup.mem_bot]
    exact hcon c hc b hb
  obtain ⟨c, hc, b, hb, hcb⟩ := hex
  have hcV : c ∈ V := (Subgroup.mem_inf.1 hc).1
  have hcC : c ∈ Subgroup.centralizer (D : Set G) := (Subgroup.mem_inf.1 hc).2
  have hbVg : b ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hb).1
  have hcU : c ∈ preCTilde V₀ V D h.isElemAbelian := by
    refine (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) hcV).2 fun d hd => ?_
    have h1 : ⁅c, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_iff.1 hcC d hd).symm
    rw [h1]
    exact V₀.one_mem
  have hcMg : c ∈ conjSubgroup M g := hU_Mg hcU
  have hD_CB : D ≤ B ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine le_inf hD fun d hd => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hcC d hd
  have hcB2 : c ∈ conjSubgroup M g ⊓
      Subgroup.centralizer ((B ⊓ Subgroup.centralizer ({c} : Set G)) : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hcMg, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
  have h2elem : ∃ k, orderOf c = 2 ^ k := by
    have h2 : c ^ 2 = 1 := h.isElemAbelian.2 c hcV
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact ⟨0, by simp [h1]⟩
    · exact ⟨1, by simp [h1]⟩
  have hBnotC : ¬ B ≤ Subgroup.centralizer ({c} : Set G) := by
    intro hBc
    exact hcb (commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hBc hb)).symm)
  by_cases hPB : PropB (conjSubgroup M g) (commElt B c)
  · have hcal : B ⊓ Subgroup.centralizer ({c} : Set G) ∈
        calBn (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M))
          (conjSubgroup M g) (conjSubgroup V g) :=
      ⟨(inf_le_left.trans inf_le_left),
        c, hcB2, h2elem, B, inf_le_left, le_rfl, inf_le_left, hBnotC, hPB⟩
    have hle : betaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V ≤
        (E3.mQuot (conjSubgroup V g) D : ℕ∞) := by
      have h2 : betaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M))
          (conjSubgroup M g) (conjSubgroup V g) ≤
          (E3.mQuot (conjSubgroup V g) (B ⊓ Subgroup.centralizer ({c} : Set G)) : ℕ∞) :=
        iInf₂_le _ hcal
      rw [betaN_conj (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V g] at h2
      exact h2.trans (by exact_mod_cast E3.mQuot_mono hD_CB)
    exact absurd hβ (not_lt.2 hle)
  · have hCB : Subgroup.centralizer ((commElt B c : Subgroup G) : Set G) ≤ conjSubgroup M g :=
      of_not_not hPB
    have hcommV : commElt B c ≤ V := by
      rw [commElt, Subgroup.closure_le]
      rintro x ⟨y, hy, rfl⟩
      have hyVg : y ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hy).1
      have hyM : y ∈ M := (Subgroup.mem_inf.1 hy).2
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
        rw [h.normalizer_eq]; exact hyM
      have hcN : c ∈ Subgroup.normalizer (V : Set G) := by
        rw [h.normalizer_eq]; exact h.le_M hcV
      have hycV : ⁅y, c⁆ ∈ V := by
        rw [commutatorElement_def]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 hyN c).1 hcV) (V.inv_mem hcV)
      have := commutatorElement_inv_inv_mem hyN hcN hycV
      simpa [commutatorElement_def] using this
    have hVcent : V ≤ Subgroup.centralizer ((commElt B c : Subgroup G) : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (B2F.isElemAbelian_comm h.isElemAbelian hv (hcommV hx)).symm
    exact hVg (hVcent.trans hCB)

theorem six_two_four {M V₀ V D : Subgroup G} (h : Hyp62 M V₀ V) {g : G}
    (hD : D ≤ conjSubgroup V g ⊓ M)
    (hr : ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) < rMV M V)
    (hCM : ∀ v ∈ V, v ≠ 1 → ¬ M ⊓ Subgroup.centralizer ({v} : Set G) ≤ conjSubgroup M g)
    (hδ : (E3.mQuot (conjSubgroup V g) D : ℕ∞) <
      deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V) :
    ⁅V ⊓ Subgroup.centralizer (D : Set G), conjSubgroup V g ⊓ M⁆ = ⊥ := by
  set B := conjSubgroup V g ⊓ M with hBdef
  set CV := V ⊓ Subgroup.centralizer (D : Set G) with hCVdef
  by_cases hVbot : V = ⊥
  · subst hVbot
    rw [hCVdef, bot_inf_eq, Subgroup.commutator_bot_left]
  · have hU_Mg : preCTilde V₀ V D h.isElemAbelian ≤ conjSubgroup M g := six_two_one h hD hr
    obtain ⟨⟨v0, hv0V⟩, hv0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVbot
    by_contra hne
    have hex : ∃ c ∈ CV, ∃ b ∈ B, ⁅c, b⁆ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hne
      refine le_bot_iff.1 ?_
      rw [Subgroup.commutator_le]
      intro c hc b hb
      rw [Subgroup.mem_bot]
      exact hcon c hc b hb
    obtain ⟨c, hc, b, hb, hcb⟩ := hex
    have hcV : c ∈ V := (Subgroup.mem_inf.1 hc).1
    have hcC : c ∈ Subgroup.centralizer (D : Set G) := (Subgroup.mem_inf.1 hc).2
    have hcU : c ∈ preCTilde V₀ V D h.isElemAbelian := by
      refine (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) hcV).2 fun d hd => ?_
      have h1 : ⁅c, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 hcC d hd).symm
      rw [h1]
      exact V₀.one_mem
    have hcMg : c ∈ conjSubgroup M g := hU_Mg hcU
    have hD_CB : D ≤ B ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine le_inf hD fun d hd => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hcC d hd
    have hcB2 : c ∈ conjSubgroup M g ⊓
        Subgroup.centralizer ((B ⊓ Subgroup.centralizer ({c} : Set G)) : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hcMg, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
    have h2elem : ∃ k, orderOf c = 2 ^ k := by
      have h2 : c ^ 2 = 1 := h.isElemAbelian.2 c hcV
      have hdvd : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h2
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
      · exact ⟨0, by simp [h1]⟩
      · exact ⟨1, by simp [h1]⟩
    have hBnotC : ¬ B ≤ Subgroup.centralizer ({c} : Set G) := by
      intro hBc
      exact hcb (commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_singleton_iff.1 (hBc hb)).symm)
    by_cases hPD : PropD (conjSubgroup M g) (commElt B c)
    · have hcal : B ⊓ Subgroup.centralizer ({c} : Set G) ∈
          calDn (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M))
            (conjSubgroup M g) (conjSubgroup V g) :=
        ⟨(inf_le_left.trans inf_le_left),
          c, hcB2, h2elem, B, inf_le_left, le_rfl, inf_le_left, hBnotC, hPD⟩
      have hle : deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V ≤
          (E3.mQuot (conjSubgroup V g) D : ℕ∞) := by
        have h2 : deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M))
            (conjSubgroup M g) (conjSubgroup V g) ≤
            (E3.mQuot (conjSubgroup V g) (B ⊓ Subgroup.centralizer ({c} : Set G)) : ℕ∞) :=
          iInf₂_le _ hcal
        rw [deltaN_conj (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V g] at h2
        exact h2.trans (by exact_mod_cast E3.mQuot_mono hD_CB)
      exact absurd hδ (not_lt.2 hle)
    · have hex2 : ∃ z ∈ commElt B c, Subgroup.centralizer ({z} : Set G) ≤ conjSubgroup M g := by
        by_contra hcon
        push Not at hcon
        exact hPD hcon
      obtain ⟨z, hz, hzC⟩ := hex2
      have hcommV : commElt B c ≤ V := by
        rw [commElt, Subgroup.closure_le]
        rintro x ⟨y, hy, rfl⟩
        have hyVg : y ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hy).1
        have hyM : y ∈ M := (Subgroup.mem_inf.1 hy).2
        have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
          rw [h.normalizer_eq]; exact hyM
        have hcN : c ∈ Subgroup.normalizer (V : Set G) := by
          rw [h.normalizer_eq]; exact h.le_M hcV
        have hycV : ⁅y, c⁆ ∈ V := by
          rw [commutatorElement_def]
          exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 hyN c).1 hcV) (V.inv_mem hcV)
        have := commutatorElement_inv_inv_mem hyN hcN hycV
        simpa [commutatorElement_def] using this
      have hzV : z ∈ V := hcommV hz
      have hz1 : z ≠ 1 := by
        intro hz1
        have htop : Subgroup.centralizer ({z} : Set G) = ⊤ := by
          rw [hz1]
          ext x
          simp [Subgroup.mem_centralizer_singleton_iff]
        have hMg_top : conjSubgroup M g = ⊤ := top_le_iff.1 (htop ▸ hzC)
        exact hCM v0 hv0V (fun h1 => hv0ne (Subtype.ext h1))
          (by rw [hMg_top]; exact le_top)
      exact hCM z hzV hz1 (inf_le_right.trans hzC)

theorem six_three {M V₀ V T : Subgroup G} (h : Hyp62 M V₀ V) {n : ℕ}
    (hT : T ≤ M)
    (hr : ((n + mSub V₀ : ℕ) : ℕ∞) < rMV M V)
    (hγ : ((n + mSub V₀ : ℕ) : ℕ∞) < gammaN n M V) :
    V₀ ≤ Subgroup.centralizer (wClos V n T : Set G) ∧
    (∀ v ∈ V, (∀ w ∈ wClos V n T, ⁅v, w⁆ ∈ V₀) →
      v ∈ Subgroup.centralizer (wClos V n T : Set G)) := by
  have hmain : ∀ v ∈ V, (∀ w ∈ wClos V n T, ⁅v, w⁆ ∈ V₀) →
      v ∈ Subgroup.centralizer (wClos V n T : Set G) := by
    intro v hv hv₀
    have hle : wClos V n T ≤ Subgroup.centralizer ({v} : Set G) := by
      refine wClos_le_of_forall fun A hA => ?_
      obtain ⟨g, hAg, hAm⟩ := hA.2
      have hAT : A ≤ T := hA.1
      have hD : A ≤ conjSubgroup V g ⊓ M := le_inf hAg (hAT.trans hT)
      have hcomm : ⁅preCTilde V₀ V A h.isElemAbelian, A⁆ = ⊥ :=
        six_two_two h hD (by rwa [hAm]) (Or.inr (by rwa [hAm]))
      have hvA : v ∈ preCTilde V₀ V A h.isElemAbelian := by
        refine (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) hv).2 fun a ha => ?_
        exact hv₀ a (le_wClos ⟨hAT, g, hAg, hAm⟩ ha)
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ⁅v, a⁆ = 1 := by
        have := Subgroup.commutator_le.1 hcomm.le v hvA a ha
        simpa using this
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
  refine ⟨?_, hmain⟩
  intro v hv
  apply hmain v (h.le hv)
  intro w hw
  have hwM : w ∈ M := hT ((wClos_le (V := V) n T) hw)
  have hwN : w ∈ Subgroup.normalizer (V₀ : Set G) := h.normal hwM
  have hconj : w * v * w⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hwN v).1 hv
  have heq : ⁅v, w⁆ = v * (w * v * w⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [heq]
  exact V₀.mul_mem hv (V₀.inv_mem hconj)

end CFSG.LocalAnalysis.WeakClosure81
