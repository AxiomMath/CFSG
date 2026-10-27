module

public import CFSG.Quasithin.H13.A6S13826e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

structure DK (H K : Subgroup G) : Prop where
  hS : S.Hyp138
  hH : H ∈ S.Hz
  hK : K ∈ cComp H
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hHK : H = K ⊔ T
  hL1K : S.L1 ≤ K
  hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H
  hsimp : IsSimpleGroup ↥(S.KSt H K)
  hnab : ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H

namespace DK

variable {S} {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem hKH : K ≤ H := le_of_mem_cComp hd.hK

theorem hF : HypF98 T V L (fsuV1 T V) S.V3 H := hd.hS.hF H hd.hH

theorem hTH : T ≤ H := hd.hHK ▸ le_sup_right

theorem UH_le_H : conjClosure S.V3 H ≤ H :=
  hd.hF.toHypF91.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)

theorem VH_le_H : conjClosure V H ≤ H :=
  conjClosure_le fun _h hh _v hv => H.mul_mem (H.mul_mem hh (hd.hTH (hd.hF.toHypF91.V_le_T hv)))
    (H.inv_mem hh)

theorem secU {X W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWX : W ≤ X)
    (hXU : X ≤ conjClosure S.V3 H) (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ W) : S.SecHyp H K X W := by
  have hF1 := hd.hF.toHypF91
  refine ⟨hd.hS, hd.hH, hd.hKH, hd.hKn, hd.hHK, hd.hsimp, hd.hnab, hWX,
    hXU.trans hd.UH_le_H, hHX, hHW, fun q hq x hx => ?_, hKnt, fun x hx => ?_⟩
  · rw [hF1.pCoreOf_eq_centralizerMod] at hq
    exact hV1W (hq.2.2 x (hXU hx))
  · have h2 := hd.hF.F911_3.2 x (hXU hx)
    rw [pow_two] at h2
    rw [h2]
    exact W.one_mem

theorem secV (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h13314 : Stmt13_3_14) {X W : Subgroup G} (hUW : conjClosure S.V3 H ≤ W) (hWX : W ≤ X)
    (hXV : X ≤ conjClosure V H) (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ W) : S.SecHyp H K X W := by
  have hc := S.comm_VH_QH_eq hd.hS.hNS h13315 h1356two hd.hH h13314
  refine ⟨hd.hS, hd.hH, hd.hKH, hd.hKn, hd.hHK, hd.hsimp, hd.hnab, hWX,
    hXV.trans hd.VH_le_H, hHX, hHW, fun q hq x hx => ?_, hKnt, fun x hx => ?_⟩
  · have h1 : ⁅x, q⁆ ∈ ⁅conjClosure V H, pCoreOf 2 H⁆ :=
      Subgroup.commutator_mem_commutator (hXV hx) hq
    rw [hc] at h1
    have h2 := (conjClosure S.V3 H).inv_mem h1
    have e : (⁅x, q⁆)⁻¹ = q * x * q⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
    rw [e] at h2
    exact hUW h2
  · have h2 := hd.hF.F911_2.2 x (hXV hx)
    rw [pow_two] at h2
    rw [h2]
    exact W.one_mem

theorem knt_top {W : Subgroup G} (hWU : W < conjClosure S.V3 H) :
    ∃ k ∈ K, ∃ x ∈ conjClosure S.V3 H, k * x * k⁻¹ * x⁻¹ ∉ W := by
  by_contra h
  push Not at h
  apply hWU.not_ge
  rw [← hd.hUK, Subgroup.commutator_le]
  intro u hu k hk
  have h1 := W.inv_mem (h k hk u hu)
  have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ := by rw [commutatorElement_def]; group
  rw [e] at h1
  exact h1

theorem knt_VH (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h13314 : Stmt13_3_14) :
    ∃ k ∈ K, ∃ x ∈ conjClosure V H, k * x * k⁻¹ * x⁻¹ ∉ conjClosure S.V3 H := by
  by_contra hcon
  push Not at hcon
  apply S.VH_not_le_V_sup_UH hd.hS.hNS h13315 h1356two hd.hH h13314
  have hF1 := hd.hF.toHypF91
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hF1.T_normalizes_V
  have hTU : T ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    hd.hTH.trans (le_normalizer_conjClosure S.V3 H)
  refine conjClosure_le fun h hh v hv => ?_
  have hh' : h ∈ ((T ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm, ← hd.hHK]
    exact hh
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T K (hd.hTH.trans hd.hKn)] at hh'
  obtain ⟨t, ht, k, hk, rfl⟩ := hh'
  have hkv : k * v * k⁻¹ ∈ V ⊔ conjClosure S.V3 H := by
    have h1 := hcon k hk v (le_conjClosure V H hv)
    have e : k * v * k⁻¹ = (k * v * k⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hv)
  have hc : conjSub t (V ⊔ conjClosure S.V3 H) = V ⊔ conjClosure S.V3 H := by
    rw [conjSub_sup, A6P.conjSub_eq_of_mem_normalizer (hTV ht),
      A6P.conjSub_eq_of_mem_normalizer (hTU ht)]
  have hkv' := mul_mem_conjSub (g := t) hkv
  rw [hc] at hkv'
  have e : t * k * v * (t * k)⁻¹ = t * (k * v * k⁻¹) * t⁻¹ := by group
  rw [e]
  exact hkv'

theorem V1_lt_UH : fsuV1 T V < conjClosure S.V3 H := by
  refine lt_of_le_of_ne (hd.hF.toHypF91.V₁_le_Vp.trans (le_conjClosure _ _)) fun h => ?_
  have h8 := Subgroup.card_le_of_le (le_conjClosure S.V3 H)
  rw [← h, S.card_V3, S.card_V1] at h8
  exact absurd h8 (by norm_num)

theorem exists_max : ∃ W : Subgroup G, fsuV1 T V ≤ W ∧ W < conjClosure S.V3 H ∧
    H ≤ Subgroup.normalizer (W : Set G) ∧
    ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H := by
  classical
  obtain ⟨W, ⟨hV1W, hWU, hHW⟩, hmax⟩ := WellFounded.has_min (wellFounded_gt (α := Subgroup G))
    {Y : Subgroup G | fsuV1 T V ≤ Y ∧ Y < conjClosure S.V3 H ∧
      H ≤ Subgroup.normalizer (Y : Set G)}
    ⟨fsuV1 T V, le_rfl, hd.V1_lt_UH, hd.hF.toHypF91.H_normalizes_V₁⟩
  refine ⟨W, hV1W, hWU, hHW, fun W' hWW' hW'U hHW' => ?_⟩
  by_cases h : W' = conjClosure S.V3 H
  · exact Or.inr h
  · left
    by_contra hne
    exact hmax W' ⟨hV1W.trans hWW', lt_of_le_of_ne hW'U h, hHW'⟩
      (lt_of_le_of_ne hWW' (Ne.symm hne))

theorem le_normalizer_fixK :
    H ≤ Subgroup.normalizer (centralizerMod (fsuV1 T V) (conjClosure S.V3 H) K : Set G) := by
  have hF1 := hd.hF.toHypF91
  have key : ∀ h ∈ H, ∀ x ∈ centralizerMod (fsuV1 T V) (conjClosure S.V3 H) K,
      h * x * h⁻¹ ∈ centralizerMod (fsuV1 T V) (conjClosure S.V3 H) K := by
    rintro h hh x ⟨hxU, -, hxK⟩
    have hhxU : h * x * h⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hh) x).mp hxU
    refine ⟨hhxU, hF1.H_normalizes_V₁ (hd.UH_le_H hhxU), fun k hk => ?_⟩
    have hk' : h⁻¹ * k * h ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hd.hKn (H.inv_mem hh)) k).mp hk
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hF1.H_normalizes_V₁ hh) _).mp (hxK _ hk')
    have e : h * (x * (h⁻¹ * k * h) * x⁻¹ * (h⁻¹ * k * h)⁻¹) * h⁻¹ =
        h * x * h⁻¹ * k * (h * x * h⁻¹)⁻¹ * k⁻¹ := by group
    rwa [e] at h1
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem mem_max_iff_of_triv {W : Subgroup G} (hWU : W < conjClosure S.V3 H)
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (htriv : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V)
    {u : G} (hu : u ∈ conjClosure S.V3 H) :
    u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  refine ⟨fun huW k hk => htriv k hk u huW, fun hK => ?_⟩
  have hF1 := hd.hF.toHypF91
  set C := centralizerMod (fsuV1 T V) (conjClosure S.V3 H) K with hC
  have hmemC : ∀ x ∈ conjClosure S.V3 H, (∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ fsuV1 T V) → x ∈ C :=
    fun x hx hxK => ⟨hx, hF1.H_normalizes_V₁ (hd.UH_le_H hx), fun k hk => by
      have h1 := (fsuV1 T V).inv_mem (hxK k hk)
      have e : (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
      rwa [e] at h1⟩
  have hWC : W ≤ C := fun w hw => hmemC w (hWU.le hw) fun k hk => htriv k hk w hw
  rcases hmax C hWC (centralizerMod_le_left _ _ _) hd.le_normalizer_fixK with h | h
  · rw [← h]
    exact hmemC u hu hK
  · exfalso
    apply hd.V1_lt_UH.not_ge
    rw [← hd.hUK, Subgroup.commutator_le]
    intro x hx k hk
    have hxC : x ∈ C := h ▸ hx
    rw [commutatorElement_def]
    exact hxC.2.2 k hk

end DK

end Setting4

end CFSG.Quasithin.H13.A6
