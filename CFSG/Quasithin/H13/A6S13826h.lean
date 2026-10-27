module

public import CFSG.Quasithin.H13.A6S13826g

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.H13.A6Coc
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

namespace SecHyp

variable {S} {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem relIndex_le_two_of_transv
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) {z : G}
    (hz : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 2 := by
  by_cases hFQ : F ≤ pCoreOf 2 H
  · rw [Subgroup.relIndex_eq_one.2 (le_inf le_rfl hFQ)]
    norm_num
  obtain ⟨f₀, hf₀, x₀, hx₀, hfx₀⟩ : ∃ f ∈ F, ∃ x ∈ X, f * x * f⁻¹ * x⁻¹ ∉ W := by
    by_contra hall
    push Not at hall
    exact hFQ fun f hf => S.le_pCoreOf_of_triv hs.hS hs.hH hs.hKH hs.hKn hs.hHK hs.hsimp
      hs.hXH hs.hHX hs.hHW hs.hQ hs.hKnt (hFH hf) (hall f hf)
  have hf₀Q : f₀ ∉ pCoreOf 2 H := fun h => hfx₀ (hs.hQ f₀ h x₀ hx₀)
  have h16 := hs.natural_of_transv hirr hαs hαk (hFH hf₀) hf₀Q (hFs f₀ hf₀) (hz f₀ hf₀)
  have hzX : z ∈ X := by
    have hc : f₀ * x₀ * f₀⁻¹ * x₀⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hs.hHX (hFH hf₀)) x₀).mp hx₀) (X.inv_mem hx₀)
    have h := (hz f₀ hf₀ x₀ hx₀).resolve_left hfx₀
    have e : z = (f₀ * x₀ * f₀⁻¹ * x₀⁻¹ * z⁻¹)⁻¹ * (f₀ * x₀ * f₀⁻¹ * x₀⁻¹) := by group
    rw [e]
    exact X.mul_mem (X.inv_mem (hs.hWX h)) hc
  exact hs.card_le_two hirr hαs hαk h16 hFH hzX hz

theorem le_sup_of_relIndex_le {F₁ F₂ : Subgroup G} (h12 : F₁ ≤ F₂) (hF₂ : F₂ ≤ H)
    (hle : (F₂ ⊓ pCoreOf 2 H).relIndex F₂ ≤ (F₁ ⊓ pCoreOf 2 H).relIndex F₁) :
    F₂ ≤ F₁ ⊔ pCoreOf 2 H := by
  have hsub := hs.autSec_le h12 hF₂
  have heq : autSec (autOn F₁ X) ⊤ (W.subgroupOf X) = autSec (autOn F₂ X) ⊤ (W.subgroupOf X) :=
    Subgroup.eq_of_le_of_card_ge hsub (by
      rw [hs.card_autSec hF₂, hs.card_autSec (h12.trans hF₂)]
      exact hle)
  intro f hf
  have hmem : hs.act ⟨f, hF₂ hf⟩ ∈ autSec (autOn F₂ X) ⊤ (W.subgroupOf X) :=
    (hs.mem_autSec_iff hF₂).2 ⟨_, hf, rfl⟩
  rw [← heq] at hmem
  obtain ⟨f₁, hf₁, he⟩ := (hs.mem_autSec_iff (h12.trans hF₂)).1 hmem
  have hq : ((f₁⁻¹ * ⟨f, hF₂ hf⟩ : ↥H) : G) ∈ pCoreOf 2 H := by
    rw [← hs.act_eq_one_iff, map_mul, map_inv, he, inv_mul_cancel]
  have e : f = (f₁ : G) * ((f₁⁻¹ * ⟨f, hF₂ hf⟩ : ↥H) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf₁) (Subgroup.mem_sup_right hq)

end SecHyp

structure D826 (H K : Subgroup G) : Prop where
  hS : S.Hyp138
  hH : H ∈ S.Hz
  hK : K ∈ cComp H
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hHK : H = K ⊔ T
  hL1K : S.L1 ≤ K
  hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H
  h6 : IsAlt 6 ↥(S.KSt H K)

namespace D826

variable {S} {H K : Subgroup G} (hd : S.D826 H K)
include hd

theorem hKH : K ≤ H := le_of_mem_cComp hd.hK

theorem hF : HypF98 T V L (fsuV1 T V) S.V3 H := hd.hS.hF H hd.hH

theorem hTH : T ≤ H := hd.hHK ▸ le_sup_right

theorem hsimp : IsSimpleGroup ↥(S.KSt H K) := by
  obtain ⟨e⟩ := hd.h6
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact e.isSimpleGroup

omit [Finite G] hd in
theorem hnab {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H := by
  obtain ⟨a, ha⟩ := hαs aL
  obtain ⟨b, hb⟩ := hαs bL
  refine ⟨a, a.2, b, b.2, fun h => ?_⟩
  have h1 : α (a * b * a⁻¹ * b⁻¹) = 1 := (hαk _).2 (by simpa using h)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb] at h1
  exact absurd (congrArg Subtype.val h1) (by decide)

theorem UH_le_H : conjClosure S.V3 H ≤ H :=
  hd.hF.toHypF91.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)

theorem VH_le_H : conjClosure V H ≤ H :=
  conjClosure_le fun _h hh _v hv => H.mul_mem (H.mul_mem hh (hd.hTH (hd.hF.toHypF91.V_le_T hv)))
    (H.inv_mem hh)

theorem secU {X W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWX : W ≤ X)
    (hXU : X ≤ conjClosure S.V3 H) (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ W) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    S.SecHyp H K X W := by
  have hF1 := hd.hF.toHypF91
  refine ⟨hd.hS, hd.hH, hd.hKH, hd.hKn, hd.hHK, hd.hsimp, hnab hαs hαk, hWX,
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
    (hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ W) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    S.SecHyp H K X W := by
  have hc := S.comm_VH_QH_eq hd.hS.hNS h13315 h1356two hd.hH h13314
  refine ⟨hd.hS, hd.hH, hd.hKH, hd.hKn, hd.hHK, hd.hsimp, hnab hαs hαk, hWX,
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

theorem relIndex_le_two_of_chief {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W₀ X₀ : Subgroup G} (hW₀X₀ : W₀ ≤ X₀) (hX₀c : ∀ a ∈ X₀, ∀ b ∈ X₀, a * b = b * a)
    (hHX₀ : H ≤ Subgroup.normalizer (X₀ : Set G)) (hHW₀ : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X₀, k * x * k⁻¹ * x⁻¹ ∉ W₀)
    (hsec : ∀ W₁ W₂ : Subgroup G, W₀ ≤ W₁ → W₁ ≤ W₂ → W₂ ≤ X₀ →
      H ≤ Subgroup.normalizer (W₂ : Set G) → H ≤ Subgroup.normalizer (W₁ : Set G) →
      (∃ k ∈ K, ∃ x ∈ W₂, k * x * k⁻¹ * x⁻¹ ∉ W₁) → S.SecHyp H K W₂ W₁)
    {F : Subgroup G} (hFH : F ≤ H) (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) {z : G}
    (hz : ∀ f ∈ F, ∀ x ∈ X₀, f * x * f⁻¹ * x⁻¹ ∈ W₀ ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W₀) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 2 := by
  obtain ⟨W₁, W₂, hW₀W₁, hW₁W₂, hW₂X₀, hHW₁, hHW₂, hirr, hKnt'⟩ :=
    exists_chief_sec hd.hKH (perfect_of_mem_cComp hd.hK) hW₀X₀ hX₀c hHX₀ hHW₀ hKnt
  have hs := hsec W₁ W₂ hW₀W₁ hW₁W₂.le hW₂X₀ hHW₂ hHW₁ hKnt'
  have : IsMulCommutative ↥W₂ := ⟨⟨fun a b => Subtype.ext (hX₀c a (hW₂X₀ a.2) b (hW₂X₀ b.2))⟩⟩
  exact hs.relIndex_le_two_of_transv hirr hαs hαk hFH hFs fun f hf x hx =>
    (hz f hf x (hW₂X₀ hx)).imp (fun h => hW₀W₁ h) (fun h => hW₀W₁ h)

theorem relIndex_le_two_of_VH
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13314 : Stmt13_3_14)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) {z : G}
    (hz : ∀ f ∈ F, ∀ y ∈ conjClosure V H, f * y * f⁻¹ * y⁻¹ ∈ conjClosure S.V3 H ∨
      f * y * f⁻¹ * y⁻¹ * z⁻¹ ∈ conjClosure S.V3 H) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 2 := by
  have hVab := hd.hF.F911_2
  refine hd.relIndex_le_two_of_chief hαs hαk (UH_le_VH (S := S) (H := H))
    (fun a ha b hb => congrArg (Subtype.val : ↥(conjClosure V H) → G)
      (hVab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (le_normalizer_conjClosure V H) (le_normalizer_conjClosure S.V3 H)
    (hd.knt_VH h13315 h1356two h13314) (fun W₁ W₂ hUW₁ hW₁W₂ hW₂V hHW₂ hHW₁ hKnt =>
      hd.secV h13315 h1356two h13314 hUW₁ hW₁W₂ hW₂V hHW₂ hHW₁ hKnt hαs hαk) hFH hFs hz

theorem relIndex_le_two_of_U {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {W₀ X₀ : Subgroup G}
    (hV1W₀ : fsuV1 T V ≤ W₀) (hW₀X₀ : W₀ ≤ X₀) (hX₀U : X₀ ≤ conjClosure S.V3 H)
    (hHX₀ : H ≤ Subgroup.normalizer (X₀ : Set G)) (hHW₀ : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X₀, k * x * k⁻¹ * x⁻¹ ∉ W₀) {F : Subgroup G} (hFH : F ≤ H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) {z : G}
    (hz : ∀ f ∈ F, ∀ x ∈ X₀, f * x * f⁻¹ * x⁻¹ ∈ W₀ ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W₀) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 2 := by
  have hUab := hd.hF.F911_3
  refine hd.relIndex_le_two_of_chief hαs hαk hW₀X₀
    (fun a ha b hb => congrArg (Subtype.val : ↥(conjClosure S.V3 H) → G)
      (hUab.1.is_comm.comm ⟨a, hX₀U ha⟩ ⟨b, hX₀U hb⟩)) hHX₀ hHW₀ hKnt
    (fun W₁ W₂ hW₀W₁ hW₁W₂ hW₂X₀ hHW₂ hHW₁ hKnt' =>
      hd.secU (hV1W₀.trans hW₀W₁) hW₁W₂ (hW₂X₀.trans hX₀U) hHW₂ hHW₁ hKnt' hαs hαk) hFH hFs hz

end D826

end Setting4

end CFSG.Quasithin.H13.A6
