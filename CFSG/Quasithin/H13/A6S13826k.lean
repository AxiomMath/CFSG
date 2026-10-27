module

public import CFSG.Quasithin.H13.A6S13826j
public import CFSG.Quasithin.H13.A6S13825o
public import CFSG.Quasithin.H13.A6S13826f

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem nonempty_n6Model
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (h16 : W.relIndex X = 16) :
    Nonempty (B42Alt6.N6Model (autSec (autOn K X) ⊤ (W.subgroupOf X))) := by
  have C := hs.ctx hαs hαk
  obtain ⟨ι⟩ := C.iso
  have hcard : Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) = 16 := by
    rw [(card_sec (X := X) (W := W)), h16]
  obtain ⟨-, hirrL⟩ := A6Md.natural_of_card_le hs.sec_sq C (hs.fixV_eq_bot hirr)
    (hs.irr_autSec hirr) hs.top_ne_bot (by rw [hcard]; norm_num)
  exact A6Md.exists_n6Model hs.sec_sq ι hirrL.2 (by rw [hcard]; norm_num)

end SecHyp

namespace D826

variable {H K : Subgroup G} (hd : S.D826 H K)
include hd

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

theorem mem_max_iff (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    {u : G} (hu : u ∈ conjClosure S.V3 H) :
    u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have htriv := hd.triv_of_max h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two hαs hαk hV1W
    hWU hHW hmax
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
  ·
    exfalso
    apply hd.V1_lt_UH.not_ge
    rw [← hd.hUK, Subgroup.commutator_le]
    intro x hx k hk
    have hxC : x ∈ C := h ▸ hx
    rw [commutatorElement_def]
    exact hxC.2.2 k hk

theorem relIndex_max
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) :
    W.relIndex (conjClosure S.V3 H) = 16 := by
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    hαs hαk
  by_cases htr : ∃ h ∈ H, InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)
  ·
    obtain ⟨h, hh, ht⟩ := htr
    have hhQ : h ∉ pCoreOf 2 H := fun hq => ht.1 fun x hx => by
      rw [hF1.pCoreOf_eq_centralizerMod] at hq
      exact hq.2.2 x hx
    have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
      hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH) hαs hαk
    obtain ⟨hne, w, hw⟩ := L13825.exists_transvectionWith_sigmaH hd.hH hh ht
    have hsq := B1.tv_sq (fun v => by rw [pow_two]; exact hsV.sec_sq v) hw hne
    have hh2 : h * h ∈ pCoreOf 2 H := by
      have h1 := (L13825.sigmaH_eq_one_iff hd.hH hF1 (⟨h, hh⟩ * ⟨h, hh⟩)).1
        (by rw [map_mul]; exact hsq)
      simpa using h1
    obtain ⟨c, hc⟩ := ht.2
    exact hsU.natural_of_transv hmax hαs hαk hh hhQ hh2 (z := c) fun x hx =>
      (hc x hx).imp (fun h => hV1W h) (fun h => hV1W h)
  ·
    push Not at htr
    obtain ⟨γ, γ', g, s, hDγ, -, hpos, hle, -⟩ := S.case2_of_no_transv hF htr
    obtain ⟨hq, -⟩ := hF.F916_2_aux s hpos hle
    obtain ⟨c, -, hcK, hc3, hc1, hcc⟩ :=
      S.exists_c_class hd.hS hd.hH hd.hKH hd.hKn hd.hHK hd.hL1K hd.h6 hαs hαk
    have hUγel := hF.isElemAbelian_Uγ (g := g)
    refine hsU.natural_of_le_sq hmax hαs hαk hcK hc3 hc1 hcc (hF.Uγ_le_H s)
      (hd.not_Uγ_le s hDγ) (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _) ?_
    refine (Subgroup.relIndex_le_of_le_left ?_ (relIndex_ne_zero' _ _)).trans hq.2.2.2.2
    intro x hx
    exact ⟨hx.1, hHW (hd.UH_le_H hx.1), fun u hu => hV1W (hx.2.2 u hu)⟩

end D826

end Setting4

end CFSG.Quasithin.H13.A6
