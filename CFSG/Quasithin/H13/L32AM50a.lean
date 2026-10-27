module

public import CFSG.Quasithin.H13.A6S1372Mod
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

structure TopW (T L V H W : Subgroup G) : Prop where
  S : Setting147 G T L V H
  hF : HypF98 T V L (fsuV1 T V) V H
  hV₁W : fsuV1 T V ≤ W
  hWU : W < conjClosure V H
  hHW : H ≤ Subgroup.normalizer (W : Set G)
  hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure V H →
    H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure V H

theorem exists_topW (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H) :
    ∃ W : Subgroup G, TopW T L V H W := by
  classical
  set 𝒮 : Set (Subgroup G) := {W | fsuV1 T V ≤ W ∧ W < conjClosure V H ∧
    H ≤ Subgroup.normalizer (W : Set G)} with h𝒮
  have hV₁ : fsuV1 T V ∈ 𝒮 :=
    ⟨le_rfl, lt_of_lt_of_le hF.toHypF91.V₁_lt_Vp (le_conjClosure V H),
      hF.toHypF91.H_normalizes_V₁⟩
  obtain ⟨W, hW⟩ := 𝒮.toFinite.exists_maximal ⟨_, hV₁⟩
  refine ⟨W, S, hF, hW.1.1, hW.1.2.1, hW.1.2.2, fun W' hWW' hW'U hHW' => ?_⟩
  by_cases h : W' = conjClosure V H
  · exact Or.inr h
  · left
    exact (hW.2 ⟨hW.1.1.trans hWW', lt_of_le_of_ne hW'U h, hHW'⟩ hWW').antisymm hWW'

namespace TopW

variable {W : Subgroup G} (C : TopW T L V H W)
include C

theorem isElemAbelian_U : IsElemAbelian 2 (conjClosure V H) := C.hF.F911_3

theorem comm : IsMulCommutative ↥(conjClosure V H) := C.isElemAbelian_U.1

omit [Finite G] C in
theorem hHU : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H

theorem hHUW : H ≤ Subgroup.normalizer ((conjClosure V H ⊓ W : Subgroup G) : Set G) := by
  rw [inf_eq_right.2 C.hWU.le]
  exact C.hHW

theorem hWU' : W ≤ conjClosure V H := C.hWU.le

variable [IsMulCommutative ↥(conjClosure V H)]

@[expose] noncomputable def act : ↥H →* MulAut (Sec (⊤ : Subgroup ↥(conjClosure V H))
    (W.subgroupOf (conjClosure V H))) :=
  A6.A6Mod.secAct (hHU (H := H) (V := V)) C.hHUW

theorem act_secMk (h : ↥H) (u : ↥(conjClosure V H)) :
    C.act h (InternalSec.secMk (W.subgroupOf (conjClosure V H)) u) =
      InternalSec.secMk (W.subgroupOf (conjClosure V H))
        (Setup.rho (conjClosure V H) H (hHU (H := H) (V := V)) h u) := rfl

theorem act_eq_one_iff_comm (h : ↥H) :
    C.act h = 1 ↔ ∀ u ∈ conjClosure V H, (h : G) * u * (h : G)⁻¹ * u⁻¹ ∈ W := by
  unfold act
  exact A6.A6Mod.secAct_eq_one_iff _ _ h

theorem act_eq_one_of_mem {h : ↥H} (hh : (h : G) ∈ pCoreOf 2 H) : C.act h = 1 := by
  rw [C.act_eq_one_iff_comm]
  intro u hu
  rw [C.hF.toHypF91.pCoreOf_eq_centralizerMod] at hh
  exact C.hV₁W ((mem_centralizerMod.mp hh).2.2 u hu)

theorem sec_sq (y : Sec (⊤ : Subgroup ↥(conjClosure V H)) (W.subgroupOf (conjClosure V H))) :
    y * y = 1 := by
  obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf (conjClosure V H)) y
  rw [← map_mul, A6.A6Mod.secMk_eq_one_iff]
  have h1 : (x : G) * x = 1 := by
    have := C.isElemAbelian_U.2 x x.2
    rwa [pow_two] at this
  rw [Subgroup.coe_mul, h1]
  exact W.one_mem

theorem irr (J : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure V H))
      (W.subgroupOf (conjClosure V H))))
    (hJ : ∀ h : ↥H, ∀ y ∈ J, C.act h y ∈ J) : J = ⊥ ∨ J = ⊤ := by
  set X := conjClosure V H with hX
  set P : Subgroup G := (J.comap (InternalSec.secMk (W.subgroupOf X))).map X.subtype with hP
  have hmemP : ∀ x : ↥X, (x : G) ∈ P ↔ InternalSec.secMk (W.subgroupOf X) x ∈ J := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx⟩
      rw [Subtype.ext hxx] at hx'
      exact hx'
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hWP : W ≤ P := by
    intro w hw
    have hwX : w ∈ X := C.hWU' hw
    rw [show w = ((⟨w, hwX⟩ : ↥X) : G) from rfl, hmemP]
    have : InternalSec.secMk (W.subgroupOf X) ⟨w, hwX⟩ = 1 := (A6.A6Mod.secMk_eq_one_iff _).2 hw
    rw [this]
    exact J.one_mem
  have hPX : P ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P := by
      rintro h hh _ ⟨x, hx, rfl⟩
      have hhx : h * x * h⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hHU hh) x).mp x.2
      show h * (x : G) * h⁻¹ ∈ P
      rw [show h * (x : G) * h⁻¹ = ((⟨h * x * h⁻¹, hhx⟩ : ↥X) : G) from rfl, hmemP]
      have := hJ ⟨h, hh⟩ _ hx
      rw [C.act_secMk] at this
      exact this
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨key h hh p, fun hp => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hp
    simpa [mul_assoc] using this
  rcases C.hmax P hWP hPX hHP with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) y
    have hxP : (x : G) ∈ P := (hmemP x).2 hy
    rw [h] at hxP
    rw [Subgroup.mem_bot, A6.A6Mod.secMk_eq_one_iff]
    exact hxP
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) y
    have hxP : (x : G) ∈ P := by rw [h]; exact x.2
    exact (hmemP x).1 hxP

theorem top_ne_bot : (⊤ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure V H))
    (W.subgroupOf (conjClosure V H)))) ≠ ⊥ := by
  intro h
  obtain ⟨u, hu, huW⟩ := Set.exists_of_ssubset C.hWU
  have h1 : InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨u, hu⟩ ∈
      (⊤ : Subgroup (Sec _ _)) := trivial
  rw [h, Subgroup.mem_bot, A6.A6Mod.secMk_eq_one_iff] at h1
  exact huW h1

end TopW

end CFSG.Quasithin.H13.L32A.C
