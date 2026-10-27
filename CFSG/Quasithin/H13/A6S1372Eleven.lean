module

public import CFSG.Quasithin.H13.A6S13710c
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace A6Eleven

section Abstract

variable {Y : Type*} [Group Y]

theorem eq_of_le_of_index_two {E W : Subgroup Y} (hE : E.index = 2) (hW : W.index = 2)
    (hle : E ≤ W) : E = W := by
  have h := Subgroup.relIndex_mul_index hle
  rw [hE, hW] at h
  have h1 : E.relIndex W = 1 := by omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)

theorem mul_inv_mem_of_index_two {E : Subgroup Y} (hE : E.index = 2) {a u : Y} (ha : a ∉ E)
    (hu : u ∉ E) : a * u⁻¹ ∈ E := by
  rw [Subgroup.mul_mem_iff_of_index_two hE]
  exact ⟨fun h => absurd h ha, fun h => absurd (E.inv_mem_iff.mp h) hu⟩

theorem comm_of_index_two {E : Subgroup Y} (hE : E.index = 2)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {c : Y} (hc : c ∉ E)
    (hcE : ∀ e ∈ E, c * e = e * c) (a b : Y) : a * b = b * a := by
  have hsplit : ∀ x : Y, x ∈ E ∨ x * c⁻¹ ∈ E := fun x => by
    by_cases hx : x ∈ E
    · exact Or.inl hx
    · exact Or.inr (mul_inv_mem_of_index_two hE hx hc)
  have key : ∀ x : Y, ∃ e ∈ E, x = e ∨ x = e * c := fun x => by
    rcases hsplit x with h | h
    · exact ⟨x, h, Or.inl rfl⟩
    · exact ⟨x * c⁻¹, h, Or.inr (by group)⟩
  obtain ⟨e₁, he₁, h₁⟩ := key a
  obtain ⟨e₂, he₂, h₂⟩ := key b
  have hc1 := hcE e₁ he₁
  have hc2 := hcE e₂ he₂
  have h12 := hEab e₁ he₁ e₂ he₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
  · exact h12
  · calc e₁ * (e₂ * c) = e₁ * e₂ * c := by group
      _ = e₂ * e₁ * c := by rw [h12]
      _ = e₂ * (c * e₁) := by rw [mul_assoc, ← hc1]
      _ = e₂ * c * e₁ := by group
  · calc e₁ * c * e₂ = e₁ * (c * e₂) := by group
      _ = e₁ * (e₂ * c) := by rw [hc2]
      _ = e₂ * e₁ * c := by rw [← mul_assoc, h12]
      _ = e₂ * (e₁ * c) := by group
  · calc e₁ * c * (e₂ * c) = e₁ * (c * e₂) * c := by group
      _ = e₁ * (e₂ * c) * c := by rw [hc2]
      _ = e₂ * e₁ * c * c := by rw [← mul_assoc, h12]
      _ = e₂ * (c * e₁) * c := by rw [mul_assoc e₂ e₁, ← hc1]
      _ = e₂ * c * (e₁ * c) := by group

theorem eq_of_index_two {W E₁ E₂ : Subgroup Y} (hW2 : W.index = 2) (h12 : E₁.index = 2)
    (h22 : E₂.index = 2) (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWsq : ∀ a ∈ W, a * a = 1)
    (hE1 : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) (hE1sq : ∀ a ∈ E₁, a * a = 1)
    (hE2 : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a) (hE2sq : ∀ a ∈ E₂, a * a = 1)
    (hY : ∃ a b : Y, a * b ≠ b * a) (hne1 : E₁ ≠ W) (hne2 : E₂ ≠ W) : E₁ = E₂ := by
  obtain ⟨a₀, b₀, hab⟩ := hY
  have hex : ∀ E : Subgroup Y, E.index = 2 → E ≠ W → ∃ u ∈ E, u ∉ W := by
    intro E hE hne
    by_contra h
    push Not at h
    exact hne (eq_of_le_of_index_two hE hW2 h)
  obtain ⟨u₁, hu₁, hu₁W⟩ := hex E₁ h12 hne1
  obtain ⟨u₂, hu₂, hu₂W⟩ := hex E₂ h22 hne2
  have hinv : ∀ {E : Subgroup Y}, (∀ a ∈ E, a * a = 1) → ∀ a ∈ E, a⁻¹ = a := fun hsq a ha =>
    inv_eq_of_mul_eq_one_right (hsq a ha)
  have hcen : ∀ {E : Subgroup Y} {u : Y}, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → u ∈ E →
      u ∉ W → ∀ c ∈ E, c ∈ W → ∀ y : Y, c * y = y * c := by
    intro E u hEab hu huW c hcE hcW y
    by_cases hy : y ∈ W
    · exact hW c hcW y hy
    · have h1 := mul_inv_mem_of_index_two hW2 hy huW
      have e : y = (y * u⁻¹) * u := by group
      rw [e]
      calc c * (y * u⁻¹ * u) = (c * (y * u⁻¹)) * u := by group
        _ = (y * u⁻¹ * c) * u := by rw [hW c hcW _ h1]
        _ = y * u⁻¹ * (c * u) := by group
        _ = y * u⁻¹ * (u * c) := by rw [hEab c hcE u hu]
        _ = y * u⁻¹ * u * c := by group
  have hZ : ∀ c : Y, (∀ y : Y, c * y = y * c) → c ∈ E₁ := by
    intro c hc
    by_contra hcE
    exact hab (comm_of_index_two h12 hE1 hcE (fun e _ => hc e) a₀ b₀)
  have hu12 : u₁ * u₂ ∈ W := by
    rw [Subgroup.mul_mem_iff_of_index_two hW2]
    exact ⟨fun h => absurd h hu₁W, fun h => absurd h hu₂W⟩
  have hcomm12 : u₁ * u₂ = u₂ * u₁ := by
    have h1 := hWsq _ hu12
    calc u₁ * u₂ = (u₁ * u₂)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = u₂⁻¹ * u₁⁻¹ := mul_inv_rev _ _
      _ = u₂ * u₁ := by rw [hinv hE2sq u₂ hu₂, hinv hE1sq u₁ hu₁]
  have hu₂E : ∀ e ∈ E₁, u₂ * e = e * u₂ := by
    intro e he
    by_cases heW : e ∈ W
    · exact (hcen hE1 hu₁ hu₁W e he heW u₂).symm
    · have h1 : e * u₁⁻¹ ∈ W := mul_inv_mem_of_index_two hW2 heW hu₁W
      have h1E : e * u₁⁻¹ ∈ E₁ := E₁.mul_mem he (E₁.inv_mem hu₁)
      have hc := hcen hE1 hu₁ hu₁W _ h1E h1 u₂
      have e' : e = (e * u₁⁻¹) * u₁ := by group
      rw [e']
      calc u₂ * (e * u₁⁻¹ * u₁) = (u₂ * (e * u₁⁻¹)) * u₁ := by group
        _ = (e * u₁⁻¹ * u₂) * u₁ := by rw [← hc]
        _ = e * u₁⁻¹ * (u₂ * u₁) := by group
        _ = e * u₁⁻¹ * (u₁ * u₂) := by rw [hcomm12]
        _ = e * u₁⁻¹ * u₁ * u₂ := by group
  have hu₂E₁ : u₂ ∈ E₁ := by
    by_contra h
    exact hab (comm_of_index_two h12 hE1 h hu₂E a₀ b₀)
  have hle : E₂ ≤ E₁ := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact hZ x (hcen hE2 hu₂ hu₂W x hx hxW)
    · have h1 : x * u₂⁻¹ ∈ W := mul_inv_mem_of_index_two hW2 hxW hu₂W
      have h1E : x * u₂⁻¹ ∈ E₂ := E₂.mul_mem hx (E₂.inv_mem hu₂)
      have h2 := hZ _ (hcen hE2 hu₂ hu₂W _ h1E h1)
      have e : x = (x * u₂⁻¹) * u₂ := by group
      rw [e]
      exact E₁.mul_mem h2 hu₂E₁
  exact (eq_of_le_of_index_two h22 h12 hle).symm

end Abstract

section Ambient

variable {X : Type*} [Group X]

theorem comm_of_isElemAbelian {E : Subgroup X} (h : IsElemAbelian 2 E) :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun _ ha _ hb => CFSG.Open.IsElemAbelian.comm h ha hb

theorem sq_of_isElemAbelian {E : Subgroup X} (h : IsElemAbelian 2 E) : ∀ a ∈ E, a * a = 1 :=
  fun _ ha => by rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one h ha

theorem eq_of_relIndex_two {K W E₁ E₂ : Subgroup X} (hWK : W ≤ K) (h1K : E₁ ≤ K) (h2K : E₂ ≤ K)
    (hW2 : W.relIndex K = 2) (h12 : E₁.relIndex K = 2) (h22 : E₂.relIndex K = 2)
    (hW : IsElemAbelian 2 W) (hE1 : IsElemAbelian 2 E₁) (hE2 : IsElemAbelian 2 E₂)
    (hK : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) (hne1 : E₁ ≠ W) (hne2 : E₂ ≠ W) : E₁ = E₂ := by
  have hinj : ∀ {Y Z : Subgroup X}, Y ≤ K → Z ≤ K → Y.subgroupOf K = Z.subgroupOf K → Y = Z := by
    intro Y Z hY hZ h
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hY, inf_eq_left.2 hZ] at h
    exact h
  obtain ⟨a, ha, b, hb, hab⟩ := hK
  exact hinj h1K h2K (eq_of_index_two (W := W.subgroupOf K) hW2 h12 h22
    (fun x hx y hy => Subtype.ext (comm_of_isElemAbelian hW _ hx _ hy))
    (fun x hx => Subtype.ext (sq_of_isElemAbelian hW _ hx))
    (fun x hx y hy => Subtype.ext (comm_of_isElemAbelian hE1 _ hx _ hy))
    (fun x hx => Subtype.ext (sq_of_isElemAbelian hE1 _ hx))
    (fun x hx y hy => Subtype.ext (comm_of_isElemAbelian hE2 _ hx _ hy))
    (fun x hx => Subtype.ext (sq_of_isElemAbelian hE2 _ hx))
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
    (fun h => hne1 (hinj h1K hWK h)) (fun h => hne2 (hinj h2K hWK h)))

theorem relIndex_conjSub {W K : Subgroup X} {h : X} (hh : h ∈ Subgroup.normalizer (K : Set X)) :
    (conjSub h W).relIndex K = W.relIndex K := by
  calc (conjSub h W).relIndex K = (conjSub h W).relIndex (conjSub h K) := by
        rw [F7.conjSub_eq_of_mem_normalizer hh]
    _ = W.relIndex K := Subgroup.relIndex_map_map_of_injective W K (MulAut.conj h).injective

theorem conjSub_le_of_mem_normalizer {W K : Subgroup X} (hWK : W ≤ K) {h : X}
    (hh : h ∈ Subgroup.normalizer (K : Set X)) : conjSub h W ≤ K :=
  (conjSub_mono h hWK).trans (F7.conjSub_eq_of_mem_normalizer hh).le

theorem mem_normalizer_of_conjSub_eq {W : Subgroup X} {h : X} (he : conjSub h W = W) :
    h ∈ Subgroup.normalizer (W : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := mul_mem_conjSub (g := h) hx
    rwa [he] at this
  · intro hx
    rw [← he, mem_conjSub] at hx
    have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rwa [e] at hx

theorem le_normalizer_of_conjSub {H T W : Subgroup X} (hTH : T ≤ H) (hodd : ¬ 2 ∣ T.relIndex H)
    (hTW : T ≤ Subgroup.normalizer (W : Set X))
    (htwo : ∀ h₁ ∈ H, ∀ h ∈ H, conjSub h₁ W ≠ W → conjSub h W ≠ W →
      conjSub h W = conjSub h₁ W) :
    H ≤ Subgroup.normalizer (W : Set X) := by
  intro h₁ hh₁
  by_contra hn
  have hne : conjSub h₁ W ≠ W := fun he => hn (mem_normalizer_of_conjSub_eq he)
  have h2 : (H ⊓ Subgroup.normalizer (W : Set X)).relIndex H = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨h₁, hh₁, fun h => hn h.2, fun b hb => ?_⟩
    by_cases hbN : b ∈ Subgroup.normalizer (W : Set X)
    · exact Or.inr ⟨hb, hbN⟩
    · left
      refine ⟨H.mul_mem hh₁ hb, mem_normalizer_of_conjSub_eq ?_⟩
      have hb' : conjSub b W ≠ W := fun he => hbN (mem_normalizer_of_conjSub_eq he)
      rw [conjSub_mul, htwo h₁ hh₁ b hb hne hb', ← conjSub_mul]
      by_contra h3
      have e2 := htwo h₁ hh₁ (h₁ * h₁) (H.mul_mem hh₁ hh₁) hne h3
      rw [conjSub_mul, conjSub_inj] at e2
      exact hne e2
  have h3 := Subgroup.relIndex_mul_relIndex T (H ⊓ Subgroup.normalizer (W : Set X)) H
    (le_inf hTH hTW) inf_le_left
  rw [h2] at h3
  exact hodd (Dvd.intro_left _ h3)

end Ambient

end A6Eleven

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

theorem VH_split {x : G} (hx : x ∈ conjClosure V H) :
    (C.v : G) * x ∈ C.W ∨ x ∈ C.W := by
  obtain ⟨hxN, h⟩ := S.rho_VH hNS h13315 h1356two hH hab hx
  rcases h with h | h
  · exact Or.inr ⟨hx, (S.rho_eq_one_iff ⟨x, hxN⟩).1 h⟩
  · refine Or.inl ⟨(conjClosure V H).mul_mem C.v_mem hx, ?_⟩
    have h1 : S.frame.ρ (C.v * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, C.rho_v, h]
      exact swap45_sq
    exact (S.rho_eq_one_iff _).1 h1

omit hNS h13315 h1356two hH hab in
theorem v_not_mem_W : (C.v : G) ∉ C.W := by
  intro h
  have h1 := (S.rho_eq_one_iff C.v).2 h.2
  rw [C.rho_v] at h1
  exact absurd h1 (by decide)

theorem relIndex_W : C.W.relIndex (conjClosure V H) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
  exact ⟨C.v, C.v_mem, C.v_not_mem_W, fun x hx => C.VH_split hNS h13315 h1356two hH hab hx⟩

theorem UHg_le_A :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ C.A :=
  fun _ hx => ⟨C.UHg_le_VHg hx, (C.UHg_le_cLT hNS h13315 h1356two hH hab hx).2⟩

theorem isElemAbelian_W_of_eq
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (hAW : C.A = C.W) : IsElemAbelian 2 C.W := by
  have key : ∀ x : G, x ∈ fsuV1 T V → (C.g : G) * x * (C.g : G)⁻¹ ∈ fsuV1 T V → x = 1 := by
    intro x hx hgx
    refine C.V1g_inf_UH hab hna ?_ (S.V1_le_UH hx)
    rw [mem_conjSub, inv_inv]
    exact hgx
  have hWA : ∀ {x : G}, x ∈ C.W → (C.g : G) * x * (C.g : G)⁻¹ ∈ conjClosure V H :=
    fun {x} hx => (C.mem_VHg).1 (show x ∈ C.A by rw [hAW]; exact hx).1
  rw [F7.isElemAbelian_iff]
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 := S.comm_VH_mem_V1 hNS h13315 h1356two hH hab hx.1 hy.1
    have h2 := S.comm_VH_mem_V1 hNS h13315 h1356two hH hab (hWA hx) (hWA hy)
    have e : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹) *
          ((C.g : G) * x * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹)⁻¹ := by group
    rw [← e] at h2
    have h3 := key _ h1 h2
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  · have h1 := S.sq_VH_mem_V1 hNS h13315 h1356two hH hab hx.1
    have h2 := S.sq_VH_mem_V1 hNS h13315 h1356two hH hab (hWA hx)
    have e : (C.g : G) * (x * x) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) := by group
    rw [← e] at h2
    rw [pow_two]
    exact key _ h1 h2

theorem not_comm_VH (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (hW : IsElemAbelian 2 C.W) :
    ∃ a ∈ conjClosure V H, ∃ b ∈ conjClosure V H, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  apply hna
  rw [F7.isElemAbelian_iff]
  refine ⟨hc, fun x hx => ?_⟩
  rcases C.VH_split hNS h13315 h1356two hH hab hx with h | h
  · have h1 : ((C.v : G) * x) ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hW h
    have hvx := hc _ C.v_mem _ hx
    have e : ((C.v : G) * x) ^ 2 = (C.v : G) * C.v * x ^ 2 := by
      rw [pow_two, pow_two]
      calc (C.v : G) * x * ((C.v : G) * x) = (C.v : G) * (x * C.v) * x := by group
        _ = (C.v : G) * (C.v * x) * x := by rw [← hvx]
        _ = (C.v : G) * C.v * (x * x) := by group
    rw [e, C.v_sq, one_mul] at h1
    exact h1
  · exact F7.isElemAbelian_pow_eq_one hW h

omit hab in
theorem T_le_normalizer_W :
    T ≤ Subgroup.normalizer (C.W : Set G) := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  refine A5.le_normalizer_of_forall_conj_mem fun t ht x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (hF.T_le_H ht)) x).mp
      hx.1
  · exact A5.conj_mem_centralizer_of_mem_normalizer (S.frame.T_le ht) hx.2

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem A_le_T : C.A ≤ T := fun _ hx =>
  S.cLT_le_T hhat ⟨C.VHg_le_LT hNS h13315 h1356two hH hab hx.1, hx.2⟩

theorem comm_A_UH_of_le
    (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (hle : conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ pCoreOf 2 H) {a u : G} (ha : a ∈ C.A)
    (hu : u ∈ conjClosure S.V3 H) : a * u * a⁻¹ * u⁻¹ = 1 := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hgg : (C.g : G) * C.g ∈ H := hF.L₁T_le_H (C.g_sq_mem hhat)
  have hxU : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [mem_conjSub, inv_inv]
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hgg) u).mp hu
    have e : (C.g : G) * ((C.g : G) * u * (C.g : G)⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * C.g * u * ((C.g : G) * C.g)⁻¹ := by group
    rw [e]
    exact this
  have hxQ := hle hxU
  have hxC : (C.g : G) * u * (C.g : G)⁻¹ ∈
      Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    exact (C.comm_DHg_UH hNS h13315 h1356two hH hab hhat hna ⟨hxU, hxQ⟩ hu').symm
  have hy : (C.g : G) * a * (C.g : G)⁻¹ ∈ conjClosure V H := (C.mem_VHg).1 ha.1
  have h1 := S.comm_VH_HC hNS h13315 h1356two hH hxQ hxC hy
  have h2 : a * u * a⁻¹ * u⁻¹ ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V) := by
    rw [mem_conjSub, inv_inv]
    have e : (C.g : G) * (a * u * a⁻¹ * u⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * a * (C.g : G)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹) *
          ((C.g : G) * a * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  have haH : a ∈ H := hF.T_le_H (C.A_le_T hNS h13315 h1356two hH hab hhat ha)
  have h3 : a * u * a⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure S.V3 H haH) u).mp hu) ((conjClosure S.V3 H).inv_mem hu)
  exact C.V1g_inf_UH hab hna h2 h3

theorem A_eq_W_of_le (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hle : conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ pCoreOf 2 H) :
    C.A = C.W := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hAQ : C.A ≤ pCoreOf 2 H := by
    intro a ha
    have haH : a ∈ H := hF.T_le_H (C.A_le_T hNS h13315 h1356two hH hab hhat ha)
    rw [hF.pCoreOf_eq_centralizerMod, mem_centralizerMod]
    refine ⟨haH, hF.H_normalizes_V₁ haH, fun u hu => ?_⟩
    rw [C.comm_A_UH_of_le hNS h13315 h1356two hH hab hhat hna hle ha hu]
    exact (fsuV1 T V).one_mem
  have hAW : C.A ≤ C.W := by
    intro a ha
    have h1 : a ∈ C.ZI := by
      rw [← C.A_inf_QH hNS h13315 h1356two hH hab hhat hna h13314]
      exact ⟨ha, hAQ ha⟩
    exact ⟨C.ZI_le_VH h1, ha.2⟩
  have hcard : Nat.card C.A = Nat.card C.W := by
    rw [C.A_eq_conj hNS h13315 h1356two hH hab hhat, A5.card_conjSub']
  exact Subgroup.eq_of_le_of_card_ge hAW hcard.ge

theorem not_UHg_le_QH (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) : ¬ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ pCoreOf 2 H := by
  intro hle
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hAW := C.A_eq_W_of_le hNS h13315 h1356two hH hab hhat hna h13314 hle
  have hW := C.isElemAbelian_W_of_eq hNS h13315 h1356two hH hab hna hAW
  have hW2 := C.relIndex_W hNS h13315 h1356two hH hab
  have hK := C.not_comm_VH hNS h13315 h1356two hH hab hna hW
  have hconj : ∀ h ∈ H, conjSub h C.W ≤ conjClosure V H ∧
      (conjSub h C.W).relIndex (conjClosure V H) = 2 ∧ IsElemAbelian 2 (conjSub h C.W) := by
    intro h hh
    have hN := le_normalizer_conjClosure V H hh
    exact ⟨A6Eleven.conjSub_le_of_mem_normalizer C.W_le hN,
      (A6Eleven.relIndex_conjSub hN).trans hW2, F7.isElemAbelian_conjSub hW⟩
  have hHW : H ≤ Subgroup.normalizer (C.W : Set G) := by
    refine A6Eleven.le_normalizer_of_conjSub hF.T_le_H
      (A5.isSylowTwoOf_of_le S.h13.sylow hF.T_le_H).2.2
      (C.T_le_normalizer_W hNS h13315 h1356two hH) fun h₁ hh₁ h hh hne1 hne => ?_
    obtain ⟨h1K, h12, hE1⟩ := hconj h hh
    obtain ⟨h2K, h22, hE2⟩ := hconj h₁ hh₁
    exact A6Eleven.eq_of_relIndex_two C.W_le h1K h2K hW2 h12 h22 hW hE1 hE2 hK hne hne1
  apply hna
  refine F7.isElemAbelian_mono hW (conjClosure_le fun h hh x hx => ?_)
  have hxW : x ∈ C.W := by
    rw [← hAW]
    exact C.ZI_le_A hNS h13315 h1356two hH hab (C.V_le_ZI hx)
  exact (Subgroup.mem_normalizer_iff.mp (hHW hh) x).mp hxW

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
