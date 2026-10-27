module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Sec
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86SevenGen
import CFSG.GH74.QTGen4.Leaves.L14742Aut
import CFSG.Quasithin.MS93.ML3Gen
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Tools
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn StableUnder)

theorem fixV_altPre_eq_bot {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    {ψ : ↥H →* Perm (Fin n)} (hn : 3 ≤ n) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hirr : IsIrrOn H ⊤ ⊥) : fixV (altPre ψ) = ⊥ := by
  have hst : StableUnder H (fixV (altPre ψ)) := fun x hx u hu =>
    (le_stabSub_fixV le_normalizer_altPre hx u).2 hu
  rcases hirr.2.2.2 _ hst bot_le le_top with h | h
  · exact h
  · exfalso
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simpa using hn)
    obtain ⟨σ, hσ⟩ := exists_ne (1 : alternatingGroup (Fin n))
    obtain ⟨x, hx⟩ := hA σ.2
    have hxL : (x : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 (hx ▸ σ.2)
    have hx1 : x = 1 := Subtype.ext (MulEquiv.ext fun v =>
      (h ▸ Subgroup.mem_top v : v ∈ fixV (altPre ψ)) _ hxL)
    exact hσ (Subtype.ext (by rw [← hx, hx1, map_one]; rfl))

theorem commV_eq_top_of_normalizer {V : Type*} [CommGroup V] {H L : Subgroup (MulAut V)}
    (hirr : IsIrrOn H ⊤ ⊥) (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hfix : fixV L = ⊥) : commV L = ⊤ := by
  have hst : StableUnder H (commV L) := fun x hx u hu =>
    (le_stabSub_commV hN hx u).2 hu
  rcases hirr.2.2.2 _ hst bot_le le_top with h | h
  · exfalso
    have hf : fixV L = ⊤ := by
      rw [eq_top_iff]
      intro w _ g hg
      have h1 : g w * w⁻¹ ∈ commV L := Subgroup.subset_closure ⟨g, hg, w, rfl⟩
      rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    rw [hfix] at hf
    exact hirr.1.ne hf
  · exact h

theorem card_altPre_seven {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) : Nat.card ↥(altPre ψ) = 2520 := by
  rw [Nat.card_congr (altPreEquiv hψ hA).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_commV_altPre_le_seven {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) {t : ↥H} (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1)
    (hsw : ¬ (ψ t).IsSwap) :
    Nat.card (commV (altPre ψ)) ≤ (fixV (Subgroup.zpowers (t : MulAut V))).index ^ 3 := by
  classical
  have hs : ψ t * ψ t = 1 := by rw [← map_mul, ← sq, ht, map_one]
  obtain ⟨g₁, g₂, hg⟩ := exists_conj_alternatingGroup_le_closure hs ht1 hsw
  obtain ⟨a, ha⟩ : ∃ a, ψ t a ≠ a := by
    by_contra h
    exact ht1 (Equiv.ext fun a => by_contra fun h' => h ⟨a, h'⟩)
  have hsa : ψ t (ψ t a) = a := by
    have := congrArg (fun f : Perm (Fin 7) => f a) hs
    simpa using this
  have hcomm : ψ t * swap a (ψ t a) = swap a (ψ t a) * ψ t := by
    have h1 := Equiv.swap_apply_apply (ψ t) a (ψ t a)
    rw [hsa, Equiv.swap_comm] at h1
    calc ψ t * swap a (ψ t a) = ψ t * swap a (ψ t a) * (ψ t)⁻¹ * ψ t :=
          (inv_mul_cancel_right _ _).symm
      _ = swap a (ψ t a) * ψ t := by rw [← h1]
  have hconj : ∀ g : Perm (Fin 7), ∃ h : ↥H, ψ h * ψ t * (ψ h)⁻¹ = g * ψ t * g⁻¹ := by
    intro g
    by_cases hge : g ∈ alternatingGroup (Fin 7)
    · obtain ⟨h, hh⟩ := hA hge
      exact ⟨h, by rw [hh]⟩
    · have hev : g * swap a (ψ t a) ∈ alternatingGroup (Fin 7) := by
        rw [Perm.mem_alternatingGroup] at hge ⊢
        rw [Perm.sign_mul, Perm.sign_swap (Ne.symm ha)]
        rcases Int.units_eq_one_or (Perm.sign g) with h | h
        · exact absurd h hge
        · rw [h]; decide
      obtain ⟨h, hh⟩ := hA hev
      refine ⟨h, ?_⟩
      rw [hh]
      calc g * swap a (ψ t a) * ψ t * (g * swap a (ψ t a))⁻¹
          = g * (swap a (ψ t a) * ψ t * (swap a (ψ t a))⁻¹) * g⁻¹ := by group
        _ = g * ψ t * g⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
  obtain ⟨h₁, hh₁⟩ := hconj g₁
  obtain ⟨h₂, hh₂⟩ := hconj g₂
  set c₁ : ↥H := h₁ * t * h₁⁻¹ with hc₁
  set c₂ : ↥H := h₂ * t * h₂⁻¹ with hc₂
  have hψc₁ : ψ c₁ = g₁ * ψ t * g₁⁻¹ := by rw [hc₁, map_mul, map_mul, map_inv, hh₁]
  have hψc₂ : ψ c₂ = g₂ * ψ t * g₂⁻¹ := by rw [hc₂, map_mul, map_mul, map_inv, hh₂]
  let S : Finset (MulAut V) := {(t : MulAut V), (c₁ : MulAut V), (c₂ : MulAut V)}
  have hKS : (Subgroup.closure {t, c₁, c₂}).map H.subtype =
      Subgroup.closure (S : Set (MulAut V)) := by
    rw [MonoidHom.map_closure]
    simp [S, Set.image_insert_eq]
  have hK : altPre ψ ≤ (Subgroup.closure {t, c₁, c₂}).map H.subtype := by
    intro x hx
    obtain ⟨hxH, hxA⟩ := mem_altPre_iff.1 hx
    have h1 : ψ ⟨x, hxH⟩ ∈ Subgroup.closure {ψ t, ψ c₁, ψ c₂} := by
      rw [hψc₁, hψc₂]
      exact hg hxA
    have h2 : ψ ⟨x, hxH⟩ ∈ (Subgroup.closure {t, c₁, c₂}).map ψ := by
      rw [MonoidHom.map_closure]
      simpa [Set.image_insert_eq] using h1
    obtain ⟨k, hk, hkx⟩ := h2
    have hkeq : k = ⟨x, hxH⟩ := hψ hkx
    exact ⟨k, hk, by rw [hkeq]; rfl⟩
  have hle : commV (altPre ψ) ≤ commV (Subgroup.closure (S : Set (MulAut V))) := by
    rw [← hKS]
    exact MS93.commV_mono hK
  have hcard : ∀ s : MulAut V, Nat.card (commV (Subgroup.zpowers s)) =
      (fixV (Subgroup.zpowers s)).index := fun s => by
    rw [commV_zpowers_eq_map, ← MonoidHom.range_eq_map, ← ker_commHom, Subgroup.index_ker]
  have hm : ∀ s ∈ S, Nat.card (commV (Subgroup.zpowers s)) =
      (fixV (Subgroup.zpowers (t : MulAut V))).index := by
    intro s hs'
    rw [hcard]
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl
    · rfl
    · exact FixVLat.index_fixV_zpowers_conj _ _
    · exact FixVLat.index_fixV_zpowers_conj _ _
  have hpos : 0 < (fixV (Subgroup.zpowers (t : MulAut V))).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  calc Nat.card (commV (altPre ψ))
      ≤ Nat.card (commV (Subgroup.closure (S : Set (MulAut V)))) := Subgroup.card_le_of_le hle
    _ ≤ ∏ s ∈ S, Nat.card (commV (Subgroup.zpowers s)) := card_commV_closure_le S
    _ = ∏ s ∈ S, (fixV (Subgroup.zpowers (t : MulAut V))).index := Finset.prod_congr rfl hm
    _ = (fixV (Subgroup.zpowers (t : MulAut V))).index ^ S.card := Finset.prod_const _
    _ ≤ (fixV (Subgroup.zpowers (t : MulAut V))).index ^ 3 :=
        Nat.pow_le_pow_right hpos Finset.card_le_three

theorem four_le_index_seven {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) (hL : commV (altPre ψ) = ⊤) {t : ↥H}
    (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1) (hsw : ¬ (ψ t).IsSwap) :
    4 ≤ (fixV (Subgroup.zpowers (t : MulAut V))).index := by
  by_contra hlt
  push Not at hlt
  have hcard := card_commV_altPre_le_seven hψ hA ht ht1 hsw
  rw [hL, Subgroup.card_top] at hcard
  have hp : IsPGroup 2 V := fun g => ⟨1, by simpa using hV g⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : (fixV (Subgroup.zpowers (t : MulAut V))).index ∣ 2 ^ k :=
    hk ▸ Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 2 := by
    rw [hj] at hlt ⊢
    have hj1 : j ≤ 1 := by
      by_contra hj2
      push Not at hj2
      have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
      omega
    calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 2 := by norm_num
  have hV8 : Nat.card V ≤ 8 :=
    hcard.trans (calc _ ≤ 2 ^ 3 := Nat.pow_le_pow_left hidx 3
      _ = 8 := by norm_num)
  have h168 := CFSG.GH74.QTGen4.Leaves.L14742.card_mulAut_dvd_168 (fun a b => mul_comm a b)
    hV hV8
  have h2520 := Subgroup.card_subgroup_dvd_card (altPre ψ)
  rw [card_altPre_seven hψ hA] at h2520
  have := h2520.trans h168
  omega

theorem four_le_secIdx_seven {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (hY : IsChiefFac H Y₀ Y₁)
    (hYL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) {t : ↥H} (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1)
    (hsw : ¬ (ψ t).IsSwap) : 4 ≤ secIdx Y₀ Y₁ t := by
  obtain ⟨e, φ, hφe, hφinj, hφr, hirr, hfix, hidx, -⟩ :=
    exists_secTransport (by norm_num) hψ hA hY hYL
  have hcomm : commV (altPre φ) = ⊤ :=
    commV_eq_top_of_normalizer hirr le_normalizer_altPre hfix
  have h4 := four_le_index_seven (sq_eq_one_sec hV Y₁ Y₀) hφinj (hφr ▸ hA) hcomm
    (t := e t) (by rw [← map_pow, ht, map_one]) (by rw [hφe]; exact ht1)
    (by rw [hφe]; exact hsw)
  rwa [hidx t] at h4

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
