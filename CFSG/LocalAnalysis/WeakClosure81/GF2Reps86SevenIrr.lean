module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86SevenIdx
import CFSG.GH74.QTGen4.Leaves.L14742Aut
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8One

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn StableUnder)

private theorem exists_altPreRestrict {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    {ψ : ↥H →* Perm (Fin n)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) :
    ∃ ψ' : ↥(altPre ψ) →* Perm (Fin n), Function.Injective ψ' ∧
      alternatingGroup (Fin n) ≤ ψ'.range ∧ altPre ψ' = altPre ψ ∧
      ∀ (x : ↥H) (hx : (x : MulAut V) ∈ altPre ψ), ψ' ⟨(x : MulAut V), hx⟩ = ψ x := by
  refine ⟨ψ.comp (Subgroup.inclusion altPre_le), hψ.comp (Subgroup.inclusion_injective _), ?_, ?_,
    fun x hx => rfl⟩
  · intro σ hσ
    obtain ⟨x, hx⟩ := hA hσ
    exact ⟨⟨x, coe_mem_altPre_iff.2 (hx ▸ hσ)⟩, hx⟩
  · refine altPre_eq_of_range_le ?_
    rintro _ ⟨l, rfl⟩
    exact (coe_mem_altPre_iff (ψ := ψ) (x := Subgroup.inclusion altPre_le l)).1 l.2

private theorem false_of_mem_altPre_seven {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)}
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 7) ≤ ψ.range)
    (hirr : IsIrrOn H ⊤ ⊥) {t : ↥H} (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1) (hsw : ¬ (ψ t).IsSwap)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8)
    (hte : ψ t ∈ alternatingGroup (Fin 7)) {J : Subgroup V} (hJ : StableUnder (altPre ψ) J)
    (hJ0 : J ≠ ⊥) (hJ1 : J ≠ ⊤) : False := by
  obtain ⟨ψ', hψ', hA', hpre, hψ'val⟩ := exists_altPreRestrict hψ hA
  have hfix : fixV (altPre ψ) = ⊥ := fixV_altPre_eq_bot (by norm_num) hA hirr
  have hcomm : commV (altPre ψ) = ⊤ :=
    commV_eq_top_of_normalizer hirr le_normalizer_altPre hfix
  have hperf : commutator ↥(altPre ψ) = ⊤ := commutator_altPre_eq_top (by norm_num) hψ hA
  have htL : (t : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 hte
  have hJst : altPre ψ ≤ stabSub J := B1.le_stabSub_of_invariant hJ
  obtain ⟨Z₀, Z₁, hZ, hZJ, hZL⟩ := exists_isChiefFac_altPre (H := altPre ψ) (ψ := ψ')
    (by norm_num) hψ' hA' hJst (by rw [hpre, hfix]; exact fun h => hJ0 (le_bot_iff.1 h))
  obtain ⟨Z₀', Z₁', hZ', hJZ, hZL'⟩ := exists_isChiefFac_above_of_perfect hperf le_rfl hJst
    (fun hc => hJ1 (by
      have h1 := isCentralSec_iff_commSub_le.1 hc
      rw [← commV_eq_commSub, hcomm] at h1
      exact top_le_iff.1 h1))
  have htt : ψ' ⟨(t : MulAut V), htL⟩ = ψ t := hψ'val t htL
  have ht' : (⟨(t : MulAut V), htL⟩ : ↥(altPre ψ)) ^ 2 = 1 :=
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      change (t : MulAut V) ^ 2 = 1
      rw [← Subgroup.coe_pow, ht]
      rfl)
  have h4 : 4 ≤ secIdx Z₀ Z₁ (t : MulAut V) :=
    four_le_secIdx_seven hV hψ' hA' hZ hZL (t := ⟨(t : MulAut V), htL⟩) ht'
      (by rw [htt]; exact ht1) (by rw [htt]; exact hsw)
  have h4' : 4 ≤ secIdx Z₀' Z₁' (t : MulAut V) :=
    four_le_secIdx_seven hV hψ' hA' hZ' (by rw [hpre]; exact hZL')
      (t := ⟨(t : MulAut V), htL⟩) ht' (by rw [htt]; exact ht1) (by rw [htt]; exact hsw)
  have h16 := secIdx_mul_secIdx_le hZ.le (hZJ.trans hJZ) hZ'.le (hZ.stab₁ htL) (hZ'.stab₁ htL)
  have := Nat.mul_le_mul h4 h4'
  omega

private theorem false_of_not_mem_altPre_seven {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)}
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 7) ≤ ψ.range)
    (hirr : IsIrrOn H ⊤ ⊥) {t : ↥H} (ht : t ^ 2 = 1)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8)
    (hte : ψ t ∉ alternatingGroup (Fin 7)) {J : Subgroup V} (hJ : StableUnder (altPre ψ) J)
    (hJ0 : J ≠ ⊥) (hJ1 : J ≠ ⊤) : False := by
  obtain ⟨ψ', hψ', hA', hpre, -⟩ := exists_altPreRestrict hψ hA
  have hfix : fixV (altPre ψ) = ⊥ := fixV_altPre_eq_bot (by norm_num) hA hirr
  have hcos : ∀ h : ↥H, (h : MulAut V) ∈ altPre ψ ∨ ((h * t : ↥H) : MulAut V) ∈ altPre ψ := by
    intro h
    by_cases hh : ψ h ∈ alternatingGroup (Fin 7)
    · exact Or.inl (coe_mem_altPre_iff.2 hh)
    · right
      refine coe_mem_altPre_iff.2 ?_
      rw [map_mul]
      rw [Perm.mem_alternatingGroup] at hh hte ⊢
      rw [Perm.sign_mul]
      rcases Int.units_eq_one_or (Perm.sign (ψ h)) with h1 | h1
      · exact absurd h1 hh
      rcases Int.units_eq_one_or (Perm.sign (ψ t)) with h2 | h2
      · exact absurd h2 hte
      rw [h1, h2]
      decide
  have := finite_subgroup (V := V)
  obtain ⟨J₁, ⟨hJ₁st, hJ₁0, hJ₁J⟩, hmin⟩ := Set.exists_min_image
    {K : Subgroup V | StableUnder (altPre ψ) K ∧ K ≠ ⊥ ∧ K ≤ J} (fun K => Nat.card K)
    (Set.toFinite _) ⟨J, hJ, hJ0, le_rfl⟩
  have hJ₁1 : J₁ ≠ ⊤ := fun h => hJ1 (top_le_iff.1 (h ▸ hJ₁J))
  have hJ₁min : ∀ K : Subgroup V, StableUnder (altPre ψ) K → K ≤ J₁ → K = ⊥ ∨ K = J₁ := by
    intro K hK hKJ₁
    by_cases hK0 : K = ⊥
    · exact Or.inl hK0
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hKJ₁ (hmin K ⟨hK, hK0, hKJ₁.trans hJ₁J⟩))
  obtain ⟨tJ₁, hmemt, hcardt⟩ : ∃ K : Subgroup V,
      (∀ u, u ∈ K ↔ ∃ v ∈ J₁, (t : MulAut V) v = u) ∧ Nat.card K = Nat.card J₁ :=
    ⟨J₁.map (t : MulAut V).toMonoidHom, fun u => Subgroup.mem_map,
      Subgroup.card_map_of_injective (t : MulAut V).injective⟩
  have htJ₁st : StableUnder (altPre ψ) tJ₁ := by
    intro l hl u hu
    obtain ⟨v, hv, rfl⟩ := (hmemt u).1 hu
    have hl' : (t : MulAut V)⁻¹ * l * (t : MulAut V) ∈ altPre ψ := by
      have := conj_mem_altPre (H.inv_mem t.2) hl
      rwa [inv_inv] at this
    refine (hmemt _).2 ⟨_, hJ₁st _ hl' v hv, ?_⟩
    simp [MulAut.mul_apply]
  have hinf : StableUnder (altPre ψ) (J₁ ⊓ tJ₁) := fun l hl u hu =>
    ⟨hJ₁st l hl u hu.1, htJ₁st l hl u hu.2⟩
  rcases hJ₁min _ hinf inf_le_left with hbot | htop
  · have hdisj : fixV (Subgroup.zpowers (t : MulAut V)) ⊓ J₁ = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have htu : (t : MulAut V) u = u := mem_fixV_zpowers_iff_apply.1 hu.1
      have h1 : u ∈ J₁ ⊓ tJ₁ := ⟨hu.2, (hmemt u).2 ⟨u, hu.2, htu⟩⟩
      rwa [hbot] at h1
    have hcardJ₁ : Nat.card J₁ ≤ 8 := by
      have h1 := (fixV (Subgroup.zpowers (t : MulAut V))).relIndex_mul_card J₁
      rw [hdisj, Subgroup.card_bot, mul_one] at h1
      exact h1 ▸ (relIndex_fixV_le_index _ J₁).trans hidx
    have hY : IsChiefFac (altPre ψ) ⊥ J₁ :=
      ⟨bot_lt_iff_ne_bot.2 hJ₁0, le_stabSub_bot _, B1.le_stabSub_of_invariant hJ₁st,
        fun Z hZ h₀ h₁ => hJ₁min Z (fun x hx u hu => (hZ hx u).2 hu) h₁⟩
    have hYL : ¬ IsCentralSec (altPre ψ') ⊥ J₁ := by
      rw [hpre, isCentralSec_bot_iff, hfix]
      exact fun h => hJ₁0 (le_bot_iff.1 h)
    obtain ⟨e, -⟩ := exists_secTransport (H := altPre ψ) (ψ := ψ') (by norm_num) hψ' hA' hY hYL
    have h2520 : 2520 ∣ Nat.card (MulAut (Sec J₁ ⊥)) := by
      have h1 := Subgroup.card_subgroup_dvd_card (autSec (altPre ψ) J₁ ⊥)
      rwa [← Nat.card_congr e.toEquiv, card_altPre_seven hψ hA] at h1
    have hSec : Nat.card (Sec J₁ ⊥) ≤ 8 :=
      (Nat.card_le_card_of_surjective (QuotientGroup.mk : ↥J₁ → Sec J₁ ⊥)
        QuotientGroup.mk_surjective).trans hcardJ₁
    have h168 := CFSG.GH74.QTGen4.Leaves.L14742.card_mulAut_dvd_168 (fun a b => mul_comm a b)
      (sq_eq_one_sec hV J₁ ⊥) hSec
    have := h2520.trans h168
    omega
  · have hle : J₁ ≤ tJ₁ := htop ▸ inf_le_right
    have heq : J₁ = tJ₁ := Subgroup.eq_of_le_of_card_ge hle hcardt.le
    have hmemJ : ∀ u ∈ J₁, (t : MulAut V) u ∈ J₁ := fun u hu =>
      heq.symm ▸ (hmemt _).2 ⟨u, hu, rfl⟩
    have hstH : StableUnder H J₁ := by
      intro h hh u hu
      rcases hcos ⟨h, hh⟩ with hL | hL
      · exact hJ₁st h hL u hu
      · have hL' : h * (t : MulAut V) ∈ altPre ψ := hL
        have h1 := hJ₁st _ hL' _ (hmemJ u hu)
        have h2 : (h * (t : MulAut V)) ((t : MulAut V) u) = h u := by
          have h3 : (t : MulAut V) * (t : MulAut V) = 1 := by
            rw [← sq, ← Subgroup.coe_pow, ht]
            rfl
          rw [MulAut.mul_apply]
          exact congrArg (fun f : MulAut V => h (f u)) h3
        rwa [h2] at h1
    rcases hirr.2.2.2 J₁ hstH bot_le le_top with h | h
    · exact hJ₁0 h
    · exact hJ₁1 h

theorem isIrrOn_altPre_seven {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) (hirr : IsIrrOn H ⊤ ⊥) {t : ↥H}
    (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1) (hsw : ¬ (ψ t).IsSwap)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8) : IsIrrOn (altPre ψ) ⊤ ⊥ := by
  refine ⟨hirr.1, fun _ _ _ _ => Subgroup.mem_top _, fun x _ u hu => ?_, fun J hJ _ _ => ?_⟩
  · rw [Subgroup.mem_bot.1 hu, map_one]
    exact Subgroup.one_mem _
  · by_contra hne
    push Not at hne
    by_cases hte : ψ t ∈ alternatingGroup (Fin 7)
    · exact false_of_mem_altPre_seven hV hψ hA hirr ht ht1 hsw hidx hte hJ hne.1 hne.2
    · exact false_of_not_mem_altPre_seven hV hψ hA hirr ht hidx hte hJ hne.1 hne.2

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
