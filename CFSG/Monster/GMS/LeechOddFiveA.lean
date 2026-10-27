module

public import CFSG.Monster.GMS.LeechOddSetup
public import CFSG.Monster.GMS.Facts.Section4Coh

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀ q₀)
open scoped commutatorElement
open CFSG.Sporadic.Co1.Module.Odd (fiveA_trans fiveA_outer fiveA_triple fiveA_nondeg)

namespace LeechOdd

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ w b x : G}

theorem typeSet_zero_conj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (hY : IsOddPair a w b x) (L : LeechSystem w) (hty : LeechOddType w b x 2) {q₁ q₂ : G}
    (h₁ : q₁ ∈ L.typeSet 0) (h₂ : q₂ ∈ L.typeSet 0)
    (hH₁ : q₁ ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (hH₂ : q₂ ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :
    ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G),
      g * q₁ * g⁻¹ = q₂ := by
  have hyp := oddPairHyp I hG hw hY L
  have hot := oddType I hG hw hY L hty
  have hv₁ := (mem_inf_iff_vec I hG hw hY L h₁.1).1 hH₁
  have hv₂ := (mem_inf_iff_vec I hG hw hY L h₂.1).1 hH₂
  obtain ⟨z, hz, hzu⟩ := fiveA_trans hyp hot _ hv₁ _ hv₂ h₁.2 h₂.2
  obtain ⟨c, hcw, hcH, hcz⟩ := exists_lift I hG hw hY L hz
  have hcq : c * q₁ * c⁻¹ ∈ leechQ w := L.conj_mem' hcw h₁.1
  have hvec : L.vec (c * q₁ * c⁻¹) = L.vec q₂ := by
    rw [L.vec_conj' hcw h₁.1, hcz, hzu]
  rcases L.eq_or_eq_mul_z hcq h₂.1 hvec with h | h
  · exact ⟨c, hcH, h⟩
  ·
    have hnd := fiveA_nondeg hyp hot
    obtain ⟨v, hvV, hbil⟩ : ∃ v ∈ co1Fix (L.φ ⟨b, hY.1⟩) ∩ co1Fix (L.φ ⟨x, hY.2.1⟩),
        bil₀ (L.vec q₂) v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact L.vec_ne_zero_of_mem_typeSet h₂ (hnd _ hv₂ hcon)
    obtain ⟨p, hpQ, hpv⟩ := L.vec_surj v
    have hpH := (mem_inf_iff_vec I hG hw hY L hpQ).2 (by rw [hpv]; exact hvV)
    have hb1 : bil₀ (L.vec p) (L.vec q₂) = 1 := by
      rw [hpv, CFSG.Sporadic.Co1.Module.bil₀_comm]
      rcases CFSG.Sporadic.Co1.Module.zmod2_cases (bil₀ (L.vec q₂) v) with h0 | h1
      · exact absurd h0 hbil
      · exact h1
    have hcomm : ⁅p, q₂⁆ = w := (L.comm_eq_z_iff hpQ h₂.1).2 hb1
    have hpC : p * w = w * p := Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer hpQ)
    have hqC : q₂ * w = w * q₂ := Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer h₂.1)
    have hww : w * w = 1 := L.z_mul_self
    refine ⟨p * c, Subgroup.mul_mem _ hpH hcH, ?_⟩
    have hA : p * q₂ * p⁻¹ = w * q₂ := by
      have h' : p * q₂ * p⁻¹ * q₂⁻¹ = w := hcomm
      calc p * q₂ * p⁻¹ = (p * q₂ * p⁻¹ * q₂⁻¹) * q₂ := by group
        _ = w * q₂ := by rw [h']
    have hB : p * w * p⁻¹ = w := by
      rw [hpC]
      group
    calc p * c * q₁ * (p * c)⁻¹ = p * (c * q₁ * c⁻¹) * p⁻¹ := by group
      _ = p * (q₂ * w) * p⁻¹ := by rw [h]
      _ = (p * q₂ * p⁻¹) * (p * w * p⁻¹) := by group
      _ = (w * q₂) * w := by rw [hA, hB]
      _ = (q₂ * w) * w := by rw [hqC]
      _ = q₂ * (w * w) := by rw [mul_assoc]
      _ = q₂ := by rw [hww, mul_one]

theorem exists_conj_typeSet_zero
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) (hY : IsOddPair a w b x) (L : LeechSystem w) (hty : LeechOddType w b x 2)
    {t : G} (ht : t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (ht2 : orderOf t = 2) (hta : IsConj a t) :
    ∃ h ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G),
      h * t * h⁻¹ ∈ L.typeSet 0 := by
  have hyp := oddPairHyp I hG hw hY L
  have hot := oddType I hG hw hY L hty
  have hI : Co1InvolutionFacts := co1InvolutionFacts
  obtain ⟨h₀, hh₀, hth₀⟩ := exists_conj_mem_centralizer I hG hw hY (k := 2) (by decide) hty ht ht2
  set t₁ := h₀ * t * h₀⁻¹ with ht₁
  have ht₁H : t₁ ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    mul_mem (mul_mem hh₀ ht) (inv_mem hh₀)
  have ht₁2 : orderOf t₁ = 2 := by rw [ht₁, orderOf_conj_eq]; exact ht2
  have ht₁a : IsConj a t₁ := hta.trans (isConj_iff.2 ⟨h₀, rfl⟩)
  by_cases hQ : t₁ ∈ leechQ w
  · exact ⟨h₀, hh₀, S365.mem_typeSet_zero_of_isConj I hG hw L hQ ht₁a⟩
  ·
    have hlift := S365.isLeechCentralLift_of_isConj I hG hw hth₀ ht₁a hQ
    have hφ := phi_mem_inf hY L hth₀ ht₁H
    have hy2 : L.φ ⟨t₁, hth₀⟩ * L.φ ⟨t₁, hth₀⟩ = 1 := L.φ_mul_self hth₀ hlift.mul_self
    obtain ⟨u, v, hvV, hv4, huv⟩ := fiveA_outer hyp hot _ hφ (L.isCo1TwoA_phi hI hlift)
    obtain ⟨p, hpQ, hpu⟩ := L.vec_surj u
    have hqQ : t₁⁻¹ * p * t₁ * p⁻¹ ∈ leechQ w := by
      have h1 : t₁⁻¹ * p * t₁⁻¹⁻¹ ∈ leechQ w := L.conj_mem' (inv_mem hth₀) hpQ
      have h2 : t₁⁻¹ * p * t₁ * p⁻¹ = (t₁⁻¹ * p * t₁⁻¹⁻¹) * p⁻¹ := by group
      rw [h2]
      exact mul_mem h1 (inv_mem hpQ)
    set q := t₁⁻¹ * p * t₁ * p⁻¹ with hq
    have hinv : L.φ ⟨t₁⁻¹, inv_mem hth₀⟩ = L.φ ⟨t₁, hth₀⟩ := by
      have h1 : (⟨t₁⁻¹, inv_mem hth₀⟩ : Subgroup.centralizer ({w} : Set G)) =
          (⟨t₁, hth₀⟩ : Subgroup.centralizer ({w} : Set G))⁻¹ := rfl
      rw [h1, map_inv]
      exact inv_eq_of_mul_eq_one_right hy2
    have hA : t₁⁻¹ * p * t₁ ∈ leechQ w := by
      have := L.conj_mem' (inv_mem hth₀) hpQ
      simpa using this
    have e1 : L.vec (t₁⁻¹ * p * t₁) = co1Act (L.φ ⟨t₁, hth₀⟩) u := by
      have h := L.vec_conj' (inv_mem hth₀) hpQ
      rw [inv_inv] at h
      rw [h, hpu, hinv]
    have hqv : L.vec q = v := by
      rw [hq, L.vec_mul _ hA _ (inv_mem hpQ), e1, L.vec_inv hpQ, hpu]
      exact huv
    have hqH := (mem_inf_iff_vec I hG hw hY L hqQ).2 (by rw [hqv]; exact hvV)
    have hq4 : q ∈ L.typeSet 2 := ⟨hqQ, by rw [hqv]; exact hv4⟩
    have hq2B : IsConj z₀ q := S365.isConj_of_mem_typeSet_two I hG hw L hq4
    have hvfix : co1Act (L.φ ⟨t₁, hth₀⟩) v = v := by
      rw [← huv, map_add, CFSG.Monster.GMS.Leech.co1Act_co1Act_of_mul_self_eq_one hy2, add_comm]
    have hcomm : t₁ * q = q * t₁ :=
      L.commute_of_vec_mem_co1Fix hI hlift hqQ (by rw [hqv]; exact hvfix)
    have hmul : IsConj a (t₁ * q) := by
      have e : p * t₁ * p⁻¹ = t₁ * q := by rw [hq]; group
      exact ht₁a.trans (isConj_iff.2 ⟨p, e⟩)
    have ht₁Q : t₁ ∈ leechQ q :=
      mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG ht₁a hq2B hcomm hmul
    obtain ⟨h₁, hh₁, hh₁q⟩ := s348_transitive I.sls I.tableV I.leech I.leechOddPair I.tableIV hG
      hY.2.2.1 (hY.mem_oddNbr hw) hqH hY.mem_inf hq2B hw
    have hQ' : h₁ * t₁ * h₁⁻¹ ∈ leechQ w := by
      have := conj_mem_leechQ_conj (c := h₁) ht₁Q
      rwa [hh₁q] at this
    have hconj' : IsConj a (h₁ * t₁ * h₁⁻¹) := ht₁a.trans (isConj_iff.2 ⟨h₁, rfl⟩)
    refine ⟨h₁ * h₀, Subgroup.mul_mem _ hh₁ hh₀, ?_⟩
    have e : h₁ * h₀ * t * (h₁ * h₀)⁻¹ = h₁ * t₁ * h₁⁻¹ := by rw [ht₁]; group
    rw [e]
    exact S365.mem_typeSet_zero_of_isConj I hG hw L hQ' hconj'

end LeechOdd

open LeechOdd

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem fiveAInvolutions_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    FiveAInvolutions a z₀ := by
  intro b x hb hx
  obtain ⟨⟨hxa, hxb, hodd, w, hwH, hwB⟩, hk⟩ := hx
  have hY : IsOddPair a w b x := IsOddPair.of_mem_inf hb hxa hxb.symm hodd hwH
  have hty : LeechOddType w b x 2 := hk w hwH hwB
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG hwB
  have hyp := oddPairHyp I hG hwB hY L
  have hot := oddType I hG hwB hY L hty
  refine ⟨?_, ?_⟩
  · intro t ht s hs ht2 hs2 hcls
    rcases hcls with ⟨hta, hsa⟩ | ⟨htb, hsb⟩
    · obtain ⟨h₁, hh₁, hth₁⟩ := exists_conj_typeSet_zero I hG hwB hY L hty ht ht2 hta
      obtain ⟨h₂, hh₂, hsh₂⟩ := exists_conj_typeSet_zero I hG hwB hY L hty hs hs2 hsa
      have hH₁ : h₁ * t * h₁⁻¹ ∈ Subgroup.centralizer ({b} : Set G) ⊓
          Subgroup.centralizer ({x} : Set G) := mul_mem (mul_mem hh₁ ht) (inv_mem hh₁)
      have hH₂ : h₂ * s * h₂⁻¹ ∈ Subgroup.centralizer ({b} : Set G) ⊓
          Subgroup.centralizer ({x} : Set G) := mul_mem (mul_mem hh₂ hs) (inv_mem hh₂)
      obtain ⟨g, hg, hgt⟩ := typeSet_zero_conj I hG hwB hY L hty hth₁ hsh₂ hH₁ hH₂
      refine ⟨h₂⁻¹ * g * h₁, mul_mem (mul_mem (inv_mem hh₂) hg) hh₁, ?_⟩
      calc h₂⁻¹ * g * h₁ * t * (h₂⁻¹ * g * h₁)⁻¹ = h₂⁻¹ * (g * (h₁ * t * h₁⁻¹) * g⁻¹) * h₂ := by
            group
        _ = h₂⁻¹ * (h₂ * s * h₂⁻¹) * h₂ := by rw [hgt]
        _ = s := by group
    · exact s348_transitive I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hb
        (hY.mem_oddNbr hwB) ht hs htb hsb
  · obtain ⟨u₁, u₂, hu₁, hu₂, hu₁₂, h₁, h₂, h₃⟩ := fiveA_triple hyp hot
    obtain ⟨q₁, hq₁Q, hq₁v⟩ := L.vec_surj u₁
    obtain ⟨q₃, hq₃Q, hq₃v⟩ := L.vec_surj (u₁ + u₂)
    have hq₁H := (mem_inf_iff_vec I hG hwB hY L hq₁Q).2 (by rw [hq₁v]; exact hu₁)
    have hq₃H := (mem_inf_iff_vec I hG hwB hY L hq₃Q).2 (by rw [hq₃v]; exact hu₁₂)
    have hq₁t : q₁ ∈ L.typeSet 0 := ⟨hq₁Q, by rw [hq₁v]; exact h₁⟩
    have hq₃t : q₃ ∈ L.typeSet 2 := ⟨hq₃Q, by rw [hq₃v]; exact h₃⟩
    have hb : bil₀ u₁ (u₁ + u₂) = 0 := by
      rw [Leech.bil₀_add_right, CFSG.Sporadic.Co1.Module.bil₀_self, zero_add]
      have h := CFSG.Sporadic.Co1.Module.q₀_add u₁ u₂
      rw [Leech.q₀_eq_zero_of_mem_co1Orbit_two h₃, Leech.q₀_eq_zero_of_mem_co1Orbit_zero h₁,
        Leech.q₀_eq_zero_of_mem_co1Orbit_zero h₂] at h
      simpa using h.symm
    have hcomm : q₁ * q₃ = q₃ * q₁ :=
      commutatorElement_eq_one_iff_mul_comm.1
        ((L.comm_eq_one_iff hq₁Q hq₃Q).2 (by rw [hq₁v, hq₃v]; exact hb))
    have hprod : q₁ * q₃ ∈ L.typeSet 0 := by
      refine ⟨mul_mem hq₁Q hq₃Q, ?_⟩
      rw [L.vec_mul q₁ hq₁Q q₃ hq₃Q, hq₁v, hq₃v, ← add_assoc,
        CFSG.Sporadic.Co1.Module.vec_add_self, zero_add]
      exact h₂
    exact ⟨q₁, hq₁H, q₃, hq₃H, hcomm, S365.isConj_of_mem_typeSet_zero I hG hwB L hq₁t,
      S365.isConj_of_mem_typeSet_two I hG hwB L hq₃t,
      S365.isConj_of_mem_typeSet_zero I hG hwB L hprod⟩

end CFSG.Monster.GMS