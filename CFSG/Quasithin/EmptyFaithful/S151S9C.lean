module

public import CFSG.Quasithin.EmptyFaithful.S151S7A
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239Covers

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

theorem autFixSimple_of_inner {Q : Type} [Group Q] [Finite Q] {P : Subgroup Q}
    (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) (hZ : Subgroup.center Q = ⊥)
    (hin : ∀ β : Q ≃* Q, (∀ x, β (β x) = x) →
      (∃ P' : Sylow 2 Q, ∀ t ∈ (P' : Subgroup Q), β t = t) → IsInnerAut β) :
    AutFixSimple Q P := by
  intro φ hφ hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let β : Q ≃* Q :=
    { toFun := φ, invFun := φ, left_inv := hφ, right_inv := hφ, map_mul' := φ.map_mul }
  have hβ : ∀ x, β (β x) = x := hφ
  let P' : Sylow 2 Q := hP2.toSylow hPi
  have hP' : ∃ P'' : Sylow 2 Q, ∀ t ∈ (P'' : Subgroup Q), β t = t := ⟨P', fun t ht => hfix t ht⟩
  obtain ⟨l, hl⟩ := hin β hβ hP'
  have hφl : ∀ q, φ q = l⁻¹ * q * l := hl
  have hl2 : l * l = 1 := by
    have hc : l * l ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : β (β g) = g := hβ g
      have h2 : β (β g) = l⁻¹ * (l⁻¹ * g * l) * l := by
        change φ (φ g) = _
        rw [hφl, hφl]
      rw [h2] at h1
      calc g * (l * l) = l * l * (l⁻¹ * (l⁻¹ * g * l) * l) := by group
        _ = l * l * g := by rw [h1]
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl2
  have hcomm : ∀ x ∈ P, x * l = l * x := by
    intro x hx
    have h1 : l⁻¹ * x * l = x := (hφl x).symm.trans (hfix x hx)
    rw [hlinv] at h1
    calc x * l = l * (l * x * l) := by
          calc x * l = (l * l) * x * l := by rw [hl2, one_mul]
            _ = l * (l * x * l) := by group
      _ = l * x := by rw [h1]
  have hlC : l ∈ Subgroup.centralizer (P : Set Q) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx
  have hlN : l ∈ Subgroup.normalizer (P' : Set Q) :=
    Subgroup.centralizer_le_normalizer _ hlC
  have hl2p : IsPGroup 2 ↥(Subgroup.zpowers l) := by
    have hord : orderOf l ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hl2])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hzN : Subgroup.zpowers l ≤ Subgroup.normalizer (P' : Set Q) :=
    Subgroup.zpowers_le.mpr hlN
  have h1 := hl2p.inf_normalizer_sylow P'
  rw [inf_eq_left.mpr hzN] at h1
  have hlP : l ∈ P := by
    have hmem : l ∈ Subgroup.zpowers l := Subgroup.mem_zpowers l
    rw [h1] at hmem
    exact hmem.2
  refine ⟨l⁻¹, ⟨P.inv_mem hlP, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩, fun q => ?_⟩
  · rw [hlinv]
    exact hcomm x hx
  · rw [hφl q, inv_inv]

theorem input15120AutFixSimple_of_inner (hS : SporadicAutInner) (hE : EvenLieAutInner)
    (hZ : ∀ (Q : Type) [Group Q] [Finite Q], SimpleTypeCD15120 Q → Subgroup.center Q = ⊥) :
    Input15120AutFixSimple := by
  intro Q _ _ P hP2 hPi hT
  refine autFixSimple_of_inner hP2 hPi (hZ Q hT) ?_
  intro β hβ hP
  rcases hT with (h | h | h) | (h | h | h | h | h | h | h | h | h)
  · exact oddAutInner_psu3 (p := 3) (by norm_num) (by norm_num) h β hβ hP
  · exact hE Q (Or.inl (Or.inr h)) β hβ hP
  · exact hE Q (Or.inl (Or.inl ⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨le_rfl, h⟩)))))⟩)) β hβ hP
  · exact hS .M11 (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .M12 (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .M22 (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .M23 (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .M24 (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .J2 (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .HS (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .He (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP
  · exact hS .Ru (by unfold IsSQTKSporadicName; decide) (by decide) Q h β hβ hP

theorem center_eq_bot_of_card_simple {Q : Type} [Group Q] (hs : IsSimpleGroup Q) {N : ℕ}
    (hN : Nat.card Q = N) (h2 : 2 ∣ N) (h3 : 2 < N) : Subgroup.center Q = ⊥ := by
  obtain ⟨a, b, hab⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.exists_noncomm_of_simple_card hs hN h2 h3
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem center_eq_bot_of_simpleTypeCD
    (hZ : Input15122ZPUniqueInv) {Q : Type} [Group Q] [Finite Q]
    (h : SimpleTypeCD15120 Q) : Subgroup.center Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hP2 : IsPGroup 2 ↥(P : Subgroup Q) := P.isPGroup'
  have hPi : ¬ 2 ∣ (P : Subgroup Q).index := P.not_dvd_index
  have six : SporadicSix Q → Subgroup.center Q = ⊥ := fun h6 =>
    (hZ Q (P : Subgroup Q) hP2 hPi (Or.inr h6)).1
  rcases h with h | h
  · exact (hZ Q (P : Subgroup Q) hP2 hPi (Or.inl h)).1
  · rcases h with h | h | h | h | h | h | h | h | h
    ·
      obtain ⟨e⟩ := h
      have hsim : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
        CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
      have hs : IsSimpleGroup Q := e.isSimpleGroup
      refine center_eq_bot_of_card_simple hs (N := 7920) ?_ (by norm_num) (by norm_num)
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M11
    · exact six (Or.inr (Or.inr (Or.inl h)))
    · exact six (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact six (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact six (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact six (Or.inl h)
    ·
      obtain ⟨e⟩ := h
      have hsim : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
        CFSG.Sporadic.HS.isSimpleGroup_HS
      have hs : IsSimpleGroup Q := e.isSimpleGroup
      refine center_eq_bot_of_card_simple hs (N := 44352000) ?_ (by norm_num) (by norm_num)
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    · exact six (Or.inr (Or.inl h))
    ·
      obtain ⟨e⟩ := h
      have hsim : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
        CFSG.Sporadic.Ru.isSimpleGroup_Ru
      have hs : IsSimpleGroup Q := e.isSimpleGroup
      refine center_eq_bot_of_card_simple hs (N := 145926144000) ?_ (by norm_num) (by norm_num)
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru

end CFSG.Quasithin
