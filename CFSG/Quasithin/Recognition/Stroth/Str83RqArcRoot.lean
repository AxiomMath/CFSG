module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
public import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsMaxArc.inf_Qv_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) :
    pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Qv ε = ⊥ ∧
      pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Qv (ε + n) = ⊥ := by
  obtain ⟨h1, h2⟩ := IsMaxArc.inf_Gv_eq_bot t hfr h
  have hε := t.Qv_le_Gv hfr ε
  have hn := t.Qv_le_Gv hfr (ε + n)
  exact ⟨le_bot_iff.mp ((inf_le_inf_left _ hε.1).trans (le_of_eq h1)),
    le_bot_iff.mp ((inf_le_inf_left _ hn.2).trans (le_of_eq h2))⟩

private theorem IsMaxArc.pCoreOf_le_Gw_left {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (t.Gw ε (ε + n)) ≤ pCoreOf 2 (t.Gw ε (ε + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := IsMaxArc.two_le t hfr h
  exact t.le_pCoreOf_Gw (u := ε) (w := ε + 1) hfr (by omega) (pCoreOf_isPGroup 2 _)
    ((pCoreOf_le 2 _).trans
      (win_mono (a := ε) (b := ε + n) (a' := ε) (b' := ε + 1) le_rfl (by omega)))

private theorem IsMaxArc.pCoreOf_le_Gw_right {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (t.Gw ε (ε + n)) ≤ pCoreOf 2 (t.Gw (ε + n - 1) (ε + n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := IsMaxArc.two_le t hfr h
  exact t.le_pCoreOf_Gw (u := ε + n - 1) (w := ε + n) hfr (by omega)
    (pCoreOf_isPGroup 2 _)
    ((pCoreOf_le 2 _).trans
      (win_mono (a := ε) (b := ε + n) (a' := ε + n - 1) (b' := ε + n) (by omega) le_rfl))

private theorem IsMaxArc.K_le_normalizer_pCoreOf {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (pCoreOf 2 (t.Gw ε (ε + n)) : Set G) :=
  (t.K_le_Gw ε (ε + n)).trans (le_normalizer_pCoreOf 2 _)

private theorem IsMaxArc.K_le_normalizer_omegaOneCenterOf
    {a f : ℕ} {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n))) : Set G) :=
  (h.K_le_normalizer_pCoreOf hfr).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem IsMaxArc.omegaOneCenterOf_le_rootOmega {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n))) ≤ t.rootOmega ε := by
  intro z hz
  have hzQ : z ∈ pCoreOf 2 (t.Gw ε (ε + n)) := A4.omegaOneCenterOf_le _ hz
  have hz2 : z ^ 2 = 1 := A4.sq_eq_one_of_mem_omegaOneCenterOf hz
  rw [t.mem_rootOmega_iff hfr ε]
  exact ⟨h.pCoreOf_le_Gw_left hfr hzQ, by rw [hz2]; exact (t.Qv ε).one_mem⟩

private theorem IsMaxArc.card_eq_relIndex_Qv {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : v = ε ∨ v = ε + n) :
    Nat.card (pCoreOf 2 (t.Gw ε (ε + n))) =
      (t.Qv v).relIndex (pCoreOf 2 (t.Gw ε (ε + n))) := by
  have hbot : pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Qv v = ⊥ := by
    rcases hv with rfl | rfl
    · exact (h.inf_Qv_eq_bot t hfr).1
    · exact (h.inf_Qv_eq_bot t hfr).2
  have h := Subgroup.inf_relIndex_right (t.Qv v) (pCoreOf 2 (t.Gw ε (ε + n)))
  rw [inf_comm, hbot, Subgroup.relIndex_bot_left] at h
  exact h

private theorem IsMaxArc.card_omegaOneCenterOf_left {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    Nat.card (omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n)))) =
      if Even ε then 2 ^ (2 * a + 1) else 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := pCoreOf 2 (t.Gw ε (ε + n)) with hQ
  set W : Subgroup G := omegaOneCenterOf Q with hW
  have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQne : Q ≠ ⊥ := by
    rw [hQ]
    exact h.pCoreOf_ne_bot
  have hWne : W ≠ ⊥ := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hQp hQne
  have hWQ : W ≤ Q := by
    rw [hW]
    exact A4.omegaOneCenterOf_le Q
  have hQR : Q ≤ pCoreOf 2 (t.Gw ε (ε + 1)) := by
    rw [hQ]
    exact h.pCoreOf_le_Gw_left hfr
  have hQv_bot : Q ⊓ t.Qv ε = ⊥ := by
    rw [hQ]
    exact (h.inf_Qv_eq_bot t hfr).1
  have hWroot : W ≤ t.rootOmega ε := by
    rw [hW]
    exact h.omegaOneCenterOf_le_rootOmega hfr
  have hQvroot : t.Qv ε ≤ t.rootOmega ε := t.Qv_le_rootOmega hfr ε
  have hRleGv : pCoreOf 2 (t.Gw ε (ε + 1)) ≤ t.Gv ε :=
    (pCoreOf_le 2 _).trans (win_le_qv (a := ε) (b := ε + 1) (i := ε) le_rfl (by omega))
  have hWnorm : W ≤ normalizer (t.Qv ε : Set G) :=
    (hWQ.trans (hQR.trans hRleGv)).trans (t.Gv_le_normalizer_Qv ε)
  have hWnotle : ¬ W ≤ t.Qv ε := by
    intro hle
    exact hWne (le_bot_iff.mp ((le_inf hWQ hle).trans (le_of_eq hQv_bot)))
  have hKW : t.K ≤ normalizer (W : Set G) := by
    rw [hW]
    exact h.K_le_normalizer_omegaOneCenterOf hfr
  have hKI : t.rootOmega ε ≤ W ⊔ t.Qv ε :=
    t.rootOmega_le_sup hfr ε (hWQ.trans hQR) hKW hWnotle
  have hsup : t.rootOmega ε = W ⊔ t.Qv ε :=
    le_antisymm hKI (sup_le hWroot hQvroot)
  have hinf : W ⊓ t.Qv ε = ⊥ :=
    le_bot_iff.mp ((le_inf (inf_le_left.trans hWQ) inf_le_right).trans (le_of_eq hQv_bot))
  have hrel : (t.Qv ε).relIndex (t.rootOmega ε) = Nat.card W := by
    rw [hsup, C5.relIndex_sup_eq_of_le_normalizer hWnorm]
    have h := Subgroup.inf_relIndex_right (t.Qv ε) W
    rw [inf_comm, hinf, Subgroup.relIndex_bot_left] at h
    exact h.symm
  have hroot := t.relIndex_rootOmega hfr ε
  rw [hrel] at hroot
  rwa [hW, hQ] at hroot

private theorem IsMaxArc.card_omegaOneCenterOf_right {a f : ℕ}
    {t : Track L1 L2 S} {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n)
    (hfr : Frame L1 L2 S a f) :
    Nat.card (omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n)))) =
      if Even (ε + n) then 2 ^ (2 * a + 1) else 2 ^ f := by
  obtain ⟨y, -, -, hmap, -, -⟩ := t.exists_reflection (ε + n)
  have hQmap : (pCoreOf 2 (t.Gw ε (ε + n))).map (MulAut.conj y).toMonoidHom =
      pCoreOf 2 (t.Gw (ε + n) (ε + n + n)) := by
    rw [← pCoreOf_map_mulEquiv 2 (MulAut.conj y) (t.Gw ε (ε + n))]
    congr 1
    have h := hmap ε (ε + n)
    rw [show 2 * (ε + n) - (ε + n) = ε + n by ring,
      show 2 * (ε + n) - ε = ε + n + n by ring] at h
    exact h
  have hcard : Nat.card (omegaOneCenterOf (pCoreOf 2 (t.Gw (ε + n) (ε + n + n)))) =
      Nat.card (omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n)))) := by
    conv_lhs => rw [← hQmap]
    rw [← CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv,
      Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hleft := IsMaxArc.card_omegaOneCenterOf_left (IsMaxArc.reflect t h (ε + n)) hfr
  rw [show 2 * (ε + n) - ε - n = ε + n by ring] at hleft
  rw [hcard] at hleft
  exact hleft

theorem IsMaxArc.card_omegaOneCenterOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) {e : ℤ}
    (he : e = ε ∨ e = ε + n) :
    Nat.card (omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n)))) =
      if Even e then 2 ^ (2 * a + 1) else 2 ^ f := by
  rcases he with rfl | rfl
  · exact h.card_omegaOneCenterOf_left hfr
  · exact h.card_omegaOneCenterOf_right hfr

theorem IsMaxArc.card_pCoreOf_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) {e : ℤ}
    (he : e = ε ∨ e = ε + n) :
    Nat.card (pCoreOf 2 (t.Gw ε (ε + n))) ≤ if Even e then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases he with he | he
  · subst e
    rw [h.card_eq_relIndex_Qv hfr (v := ε) (Or.inl rfl)]
    exact t.relIndex_Qv_le hfr ε (pCoreOf_isPGroup 2 _)
      (Or.inr ((h.pCoreOf_le_Gw_left hfr).trans (pCoreOf_le 2 _)))
  · subst e
    rw [h.card_eq_relIndex_Qv hfr (v := ε + n) (Or.inr rfl)]
    exact t.relIndex_Qv_le hfr (ε + n) (pCoreOf_isPGroup 2 _)
      (Or.inl ((h.pCoreOf_le_Gw_right hfr).trans (pCoreOf_le 2 _)))

theorem IsMaxArc.mem_omegaOneCenterOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) {x : G}
    (hx : x ∈ pCoreOf 2 (t.Gw ε (ε + n))) (hx2 : x ^ 2 = 1) :
    x ∈ omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQR : pCoreOf 2 (t.Gw ε (ε + n)) ≤ pCoreOf 2 (t.Gw ε (ε + 1)) :=
    h.pCoreOf_le_Gw_left hfr
  have hxroot : x ∈ t.rootOmega ε := by
    rw [t.mem_rootOmega_iff hfr ε]
    exact ⟨hQR hx, by rw [hx2]; exact (t.Qv ε).one_mem⟩
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hx, ?_⟩, hx2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyR : y ∈ pCoreOf 2 (t.Gw ε (ε + 1)) := hQR hy
  have hcommQ : ⁅x, y⁆ ∈ pCoreOf 2 (t.Gw ε (ε + n)) :=
    Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hx hy)
  have hcommQv : ⁅x, y⁆ ∈ t.Qv ε :=
    t.commutator_rootOmega_le hfr ε (Subgroup.commutator_mem_commutator hxroot hyR)
  have hbot : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
    rw [← (h.inf_Qv_eq_bot t hfr).1]
    exact ⟨hcommQ, hcommQv⟩
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hbot
  exact hbot.symm

theorem IsMaxArc.omegaOneCenterOf_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) {X : Subgroup G}
    (hXQ : X ≤ pCoreOf 2 (t.Gw ε (ε + n))) (hX : X ≠ ⊥) (hXK : t.K ≤ normalizer (X : Set G)) :
    omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n))) ≤ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := pCoreOf 2 (t.Gw ε (ε + n)) with hQ
  set W : Subgroup G := omegaOneCenterOf Q with hW
  have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQR : Q ≤ pCoreOf 2 (t.Gw ε (ε + 1)) := by
    rw [hQ]
    exact h.pCoreOf_le_Gw_left hfr
  have hQv_bot : Q ⊓ t.Qv ε = ⊥ := by
    rw [hQ]
    exact (h.inf_Qv_eq_bot t hfr).1
  have hWQ : W ≤ Q := by
    rw [hW]
    exact A4.omegaOneCenterOf_le Q
  have hXp : IsPGroup 2 X := hQp.to_le hXQ
  have hXnt : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX
  obtain ⟨k, hk⟩ := hXp.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro hk0
    have h1 : 1 < 2 ^ k := by
      rw [← hk]
      exact Finite.one_lt_card
    rw [hk0, pow_zero] at h1
    omega
  have hdvd : 2 ∣ Nat.card X := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxG : orderOf (x : G) = 2 := by
    rw [← Subgroup.orderOf_mk (x : G) x.2]
    exact hx
  have hxG2 : (x : G) ^ 2 = 1 := by
    rw [← hxG]
    exact pow_orderOf_eq_one _
  have hxW : (x : G) ∈ W := by
    rw [hW]
    exact IsMaxArc.mem_omegaOneCenterOf t hfr h (hXQ x.2) hxG2
  set X' : Subgroup G := X ⊓ W with hX'
  have hxX' : (x : G) ∈ X' := by
    rw [hX']
    exact ⟨x.2, hxW⟩
  have hX'ne : X' ≠ ⊥ := by
    intro hbot
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hxX'
    rw [Subgroup.mem_bot] at hxbot
    have hx_eq : x = 1 := Subtype.ext hxbot
    rw [hx_eq, orderOf_one] at hx
    omega
  have hX'Q : X' ≤ Q := by
    rw [hX']
    exact inf_le_left.trans hXQ
  have hX'R : X' ≤ pCoreOf 2 (t.Gw ε (ε + 1)) := hX'Q.trans hQR
  have hX'K : t.K ≤ normalizer (X' : Set G) := by
    rw [hX']
    exact (le_inf hXK (h.K_le_normalizer_omegaOneCenterOf hfr)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hX'Qv : ¬ X' ≤ t.Qv ε := by
    intro hle
    exact hX'ne (le_bot_iff.mp ((le_inf hX'Q hle).trans (le_of_eq hQv_bot)))
  have hKI : t.rootOmega ε ≤ X' ⊔ t.Qv ε :=
    t.rootOmega_le_sup hfr ε hX'R hX'K hX'Qv
  have hRleGv : pCoreOf 2 (t.Gw ε (ε + 1)) ≤ t.Gv ε :=
    (pCoreOf_le 2 _).trans (win_le_qv (a := ε) (b := ε + 1) (i := ε) le_rfl (by omega))
  have hX'norm : X' ≤ normalizer (t.Qv ε : Set G) :=
    (hX'R.trans hRleGv).trans (t.Gv_le_normalizer_Qv ε)
  intro z hz
  have hzroot : z ∈ t.rootOmega ε := by
    rw [hW] at hz
    exact h.omegaOneCenterOf_le_rootOmega hfr hz
  have hzsup : z ∈ X' ⊔ t.Qv ε := hKI hzroot
  change z ∈ ((X' ⊔ t.Qv ε : Subgroup G) : Set G) at hzsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X' (t.Qv ε) hX'norm] at hzsup
  obtain ⟨x', hx', q, hq, hx'q⟩ := hzsup
  have hx'X : x' ∈ X := by
    rw [hX'] at hx'
    exact hx'.1
  have hqQ : q ∈ Q := by
    have hq_eq : q = x'⁻¹ * z := by
      rw [← hx'q]
      group
    rw [hq_eq]
    exact Q.mul_mem (Q.inv_mem (hX'Q hx')) (hWQ hz)
  have hqbot : q = 1 := by
    have hqbot_mem : q ∈ (⊥ : Subgroup G) := by
      rw [← hQv_bot]
      exact ⟨hqQ, hq⟩
    rwa [Subgroup.mem_bot] at hqbot_mem
  have hz_eq : z = x' := by
    rw [← hx'q, hqbot]
    simp
  rw [hz_eq]
  exact hx'X

theorem IsMaxArc.even {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) (hrq : f ≠ 2 * a + 1) : Even n := by
  by_contra hn
  have hodd : Odd n := Nat.not_even_iff_odd.mp hn
  have hoddZ : Odd (n : ℤ) := by
    exact_mod_cast hodd
  have hleft := IsMaxArc.card_omegaOneCenterOf t hfr h (e := ε) (Or.inl rfl)
  have hright := IsMaxArc.card_omegaOneCenterOf t hfr h (e := ε + n) (Or.inr rfl)
  have hqr : 2 ^ (2 * a + 1) = 2 ^ f := by
    by_cases he : Even ε
    · have hne : ¬ Even (ε + n) := fun h' => Int.not_even_iff_odd.mpr (he.add_odd hoddZ) h'
      rw [if_pos he] at hleft
      rw [if_neg hne] at hright
      exact hleft.symm.trans hright
    · have hoddε : Odd ε := Int.not_even_iff_odd.mp he
      have hne : Even (ε + n) := hoddε.add_odd hoddZ
      rw [if_neg he] at hleft
      rw [if_pos hne] at hright
      exact hright.symm.trans hleft
  exact hrq (Nat.pow_right_injective le_rfl hqr).symm

end Track

end CFSG.Quasithin.Stroth.Rq

end
