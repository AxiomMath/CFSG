module

public import CFSG.Sporadic.HNOddCore.FusA
public import CFSG.Sporadic.HNOddCore.SixA
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HN.Local
open Equiv Equiv.Perm

abbrev t1V : RV := ⟨cR, cR_mem_RV⟩

abbrev t2V :
    RV := ⟨jR t2J, (jR_mem_RV_iff t2J).2 t2H.2⟩

abbrev t4V :
    RV := ⟨jR t4J, (jR_mem_RV_iff t4J).2 t4H.2⟩

abbrev t6V :
    RV := ⟨jR aJ, (jR_mem_RV_iff aJ).2 aJ_mem_HJ⟩

theorem thetaR_t1V :
    (thetaR t1V).cycleType = Multiset.replicate 1 2 := by
  rw [thetaR_cR]; exact swap01_type

theorem thetaR_t2V :
    (thetaR t2V).cycleType = Multiset.replicate 2 2 := by
  rw [(thetaR_jR t2H.2).trans thetaJ_t2H]; exact sig2_type

theorem thetaR_t4V :
    (thetaR t4V).cycleType = Multiset.replicate 4 2 := by
  rw [(thetaR_jR t4H.2).trans thetaJ_t4H]; exact sig4_type

theorem thetaR_t6V :
    (thetaR t6V).cycleType = Multiset.replicate 6 2 := by
  rw [(thetaR_jR aJ_mem_HJ).trans thetaJ_aJ]; exact sig6_type

theorem sq_of_thetaR
    {r : RV} {k : ℕ} (h : (thetaR r).cycleType = Multiset.replicate k 2) :
    (r : RH) ^ 2 = 1 := by
  have e : thetaR (r ^ 2) = 1 := by rw [map_pow]; exact sq_eq_one_of_cycleType_replicate h
  rw [← map_one thetaR] at e
  rw [← Subgroup.coe_pow, thetaR.injective e, Subgroup.coe_one]

theorem ne_one_of_thetaR
    {r : RV} {k : ℕ} (hk : k ≠ 0)
    (h : (thetaR r).cycleType = Multiset.replicate k 2) : (r : RH) ≠ 1 := by
  intro e
  have e' : r = 1 := Subtype.ext e
  rw [e', map_one, Equiv.Perm.cycleType_one] at h
  have := congrArg Multiset.card h
  rw [Multiset.card_replicate, Multiset.card_zero] at this
  exact hk this.symm

theorem card_fix_of_isConj
    {a b : RH} (h : IsConj a b) :
    Nat.card {x : X // a • x = x} = Nat.card {x : X // b • x = x} :=
  card_fixed_of_isConj (X := X) h

theorem not_isConj_t2_t4 :
    ¬ IsConj (jR t2J) (jR t4J) := fun h => by
  have := card_fix_of_isConj h
  rw [card_fix_t2, card_fix_t4] at this
  exact absurd this (by norm_num)

theorem not_isConj_t6_t4 :
    ¬ IsConj (jR aJ) (jR t4J) := fun h => by
  have := card_fix_of_isConj h
  rw [card_fix_t6, card_fix_t4] at this
  exact absurd this (by norm_num)

theorem not_isConj_c_jR
    (g : JH) : ¬ IsConj cR (jR g) := fun h =>
  not_isOuter_jR g ((isOuter_of_isConj h).1 isOuter_cR)

theorem HJ_sq
    {h : HJ} (hsq : (h : JH) ^ 2 = 1) : (thetaJ h : Perm (Fin 12)) ^ 2 = 1 := by
  have e : h ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hsq
  rw [← Subgroup.coe_pow, ← map_pow, e, map_one, Subgroup.coe_one]

theorem HJ_ne_one
    {h : HJ} (hne : (h : JH) ≠ 1) : (thetaJ h : Perm (Fin 12)) ≠ 1 := by
  intro e
  apply hne
  have e' : thetaJ h = 1 := Subtype.ext e
  rw [← map_one thetaJ] at e'
  rw [thetaJ.injective e', Subgroup.coe_one]

theorem exists_type_two_conj_aJ :
    ∃ h : HJ, (thetaJ h : Perm (Fin 12)).cycleType = Multiset.replicate 2 2 ∧
      IsConj aJ (h : JH) := by
  by_contra hne
  push Not at hne
  have hle : Nat.card {h : JH // h ∈ HJ ∧ IsConj aJ h} ≤
      (Finset.univ.filter fun σ : Perm (Fin 12) => σ.cycleType = Multiset.replicate 6 2).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun h => ⟨(thetaJ ⟨h.1, h.2.1⟩ : Perm (Fin 12)), ?_⟩) ?_
    · obtain ⟨h, hH, hc⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hsq := HJ_sq (h := ⟨h, hH⟩) (sq_of_isConj hc aJ_sq)
      have hne1 := HJ_ne_one (h := ⟨h, hH⟩) (ne_one_of_isConj hc aJ_ne_one)
      rcases involution_alt_type hsq hne1 (thetaJ ⟨h, hH⟩).2 with h2 | h4 | h6
      · exact absurd hc (hne ⟨h, hH⟩ h2)
      · exfalso
        have hc4 : IsConj (jR h) (jR t4J) :=
          isConj_RV_of_cycleType (r := ⟨jR h, (jR_mem_RV_iff h).2 hH⟩) (s := t4V)
            (by rw [thetaR_t4V, thetaR_jR hH, h4])
        exact not_isConj_t6_t4 ((isConj_jR hc).trans hc4)
      · exact h6
    · rintro ⟨a, ha, hac⟩ ⟨b, hb, hbc⟩ hab
      have e1 := Subtype.ext_iff.1 hab
      dsimp only at e1
      have e2 := thetaJ.injective (Subtype.ext e1)
      have e3 := Subtype.ext_iff.1 e2
      dsimp only at e3
      subst e3
      rfl
  rw [card_T6, card_type_six] at hle
  exact absurd hle (by norm_num)

theorem isConj_t2_aJ :
    IsConj t2J aJ := by
  obtain ⟨h, h2, hc⟩ := exists_type_two_conj_aJ
  have e : (thetaJ t2H : Perm (Fin 12)).cycleType = (thetaJ h : Perm (Fin 12)).cycleType := by
    rw [thetaJ_t2H, sig2_type, h2]
  have ht2 : IsConj t2J (h : JH) := isConj_HJ_of_cycleType
    (by rw [thetaJ_t2H]; exact sq_eq_one_of_cycleType_replicate sig2_type)
    (by rw [thetaJ_t2H]; unfold sig2; decide) e
  exact ht2.trans hc.symm

theorem card_filter_or_le (P Q : Perm (Fin 12) → Prop) [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter fun σ => P σ ∨ Q σ).card ≤
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

theorem exists_odd_type_conj_c
    {k j : ℕ} (hk : k = 3 ∧ j = 5 ∨ k = 5 ∧ j = 3) :
    ∃ r : RV, (thetaR r).cycleType = Multiset.replicate k 2 ∧ IsConj cR (r : RH) := by
  by_contra hne
  push Not at hne
  have hle : Nat.card {h : RH // h ∈ RV ∧ IsConj cR h} ≤
      (Finset.univ.filter fun σ : Perm (Fin 12) => σ.cycleType = Multiset.replicate 1 2 ∨
        σ.cycleType = Multiset.replicate j 2).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun h => ⟨thetaR ⟨h.1, h.2.1⟩, ?_⟩) ?_
    · obtain ⟨h, hV, hc⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hsq : h ^ 2 = 1 := sq_of_isConj hc cR_sq
      have hout : IsOuter h := (isOuter_of_isConj hc).1 isOuter_cR
      have hs := (isOuter_iff_sign ⟨h, hV⟩).1 hout
      rcases involution_odd_type (thetaR_sq (r := ⟨h, hV⟩) hsq) hs with h1 | h3 | h5
      · exact Or.inl h1
      · rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hc (hne ⟨h, hV⟩ h3)
        · exact Or.inr h3
      · rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr h5
        · exact absurd hc (hne ⟨h, hV⟩ h5)
    · rintro ⟨a, ha, hac⟩ ⟨b, hb, hbc⟩ hab
      have e1 := Subtype.ext_iff.1 hab
      dsimp only at e1
      have e2 := thetaR.injective e1
      have e3 := Subtype.ext_iff.1 e2
      dsimp only at e3
      subst e3
      rfl
  have h2 := hle.trans (card_filter_or_le _ _)
  rw [card_T1, card_type_one] at h2
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [card_type_five] at h2
    exact absurd h2 (by norm_num)
  · rw [card_type_three] at h2
    exact absurd h2 (by norm_num)

theorem even_type
    {r : RV} (h2 : (r : RH) ^ 2 = 1) (h1 : (r : RH) ≠ 1) (hr : ¬ IsOuter (r : RH)) :
    (thetaR r).cycleType = Multiset.replicate 2 2 ∨ (thetaR r).cycleType = Multiset.replicate 4 2 ∨
      (thetaR r).cycleType = Multiset.replicate 6 2 := by
  have hs : sign (thetaR r) = 1 := by
    rcases Int.units_eq_one_or (sign (thetaR r)) with h | h
    · exact h
    · exact absurd ((isOuter_iff_sign r).2 h) hr
  exact involution_alt_type (thetaR_sq h2) (thetaR_ne_one h1) (Equiv.Perm.mem_alternatingGroup.2 hs)

theorem conj_c_iff
    {r : RV} (h2 : (r : RH) ^ 2 = 1) :
    IsConj cR (r : RH) ↔ ((thetaR r).cycleType = Multiset.replicate 1 2 ∨
      (thetaR r).cycleType = Multiset.replicate 3 2 ∨
      (thetaR r).cycleType = Multiset.replicate 5 2) := by
  constructor
  · intro hc
    exact involution_odd_type (thetaR_sq h2)
      ((isOuter_iff_sign r).1 ((isOuter_of_isConj hc).1 isOuter_cR))
  · rintro (h | h | h)
    · exact isConj_RV_of_cycleType (r := t1V) (s := r) (by rw [thetaR_t1V, h])
    · obtain ⟨r3, h3, hc⟩ := exists_odd_type_conj_c (k := 3) (j := 5) (Or.inl ⟨rfl, rfl⟩)
      exact hc.trans (isConj_RV_of_cycleType (by rw [h3, h]))
    · obtain ⟨r5, h5, hc⟩ := exists_odd_type_conj_c (k := 5) (j := 3) (Or.inr ⟨rfl, rfl⟩)
      exact hc.trans (isConj_RV_of_cycleType (by rw [h5, h]))

theorem conj_t2_iff
    {r : RV} (h2 : (r : RH) ^ 2 = 1) (h1 : (r : RH) ≠ 1) :
    IsConj (jR t2J) (r : RH) ↔ ((thetaR r).cycleType = Multiset.replicate 2 2 ∨
      (thetaR r).cycleType = Multiset.replicate 6 2) := by
  constructor
  · intro hc
    have hr : ¬ IsOuter (r : RH) := fun h => not_isOuter_jR t2J ((isOuter_of_isConj hc).2 h)
    rcases even_type h2 h1 hr with h | h | h
    · exact Or.inl h
    · exfalso
      exact not_isConj_t2_t4 (hc.trans (isConj_RV_of_cycleType (s := t4V) (by
        rw [thetaR_t4V, h])))
    · exact Or.inr h
  · rintro (h | h)
    · exact isConj_RV_of_cycleType (r := t2V) (s := r) (by rw [thetaR_t2V, h])
    · exact (isConj_jR isConj_t2_aJ).trans
        (isConj_RV_of_cycleType (r := t6V) (s := r) (by rw [thetaR_t6V, h]))

theorem conj_t4_iff
    {r : RV} (h2 : (r : RH) ^ 2 = 1) (h1 : (r : RH) ≠ 1) :
    IsConj (jR t4J) (r : RH) ↔ (thetaR r).cycleType = Multiset.replicate 4 2 := by
  constructor
  · intro hc
    have hr : ¬ IsOuter (r : RH) := fun h => not_isOuter_jR t4J ((isOuter_of_isConj hc).2 h)
    rcases even_type h2 h1 hr with h | h | h
    · exact absurd (((conj_t2_iff h2 h1).2 (Or.inl h)).trans hc.symm) not_isConj_t2_t4
    · exact h
    · exact absurd (((conj_t2_iff h2 h1).2 (Or.inr h)).trans hc.symm) not_isConj_t2_t4
  · intro h
    exact isConj_RV_of_cycleType (r := t4V) (s := r) (by rw [thetaR_t4V, h])

theorem conj_mem_RV_isConj
    {y g : RH} (hg : g * y * g⁻¹ ∈ RV) :
    IsConj ((⟨g * y * g⁻¹, hg⟩ : RV) : RH) y :=
  isConj_iff.2 ⟨g⁻¹, by group⟩

theorem conj_sq
    {y g : RH} (h2 : y ^ 2 = 1) : (g * y * g⁻¹) ^ 2 = 1 := by
  rw [conj_pow, h2, mul_one, mul_inv_cancel]

theorem conj_ne_one
    {y g : RH} (h1 : y ≠ 1) : g * y * g⁻¹ ≠ 1 := by
  intro h
  apply h1
  rw [show y = g⁻¹ * (g * y * g⁻¹) * g by group, h]
  group

theorem involution_cover_R
    {y : RH} (h2 : y ^ 2 = 1) (h1 : y ≠ 1) :
    IsConj cR y ∨ IsConj (jR t2J) y ∨ IsConj (jR t4J) y := by
  obtain ⟨g, hg⟩ := exists_conj_RV h2 h1
  set r : RV := ⟨g * y * g⁻¹, hg⟩ with hr
  have hry : IsConj (r : RH) y := conj_mem_RV_isConj hg
  have hr2 : (r : RH) ^ 2 = 1 := conj_sq h2
  have hr1 : (r : RH) ≠ 1 := conj_ne_one h1
  obtain ⟨k, hk1, hk6, hk⟩ := exists_cycleType_of_sq (thetaR_sq hr2) (thetaR_ne_one hr1)
  interval_cases k
  · exact Or.inl (((conj_c_iff hr2).2 (Or.inl hk)).trans hry)
  · exact Or.inr (Or.inl (((conj_t2_iff hr2 hr1).2 (Or.inl hk)).trans hry))
  · exact Or.inl (((conj_c_iff hr2).2 (Or.inr (Or.inl hk))).trans hry)
  · exact Or.inr (Or.inr (((conj_t4_iff hr2 hr1).2 hk).trans hry))
  · exact Or.inl (((conj_c_iff hr2).2 (Or.inr (Or.inr hk))).trans hry)
  · exact Or.inr (Or.inl (((conj_t2_iff hr2 hr1).2 (Or.inr hk)).trans hry))

theorem exists_outer_comm
    {y : RH} (h2 : y ^ 2 = 1) (h1 : y ≠ 1) :
    ∃ u : RH, IsOuter u ∧ u * y = y * u := by
  obtain ⟨g, hg⟩ := exists_conj_RV h2 h1
  set r : RV := ⟨g * y * g⁻¹, hg⟩ with hr
  have hσ2 := thetaR_sq (r := r) (conj_sq h2)
  have hσ1 := thetaR_ne_one (r := r) (conj_ne_one h1)
  obtain ⟨a, ha⟩ : ∃ a, thetaR r a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  set u' : RV := thetaR.symm (swap a (thetaR r a)) with hu'
  have hout : IsOuter (u' : RH) := by
    rw [isOuter_iff_sign, hu', MulEquiv.apply_symm_apply]
    exact sign_swap (Ne.symm ha)
  have hcomm : u' * r = r * u' := by
    apply thetaR.injective
    rw [map_mul, map_mul, hu', MulEquiv.apply_symm_apply]
    exact (swap_commute_involution hσ2 a).symm
  refine ⟨g⁻¹ * u' * g, ?_, ?_⟩
  · have := (isOuter_conj g⁻¹ (u' : RH)).2 hout
    rwa [inv_inv] at this
  · have e : (u' : RH) * (g * y * g⁻¹) = (g * y * g⁻¹) * u' := by
      have := congrArg Subtype.val hcomm
      rwa [Subgroup.coe_mul, Subgroup.coe_mul] at this
    calc g⁻¹ * u' * g * y = g⁻¹ * ((u' : RH) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * u') * g := by rw [e]
      _ = y * (g⁻¹ * u' * g) := by group

theorem exists_J_conj
    {x y : RH} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) (hc : IsConj x y) :
    ∃ g : JH, jR g * x * (jR g)⁻¹ = y := by
  obtain ⟨r, hr⟩ := isConj_iff.1 hc
  by_cases hout : IsOuter r
  · obtain ⟨u, hu, hux⟩ := exists_outer_comm h2 h1
    obtain ⟨g, hg⟩ := exists_of_not_isOuter (not_isOuter_mul hout hu)
    refine ⟨g, ?_⟩
    rw [← hg, ← hr]
    calc r * u * x * (r * u)⁻¹ = r * (u * x) * u⁻¹ * r⁻¹ := by group
      _ = r * (x * u) * u⁻¹ * r⁻¹ := by rw [hux]
      _ = r * x * r⁻¹ := by group
  · obtain ⟨g, rfl⟩ := exists_of_not_isOuter hout
    exact ⟨g, hr⟩

theorem isConj_J_of_R
    {a b : JH} (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (h : IsConj (jR a) (jR b)) :
    IsConj a b := by
  obtain ⟨g, hg⟩ := exists_J_conj (by rw [← map_pow, ha2, map_one])
    (fun e => ha1 (jR_injective (by rw [e, map_one]))) h
  refine isConj_iff.2 ⟨g, jR_injective ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hg

theorem card_centralizer_of_isConj {G : Type*} [Group G] [Finite G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer {a}) = Nat.card (Subgroup.centralizer {b}) := by
  have ha := card_conj_mul_card_centralizer a
  have hb := card_conj_mul_card_centralizer b
  have e : Nat.card {s : G // IsConj a s} = Nat.card {s : G // IsConj b s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => ⟨fun hs => h.symm.trans hs,
      fun hs => h.trans hs⟩)
  rw [e] at ha
  have : Nonempty {s : G // IsConj b s} := ⟨⟨b, IsConj.refl b⟩⟩
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (ha.trans hb.symm)

theorem card_CJ_t2 :
    Nat.card (Subgroup.centralizer {t2J}) = 177408000 := by
  rw [card_centralizer_of_isConj isConj_t2_aJ, card_CJ_t6]

end CFSG.Sporadic.HNOddCore
