module

public import CFSG.RankThree.PartTwo.KFacts.KP4Signal
public import CFSG.RankThree.PartTwo.KFacts.KP4AutCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.RankThree.GroupTheory.SteinbergBYAutCentralizerTheta
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.WittDesign MulAction
open CFSG.RankThree.Asc83Table.M22 (x y X Y E)
open CFSG.RankThree.Asc83Table (Automizer)
open CFSG.Sporadic.Schreier (m22Delta m22_delta_normalizes m22_delta_sq m22_center_eq_bot'
  m22_delta_outer m22_mulAut_card exists_eq_conj_of_outer conj_injective_of_center)
open CFSG.RankThree.GroupTheory.SteinbergBY (mulAut_conj_apply_eq mem_normalizer_of_map_conj_eq)

noncomputable abbrev Inn22 : Subgroup (MulAut G22) := (MulAut.conj : G22 →* MulAut G22).range

instance : Finite (MulAut G22) :=
  Finite.of_injective (fun α : MulAut G22 => (α : G22 → G22)) DFunLike.coe_injective

theorem conj_injective_G22 : Function.Injective (MulAut.conj : G22 →* MulAut G22) :=
  conj_injective_of_center NativeSporadic.M22 m22_center_eq_bot'

theorem index_inner_le : (Inn22).index ≤ 2 := by
  have h1 := (Inn22).card_mul_index
  have h2 : Nat.card (Inn22) = Nat.card G22 :=
    (Nat.card_congr (MonoidHom.ofInjective conj_injective_G22).toEquiv).symm
  have h3 : Nat.card (MulAut G22) ≤ 2 * Nat.card G22 := m22_mulAut_card
  rw [h2] at h1
  have hpos : 0 < Nat.card G22 := Nat.card_pos
  by_contra h
  push Not at h
  have : Nat.card G22 * 3 ≤ Nat.card G22 * (Inn22).index := Nat.mul_le_mul_left _ h
  omega

theorem sq_mem_inner (α : MulAut G22) : α ^ 2 ∈ Inn22 := by
  have hne : (Inn22).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h := index_inner_le
  rcases (show (Inn22).index = 1 ∨ (Inn22).index = 2 by omega) with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact mem_top _
  · exact Subgroup.sq_mem_of_index_two h2 α

theorem pow_four_mem_centralizer {g : G22} (hg : g ∈ normalizer (P0 : Set G22)) :
    g ^ 4 ∈ centralizer (P0 : Set G22) := by
  obtain ⟨e⟩ := CFSG.RankThree.Asc83Table.M22.automizer_P0
  have hexp : Monoid.exponent (QuaternionGroup 2) = 4 := by
    rw [QuaternionGroup.exponent]
    decide
  have h4 : ((⟨g, hg⟩ : normalizer (P0 : Set G22)) : Automizer P0) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one, ← hexp]
    exact Monoid.pow_exponent_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at h4
  exact h4

theorem map_mul_aut (α β : MulAut G22) (H : Subgroup G22) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem aut_pow_eight {α : MulAut G22} (hα : P0.map α.toMonoidHom = P0) {b : G22}
    (hb : b ∈ P0) : (α ^ 8) b = b := by
  obtain ⟨g, hg⟩ := sq_mem_inner α
  have hα2 : P0.map (α ^ 2).toMonoidHom = P0 := by rw [sq, map_mul_aut, hα, hα]
  have hgN : g ∈ normalizer (P0 : Set G22) := by
    apply mem_normalizer_of_map_conj_eq
    rw [hg]
    exact hα2
  have h4 := pow_four_mem_centralizer hgN
  have h8 : α ^ 8 = MulAut.conj (g ^ 4) := by
    rw [map_pow, hg, ← pow_mul]
  rw [h8, MulAut.conj_apply, (mem_centralizer_iff.1 h4 b hb).symm, mul_inv_cancel_right]

theorem centralizer_P0 : centralizer (P0 : Set G22) = P0 := by
  set D := centralizer (P0 : Set G22)
  have hPD : P0 ≤ D := fun g hg => mem_centralizer_iff.2 fun h hh => P0_comm hh hg
  have hD0 : D ≤ centralizer ({lineE 0} : Set G22) := fun g hg =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hg _ (lineE_mem_P0 0)).symm
  have hD1 : D ≤ centralizer ({lineE 1} : Set G22) := fun g hg =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hg _ (lineE_mem_P0 1)).symm
  have hno2 : ¬ 2 ∣ Nat.card D := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2
    have hg' : orderOf (g : G22) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
    have hgV0 : (g : G22) ∈ V 0 :=
      mem_V_of_pow_four (hD0 g.2) (orderOf_dvd_iff_pow_eq_one.1 (by rw [hg']; norm_num))
    have hgV1 : (g : G22) ∈ V 1 := by
      have hmem : (g : G22) ∈ R 0 ⊓ centralizer ({lineE (hexSnd 0)} : Set G22) :=
        ⟨(show V 0 ≤ R 0 from le_sup_left) hgV0, hD1 g.2⟩
      rw [R_inf_centralizer_snd] at hmem
      exact hmem
    have hbot : (g : G22) ∈ V (hexFst 0) ⊓ V (hexSnd 0) := ⟨hgV0, hgV1⟩
    rw [V_inf_V, mem_bot] at hbot
    have : g = 1 := Subtype.ext hbot
    rw [this, orderOf_one] at hg
    norm_num at hg
  have hdvd36 : Nat.card D ∣ 36 := by
    rw [← card_centralizer_line 0]
    exact Subgroup.card_dvd_of_le hD0
  have h9 : 9 ∣ Nat.card D := card_P0 ▸ Subgroup.card_dvd_of_le hPD
  have hpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨m, hm⟩ := h9
  have hm4 : m ∣ 4 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by rw [← hm]; exact hdvd36)
  have hm4' : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
  have hD9 : Nat.card D = 9 := by
    rw [hm] at hpos hno2 ⊢
    interval_cases m <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hPD (by rw [hD9, card_P0])).symm

theorem ofTab_lineTab_zero : ∀ p, ofTab (lineTab 0) p = (X : Perm (Fin 22)) p := by
  decide +kernel

theorem ofTab_lineTab_one : ∀ p, ofTab (lineTab 1) p = (Y : Perm (Fin 22)) p := by
  decide +kernel

theorem aut_fix_eq_conj {α : MulAut G22} (hα : ∀ b ∈ P0, α b = b) :
    ∃ c ∈ P0, α = MulAut.conj c := by
  by_cases hin : α ∈ Inn22
  · obtain ⟨g, rfl⟩ := hin
    refine ⟨g, ?_, rfl⟩
    rw [← centralizer_P0, mem_centralizer_iff]
    intro h hh
    have := hα h hh
    rw [MulAut.conj_apply] at this
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  · exfalso
    obtain ⟨g, hgM, hgα⟩ := exists_eq_conj_of_outer NativeSporadic.M22 m22Delta
      m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hin
    have hX := hgα X
    have hY := hgα Y
    rw [hα X X_mem_P0] at hX
    rw [hα Y Y_mem_P0] at hY
    have hcount := kp4_outer_count
    rw [← card_m22_subtype] at hcount
    have hmem : (fun f : Fin 22 → Fin 22 => (∀ p, f (ofTab deltaTab (ofTab (lineTab 0) p)) =
        ofTab (lineTab 0) (f (ofTab deltaTab p))) ∧
        ∀ p, f (ofTab deltaTab (ofTab (lineTab 1) p)) =
          ofTab (lineTab 1) (f (ofTab deltaTab p))) ⇑g := by
      simp only [ofTab_deltaTab, ofTab_lineTab_zero, ofTab_lineTab_one]
      have ex : ∀ (u : G22), (u : Perm (Fin 22)) = g * m22Delta * u * (g * m22Delta)⁻¹ →
          ∀ p, g (m22Delta ((u : Perm (Fin 22)) p)) = (u : Perm (Fin 22)) (g (m22Delta p)) := by
        intro u hu p
        have h2 : (u : Perm (Fin 22)) * (g * m22Delta) = g * m22Delta * u := by
          nth_rewrite 1 [hu]
          group
        exact (congrArg (fun σ : Perm (Fin 22) => σ p) h2).symm
      exact ⟨ex X hX, ex Y hY⟩
    exact (Nat.card_pos_iff.2 ⟨⟨⟨⟨g, hgM⟩, hmem⟩⟩, inferInstance⟩).ne' hcount

section Invariant

variable {Q : Subgroup (MulAut G22)}
  (hP : P0.map (MulAut.conj : G22 →* MulAut G22) ≤ normalizer (Q : Set (MulAut G22)))
include hP

@[expose] noncomputable def actHom : P0 →* normalizer (Q : Set (MulAut G22)) :=
  ((MulAut.conj : G22 →* MulAut G22).comp P0.subtype).codRestrict _ fun b =>
    hP (mem_map_of_mem _ b.2)

theorem aut_threePrime_le_inner (h3 : ¬ 3 ∣ Nat.card Q) : Q ≤ Inn22 := by
  classical
  by_contra hQ
  let _ : MulAction P0 Q := MulAction.compHom Q (actHom hP)
  set Q₀ := (Inn22).subgroupOf Q
  have hrel : (Inn22).relIndex Q = 2 := by
    have hdvd : (Inn22).relIndex Q ∣ (Inn22).index := by
      have : (Inn22).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal G22
      exact Subgroup.relIndex_dvd_index_of_normal Inn22 Q
    have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := Inn22))) hdvd).trans index_inner_le
    have hne1 : (Inn22).relIndex Q ≠ 1 := by
      intro h1
      exact hQ (Subgroup.relIndex_eq_one.1 h1)
    have hne0 : (Inn22).relIndex Q ≠ 0 :=
      (Subgroup.index_ne_zero_of_finite : ((Inn22).subgroupOf Q).index ≠ 0)
    omega
  have hcardQ : Nat.card Q = 2 * Nat.card Q₀ := by
    have := Q₀.card_mul_index
    rw [show Q₀.index = 2 from hrel] at this
    omega
  let S : SubMulAction P0 Q :=
    { carrier := {q | q ∉ Q₀}
      smul_mem' := by
        intro b q hq hbq
        apply hq
        rw [mem_subgroupOf] at hbq ⊢
        have hb : MulAut.conj (b : G22) ∈ Inn22 := ⟨b, rfl⟩
        have heq : ((b • q : Q) : MulAut G22) =
            MulAut.conj (b : G22) * q * (MulAut.conj (b : G22))⁻¹ := rfl
        rw [heq] at hbq
        have := (Inn22).mul_mem ((Inn22).mul_mem ((Inn22).inv_mem hb) hbq) hb
        rwa [show (MulAut.conj (b : G22))⁻¹ * (MulAut.conj (b : G22) * q *
          (MulAut.conj (b : G22))⁻¹) * MulAut.conj (b : G22) = (q : MulAut G22) by group]
          at this }
  have hcardS : Nat.card S = Nat.card Q₀ := by
    have h1 : Nat.card S = Nat.card {q : Q // q ∉ Q₀} := rfl
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card]
    have : Nat.card {q : Q // q ∈ Q₀} = Nat.card Q₀ := rfl
    rw [this, hcardQ]
    omega
  have hS3 : ¬ 3 ∣ Nat.card S := by
    rw [hcardS]
    intro h
    exact h3 (h.trans ⟨2, by rw [hcardQ]; ring⟩)
  have hP3 : IsPGroup 3 P0 := IsPGroup.of_card (n := 2) (by rw [card_P0]; norm_num)
  obtain ⟨s, hs⟩ := hP3.nonempty_fixed_point_of_prime_not_dvd_card S hS3
  have hsQ : ((s : Q) : MulAut G22) ∉ Inn22 := s.2
  apply hsQ
  have hfix : ∀ b ∈ P0, ((s : Q) : MulAut G22) b = b := by
    intro b hb
    have h := hs ⟨b, hb⟩
    have h' : ((⟨b, hb⟩ : P0) • (s : Q) : Q) = s := congrArg Subtype.val h
    have h'' : MulAut.conj b * ((s : Q) : MulAut G22) * (MulAut.conj b)⁻¹ =
        ((s : Q) : MulAut G22) := congrArg Subtype.val h'
    have hc : MulAut.conj (((s : Q) : MulAut G22) b) = MulAut.conj b := by
      rw [mulAut_conj_apply_eq]
      calc ((s : Q) : MulAut G22) * MulAut.conj b * ((s : Q) : MulAut G22)⁻¹ =
          (MulAut.conj b * ((s : Q) : MulAut G22) * (MulAut.conj b)⁻¹) * MulAut.conj b *
            ((s : Q) : MulAut G22)⁻¹ := by rw [h'']
        _ = MulAut.conj b := by group
    exact conj_injective_G22 hc
  obtain ⟨c, -, hc⟩ := aut_fix_eq_conj hfix
  exact ⟨c, hc.symm⟩

end Invariant

end CFSG.RankThree.PartTwo.KFacts.KP4
