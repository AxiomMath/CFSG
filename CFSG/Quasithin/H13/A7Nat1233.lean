module

public import CFSG.Quasithin.H13.A7NatMain
public import CFSG.Quasithin.H13.A7NatInputs
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Timmesfeld.Final.PSU33
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

theorem units_zmod_two_eq_one : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by
  decide

theorem nat_card_SL_zmod_two (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  classical
  have h : Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
    refine Nat.card_congr (Equiv.ofBijective Matrix.SpecialLinearGroup.toGL
      ⟨fun a b hab => ?_, fun g => ?_⟩)
    · apply Subtype.ext
      have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
        (g : Matrix (Fin n) (Fin n) (ZMod 2))) hab
      simpa using this
    · have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact units_zmod_two_eq_one _
      exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  rw [h, Matrix.card_GL_field, ZMod.card]

theorem nat_card_SL_three_zmod_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [nat_card_SL_zmod_two]
  decide

theorem nat_card_SL_four_zmod_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [nat_card_SL_zmod_two]
  decide

theorem nat_card_SL_five_zmod_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [nat_card_SL_zmod_two]
  decide

theorem nat_card_psu331_dvd : Nat.card (CFSG.Open.PSU3 3 1) ∣ 6048 := by
  rw [psu3_three_one_eq_map_gramSU, ← card_gramSU_antidiag]
  exact Subgroup.card_map_dvd _ _

theorem card_eq_of_quot_center_alternating_seven {Q : Type*} [Group Q] [Finite Q]
    (h : Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 7))) :
    Nat.card Q = 2520 * Nat.card (center Q) := by
  obtain ⟨e⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q), Nat.card_congr e.toEquiv,
    nat_card_alternating_seven]

theorem nat_card_alternating_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem eq_seven_of_surjective_alternating {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hQ : Nat.card (L ⧸ CFSG.pCore 2 L) = 2520 * Nat.card (center (L ⧸ CFSG.pCore 2 L)))
    (hodd : Odd (Nat.card (center (L ⧸ CFSG.pCore 2 L)))) {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    {φ : L →* alternatingGroup (Fin n)} (hφs : Function.Surjective φ) : n = 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 :=
    nat_card_alternating_fin n (by omega)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rw [hcard]
    interval_cases n <;> decide
  have hP : (CFSG.pCore 2 L).map φ = ⊥ := by
    have hN : ((CFSG.pCore 2 L).map φ).Normal := (CFSG.pCore_normal).map φ hφs
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hN with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 L).map φ) := CFSG.pCore_isPGroup.map φ
      rw [h] at h2
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 h2)
      rw [Subgroup.card_top] at hk
      rw [hk] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hle : CFSG.pCore 2 L ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact hP
  set φ' := QuotientGroup.lift (CFSG.pCore 2 L) φ hle with hφ'
  have hφ's : Function.Surjective φ' := by
    intro a
    obtain ⟨x, rfl⟩ := hφs a
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hK : φ'.ker ≤ center (L ⧸ CFSG.pCore 2 L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq φ'.normal_ker with h | h
    · exfalso
      have h1 : ∀ a, a = (1 : alternatingGroup (Fin n)) := by
        intro a
        obtain ⟨x, rfl⟩ := hφ's a
        exact (MonoidHom.mem_ker).1 (h ▸ mem_top x)
      have h2 : Nat.card (alternatingGroup (Fin n)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, inferInstance⟩
      rw [h2] at h3
      norm_num at h3
    · exact h
  have hord : Nat.card (L ⧸ CFSG.pCore 2 L) =
      Nat.card (alternatingGroup (Fin n)) * Nat.card φ'.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ'.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).toEquiv]
  obtain ⟨m, hm⟩ : Nat.card φ'.ker ∣ Nat.card (center (L ⧸ CFSG.pCore 2 L)) :=
    Subgroup.card_dvd_of_le hK
  have hkpos : 0 < Nat.card φ'.ker := Nat.card_pos
  have hA : Nat.card (alternatingGroup (Fin n)) = 2520 * m := by
    have h1 : Nat.card (alternatingGroup (Fin n)) * Nat.card φ'.ker =
        (2520 * m) * Nat.card φ'.ker := by
      rw [← hord, hQ, hm]
      ring
    exact Nat.eq_of_mul_eq_mul_right hkpos h1
  have hmodd : Odd m := by
    rw [hm] at hodd
    exact (Nat.odd_mul.1 hodd).2
  rw [hcard] at hA
  obtain ⟨j, hj⟩ := hmodd
  interval_cases n <;> simp [Nat.factorial] at hA <;> omega

section Main

variable {G : Type} [Group G] [Finite G]

theorem A7_natural_or_four (h1222 : Stmt12_2_2) (hI16 : AsI16AltSevenCover) {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))) :
    (∃ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) ∨
    (Nat.card V = 2 ^ 4 ∧ ∃ φ : ↥L →* ↥(alternatingGroup (Fin 7)), Function.Surjective φ ∧
      φ.ker = (centralizer (V : Set G)).subgroupOf L) := by
  classical
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hab, hmod⟩ := hall V hyp.irrPlus
  have hQ := card_eq_of_quot_center_alternating_seven hA7
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hyp.quasisimple
  have hzpos : 0 < Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) := Nat.card_pos
  obtain ⟨k, hk⟩ := hodd
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφs, -⟩, hnat⟩ | hfour | ⟨hlie, -⟩ | ⟨-, -, ⟨e⟩, -⟩
  ·
    exfalso
    have hc := Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl | rfl
    · rw [nat_card_SL_three_zmod_two, hQ] at hc
      omega
    · rw [nat_card_SL_four_zmod_two, hQ] at hc
      omega
    · rw [nat_card_SL_five_zmod_two, hQ] at hc
      omega
  · exfalso
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_SL_three_zmod_two, hQ] at hc
    omega
  · exfalso
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_SL_five_zmod_two, hQ] at hc
    omega
  ·
    have hn7 := eq_seven_of_surjective_alternating hyp.quasisimple hQ ⟨k, hk⟩ hn5 hn8 hφs
    subst hn7
    have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
    have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
      obtain ⟨-, hEA, -⟩ := hred
      intro v hv
      have hv' : (⟨v, le_sup_right (b := T) (a := L) (hVT hv)⟩ : ↥(L ⊔ T)) ∈
          V.subgroupOf (L ⊔ T) := hv
      have h1 := (BlueprintB2.isElementaryAbelian_iff.1 hEA).2 _ hv'
      exact congrArg Subtype.val h1
    have hCV := hI16 G L V hsq hLV hyp.irrPlus.2.2.2.1 hnat
    exact Or.inl (exists_coord_of_alternatingNatural hLV hnat hCV)
  · exact Or.inr hfour
  ·
    exfalso
    obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hlie
    have hc := Nat.card_congr e.toEquiv
    have h5 : 5 ∣ Nat.card (CFSG.Open.PSU3 3 1) := by
      rw [← hc, hQ]
      exact Dvd.dvd.mul_right (by norm_num) _
    have h6 := h5.trans nat_card_psu331_dvd
    norm_num at h6
  ·
    exfalso
    obtain ⟨e₇⟩ := hA7
    have hc := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e₇.toEquiv)
    rw [nat_card_alternating_seven, nat_card_alternating_fin 6 (by norm_num)] at hc
    norm_num [Nat.factorial] at hc

end Main

@[expose] def A7FourExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ¬ (Nat.card V = 2 ^ 4 ∧ ∃ φ : ↥L →* ↥(alternatingGroup (Fin 7)), Function.Surjective φ ∧
      φ.ker = (centralizer (V : Set G)).subgroupOf L)

theorem stmt12_3_3_of_four (h1222 : Stmt12_2_2) (hI16 : AsI16AltSevenCover)
    (hfour : A7FourExcluded) : Stmt12_3_3 := by
  intro G _ _ T L V hyp hA7
  rcases A7_natural_or_four h1222 hI16 hyp hA7 with h | h
  · exact h
  · exact absurd h (hfour G T L V hyp hA7)

end CFSG.Quasithin.H13.A7
