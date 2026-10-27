module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Model
public import CFSG.RankThree.PartTwo.Sec8.Hering418V2
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Type418
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)


theorem card_center_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) := by
  rw [← map_center_eq e]
  exact (Subgroup.card_map_of_injective e.injective).symm

theorem odd_of_three_dvd_two_pow {n : ℕ} (h : 3 ∣ 2 ^ (3 * n) + 1) : Odd n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exfalso
    have hq : 2 ^ (3 * (2 * k)) % 3 = 1 := by
      rw [show 3 * (2 * k) = 6 * k by ring, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · exact ⟨k, rfl⟩

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem Cfg.e27_of_isType418 (c : Cfg L K a b) {n : ℕ} (hn : 1 ≤ n)
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (htype : IsType418 (K ⧸ aschbacherSolvableCore 3 K) n)
    (hKa : KFacts.InducesStdKind K a .field) : c.E27 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥
  ·
    have hT := type418Arith_of hn hq htype
    have h3K : 3 ∣ Nat.card K := by
      have h1 : 3 ∣ Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸
          Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) :=
        (dvd_pow_self 3 (by norm_num : 2 ≠ 0)).trans hT.2.1
      have h2 := (Subgroup.card_quotient_dvd_card (Subgroup.center
        (K ⧸ aschbacherSolvableCore 3 K)))
      have h3 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 K)
      exact h1.trans (h2.trans h3)
    exact c.e27_of_center_eq_bot hZ h3K
  ·
    rcases htype with hSU | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · obtain ⟨F, hFf, hFfin, hF, ⟨ψ⟩⟩ := hSU
      have hcf := center_su3_facts (K := F) hn hF
      have hcardZ : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) ≤ 3 := by
        rw [card_center_congr ψ]
        exact hcf.1
      have h3q : 3 ∣ 2 ^ (3 * n) + 1 := by
        apply hcf.2
        intro hbot
        apply hZ
        rw [← Subgroup.card_eq_one, card_center_congr ψ, Subgroup.card_eq_one.mpr hbot]
      have hodd : Odd n := odd_of_three_dvd_two_pow h3q
      have hSU' : IsoSUThree (K ⧸ aschbacherSolvableCore 3 K) (2 ^ (3 * n)) :=
        ⟨F, hFf, hFfin, hF, ⟨ψ⟩⟩
      obtain ⟨F', hF'f, hF'fin, hF', ⟨ψ'⟩⟩ :=
        KFacts.isoSUThree_barCentralizer_of_inducesStdKind hodd hSU' c.ha3 hKa
      have h3n : 3 ∣ 2 ^ n + 1 := by
        have := Sec4.HeringUnitary.two_pow_mod_three_of_odd hodd
        omega
      obtain ⟨Esu, hEsu, hEsu9⟩ := exists_elemAbelian_nine_statedSU hF' h3n
      replace hEsu : IsElemAbelian 3 Esu := hEsu
      set C := Sec8.barCentralizer (Subgroup.zpowers a) K with hC
      set Ē : Subgroup (K ⧸ aschbacherSolvableCore 3 K) :=
        (Esu.map ψ'.symm.toMonoidHom).map C.subtype with hĒ
      have hĒab : IsElemAbelian 3 Ē :=
        ((hEsu.map ψ'.symm.toMonoidHom).map C.subtype)
      have hĒcard : Nat.card Ē = 3 ^ 2 := by
        rw [hĒ, Subgroup.card_map_of_injective C.subtype_injective,
          Subgroup.card_map_of_injective ψ'.symm.injective, hEsu9]
        norm_num
      have hfix : ∀ y ∈ Ē, Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y = y := by
        rintro y ⟨y', -, rfl⟩
        exact (KFacts.mem_barCentralizer_zpowers_iff c.haK _).mp y'.2
      obtain ⟨E, hE, hEc, hEa, -⟩ := exists_elemAbelian_lift c.haK c.ha3 hĒab hĒcard hfix
      exact c.e27_of_elemAbelian_nine hcardZ hE hEc hEa
    · exact (hZ (Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inl rfl) hn) hq
        φ)).elim
    · exact (hZ (Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inr rfl) hn) hq
        φ)).elim

theorem Cfg.false_of_bound (c : Cfg L K a b) {n : ℕ} (hn : 1 ≤ n)
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (htype : IsType418 (K ⧸ aschbacherSolvableCore 3 K) n)
    (hKa : KFacts.InducesStdKind K a .field)
    {N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))} (hinn : innBar L ≤ N)
    (hα : c.alpha ∈ N) (hβ : c.beta ∈ N)
    (hN : ∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsElemAbelian 3 F →
      F ≤ N → Nat.card F ≤ 9) : False :=
  c.false_of_e27 (c.e27_of_isType418 hn hq htype hKa) hinn hα hβ hN

theorem kF418ModelOn_of_bound {P : ∀ (X : Type) [Group X], Prop}
    (hbound : ∀ (X : Type) [Group X] [Finite X], P X →
      ∃ N : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ N ∧
        (∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ N) ∧
        ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9) :
    KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  obtain ⟨N, hinn, h3, hN⟩ := hbound _ hl
  exact c.false_of_bound hn hKq htype hKa hinn (h3 _ c.alpha_pow_three) (h3 _ c.beta_pow_three) hN

end CFSG.RankThree.PartTwo.Sec8.Hering418
