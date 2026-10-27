module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwistFrame
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathFrame
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsuFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamUSylow
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin (StatedGU)
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs (famUProj famU_card_GU famU_card_ker_proj
  famU_two_le)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

variable {L : Type} [Field L] [Finite L] {ℓ f n r : ℕ}

theorem orderOf_neg_natCast_mod_three {q : ℕ} (hq : q % 3 = 1) :
    orderOf (-((q : ℕ) : ZMod 3)) = 2 := by
  have h : ((q : ℕ) : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod, hq]
    norm_num
  rw [h]
  exact orderOf_eq_prime (by decide) (by decide)

private theorem factorization_card_statedGU_of_orderOf {p : ℕ} [Fact p.Prime] (hp1 : Odd p)
    {L : Type} [Field L] [Fintype L] {q n e a r : ℕ} (hq : Fintype.card L = q ^ 2)
    (hpq : ¬ p ∣ q) (hn1 : 1 ≤ n) (he : orderOf (-(q : ZMod p)) = e)
    (ha : padicValInt p ((-(q : ℤ)) ^ e - 1) = a) (hr : n / e = r) :
    (Nat.card (StatedGU n q L)).factorization p = a * r + (Nat.factorial r).factorization p := by
  subst he ha hr
  refine (CFSG.GroupTheory.WeirSylow.factorization_card_statedGU hp1 L hq hpq hn1).trans ?_
  rw [Nat.factorization_def _ (Fact.out : p.Prime)]
  rfl

theorem exists_frame_statedProj_su (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hq : ℓ ^ f % 3 = 1) (hn : n / 2 = r) (hn1 : 1 ≤ n) :
    ∃ (a : ℕ) (μ : ℤ), 1 ≤ a ∧ ¬ (3 : ℤ) ∣ μ - 1 ∧
      Nonempty (TwistFrame (Multiplicative (ZMod (3 ^ a))) r
        (StatedProj (StatedSU n (ℓ ^ f) L)) μ) ∧
      ¬ 3 ^ (a * r + (Nat.factorial r).factorization 3 + 1) ∣
        Nat.card (StatedProj (StatedSU n (ℓ ^ f) L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype L := Fintype.ofFinite L
  have hp1 : Odd 3 := by decide
  have hker := famU_card_ker_proj hℓ hL hn1
  have hGU := famU_card_GU hℓ hL hn1
  have hq2 := famU_two_le hL
  obtain ⟨q, hqdef⟩ : ∃ q, ℓ ^ f = q := ⟨_, rfl⟩
  rw [hqdef] at hker hGU hq2 hq hL ⊢
  have hq' : Fintype.card L = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hL]
  have hpq : ¬ 3 ∣ q := by omega
  have hpq1 : ¬ 3 ∣ q + 1 := by omega
  have he : orderOf (-((q : ℕ) : ZMod 3)) = 2 := orderOf_neg_natCast_mod_three hq
  obtain ⟨a, ha_def⟩ : ∃ a, padicValInt 3 ((-(q : ℤ)) ^ 2 - 1) = a := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [← ha_def]
    have hfac : (-(q : ℤ)) ^ 2 - 1 = ((q : ℤ) - 1) * ((q : ℤ) + 1) := by ring
    have hdvd : (3 : ℤ) ^ 1 ∣ (-(q : ℤ)) ^ 2 - 1 := by
      rw [pow_one, hfac]
      exact Dvd.dvd.mul_right (by omega) _
    have hne : (-(q : ℤ)) ^ 2 - 1 ≠ 0 := by
      have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq2
      intro h0
      nlinarith
    rcases (padicValInt_dvd_iff 1 _).1 hdvd with h0 | h1
    · exact absurd h0 hne
    · exact h1
  obtain ⟨μ, hμ, ⟨F⟩⟩ := nonempty_suFrame (by norm_num : (3 : ℕ) ≠ 2) hq' hpq hpq1 n he ha_def hn
  have hinj : Function.Injective ((famUProj n q L).comp F.T) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : F.T x ∈ (famUProj n q L).ker := hx
    have h1 : F.T x ^ Nat.gcd n (q + 1) = 1 := by
      have h := pow_card_eq_one' (G := (famUProj n q L).ker) (x := ⟨F.T x, hmem⟩)
      rw [hker] at h
      have h' := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have h2 : F.T x ^ 3 ^ a = 1 := by rw [← map_pow, pow_pPow_eq_one_pi x, map_one]
    have hcop : Nat.Coprime (Nat.gcd n (q + 1)) (3 ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (fun h => hpq1 (h.trans (Nat.gcd_dvd_right _ _)))).symm
    have h3 : orderOf (F.T x) ∣ Nat.gcd (Nat.gcd n (q + 1)) (3 ^ a) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hcop.gcd_eq_one] at h3
    exact F.T_injective (by rw [map_one]; exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))
  have hGUfac := factorization_card_statedGU_of_orderOf hp1 hq' hpq hn1 he ha_def hn
  have hdvd : Nat.card (StatedProj (StatedSU n q L)) ∣ Nat.card (StatedGU n q L) := by
    have h1 : Nat.card (StatedProj (StatedSU n q L)) ∣ Nat.card (StatedSU n q L) :=
      ⟨Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)),
        Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
    exact h1.trans ⟨q + 1, hGU⟩
  refine ⟨a, μ, ha1, hμ, ⟨F.map (famUProj n q L) hinj⟩, fun hdv => ?_⟩
  have h3 := hdv.trans hdvd
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne', hGUfac] at h3
  omega

theorem listRow_statedProj_su_three (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hq : ℓ ^ f % 3 = 1) (hn : n / 2 = 3) : ListRow (StatedProj (StatedSU n (ℓ ^ f) L)) := by
  obtain ⟨a, μ, ha, hμ, ⟨F⟩, hS⟩ := exists_frame_statedProj_su hℓ hL hq hn (by omega)
  rw [Wreath.factorization_factorial_three, show a * 3 + 1 + 1 = 3 * a + 2 by ring] at hS
  exact Wreath.listRow_of_twistFrame ha hμ F hS

theorem listRow_statedProj_su_two (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hq : ℓ ^ f % 3 = 1) (hn : n / 2 = 2) : ListRow (StatedProj (StatedSU n (ℓ ^ f) L)) := by
  obtain ⟨a, μ, ha, hμ, ⟨F⟩, hS⟩ := exists_frame_statedProj_su hℓ hL hq hn (by omega)
  have h2 : (Nat.factorial 2).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  rw [h2, show a * 2 + 0 + 1 = 2 * a + 1 by ring] at hS
  exact Wreath.listRow_of_twistFrame_two hμ F hS

theorem listRow_psu5 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSU 5 p f)
    (hq : p ^ f % 3 = 1) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_su_two hadm.1 hK hq (by norm_num))

theorem listRow_psu6 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSU 6 p f)
    (hq : p ^ f % 3 = 1) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_su_three hadm.1 hK hq (by norm_num))

theorem listRow_psu7 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSU 7 p f)
    (hq : p ^ f % 3 = 1) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_su_three hadm.1 hK hq (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
