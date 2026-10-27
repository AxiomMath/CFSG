module

import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.Quasithin.Background.F1Models
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint.Multiplier

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_u5_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU5 Y n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : r ≠ 5) (hrn : r ∣ 2 ^ n - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := uc22s218_u5_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1) :=
    CFSG.Quasithin.H13.Sec53F.Unit.finite_hypPSU_five h
  rw [← CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  exact uc22s218_u5_model_not_dvd_card_sylow h hr hr2 hr5 hrn

theorem uc22s2114_u4_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 < 2 ^ n := by
    have h1 : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (CFSG.Blueprint.LieModel.admissible hY).2.1
    have h2 := Nat.le_of_dvd (by omega) hrn
    have := hr.two_le
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hK := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_U4CartanRank_holds Y n hY hq
    (P : Subgroup Y) (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P) r hr hr2 hrn
  have hdvd : Nat.card (TauCeti.Subgroup.normalizerQuotient (P : Subgroup Y)) ∣
      Nat.card (normalizer ((P : Subgroup Y) : Set Y)) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((P : Subgroup Y).subgroupOf (normalizer ((P : Subgroup Y) : Set Y)))
    exact Dvd.intro _ h.symm
  refine CFSG.RankThree.PartOne.K133.not_dvd_card_sylow_of_le_normalizer hr P
    (normalizer ((P : Subgroup Y) : Set Y)) le_rfl (fun k hk => ?_)
  have hk' := (Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').1 hk
  rw [hK.2.2] at hk'
  exact ((Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').2 hk').trans hdvd

theorem uc22s2114_center_bar2_eq_bot_of_isU4_of_ne_one (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ} (hX : IsU4 (BarInf L) f) (hf : f ≠ 1) :
    center (Bar2 L) = ⊥ := by
  have hf0 : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible hX).2.1
  have hex : exceptionalOrders .PSU 4 2 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSU 4 2 f = (1, 1) := by
    have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    have hcop : Nat.Coprime (2 ^ 2) (2 ^ f + 1) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
    show (Nat.gcd 4 (2 ^ f + 1), 1) = (1, 1)
    rw [show Nat.gcd 4 (2 ^ f + 1) = 1 from hcop]
  exact center_bar2_eq_bot_of_row hL hg hex
    (griessRow_of_lieModel_classical hGA hX (by decide))

theorem uc22s2114_false_of_isU5 (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsU5 (BarInf L) f) (hf : 2 ∣ f)
    (hn : 4 ∣ c.n) : False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have h15 : 15 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 15 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h5σ : 5 ∉ D.sig :=
    uc22s2114_not_mem_sig hSg hns hH c (by norm_num) ((by norm_num : 5 ∣ 15).trans h15)
  have h3f : 3 ∣ 2 ^ f - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h3f2 : 3 ∣ 2 ^ (2 * f) - 1 :=
    h3f.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left f 2))
  have hZ := card_center_bar2_dvd_of_isU5 hGA hL hX
  have hZ5 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 5 → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ hℓ5 h =>
    hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1
      (h.trans (hZ.trans (Nat.gcd_dvd_left 5 _))))
  obtain ⟨T, hTc, hTE⟩ := uc22s218_u5_torus hX
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hp5 : p ≠ 5 := fun h => h5σ (h ▸ hp)
  refine uc22s2114_false_of_torusFacts hSg h614 h76 h4 hH c hL (torusFacts218_U5 hX) hTc hTE
    Nat.prime_three (by norm_num) ⟨h3f2, fun h => absurd h.1 (by norm_num)⟩
    ((by norm_num : 3 ∣ 15).trans h15)
    (uc22s2114_u5_not_dvd_card_sylow hX Nat.prime_three (by norm_num) (by norm_num) h3f)
    (hZ5 3 Nat.prime_three (by norm_num)) hp (hZ5 p (D.sig_prime p hp).1 hp5) ?_
  by_cases hpq : p ∣ 2 ^ (2 * f) - 1
  · exact Or.inl ⟨hpq, fun h => hp5 h.1⟩
  · exact Or.inr hpq

theorem uc22s2114_false_of_isU4 (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsU4 (BarInf L) f) (hf : 2 ∣ f)
    (hn : 2 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig) (hpf : ¬ p ∣ 2 ^ f + 1) : False := by
  have h3n : 3 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h3f : 3 ∣ 2 ^ f - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [uc22s2114_center_bar2_eq_bot_of_isU4_of_ne_one hGA hL hX (by omega), card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨T, hTc, hTE, -⟩ := uc22s218_u4_torus hX
  refine uc22s2114_false_of_torusFacts hSg h614 h76 h4 hH c hL (torusFacts218_U4 hX) hTc hTE
    Nat.prime_three (by norm_num) h3f h3n
    (uc22s2114_u4_not_dvd_card_sylow hX Nat.prime_three (by norm_num) h3f)
    (hZ 3 Nat.prime_three) hp (hZ p (D.sig_prime p hp).1) ?_
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact Or.inl hpq
  · exact Or.inr ⟨hpq, hpf⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
