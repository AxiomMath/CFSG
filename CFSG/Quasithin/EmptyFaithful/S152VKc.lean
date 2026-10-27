module

public import CFSG.Quasithin.EmptyFaithful.S152UTail
public import CFSG.Quasithin.EmptyFaithful.S152He5AutBase
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Blueprint

namespace S152V

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_dvd_of_hasSectionIso {X : Subgroup G} {Y : Type} [Group Y]
    (h : S152U.HasSectionIso X Y) : Nat.card Y ∣ Nat.card ↥X := by
  obtain ⟨A, N, hN, hAX, ⟨e⟩⟩ := h
  rw [← Nat.card_congr e.toEquiv]
  exact (Subgroup.card_quotient_dvd_card N).trans (Subgroup.card_dvd_of_le hAX)

theorem card_M22 :
    Nat.card (NativeSporadic.Carrier .M22) = 443520 :=
  CFSG.Sporadic.Mathieu.card_M22

theorem exists_card_eq_two_pow_mul_oTwoQuot (X : Subgroup G) :
    ∃ a : ℕ, Nat.card ↥X = 2 ^ a * Nat.card (OTwoQuot X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 X).exists_card_eq
  refine ⟨a, ?_⟩
  have h1 := card_eq_card_pCoreOf_mul_relIndex X
  have h2 : Nat.card (OTwoQuot X) = (pCoreOf 2 X).relIndex X := by
    unfold Subgroup.relIndex
    have : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X := by
      unfold pCoreOf Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    rw [this]
    rfl
  rw [h1, ha, h2]

theorem isXi_not_hasSectionIso_M22 {T K : Subgroup G}
    (hX : IsXi T K) : ¬ S152U.HasSectionIso K (NativeSporadic.Carrier .M22) := by
  intro hs
  obtain ⟨-, -, -, p, hp, hp2, -, hidx, -⟩ := hX
  have h35 : 35 ∣ Nat.card ↥K := by
    refine Dvd.dvd.trans ?_ (card_dvd_of_hasSectionIso hs)
    rw [card_M22]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 K).exists_card_eq
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (pCoreOf 2 K).relIndex K = p ^ k := by
    rcases hidx with h | ⟨h, -⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  have hcard : Nat.card ↥K = 2 ^ a * p ^ k := by
    rw [card_eq_card_pCoreOf_mul_relIndex K, ha, hk]
  rw [hcard] at h35
  have h5 : 5 ∣ 2 ^ a * p ^ k := (by norm_num : 5 ∣ 35).trans h35
  have h7 : 7 ∣ 2 ^ a * p ^ k := (by norm_num : 7 ∣ 35).trans h35
  have h5' : 5 ∣ p ^ k := by
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
        ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h)) (by norm_num)
    · exact h
  have h7' : 7 ∣ p ^ k := by
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h7 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
        ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)) (by norm_num)
    · exact h
  have hp5 : p = 5 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1
    ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5')).symm
  have hp7 : p = 7 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1
    ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h7')).symm
  omega

theorem card_mulAut_projectiveSL {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n
        CFSG.Quasithin.He5.K2)) =
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) CFSG.Quasithin.He5.K2) := by
  have h1 := Subgroup.card_mul_index (CFSG.Quasithin.He5.InnP n)
  rw [CFSG.Quasithin.He5.index_inn_eq_two hn] at h1
  have h2 : Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n
        CFSG.Quasithin.He5.K2) = Nat.card (CFSG.Quasithin.He5.InnP n) :=
    Nat.card_congr (MonoidHom.ofInjective (CFSG.Quasithin.He5.conj_injective n)).toEquiv
  have h3 : Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n
        CFSG.Quasithin.He5.K2) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) CFSG.Quasithin.He5.K2) :=
    (Nat.card_congr (Equiv.ofBijective
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n CFSG.Quasithin.He5.K2)
      ⟨CFSG.Quasithin.He5.proj_injective n,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective n
          CFSG.Quasithin.He5.K2⟩)).symm
  rw [← h1, ← h2, h3, mul_comm]

theorem card_mulAut_psl {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) =
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  let e0 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n CFSG.Quasithin.He5.K2 ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center n CFSG.Quasithin.He5.K2)
  rw [← Nat.card_congr (MulAut.congr e0).toEquiv]
  exact card_mulAut_projectiveSL hn

theorem card_SL_four_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field, ZMod.card]
  decide

theorem card_SL_five_two : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_SL_field, ZMod.card]
  decide

theorem caseII_not_hasSectionIso_M22 {T Kc : Subgroup G}
    (h : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsAutLnTwo n (OTwoQuot (Kc ⊔ T))) :
    ¬ S152U.HasSectionIso Kc (NativeSporadic.Carrier .M22) := by
  intro hs
  obtain ⟨n, hn, ⟨e⟩⟩ := h
  have h11 : 11 ∣ Nat.card ↥Kc := by
    refine Dvd.dvd.trans ?_ (card_dvd_of_hasSectionIso hs)
    rw [card_M22]
    norm_num
  obtain ⟨b, hb⟩ := exists_card_eq_two_pow_mul_oTwoQuot (Kc ⊔ T)
  have hq : Nat.card (OTwoQuot (Kc ⊔ T)) =
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [Nat.card_congr e.toEquiv]
    exact card_mulAut_psl (n := n) (by omega)
  have hdvd : 11 ∣ Nat.card ↥(Kc ⊔ T) := h11.trans (Subgroup.card_dvd_of_le le_sup_left)
  rw [hb, hq] at hdvd
  have hSL : ¬ 11 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rcases hn with rfl | rfl
    · rw [card_SL_four_two]
      norm_num
    · rw [card_SL_five_two]
      norm_num
  have h11p : Nat.Prime 11 := by norm_num
  rcases (Nat.Prime.dvd_mul h11p).1 hdvd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq h11p Nat.prime_two).1 (h11p.dvd_of_dvd_pow h))
      (by norm_num)
  · rcases (Nat.Prime.dvd_mul h11p).1 h with h' | h'
    · exact absurd h' (by norm_num)
    · exact hSL h'

theorem caseHe_not_hasSectionIso_M22
    {Kc : Subgroup G} (h : Nonempty (OTwoQuot Kc ≃* NativeSporadic.Carrier .He)) :
    ¬ S152U.HasSectionIso Kc (NativeSporadic.Carrier .M22) := by
  intro hs
  obtain ⟨e⟩ := h
  have h11 : 11 ∣ Nat.card ↥Kc := by
    refine Dvd.dvd.trans ?_ (card_dvd_of_hasSectionIso hs)
    rw [card_M22]
    norm_num
  obtain ⟨a, ha⟩ := exists_card_eq_two_pow_mul_oTwoQuot Kc
  have hHe : Nat.card (NativeSporadic.Carrier .He) = 4030387200 :=
    CFSG.Sporadic.He.card_He
  have hq : Nat.card (OTwoQuot Kc) = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact hHe
  rw [ha, hq] at h11
  have h11p : Nat.Prime 11 := by norm_num
  rcases (Nat.Prime.dvd_mul h11p).1 h11 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq h11p Nat.prime_two).1 (h11p.dvd_of_dvd_pow h))
      (by norm_num)
  · exact absurd h (by norm_num)

end S152V

@[expose] def Tail15215KcIii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc K : Subgroup G), IsXi T K →
    Case15212iii T Mc (conjClosure K Mc) →
      ¬ S152U.HasSectionIso (conjClosure K Mc) (NativeSporadic.Carrier .M22)

theorem tail15215Kc_of_iii
    (hiii : Tail15215KcIii) : Tail15215Kc := by
  intro G _ _ T Mc K hxi hcases
  rcases hcases with h | h | h | h
  · rw [h]
    exact S152V.isXi_not_hasSectionIso_M22 hxi
  · exact S152V.caseII_not_hasSectionIso_M22 h.2.2
  · exact hiii G T Mc K hxi h
  · exact S152V.caseHe_not_hasSectionIso_M22 h.2.2

end CFSG.Quasithin
