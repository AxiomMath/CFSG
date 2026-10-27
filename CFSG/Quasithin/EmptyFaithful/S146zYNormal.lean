module

public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Normal

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3 CFSG.Quasithin.H13.NQCore
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem normal_case_five (hR : NormalInputs) (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : p = 5) {P T N L : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2) (hPc : P ≤ commutator Γ)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    P ≤ L ∧ NormalOutcome p L P T := by
  have hp2 : p ≠ 2 := by omega
  have hrank : Open.pRank p (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) p hp.out hp2
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : p ^ 2 ≤ Nat.card P := hcard.ge
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rw [hcard]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  set C := Subgroup.centralizer (L : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  set D := L ⊔ C with hDdef
  have hDn : D.Normal := Subgroup.sup_normal L C
  have hinv := fun (W : Subgroup Γ) (hW : N ≤ Subgroup.normalizer (W : Set Γ)) =>
    inf_le_or_le_of_irreducible hPp hexp hNP hirr hW
  have hPD : P ≤ D := by
    rcases hinv D (le_normalizer_of_normal hDn N) with h | h
    · exfalso
      have hPab : IsMulCommutative ↥P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
      have hcomm0 : ⁅P, P⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hPab
      have hPD1 : P ⊓ D = ⊥ := eq_bot_iff.mpr (h.trans hcomm0.le)
      by_cases hpL : p ∣ Nat.card L
      ·
        have hPL1 : P ⊓ L = ⊥ :=
          eq_bot_iff.mpr ((inf_le_inf_left P le_sup_left).trans hPD1.le)
        exact false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hLn P) hPL1 hpL
      · exact hR.outNoE25 p hp5 Γ L P hyp hLn hL hpL hPc hexp hcard hPD1
    · exact h
  have hPC : P ⊓ C ≤ ⁅P, P⁆ := by
    rcases hinv C (le_normalizer_of_normal hCn N) with h | h
    · exact h
    · exact absurd h hLP
  have hZ : Nat.card (L ⊓ C : Subgroup Γ) = 1 ∨ Nat.card (L ⊓ C : Subgroup Γ) = 3 := by
    rw [card_inf_centralizer]
    exact card_center_of_a36Common' hL.1 (h36 L hLc).2.1
  have hPZ : P ⊓ (L ⊓ C) = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hPp.to_le (inf_le_left : P ⊓ (L ⊓ C) ≤ P))
    have hdvd : Nat.card (P ⊓ (L ⊓ C) : Subgroup Γ) ∣ Nat.card (L ⊓ C : Subgroup Γ) :=
      Subgroup.card_dvd_of_le inf_le_right
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exfalso
      have hpd : p ∣ Nat.card (L ⊓ C : Subgroup Γ) :=
        (dvd_pow_self p h0.ne').trans (hk ▸ hdvd)
      rcases hZ with h1 | h3
      · rw [h1] at hpd
        exact hp.out.one_lt.ne' (Nat.dvd_one.mp hpd)
      · rw [h3] at hpd
        have := Nat.le_of_dvd (by norm_num) hpd
        omega
  have hPL : P ≤ L := by
    rcases hinv L (le_normalizer_of_normal hLn N) with h | h
    swap
    · exact h
    exfalso
    by_cases hpC : p ∣ Nat.card C
    · by_cases hPC1 : P ⊓ C = ⊥
      · exact false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hCn P) hPC1 hpC
      by_cases hPL1 : P ⊓ L = ⊥
      · by_cases hpL : p ∣ Nat.card L
        · exact false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hLn P) hPL1 hpL
        · apply hLP
          intro x hx
          exact mem_of_mem_sup_of_coprime (M := L) (M' := C) le_rfl hpL (hPD hx) (hexp x hx)
      have hle : (P ⊓ L) ⊔ (P ⊓ C) ≤ ⁅P, P⁆ := sup_le h hPC
      have hnorm : P ⊓ C ≤ Subgroup.normalizer ((P ⊓ L : Subgroup Γ) : Set Γ) :=
        le_normalizer_inf' (inf_le_left.trans Subgroup.le_normalizer)
          (inf_le_right.trans (P134.centralizer_le_normalizer_self L))
      have hdisj : Disjoint (P ⊓ L) (P ⊓ C) := by
        rw [disjoint_iff]
        refine eq_bot_iff.mpr fun x hx => ?_
        have hx' : x ∈ P ⊓ (L ⊓ C) := ⟨hx.1.1, hx.1.2, hx.2.2⟩
        rw [hPZ] at hx'
        exact hx'
      have hcard' := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj
      have h1 := le_card_of_ne_bot (hPp.to_le inf_le_left) hPL1
      have h2 := le_card_of_ne_bot (hPp.to_le inf_le_left) hPC1
      have h3 := Subgroup.card_le_of_le hle
      have h4 := card_commutator_le hexp hc2 hc3
      have h5 : p * p ≤ Nat.card (P ⊓ L : Subgroup Γ) * Nat.card (P ⊓ C : Subgroup Γ) :=
        Nat.mul_le_mul h1 h2
      rw [← hcard'] at h5
      have h6 : p < p * p := by
        have := hp.out.one_lt
        nlinarith
      omega
    ·
      have hPL' : P ≤ L := by
        intro x hx
        have hx' : x ∈ C ⊔ L := by rw [sup_comm]; exact hPD hx
        refine mem_of_mem_sup_of_coprime (M := C) (M' := L) ?_ hpC hx' (hexp x hx)
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm
      have hPc : P ≤ ⁅P, P⁆ := by
        have := (inf_eq_left.mpr hPL') ▸ h
        exact this
      exact frattiniIn_ne_of_ne_bot hP1 (le_antisymm (Subgroup.map_subtype_le _) (hΦ ▸ hPc))
  exact ⟨hPL, hR.normal p hp5 Γ L P T ⟨hyp, hLn, hL, hPL, hexp, Or.inl hcard, hT, hmul,
    fun U h1 h2 h3 => hirr U h1 h2 ((le_inf hNT hNP).trans h3)⟩ hcard⟩

end CFSG.Quasithin.S146zY
