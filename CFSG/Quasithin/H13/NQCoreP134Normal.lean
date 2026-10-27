module

public import CFSG.Quasithin.H13.NQCoreP134Inputs
public import CFSG.Quasithin.H13.NQCoreP134Group
import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3
open scoped commutatorElement

theorem card_center_of_a36Common' {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : A36Common X) :
    Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨-, -, hbr, -⟩ := id h
  rcases hbr with ⟨hFF, -⟩ | ⟨hFZ, -, hc⟩
  · exact absurd hFF (A36A.generalizedFitting_ne_fittingSubgroup hq (A37.fitting_le_center hq h))
  · rwa [← hFZ]

variable {Γ : Type} [Group Γ]

theorem le_normalizer_inf' {N A B : Subgroup Γ} (hA : N ≤ Subgroup.normalizer (A : Set Γ))
    (hB : N ≤ Subgroup.normalizer (B : Set Γ)) :
    N ≤ Subgroup.normalizer ((A ⊓ B : Subgroup Γ) : Set Γ) :=
  fun _ hn => Subgroup.inf_normalizer_le_normalizer_inf ⟨hA hn, hB hn⟩

theorem card_inf_centralizer (L : Subgroup Γ) :
    Nat.card (L ⊓ Subgroup.centralizer (L : Set Γ) : Subgroup Γ) =
      Nat.card (Subgroup.center ↥L) := by
  have hmap : (Subgroup.center ↥L).map L.subtype = L ⊓ Subgroup.centralizer (L : Set Γ) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
    · rintro ⟨hxL, hxC⟩
      refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.mpr fun l => Subtype.ext ?_, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hxC) l l.2
  rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective]

theorem le_normalizer_of_normal {K : Subgroup Γ} (hK : K.Normal) (M : Subgroup Γ) :
    M ≤ Subgroup.normalizer (K : Set Γ) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hK]
  exact le_top

theorem le_normalizer_commutator {P N : Subgroup Γ} (hNP : N ≤ Subgroup.normalizer (P : Set Γ)) :
    N ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup Γ) : Set Γ) := by
  intro n hn
  have h : ⁅P, P⁆.map (MulAut.conj n).toMonoidHom = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hNP hn)]
  exact mem_normalizer_of_map_conj_le h.le (by
    have hi : ⁅P, P⁆.map (MulAut.conj n⁻¹).toMonoidHom = ⁅P, P⁆ := by
      rw [Subgroup.map_commutator,
        map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ (hNP hn))]
    exact hi.le)

theorem inf_le_or_le_of_irreducible [Finite Γ] {p : ℕ} [hp : Fact p.Prime] {P N W : Subgroup Γ}
    (hPp : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hNW : N ≤ Subgroup.normalizer (W : Set Γ)) : P ⊓ W ≤ ⁅P, P⁆ ∨ P ≤ W := by
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hcP : ⁅P, P⁆ ≤ P := commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  have hN : N ≤ Subgroup.normalizer (((P ⊓ W) ⊔ ⁅P, P⁆ : Subgroup Γ) : Set Γ) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_inf' hNP hNW hn, le_normalizer_commutator hNP hn⟩
  rcases hirr ((P ⊓ W) ⊔ ⁅P, P⁆) le_sup_right (sup_le inf_le_left hcP) hN with h | h
  · exact Or.inl (le_sup_left.trans h.le)
  · right
    have h1 : P ⊓ W ⊔ frattiniIn P = P := by rw [hΦ]; exact h
    have h2 := eq_of_sup_frattiniIn_eq inf_le_left h1
    rw [← h2]
    exact inf_le_right

theorem le_card_of_ne_bot [Finite Γ] {p : ℕ} [hp : Fact p.Prime] {Q : Subgroup Γ}
    (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥) : p ≤ Nat.card Q := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hQ1 (Subgroup.card_eq_one.mp hk)
  rw [hk]
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr hk0)

variable [Finite Γ]

theorem normal_case_odd (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ) (hF : Facts134Odd)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {P T N L : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    P ≤ L ∧ OddOutcome p L P T := by
  have hp2 : p ≠ 2 := by omega
  have hrank : Open.pRank p (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) p hp.out hp2
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : p ^ 2 ≤ Nat.card P := by
    rcases hcard with h | h <;> rw [h]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rcases hcard with h | h <;> rw [h]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hpsq : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  set C := Subgroup.centralizer (L : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  set D := L ⊔ C with hDdef
  have hDn : D.Normal := Subgroup.sup_normal L C
  have hinv := fun (W : Subgroup Γ) (hW : N ≤ Subgroup.normalizer (W : Set Γ)) =>
    inf_le_or_le_of_irreducible hPp hexp hNP hirr hW
  have hPD : P ≤ D := by
    rcases hinv D (le_normalizer_of_normal hDn N) with h | h
    · exfalso
      obtain ⟨u, huP, hu⟩ := hF.outCyclic Γ L P p hp.out hp5 hyp hLn hL hPp
      have huP' : Subgroup.zpowers u ≤ P := Subgroup.zpowers_le.mpr huP
      have h1 : P ≤ Subgroup.zpowers u ⊔ (P ⊓ D) := by
        intro x hx
        have hx' := hu hx
        rw [sup_comm] at hx'
        obtain ⟨d, hd, v, hv, rfl⟩ :=
          (mem_sup_iff_of_le_normalizer (le_normalizer_of_normal hDn _)).1 hx'
        have hvP : v ∈ P := huP' hv
        have hdP : d ∈ P := by
          have := P.mul_mem hx (P.inv_mem hvP)
          simpa using this
        rw [sup_comm]
        exact Subgroup.mul_mem_sup ⟨hdP, hd⟩ hv
      have h2 : Subgroup.zpowers u ⊔ frattiniIn P = P :=
        le_antisymm (sup_le huP' (Subgroup.map_subtype_le _))
          (h1.trans (sup_le_sup_left (hΦ ▸ h) _))
      have h3 := eq_of_sup_frattiniIn_eq huP' h2
      have : Nat.card P ≤ p := by
        rw [← h3, Nat.card_zpowers]
        exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hexp u huP))
      omega
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
  exact ⟨hPL, hF.normal Γ p L P T hp5 ⟨hyp, hLn, hL, hPL, hexp, hcard, hT, hmul,
    fun U h1 h2 h3 => hirr U h1 h2 ((le_inf hNT hNP).trans h3)⟩⟩

end CFSG.Quasithin.H13.NQCore
