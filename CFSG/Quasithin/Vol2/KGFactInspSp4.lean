module

public import CFSG.Quasithin.Vol2.KGFactInspOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag StatedProj StatedSU
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.SectionRank.ClassicalEven (torusDiag coe_torusDiag torusDiag_injective
  scalar_eq_torusDiag torusVec torusVec_pow torusVec_one torusVec_apply_left torusVec_apply_right
  torusVec_apply_of_ne)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (symplectic_higher_order_and_Sylow)
open Matrix
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K]

theorem torusDiag_mem_sp {m : ℕ} {d : Fin m ⊕ Fin m → Kˣ}
    (hd : ∀ i, (d (Sum.inl i) : K) * d (Sum.inr i) = 1) : torusDiag d ∈ StatedSp m K := by
  refine Subgroup.subset_closure ?_
  show (torusDiag d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      (torusDiag d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = fromBlocks 0 1 (-1) 0
  rw [coe_torusDiag, diagonal_transpose]
  ext u v
  rw [mul_diagonal, diagonal_mul]
  rcases u with i | i <;> rcases v with j | j
  · simp
  · simp only [fromBlocks_apply₁₂, one_apply]
    split_ifs with hij
    · subst hij
      rw [mul_one]
      exact hd i
    · simp
  · rw [fromBlocks_apply₂₁]
    by_cases hij : i = j
    · subst hij
      have e1 : (-1 : Matrix (Fin m) (Fin m) K) i i = -1 := by simp
      rw [e1]
      linear_combination -(hd i)
    · have e1 : (-1 : Matrix (Fin m) (Fin m) K) i j = 0 := by simp [one_apply_ne hij]
      rw [e1]
      simp
  · simp

theorem two_le_pRank_psp4 [Finite K] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp 2 K))) := by
  obtain ⟨ζ, hζ⟩ :=
    exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hdvd)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hpow (j : Fin 2) : torusDiag (torusVec ζ (Sum.inl j) (Sum.inr j)) ^ p = 1 := by
    rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
  have hmem (j : Fin 2) : torusDiag (torusVec ζ (Sum.inl j) (Sum.inr j)) ∈ StatedSp 2 K := by
    refine torusDiag_mem_sp fun i => ?_
    by_cases hij : i = j
    · subst hij
      rw [torusVec_apply_left ζ Sum.inl_ne_inr, torusVec_apply_right ζ Sum.inl_ne_inr]
      simp
    · rw [torusVec_apply_of_ne ζ (by simpa using hij) Sum.inl_ne_inr,
        torusVec_apply_of_ne ζ Sum.inr_ne_inl (by simpa using hij)]
      simp
  have hent {d d' : Fin 2 ⊕ Fin 2 → Kˣ} (h : torusDiag d = torusDiag d') (i : Fin 2 ⊕ Fin 2) :
      d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_statedProj (H := StatedSp 2 K)
    (hmem 0) (hmem 1) (hpow 0) (hpow 1) ((Commute.all _ _).map torusDiag) ?_ ?_
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := hent hc (Sum.inl 0)
    have e1 := hent hc (Sum.inl 1)
    rw [torusVec_apply_left ζ Sum.inl_ne_inr] at e0
    rw [torusVec_apply_of_ne ζ (by decide) Sum.inl_ne_inr] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro k c ⟨c', rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e1 := hent h (Sum.inl 1)
    have e2 := hent h (Sum.inr 1)
    simp only [Pi.mul_apply] at e1 e2
    rw [torusVec_apply_of_ne _ (by decide) Sum.inl_ne_inr, torusVec_apply_left _ Sum.inl_ne_inr,
      one_mul] at e1
    rw [torusVec_apply_of_ne _ Sum.inr_ne_inl (by decide), torusVec_apply_right _ Sum.inl_ne_inr,
      one_mul] at e2
    have hinv : ζ = ζ⁻¹ := e1.symm.trans e2
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel ζ
    have hp2' : p ∣ 2 := hζ ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hp2')

end Torus

theorem dvd_two_pow_sub_one_of_odd {p n f : ℕ} (hn : Odd n) (hpn : p ∣ 2 ^ n - 1)
    (hpf : p ∣ 2 ^ (4 * f) - 1) : p ∣ 2 ^ f - 1 := by
  have key : ∀ m : ℕ, p ∣ 2 ^ m - 1 ↔ (2 : ZMod p) ^ m = 1 := by
    intro m
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_eq_zero]
  rw [key] at hpn hpf ⊢
  have h := pow_gcd_eq_one.mpr ⟨hpf, hpn⟩
  have hcop : Nat.Coprime 4 n := by
    have : Nat.Coprime (2 ^ 2) n := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hn)
    simpa using this
  rw [Nat.Coprime.gcd_mul_left_cancel f hcop] at h
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_left f n
  rw [hc, pow_mul, h, one_pow]

namespace Cfg4316

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem of_psleps3q (h : Cfg4316 S R K n x) (hRS : R ≤ S)
    {s : Bool} {q : ℕ} (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1))
    (hL : IsPSLEps3q s q ↥S) : n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S) := by
  obtain ⟨p, e, hp, he1, rfl, hm⟩ := hL
  by_cases hp2 : p = 2
  · subst hp2
    cases s
    · exfalso
      have hm' : StatedClassicalModel ↥S .PSU 3 2 e := hm
      obtain ⟨-, -, -, hne⟩ := hm'.1
      have he2 : 2 ≤ e := by
        by_contra hlt
        have : e = 1 := by omega
        subst this
        exact hne rfl
      exact h.toCfg.false_of_psu3_two hRS he2 hm'
    · have hm' : StatedClassicalModel ↥S .PSL 3 2 e := hm
      have he2 : 2 ≤ e := by
        by_contra hlt
        have : e = 1 := by omega
        subst this
        revert hq
        decide
      obtain ⟨hn, he⟩ := h.eq_two_of_psl3_two hRS he2 hm'
      subst he
      exact ⟨hn, Or.inl hm'⟩
  · cases s
    · obtain ⟨hn, h5⟩ := h.eq_five_psu hRS hp hp2 hm
      obtain ⟨rfl, rfl⟩ := ((by norm_num : Nat.Prime 5).pow_eq_iff).mp h5
      exact ⟨hn, Or.inr hm⟩
    · obtain ⟨-, h5⟩ := h.eq_five_psl hRS hp hp2 hm
      rw [h5] at hq
      exact absurd hq (by decide)

theorem of_psp4 (h : Cfg4316 S R K n x) (hRS : R ≤ S) {f : ℕ}
    (hm : StatedClassicalModel ↥S .PSp 2 2 f) : n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
  have hpr : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 → 2 ≤ CFSG.Open.pRank p S →
      n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S) := by
    intro p hp hp2 hpn h2
    rcases h.prime p hp hp2 hpn with h1 | ⟨-, s, q, hq, hL⟩
    · omega
    · exact h.of_psleps3q hRS hq hL
  have hn2 := h.two_le
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hn
  ·
    refine hpr 3 Nat.prime_three (by norm_num) ?_ ?_
    · have h4 : 2 ^ n = 4 ^ k := by rw [hk, ← two_mul, pow_mul]; norm_num
      rw [h4]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    · obtain ⟨A, hA, hc⟩ := CFSG.QuasithinUnique.Id2519.hasElemAb_nine_psp_four F
      exact CFSG.QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv e (by norm_num)
        (CFSG.SectionRank.le_pRank (by norm_num) le_top hA (k := 2) (by rw [hc]; norm_num))
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card]; exact hF)
    have h4n : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    set p := Nat.minFac (2 ^ n - 1) with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have : Fact p.Prime := ⟨hp⟩
    have hpn : p ∣ 2 ^ n - 1 := Nat.minFac_dvd _
    have hp2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpn
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    obtain ⟨F', _, _, hF', χ, hχ, -⟩ := h.chi
    have hSL : 2 ^ n - 1 ∣ Nat.card SL(2, F') := by
      rw [CFSG.Quasithin.H13.KGInspOdd.card_sl2, Nat.card_eq_fintype_card, hF']
      refine Dvd.dvd.mul_left ?_ _
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    have hKS : Nat.card ↥K ∣ Nat.card ↥S := Subgroup.card_dvd_of_le h.le
    have hSP : Nat.card ↥S ∣ Nat.card ↥(StatedSp 2 F) := by
      rw [Nat.card_congr e.toEquiv]
      exact Subgroup.card_dvd_of_surjective
        (CFSG.RankThree.CentralCover.statedProjMk_surjective (StatedSp 2 F))
    have hcard := (symplectic_higher_order_and_Sylow (K := F) 2 (2 ^ f) hF (r := 2)
      (by norm_num)).1
    have hpSp : p ∣ (2 ^ f) ^ 4 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) := by
      have h1 := hpn.trans (hSL.trans ((Subgroup.card_dvd_of_surjective hχ).trans
        (hKS.trans hSP)))
      rw [hcard] at h1
      simpa [Finset.prod_Icc_succ_top, mul_assoc] using h1
    have hpf4 : p ∣ 2 ^ (4 * f) - 1 := by
      have hq4 : ¬ p ∣ (2 ^ f) ^ 4 := fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)))
      have h2 : (2 ^ f) ^ 2 - 1 ∣ (2 ^ f) ^ 4 - 1 := by
        generalize 2 ^ f = a
        have := Nat.sub_dvd_pow_sub_pow (a ^ 2) 1 2
        rwa [one_pow, ← pow_mul] at this
      rw [show 4 * f = f * 4 from mul_comm 4 f, pow_mul]
      rcases (Nat.Prime.dvd_mul hp).mp hpSp with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · exact absurd h4 hq4
        · exact h4.trans h2
      · exact h3
    have hpf := dvd_two_pow_sub_one_of_odd hn hpn hpf4
    obtain ⟨hn', -⟩ := hpr p hp hp2 hpn (CFSG.QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv e
      hp.one_lt (two_le_pRank_psp4 hp2 (by rw [hF]; exact hpf)))
    subst hn'
    exact absurd hn (by decide)

end Cfg4316

@[expose] def Insp4316OutLieExc : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X), Cfg4316 S R K n x →
    R ≤ S → (∃ f : ℕ,
      (2 ≤ f ∧ ChevalleyExceptionalModel ↥S .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel ↥S .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel ↥S .twistedF4 2 f)) →
    ∀ x' ∈ Subgroup.zpowers x, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 → orderOf x' = p →
      x' ∉ S → n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)

theorem insp4316OutLieRank2_of (hE : Insp4316OutLieExc) :
    Insp4316OutLieRank2 := by
  intro X _ _ S R K n x h hRS hLie x' hx'z p hp hp2 hpn hx'o hx'S
  rcases hLie with ⟨f, ⟨-, hm⟩ | hm⟩
  · exact h.of_psp4 hRS hm
  · exact hE X S R K n x h hRS ⟨f, hm⟩ x' hx'z p hp hp2 hpn hx'o hx'S

end CFSG.Quasithin.H13.KGInsp4316
