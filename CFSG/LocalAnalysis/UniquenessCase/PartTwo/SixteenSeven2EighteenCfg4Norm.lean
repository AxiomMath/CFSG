module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem natCard_multiplicative (α : Type*) : Nat.card (Multiplicative α) = Nat.card α :=
  Nat.card_congr Multiplicative.ofAdd.symm

private theorem card_of_isElemAbelianOfRank {p n : ℕ} {X : Type} [Group X]
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, natCard_multiplicative, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]

private theorem eq_three_of_prime_pow_eq {p r : ℕ} (hp : p.Prime) (h : p ^ r = 27) :
    p = 3 ∧ r = 3 := by
  have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
  have h' : p ^ r = 3 ^ 3 := h.trans h27.symm
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  have hpdv : p ∣ 3 ^ 3 := by
    rw [← h']
    exact dvd_pow_self p hr
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hpdv)
  refine ⟨hp3, ?_⟩
  rw [hp3] at h'
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h'

private theorem not_quasisimple_of_comm {V : Type} [Group V]
    (hcomm : ∀ x y : V, x * y = y * x) (hq : CFSG.Open.IsQuasisimple V) : False := by
  have hcenter : Subgroup.center V = ⊤ :=
    Subgroup.center_eq_top_iff.mpr (IsMulCommutative.of_comm hcomm)
  have hNontriv : Nontrivial (V ⧸ Subgroup.center V) := hq.2.toNontrivial
  rw [hcenter] at hNontriv
  haveI : Subsingleton (V ⧸ (⊤ : Subgroup V)) :=
    QuotientGroup.subsingleton_quotient_top
  obtain ⟨a, b, hab⟩ := hNontriv.exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem s16c167_cfg4_rk_top {X : Subgroup (MulAut W)} {Z : Subgroup W} (hZ : rk ↥Z = 2)
    (hind : sSupIndep (conjSubs X Z)) (hsup : sSup (conjSubs X Z) = ⊤)
    (hn : (conjSubs X Z).ncard = 4) : rk ↥(⊤ : Subgroup W) = 8 := by
  have hrank_mem : ∀ x : Subgroup W, x ∈ conjSubs X Z → rk ↥x = 2 := by
    rintro x ⟨g, -, rfl⟩
    rw [rk_map_aut_eq, hZ]
  calc rk ↥(⊤ : Subgroup W) = rk ↥(sSup (conjSubs X Z)) := by rw [hsup]
    _ = ∑ᶠ U ∈ conjSubs X Z, rk ↥U := s15_Lin_rk_sSup_eq_finsum hind
    _ = (conjSubs X Z).ncard * 2 :=
        s15_Two_finsum_mem_eq_ncard_mul _ _ _ (Set.toFinite _) hrank_mem
    _ = 8 := by simp [hn]

theorem s16c167_cfg4_normal (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 3 ↥L) (hrk : rk ↥(⊤ : Subgroup W) = 8)
    (h : Conc4_136W A t L) : ∀ x ∈ A, L.map (MulAut.conj x).toMonoidHom = L := by
  obtain ⟨-, hcomm, halt⟩ := h
  have hcard : Nat.card ↥L = 27 := by
    have h := card_of_isElemAbelianOfRank hL
    norm_num at h
    exact h
  obtain ⟨e⟩ := hL
  have hcommL : ∀ x y : ↥L, x * y = y * x := by
    intro x y
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hcommL' : ∀ a b : MulAut W, a ∈ L → b ∈ L → a * b = b * a := by
    intro a b ha hb
    simpa using congrArg Subtype.val (hcommL ⟨a, ha⟩ ⟨b, hb⟩)
  have hcenterL : Subgroup.center ↥L = ⊤ :=
    Subgroup.center_eq_top_iff.mpr (IsMulCommutative.of_comm hcommL)
  have hLbot : L ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥L = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    omega
  have hrk_comm : rk ↥(commSub ⊤ L) = 8 := by
    rcases halt with h133 | hK | hComp | hComp4
    · obtain ⟨p, hp, -, -, -, hcases⟩ := h133
      rcases hcases with
        ⟨hcyc, -⟩ | ⟨hcyc, -⟩ | ⟨hpp, -⟩ | ⟨hEA, -⟩ | ⟨hcyc, -⟩ |
        ⟨r, m, hpm, -, hEAr, hrkeq, -⟩ | ⟨hEA, -, -⟩
      · exfalso
        have h3 := hcyc.2
        omega
      · exfalso
        have h5 := hcyc.2
        omega
      · exfalso
        haveI : IsExtraspecial 3 ↥L := hpp.1
        have h3 : Nat.card (Subgroup.center ↥L) = 3 := IsExtraspecial.center_order_p 3 ↥L
        have h27 : Nat.card (Subgroup.center ↥L) = 27 := by
          rw [hcenterL, Subgroup.card_top]
          exact hcard
        omega
      · exfalso
        have h9 := card_of_isElemAbelianOfRank hEA
        norm_num at h9
        omega
      · exfalso
        have h7 := hcyc.2
        omega
      · have hcard_pr : Nat.card ↥L = p ^ r := card_of_isElemAbelianOfRank hEAr
        have hpr : p ^ r = 27 := hcard_pr.symm.trans hcard
        obtain ⟨hp3, hr3⟩ := eq_three_of_prime_pow_eq hp hpr
        have hm2 : m = 2 := by
          rcases hpm with ⟨-, hm⟩ | ⟨hp7, -⟩
          · exact hm
          · exact absurd (hp7 ▸ hp3) (by norm_num)
        simp [hrkeq, hr3, hm2]
      · exfalso
        have h9 := card_of_isElemAbelianOfRank hEA
        norm_num at h9
        omega
    · obtain ⟨K, hKcomp, g, -, -, hLK, -⟩ := hK
      have hKL : K ≤ L := by
        rw [hLK]
        exact le_sup_left
      have hcommK : ∀ x y : ↥K, x * y = y * x := by
        intro x y
        exact Subtype.ext (hcommL' x.1 y.1 (hKL x.2) (hKL y.2))
      exact (not_quasisimple_of_comm hcommK hKcomp.2.2).elim
    · exact (not_quasisimple_of_comm hcommL hComp.1.2.2).elim
    · exact (not_quasisimple_of_comm hcommL hComp4.2.2.1.2.2).elim
  have hall : commSub ⊤ L = ⊤ := by
    refine eq_of_le_of_rk_le hW le_top ?_
    simp [hrk, hrk_comm]
  intro x hx
  by_contra hne
  have hnot : x ∉ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro hxN
    exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq).mp hxN)
  have h1 : commSub (commSub ⊤ L) (L.map (MulAut.conj x).toMonoidHom) = ⊥ :=
    (hcomm x hx hnot).2
  rw [hall] at h1
  have h2 : (⊤ : Subgroup W) ≤ fixV (L.map (MulAut.conj x).toMonoidHom) :=
    commSub_eq_bot_iff.mp h1
  have h3 : L.map (MulAut.conj x).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    ext w
    have hfix : y w = w :=
      (mem_fixV.mp (h2 (show w ∈ (⊤ : Subgroup W) from trivial))) y hy
    simpa using hfix
  have h4 : L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective L (MulAut.conj x).injective).mp h3
  exact hLbot h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
