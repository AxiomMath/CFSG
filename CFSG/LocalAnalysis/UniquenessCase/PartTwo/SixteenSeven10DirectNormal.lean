module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case4Sym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s16c1610_n3_comm_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s16c1610_n3_center_eq_top {X : Type*} [Group X]
    (hcomm : ∀ a b : X, a * b = b * a) : Subgroup.center X = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_center_iff]
  intro y
  exact hcomm y x

private theorem s16c1610_n3_false_of_isQuasisimple_of_comm {X : Type*} [Group X]
    (hcomm : ∀ a b : X, a * b = b * a) (h : CFSG.Open.IsQuasisimple X) : False := by
  have hcenter : Subgroup.center X = ⊤ := s16c1610_n3_center_eq_top hcomm
  have hbot : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr hcenter
  have hperf : commutator X = ⊤ := h.1
  have htopbot : (⊤ : Subgroup X) = ⊥ := hperf ▸ hbot
  haveI : Subsingleton X := by
    rw [Subgroup.eq_bot_iff_forall] at htopbot
    exact ⟨fun a b => (htopbot a trivial).trans (htopbot b trivial).symm⟩
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (X ⧸ Subgroup.center X)).exists_pair_ne
  exact hab (Subsingleton.elim a b)

private theorem s16c1610_n3_rk_commSub_eq_eight_of_conc4133 {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hcommL : ∀ a b : ↥L, a * b = b * a) (hcardL : Nat.card ↥L = 27)
    (h : Conc4_133 A t L) : rk ↥(commSub ⊤ L) = 8 := by
  obtain ⟨p, hpp, _, _, _, halt⟩ := h
  rcases halt with ⟨hcyc, h | h | h⟩ | ⟨hcyc, h⟩ | ⟨h1p2, h⟩ | ⟨hEA, h8, _⟩ |
    ⟨hcyc, h | h⟩ | ⟨r, m, hpm, hr2, hEAr, hrk, _⟩ | ⟨hEA, h6, _⟩
  · exfalso; have := hcyc.2; omega
  · exfalso; have := hcyc.2; omega
  · exfalso; have := hcyc.2; omega
  · exfalso; have := hcyc.2; omega
  · exfalso
    haveI := h1p2.1
    have hc3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
    rw [s16c1610_n3_center_eq_top hcommL, Subgroup.card_top] at hc3
    omega
  · exfalso
    have := A38.card_eq_of_isElemAbelianOfRank (q := 3) (n := 2) (by norm_num) hEA
    omega
  · exfalso; have := hcyc.2; omega
  · exfalso; have := hcyc.2; omega
  · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hp3 : 3 ^ r = 27 := by
        rw [← hcardL]
        exact (A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEAr).symm
      have hp33 : 3 ^ r = 3 ^ 3 := by rw [hp3]; norm_num
      have hr : r = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hp33
      rw [hr] at hrk
      rw [hrk]
    · exfalso
      have hp7 : 7 ^ r = 27 := by
        rw [← hcardL]
        exact (A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 7) hEAr).symm
      have h7 : 7 ^ 2 ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
      rw [hp7] at h7
      norm_num at h7
  · exfalso
    have := A38.card_eq_of_isElemAbelianOfRank (q := 3) (n := 2) (by norm_num) hEA
    omega

theorem s16c1610_lBar_normal_of_case4_three (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h4 : Case168_4At D V₀ V hV L 3 3) :
    ∀ m ∈ Mbar D.M V₀ V hV, ∀ x ∈ lBar V₀ V hV L,
      m * x * m⁻¹ ∈ lBar V₀ V hV L := by
  classical
  obtain ⟨t, htA, ht2, ht1, htrk, hW136⟩ := hc.conc
  obtain ⟨hsupW, hnormW, hthird⟩ := hW136
  have hcardL : Nat.card ↥(lBar V₀ V hV L) = 27 := by
    have h := A38.card_eq_of_isElemAbelianOfRank (q := 3) (n := 3) (by norm_num) h4.1
    simpa using h
  have hcommL : ∀ a b : ↥(lBar V₀ V hV L), a * b = b * a :=
    s16c1610_n3_comm_of_isElemAbelianOfRank h4.1
  have hrkW : rk (Vtil V₀ V hV) = 8 := by
    have h := s16c1610_rk_of_symSumOfConj h4.2.1
    rw [s16c1610_dParam_three] at h
    simpa using h
  have hrk8 : rk ↥(commSub ⊤ (lBar V₀ V hV L)) = 8 := by
    rcases hthird with h133 | ⟨K, hKmem, g, hgA, hKg, hLK, htens⟩ |
      ⟨hcomp3, _, _⟩ | ⟨_, _, hcomp4, _⟩
    · exact s16c1610_n3_rk_commSub_eq_eight_of_conc4133 hcommL hcardL h133
    · exfalso
      have hKL : K ≤ lBar V₀ V hV L := by rw [hLK]; exact le_sup_left
      have hcommK : ∀ a b : ↥K, a * b = b * a := by
        intro a b
        apply Subtype.ext
        simpa using congrArg Subtype.val (hcommL ⟨(a : MulAut (Vtil V₀ V hV)), hKL a.2⟩
          ⟨(b : MulAut (Vtil V₀ V hV)), hKL b.2⟩)
      exact s16c1610_n3_false_of_isQuasisimple_of_comm hcommK hKmem.2.2
    · exfalso
      exact s16c1610_n3_false_of_isQuasisimple_of_comm hcommL hcomp3.2.2
    · exfalso
      exact s16c1610_n3_false_of_isQuasisimple_of_comm hcommL hcomp4.2.2
  have hcommSubTop : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    refine eq_of_le_of_rk_le (Vtil_pow_two hV) le_top ?_
    rw [rk_top, hrkW, hrk8]
  intro m hm x hx
  by_cases hmN : m ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))
  · exact (Subgroup.mem_normalizer_iff.mp hmN x).mp hx
  · exfalso
    have hbot := (hnormW m hm hmN).2
    rw [hcommSubTop] at hbot
    have hmapbot : (lBar V₀ V hV L).map (MulAut.conj m).toMonoidHom = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro φ hφ
      apply MulEquiv.ext
      intro v
      exact (mem_fixV.mp (commSub_eq_bot_iff.mp hbot (Subgroup.mem_top v))) φ hφ
    have hcardmap : Nat.card ↥((lBar V₀ V hV L).map (MulAut.conj m).toMonoidHom) = 27 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hcardL]
    rw [hmapbot, Subgroup.card_bot] at hcardmap
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
