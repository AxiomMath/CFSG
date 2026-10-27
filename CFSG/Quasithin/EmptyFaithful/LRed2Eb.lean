module

public import CFSG.Quasithin.EmptyFaithful.LRed2EbS5
public import CFSG.Quasithin.EmptyFaithful.LRed2EbA
public import CFSG.Quasithin.Background.S1549EB
public import CFSG.Quasithin.Background.FFC4CaseI
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem lred2_classify (hI : FFC.B58Inputs) {M : Type} [CommGroup M] [Finite M]
    {X K : Subgroup (MulAut M)} (hJ : X = ffJ X) (hne : X ≠ ⊥) (hKX : K ≤ X)
    (hnoK : ¬ FFC.ThreeRank2 ↥K) (hnoX : ¬ FFC.ThreeRank2 ↥X) (P2 : B51Part2 K) (P5 : B51Part5 X K)
    (hi : B51Case1i X K) :
    commV K ∈ IrrPlus K ⊤ ∧
      ((X = K ∧ commV K ⊔ fixV K = ⊤ ∧
          ∃ n, BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 2 n) ∨
        (X = K ∧ ∃ m, Odd m ∧ BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 m) ∨
        (X ≠ K ∧ commV K ⊔ fixV X = ⊤ ∧ fixV K ⊓ commV K = ⊥ ∧
          SymmetricNatural X (commV K) (fixV K ⊓ commV K) 5)) := by
  obtain ⟨hirr, hpair, hT⟩ := hi
  refine ⟨hirr, ?_⟩
  obtain ⟨T, hTsyl⟩ := B5.exists_isSylowTwoOf X
  by_cases hXK : X = K
  · subst hXK
    by_cases hα : commV X ⊔ fixV X = ⊤
    · rcases FFC.pairOK_of_pair hI hnoK hpair with hn2 | ⟨m, hm, hn3⟩ | h5
      · exact Or.inl ⟨rfl, hα, hn2⟩
      · exact Or.inr (Or.inl ⟨rfl, m, hm, hn3⟩)
      · exact (FFC.false_of_alt5 hJ hne hα (inf_comm _ _) h5).elim
    · obtain ⟨hirr', hlist5, hZ3⟩ := P5.resolve_left hα
      rcases hlist5 with ⟨n, hn⟩ | h6 | h8 | h3
      · exact (FFC.false_of_sp4 hnoK hn).elim
      · exact (FFC.false_of_alt_ge_six hnoK (by norm_num) h6).elim
      · exact (FFC.false_of_alt_ge_six hnoK (by norm_num) h8).elim
      · exact Or.inr (Or.inl ⟨rfl, 1, odd_one, h3⟩)
  · rcases (hT T hTsyl).resolve_left hXK with ⟨hXKT, hn⟩
    rcases hn with ⟨n, hn5, hn8, hsym⟩ | hg2
    · obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin n) →* ↥X,
          (FFModel.symDn n).RealizesVia X (commV K) (fixV K ⊓ commV K) π := hsym
      by_cases hn5' : n = 5
      · subst hn5'
        have hα : commV K ⊔ fixV X = ⊤ := by
          by_contra hα
          obtain ⟨hirr', hlist5, hZ3⟩ := P5.resolve_left hα
          rcases hlist5 with ⟨m, hm⟩ | h6 | h8 | h3
          · exact FFC.false_of_sp4 hnoK hm
          · exact FFC.false_of_alt_ge_six hnoK (by norm_num) h6
          · exact FFC.false_of_alt_ge_six hnoK (by norm_num) h8
          · obtain ⟨K', hK', hf, hc, ρ, hρ⟩ := h3
            exact FFC.false_of_sl3_sym5 (by simpa using hc) hρ hπ
        have hZ : fixV K ⊓ commV K = ⊥ := FFC.Z_eq_bot_of_s5 hI hKX hnoX hπ P2
        exact Or.inr (Or.inr ⟨hXK, hα, hZ, ⟨π, hπ⟩⟩)
      · exact (hnoX (FFC.threeRank2_of_realizes (FFC.symDn_faithful (by omega)) hπ
          (FFC.threeRank2_perm (by omega)))).elim
    · exact (FFC.false_of_g2 hI hnoX hg2).elim

private theorem lred2_not_threeRank2_of_mem {G : Type*} [Group G] {L J : Subgroup G}
    (hmem : ∀ z ∈ J, z ^ 3 = 1 → z ∈ L) (hL : ¬ FFC.ThreeRank2 ↥L) : ¬ FFC.ThreeRank2 ↥J := by
  rintro ⟨x, y, hx1, hx3, hy3, hxy, hy⟩
  have hxL : (x : G) ∈ L := hmem x x.2 (by simpa using congrArg Subtype.val hx3)
  have hyL : (y : G) ∈ L := hmem y y.2 (by simpa using congrArg Subtype.val hy3)
  refine hL ⟨⟨x, hxL⟩, ⟨y, hyL⟩, fun h => hx1 (Subtype.ext (by simpa using congrArg Subtype.val h)),
    Subtype.ext (by simpa using congrArg Subtype.val hx3),
    Subtype.ext (by simpa using congrArg Subtype.val hy3),
    Subtype.ext (by simpa using congrArg Subtype.val hxy), fun hz => hy ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun t : ↥L => ((t : G))) hk
  simpa using this

private theorem lred2_mem_of_cube {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hS2 : IsPGroup 2 ↥S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {z : G} (hz : z ∈ L ⊔ S)
    (hz3 : z ^ 3 = 1) : z ∈ L := by
  obtain ⟨e, he⟩ := InternalSec.two_of_sup hS2 hSL z hz
  have h4 : 4 ^ e % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  obtain ⟨t, ht⟩ : ∃ t, 4 ^ e = 3 * t + 1 := ⟨4 ^ e / 3, by omega⟩
  have hzz : z = (z ^ 2 ^ e) ^ 2 ^ e := by
    rw [← pow_mul, show 2 ^ e * 2 ^ e = 4 ^ e by rw [← mul_pow]; norm_num, ht, pow_succ, pow_mul, hz3,
      one_pow, one_mul]
  rw [hzz]
  exact L.pow_mem he _

theorem l2OffenderNatural_of_b51 (hB51 : AsB51) (hI : FFC.B58Inputs) : S1549E.L2OffenderNatural := by
  intro V _ _ hV X L S Q B K _ _ e he hK hL _ hLn hS hXLS _ hhyp hSQ _ hB hBQ y hy hy3 u hu hyu
  have hconc := hB51 V hV (ffJ X) L hhyp
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  have hSX : S ≤ X := hS.1
  have hSN : S ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => hLn s (hSX hs) l hl, fun h => ?_⟩
    have := hLn s⁻¹ (X.inv_mem (hSX hs)) _ h
    simpa [mul_assoc] using this
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  have hJnorm : X ≤ Subgroup.normalizer ((ffJ X : Subgroup (MulAut V)) : Set (MulAut V)) :=
    B6.le_normalizer_ffJ X
  obtain ⟨-, -, -, hLJ, -, hJJ⟩ := hhyp
  have hmem3 : ∀ z ∈ ffJ X, z ^ 3 = 1 → z ∈ L := fun z hz hz3 =>
    lred2_mem_of_cube hS2 hSN (hXLS (hJX hz)) hz3
  have hnoK := lred2_not_threeRank2_sl2 hK hL
  have hnoJ := lred2_not_threeRank2_of_mem hmem3 hnoK
  have hL0 : L ≠ ⊥ := by
    intro h
    have hc := lred2_card_L hK hL
    rw [h, Subgroup.card_bot] at hc
    have h1 : 2 ^ e = 1 := Nat.eq_one_of_mul_eq_one_right hc.symm
    have h2 : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hne : ffJ X ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLJ))
  have hyL : y ∈ L := hy.2
  obtain ⟨hP1, hP2, -, -, hP5, -⟩ := hconc
  obtain ⟨-, hcases⟩ := hP1
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, hout⟩ := lred2_classify hI hJJ hne hLJ hnoK hnoJ hP2 hP5 hi
    rcases hout with ⟨-, -, n, hn2⟩ | ⟨-, m, -, hn3⟩ | ⟨-, hα, hZ, hsym⟩
    · obtain ⟨K', _, _, hc, π, hπ⟩ := hn2
      exact (lred2_natural_fixed hc hπ hyL hy3 hu hyu).1
    · obtain ⟨K', _, _, hc, π, hπ⟩ := hn3
      exact (lred2_false_sl3 he hK hL hc hπ).elim
    · obtain ⟨π, hπ⟩ := hsym
      exfalso
      have hUZ : commV L ⊓ fixV (ffJ X) = fixV L ⊓ commV L := by
        apply le_antisymm
        · exact fun x hx => ⟨B1.fixV_le_fixV hLJ hx.2, hx.1⟩
        · rw [hZ]
          exact bot_le
      exact lred2_false_of_sym5 hJX hJnorm hS hSQ hB (B19.le_ffJ hB) hBQ hy.1 (hLJ hyL) hy3 hα hUZ hπ
  · exfalso
    obtain ⟨-, n, K', _, _, hc, I, π, -, -, hreal, -, -⟩ := hii
    exact lred2_false_sl3 he hK hL hc (hreal 0)
  · exact (FFC.false_of_case_iii hLJ hnoJ hiii.2).elim
  · exact (FFC.false_of_case_iv hLJ hnoJ hiv.2).elim

end CFSG.Quasithin
