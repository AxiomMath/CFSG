module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5R2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HE
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3B
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e_false_of_trivial_on_one {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h15 : S21_15C D Ch)
    (h8100 : R8100U2 D) (h1930 : H1930 D) (c : Ctx21 D Ch) (he : CFSG.Open.evenRank G = 3)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = 3)
    {Y : Subgroup G} (hY : Y ∈ conjSetOf D.M L)
    (hbY : ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) : False := by
  classical
  have hYC : Y ∈ calC D.M := by
    obtain ⟨K₀, -, hset₀, hK₀⟩ := uc22s21ru4e_exists_second_member hc2 hL
    rw [hset₀] at hY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    rcases hY with rfl | rfl
    exacts [hL, hK₀]
  have hc2Y : (conjSetOf D.M Y).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hY]; exact hc2
  obtain ⟨eY⟩ := u4x_bar2_equiv hY
  have hSzY : IsSz (Bar2 Y) n := CFSG.Blueprint.LieModel.of_mulEquiv eY hSz
  clear hY hL hc2 hSz eY
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2Y hYC
  have hKm : K ∈ conjSetOf D.M Y := by rw [hset]; simp
  have hc2K : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hKm]; exact hc2Y
  obtain ⟨eK⟩ := u4x_bar2_equiv hKm
  have hSzK : IsSz (Bar2 K) n := CFSG.Blueprint.LieModel.of_mulEquiv eK hSzY
  have hbM : b ∈ D.M := c.hBM hb
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hbK := uc22p2214_mem_normalizer_of_odd hc2K hbM hodd
  have hYM : Y ≤ D.M := hYC.1.le
  have hKM : K ≤ D.M := hK.1.le
  obtain ⟨hcomm, -, -, -, hX, -, hcen⟩ := u4x_bar_structure hYC hK hne hset (Or.inr hSzY)
  obtain ⟨p, hp⟩ := hSg.nonempty
  set π := uc22p21cPi D.M with hπ
  have hker : ∀ w : ↥D.M, (w : G) ∈ pCoreOf 2 D.M ↔ π w = 1 := by
    intro w
    constructor
    · rintro ⟨z, hz, hzw⟩
      have hzw' : z = w := Subtype.ext hzw
      subst hzw'
      exact (QuotientGroup.eq_one_iff z).2 hz
    · intro h
      exact ⟨w, (QuotientGroup.eq_one_iff w).1 h, rfl⟩
  have hsup : ∀ {z : Bar2 D.M}, z ∈ centralizer (barImage D.M Y : Set (Bar2 D.M)) →
      z ∈ centralizer (barImage D.M K : Set (Bar2 D.M)) →
      z ∈ centralizer ((barImage D.M Y ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
        Set (Bar2 D.M)) := by
    intro z hzY hzK
    have h : barImage D.M Y ⊔ barImage D.M K ≤ centralizer (zpowers z : Set (Bar2 D.M)) :=
      sup_le (le_centralizer_iff.1 (zpowers_le.2 hzY)) (le_centralizer_iff.1 (zpowers_le.2 hzK))
    exact le_centralizer_iff.1 h (mem_zpowers z)
  have hbbY : π ⟨b, hbM⟩ ∈ centralizer (barImage D.M Y : Set (Bar2 D.M)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h1 := (hker (⟨b, hbM⟩ * y * ⟨b, hbM⟩⁻¹ * y⁻¹)).1 (hbY y hy)
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hbbK : π ⟨b, hbM⟩ ∉ centralizer (barImage D.M K : Set (Bar2 D.M)) := by
    intro hbbK
    have u : R3Pair D Y K n p :=
      ⟨hYC, hK, hne, hset, hc2Y, hn, hp, h15 h1930 c Y hYC hc2Y n (Or.inl hSzY) p hp⟩
    refine u4p_not_mem_centralizer h869 h1930 c hYC u.pX hb Nat.prime_three (by norm_num) hbo ?_
    rw [hX]
    exact hsup hbbY hbbK
  have hninn : ¬ ∃ y ∈ K, ∀ x ∈ K, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ pCoreOf 2 D.M := by
    rintro ⟨y, hyK, hy⟩
    have hyb : π ⟨y, hKM hyK⟩ ∈ barImage D.M K := ⟨⟨y, hKM hyK⟩, hyK, rfl⟩
    have hz : (π ⟨y, hKM hyK⟩)⁻¹ * π ⟨b, hbM⟩ ∈
        centralizer (barImage D.M K : Set (Bar2 D.M)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have h1 := (hker (⟨b, hbM⟩ * x * ⟨b, hbM⟩⁻¹ *
        (⟨y, hKM hyK⟩ * x * ⟨y, hKM hyK⟩⁻¹)⁻¹)).1 (hy x hx)
      simp only [map_mul, map_inv] at h1
      rw [mul_inv_eq_one] at h1
      calc π x * ((π ⟨y, hKM hyK⟩)⁻¹ * π ⟨b, hbM⟩)
          = (π ⟨y, hKM hyK⟩)⁻¹ * (π ⟨y, hKM hyK⟩ * π x * (π ⟨y, hKM hyK⟩)⁻¹) *
            π ⟨b, hbM⟩ := by group
        _ = (π ⟨y, hKM hyK⟩)⁻¹ * (π ⟨b, hbM⟩ * π x * (π ⟨b, hbM⟩)⁻¹) * π ⟨b, hbM⟩ := by
          rw [h1]
        _ = (π ⟨y, hKM hyK⟩)⁻¹ * π ⟨b, hbM⟩ * π x := by group
    have hyY : π ⟨y, hKM hyK⟩ ∈ centralizer (barImage D.M Y : Set (Bar2 D.M)) :=
      mem_centralizer_iff.2 fun f hf => hcomm f hf _ hyb
    have hzX := hsup (mul_mem (inv_mem hyY) hbbY) hz
    have hb3 : π ⟨b, hbM⟩ ^ 3 = 1 := by
      have h3 : (⟨b, hbM⟩ : ↥D.M) ^ 3 = 1 := Subtype.ext (by
        rw [← hbo]
        simp)
      rw [← map_pow, h3, map_one]
    have hcz : Commute (π ⟨y, hKM hyK⟩) ((π ⟨y, hKM hyK⟩)⁻¹ * π ⟨b, hbM⟩) :=
      mem_centralizer_iff.1 hz _ hyb
    have hy3 : π ⟨y, hKM hyK⟩ ^ 3 * ((π ⟨y, hKM hyK⟩)⁻¹ * π ⟨b, hbM⟩) ^ 3 = 1 := by
      rw [← hcz.mul_pow, mul_inv_cancel_left, hb3]
    have hmem : π ⟨y, hKM hyK⟩ ^ 3 ∈ (barImage D.M Y ⊔ barImage D.M K) ⊓
        centralizer ((barImage D.M Y ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
          Set (Bar2 D.M)) := by
      refine Subgroup.mem_inf.2 ⟨mem_sup_right (pow_mem hyb 3), ?_⟩
      rw [eq_inv_of_mul_eq_one_left hy3]
      exact inv_mem (pow_mem hzX 3)
    rw [hcen, mem_bot] at hmem
    obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hK
    have hyb1 : π ⟨y, hKM hyK⟩ = 1 := u4x_eq_one_of_pow hyb Nat.prime_three
      (by
        rw [← Nat.card_congr e₁.toEquiv]
        exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSzK)
      hmem
    exact hbbK (by simpa [hyb1] using hz)
  obtain ⟨r, hr, hrd, a, haY, hao, hba⟩ := uc22r3e_exists_commute_of_trivial hn hSzY hbo
    (uc22p2214_mem_normalizer_of_odd hc2Y hbM hodd) hbY
  have hAU : zpowers a ∈ uniqueSet D.M :=
    h8100 he Y n n r p hYC hc2Y (h15 h1930 c Y hYC hc2Y n (Or.inl hSzY) p hp)
      (CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSzY) dvd_rfl hr hrd hp
      (zpowers a) (zpowers_le.2 haY) (by rw [Nat.card_zpowers, hao])
  let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hbne : zpowers b ≠ ⊥ := zpowers_ne_bot.2 fun h => by rw [h, orderOf_one] at hbo; omega
  have hane : zpowers a ≠ ⊥ :=
    zpowers_ne_bot.2 fun h => hr.one_lt.ne' (by rw [← hao, h, orderOf_one])
  have hXn : zpowers a ≤ normalizer (zpowers b : Set G) := by
    have h1 : centralizer ({b} : Set G) = centralizer (zpowers b : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact (h1 ▸ zpowers_le.2 (mem_centralizer_singleton_iff.2 hba.symm)).trans
      (centralizer_le_normalizer _)
  obtain ⟨m, hmM, hm⟩ := s21_10 D Ch h1930 c' (zpowers b) hbne (zpowers_le.2 hb) (zpowers a)
    hane ⟨r, hr, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])⟩ hXn hAU
  have hmb : m * b * m⁻¹ = b⁻¹ := hm b (mem_zpowers b)
  by_cases hmY : m ∈ normalizer (Y : Set G)
  ·
    have hmK : m ∈ normalizer (K : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq]
      have h : K.map (MulAut.conj m).toMonoidHom ∈ conjSetOf D.M K := ⟨m, hmM, rfl⟩
      rw [uc22p2214_conjSetOf_eq hKm, hset] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      refine h.resolve_left fun h' => hne ?_
      exact Subgroup.map_injective (f := (MulAut.conj m).toMonoidHom) (MulAut.conj m).injective
        (h'.trans (mem_normalizer_iff_map_conj_eq.1 hmY).symm)
    exact uc22r3g_false_of_inverted _ hbK hmK Nat.prime_three (by norm_num) hbo
      (uc22r3g_not_inner hK (center_eq_bot_of_isSz hK.2.2 hSzK) hbK hninn)
      (uc22r3g_comm_of_isSz hK hSzK) hmb
  ·
    have hYm : Y.map (MulAut.conj m).toMonoidHom = K := by
      have h : Y.map (MulAut.conj m).toMonoidHom ∈ conjSetOf D.M Y := ⟨m, hmM, rfl⟩
      rw [hset] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h.resolve_left fun h' => hmY (mem_normalizer_iff_map_conj_eq.2 h')
    have hbinv : (π ⟨b, hbM⟩)⁻¹ = π ⟨m, hmM⟩ * π ⟨b, hbM⟩ * (π ⟨m, hmM⟩)⁻¹ := by
      have h : (⟨b, hbM⟩ : ↥D.M)⁻¹ = ⟨m, hmM⟩ * ⟨b, hbM⟩ * ⟨m, hmM⟩⁻¹ := Subtype.ext hmb.symm
      have h' := congrArg π h
      simp only [map_mul, map_inv] at h'
      exact h'
    have hinv : (π ⟨b, hbM⟩)⁻¹ ∈ centralizer (barImage D.M K : Set (Bar2 D.M)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ Y.map (MulAut.conj m).toMonoidHom := by rw [hYm]; exact hk
      obtain ⟨y, hy, hyk⟩ := hk'
      have hkeq : k = ⟨m, hmM⟩ * ⟨y, hYM hy⟩ * ⟨m, hmM⟩⁻¹ := Subtype.ext hyk.symm
      subst hkeq
      have hyb := mem_centralizer_iff.1 hbbY (π ⟨y, hYM hy⟩) ⟨⟨y, hYM hy⟩, hy, rfl⟩
      show π (⟨m, hmM⟩ * ⟨y, hYM hy⟩ * ⟨m, hmM⟩⁻¹) * (π ⟨b, hbM⟩)⁻¹ =
        (π ⟨b, hbM⟩)⁻¹ * π (⟨m, hmM⟩ * ⟨y, hYM hy⟩ * ⟨m, hmM⟩⁻¹)
      simp only [map_mul, map_inv]
      rw [hbinv]
      calc π ⟨m, hmM⟩ * π ⟨y, hYM hy⟩ * (π ⟨m, hmM⟩)⁻¹ *
            (π ⟨m, hmM⟩ * π ⟨b, hbM⟩ * (π ⟨m, hmM⟩)⁻¹)
          = π ⟨m, hmM⟩ * (π ⟨y, hYM hy⟩ * π ⟨b, hbM⟩) * (π ⟨m, hmM⟩)⁻¹ := by group
        _ = π ⟨m, hmM⟩ * (π ⟨b, hbM⟩ * π ⟨y, hYM hy⟩) * (π ⟨m, hmM⟩)⁻¹ := by rw [hyb]
        _ = π ⟨m, hmM⟩ * π ⟨b, hbM⟩ * (π ⟨m, hmM⟩)⁻¹ *
            (π ⟨m, hmM⟩ * π ⟨y, hYM hy⟩ * (π ⟨m, hmM⟩)⁻¹) := by group
    exact hbbK (by simpa using inv_mem hinv)

theorem s21_22R3E5R_of_s21_22R3E5R2 {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h15 : S21_15C D Ch)
    (h8100 : R8100U2 D) (h : S21_22R3E5R2 D Ch) : S21_22R3E5R D Ch :=
  fun h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he hpow L hL hc2 n hn hS =>
    h h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he hpow L hL hc2 n hn
      (hS.imp (fun hS => ⟨hS.1, hS.2, fun _ hb hbo _ hY hbY =>
        uc22r3e_false_of_trivial_on_one hSg h869 h15 h8100 h1930 c he hL hc2 hn hS.1 hb hbo hY
          hbY⟩) id)

end CFSG.LocalAnalysis.UniquenessCase.UC22
