module

public import CFSG.RankThree.PartTwo.Toolkit.BloomMono
public import CFSG.RankThree.PartTwo.Toolkit.Bloom13
public import CFSG.RankThree.PartTwo.Toolkit.BloomGamma
public import CFSG.CharacterTheory.Burnside
public import Certificates.Certificate8171
public import Certificates.Certificate8172

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "GL33" => GL (Fin 3) (ZMod 3)

theorem eq_one_or_neg_one_of_scalar {x : GL33} {c : ZMod 3}
    (hx : (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) = Matrix.scalar (Fin 3) c) : x = 1 ∨ x = -1 := by
  have hc : c ≠ 0 := by
    intro h0
    have := x.isUnit
    rw [hx, h0, map_zero] at this
    exact not_isUnit_zero this
  have key : ∀ d : ZMod 3, d ≠ 0 → d = 1 ∨ d = -1 := by decide
  rcases key c hc with rfl | rfl
  · exact Or.inl (Units.ext (by rw [hx, map_one, Units.val_one]))
  · exact Or.inr (Units.ext (by rw [hx, map_neg, map_one, Units.val_neg, Units.val_one]))

theorem det_neg_one_GL : ((-1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = -1 := by
  rw [Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one]
  decide

theorem det_commutator (a b : GL33) :
    ((a * b * a⁻¹ * b⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
  have hinv : ∀ g : GL33, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det *
      ((g⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := fun g => by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  simp only [Units.val_mul, Matrix.det_mul]
  linear_combination ((b : Matrix (Fin 3) (Fin 3) (ZMod 3)).det *
    ((b⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)).det) * hinv a + hinv b

theorem not_forall_scalar {G : Subgroup GL33} (hG : IsIrreducibleOn G) :
    ¬ ∀ x ∈ G, x = 1 ∨ x = -1 := by
  intro h
  have hinv : ∀ g ∈ G, ∀ w ∈ Submodule.span (ZMod 3) {(Pi.single 0 1 : Fin 3 → ZMod 3)},
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈
        Submodule.span (ZMod 3) {(Pi.single 0 1 : Fin 3 → ZMod 3)} := by
    intro g hg w hw
    rcases h g hg with rfl | rfl
    · rw [Units.val_one, Matrix.one_mulVec]
      exact hw
    · rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
      exact neg_mem hw
  rcases hG _ hinv with h0 | h0
  · exact single_ne_zero 0 ((Submodule.span_singleton_eq_bot).1 h0)
  · have h1 := congrArg (fun W : Submodule (ZMod 3) (Fin 3 → ZMod 3) =>
      Module.finrank (ZMod 3) W) h0
    rw [finrank_span_singleton (single_ne_zero 0), finrank_top, Module.finrank_fin_fun] at h1
    norm_num at h1

theorem le_scalar_of_solvable {G : Subgroup GL33} (hsol : Group.IsSolvable G)
    (hab : ∀ N ≤ G, (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      ∀ x ∈ N, ∃ c : ZMod 3, (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) = Matrix.scalar (Fin 3) c) :
    ∀ x ∈ G, x = 1 ∨ x = -1 := by
  obtain ⟨m, hm⟩ := (Group.isSolvable_def G).1 hsol
  have hstep : ∀ k, (∀ x ∈ (derivedSeries G (k + 1)).map G.subtype, x = 1 ∨ x = -1) →
      ∀ x ∈ (derivedSeries G k).map G.subtype, x = 1 ∨ x = -1 := by
    intro k hk
    have hcomm : ∀ a ∈ (derivedSeries G k).map G.subtype,
        ∀ b ∈ (derivedSeries G k).map G.subtype, a * b = b * a := by
      intro a ha b hb
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ (derivedSeries G (k + 1)).map G.subtype := by
        rw [derivedSeries_succ, Subgroup.map_commutator]
        exact Subgroup.commutator_mem_commutator ha hb
      rcases hk _ hmem with h | h
      · calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
          _ = b * a := by rw [h, one_mul]
      · exfalso
        have h1 := det_commutator a b
        rw [h, det_neg_one_GL] at h1
        exact absurd h1 (by decide)
    have hnorm : ∀ g ∈ G, ∀ x ∈ (derivedSeries G k).map G.subtype,
        g * x * g⁻¹ ∈ (derivedSeries G k).map G.subtype := by
      intro g hg x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_map.2 ⟨_, (derivedSeries_normal G k).conj_mem y hy ⟨g, hg⟩, by simp⟩
    intro x hx
    obtain ⟨c, hc⟩ := hab _ (Subgroup.map_subtype_le _) hnorm hcomm x hx
    exact eq_one_or_neg_one_of_scalar hc
  have hD : ∀ j, ∀ x ∈ (derivedSeries G (m - j)).map G.subtype, x = 1 ∨ x = -1 := by
    intro j
    induction j with
    | zero =>
      intro x hx
      rw [Nat.sub_zero, hm, Subgroup.map_bot, Subgroup.mem_bot] at hx
      exact Or.inl hx
    | succ j ih =>
      by_cases hj : j < m
      · have hmj : m - j = m - (j + 1) + 1 := by omega
        rw [hmj] at ih
        exact hstep _ ih
      · have hmj : m - (j + 1) = m - j := by omega
        rw [hmj]
        exact ih
  intro x hx
  have h0 := hD m x
  rw [Nat.sub_self, derivedSeries_zero] at h0
  exact h0 (Subgroup.mem_map.2 ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)

theorem isSolvable_of_not_dvd {G : Subgroup GL33} (h13 : ¬ 13 ∣ Nat.card G) :
    Group.IsSolvable G := by
  have h1 : Nat.card G ∣ 13 * (2 ^ 5 * 3 ^ 3) := by
    rw [show 13 * (2 ^ 5 * 3 ^ 3) = 11232 by norm_num, ← card_GL33]
    exact Subgroup.card_subgroup_dvd_card G
  have hdvd : Nat.card G ∣ 2 ^ 5 * 3 ^ 3 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h13)).dvd_of_dvd_mul_left
      h1
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 hdvd
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem card_normalizer_of_card_13 {F : Subgroup GL33} (hF : Nat.card F = 13) :
    Nat.card (normalizer (F : Set GL33)) = 78 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hF0 : Nat.card F0 = 13 ^ (Nat.card GL33).factorization 13 := by
    rw [factorization_GL33, card_F0, pow_one]
  have hF1 : Nat.card F = 13 ^ (Nat.card GL33).factorization 13 := by
    rw [factorization_GL33, hF, pow_one]
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hF0 (Sylow.ofCard F hF1)
  rw [Sylow.coe_ofCard] at hg
  rw [hg, ← Nat.card_congr
    (CFSG.RankThree.Asc83Table.normalizerCongr (MulAut.conj g) F0).toEquiv, card_NF0]

theorem isSemilinearNormalizer_of_card {F : Subgroup GL33} (hF : Nat.card F = 13) :
    IsSemilinearNormalizer F := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hFE : Nat.card (FE eK) = 13 ^ (Nat.card GL33).factorization 13 := by
    rw [factorization_GL33, card_FE, pow_one]
  have hF1 : Nat.card F = 13 ^ (Nat.card GL33).factorization 13 := by
    rw [factorization_GL33, hF, pow_one]
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hFE (Sylow.ofCard F hF1)
  rw [Sylow.coe_ofCard, FE_conj] at hg
  rw [hg]
  exact isSemilinearNormalizer_FE _ (by rw [← hg]; exact card_normalizer_of_card_13 hF)

theorem exists_card_13 {G : Subgroup GL33} (h13 : 13 ∣ Nat.card G) :
    ∃ F ≤ G, Nat.card F = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 13 h13
  refine ⟨zpowers (x : GL33), (zpowers_le).2 x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

theorem bloomCaseA_of_normal {G F : Subgroup GL33} (hFG : F ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ F, g * x * g⁻¹ ∈ F) (hF : Nat.card F = 13) : BloomCaseA G := by
  have hGN : G ≤ normalizer (F : Set GL33) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hnorm g hg x, fun h => ?_⟩
    have := hnorm g⁻¹ (G.inv_mem hg) _ h
    simpa [mul_assoc] using this
  refine ⟨F, hFG, ⟨fun n hn g => ?_⟩, hF, hGN, isSemilinearNormalizer_of_card hF⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact hnorm g g.2 n hn

theorem bloomCaseB_of_le {G : Subgroup GL33}
    (h : CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ G) : BloomCaseB G := by
  by_cases hG : G = CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3)
  · exact Or.inl hG
  · right
    have hdet : ∀ y : GL33, y ∉ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) →
        (y : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = -1 := by
      intro y hy
      rw [mem_statedSL_iff] at hy
      have hne : (y : Matrix (Fin 3) (Fin 3) (ZMod 3)).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
      have key : ∀ d : ZMod 3, ¬ d = 1 → d ≠ 0 → d = -1 := by decide
      exact key _ hy hne
    obtain ⟨g, hgG, hgSL⟩ : ∃ g ∈ G, g ∉ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
      by_contra hcon
      push Not at hcon
      exact hG (le_antisymm hcon h)
    rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3)
    · exact h hx
    · have hg' : g⁻¹ ∉ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := fun h' =>
        hgSL (by simpa using Subgroup.inv_mem _ h')
      have hgx : g⁻¹ * x ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
        rw [mem_statedSL_iff, Units.val_mul, Matrix.det_mul, hdet _ hg', hdet _ hx]
        decide
      have := G.mul_mem hgG (h hgx)
      rwa [mul_inv_cancel_left] at this

theorem caseAB_of_dvd {G : Subgroup GL33} (h13 : 13 ∣ Nat.card G) :
    BloomCaseA G ∨ BloomCaseB G := by
  obtain ⟨F, hFG, hF⟩ := exists_card_13 h13
  by_cases hnorm : ∀ g ∈ G, ∀ x ∈ F, g * x * g⁻¹ ∈ F
  · exact Or.inl (bloomCaseA_of_normal hFG hnorm hF)
  · right
    push Not at hnorm
    obtain ⟨g, hg, x, hx, hgx⟩ := hnorm
    obtain ⟨F', hF'⟩ : ∃ F', F' = F.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
    have hcard : Nat.card F' = 13 := by
      rw [hF', CFSG.RankThree.Asc83Table.card_map_conj, hF]
    have hmem : g * x * g⁻¹ ∈ F' := by
      rw [hF']
      exact ⟨x, hx, by simp⟩
    have hne : F ≠ F' := fun h => hgx (by rw [h]; exact hmem)
    have hF'G : F' ≤ G := by
      rw [hF']
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact G.mul_mem (G.mul_mem hg (hFG hy)) (G.inv_mem hg)
    exact bloomCaseB_of_le ((statedSL_le_sup hF hcard hne).trans (sup_le hFG hF'G))

theorem caseC_of_not_dvd {G : Subgroup GL33} (hG : IsIrreducibleOn G)
    (h13 : ¬ 13 ∣ Nat.card G) : BloomCaseC G := by
  rcases irreducible_prime_degree_reduction (K := ZMod 3) Nat.prime_three
      (isIrreducibleOn_iff.1 hG) with ⟨H, hHG, -, -, -, hdvd, hndvd⟩ | hmono | ⟨-, -, hab⟩
  · exfalso
    rw [Nat.card_zmod] at hdvd hndvd
    apply h13
    have h13H : 13 ∣ Nat.card H := by
      by_contra h
      apply hndvd
      have hcop : Nat.Coprime (Nat.card H) 13 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h).symm
      exact hcop.dvd_of_dvd_mul_right (show Nat.card H ∣ 2 * 13 by simpa using hdvd)
    exact h13H.trans (Subgroup.card_dvd_of_le hHG)
  · exact bloomCaseC_of_transitiveMonomial hG hmono
  · exact absurd (le_scalar_of_solvable (isSolvable_of_not_dvd h13) hab) (not_forall_scalar hG)

theorem card_G0std : Nat.card G0std = 12 := by
  rw [Nat.card_congr G0Equiv.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem card_dvd_78_of_caseA {G : Subgroup GL33} (hA : BloomCaseA G) : Nat.card G ∣ 78 := by
  obtain ⟨F, -, -, hF, hGN, -⟩ := hA
  have := Subgroup.card_dvd_of_le hGN
  rwa [card_normalizer_of_card_13 hF] at this

theorem monomialDetOne_le_statedSL (L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    monomialDetOne L ≤ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) :=
  inf_le_right

theorem statedSL_le_of_caseB {G : Subgroup GL33} (hB : BloomCaseB G) :
    CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ G := by
  rcases hB with rfl | rfl
  · exact le_rfl
  · exact le_top

theorem twelve_dvd_of_caseB {G : Subgroup GL33} (hB : BloomCaseB G) : 12 ∣ Nat.card G := by
  rw [← card_G0std]
  exact Subgroup.card_dvd_of_le (G0std_le.trans
    ((monomialDetOne_le_statedSL Lstd).trans (statedSL_le_of_caseB hB)))

theorem twelve_dvd_of_caseC {G : Subgroup GL33} (hC : BloomCaseC G) : 12 ∣ Nat.card G := by
  obtain ⟨L, -, -, -, -, -, -, G₀, -, -, ⟨φ⟩, hG₀G, -⟩ := hC
  have h12 : Nat.card G₀ = 12 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  rw [← h12]
  exact Subgroup.card_dvd_of_le hG₀G

theorem pow_24_of_caseC {G : Subgroup GL33} (hC : BloomCaseC G) {g : GL33} (hg : g ∈ G) :
    g ^ 24 = 1 := by
  obtain ⟨L, -, -, -, -, ⟨φ⟩, -, -, -, -, -, -, hGle⟩ := hC
  have : (zpowers (-1 : GL33)).Normal := ⟨fun n hn h => by
    rcases mem_zpowers_neg_one_iff.1 hn with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [mul_neg, mul_one, neg_mul, mul_inv_cancel]
      exact mem_zpowers _⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hGle hg)
  have hcard : Nat.card (monomialDetOne L) = 24 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hy24 : y ^ 24 = 1 := by
    have := pow_card_eq_one' (G := monomialDetOne L) (x := ⟨y, hy⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  rcases mem_zpowers_neg_one_iff.1 hz with rfl | rfl
  · rw [mul_one, hy24]
  · rw [mul_neg_one, Even.neg_pow (by decide), hy24]

theorem cGL_mem_statedSL : cGL ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
  rw [mem_statedSL_iff, ← rdet_ofMat, ofMat_cGL]
  decide

theorem toolkit_clause2 : BloomIrreducibleGL33 := by
  intro G hG
  have hcases : BloomCaseA G ∨ BloomCaseB G ∨ BloomCaseC G := by
    by_cases h13 : 13 ∣ Nat.card G
    · rcases caseAB_of_dvd h13 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (caseC_of_not_dvd hG h13))
  have hA12 : BloomCaseA G → ¬ 12 ∣ Nat.card G := fun hA h12 => by
    have := h12.trans (card_dvd_78_of_caseA hA)
    norm_num at this
  refine ⟨hcases, fun ⟨hA, hB⟩ => hA12 hA (twelve_dvd_of_caseB hB),
    fun ⟨hA, hC⟩ => hA12 hA (twelve_dvd_of_caseC hC), fun ⟨hB, hC⟩ => ?_⟩
  have h24 := pow_24_of_caseC hC (statedSL_le_of_caseB hB cGL_mem_statedSL)
  have h1 : cGL ^ (Nat.gcd 24 13) = 1 := pow_gcd_eq_one.2 ⟨h24, cGL_pow_13⟩
  rw [show Nat.gcd 24 13 = 1 by norm_num, pow_one] at h1
  exact cGL_ne_one h1

end CFSG.RankThree.PartTwo.Toolkit
