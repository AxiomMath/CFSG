module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveBar
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.RankThree.GF2n.SzExplicit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels CFSG.ShultStronglyClosedTI
open scoped MatrixGroups

theorem rankOne_benderType {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n Y ∨ CFSG.Quasithin.IsSz n Y) :
    BenderType Y n 1 1 ∨ BenderType Y n 2 1 := by
  rcases h with h | h
  · obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := h
    have hn1 : 1 ≤ n := hadm.2.1
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hadm.2.2.2.1 (by simp)
    let e' : Y ≃* PSL(2, GaloisField 2 n) :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (projectiveSpecialLinearFieldEquiv (finiteFieldEquivGaloisField K 2 n (by omega) hcard)
          (Fin 2)))
    exact Or.inl (BenderType.linear n hn2 e')
  · obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := h
    subst hn
    let e' : Y ≃* Sz a :=
      e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
        (glaSzEquivNative a ha hcard))
    exact Or.inr
      (BenderType.suzuki a ha (e'.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))

theorem rankOne_isConj_of_involutions {Y : Type} [Group Y] [Finite Y]
    {n : ℕ} (h : CFSG.Quasithin.IsPSL 2 2 n Y ∨ CFSG.Quasithin.IsSz n Y) {u v : Y}
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv : v * v = 1) (hv1 : v ≠ 1) : IsConj u v := by
  rcases rankOne_benderType h with hB | hB
  · obtain ⟨t, hc⟩ := hB.exists_benderCore (default : Sylow 2 Y)
    exact hc.isConj_of_involutions hu hu1 hv hv1
  · obtain ⟨t, hc⟩ := hB.exists_benderCore (default : Sylow 2 Y)
    exact hc.isConj_of_involutions hu hu1 hv hv1

theorem rankOne_exists_pair_three {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n Y) :
    ∃ u v : Y, u * u = 1 ∧ v * v = 1 ∧ orderOf (u * v) = 3 := by
  obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := h
  have hn1 : 1 ≤ n := hadm.2.1
  let F := GaloisField 2 n
  let e' : Y ≃* PSL(2, F) :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (projectiveSpecialLinearFieldEquiv (finiteFieldEquivGaloisField K 2 n (by omega) hcard)
        (Fin 2)))
  let U : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let L : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hUU : U * U = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hLL : L * L = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hX3 : (U * L) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one]
    rw [pow_succ, pow_succ, pow_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, L, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hX01 : ((U * L : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [U, L, Matrix.mul_apply, Fin.sum_univ_two]
  have hXcenter : U * L ∉ Subgroup.center (SL(2, F)) := by
    intro hx
    obtain ⟨r, -, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
    have h := congrFun (congrFun hscalar 0) 1
    rw [Matrix.scalar_apply, hX01] at h
    exact zero_ne_one h
  let N : Subgroup (SL(2, F)) := Subgroup.center (SL(2, F))
  have hUUq : (U : PSL(2, F)) * (U : PSL(2, F)) = 1 := by
    change (QuotientGroup.mk' N U) * (QuotientGroup.mk' N U) = 1
    rw [← map_mul, hUU, map_one]
  have hLLq : (L : PSL(2, F)) * (L : PSL(2, F)) = 1 := by
    change (QuotientGroup.mk' N L) * (QuotientGroup.mk' N L) = 1
    rw [← map_mul, hLL, map_one]
  have hULord : orderOf ((U : PSL(2, F)) * (L : PSL(2, F))) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hpowq : ((QuotientGroup.mk' N U) * (QuotientGroup.mk' N L)) ^ 3 = 1 := by
      rw [← map_mul, ← map_pow, hX3, map_one]
    have hne : (QuotientGroup.mk' N U) * (QuotientGroup.mk' N L) ≠ 1 := by
      intro hcon
      apply hXcenter
      rw [← map_mul] at hcon
      exact (QuotientGroup.eq_one_iff (U * L)).mp hcon
    change orderOf ((QuotientGroup.mk' N U) * (QuotientGroup.mk' N L)) = 3
    exact orderOf_eq_prime hpowq hne
  refine ⟨e'.symm (U : PSL(2, F)), e'.symm (L : PSL(2, F)), ?_, ?_, ?_⟩
  · rw [← map_mul, hUUq, map_one]
  · rw [← map_mul, hLLq, map_one]
  · rw [← map_mul, MulEquiv.orderOf_eq, hULord]

theorem rankOne_exists_pair_five {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Quasithin.IsSz n Y) :
    ∃ u v : Y, u * u = 1 ∧ v * v = 1 ∧ orderOf (u * v) = 5 := by
  obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := h
  subst hn
  let e' : Y ≃* Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (glaSzEquivNative a ha hcard))
  refine ⟨e'.symm (CFSG.RankThree.GF2n.SzExplicit.w a),
    e'.symm (CFSG.RankThree.GF2n.SzExplicit.u a), ?_, ?_, ?_⟩
  · rw [← map_mul, CFSG.RankThree.GF2n.SzExplicit.w_mul_self, map_one]
  · rw [← map_mul, CFSG.RankThree.GF2n.SzExplicit.u_mul_self, map_one]
  · rw [← map_mul, MulEquiv.orderOf_eq, CFSG.RankThree.GF2n.SzExplicit.orderOf_w_mul_u]

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.exists_benderCore (h : Setting12Two A M n) :
    ∃ (i : ℕ) (S : Sylow 2 (G ⧸ CFSG.Quasithin.kerIn M ⊤)) (t : G ⧸ CFSG.Quasithin.kerIn M ⊤),
      A.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) ≤
          (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ∧
        M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) =
          borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ∧
        BenderCore (2 ^ n) i 1 (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hBex : ∃ i : ℕ, BenderType (G ⧸ CFSG.Quasithin.kerIn M ⊤) n i 1 := by
    rcases rankOne_benderType h.type with hB | hB
    · exact ⟨1, hB⟩
    · exact ⟨2, hB⟩
  obtain ⟨i, hB⟩ := hBex
  obtain ⟨S, hAS⟩ := (h.A_two.map π).exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hBne : borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ≠ ⊤ := hc.strong.1
  have hle : borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ≤ M.map π :=
    b12_TwelveBar_le_map_of_ne_top h (Nbar := borel (S : Subgroup _))
      (hAS.trans (le_borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)))) hBne
  have hSM : (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ≤ M.map π :=
    (le_borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤))).trans hle
  have hMle : M.map π ≤ borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) := by
    haveI := hB.isSimple
    exact hc.le_borel_of_le hSM (b12_TwelveBar_map_ne_top h)
  exact ⟨i, S, t, hAS, le_antisymm hMle hle, hc⟩

theorem Setting12Two.map_involutions_commute (h : Setting12Two A M n)
    {α β : G ⧸ CFSG.Quasithin.kerIn M ⊤}
    (hα : α ∈ M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)))
    (hβ : β ∈ M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)))
    (hα2 : α * α = 1) (hβ2 : β * β = 1) : α * β = β * α := by
  obtain ⟨i, S, t, -, hMS, hc⟩ := h.exists_benderCore
  by_cases hα1 : α = 1
  · subst hα1
    rw [one_mul, mul_one]
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [mul_one, one_mul]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαroot : α ∈ rootCenter (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) :=
    hc.center_of_involution α (hMS ▸ hα)
      (orderOf_eq_prime (by rw [sq]; exact hα2) hα1)
  have hβroot : β ∈ rootCenter (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) :=
    hc.center_of_involution β (hMS ▸ hβ)
      (orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1)
  exact ((mem_rootCenter_iff.mp hαroot).2 β (mem_rootCenter_iff.mp hβroot).1).symm

theorem Setting12Two.exists_cartan_pair (h : Setting12Two A M n) :
    ∃ u v : G ⧸ CFSG.Quasithin.kerIn M ⊤, u * u = 1 ∧ v * v = 1 ∧ u * v ≠ 1 ∧
      Odd (orderOf (u * v)) ∧ u * v ∈ M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) := by
  obtain ⟨i, S, t, -, hMS, hc⟩ := h.exists_benderCore
  have h2n : 3 ≤ 2 ^ n := by
    have hlt : (2 : ℕ) < 2 ^ n := by
      simpa using Nat.pow_lt_pow_right (by norm_num : 1 < 2) h.one_lt_n
    omega
  have hcardD : Nat.card (cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t) =
      (2 ^ n - 1) * 1 := hc.card_cartan
  have hone : 1 < Nat.card (cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t) := by
    rw [hcardD, mul_one]
    omega
  have hDne : cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).mp hone
  obtain ⟨δ, hδ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hsub : {x : G ⧸ CFSG.Quasithin.kerIn M ⊤ |
      x ∈ cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t ∧ t * x * t = x⁻¹} ⊆
      (cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t :
        Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) := fun _ hx => hx.1
  have hle : (cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t :
        Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)).ncard ≤
      {x : G ⧸ CFSG.Quasithin.kerIn M ⊤ |
        x ∈ cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t ∧ t * x * t = x⁻¹}.ncard := by
    rw [hc.ncard_inv]
    change Nat.card (cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t) ≤ 2 ^ n - 1
    rw [hcardD, mul_one]
  have hset : {x : G ⧸ CFSG.Quasithin.kerIn M ⊤ |
      x ∈ cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t ∧ t * x * t = x⁻¹} =
      (cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t :
        Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) :=
    Set.eq_of_subset_of_ncard_le hsub hle
  have hinv : ∀ x ∈ cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t,
      t * x * t = x⁻¹ := by
    intro x hx
    have hx' : x ∈ ({x : G ⧸ CFSG.Quasithin.kerIn M ⊤ |
        x ∈ cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t ∧ t * x * t = x⁻¹} :
        Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) := by
      rw [hset]
      exact hx
    exact hx'.2
  have hinvδ : t * δ * t = δ⁻¹ := hinv δ δ.2
  have huv : t * (t * δ) = (δ : G ⧸ CFSG.Quasithin.kerIn M ⊤) := by
    calc t * (t * δ) = (t * t) * δ := by group
      _ = δ := by rw [hc.sq_eq_one, one_mul]
  have hδne : (δ : G ⧸ CFSG.Quasithin.kerIn M ⊤) ≠ 1 :=
    fun hcon => hδ1 (Subtype.ext hcon)
  refine ⟨t, t * δ, hc.sq_eq_one, ?_, ?_, ?_, ?_⟩
  · calc (t * δ) * (t * δ) = (t * δ * t) * δ := by group
      _ = δ⁻¹ * δ := by rw [hinvδ]
      _ = 1 := inv_mul_cancel (δ : G ⧸ CFSG.Quasithin.kerIn M ⊤)
  · rw [huv]
    exact hδne
  · rw [huv]
    exact Odd.of_dvd_nat hc.odd_card_cartan (Subgroup.orderOf_dvd_natCard _ δ.2)
  · rw [huv, hMS]
    exact cartan_le_borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t δ.2

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81
