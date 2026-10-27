module

public import CFSG.Quasithin.Background.A318PInn
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank

public section

namespace CFSG.Quasithin

namespace A318P

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem sq_mem_of_index_le_two {G : Type*} [Group G] {H : Subgroup G} [H.Normal] [Finite G]
    (h : H.index ≤ 2) (g : G) : g ^ 2 ∈ H := by
  have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card (G ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  have h1 := pow_card_eq_one' (G := G ⧸ H) (x := (g : G ⧸ H))
  rw [hcard] at h1
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h2 | h2
  · rw [h2, pow_one] at h1
    rw [h1, one_pow]
  · rw [h2] at h1
    exact h1

theorem mem_of_index_le_two_of_orderOf_three_pow {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    [Finite G] (hH : H.index ≤ 2) {g : G} {k : ℕ} (hg : orderOf g = 3 ^ k) : g ∈ H := by
  have hsq := sq_mem_of_index_le_two hH g
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k + 1 = 2 * m := by
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    exact ⟨j + 1, by omega⟩
  have hpow : g ^ (3 ^ k) = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have : g = (g ^ 2) ^ m := by
    rw [← pow_mul, ← hm, pow_succ, hpow, one_mul]
  rw [this]
  exact pow_mem hsq m

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
open CFSG.LieType.SteinbergBR.EvenSp in
theorem projEquiv_proj (hn : 1 ≤ 2) (g : StatedSp 2 K) :
    projEquiv hn (proj 2 K g) = g := rfl

omit [Finite K] in
open CFSG.LieType.SteinbergBR.EvenSp in
theorem map_of_mem_zpowers_tGL (σ : K ≃+* K) {g : GL (Fin 2) K}
    (hg : g ∈ Subgroup.zpowers (tGL (K := K))) :
    (g : Matrix (Fin 2) (Fin 2) K).map σ = (g : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h1 : GeneralLinearGroup.map (σ : K →+* K) (tGL (K := K)) = tGL := by
    apply Units.ext
    change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).map σ = !![0, 1; 1, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h2 : GeneralLinearGroup.map (σ : K →+* K) (tGL (K := K) ^ a) = tGL ^ a := by
    rw [map_zpow, h1]
  have h3 := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h2
  exact h3

omit [Finite K] in
open CFSG.LieType.SteinbergBR.EvenSp in
theorem exists_nine_sp4 (σ : K ≃+* K) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), Nat.card E = 9 ∧ CFSG.Open.IsElemAbelian 3 E ∧
      ∀ y ∈ E, fieldAut 2 K σ y = y := by
  have hn : 1 ≤ 2 := by norm_num
  refine ⟨(torusHom (K := K) (n := 2) hn).range, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective hn)).toEquiv, Nat.card_fun,
      Nat.card_zpowers, orderOf_tGL, Nat.card_fin]
    norm_num
  · refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (isElementaryAbelian_range _ (fun x y => funext fun j => Subtype.ext ?_) fun x =>
        funext fun j => Subtype.ext ?_)
    · obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (x j).2
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 (y j).2
      change ((x j : GL (Fin 2) K)) * (y j) = (y j) * (x j)
      rw [← ha, ← hb, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
    · obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (x j).2
      change ((x j : GL (Fin 2) K)) ^ 3 = 1
      rw [← ha, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        tGL_pow_three, _root_.one_zpow]
  · rintro _ ⟨x, rfl⟩
    set g : StatedSp 2 K := ⟨planeHom (fun j => (x j : GL (Fin 2) K)),
      planeHom_mem_statedSp _ fun j => det_of_mem_zpowers (x j).2⟩ with hg
    have h1 : torusHom (K := K) (n := 2) hn x = proj 2 K g := by
      change (projEquiv hn).symm g = proj 2 K g
      exact (MulEquiv.symm_apply_eq _).2 (projEquiv_proj hn g).symm
    have h2 : fieldSp 2 K σ g = g := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_fieldSp]
      change ((planeHom (fun j => (x j : GL (Fin 2) K)) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ = _
      rw [planeHom_val]
      have hent : ∀ (j : Fin 2) (a b : Fin 2),
          σ (((x j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b) =
            ((x j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b := fun j a b =>
        congrFun (congrFun (map_of_mem_zpowers_tGL σ (x j).2) a) b
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [planeMat, Matrix.fromBlocks, Matrix.diagonal_apply] <;>
        split_ifs <;> simp [hent]
    rw [h1, fieldAut_proj, h2]

omit [CharP K 2] in
theorem sp4_three_mem {α : MulAut (StatedProj (StatedSp 2 K))} {k : ℕ} (hα : orderOf α = 3 ^ k) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  obtain ⟨-, -, hnorm, hidx⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  exact mem_spSemilinearAutGroup_iff.1 (mem_of_index_le_two_of_orderOf_three_pow hidx hα)

@[expose] noncomputable def sp4InnFrame (K : Type) [Field K] [Finite K] [CharP K 2] :
    InnFrame (StatedProj (StatedSp 2 K)) (K ≃+* K) where
  fld := fieldAut 2 K
  fld_inter := fun c hc =>
    (fieldAut_mem_range_conjAut_iff (by norm_num)).1 (innAut_le_range_spConjAut 2 K hc)
  three_mem := fun α k hα => by
    obtain ⟨A, σ, rfl⟩ := sp4_three_mem hα
    obtain ⟨y, hy⟩ := conjAut_mem_inner_of_charTwo A
    exact ⟨conjAut 2 K A, ⟨y, hy⟩, σ, rfl⟩
  nine := fun c _ => exists_nine_sp4 c

theorem aut_Sp4 {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) {f : ℕ}
    (hm : StatedClassicalModel ↥S .PSp 2 2 f) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ S := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact innFrame_core hC ((sp4InnFrame K).ofMulEquiv e) hX

end A318P

end CFSG.Quasithin
