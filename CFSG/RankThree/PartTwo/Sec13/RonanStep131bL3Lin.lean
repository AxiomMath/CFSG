module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3Diag
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3Fix
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3

open Matrix CFSG.SectionRank.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_GL_three_eq {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q)
    (hq : q % 3 = 1) :
    ∃ i : ℕ, ¬ 3 ∣ i ∧
      Nat.card (GL (Fin 3) K) = 3 * Nat.card (⊤ : Subgroup Kˣ) ^ 3 * i := by
  have := Fintype.ofFinite K
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have hFin : Fintype.card K = 3 * t + 1 := by rw [← Nat.card_eq_fintype_card, hK]
  have hM : Nat.card (⊤ : Subgroup Kˣ) = 3 * t := by
    rw [Subgroup.card_top, Nat.card_units, hK]
    omega
  refine ⟨(3 * t + 1) ^ 3 * (3 * t + 1 + 1) * (3 * t ^ 2 + 3 * t + 1), ?_, ?_⟩
  · intro h
    have := Nat.mod_eq_zero_of_dvd h
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod] at this
  · rw [Matrix.card_GL_field, hM, hFin, Fin.prod_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    have h1 : 1 ≤ (3 * t + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h2 : 3 * t + 1 ≤ (3 * t + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : (3 * t + 1) ^ 2 ≤ (3 * t + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    zify [h1, h2, h3]
    ring

section Sign

variable {K : Type} [Field K]

@[expose] def signSL : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  (signDiag (K := K)).comap SpecialLinearGroup.toGL

@[expose] noncomputable def signProj : Subgroup (projectiveSL 3 K) :=
  (signSL (K := K)).map (proj 3 K)

theorem mem_signSL {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ signSL ↔ SpecialLinearGroup.toGL g ∈ signDiag :=
  Iff.rfl

theorem isPGroup_signProj : IsPGroup 2 (signProj (K := K)) := by
  intro x
  obtain ⟨x, hx⟩ := x
  obtain ⟨g, hg, rfl⟩ := hx
  have hg' : g ∈ signSL := hg
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have h1 : SpecialLinearGroup.toGL g ^ 2 = 1 := sq_eq_one_of_mem_signDiag hg'
  have h2 : g ^ 2 = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, h1, map_one]
  change proj 3 K g ^ 2 ^ 1 = 1
  rw [pow_one, ← map_pow, h2, map_one]

theorem conjAut_mem_signProj {n : GL (Fin 3) K}
    (hn : n ∈ Subgroup.normalizer (signDiag (K := K) : Set (GL (Fin 3) K)))
    {x : projectiveSL 3 K} (hx : x ∈ signProj) : conjAut 3 K n x ∈ signProj := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hg' : g ∈ signSL := hg
  rw [conjAut_proj]
  refine ⟨_, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_signSL,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact (Subgroup.mem_normalizer_iff.mp hn _).mp hg'

theorem signProj_ne_bot (h2 : (2 : K) ≠ 0) : signProj (K := K) ≠ ⊥ := by
  let g₀ : SpecialLinearGroup (Fin 3) K :=
    ⟨diagonal ![1, -1, -1], by simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩
  have hg₀ : SpecialLinearGroup.toGL g₀ = diagHom 3 ![1, -1, -1] := by
    apply Units.ext
    rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_diagHom]
    change diagonal ![(1 : K), -1, -1] = _
    congr 1
    funext i
    fin_cases i <;> simp
  have hmem : g₀ ∈ signSL := by
    rw [mem_signSL, hg₀]
    exact ⟨![1, -1, -1], rfl, fun i => by fin_cases i <;> simp, by simp⟩
  intro hbot
  have hx : proj 3 K g₀ ∈ signProj := ⟨g₀, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot, proj_eq_one_iff] at hx
  obtain ⟨c, -, hc⟩ := hx
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [g₀, Matrix.scalar_apply] at h00 h11
  exact h2 (by linear_combination h00 - h11)

end Sign

theorem mem_range_conjAut_of_pow_three {p e : ℕ} [Fact p.Prime] (he1 : 1 ≤ e) (he2 : e ≤ 2)
    {σ : MulAut (projectiveSL 3 (GaloisField p e))} (hσ : σ ^ 3 = 1) :
    σ ∈ (conjAut 3 (GaloisField p e)).range := by
  by_contra hnot
  rw [← linearAutGroup_eq_range] at hnot
  obtain ⟨τ, hτ, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (by norm_num) σ hσ hnot
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have h3 := (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
    (Fact.out : p.Prime) he1 hK hτ).1
  omega

theorem norm2e_projectiveSL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hq : p ^ e % 3 = 1) (P : Subgroup (MulAut (projectiveSL 3 (GaloisField p e))))
    (hP : IsPGroup 3 P) (hP3 : ∀ σ ∈ P, σ ^ 3 = 1) :
    ∃ V : Subgroup (projectiveSL 3 (GaloisField p e)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  obtain ⟨i, hi3, hGL⟩ := card_GL_three_eq hK hq
  have hNcard : Nat.card ↥(diagSub (⊤ : Subgroup (GaloisField p e)ˣ) ⊔
      Subgroup.zpowers (cycGL : GL (Fin 3) (GaloisField p e))) =
      3 * Nat.card (⊤ : Subgroup (GaloisField p e)ˣ) ^ 3 := card_diagSub_sup_cyc _
  have hN : ¬ 3 ∣ (diagSub (⊤ : Subgroup (GaloisField p e)ˣ) ⊔
      Subgroup.zpowers (cycGL : GL (Fin 3) (GaloisField p e))).index := by
    rw [index_eq_of_card_eq _ (i := i) (by rw [hNcard]; exact hGL)]
    exact hi3
  have h2 : (2 : GaloisField p e) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p e) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).mp h'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  exact exists_stable_subgroup (conjAut 3 (GaloisField p e)) hN (signProj_ne_bot h2)
    isPGroup_signProj
    (fun n hn x hx => conjAut_mem_signProj (diagSub_sup_cyc_le_normalizer_signDiag ⊤ hn) hx) hP
    (fun σ hσ => mem_range_conjAut_of_pow_three he1 he2 (hP3 σ hσ))

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3
