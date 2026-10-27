module

public import CFSG.Quasithin.Background.F420Basic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear

public section

namespace CFSG.Quasithin.F420

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.QuasithinUnique.K1 CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}

theorem charP_two_of_card_two [Finite K] (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])

theorem eq_zero_or_one_of_card_two [Finite K] (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  have h := Finset.eq_univ_of_card _ hc
  have hc' : c ∈ ({0, 1} : Finset K) := h ▸ Finset.mem_univ c
  simpa using hc'

@[expose] def rootZ (hn : 2 ≤ n) : SpecialLinearGroup (Fin n) K :=
  SpecialLinearGroup.transvection (i := (⟨0, by omega⟩ : Fin n)) (j := ⟨n - 1, by omega⟩)
    (fin_mk_ne _ _ (by omega)) 1

theorem centralizer_projUnitriangular_of_card_two [Finite K] (hK : Nat.card K = 2) (hn : 3 ≤ n)
    (x : projectiveSL n K) (hx : ∀ t ∈ projUnitriangular n K, x * t = t * x) :
    x = 1 ∨ x = proj n K (rootZ (by omega)) := by
  have : CharP K 2 := charP_two_of_card_two hK
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  have hcomm : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) →
      (g : Matrix (Fin n) (Fin n) K) * single i j (1 : K) =
        single i j (1 : K) * (g : Matrix (Fin n) (Fin n) K) := by
    intro i j hij
    have hlt : i < j := by
      rw [Fin.lt_def]
      omega
    obtain ⟨T, hTdef⟩ : ∃ T : SpecialLinearGroup (Fin n) K,
        T = SpecialLinearGroup.transvection hlt.ne (1 : K) := ⟨_, rfl⟩
    have hT : proj n K T ∈ projUnitriangular n K := by
      rw [hTdef]
      exact Subgroup.mem_map_of_mem _ (LinearFlag.transvection_mem_unitriangular hlt 1)
    have h1 := hx _ hT
    have h2 : proj n K (g * T * g⁻¹) = proj n K T := by
      rw [map_mul, map_mul, h1, map_inv]
      group
    have hTT : T * T = 1 := by
      rw [hTdef]
      exact transvection_mul_self_of_charTwo hlt.ne 1
    have hgT : (g * T * g⁻¹) * (g * T * g⁻¹) = 1 := by
      calc (g * T * g⁻¹) * (g * T * g⁻¹) = g * (T * T) * g⁻¹ := by group
        _ = 1 := by rw [hTT]; group
    have h3 := eq_of_proj_eq_of_mul_self_eq_one (by omega) hgT hTT h2
    have h4 : g * T = T * g := by
      calc g * T = (g * T * g⁻¹) * g := by group
        _ = T * g := by rw [h3]
    have hTm : (T : Matrix (Fin n) (Fin n) K) = 1 + single i j (1 : K) := by
      rw [hTdef, Matrix.SpecialLinearGroup.transvection_coe]
    have h5 : (g : Matrix (Fin n) (Fin n) K) * (T : Matrix (Fin n) (Fin n) K) =
        (T : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h4]
    rw [hTm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h5
    exact add_left_cancel h5
  obtain ⟨a, b, hab⟩ := eq_smul_one_add_single_of_commute (by omega)
    (g : Matrix (Fin n) (Fin n) K) hcomm
  have ha : a = 1 := by
    rcases eq_zero_or_one_of_card_two hK a with h | h
    · exfalso
      have hdet := g.2
      have hrow : ∀ j : Fin n, (g : Matrix (Fin n) (Fin n) K) ⟨1, by omega⟩ j = 0 := by
        intro j
        rw [hab, h]
        simp
      rw [Matrix.det_eq_zero_of_row_eq_zero _ hrow] at hdet
      exact zero_ne_one hdet
    · exact h
  rcases eq_zero_or_one_of_card_two hK b with hb | hb
  · left
    have : g = 1 := by
      ext i j
      rw [hab, ha, hb, one_smul, zero_smul, add_zero, Matrix.SpecialLinearGroup.coe_one]
    rw [this, map_one]
  · right
    have : g = rootZ (by omega) := by
      ext i j
      rw [hab, ha, hb, one_smul, one_smul, rootZ, Matrix.SpecialLinearGroup.transvection_coe]
    rw [this]

theorem smallCentralizerWitness_projectiveSL_two [Finite K] (hK : Nat.card K = 2) (hn : 3 ≤ n) :
    SmallCentralizerWitness (projectiveSL n K) := by
  have : CharP K 2 := charP_two_of_card_two hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)
  refine ⟨projUnitriangular n K, proj n K (rootZ (by omega)), ?_, fun x hx =>
    centralizer_projUnitriangular_of_card_two hK hn x hx⟩
  rw [← hP]
  exact P.isPGroup'

theorem noFourCentralizing_projectiveSL_two [Finite K] (hK : Nat.card K = 2) (hn : 3 ≤ n) :
    NoFourCentralizing (projectiveSL n K) := by
  have : CharP K 2 := charP_two_of_card_two hK
  refine noFourCentralizing_of_inner (fun S hS α hα => ?_)
    (smallCentralizerWitness_projectiveSL_two hK hn)
  exact sylowCentralizingAutInner_projectiveSL hn S (isSylowTwoOf_top_iff.mpr hS) α hα

theorem noFourCentralizing_of_statedPSL_two {X : Type} [Group X] (hn : 3 ≤ n)
    (h : StatedClassicalModel X .PSL n 2 1) : NoFourCentralizing X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  exact NoFourCentralizing.of_mulEquiv (e.trans (statedProjEquivProjectiveSL n K))
    (noFourCentralizing_projectiveSL_two hK hn)

end CFSG.Quasithin.F420
