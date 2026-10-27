module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQ
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open Matrix

theorem transvection_commute_diagonal {K : Type} [Field K] {i j : Fin 4} {d : Fin 4 → K}
    (hd : d i = d j) (t : K) :
    Matrix.diagonal d * Matrix.transvection i j t =
      Matrix.transvection i j t * Matrix.diagonal d := by
  apply commute_diagonal_of_support
  intro a b h
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at h
  by_cases hab : a = b
  · rw [hab]
  · rw [if_neg hab, zero_add] at h
    by_cases hij' : i = a ∧ j = b
    · rw [← hij'.1, hd, ← hij'.2]
    · rw [if_neg hij'] at h
      exact absurd rfl h

theorem exists_statedSL_rootGroup {K : Type} [Field K] {i j : Fin 4} (hij : i ≠ j) :
    ∃ φ : Multiplicative K →* StatedSL 4 K, Function.Injective φ ∧
      ∀ (a : Multiplicative K) (d : Fin 4 → K), d i = d j →
        Matrix.diagonal d * ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d := by
  let M : K → Matrix (Fin 4) (Fin 4) K := fun t => Matrix.transvection i j t
  have h0 : M 0 = 1 := Matrix.transvection_zero i j
  have hadd : ∀ a b : K, M (a + b) = M a * M b := fun a b =>
    (Matrix.transvection_mul_transvection_same i j hij a b).symm
  let ψ : Multiplicative K →* GL (Fin 4) K :=
    CFSG.SectionRank.ClassicalOdd.glOfAdd M h0 hadd
  have hψinj : Function.Injective ψ := by
    apply CFSG.SectionRank.ClassicalOdd.glOfAdd_injective
    intro a b hab
    have h := congrFun (congrFun hab i) j
    simpa [M, Matrix.transvection, Matrix.one_apply_ne hij] using h
  let φ : Multiplicative K →* StatedSL 4 K := ψ.codRestrict (StatedSL 4 K) fun a => by
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    change (Matrix.transvection i j a.toAdd).det = 1
    exact Matrix.det_transvection_of_ne i j hij a.toAdd
  refine ⟨φ, ?_, ?_⟩
  · intro a b hab
    exact hψinj (Subtype.ext_iff.mp hab)
  · intro a d hd
    change Matrix.diagonal d * ((ψ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((ψ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d
    rw [show ((ψ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = M a.toAdd from rfl]
    exact transvection_commute_diagonal hd a.toAdd

theorem le_pRank_centralizer_stdDiagHomH_sl {K : Type} [Field K] [Finite K] {r f : ℕ}
    (hr : r.Prime) (hK : Nat.card K = r ^ f) (ζ : CubeRoot K) (hD : D₀ ζ ≤ StatedSL 4 K)
    (S : Set (Multiplicative (Fin 4 → ZMod 3))) {i j : Fin 4} (hij : i ≠ j)
    (hS : ∀ v ∈ S, Multiplicative.toAdd v i = Multiplicative.toAdd v j) :
    f ≤ CFSG.Open.pRank r (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
  obtain ⟨φ, hφinj, hφd⟩ := exists_statedSL_rootGroup (K := K) hij
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K r := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := r) (f := f) hK
  refine le_pRank_centralizer_of_diag_commuting (K := K) (H := StatedSL 4 K)
    (p := r) (k := f) hr.one_lt (A := Multiplicative K) (fun a b => mul_comm a b)
    (fun a : Multiplicative K =>
      CFSG.SectionRank.ClassicalOdd.pow_char_eq_one (K := K) (V := K) (p := r) a)
    (by rw [Nat.card_congr Multiplicative.toAdd, hK])
    φ hφinj (fun d => d i = d j) (fun a d hd => hφd a d hd)
    (stdDiagHomH ζ hD '' S) ?_
  intro t ht
  obtain ⟨v, hvS, rfl⟩ := ht
  refine ⟨fun k => (ζ.pow (Multiplicative.toAdd v k - ∑ l, Multiplicative.toAdd v l) : K),
    ?_, ?_⟩
  · exact congrArg (fun x => (ζ.pow (x - ∑ l, Multiplicative.toAdd v l) : K)) (hS v hvS)
  · rfl

theorem diagUnit_mem_statedSL {K : Type} [Field K] (x y : Kˣ) :
    diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] ∈ StatedSL 4 K := by
  apply CFSG.Open.StatedAPI.mem_statedSL_of_det
  rw [show ((diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun k => (![x, x⁻¹, y, y⁻¹] k : K)) from rfl, Matrix.det_diagonal,
    Fin.prod_univ_four]
  simp [Units.val_mul]

theorem two_le_pRank_centralizer_stdDiagHomH_univ_sl {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (ζ : CubeRoot K) (hD : D₀ ζ ≤ StatedSL 4 K) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      (stdDiagHomH ζ hD '' (Set.univ : Set (Multiplicative (Fin 4 → ZMod 3))))) := by
  obtain ⟨a, ha⟩ := exists_units_orderOf_eq_prime (K := K) hp hpK
  refine two_le_pRank_centralizer_of_diagTorus (K := K) (H := StatedSL 4 K) hp ha ?_ _ ?_
  · intro x _ y _
    exact diagUnit_mem_statedSL x y
  · intro t ht
    obtain ⟨v, -, rfl⟩ := ht
    change (((stdDiagHom ζ v : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K).IsDiag
    exact monomial_of_normalizes_diag ζ ⟨v, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
