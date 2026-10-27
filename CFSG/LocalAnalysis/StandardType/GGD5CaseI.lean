module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module
open scoped Matrix

private lemma lup10ci_linearIndependent_of_dual
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {φ : ι → Module.Dual (ZMod p) V}
    {A : Matrix ι ι (ZMod p)} (hdet : A.det ≠ 0)
    (hpair : ∀ i j, φ i (v j) = A i j) :
    LinearIndependent (ZMod p) v := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have h1 : ∀ k, ∑ j ∈ s, c j * A k j = 0 := by
    intro k
    have h := congrArg (φ k) hc
    simp only [map_sum, map_smul, smul_eq_mul, hpair, map_zero] at h
    simpa using h
  let c' : ι → ZMod p := fun j => if j ∈ s then c j else 0
  have h2 : Matrix.mulVec A c' = 0 := by
    ext k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    calc ∑ j, A k j * c' j
        = ∑ j, if j ∈ s then A k j * c j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j ∈ s <;> simp [c', hj]
      _ = ∑ j ∈ s, A k j * c j := by rw [Finset.sum_ite_mem_eq]
      _ = ∑ j ∈ s, c j * A k j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_comm]
      _ = 0 := h1 k
  have hc' : c' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet h2
  have : c' i = 0 := congrFun hc' i
  simpa [c', hi] using this

private lemma lup10ci_D5_matrix :
    (CartanMatrix.D 5).map (Int.cast : ℤ → ZMod 3) =
      !![2, 2, 0, 0, 0;
         2, 2, 2, 0, 0;
         0, 2, 2, 2, 2;
         0, 0, 2, 2, 0;
         0, 0, 2, 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma lup10ci_D5_det : ((CartanMatrix.D 5).map (Int.cast : ℤ → ZMod 3)).det ≠ 0 := by
  rw [lup10ci_D5_matrix]
  have hBA : (!![1, 1, 1, 2, 2;
                 1, 2, 2, 1, 1;
                 1, 2, 0, 0, 0;
                 2, 1, 0, 2, 0;
                 2, 1, 0, 0, 2] : Matrix (Fin 5) (Fin 5) (ZMod 3)) *
             (!![2, 2, 0, 0, 0;
                2, 2, 2, 0, 0;
                0, 2, 2, 2, 2;
                0, 0, 2, 2, 0;
                0, 0, 2, 0, 2] : Matrix (Fin 5) (Fin 5) (ZMod 3)) = 1 := by
    decide
  exact Matrix.det_ne_zero_of_left_inverse hBA

theorem lup10d_caseI {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hV : Submodule.span (ZMod p)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    (hp : p = 3) : M.toLin.Basis := by
  subst hp
  classical
  let A : Matrix (Fin 5) (Fin 5) (ZMod 3) := (CartanMatrix.D 5).map (Int.cast : ℤ → ZMod 3)
  have hdet : A.det ≠ 0 := by
    dsimp [A]
    exact lup10ci_D5_det
  have hpairA : ∀ k l : Fin 5, M.root (e k) (M.coroot (e l)) = A k l := by
    intro k l
    rw [M.pairing]
    dsimp [A]
    rw [hecart]
  have hind : LinearIndependent (ZMod 3) (fun l : Fin 5 => M.coroot (e l)) :=
    lup10ci_linearIndependent_of_dual hdet hpairA
  have hind' : LinearIndependent (ZMod 3) M.coroot := by
    have h := hind.comp e.symm e.symm.injective
    simpa [Function.comp_def] using h
  have hcardι : Fintype.card M.ι = 5 := by
    simpa using (Fintype.card_congr e).symm
  let U : Finset M.V :=
    Finset.image (fun i : {k // k ≠ M.a} => M.coroot i) Finset.univ
  let T : Finset M.V := insert M.xV U
  have hTS : (T : Set M.V) = insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
    ext v
    simp [T, U]
  have hspan : Submodule.span (ZMod 3) (T : Set M.V) = ⊤ := by
    rw [hTS]
    exact hV
  have hcard4 : Fintype.card {k : M.ι // k ≠ M.a} = 4 := by
    simp [hcardι]
  have hTcard : T.card ≤ 5 := by
    have hcardimg : U.card ≤ 4 := by
      dsimp only [U]
      calc (Finset.image (fun i : {k // k ≠ M.a} => M.coroot i) Finset.univ).card
          ≤ (Finset.univ : Finset {k // k ≠ M.a}).card := Finset.card_image_le
        _ = 4 := by simpa using hcard4
    calc T.card = (insert M.xV U).card := rfl
      _ ≤ U.card + 1 := Finset.card_insert_le _ _
      _ ≤ 5 := by omega
  have htop : Module.Finite (ZMod 3) (⊤ : Submodule (ZMod 3) M.V) := by
    rw [← hspan]
    infer_instance
  have hge : 5 ≤ Module.finrank (ZMod 3) M.V := by
    have hli : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range fun l : Fin 5 => M.coroot (e l))) = 5 := by
      rw [finrank_span_eq_card hind]
      simp
    have hle : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range fun l : Fin 5 => M.coroot (e l))) ≤
        Module.finrank (ZMod 3) M.V := by
      have hmono := Submodule.finrank_mono (s := Submodule.span (ZMod 3)
        (Set.range fun l : Fin 5 => M.coroot (e l))) (t := ⊤) le_top
      simpa using hmono
    omega
  have hle : Module.finrank (ZMod 3) M.V ≤ 5 := by
    have h1 : Module.finrank (ZMod 3) M.V ≤ T.card := by
      have h := finrank_span_finset_le_card (R := ZMod 3) T
      rw [Set.finrank, hspan, finrank_top] at h
      exact h
    omega
  constructor
  · exact hind'
  · change Fintype.card M.ι = Module.finrank (ZMod 3) M.V
    rw [hcardι]
    exact (le_antisymm hle hge).symm

end CFSG.StandardType

end
