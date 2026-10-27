module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAction
public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace KCUnitary

variable {G : Type*} [Group G]

theorem endo_eq_of_central {F Z : Subgroup G} (φ : G →* G) (hF : Group.IsPerfect F)
    (hZ : ∀ z ∈ Z, ∀ g : G, Commute z g) (h : ∀ g ∈ F, φ g * g⁻¹ ∈ Z) :
    ∀ g ∈ F, φ g = g := by
  let f : F →* Z :=
    { toFun := fun g => ⟨φ (g : G) * (g : G)⁻¹, h g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change φ ((a : G) * (b : G)) * ((a : G) * (b : G))⁻¹ =
          (φ (a : G) * (a : G)⁻¹) * (φ (b : G) * (b : G)⁻¹)
        have h1 : φ ((a : G) * (b : G)) * ((a : G) * (b : G))⁻¹ =
            φ (a : G) * (φ (b : G) * (b : G)⁻¹) * (a : G)⁻¹ := by
          rw [map_mul]
          group
        have hc := (hZ _ (h b b.2) (φ (a : G))).eq
        have h2 : φ (a : G) * (φ (b : G) * (b : G)⁻¹) * (a : G)⁻¹ =
            (φ (b : G) * (b : G)⁻¹) * (φ (a : G) * (a : G)⁻¹) := by
          calc φ (a : G) * (φ (b : G) * (b : G)⁻¹) * (a : G)⁻¹
              = ((φ (b : G) * (b : G)⁻¹) * φ (a : G)) * (a : G)⁻¹ := by rw [hc]
            _ = (φ (b : G) * (b : G)⁻¹) * (φ (a : G) * (a : G)⁻¹) := by group
        have h3 := (hZ _ (h a a.2) (φ (b : G) * (b : G)⁻¹)).eq
        rw [h1, h2, ← h3]) }
  have hφ := eq_one_of_perfect_of_comm hF
    (fun a b : Z => Subtype.ext (hZ _ a.2 (b : G)).eq) f
  intro g hg
  have := congrArg Subtype.val (hφ ⟨g, hg⟩)
  exact (mul_inv_eq_one.mp this)

end KCUnitary

namespace KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem primeFormPsi_conj_primeFormConjHom
    (w : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K))
    (A : primeFormUnitary h (idGram K n)) :
    primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) w *
        primeFormConjHom h (idGram K n) A *
          (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) w)⁻¹ =
      primeFormConjHom h (idGram K n) (idUAction h n w A) := by
  obtain ⟨M, σ⟩ := w
  rw [idUAction_mk]
  have h1 := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ A
  rw [primeFormPsi_apply, map_mul, map_mul, map_inv, ← h1]
  group

theorem idUAction_eq_of_centralizes (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {F : Subgroup (primeFormUnitary h (idGram K n))} (hF : Group.IsPerfect F)
    (w : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K))
    (hw : ∀ g ∈ F, primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) w *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) w) :
    ∀ g ∈ F, idUAction h n w g = g := by
  refine endo_eq_of_central (Z := (primeFormConjHom h (idGram K n)).ker)
    (idUAction h n w).toMonoidHom hF (fun z hz g => ?_) (fun g hg => ?_)
  · exact commute_of_mem_ker_of_ne hn hne (MonoidHom.mem_ker.mp hz) g
  · rw [MonoidHom.mem_ker]
    change primeFormConjHom h (idGram K n) (idUAction h n w g * g⁻¹) = 1
    rw [map_mul, map_inv, ← primeFormPsi_conj_primeFormConjHom, hw g hg, mul_inv_cancel_right,
      mul_inv_cancel]

theorem matrix_eq_of_centralizes (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {F : Subgroup (primeFormUnitary h (idGram K n))} (hF : Group.IsPerfect F)
    (M : primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (hw : ∀ g ∈ F, primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, σ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, σ⟩) :
    ∀ g ∈ F, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ *
          (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro g hg
  have h1 := idUAction_eq_of_centralizes hn hne hF ⟨M, σ⟩ hw g hg
  rw [idUAction_mk] at h1
  have h2 := congrArg (fun u : primeFormUnitary h (idGram K n) =>
    ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
  exact h2

end KCUnitaryModel

end CFSG.RankThree.PartOne
