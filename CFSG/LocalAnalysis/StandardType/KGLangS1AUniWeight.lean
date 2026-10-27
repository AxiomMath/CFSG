module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinWeight

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

theorem kgLangS1A_uni_weight {d m p : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 m K) (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1) (hd : d = p ∨ d = 2 * p)
    {G : Subgroup (GL (Fin d) K)} (hG : TypeA.PGLTor.IsProjElem p G)
    (hab : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x)
    (hGU : ∀ x ∈ G, x ∈ LargeEvenGUSet (Fin d) K (2 ^ m))
    (hcard : p ^ 2 * (Nat.card K - 1) ≤ Nat.card G) :
    ∃ P ∈ UnitaryHigher.primeFormUnitary h (RankThree.PartOne.KCUnitaryModel.idGram K d),
      ∃ a : Fin d → ℤ,
        (∀ x ∈ G, ∀ i j, a i ≠ a j →
          ((P⁻¹ * x * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0) ∧
        ∑ i, a i = 0 ∧ ∃ i j, ¬ (p : ℤ) ∣ a i - a j := by
  classical
  have hp0 : 0 < p := hp.pos
  have hd0 : 0 < d := by rcases hd with h | h <;> omega
  have hp2 : p ≠ 2 := TableBUD.ne_two_of_dvd h hpq
  let H₁ : Subgroup (UnitaryHigher.primeFormUnitary h
      (RankThree.PartOne.KCUnitaryModel.idGram K d)) :=
    { carrier := {u | (u : GL (Fin d) K) ∈ G ∧ u ^ p = 1}
      mul_mem' := by
        rintro u v ⟨hu, hup⟩ ⟨hv, hvp⟩
        refine ⟨G.mul_mem hu hv, ?_⟩
        have huv : Commute u v := Subtype.ext (hab _ hu _ hv)
        rw [huv.mul_pow, hup, hvp, one_mul]
      one_mem' := ⟨G.one_mem, one_pow _⟩
      inv_mem' := by
        rintro u ⟨hu, hup⟩
        exact ⟨G.inv_mem hu, by rw [inv_pow, hup, inv_one]⟩ }
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq H₁
    (fun x hx y hy => Subtype.ext (hab _ hx.1 _ hy.1)) (fun x hx => hx.2)
  obtain ⟨a, ha, hsum, hneq⟩ := kgLangS1A_weight_of_diag hp hp2 hd hG hab hcard
    (A := (P : GL (Fin d) K)⁻¹) (fun y hy hyp i j hij => by
      have hyU : y ∈ UnitaryHigher.primeFormUnitary h
          (RankThree.PartOne.KCUnitaryModel.idGram K d) :=
        TableBUD.mem_primeFormUnitary_of_pow_eq_one h hpq hd0 (hGU y hy) (g := y) (c := 1)
          (by simp) hyp
      have hdiag := hP ⟨y, hyU⟩ ⟨hy, Subtype.ext (by rw [Subgroup.coe_pow, hyp]; rfl)⟩
      have hPg : ((P⁻¹ * ⟨y, hyU⟩ * P : UnitaryHigher.primeFormUnitary h
            (RankThree.PartOne.KCUnitaryModel.idGram K d)) : GL (Fin d) K) =
          (P : GL (Fin d) K)⁻¹ * y * (P : GL (Fin d) K) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hPg] at hdiag
      simpa only [inv_inv, Units.val_mul] using hdiag (i := i) (j := j) hij)
  refine ⟨P, P.2, a, ?_, hsum, hneq⟩
  intro x hx i j hij
  have h := ha x hx i j hij
  simp only [Units.val_mul, Subgroup.coe_inv, inv_inv] at h ⊢
  exact h

end CFSG.StandardType
