module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.F918F1

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovL42

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped Matrix

@[expose] def covMat : Fin 8 → Matrix (Fin 4) (Fin 4) (ZMod 2) := ![
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 0, 1],
  !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1],
  !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0],
  !![0, 0, 1, 1; 1, 0, 0, 1; 0, 1, 0, 1; 1, 1, 1, 0],
  !![0, 1, 0, 0; 1, 1, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0],
  !![0, 1, 0, 1; 1, 0, 1, 1; 1, 1, 0, 0; 0, 1, 1, 0],
  !![0, 1, 1, 1; 1, 1, 1, 0; 0, 0, 1, 1; 0, 0, 1, 0],
  !![0, 1, 1, 0; 0, 1, 1, 1; 1, 0, 0, 1; 1, 1, 0, 1]]

theorem covMat_cube : ∀ i : Fin 8, covMat i * covMat i * covMat i = 1 := by
  decide +kernel

theorem covering : ∀ x : Fin 6 → ZMod 2, x ≠ 0 →
    ∃ i : Fin 8, wedgeMat4 (covMat i) *ᵥ x = x := by
  decide +kernel

theorem exists_moved : ∀ i : Fin 8, ∃ x : Fin 6 → ZMod 2, wedgeMat4 (covMat i) *ᵥ x ≠ x := by
  decide +kernel

theorem det_eq_one_of_unit (M : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 := by
  have hu : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact hu _

@[expose] def covGL (i : Fin 8) : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) where
  val := covMat i
  inv := covMat i * covMat i
  val_inv := by rw [← mul_assoc]; exact covMat_cube i
  inv_val := covMat_cube i

@[expose] def covSL (i : Fin 8) : ↥(StatedSL 4 (ZMod 2)) :=
  ⟨covGL i, Subgroup.subset_closure (det_eq_one_of_unit _)⟩

theorem covSL_pow_three (i : Fin 8) : covSL i ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_succ, pow_two]
  exact covMat_cube i

theorem covL42_holds : CovL42 := by
  intro W _ _ J h w hw
  obtain ⟨π, β, -, -, -, hβs, hβk, hβe⟩ := sl4ExteriorTwo_coord h
  have hinj : Function.Injective β := (injective_iff_map_eq_one β).2 fun a ha =>
    Subtype.ext (Subgroup.mem_bot.1 ((hβk a).1 ha))
  let u : ↥(⊤ : Subgroup W) := ⟨w, Subgroup.mem_top w⟩
  have hx : Multiplicative.toAdd (β u) ≠ 0 := by
    intro h0
    have h1 : β u = 1 := by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this
    exact hw (Subgroup.mem_bot.1 ((hβk u).1 h1))
  obtain ⟨i, hi⟩ := covering _ hx
  have hfix : ∀ v : ↥(⊤ : Subgroup W), ∀ hv : ((π (covSL i) : ↥J) : MulAut W) (v : W) ∈
      (⊤ : Subgroup W), β ⟨((π (covSL i) : ↥J) : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (wedgeMat4 (covMat i) *ᵥ Multiplicative.toAdd (β v)) :=
    fun v hv => hβe (covSL i) v hv
  refine ⟨((π (covSL i) : ↥J) : MulAut W), (π (covSL i)).2, ?_, ?_⟩
  · have hg3 : ((π (covSL i) : ↥J) : MulAut W) ^ 3 = 1 := by
      have h3 : (π (covSL i)) ^ 3 = 1 := by rw [← map_pow, covSL_pow_three, map_one]
      simpa using congrArg Subtype.val h3
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hg3) with h1 | h3
    · exfalso
      have hg1 : ((π (covSL i) : ↥J) : MulAut W) = 1 := orderOf_eq_one_iff.1 h1
      obtain ⟨x, hxne⟩ := exists_moved i
      obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd x)
      have hmem : ((π (covSL i) : ↥J) : MulAut W) (v : W) ∈ (⊤ : Subgroup W) :=
        Subgroup.mem_top _
      have e := hfix v hmem
      have e1 : (⟨((π (covSL i) : ↥J) : MulAut W) (v : W), hmem⟩ : ↥(⊤ : Subgroup W)) = v :=
        Subtype.ext (by rw [hg1]; rfl)
      rw [e1, hv] at e
      simp only [toAdd_ofAdd] at e
      exact hxne (Multiplicative.ofAdd.injective e).symm
    · exact h3
  · have hmem : ((π (covSL i) : ↥J) : MulAut W) (u : W) ∈ (⊤ : Subgroup W) :=
      Subgroup.mem_top _
    have e := hfix u hmem
    rw [hi, ofAdd_toAdd] at e
    exact congrArg Subtype.val (hinj e)

end CovL42

end S153G93D

end CFSG.Quasithin
