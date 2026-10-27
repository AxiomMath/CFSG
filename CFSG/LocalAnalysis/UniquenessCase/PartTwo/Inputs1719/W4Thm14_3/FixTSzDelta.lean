module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin Subgroup CFSG.LieType.Ree

theorem suzukiS_norm_mulVec (a : ℕ) {K : Type} [Field K] (h2 : (2 : K) = 0)
    (u w z0 : K) :
    let M : Matrix (Fin 4) (Fin 4) K := CFSG.Blueprint.suzukiS a u w
    let z : Fin 4 → K := ![z0, 0, 0, 0]
    z + M.mulVec z + M.mulVec (M.mulVec z) + M.mulVec (M.mulVec (M.mulVec z)) =
      ![0, 0, 0, z0 * u ^ (2 ^ (a + 1) + 2)] := by
  dsimp only
  have h1 : (CFSG.Blueprint.suzukiS a u w).mulVec ![z0, 0, 0, 0] =
      ![z0, u * z0, w * z0, CFSG.Blueprint.suzukiN a u w * z0] := by
    ext i
    fin_cases i <;>
      simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
  have h2' : (CFSG.Blueprint.suzukiS a u w).mulVec
        ![z0, u * z0, w * z0, CFSG.Blueprint.suzukiN a u w * z0] =
      ![z0, 0, u ^ (2 ^ (a + 1) + 1) * z0, u ^ (2 ^ (a + 1) + 2) * z0] := by
    ext i
    fin_cases i
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      linear_combination (u * z0) * h2
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      linear_combination (w * z0) * h2
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      linear_combination (CFSG.Blueprint.suzukiN a u w * z0 + u * w * z0) * h2
  have h3' : (CFSG.Blueprint.suzukiS a u w).mulVec ![z0, 0, u ^ (2 ^ (a + 1) + 1) * z0,
        u ^ (2 ^ (a + 1) + 2) * z0] =
      ![z0, u * z0, (w + u ^ (2 ^ (a + 1) + 1)) * z0, CFSG.Blueprint.suzukiN a u w * z0] := by
    ext i
    fin_cases i
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      ring
    · simp [CFSG.Blueprint.suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      linear_combination (z0 * u ^ 2 * u ^ (2 ^ a * 2)) * h2
  rw [h1, h2', h3']
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination (2 * z0) * h2
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination (u * z0) * h2
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination (w * z0 + u ^ (2 ^ (a + 1) + 1) * z0) * h2
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination (CFSG.Blueprint.suzukiN a u w * z0) * h2

theorem exists_fixed_suzukiU_of_norm {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {J J₀ : Subgroup W} {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (π : ↥(CFSG.Blueprint.suzukiGroup a K) →* ↥L)
    (hJinv : ∀ h : ↥L, ∀ u ∈ J, (h : MulAut W) u ∈ J) (hJ₀ : J₀ ≤ fixV L) {M : Type}
    [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a K) M)
    (β : ↥J →* Multiplicative M) (hβs : Function.Surjective β)
    (hβk : ∀ w : ↥J, β w = 1 ↔ (w : W) ∈ J₀)
    (hβe : ∀ (γ : ↥(CFSG.Blueprint.suzukiGroup a K)) (w : ↥J)
      (hw : ((π γ : ↥L) : MulAut W) (w : W) ∈ J),
      β ⟨_, hw⟩ = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (β w))))
    {m : M} (hm : ∀ u v : K, u ≠ 0 → ∃ z : M,
      m = z + ρ (suzukiSElt a K u v) z + ρ (suzukiSElt a K u v) (ρ (suzukiSElt a K u v) z) +
        ρ (suzukiSElt a K u v) (ρ (suzukiSElt a K u v) (ρ (suzukiSElt a K u v) z)))
    (hmD : ∃ l : Kˣ, ρ (suzukiDElt a K l) m ≠ m) :
    ∃ x : W, (∀ u v : K, ((π (suzukiSElt a K u v) : ↥L) : MulAut W) x = x) ∧
      ∃ l : Kˣ, ((π (suzukiDElt a K l) : ↥L) : MulAut W) x ≠ x := by
  classical
  obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd m)
  have hchar : (2 : K) = 0 := (suzuki_frob_data a hK).1
  have h2u : ∀ z : K, z + z = 0 := fun z => by linear_combination z * hchar
  have hS4 : ∀ u v : K, suzukiSElt a K u v ^ 4 = 1 := by
    intro u v
    have hsq : suzukiSElt a K u v ^ 2 =
        suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
      rw [sq, suzukiSElt_mul hK, suzukiSElt_inj]
      exact ⟨by rw [h2u u], by rw [h2u v, zero_add, ← pow_succ]⟩
    have hsq0 : suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) ^ 2 = 1 := by
      rw [sq, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK, suzukiSElt_inj]
      refine ⟨by rw [add_zero], ?_⟩
      simp [h2u, zero_pow (show 2 ^ (a + 1) ≠ 0 by positivity)]
    calc suzukiSElt a K u v ^ 4
        = suzukiSElt a K u v ^ 2 * suzukiSElt a K u v ^ 2 := by group
      _ = suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) *
          suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by rw [hsq]
      _ = 1 := by simpa [sq] using hsq0
  have hkey : ∀ u v : K, u ≠ 0 →
      ((π (suzukiSElt a K u v) : ↥L) : MulAut W) (x : W) = (x : W) := by
    intro u v hu
    obtain ⟨z, hz⟩ := hm u v hu
    obtain ⟨y1, hy1⟩ := hβs (Multiplicative.ofAdd z)
    let g : MulAut W := ((π (suzukiSElt a K u v) : ↥L) : MulAut W)
    let y2 : ↥J := ⟨g (y1 : W), hJinv (π (suzukiSElt a K u v)) y1 y1.2⟩
    let y3 : ↥J := ⟨g (y2 : W), hJinv (π (suzukiSElt a K u v)) y2 y2.2⟩
    let y4 : ↥J := ⟨g (y3 : W), hJinv (π (suzukiSElt a K u v)) y3 y3.2⟩
    let n : ↥J := y1 * y2 * y3 * y4
    have hc2 : β y2 = Multiplicative.ofAdd (ρ (suzukiSElt a K u v) z) := by
      have h := hβe (suzukiSElt a K u v) y1
        (hJinv (π (suzukiSElt a K u v)) y1 y1.2)
      rw [hy1] at h
      simpa using h
    have hc3 : β y3 = Multiplicative.ofAdd
        (ρ (suzukiSElt a K u v) (ρ (suzukiSElt a K u v) z)) := by
      have h := hβe (suzukiSElt a K u v) y2
        (hJinv (π (suzukiSElt a K u v)) y2 y2.2)
      rw [hc2] at h
      simpa using h
    have hc4 : β y4 = Multiplicative.ofAdd
        (ρ (suzukiSElt a K u v) (ρ (suzukiSElt a K u v) (ρ (suzukiSElt a K u v) z))) := by
      have h := hβe (suzukiSElt a K u v) y3
        (hJinv (π (suzukiSElt a K u v)) y3 y3.2)
      rw [hc3] at h
      simpa using h
    have hcn : β n = Multiplicative.ofAdd m := by
      rw [show n = y1 * y2 * y3 * y4 from rfl, map_mul, map_mul, map_mul, hy1, hc2, hc3, hc4,
        ← ofAdd_add, ← ofAdd_add, ← ofAdd_add, ← hz]
    have hg4 : g ^ 4 = 1 := by
      have h1 : (π (suzukiSElt a K u v)) ^ 4 = 1 := by
        rw [← map_pow, hS4 u v, map_one]
      simpa [g] using congrArg (fun h : ↥L => (h : MulAut W)) h1
    have hgn : g (n : W) = (n : W) := by
      have h1 : g (n : W) = g (y1 : W) * g (y2 : W) * g (y3 : W) * g (y4 : W) := by
        simp only [n, Subgroup.coe_mul, map_mul]
      rw [h1]
      have h2 : g (y1 : W) = (y2 : W) := by dsimp only [y2]
      have h3 : g (y2 : W) = (y3 : W) := by dsimp only [y3]
      have h4 : g (y3 : W) = (y4 : W) := by dsimp only [y4]
      have h5 : g (y4 : W) = (y1 : W) := by
        dsimp only [y2, y3, y4]
        have h := congrArg (fun f : MulAut W => f (y1 : W)) hg4
        simpa [pow_succ] using h
      rw [h2, h3, h4, h5]
      simp only [n, Subgroup.coe_mul]
      ac_rfl
    have hd : ((n * x⁻¹ : ↥J) : W) ∈ J₀ := by
      refine (hβk (n * x⁻¹)).mp ?_
      rw [map_mul, map_inv, hcn, hx, mul_inv_cancel]
    have hfixd : g ((n * x⁻¹ : ↥J) : W) = ((n * x⁻¹ : ↥J) : W) := by
      exact (mem_fixV.mp (hJ₀ hd)) g (π (suzukiSElt a K u v)).2
    have hgnx : g ((n : W) * ((x : W))⁻¹) = (n : W) * (x : W)⁻¹ := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hfixd
    have h1 : g ((n : W) * ((x : W))⁻¹) = g (n : W) * (g (x : W))⁻¹ := by
      rw [map_mul, map_inv]
    rw [hgnx, hgn] at h1
    have h2 := mul_left_cancel h1
    exact (inv_injective h2).symm
  have hfix0 : ∀ v : K,
      ((π (suzukiSElt a K 0 v) : ↥L) : MulAut W) (x : W) = (x : W) := by
    intro v
    have hmul : suzukiSElt a K 0 v =
        suzukiSElt a K 1 0 * suzukiSElt a K 1 (v + 1) := by
      rw [suzukiSElt_mul hK, suzukiSElt_inj]
      exact ⟨by rw [h2u 1], by rw [one_pow, one_mul, zero_add, add_assoc, h2u 1, add_zero]⟩
    have hU : π (suzukiSElt a K 0 v) =
        π (suzukiSElt a K 1 0) * π (suzukiSElt a K 1 (v + 1)) := by
      rw [← map_mul, hmul]
    calc ((π (suzukiSElt a K 0 v) : ↥L) : MulAut W) (x : W)
        = ((π (suzukiSElt a K 1 0) * π (suzukiSElt a K 1 (v + 1)) : ↥L) : MulAut W)
            (x : W) := by rw [hU]
      _ = ((π (suzukiSElt a K 1 0) : ↥L) : MulAut W)
            (((π (suzukiSElt a K 1 (v + 1)) : ↥L) : MulAut W) (x : W)) := by
            simp only [Subgroup.coe_mul, MulAut.mul_apply]
      _ = (x : W) := by rw [hkey 1 (v + 1) one_ne_zero, hkey 1 0 one_ne_zero]
  have hD : ∀ l : Kˣ,
      ((π (suzukiDElt a K l) : ↥L) : MulAut W) (x : W) = (x : W) →
        ρ (suzukiDElt a K l) m = m := by
    intro l hfix
    let x' : ↥J := ⟨((π (suzukiDElt a K l) : ↥L) : MulAut W) (x : W),
      hJinv (π (suzukiDElt a K l)) x x.2⟩
    have h1 : β x' = Multiplicative.ofAdd (ρ (suzukiDElt a K l) m) := by
      have h := hβe (suzukiDElt a K l) x (hJinv (π (suzukiDElt a K l)) x x.2)
      rw [hx] at h
      exact h
    have h2 : β x' = Multiplicative.ofAdd m := by
      have hxx : (x' : W) = (x : W) := hfix
      rw [show x' = x from Subtype.ext hxx, hx]
    have h3 := congrArg Multiplicative.toAdd (h1.symm.trans h2)
    simpa using h3
  refine ⟨(x : W), ?_, ?_⟩
  · intro u v
    by_cases hu : u = 0
    · rw [hu]
      exact hfix0 v
    · exact hkey u v hu
  · obtain ⟨l, hl⟩ := hmD
    exact ⟨l, fun hfix => hl (hD l hfix)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
