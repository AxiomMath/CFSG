module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D1
public import CFSG.Quasithin.Vol2.Ch3E213MP6CB

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ClassicalGroups.Alternating (symplecticTransvection)

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem bil_single (x : Fin 4 → k) (i : Fin 4) : spBil x (Pi.single i 1) = x (Fin.rev i) := by
  fin_cases i <;> simp [bil_apply, Fin.rev]

@[expose] noncomputable def ofBasis (e : Fin 4 → Fin 4 → k)
    (he : ∀ s t, spBil (e s) (e t) = minorJ k s t) : antiSp k :=
  let Z : Matrix (Fin 4) (Fin 4) k := Matrix.of fun r s => e s r
  have hJ : Z.transpose * minorJ k * Z = minorJ k := by
    ext s t
    rw [transpose_mul_minorJ_mul_apply, ← he, bil_apply]
    simp [Z]
  have hleft : (minorJ k * Z.transpose * minorJ k) * Z = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Z.transpose, hJ, minorJ_mul_self]
  ⟨⟨Z, minorJ k * Z.transpose * minorJ k, mul_eq_one_comm.mp hleft, hleft⟩, hJ⟩

omit [CharP k 2] in
theorem act_ofBasis_single (e : Fin 4 → Fin 4 → k)
    (he : ∀ s t, spBil (e s) (e t) = minorJ k s t) (j : Fin 4) :
    natAct (ofBasis e he) (Pi.single j 1) = e j := by
  ext r
  simp [ofBasis, natAct, glMat, Matrix.mulVec, dotProduct, Pi.single_apply]

omit [CharP k 2] in
theorem act_ofBasis (e : Fin 4 → Fin 4 → k) (he : ∀ s t, spBil (e s) (e t) = minorJ k s t)
    (x : Fin 4 → k) : natAct (ofBasis e he) x = ∑ j, x j • e j := by
  conv_lhs => rw [show x = ∑ j, x j • Pi.single j (1 : k) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [natAct, Matrix.mulVec_sum, Matrix.mulVec_smul]
  congr 1
  ext j
  rw [← natAct, act_ofBasis_single]

theorem subAntiSp_trv (F₀ : Subfield k) (v : Fin 4 → F₀) (c : F₀) :
    subAntiSp F₀ (trv v c) = trv (fun i => (v i : k)) (c : k) := by
  apply antiSp_ext
  rw [glMat_subAntiSp, glMat_trv, glMat_trv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat]

theorem closure_trv_eq_top (K : Type) [Field K] [CharP K 2] :
    Subgroup.closure {g : antiSp K | ∃ (v : Fin 4 → K) (c : K), g = trv v c} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : GL (Fin 4) K) ∈
      (Subgroup.closure {g : antiSp K | ∃ (v : Fin 4 → K) (c : K), g = trv v c}).map
        (antiSp K).subtype := by
    rw [MonoidHom.map_closure]
    have hset : (antiSp K).subtype '' {g : antiSp K | ∃ (v : Fin 4 → K) (c : K), g = trv v c} =
        {g | ∃ (v : Fin 4 → K) (t : K), g = Matrix.GeneralLinearGroup.toLin.symm
          (symplecticTransvection (minorForm K) minorForm_isAlt v t)} := by
      ext y
      constructor
      · rintro ⟨_, ⟨v, c, rfl⟩, rfl⟩
        exact ⟨v, c, rfl⟩
      · rintro ⟨v, c, rfl⟩
        exact ⟨trv v c, ⟨v, c, rfl⟩, rfl⟩
    rw [hset, ← antiSp_eq_closure]
    exact g.2
  obtain ⟨y, hy, hyg⟩ := hg
  rwa [Subtype.coe_injective hyg] at hy

theorem subfieldSp_le_closure (F₀ : Subfield k) :
    subfieldSp F₀ ≤ Subgroup.closure
      {g | ∃ (v : Fin 4 → F₀) (c : F₀), g = trv (fun i => (v i : k)) (c : k)} := by
  rw [← range_subAntiSp, MonoidHom.range_eq_map, ← closure_trv_eq_top, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨_, ⟨v, c, rfl⟩, rfl⟩
  exact ⟨v, c, subAntiSp_trv F₀ v c⟩

variable {G₀ : Subgroup (antiSp k)} {F₀ : Subfield k}

omit [CharP k 2] in
theorem coord_eq_bil (x : Fin 4 → k) (i : Fin 4) : x i = spBil x (Pi.single (Fin.rev i) 1) := by
  rw [bil_single, Fin.rev_rev]

theorem spW_of_basis [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) (e : Fin 4 → Fin 4 → k)
    (he : ∀ s t, spBil (e s) (e t) = minorJ k s t)
    (hnorm : ∀ c : Fin 4 → k, (∀ j, c j ∈ F₀) → c ≠ 0 → IsNorm G₀ F₀ (∑ j, c j • e j)) :
    G41SpW G₀ := by
  have hej : ∀ j, IsNorm G₀ F₀ (e j) := by
    intro j
    have := hnorm (Pi.single j 1) (fun l => by
      rw [Pi.single_apply]; split_ifs
      exacts [F₀.one_mem, F₀.zero_mem]) (by simp)
    simpa [Pi.single_apply] using this
  refine ⟨F₀, ofBasis e he, le_antisymm ?_ ?_⟩
  · intro g hg
    refine ⟨(ofBasis e he)⁻¹ * g * ofBasis e he, fun i j => ?_, ?_⟩
    · rw [← act_single_apply, natAct_mul, natAct_mul, act_ofBasis_single,
        coord_eq_bil (natAct (ofBasis e he)⁻¹ (natAct g (e j))) i, bil_act_inv,
        act_ofBasis_single]
      exact bil_mem_of_isNorm hk hF4 (isNorm_act (hej j) hg) (hej _)
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro _ ⟨g₀, hg₀, rfl⟩
    have hcl := subfieldSp_le_closure F₀ hg₀
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj (ofBasis e he)).toMonoidHom hcl
    rw [MonoidHom.map_closure] at hmap
    refine (Subgroup.closure_le G₀).mpr ?_ hmap
    rintro _ ⟨_, ⟨v, c, rfl⟩, rfl⟩
    change ofBasis e he * trv (fun i => (v i : k)) (c : k) * (ofBasis e he)⁻¹ ∈ G₀
    rw [conj_trv]
    by_cases hv : (fun i => (v i : k)) = 0
    · rw [hv, act_zero, trv_zero_left]
      exact G₀.one_mem
    · rw [act_ofBasis]
      exact (hnorm _ (fun j => (v j).2) hv).mem c.2

end CFSG.Quasithin.Ch3E213M.G41
