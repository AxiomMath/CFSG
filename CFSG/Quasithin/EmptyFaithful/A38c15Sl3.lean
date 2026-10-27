module

public import CFSG.Quasithin.EmptyFaithful.A38c15Line
public import CFSG.RankThree.SubgroupLists.LinearThreeFamily

public section

namespace CFSG.Quasithin.A38c15

open Matrix CFSG.RankThree.SubgroupLists CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

section Irreducible

variable {K : Type*} [Field K]

@[expose] def IsIrreducibleSL3 (M : Subgroup SL(3, K)) : Prop :=
  ∀ W : Submodule K (Fin 3 → K),
    (∀ g ∈ M, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤

theorem exists_line_or_row (M : Subgroup SL(3, K)) (hred : ¬ IsIrreducibleSL3 M) :
    (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ g ∈ M, ∃ c : K,
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v) ∨
      (∃ f : Fin 3 → K, f ≠ 0 ∧ ∀ g ∈ M, ∃ c : K,
        f ᵥ* (g : Matrix (Fin 3) (Fin 3) K) = c • f) := by
  unfold IsIrreducibleSL3 at hred
  push Not at hred
  obtain ⟨W, hW, hbot, htop⟩ := hred
  have hlt : Module.finrank K W < 3 := by
    have := Submodule.finrank_lt htop
    simpa using this
  have hne : Module.finrank K W ≠ 0 := fun h0 => hbot (Submodule.finrank_eq_zero.mp h0)
  have h12 : Module.finrank K W = 1 ∨ Module.finrank K W = 2 := by omega
  rcases h12 with h1 | h2
  · obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
    refine Or.inl ⟨v.1, fun h => hv0 (Subtype.ext h), fun g hg => ?_⟩
    obtain ⟨c, hc⟩ := hv ⟨(g : Matrix (Fin 3) (Fin 3) K) *ᵥ v.1, hW g hg v.1 v.2⟩
    exact ⟨c, congrArg Subtype.val hc.symm⟩
  · obtain ⟨φ, hφ0, hWφ⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr htop)
    have hker : Module.finrank K (LinearMap.ker φ) = 2 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker φ
      have h2 : Module.finrank K (LinearMap.range φ) = 1 := by
        have hle : Module.finrank K (LinearMap.range φ) ≤ 1 := by
          simpa using Submodule.finrank_le (LinearMap.range φ)
        have hne' : Module.finrank K (LinearMap.range φ) ≠ 0 := by
          intro h0
          exact hφ0 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
        omega
      simp at h1
      omega
    have hWeq : W = LinearMap.ker φ := Submodule.eq_of_le_of_finrank_eq hWφ (by rw [h2, hker])
    let f : Fin 3 → K := fun i => φ (fun j => if i = j then 1 else 0)
    have hφf : ∀ x, φ x = f ⬝ᵥ x := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [dotProduct, f, mul_comm]
    obtain ⟨x0, hx0⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hφ0 (LinearMap.ext hcon)
    obtain ⟨u, hu⟩ : ∃ u, φ u = 1 := ⟨(φ x0)⁻¹ • x0, by simp [hx0]⟩
    refine Or.inr ⟨f, ?_, fun g hg => ?_⟩
    · intro hf0
      apply hφ0
      apply LinearMap.ext
      intro x
      rw [hφf, hf0]
      simp
    · refine ⟨φ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u), ?_⟩
      apply dotProduct_eq
      intro x
      rw [← Matrix.dotProduct_mulVec, ← hφf]
      have hx' : x - φ x • u ∈ LinearMap.ker φ := by simp [hu]
      have hx'W : x - φ x • u ∈ W := hWeq ▸ hx'
      have h3 := hW g hg _ hx'W
      rw [hWeq, LinearMap.mem_ker] at h3
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, map_sub, map_smul, smul_eq_mul] at h3
      rw [smul_dotProduct, ← hφf, smul_eq_mul]
      linear_combination h3
end Irreducible

@[expose] def SL3OddIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ M : Subgroup SL(3, ZMod p), Odd M.index →
    IsIrreducibleSL3 M → M = ⊤ ∨ Group.IsSolvable ↥M

theorem exists_sl3_mulVec {v : Fin 3 → ZMod p} (hv : v ≠ 0) :
    ∃ h : SL(3, ZMod p), (h : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ ![0, 0, 1] = v := by
  by_cases h2 : v 2 = 0
  · by_cases h1 : v 1 = 0
    · have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      refine ⟨⟨!![0, 0, v 0; 1, 0, 0; 0, (v 0)⁻¹, 0], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_three]
        field_simp
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]
    · refine ⟨⟨!![1, 0, v 0; 0, 0, v 1; 0, -(v 1)⁻¹, 0], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_three]
        field_simp
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]
  · refine ⟨⟨!![1, 0, v 0; 0, (v 2)⁻¹, v 1; 0, 0, v 2], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_three]
      field_simp
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

section Transpose

variable {R : Type*} [CommRing R]

theorem slT_mul (a b : SL(3, R)) :
    Matrix.SpecialLinearGroup.transpose (a * b) =
      Matrix.SpecialLinearGroup.transpose b * Matrix.SpecialLinearGroup.transpose a :=
  Subtype.ext (by simp [Matrix.transpose_mul])

theorem slT_slT (a : SL(3, R)) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose a) = a :=
  Subtype.ext (by simp)

theorem slT_inv (a : SL(3, R)) :
    Matrix.SpecialLinearGroup.transpose a⁻¹ = (Matrix.SpecialLinearGroup.transpose a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← slT_mul, mul_inv_cancel]
  exact Subtype.ext (by simp)

end Transpose

@[expose] def slTau (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) ≃* SL(3, ZMod p) where
  toFun g := Matrix.SpecialLinearGroup.transpose g⁻¹
  invFun g := Matrix.SpecialLinearGroup.transpose g⁻¹
  left_inv g := by simp [slT_inv, slT_slT]
  right_inv g := by simp [slT_inv, slT_slT]
  map_mul' a b := by simp [slT_mul]

theorem slTau_apply (g : SL(3, ZMod p)) :
    slTau p g = Matrix.SpecialLinearGroup.transpose g⁻¹ := rfl

theorem col3_of_mulVec {X : Matrix (Fin 3) (Fin 3) (ZMod p)} {c : ZMod p}
    (h : X *ᵥ ![0, 0, 1] = c • ![0, 0, 1]) : X 0 2 = 0 ∧ X 1 2 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  exact ⟨h0, h1⟩

theorem exists_aut_of_line (M : Subgroup SL(3, ZMod p)) {v : Fin 3 → ZMod p} (hv : v ≠ 0)
    (hM : ∀ g ∈ M, ∃ c : ZMod p, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = c • v) :
    ∃ φ : SL(3, ZMod p) ≃* SL(3, ZMod p), M.map φ.toMonoidHom ≤ linePar p := by
  obtain ⟨h, hh⟩ := exists_sl3_mulVec hv
  refine ⟨MulAut.conj h⁻¹, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨c, hc⟩ := hM m hm
  have hinv : (h⁻¹ : SL(3, ZMod p)).1 *ᵥ v = ![0, 0, 1] := by
    rw [← hh, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hX : ((MulAut.conj h⁻¹ m : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ ![0, 0, 1] =
      c • ![0, 0, 1] := by
    simp only [MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh, hc, Matrix.mulVec_smul, hinv]
  exact col3_of_mulVec hX

theorem exists_aut_of_row (M : Subgroup SL(3, ZMod p)) {f : Fin 3 → ZMod p} (hf : f ≠ 0)
    (hM : ∀ g ∈ M, ∃ c : ZMod p, f ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = c • f) :
    ∃ φ : SL(3, ZMod p) ≃* SL(3, ZMod p), M.map φ.toMonoidHom ≤ linePar p := by
  have hM' : ∀ g ∈ M.map (slTau p).toMonoidHom, ∃ c : ZMod p,
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ f = c • f := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨c, hc⟩ := hM m⁻¹ (M.inv_mem hm)
    refine ⟨c, ?_⟩
    change ((Matrix.SpecialLinearGroup.transpose m⁻¹ : SL(3, ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ f = c • f
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.mulVec_transpose]
    exact hc
  obtain ⟨φ, hφ⟩ := exists_aut_of_line (M.map (slTau p).toMonoidHom) hf hM'
  refine ⟨(slTau p).trans φ, ?_⟩
  have : M.map ((slTau p).trans φ).toMonoidHom =
      (M.map (slTau p).toMonoidHom).map φ.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [this]
  exact hφ

theorem exists_aut_le_linePar (M : Subgroup SL(3, ZMod p)) (hred : ¬ IsIrreducibleSL3 M) :
    ∃ φ : SL(3, ZMod p) ≃* SL(3, ZMod p), M.map φ.toMonoidHom ≤ linePar p := by
  rcases exists_line_or_row M hred with ⟨v, hv, hM⟩ | ⟨f, hf, hM⟩
  · exact exists_aut_of_line M hv hM
  · exact exists_aut_of_row M hf hM

theorem sylowCore_sl3 (hR1 : GL2OddIndex) (hirr : SL3OddIrr) (hp2 : p ≠ 2) :
    SylowCore p SL(3, ZMod p) := by
  intro M hodd hne
  by_cases hI : IsIrreducibleSL3 M
  · rcases hirr p hp2 M hodd hI with h | h
    · exact absurd h hne
    · exact Or.inl h
  · obtain ⟨φ, hφ⟩ := exists_aut_le_linePar M hI
    have hodd' : Odd (M.map φ.toMonoidHom).index := by
      rwa [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective M]
    rcases sylowCore_line hR1 hp2 _ hφ hodd' with hs | hl
    · left
      exact Group.isSolvable_of_isSolvable_injective
        (f := (M.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom)
        (MulEquiv.injective _)
    · right
      refine IsLeviBlock.of_mulEquiv ?_ hl
      exact (MulEquiv.subgroupCongr (map_perfectCore φ.toMonoidHom M)).symm.trans
        ((perfectCore M).equivMapOfInjective φ.toMonoidHom φ.injective).symm

noncomputable def fieldEquivZMod {K : Type} [Field K] [Finite K] (hK : Nat.card K = p) :
    K ≃+* ZMod p :=
  letI := Fintype.ofFinite K
  (ZMod.ringEquivOfPrime K (Fact.out : p.Prime)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)).symm

theorem sylowCore_of_isSL3 (hR1 : GL2OddIndex) (hirr : SL3OddIrr) (hp2 : p ≠ 2) {X : Type}
    [Group X] [Finite X] (hX : IsSL3 p X) : SylowCore p X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
  let e1 : X ≃* SL(3, ZMod p) :=
    e.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.trans
      (CFSG.ClassicalModels.specialLinearFieldEquiv (fieldEquivZMod hK) (Fin 3)))
  exact SylowCore.of_mulEquiv e1 (sylowCore_sl3 hR1 hirr hp2)

theorem coprime_card_center_sl3 (hp2 : p ≠ 2) :
    Nat.Coprime (Nat.card (Subgroup.center SL(3, ZMod p))) (2 * p) := by
  rw [card_center_sl3, Nat.card_zmod]
  have hd : Nat.gcd (p - 1) 3 ∣ 3 := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · rw [h]
    exact Nat.coprime_one_left _
  · rw [h]
    have h3 : 3 ∣ p - 1 := by
      have := Nat.gcd_dvd_left (p - 1) 3
      rwa [h] at this
    have hp3 : p ≠ 3 := by
      rintro rfl
      omega
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hdvd => ?_
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h2 | h2
    · omega
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp h2).symm

theorem sylowCore_psl3 (hR1 : GL2OddIndex) (hirr : SL3OddIrr) (hp2 : p ≠ 2) :
    SylowCore p (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p)) :=
  SylowCore.quotient hp2 (Subgroup.center SL(3, ZMod p)) le_rfl (coprime_card_center_sl3 hp2)
    (sylowCore_sl3 hR1 hirr hp2)

theorem sylowCore_of_isPSL3 (hR1 : GL2OddIndex) (hirr : SL3OddIrr) (hp2 : p ≠ 2) {X : Type}
    [Group X] [Finite X] (hX : IsPSL 3 p 1 X) : SylowCore p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  rw [pow_one] at hK
  let e1 : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p) :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv (fieldEquivZMod hK) (Fin 3)))
  exact SylowCore.of_mulEquiv e1 (sylowCore_psl3 hR1 hirr hp2)

@[expose] def FamSl3oddPlus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.IsQuasisimple X → p.Prime → p ≠ 2 →
    IsSL3 p X → A312For X

@[expose] def FamSl3oddMinus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.IsQuasisimple X → p.Prime → p ≠ 2 →
    IsSU3 p X → A312For X

theorem famSl3odd_of (hplus : FamSl3oddPlus) (hminus : FamSl3oddMinus) : FamSl3odd := by
  intro X _ _ s p hq hp hp2 hX
  cases s with
  | true => exact hplus X p hq hp hp2 hX
  | false => exact hminus X p hq hp hp2 hX

theorem famL3odd_of (hR1 : GL2OddIndex) (hirr : SL3OddIrr) : FamL3odd := by
  intro X _ _ p hq hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  exact a312For_of_sylowCore hp hp2 hq (Or.inl hX) (sylowCore_of_isPSL3 hR1 hirr hp2 hX)

theorem famSl3oddPlus_of (hR1 : GL2OddIndex) (hirr : SL3OddIrr) : FamSl3oddPlus := by
  intro X _ _ p hq hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  exact a312For_of_sylowCore hp hp2 hq (Or.inr hX) (sylowCore_of_isSL3 hR1 hirr hp2 hX)

end CFSG.Quasithin.A38c15
