module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

theorem eq_of_isInvD [Finite K] {M : Subgroup (W6 K)} (hM : IsInvD M) :
    M = ⊥ ∨ M = ⊤ ∨ ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ M = natSub a b := by
  classical
  let U₂ : AddSubgroup (Fin 3 → K) :=
    { carrier := {u | natEmb 0 1 (Multiplicative.ofAdd u) ∈ M}
      add_mem' := fun {a b} ha hb => by
        change natEmb 0 1 (Multiplicative.ofAdd (a + b)) ∈ M
        rw [ofAdd_add, map_mul]
        exact M.mul_mem ha hb
      zero_mem' := by
        change natEmb 0 1 (Multiplicative.ofAdd 0) ∈ M
        rw [ofAdd_zero, map_one]
        exact M.one_mem
      neg_mem' := fun {a} ha => by
        change natEmb 0 1 (Multiplicative.ofAdd (-a)) ∈ M
        rw [ofAdd_neg, map_inv]
        exact M.inv_mem ha }
  have hU₂ : ∀ g ∈ StatedSL 3 K, ∀ u ∈ U₂, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U₂ := by
    intro g hg u hu
    have h1 := hM g hg _ hu
    rw [matAut_dgHom_natEmb] at h1
    exact h1
  let U₁ : AddSubgroup (Fin 3 → K) :=
    { carrier := {u | ∃ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = u}
      add_mem' := fun {a b} ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩ => ⟨x * y, M.mul_mem hx hy, by
        rw [← hxa, ← hyb]
        rfl⟩
      zero_mem' := ⟨1, M.one_mem, rfl⟩
      neg_mem' := fun {a} ⟨x, hx, hxa⟩ => ⟨x⁻¹, M.inv_mem hx, by
        rw [← hxa]
        rfl⟩ }
  have hU₁ : ∀ g ∈ StatedSL 3 K, ∀ u ∈ U₁, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U₁ := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨matAut (dgHom g) x, hM g hg x hx, dgHom_mulVec_inl g _⟩
  have hmem₂ : ∀ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = 0 →
      Multiplicative.toAdd x ∘ Sum.inr ∈ U₂ := by
    intro x hx h0
    change natEmb 0 1 (Multiplicative.ofAdd (Multiplicative.toAdd x ∘ Sum.inr)) ∈ M
    convert hx using 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_natEmb, toAdd_ofAdd]
    funext i
    rcases i with i | i
    · have := congrFun h0 i
      simpa [natVec] using this.symm
    · simp [natVec]
  rcases isNatIrr_SL3 U₂ hU₂ with h2 | h2 <;> rcases isNatIrr_SL3 U₁ hU₁ with h1 | h1
  ·
    left
    rw [eq_bot_iff]
    intro x hx
    have hx1 : Multiplicative.toAdd x ∘ Sum.inl = 0 := by
      have : Multiplicative.toAdd x ∘ Sum.inl ∈ U₁ := ⟨x, hx, rfl⟩
      rwa [h1, AddSubgroup.mem_bot] at this
    have hx2 := hmem₂ x hx hx1
    rw [h2, AddSubgroup.mem_bot] at hx2
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i
    · exact congrFun hx1 i
    · exact congrFun hx2 i
  ·
    right; right
    have hinj : ∀ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = 0 → x = 1 := by
      intro x hx h0
      have hx2 := hmem₂ x hx h0
      rw [h2, AddSubgroup.mem_bot] at hx2
      apply Multiplicative.toAdd.injective
      funext i
      rcases i with i | i
      · exact congrFun h0 i
      · exact congrFun hx2 i
    obtain ⟨c, hc⟩ := eq_natSub_one_of_proj hM hinj fun u => by
      have : u ∈ U₁ := by rw [h1]; trivial
      exact this
    exact ⟨1, c, Or.inl one_ne_zero, hc⟩
  ·
    right; right
    refine ⟨0, 1, Or.inr one_ne_zero, le_antisymm (fun x hx => ?_) ?_⟩
    · have hx1 : Multiplicative.toAdd x ∘ Sum.inl = 0 := by
        have : Multiplicative.toAdd x ∘ Sum.inl ∈ U₁ := ⟨x, hx, rfl⟩
        rwa [h1, AddSubgroup.mem_bot] at this
      exact natSub_zero_one_eq.mpr hx1
    · rintro _ ⟨u, rfl⟩
      have hu : Multiplicative.toAdd u ∈ U₂ := by rw [h2]; trivial
      change natEmb 0 1 (Multiplicative.ofAdd (Multiplicative.toAdd u)) ∈ M at hu
      rwa [ofAdd_toAdd] at hu
  ·
    right; left
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx, hxv⟩ : Multiplicative.toAdd v ∘ Sum.inl ∈ U₁ := by rw [h1]; trivial
    have hy : (Multiplicative.toAdd v - Multiplicative.toAdd x) ∘ Sum.inr ∈ U₂ := by
      rw [h2]; trivial
    have hy' : natEmb 0 1 (Multiplicative.ofAdd
        ((Multiplicative.toAdd v - Multiplicative.toAdd x) ∘ Sum.inr)) ∈ M := hy
    have hv : v = x * natEmb 0 1 (Multiplicative.ofAdd
        ((Multiplicative.toAdd v - Multiplicative.toAdd x) ∘ Sum.inr)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_natEmb, toAdd_ofAdd]
      funext i
      rcases i with i | i
      · have := congrFun hxv i
        simp only [Function.comp_apply] at this
        simp [natVec, this]
      · simp [natVec]
    rw [hv]
    exact M.mul_mem hx hy'

theorem exists_sl_e0 (v : Fin 3 → K) (hv : v ≠ 0) :
    ∃ g : GL (Fin 3) K, g ∈ StatedSL 3 K ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = v := by
  have key : ∀ m : Matrix (Fin 3) (Fin 3) K, m.det = 1 → (∀ i, m i 0 = v i) →
      ∃ g : GL (Fin 3) K, g ∈ StatedSL 3 K ∧
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = v := by
    intro m hm hcol
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero m (by rw [hm]; exact one_ne_zero),
      SL3Pair.mem_statedSL_iff.mpr hm, ?_⟩
    funext i
    rw [Matrix.mulVec_single_one]
    exact hcol i
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i <;> assumption
      refine key !![0, (v 2)⁻¹, 0; 0, 0, 1; v 2, 0, 0] ?_ ?_
      · simp [det_fin_three, h2]
      · intro i
        fin_cases i <;> simp [h0, h1]
    · refine key !![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1] ?_ ?_
      · simp [det_fin_three, h1]
      · intro i
        fin_cases i <;> simp [h0]
  · refine key !![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1] ?_ ?_
    · simp [det_fin_three, h0]
    · intro i
      fin_cases i <;> simp

theorem exists_sl_mulVec {p h : Fin 3 → K} (hp : p ≠ 0) (hh : h ≠ 0) :
    ∃ g : GL (Fin 3) K, g ∈ StatedSL 3 K ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ p = h := by
  obtain ⟨g₁, hg₁, e₁⟩ := exists_sl_e0 p hp
  obtain ⟨g₂, hg₂, e₂⟩ := exists_sl_e0 h hh
  refine ⟨g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
  rw [← e₁, Matrix.mulVec_mulVec, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one, e₂]

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
