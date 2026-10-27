module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestNonsplit

public section

namespace CFSG.StandardType

open Matrix

namespace SLNS

variable {F : Type} [Field F] {n e s r : ℕ} (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)

theorem nsCore_kT_sub_one_apply_of_not_inT_left {C : Matrix (Fin e) (Fin e) F}
    (Tb : Finset (Fin s)) {α : (Fin e × Fin s) ⊕ Fin r} (hα : ¬ inT Tb α)
    (β : (Fin e × Fin s) ⊕ Fin r) : (nsCore (r := r) C (kT Tb) - 1) α β = 0 := by
  rw [nsCore_kT_sub_one]
  rcases α with ⟨a, i⟩ | u <;> rcases β with ⟨b, j⟩ | v
  · simp only [inT, Sum.elim_inl] at hα
    simp [blockDiagonal_apply, hα]
  all_goals simp

theorem nsCore_kT_sub_one_apply_of_not_inT_right {C : Matrix (Fin e) (Fin e) F}
    (Tb : Finset (Fin s)) (α : (Fin e × Fin s) ⊕ Fin r) {β : (Fin e × Fin s) ⊕ Fin r}
    (hβ : ¬ inT Tb β) : (nsCore (r := r) C (kT Tb) - 1) α β = 0 := by
  rw [nsCore_kT_sub_one]
  rcases α with ⟨a, i⟩ | u <;> rcases β with ⟨b, j⟩ | v
  · simp only [inT, Sum.elim_inl] at hβ
    simp only [fromBlocks_apply₁₁, blockDiagonal_apply]
    split_ifs with hij hi
    · have h1 : i = j := hij
      have h2 : i ∈ Tb := hi
      exact absurd (h1 ▸ h2) hβ
    · rfl
    · rfl
  all_goals simp

theorem nsMat_kT_apply_eq (C : Matrix (Fin e) (Fin e) F) (Tb : Finset (Fin s)) (u w : Fin n) :
    nsMat ε C (kT Tb) u w =
      (1 : Matrix (Fin n) (Fin n) F) u w + (nsCore (r := r) C (kT Tb) - 1) (ε u) (ε w) := by
  simp only [Matrix.sub_apply, nsMat, Matrix.submatrix_apply, Matrix.one_apply,
    ε.injective.eq_iff]
  abel

theorem nsMat_kT_apply_of_mem_fixS_left (C : Matrix (Fin e) (Fin e) F) (Tb : Finset (Fin s))
    {u : Fin n} (hu : u ∈ fixS ε Tb) (w : Fin n) :
    nsMat ε C (kT Tb) u w = (1 : Matrix (Fin n) (Fin n) F) u w := by
  rw [nsMat_kT_apply_eq,
    nsCore_kT_sub_one_apply_of_not_inT_left Tb ((mem_fixS ε).mp hu), add_zero]

theorem nsMat_kT_apply_of_mem_fixS_right (C : Matrix (Fin e) (Fin e) F) (Tb : Finset (Fin s))
    (u : Fin n) {w : Fin n} (hw : w ∈ fixS ε Tb) :
    nsMat ε C (kT Tb) u w = (1 : Matrix (Fin n) (Fin n) F) u w := by
  rw [nsMat_kT_apply_eq,
    nsCore_kT_sub_one_apply_of_not_inT_right Tb _ ((mem_fixS ε).mp hw), add_zero]

theorem nsMat_apply_of_block_ne (C : Matrix (Fin e) (Fin e) F) (k : Fin s → ℕ) {i j : Fin s}
    (hij : i ≠ j) (a b : Fin e) :
    nsMat ε C k (ε.symm (Sum.inl (a, i))) (ε.symm (Sum.inl (b, j))) = 0 := by
  rw [nsMat, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, nsCore,
    fromBlocks_apply₁₁, blockDiagonal_apply, ite_eq_right hij]

omit [Field F] in
theorem exists_of_not_mem_fixS_pair {i₀ i₁ : Fin s} {x : Fin n}
    (hx : x ∉ fixS ε {i₀, i₁}) :
    ∃ a : Fin e, x = ε.symm (Sum.inl (a, i₀)) ∨ x = ε.symm (Sum.inl (a, i₁)) := by
  rw [mem_fixS, not_not] at hx
  rcases hε : ε x with ⟨a, j⟩ | u
  · rw [hε] at hx
    simp only [inT, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton] at hx
    refine ⟨a, ?_⟩
    rcases hx with rfl | rfl
    · exact Or.inl (by rw [← hε, Equiv.symm_apply_apply])
    · exact Or.inr (by rw [← hε, Equiv.symm_apply_apply])
  · rw [hε] at hx
    exact absurd hx (by simp [inT])

omit [Field F] in
theorem not_mem_fixS_pair_left (i₀ i₁ : Fin s) (a : Fin e) :
    ε.symm (Sum.inl (a, i₀)) ∉ fixS ε {i₀, i₁} := by
  rw [mem_fixS, not_not, Equiv.apply_symm_apply]
  simp [inT]

omit [Field F] in
theorem not_mem_fixS_pair_right (i₀ i₁ : Fin s) (a : Fin e) :
    ε.symm (Sum.inl (a, i₁)) ∉ fixS ε {i₀, i₁} := by
  rw [mem_fixS, not_not, Equiv.apply_symm_apply]
  simp [inT]

omit [Field F] in
theorem exists_perm_twoBlock {i₀ i₁ : Fin s} (h01 : i₀ ≠ i₁) {l : ℕ} (hel : e ≤ l)
    (hln : 2 * l ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), (∀ a : Fin e, (σ (ε.symm (Sum.inl (a, i₀))) : ℕ) = a) ∧
      ∀ a : Fin e, (σ (ε.symm (Sum.inl (a, i₁))) : ℕ) = a + (n - l) := by
  classical
  let g : Fin e ⊕ Fin e → Fin n :=
    Sum.elim (fun a => ε.symm (Sum.inl (a, i₀))) (fun a => ε.symm (Sum.inl (a, i₁)))
  let h : Fin e ⊕ Fin e → Fin n :=
    Sum.elim (fun a => ⟨a, by have := a.isLt; omega⟩)
      (fun a => ⟨a + (n - l), by have := a.isLt; omega⟩)
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) hab <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at hab
    · have := Sum.inl_injective (ε.symm.injective hab)
      rw [Prod.mk.injEq] at this
      rw [this.1]
    · exact absurd (congrArg Prod.snd (Sum.inl_injective (ε.symm.injective hab))) h01
    · exact absurd (congrArg Prod.snd (Sum.inl_injective (ε.symm.injective hab))).symm h01
    · have := Sum.inl_injective (ε.symm.injective hab)
      rw [Prod.mk.injEq] at this
      rw [this.1]
  have hh : Function.Injective h := by
    rintro (a | a) (b | b) hab <;> simp only [h, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at hab
    · rw [Fin.ext hab]
    · have := a.isLt
      omega
    · have := b.isLt
      omega
    · rw [Fin.ext (by omega : (a : ℕ) = b)]
  let e₁ : {x // x ∈ Set.range g} ≃ {x // x ∈ Set.range h} :=
    (Equiv.ofInjective g hg).symm.trans (Equiv.ofInjective h hh)
  have happ : ∀ z, e₁.extendSubtype (g z) = h z := by
    intro z
    rw [Equiv.extendSubtype_apply_of_mem e₁ _ ⟨z, rfl⟩]
    simp only [e₁, Equiv.trans_apply, Equiv.ofInjective_symm_apply, Equiv.ofInjective_apply]
  refine ⟨e₁.extendSubtype, fun a => ?_, fun a => ?_⟩
  · have := happ (Sum.inl a)
    simp only [g, h, Sum.elim_inl] at this
    rw [this]
  · have := happ (Sum.inr a)
    simp only [g, h, Sum.elim_inr] at this
    rw [this]

theorem nsMat_kT_mul_comm_twoBlock (C : Matrix (Fin e) (Fin e) F) {i₀ i₁ : Fin s}
    (h01 : i₀ ≠ i₁) {l : ℕ} (hel : e ≤ l) (hln : 2 * l ≤ n) (σ : Equiv.Perm (Fin n))
    (hσx : ∀ a : Fin e, (σ (ε.symm (Sum.inl (a, i₀))) : ℕ) = a)
    (hσy : ∀ a : Fin e, (σ (ε.symm (Sum.inl (a, i₁))) : ℕ) = a + (n - l)) :
    nsMat ε C (kT {i₀, i₁}) * (ggInvMatrix n l F).submatrix σ σ =
      (ggInvMatrix n l F).submatrix σ σ * nsMat ε C (kT {i₀, i₁}) := by
  classical
  set d := n - l with hd
  set S := fixS ε {i₀, i₁} with hS
  set Y := nsMat ε C (kT {i₀, i₁}) with hY
  set N := (ggInvNil n l F).submatrix σ σ with hN
  have hM : (ggInvMatrix n l F).submatrix σ σ = 1 + N := by
    ext u v
    simp only [hN, ggInvMatrix, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply,
      σ.injective.eq_iff]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  have hNapp : ∀ u v, N u v =
      if (σ v : ℕ) < l ∧ (σ u : ℕ) = σ v + d ∧ (σ v : ℕ) < σ u then 1 else 0 :=
    fun u v => by rw [hN, Matrix.submatrix_apply, ggInvNil_apply]
  have hσinj : ∀ u w : Fin n, (σ u : ℕ) = σ w → u = w := fun u w h => σ.injective (Fin.ext h)
  have hxS : ∀ a, ε.symm (Sum.inl (a, i₀)) ∉ S := not_mem_fixS_pair_left ε i₀ i₁
  have hyS : ∀ a, ε.symm (Sum.inl (a, i₁)) ∉ S := not_mem_fixS_pair_right ε i₀ i₁
  have hblk : ∀ u, u ∉ S →
      ∃ a, u = ε.symm (Sum.inl (a, i₀)) ∨ u = ε.symm (Sum.inl (a, i₁)) :=
    fun u hu => exists_of_not_mem_fixS_pair ε hu
  have hY1 : ∀ u, u ∈ S → ∀ w, Y u w = (1 : Matrix (Fin n) (Fin n) F) u w :=
    fun u hu w => nsMat_kT_apply_of_mem_fixS_left ε C _ hu w
  have hY2 : ∀ w, w ∈ S → ∀ u, Y u w = (1 : Matrix (Fin n) (Fin n) F) u w :=
    fun w hw u => nsMat_kT_apply_of_mem_fixS_right ε C _ u hw
  have hN1 : ∀ u w, u ∈ S → N u w ≠ 0 → w ∈ S := by
    intro u w hu hne
    rw [hNapp] at hne
    split_ifs at hne with hP
    · by_contra hw
      obtain ⟨c, rfl | rfl⟩ := hblk w hw
      · have h2 := hP.2.1
        rw [hσx] at h2
        have hu' : u = ε.symm (Sum.inl (c, i₁)) := hσinj _ _ (by rw [hσy]; exact h2)
        exact hyS c (hu' ▸ hu)
      · have h1 := hP.1
        rw [hσy] at h1
        omega
    · exact absurd rfl hne
  have hN2 : ∀ w v, v ∈ S → N w v ≠ 0 → w ∈ S := by
    intro w v hv hne
    rw [hNapp] at hne
    split_ifs at hne with hP
    · by_contra hw
      obtain ⟨c, rfl | rfl⟩ := hblk w hw
      · have h2 := hP.2.1
        rw [hσx] at h2
        have := c.isLt
        omega
      · have h2 := hP.2.1
        rw [hσy] at h2
        have hv' : v = ε.symm (Sum.inl (c, i₀)) := hσinj _ _ (by rw [hσx]; omega)
        exact hxS c (hv' ▸ hv)
    · exact absurd rfl hne
  have hL1 : ∀ w b, N w (ε.symm (Sum.inl (b, i₀))) =
      if w = ε.symm (Sum.inl (b, i₁)) then 1 else 0 := by
    intro w b
    rw [hNapp, hσx]
    have hb := b.isLt
    by_cases hw : w = ε.symm (Sum.inl (b, i₁))
    · rw [ite_eq_left hw, ite_eq_left]
      rw [hw, hσy]
      refine ⟨by omega, rfl, by omega⟩
    · rw [ite_eq_right hw, ite_eq_right]
      rintro ⟨-, h2, -⟩
      exact hw (hσinj _ _ (by rw [hσy]; exact h2))
  have hL2 : ∀ w b, N w (ε.symm (Sum.inl (b, i₁))) = 0 := by
    intro w b
    rw [hNapp, hσy, ite_eq_right]
    rintro ⟨h1, -, -⟩
    omega
  have hL3 : ∀ a w, N (ε.symm (Sum.inl (a, i₁))) w =
      if w = ε.symm (Sum.inl (a, i₀)) then 1 else 0 := by
    intro a w
    rw [hNapp, hσy]
    have ha := a.isLt
    by_cases hw : w = ε.symm (Sum.inl (a, i₀))
    · rw [ite_eq_left hw, ite_eq_left]
      rw [hw, hσx]
      refine ⟨by omega, rfl, by omega⟩
    · rw [ite_eq_right hw, ite_eq_right]
      rintro ⟨-, h2, -⟩
      exact hw (hσinj _ _ (by rw [hσx]; omega))
  have hL4 : ∀ a w, N (ε.symm (Sum.inl (a, i₀))) w = 0 := by
    intro a w
    rw [hNapp, hσx, ite_eq_right]
    rintro ⟨-, h2, -⟩
    have := a.isLt
    omega
  have hk0 : kT {i₀, i₁} i₀ = 1 := by simp [kT]
  have hk1 : kT {i₀, i₁} i₁ = 1 := by simp [kT]
  have hYxy : ∀ a b, Y (ε.symm (Sum.inl (a, i₀))) (ε.symm (Sum.inl (b, i₁))) = 0 :=
    fun a b => nsMat_apply_of_block_ne ε C _ h01 a b
  have hYxx : ∀ a b, Y (ε.symm (Sum.inl (a, i₀))) (ε.symm (Sum.inl (b, i₀))) = C a b :=
    fun a b => by rw [hY, nsMat_block, hk0, pow_one]
  have hYyy : ∀ a b, Y (ε.symm (Sum.inl (a, i₁))) (ε.symm (Sum.inl (b, i₁))) = C a b :=
    fun a b => by rw [hY, nsMat_block, hk1, pow_one]
  have hS1 : ∀ u b, ∑ w, Y u w * N w (ε.symm (Sum.inl (b, i₀))) =
      Y u (ε.symm (Sum.inl (b, i₁))) := by
    intro u b
    simp only [hL1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hS2 : ∀ u b, ∑ w, Y u w * N w (ε.symm (Sum.inl (b, i₁))) = 0 := by
    intro u b
    simp only [hL2, mul_zero, Finset.sum_const_zero]
  have hS3 : ∀ a v, ∑ w, N (ε.symm (Sum.inl (a, i₁))) w * Y w v =
      Y (ε.symm (Sum.inl (a, i₀))) v := by
    intro a v
    simp only [hL3, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hS4 : ∀ a v, ∑ w, N (ε.symm (Sum.inl (a, i₀))) w * Y w v = 0 := by
    intro a v
    simp only [hL4, zero_mul, Finset.sum_const_zero]
  ext u v
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hu : u ∈ S
  · calc ∑ w, Y u w * N w v = ∑ w, (1 : Matrix (Fin n) (Fin n) F) u w * N w v :=
          Finset.sum_congr rfl fun w _ => by rw [hY1 u hu w]
      _ = ∑ w, N u w * (1 : Matrix (Fin n) (Fin n) F) w v := by
          rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul, Matrix.mul_one]
      _ = ∑ w, N u w * Y w v := Finset.sum_congr rfl fun w _ => by
          by_cases hw : N u w = 0
          · rw [hw, zero_mul, zero_mul]
          · rw [hY1 w (hN1 u w hu hw) v]
  by_cases hv : v ∈ S
  · calc ∑ w, Y u w * N w v = ∑ w, (1 : Matrix (Fin n) (Fin n) F) u w * N w v :=
          Finset.sum_congr rfl fun w _ => by
            by_cases hw : N w v = 0
            · rw [hw, mul_zero, mul_zero]
            · rw [hY2 w (hN2 w v hv hw) u]
      _ = ∑ w, N u w * (1 : Matrix (Fin n) (Fin n) F) w v := by
          rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul, Matrix.mul_one]
      _ = ∑ w, N u w * Y w v := Finset.sum_congr rfl fun w _ => by rw [hY2 v hv w]
  obtain ⟨a, rfl | rfl⟩ := hblk u hu <;> obtain ⟨b, rfl | rfl⟩ := hblk v hv
  · rw [hS1, hS4, hYxy]
  · rw [hS2, hS4]
  · rw [hS1, hS3, hYyy, hYxx]
  · rw [hS2, hS3, hYxy]

end SLNS

theorem ggNSTwoBlockPermInput_holds : GGNSTwoBlockPermInput := by
  intro F _ _ n e s r ε C hC i₀ i₁ h01 l hel hln
  obtain ⟨σ, hσx, hσy⟩ := SLNS.exists_perm_twoBlock ε h01 hel hln
  exact ⟨σ, SLNS.nsMat_kT_mul_comm_twoBlock ε C h01 hel hln σ hσx hσy⟩

end CFSG.StandardType
