module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G]

structure GGQTwoXInLUCoordAt (Bs X L : Subgroup G) (x : G) (n : ℕ) (K : Type) [Field K]
    (j₀ : Fin (n + 1)) where
  field : UnitaryFieldData 2 1 K
  φ : ↥(unitarySU 2 1 K (n + 1)) →* G
  range_eq : φ.range = X
  ker_le : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (n + 1))
  ω : Kˣ
  ω_ne_one : ω ≠ 1
  ι : Additive ↥Bs ≃+ ↥(GGQTwoXInLAug n)
  diag : ∀ b : ↥Bs, ∃ s : ↥(unitarySU 2 1 K (n + 1)),
    (s : GL (Fin (n + 1)) K) = diagHom (n + 1)
      (fun i => ω ^ ((ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i).val) ∧ φ s = b
  mem_x : x ∈ Bs
  ι_x : ((ι (Additive.ofMul ⟨x, mem_x⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
    fun i => if i = j₀ then 0 else -1
  L_eq : L = (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase j₀)).map φ

variable {Bs X L : Subgroup G} {x : G} {n : ℕ} {K : Type} [Field K]

@[expose] def GGQTwoXInLUCoordAt.toCoord (C : GGQTwoXInLUCoordAt Bs X L x n K 0) :
    GGQTwoXInLUCoord Bs X L x n K :=
  ⟨C.field, C.φ, C.range_eq, C.ker_le, C.ω, C.ω_ne_one, C.ι, C.diag, C.mem_x, C.ι_x, C.L_eq⟩

@[expose] def GGQTwoXInLUCoord.toAt (C : GGQTwoXInLUCoord Bs X L x n K) :
    GGQTwoXInLUCoordAt Bs X L x n K 0 :=
  ⟨C.field, C.φ, C.range_eq, C.ker_le, C.ω, C.ω_ne_one, C.ι, C.diag, C.mem_x, C.ι_x, C.L_eq⟩

@[simp] theorem GGQTwoXInLUCoordAt.toCoord_φ (C : GGQTwoXInLUCoordAt Bs X L x n K 0) :
    C.toCoord.φ = C.φ := rfl

@[simp] theorem GGQTwoXInLUCoordAt.toCoord_ι (C : GGQTwoXInLUCoordAt Bs X L x n K 0) :
    C.toCoord.ι = C.ι := rfl

@[simp] theorem GGQTwoXInLUCoord.toAt_φ (C : GGQTwoXInLUCoord Bs X L x n K) :
    C.toAt.φ = C.φ := rfl

@[simp] theorem GGQTwoXInLUCoord.toAt_ι (C : GGQTwoXInLUCoord Bs X L x n K) :
    C.toAt.ι = C.ι := rfl


private def ggQTUp_compPerm (σ : Equiv.Perm (Fin (n + 1))) :
    ↥(GGQTwoXInLAug n) →+ ↥(GGQTwoXInLAug n) where
  toFun v := ⟨fun i => (v : Fin (n + 1) → ZMod 3) (σ i), by
    rw [LinearMap.mem_ker]
    have hv : ∑ i, (v : Fin (n + 1) → ZMod 3) i = 0 := by
      have h := v.2
      rw [LinearMap.mem_ker] at h
      simpa only [LinearMap.sum_apply, LinearMap.proj_apply, Finset.sum_apply,
        Finset.mem_univ, Finset.sum_const, smul_eq_mul] using h
    have hsum : ∑ i, (v : Fin (n + 1) → ZMod 3) (σ i) = 0 := by
      rw [Equiv.sum_comp σ (v : Fin (n + 1) → ZMod 3)]
      exact hv
    simpa only [LinearMap.sum_apply, LinearMap.proj_apply, Finset.sum_apply,
      Finset.mem_univ, Finset.sum_const, smul_eq_mul] using hsum⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    simp
  map_add' x y := by
    apply Subtype.ext
    funext i
    simp [Pi.add_apply]

private theorem ggQTUp_compPerm_coe (σ : Equiv.Perm (Fin (n + 1)))
    (v : ↥(GGQTwoXInLAug n)) :
    ((ggQTUp_compPerm σ v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
      fun i => (v : Fin (n + 1) → ZMod 3) (σ i) := rfl

private def ggQTUp_compPermEquiv (σ : Equiv.Perm (Fin (n + 1))) :
    ↥(GGQTwoXInLAug n) ≃+ ↥(GGQTwoXInLAug n) where
  toFun := ggQTUp_compPerm σ
  invFun := ggQTUp_compPerm σ.symm
  left_inv v := by
    apply Subtype.ext
    funext i
    simp only [ggQTUp_compPerm_coe, Equiv.apply_symm_apply]
  right_inv v := by
    apply Subtype.ext
    funext i
    simp only [ggQTUp_compPerm_coe, Equiv.symm_apply_apply]
  map_add' := map_add (ggQTUp_compPerm σ)

private theorem ggQTUp_compPermEquiv_coe (σ : Equiv.Perm (Fin (n + 1)))
    (v : ↥(GGQTwoXInLAug n)) :
    ((ggQTUp_compPermEquiv σ v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
      fun i => (v : Fin (n + 1) → ZMod 3) (σ i) := rfl

private theorem ggQTUp_permMatrix_apply_inv (σ : Equiv.Perm (Fin (n + 1)))
    (a b : Fin (n + 1)) :
    (Equiv.Perm.permMatrix K σ⁻¹) a b = if σ⁻¹ a = b then (1 : K) else 0 := by
  rw [← LineU.coe_permGL_matrix σ]
  exact TableBUE.permGL_apply σ a b

private theorem ggQTUp_permMatrix_apply (σ : Equiv.Perm (Fin (n + 1)))
    (a b : Fin (n + 1)) :
    (Equiv.Perm.permMatrix K σ) a b = if σ a = b then (1 : K) else 0 := by
  have hP : Equiv.Perm.permMatrix K σ =
      ((CFSG.RankThree.Classical.permGL σ⁻¹ : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) := by
    rw [map_inv]
    exact (LineU.coe_permGL_inv_matrix σ).symm
  rw [hP, TableBUE.permGL_apply]
  simp

private theorem ggQTUp_permMatrix_mul_apply (σ : Equiv.Perm (Fin (n + 1)))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i j : Fin (n + 1)) :
    (Equiv.Perm.permMatrix K σ⁻¹ * M) i j = M (σ⁻¹ i) j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ⁻¹ i)]
  · rw [ggQTUp_permMatrix_apply_inv, if_pos rfl, one_mul]
  · intro k _ hk
    rw [ggQTUp_permMatrix_apply_inv, if_neg (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem ggQTUp_permMatrix_mul_apply_right (σ : Equiv.Perm (Fin (n + 1)))
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i j : Fin (n + 1)) :
    (N * Equiv.Perm.permMatrix K σ) i j = N i (σ⁻¹ j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [ggQTUp_permMatrix_apply, if_pos (by simp), mul_one]
    simp
  · intro k _ hk
    rw [ggQTUp_permMatrix_apply, if_neg, mul_zero]
    intro h
    exact hk (by
      calc k = σ.symm (σ k) := (Equiv.symm_apply_apply σ k).symm
        _ = σ.symm j := by rw [h])
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem ggQTUp_permMatrix_conj_apply (σ : Equiv.Perm (Fin (n + 1)))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i j : Fin (n + 1)) :
    (Equiv.Perm.permMatrix K σ⁻¹ * M * Equiv.Perm.permMatrix K σ) i j =
      M (σ⁻¹ i) (σ⁻¹ j) := by
  rw [ggQTUp_permMatrix_mul_apply_right, ggQTUp_permMatrix_mul_apply]

private theorem ggQTUp_permMatrix_conj_apply_inv (σ : Equiv.Perm (Fin (n + 1)))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i j : Fin (n + 1)) :
    (Equiv.Perm.permMatrix K σ * M * Equiv.Perm.permMatrix K σ⁻¹) i j =
      M (σ i) (σ j) := by
  have h := ggQTUp_permMatrix_conj_apply (K := K) σ⁻¹ M i j
  simpa [Equiv.symm_symm] using h

private theorem ggQTUp_gl_conj_apply (hK : UnitaryFieldData 2 1 K)
    (σ : Equiv.Perm (Fin (n + 1))) (Y : GL (Fin (n + 1)) K) (i j : Fin (n + 1)) :
    (((LineU.permSU hK σ : GL (Fin (n + 1)) K) * Y *
        ((LineU.permSU hK σ : GL (Fin (n + 1)) K))⁻¹ : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j =
      ((Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (σ⁻¹ i) (σ⁻¹ j)) := by
  have hP : ((LineU.permSU hK σ : ↥(unitarySU 2 1 K (n + 1))) :
      GL (Fin (n + 1)) K) = CFSG.RankThree.Classical.permGL σ :=
    LineU.coe_permSU hK σ
  have hPinv : ((LineU.permSU hK σ : GL (Fin (n + 1)) K))⁻¹ =
      (CFSG.RankThree.Classical.permGL σ)⁻¹ := by
    rw [hP]
  rw [hPinv, hP, Units.val_mul, Units.val_mul]
  rw [LineU.coe_permGL_matrix, LineU.coe_permGL_inv_matrix]
  exact ggQTUp_permMatrix_conj_apply σ (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j

private theorem ggQTUp_conj_apply (hK : UnitaryFieldData 2 1 K)
    (σ : Equiv.Perm (Fin (n + 1))) (y : ↥(unitarySU 2 1 K (n + 1)))
    (i j : Fin (n + 1)) :
    ((((MulAut.conj (LineU.permSU hK σ) y : ↥(unitarySU 2 1 K (n + 1))) :
        GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j) =
      (((y : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (σ⁻¹ i)
        (σ⁻¹ j)) := by
  have hgl : (((MulAut.conj (LineU.permSU hK σ) y : ↥(unitarySU 2 1 K (n + 1))) :
      GL (Fin (n + 1)) K)) =
      (LineU.permSU hK σ : GL (Fin (n + 1)) K) * (y : GL (Fin (n + 1)) K) *
        ((LineU.permSU hK σ : GL (Fin (n + 1)) K))⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  rw [hgl]
  exact ggQTUp_gl_conj_apply hK σ (y : GL (Fin (n + 1)) K) i j

private theorem ggQTUp_mem_map_symm (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (t : Fin (n + 1)) :
    t ∈ S.map σ.symm.toEmbedding ↔ σ t ∈ S := by
  rw [Finset.mem_map_equiv]
  simp

private theorem ggQTUp_blockSU_le (hK : UnitaryFieldData 2 1 K)
    (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin (n + 1))) :
    (TableBUE.blockSU (K := K) (n := 1) (S.map σ.symm.toEmbedding)).map
        (MulAut.conj (LineU.permSU hK σ)).toMonoidHom ≤ TableBUE.blockSU (K := K) (n := 1) S := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [TableBUE.mem_blockSU] at hy ⊢
  change TableBUE.IsBlockOn S
    ((((MulAut.conj (LineU.permSU hK σ) y : ↥(unitarySU 2 1 K (n + 1))) :
      GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K))
  intro i j hij
  rw [ggQTUp_conj_apply hK σ y i j]
  have hmem : σ⁻¹ i ∉ S.map σ.symm.toEmbedding ∨
      σ⁻¹ j ∉ S.map σ.symm.toEmbedding := by
    rcases hij with hi | hj
    · left
      intro h
      exact hi (by simpa using (ggQTUp_mem_map_symm σ S (σ⁻¹ i)).mp h)
    · right
      intro h
      exact hj (by simpa using (ggQTUp_mem_map_symm σ S (σ⁻¹ j)).mp h)
  rw [hy (σ⁻¹ i) (σ⁻¹ j) hmem]
  by_cases h : i = j
  · subst h
    simp
  · have h' : σ⁻¹ i ≠ σ⁻¹ j := fun hh => h (σ⁻¹.injective hh)
    rw [Matrix.one_apply, Matrix.one_apply, if_neg h, if_neg h']

private theorem ggQTUp_blockSU_le_rev (hK : UnitaryFieldData 2 1 K)
    (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin (n + 1))) :
    TableBUE.blockSU (K := K) (n := 1) S ≤
      (TableBUE.blockSU (K := K) (n := 1) (S.map σ.symm.toEmbedding)).map
        (MulAut.conj (LineU.permSU hK σ)).toMonoidHom := by
  intro x hx
  rw [TableBUE.mem_blockSU] at hx
  rw [Subgroup.mem_map]
  refine ⟨(LineU.permSU hK σ)⁻¹ * x * LineU.permSU hK σ, ?_, ?_⟩
  · rw [TableBUE.mem_blockSU]
    intro i j hij
    have hP : ((LineU.permSU hK σ : ↥(unitarySU 2 1 K (n + 1))) :
        GL (Fin (n + 1)) K) = CFSG.RankThree.Classical.permGL σ :=
      LineU.coe_permSU hK σ
    have hPinv : (((LineU.permSU hK σ)⁻¹ : ↥(unitarySU 2 1 K (n + 1))) :
        GL (Fin (n + 1)) K) = (CFSG.RankThree.Classical.permGL σ)⁻¹ := by
      rw [Subgroup.coe_inv, hP]
    have hy : ((((LineU.permSU hK σ)⁻¹ * x * LineU.permSU hK σ :
        ↥(unitarySU 2 1 K (n + 1)))) : GL (Fin (n + 1)) K) =
        (((LineU.permSU hK σ)⁻¹ : ↥(unitarySU 2 1 K (n + 1))) :
            GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) *
          ((LineU.permSU hK σ : ↥(unitarySU 2 1 K (n + 1))) :
            GL (Fin (n + 1)) K) := rfl
    rw [hy, hPinv, hP, Units.val_mul, Units.val_mul,
      LineU.coe_permGL_inv_matrix, LineU.coe_permGL_matrix]
    rw [ggQTUp_permMatrix_conj_apply_inv]
    have hmem : σ i ∉ S ∨ σ j ∉ S := by
      rcases hij with hi | hj
      · left
        intro h
        exact hi ((ggQTUp_mem_map_symm σ S i).mpr h)
      · right
        intro h
        exact hj ((ggQTUp_mem_map_symm σ S j).mpr h)
    rw [hx (σ i) (σ j) hmem]
    by_cases h : i = j
    · subst h
      simp
    · have h' : σ i ≠ σ j := fun hh => h (σ.injective hh)
      rw [Matrix.one_apply, Matrix.one_apply, if_neg h, if_neg h']
  · change MulAut.conj (LineU.permSU hK σ)
      ((LineU.permSU hK σ)⁻¹ * x * LineU.permSU hK σ) = x
    rw [MulAut.conj_apply]
    group

private theorem ggQTUp_blockSU_map_conj (hK : UnitaryFieldData 2 1 K)
    (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin (n + 1))) :
    (TableBUE.blockSU (K := K) (n := 1) (S.map σ.symm.toEmbedding)).map
        (MulAut.conj (LineU.permSU hK σ)).toMonoidHom = TableBUE.blockSU (K := K) (n := 1) S :=
  le_antisymm (ggQTUp_blockSU_le hK σ S) (ggQTUp_blockSU_le_rev hK σ S)

private theorem ggQTUp_permGL_inv_conj_diagHom (σ : Equiv.Perm (Fin (n + 1)))
    (d : Fin (n + 1) → Kˣ) :
    (CFSG.RankThree.Classical.permGL σ)⁻¹ * diagHom (n + 1) d *
        CFSG.RankThree.Classical.permGL σ = diagHom (n + 1) (fun i => d (σ i)) := by
  have h := CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (K := K) σ⁻¹ d
  rw [map_inv] at h
  have hd : (d ∘ ⇑(Equiv.symm σ⁻¹)) = fun i => d (σ i) := rfl
  simpa [hd] using h

private theorem ggQTUp_erase_map (σ : Equiv.Perm (Fin (n + 1))) {j₀ j₁ : Fin (n + 1)}
    (hj : σ j₁ = j₀) :
    (Finset.univ.erase j₀).map σ.symm.toEmbedding = Finset.univ.erase j₁ := by
  rw [Finset.map_erase, Finset.map_univ_equiv]
  congr 1
  show σ.symm j₀ = j₁
  rw [← hj, Equiv.symm_apply_apply]

theorem GGQTwoXInLUCoordAt.relabel {j₀ : Fin (n + 1)} (C : GGQTwoXInLUCoordAt Bs X L x n K j₀)
    (σ : Equiv.Perm (Fin (n + 1))) {j₁ : Fin (n + 1)} (hj : σ j₁ = j₀) :
    ∃ C' : GGQTwoXInLUCoordAt Bs X L x n K j₁,
      (∀ b : ↥Bs, ((C'.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
        fun i => ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) (σ i)) ∧
      ∀ S : Finset (Fin (n + 1)),
        (TableBUE.blockSU (K := K) (n := 1) (S.map σ.symm.toEmbedding)).map C'.φ =
          (TableBUE.blockSU (K := K) (n := 1) S).map C.φ := by
  classical
  let P : ↥(unitarySU 2 1 K (n + 1)) := LineU.permSU C.field σ
  let c : MulAut ↥(unitarySU 2 1 K (n + 1)) := MulAut.conj P
  let e : ↥(GGQTwoXInLAug n) ≃+ ↥(GGQTwoXInLAug n) := ggQTUp_compPermEquiv σ
  let ι' : Additive ↥Bs ≃+ ↥(GGQTwoXInLAug n) := C.ι.trans e
  have hcoord : ∀ b : ↥Bs, ((ι' (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) :
      Fin (n + 1) → ZMod 3) =
      fun i => ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) (σ i) := by
    intro b
    dsimp only [ι', e]
    exact ggQTUp_compPermEquiv_coe σ (C.ι (Additive.ofMul b))
  have hblock : ∀ S : Finset (Fin (n + 1)),
      (TableBUE.blockSU (K := K) (n := 1) (S.map σ.symm.toEmbedding)).map c.toMonoidHom =
        TableBUE.blockSU (K := K) (n := 1) S := by
    intro S
    exact ggQTUp_blockSU_map_conj C.field σ S
  refine ⟨⟨C.field, C.φ.comp c.toMonoidHom, ?_, ?_, C.ω, C.ω_ne_one, ι', ?_, C.mem_x, ?_, ?_⟩,
    ?_, ?_⟩
  · have htop : c.toMonoidHom.range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      exact fun y => ⟨c.symm y, by simp⟩
    rw [MonoidHom.range_comp C.φ c.toMonoidHom, htop, Subgroup.map_top]
    exact C.range_eq
  · intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hzu : c u ∈ C.φ.ker := by
      rw [MonoidHom.mem_ker]
      simpa using hu
    have hz := C.ker_le hzu
    have hcomm : P * c u = c u * P := Subgroup.mem_center_iff.mp hz P
    have hu_eq : u = c u := by
      calc u = P⁻¹ * (P * u * P⁻¹) * P := by group
        _ = P⁻¹ * (c u) * P := by rw [MulAut.conj_apply]
        _ = c u := by rw [mul_assoc, ← hcomm]; group
    rw [hu_eq]
    exact hz
  · intro b
    obtain ⟨s, hsmat, hsb⟩ := C.diag b
    refine ⟨P⁻¹ * s * P, ?_, ?_⟩
    · have hP : ((P : ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) =
          CFSG.RankThree.Classical.permGL σ := by
        dsimp only [P]
        exact LineU.coe_permSU C.field σ
      have hPinv : (((P)⁻¹ : ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) =
          (CFSG.RankThree.Classical.permGL σ)⁻¹ := by
        rw [Subgroup.coe_inv, hP]
      have hcoe : (((P⁻¹ * s * P : ↥(unitarySU 2 1 K (n + 1))) :
          GL (Fin (n + 1)) K)) =
          (P : GL (Fin (n + 1)) K)⁻¹ * (s : GL (Fin (n + 1)) K) *
            (P : GL (Fin (n + 1)) K) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hPinv, hP]
      rw [hcoe, hsmat, hP]
      rw [ggQTUp_permGL_inv_conj_diagHom σ
        (fun i => C.ω ^ (((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) :
          Fin (n + 1) → ZMod 3) i).val)]
      rw [hcoord b]
    · have hc : c (P⁻¹ * s * P) = s := by
        rw [MulAut.conj_apply]
        group
      show C.φ (c (P⁻¹ * s * P)) = b
      rw [hc, hsb]
  · show ((ι' (Additive.ofMul ⟨x, C.mem_x⟩) : ↥(GGQTwoXInLAug n)) :
      Fin (n + 1) → ZMod 3) = fun i => if i = j₁ then 0 else -1
    rw [hcoord]
    funext i
    rw [C.ι_x]
    change (if σ i = j₀ then 0 else -1) = (if i = j₁ then 0 else -1)
    have hiff : σ i = j₀ ↔ i = j₁ := by
      constructor
      · intro h
        apply σ.injective
        rw [h, hj]
      · rintro rfl
        exact hj
    by_cases h : σ i = j₀
    · have hi : i = j₁ := hiff.mp h
      rw [if_pos h, if_pos hi]
    · have hi : i ≠ j₁ := fun h' => h (hiff.mpr h')
      rw [if_neg h, if_neg hi]
  · calc L = (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase j₀)).map C.φ := C.L_eq
      _ = (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase j₁)).map
            (C.φ.comp c.toMonoidHom) := by
        rw [← Subgroup.map_map]
        rw [← ggQTUp_erase_map σ hj]
        rw [hblock (Finset.univ.erase j₀)]
  · intro b
    exact hcoord b
  · intro S
    change (TableBUE.blockSU (K := K) (n := 1) (S.map σ.symm.toEmbedding)).map
        (C.φ.comp c.toMonoidHom) = (TableBUE.blockSU (K := K) (n := 1) S).map C.φ
    rw [← Subgroup.map_map, hblock S]


end CFSG.StandardType

end


