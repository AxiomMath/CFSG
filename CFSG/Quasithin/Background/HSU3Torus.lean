module

public import CFSG.Quasithin.Background.HSU3NPrime

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def torJMat (n : ℕ) (α : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![α, bar n α * α⁻¹, (bar n α)⁻¹]

theorem det_torJMat {α : K} (hα : α ≠ 0) : (torJMat n α).det = 1 := by
  have hb : bar n α ≠ 0 := (map_ne_zero (bar n)).mpr hα
  rw [torJMat, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp

theorem torJMat_mul {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    torJMat n (α * β) = torJMat n α * torJMat n β := by
  rw [torJMat, torJMat, torJMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val, map_mul]
    field_simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val, map_mul, mul_inv]

theorem torJMat_one : torJMat n (1 : K) = 1 := by
  rw [torJMat, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] noncomputable def torJ (n : ℕ) : Kˣ →* GL (Fin 3) K where
  toFun α :=
    { val := torJMat n (α : K)
      inv := torJMat n ((α⁻¹ : Kˣ) : K)
      val_inv := by
        rw [← torJMat_mul α.ne_zero (α⁻¹).ne_zero, Units.mul_inv, torJMat_one]
      inv_val := by
        rw [← torJMat_mul (α⁻¹).ne_zero α.ne_zero, Units.inv_mul, torJMat_one] }
  map_one' := Units.ext (by
    change torJMat n ((1 : Kˣ) : K) = 1
    rw [Units.val_one, torJMat_one])
  map_mul' α β := Units.ext (by
    change torJMat n ((α * β : Kˣ) : K) = torJMat n (α : K) * torJMat n (β : K)
    rw [Units.val_mul, torJMat_mul α.ne_zero β.ne_zero])

theorem coe_torJ (α : Kˣ) :
    ((torJ n α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = torJMat n (α : K) := rfl

theorem isUnitaryJ_torJMat (hK : Nat.card K = (2 ^ n) ^ 2) {α : K} (hα : α ≠ 0) :
    IsUnitaryJ n (torJMat n α) := by
  have hb : bar n α ≠ 0 := (map_ne_zero (bar n)).mpr hα
  have hbb := bar_bar (n := n) hK α
  unfold IsUnitaryJ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjM, torJMat, antiJ, Matrix.mul_apply, Fin.sum_univ_three, hbb, map_inv₀] <;>
    field_simp

theorem conj_torJ_mem (hK : Nat.card K = (2 ^ n) ^ 2) (α : Kˣ) :
    wittGL * torJ n α * wittGL⁻¹ ∈ StatedSU 3 (2 ^ n) K := by
  refine mem_statedSU ?_ ?_
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, coe_torJ,
      det_torJMat α.ne_zero, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.det_one]
  · rw [← conjM_eq_map_pow, Units.val_mul, Units.val_mul, coe_wittGL, coe_wittGL_inv, coe_torJ]
    exact (isUnitaryM_conj_iff _).mpr (isUnitaryJ_torJMat hK α.ne_zero)

@[expose] noncomputable def torI (hK : Nat.card K = (2 ^ n) ^ 2) :
    Kˣ →* ↥(StatedSU 3 (2 ^ n) K) where
  toFun α := ⟨wittGL * torJ n α * wittGL⁻¹, conj_torJ_mem hK α⟩
  map_one' := Subtype.ext (by simp)
  map_mul' α β := Subtype.ext (by
    simp only [map_mul, Subgroup.coe_mul]
    group)

theorem torI_injective (hK : Nat.card K = (2 ^ n) ^ 2) : Function.Injective (torI (n := n) hK) := by
  intro α β h
  have h1 : (torJ n α : GL (Fin 3) K) = torJ n β := by
    have h2 := congrArg (fun x : ↥(StatedSU 3 (2 ^ n) K) =>
      wittGL⁻¹ * (x : GL (Fin 3) K) * wittGL) h
    simp only [torI, MonoidHom.coe_mk, OneHom.coe_mk] at h2
    simpa [mul_assoc] using h2
  apply Units.ext
  have h3 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simpa [coe_torJ, torJMat] using h3

theorem mem_borGL_of_normalizes (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {δ : GL (Fin 3) K} (hδ : IsUnitaryJ n (δ : Matrix (Fin 3) (Fin 3) K))
    (hN : ∀ u ∈ ujSub n K, δ⁻¹ * u * δ ∈ ujSub n K) : δ ∈ Tri.borGL 3 K := by
  have hfix : ∀ u ∈ ujSub n K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((δ : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1) =
      (δ : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 := by
    intro u hu
    obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries (ujSub_le_uni3 (hN u hu))
    have he : ((δ⁻¹ * u * δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
        Pi.single 0 1 := by
      ext i
      rw [mulVec_single_one]
      fin_cases i
      · simpa using hdiag 0
      · simpa using hlow 1 0 (by decide)
      · simpa using hlow 2 0 (by decide)
    have h1 : (u : Matrix (Fin 3) (Fin 3) K) * (δ : Matrix (Fin 3) (Fin 3) K) =
        (δ : Matrix (Fin 3) (Fin 3) K) * ((δ⁻¹ * u * δ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [mulVec_mulVec, h1, ← mulVec_mulVec, he]
  set v := (δ : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 with hv
  have hv0 : ∀ i, v i = (δ : Matrix (Fin 3) (Fin 3) K) i 0 := fun i => by
    rw [hv, mulVec_single_one]
    rfl
  have hv2 : v 2 = 0 := by
    obtain ⟨u, hu, hu12⟩ := exists_ujSub_one_two hn hK 1
    obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries (ujSub_le_uni3 hu)
    have h := congrFun (hfix u hu) 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    rw [hlow 1 0 (by decide), hdiag 1, hu12] at h
    simpa using h
  have hv1 : v 1 = 0 := by
    obtain ⟨u, hu, hu01⟩ := exists_ujSub_zero_one hn hK 1
    obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries (ujSub_le_uni3 hu)
    have h := congrFun (hfix u hu) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    rw [hdiag 0, hu01, hv2] at h
    simpa using h
  have h10 : (δ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by rw [← hv0]; exact hv1
  have h20 : (δ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by rw [← hv0]; exact hv2
  have h00 : (δ : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    have hdet : (δ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit).ne_zero
    apply hdet
    rw [Matrix.det_fin_three, h0, h10, h20]
    ring
  have h21 : (δ : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have h := congrFun (congrFun hδ 0) 1
    simp [conjM, antiJ, Matrix.mul_apply, Fin.sum_univ_three, h10, h20] at h
    rcases h with h | h
    · exact absurd h h00
    · exact h
  exact Tri.mem_borGL_three.mpr ⟨h10, h20, h21⟩

omit [Finite K] [CharP K 2] in
theorem det_of_mem_statedSU {q : ℕ} {l : GL (Fin 3) K} (hl : l ∈ StatedSU 3 q K) :
    (l : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hl

theorem exists_torJ_mul (hK : Nat.card K = (2 ^ n) ^ 2) {δ : GL (Fin 3) K}
    (hδB : δ ∈ Tri.borGL 3 K) (hδ : wittGL * δ * wittGL⁻¹ ∈ StatedSU 3 (2 ^ n) K) :
    ∃ α : Kˣ, ∃ u ∈ ujSub n K, δ = torJ n α * u := by
  obtain ⟨h10, h20, h21⟩ := Tri.mem_borGL_three.mp hδB
  have hU : IsUnitaryJ n (δ : Matrix (Fin 3) (Fin 3) K) := by
    have h := isUnitaryM_of_mem hK hδ
    rw [Units.val_mul, Units.val_mul, coe_wittGL, coe_wittGL_inv] at h
    exact (isUnitaryM_conj_iff _).mp h
  have hdet : (δ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h := det_of_mem_statedSU hδ
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one,
      one_mul] at h
    exact h
  have h02 : bar n ((δ : Matrix (Fin 3) (Fin 3) K) 0 0) *
      (δ : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := congrFun (congrFun hU 0) 2
    simpa [conjM, antiJ, Matrix.mul_apply, Fin.sum_univ_three, h10, h20] using h
  have hd : (δ : Matrix (Fin 3) (Fin 3) K) 0 0 * (δ : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (δ : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    rw [Matrix.det_of_isUpperTriangular hδB, Fin.prod_univ_three] at hdet
    exact hdet
  have h00 : (δ : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h => by
    rw [h, map_zero, zero_mul] at h02
    exact zero_ne_one h02
  have hb0 : bar n ((δ : Matrix (Fin 3) (Fin 3) K) 0 0) ≠ 0 := (map_ne_zero (bar n)).mpr h00
  set α : Kˣ := Units.mk0 _ h00 with hα
  set u := torJ n α⁻¹ * δ with hu
  have hue : ∀ i j, (u : Matrix (Fin 3) (Fin 3) K) i j =
      ![((δ : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹,
        (bar n ((δ : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹ * (δ : Matrix (Fin 3) (Fin 3) K) 0 0,
        bar n ((δ : Matrix (Fin 3) (Fin 3) K) 0 0)] i * (δ : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    rw [hu, Units.val_mul, coe_torJ, torJMat, Matrix.diagonal_mul]
    fin_cases i <;> simp [hα, map_inv₀]
  have huU : u ∈ Tri.uni3 K := by
    refine Tri.mem_uniGL_of (fun i j hij => ?_) (fun i => ?_)
    · rw [hue, Tri.mem_borGL.mp hδB i j hij, mul_zero]
    · rw [hue]
      fin_cases i
      · simp [h00]
      · simp only [Fin.reduceFinMk, Matrix.cons_val]
        field_simp
        have h22 : (δ : Matrix (Fin 3) (Fin 3) K) 2 2 =
            (bar n ((δ : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹ := eq_inv_of_mul_eq_one_right h02
        rw [h22] at hd
        field_simp at hd
        linear_combination hd
      · simpa using h02
  have hmem : u ∈ ujSub n K := by
    refine ⟨⟨wittGL * u * wittGL⁻¹, ?_, ?_⟩, huU⟩
    · have e : wittGL * u * wittGL⁻¹ =
          (wittGL * torJ n α⁻¹ * wittGL⁻¹) * (wittGL * δ * wittGL⁻¹) := by
        rw [hu]
        group
      rw [e]
      exact Subgroup.mul_mem _ (conj_torJ_mem hK α⁻¹) hδ
    · change wittGL⁻¹ * (wittGL * u * wittGL⁻¹) * wittGL⁻¹⁻¹ = u
      group
  refine ⟨α, u, hmem, ?_⟩
  rw [hu, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem torJ_mem_witt (hK : Nat.card K = (2 ^ n) ^ 2) (α : Kˣ) :
    torJ n α ∈ (StatedSU 3 (2 ^ n) K).map (MulAut.conj (wittGL⁻¹ : GL (Fin 3) K)).toMonoidHom :=
  ⟨wittGL * torJ n α * wittGL⁻¹, conj_torJ_mem hK α, by
    change wittGL⁻¹ * (wittGL * torJ n α * wittGL⁻¹) * wittGL⁻¹⁻¹ = _
    group⟩

theorem torJ_conj_mem_uni3 (α : Kˣ) {u : GL (Fin 3) K} (hu : u ∈ Tri.uni3 K) :
    torJ n α * u * (torJ n α)⁻¹ ∈ Tri.uni3 K := by
  obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries hu
  have e : ((torJ n α * u * (torJ n α)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      torJMat n (α : K) * (u : Matrix (Fin 3) (Fin 3) K) * torJMat n ((α⁻¹ : Kˣ) : K) := by
    rw [Units.val_mul, Units.val_mul, coe_torJ, ← map_inv, coe_torJ]
  refine Tri.mem_uniGL_of (fun i j hij => ?_) (fun i => ?_)
  · rw [e, torJMat, torJMat, Matrix.mul_diagonal, Matrix.diagonal_mul, hlow i j hij]
    simp
  · rw [e, torJMat, torJMat, Matrix.mul_diagonal, Matrix.diagonal_mul, hdiag i]
    have hb : bar n (α : K) ≠ 0 := (map_ne_zero (bar n)).mpr α.ne_zero
    have ha : (α : K) ≠ 0 := α.ne_zero
    fin_cases i <;> simp [map_inv₀]
    field_simp

theorem torJ_conj_mem_ujSub (hK : Nat.card K = (2 ^ n) ^ 2) (α : Kˣ) {u : GL (Fin 3) K}
    (hu : u ∈ ujSub n K) : torJ n α * u * (torJ n α)⁻¹ ∈ ujSub n K :=
  ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (torJ_mem_witt hK α) hu.1)
    (Subgroup.inv_mem _ (torJ_mem_witt hK α)), torJ_conj_mem_uni3 α hu.2⟩

omit [Finite K] in
theorem mem_uiSub_iff {x : GL (Fin 3) K} :
    x ∈ uiSub n K ↔ wittGL⁻¹ * x * wittGL ∈ ujSub n K := by
  rw [uiSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem le_nPrime (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hX1 : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hX2 : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) : 2 * n ≤ E3.nPrime X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  set ν := natAut (StatedSU 3 (2 ^ n) K) with hν
  have hνinj : Function.Injective ν := natAut_injective _
  have hsylUI := isSylowIn_uiSub hn hK
  set P₀ := hsylUI.toSylow with hP₀
  set Ui := (uiSub n K).subgroupOf (StatedSU 3 (2 ^ n) K) with hUi
  have hP₀U : (P₀ : Subgroup ↥(StatedSU 3 (2 ^ n) K)) = Ui := IsSylowIn.coe_toSylow hsylUI
  set U₀ := Ui.map ν with hU₀
  have hU₀L : U₀ ≤ natImage (StatedSU 3 (2 ^ n) K) := Subgroup.map_le_range _ _
  have hU₀p : IsPGroup 2 U₀ := by
    rw [hU₀, ← hP₀U]
    exact P₀.isPGroup'.map _
  obtain ⟨S, hS, hUS⟩ := exists_isSylowIn_ge 2 (hU₀L.trans hX1) hU₀p
  have hSU : S ⊓ natImage (StatedSU 3 (2 ^ n) K) = U₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hUS hU₀L)
    obtain ⟨g, rfl⟩ := hx.2
    have hQ : IsPGroup 2 ((S ⊓ natImage (StatedSU 3 (2 ^ n) K)).comap ν) :=
      hS.isPGroup.to_inf_left.comap_of_injective _ hνinj
    have hle : (P₀ : Subgroup ↥(StatedSU 3 (2 ^ n) K)) ≤
        (S ⊓ natImage (StatedSU 3 (2 ^ n) K)).comap ν := by
      rw [hP₀U]
      intro u hu
      exact ⟨hUS ⟨u, hu, rfl⟩, ⟨u, rfl⟩⟩
    have heq := P₀.is_maximal' hQ hle
    have hg : g ∈ (S ⊓ natImage (StatedSU 3 (2 ^ n) K)).comap ν := hx
    rw [heq, hP₀U] at hg
    exact ⟨g, hg, rfl⟩
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (U₀ : Set (MulAut (StdMod (Fin 3) K))) := by
    intro s hs
    rw [← hSU, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) x,
      Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) x]
  have hTN : ∀ α : Kˣ, torI hK α ∈ Subgroup.normalizer (Ui : Set ↥(StatedSU 3 (2 ^ n) K)) := by
    intro α
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change (x : GL (Fin 3) K) ∈ uiSub n K ↔
      ((torI hK α * x * (torI hK α)⁻¹ : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) ∈ uiSub n K
    rw [mem_uiSub_iff, mem_uiSub_iff]
    have e : wittGL⁻¹ * ((torI hK α * x * (torI hK α)⁻¹ : ↥(StatedSU 3 (2 ^ n) K)) :
        GL (Fin 3) K) * wittGL =
        torJ n α * (wittGL⁻¹ * (x : GL (Fin 3) K) * wittGL) * (torJ n α)⁻¹ := by
      change wittGL⁻¹ * ((wittGL * torJ n α * wittGL⁻¹) * (x : GL (Fin 3) K) *
        (wittGL * torJ n α * wittGL⁻¹)⁻¹) * wittGL = _
      group
    rw [e]
    constructor
    · exact torJ_conj_mem_ujSub hK α
    · intro h
      have h' := torJ_conj_mem_ujSub hK α⁻¹ h
      rw [map_inv] at h'
      simpa [mul_assoc] using h'
  set B := (ν.comp (torI (n := n) hK)).range with hB
  have hSB : (S : Set (MulAut (StdMod (Fin 3) K))) * B ⊆ B * S := by
    rintro _ ⟨s, hs, _, ⟨α, rfl⟩, rfl⟩
    have h1 : s * ν (torI hK α) * s⁻¹ ∈ natImage (StatedSU 3 (2 ^ n) K) :=
      (Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) _).mp ⟨_, rfl⟩
    obtain ⟨γ, hγ⟩ := h1
    have hγN : ν γ ∈ Subgroup.normalizer (U₀ : Set (MulAut (StdMod (Fin 3) K))) := by
      rw [hγ]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSN s hs)
        (Subgroup.le_normalizer_map ν ⟨_, hTN α, rfl⟩)) (Subgroup.inv_mem _ (hSN s hs))
    have hγUi : γ ∈ Subgroup.normalizer (Ui : Set ↥(StatedSU 3 (2 ^ n) K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have h2 := Subgroup.mem_normalizer_iff.mp hγN (ν u)
      rw [Subgroup.mem_map_iff_mem hνinj, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hνinj] at h2
      exact h2
    set δ := wittGL⁻¹ * (γ : GL (Fin 3) K) * wittGL with hδ
    have hδmem : wittGL * δ * wittGL⁻¹ ∈ StatedSU 3 (2 ^ n) K := by
      have e : wittGL * δ * wittGL⁻¹ = (γ : GL (Fin 3) K) := by rw [hδ]; group
      rw [e]
      exact γ.2
    have hδU : IsUnitaryJ n (δ : Matrix (Fin 3) (Fin 3) K) := by
      have h := isUnitaryM_of_mem hK hδmem
      rw [Units.val_mul, Units.val_mul, coe_wittGL, coe_wittGL_inv] at h
      exact (isUnitaryM_conj_iff _).mp h
    have hδN : ∀ u ∈ ujSub n K, δ⁻¹ * u * δ ∈ ujSub n K := by
      intro u hu
      have hPu : wittGL * u * wittGL⁻¹ ∈ uiSub n K := by
        rw [mem_uiSub_iff]
        have e : wittGL⁻¹ * (wittGL * u * wittGL⁻¹) * wittGL = u := by group
        rw [e]
        exact hu
      have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hγUi)
        ⟨_, uiSub_le hPu⟩).mp hPu
      have h4 : ((γ⁻¹ * ⟨_, uiSub_le hPu⟩ * γ⁻¹⁻¹ : ↥(StatedSU 3 (2 ^ n) K)) :
          GL (Fin 3) K) ∈ uiSub n K := h3
      rw [mem_uiSub_iff] at h4
      have e : wittGL⁻¹ * ((γ⁻¹ * ⟨_, uiSub_le hPu⟩ * γ⁻¹⁻¹ : ↥(StatedSU 3 (2 ^ n) K)) :
          GL (Fin 3) K) * wittGL = δ⁻¹ * u * δ := by
        rw [hδ]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [e] at h4
      exact h4
    have hδB := mem_borGL_of_normalizes hn hK hδU hδN
    obtain ⟨α', u', hu', hδe⟩ := exists_torJ_mul hK hδB hδmem
    have hPu' : wittGL * u' * wittGL⁻¹ ∈ uiSub n K := by
      rw [mem_uiSub_iff]
      have e : wittGL⁻¹ * (wittGL * u' * wittGL⁻¹) * wittGL = u' := by group
      rw [e]
      exact hu'
    have hγe : γ = torI hK α' * ⟨_, uiSub_le hPu'⟩ := by
      apply Subtype.ext
      change (γ : GL (Fin 3) K) = (wittGL * torJ n α' * wittGL⁻¹) * (wittGL * u' * wittGL⁻¹)
      have e : (γ : GL (Fin 3) K) = wittGL * δ * wittGL⁻¹ := by rw [hδ]; group
      rw [e, hδe]
      group
    refine ⟨ν (torI hK α'), ⟨α', rfl⟩, ν ⟨_, uiSub_le hPu'⟩ * s,
      S.mul_mem (hUS ⟨_, hPu', rfl⟩) hs, ?_⟩
    change ν (torI hK α') * (ν ⟨_, uiSub_le hPu'⟩ * s) = s * ν (torI hK α)
    rw [← mul_assoc, ← map_mul, ← hγe, hγ]
    group
  have hBS : (B : Set (MulAut (StdMod (Fin 3) K))) * S = S * B := SL3Pair.mul_comm_of_subset hSB
  have hBX : B ≤ X := by
    refine le_trans ?_ hX1
    rw [hB, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm p q]
  have hinj : Function.Injective (ν.comp (torI (n := n) hK)) := hνinj.comp (torI_injective hK)
  have hBc : Nat.card B = 2 ^ (2 * n) - 1 := by
    rw [hB, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units,
      card_eq_two_pow hK]
  have hBodd : Odd (Nat.card B) := by
    rw [hBc]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hBcyc : IsCyclic B :=
    isCyclic_of_surjective (ν.comp (torI hK)).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  exact E3.le_nPrime le_rfl hBX hBcyc hBc hBab hBodd hS hBS

theorem nPrime_eq (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hX1 : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hX2 : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) : E3.nPrime X = 2 * n :=
  le_antisymm (nPrime_le hn hK hX1 hX2) (le_nPrime (by omega) hK hX1 hX2)

end SU3

open SU3 in
theorem H2_SU3_nPrime {V : Type*} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (hL : BinaryNaturalSU3 L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) : E3.nPrime M = 2 * n := by
  obtain ⟨K, _, _, hK, hreal⟩ := hL
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * n) (SU3.card_eq_two_pow hK)
  obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLM hMN
  rw [← nPrime_map_congrHom e M]
  exact nPrime_eq hn hK h1 h2

end H

end CFSG.Quasithin
