module

public import CFSG.RankThree.PartOne.CTP.StdMatrix
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne.EmbeddingTransport CFSG.RankThree.PartOne.EmbeddingFixedResidual
open Matrix CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.Classical

variable {f : ℕ} {F : Type} [Field F]

theorem coordEmbed_map_ringHom {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n : ℕ}
    (i j : Fin n) (X : Matrix (Fin 2) (Fin 2) K) :
    (coordEmbed K i j X).map φ = coordEmbed K' i j (X.map φ) := by
  have h1 : (coordIncl K i j).map φ = coordIncl K' i j := by
    ext k a
    simp only [coordIncl, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have h2 : (coordProj K i j).map φ = coordProj K' i j := by
    unfold coordProj
    rw [Matrix.transpose_map, h1]
  unfold coordEmbed
  rw [Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ), h1,
    h2]

theorem subfieldGL_diagU (K₀ : Subfield F) {n : ℕ} (d : Fin n → K₀ˣ) :
    subfieldGL K₀ n (diagU d) = diagU (fun i => Units.map K₀.subtype.toMonoidHom (d i)) := by
  apply Units.ext
  rw [coe_subfieldGL, diagU_val, diagU_val]
  rw [Matrix.diagonal_map (map_zero _)]
  rfl

section Sub

variable {e : ℕ} (hF : UnitaryFieldData 2 f F) (K₀ : Subfield F) (h₀ : UnitaryFieldData 2 e K₀)
  (hbar : ∀ c : K₀, (h₀.bar c : F) = hF.bar c)

include hbar in
theorem map_blk_subfield_le {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    (blk h₀ hab).map (subfieldGL K₀ n) ≤ blk hF hab := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hab).mp hg
  refine (mem_blk_iff hab).mpr ⟨subfieldGL K₀ 2 X, subfieldGL_mem_gramSU hF h₀ hbar 2 hX, ?_⟩
  rw [coe_subfieldGL, hgX, coordEmbed_map_ringHom, coe_subfieldGL]

@[expose] def Bst (K₀ : Subfield F) : Subgroup (GL (Fin 3) F) :=
  (torusSU 5 3 K₀).map (subfieldGL K₀ 3)

@[expose] noncomputable def Jst (h₀ : UnitaryFieldData 2 e K₀) {a b : Fin 3} (hab : a ≠ b) :
    Subgroup (GL (Fin 3) F) :=
  (blk h₀ hab).map (subfieldGL K₀ 3)

theorem mem_Bst_iff (K₀ : Subfield F) {y : GL (Fin 3) F} :
    y ∈ Bst K₀ ↔ ∃ d₀ : Fin 3 → K₀ˣ, (∀ i, d₀ i ^ 5 = 1) ∧ ∏ i, d₀ i = 1 ∧
      y = diagU (fun i => Units.map K₀.subtype.toMonoidHom (d₀ i)) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨d₀, h1, h2, rfl⟩ := mem_torusSU_iff.mp hg
    exact ⟨d₀, h1, h2, subfieldGL_diagU K₀ d₀⟩
  · rintro ⟨d₀, h1, h2, rfl⟩
    exact ⟨diagU d₀, mem_torusSU_iff.mpr ⟨d₀, h1, h2, rfl⟩, subfieldGL_diagU K₀ d₀⟩

include hbar in
theorem Bst_le_unitarySU (h5 : 5 ∣ 2 ^ e + 1) : Bst K₀ ≤ unitarySU 2 f F 3 := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' := torusSU_le_unitarySU h₀ h5 hg
  rw [unitarySU_eq_gramSU h₀] at hg'
  have := subfieldGL_mem_gramSU hF h₀ hbar 3 hg'
  rw [unitarySU_eq_gramSU hF 3]
  exact this

end Sub

section Beta

variable {e : ℕ} (K₀ : Subfield F) (h₀ : UnitaryFieldData 2 e K₀)

theorem mem_Bst_inf_centralizer_Jst {y : GL (Fin 3) F} {a b : Fin 3} (hab : a ≠ b)
    (hy : y ∈ Bst K₀ ⊓ Subgroup.centralizer (Jst K₀ h₀ hab : Set (GL (Fin 3) F))) :
    ∃ d : Fin 3 → Fˣ, y = diagU d ∧ d a = d b := by
  obtain ⟨d₀, h1, h2, rfl⟩ := (mem_Bst_iff K₀).mp hy.1
  refine ⟨_, rfl, ?_⟩
  set s : GL (Fin 3) K₀ :=
    ((swapCoord h₀ hab : primeFormUnitary h₀ (idGram K₀ 3)) : GL (Fin 3) K₀) with hs'
  have hs : s ∈ blk h₀ hab := ⟨_, swapCoord_mem_coordSU h₀ hab, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hy.2 (subfieldGL K₀ 3 s) ⟨s, hs, rfl⟩
  have := (mul_diagU_eq_iff.mp hcomm) a b
  have hsab : ((subfieldGL K₀ 3 s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) a b = 1 := by
    rw [coe_subfieldGL]
    have := swapCoord_apply h₀ hab
    simp [Matrix.map_apply, hs', this]
  rw [hsab] at this
  exact Units.ext (by simpa using this.symm)

end Beta

section Std

variable {e : ℕ} (hF : UnitaryFieldData 2 f F) (K₀ : Subfield F) (h₀ : UnitaryFieldData 2 e K₀)

noncomputable def betaVec (ζ : Fˣ) (e' : Fin 3) : Fin 3 → Fˣ :=
  fun i => if i = e' then (ζ⁻¹) ^ 2 else ζ

theorem blk_le_centralizer_diagU {a b : Fin 3} (hab : a ≠ b) {d : Fin 3 → Fˣ} (hd : d a = d b) :
    blk hF hab ≤ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F)) := by
  intro g hg
  obtain ⟨X, -, hX⟩ := (mem_blk_iff hab).mp hg
  refine Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, hX, diagU_val]
  exact (diagonal_mul_coordEmbed (fun i => (d i : F)) (by simp [hd]) _).symm

theorem zeta_ne {ζ : Fˣ} (hζ : ζ ^ 3 ≠ 1) : ζ ≠ (ζ⁻¹) ^ 2 := by
  intro h
  apply hζ
  calc ζ ^ 3 = ζ * ζ ^ 2 := by rw [pow_succ']
    _ = (ζ⁻¹) ^ 2 * ζ ^ 2 := by rw [← h]
    _ = 1 := by rw [← mul_pow, inv_mul_cancel, one_pow]

theorem block_of_comm_betaVec {ζ : Fˣ} (hζ : ζ ^ 3 ≠ 1) (e' : Fin 3) {g : GL (Fin 3) F}
    (hg : g * diagU (betaVec ζ e') = diagU (betaVec ζ e') * g) (i j : Fin 3) :
    (i = e' ↔ j = e') ∨ (g : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have h := (mul_diagU_eq_iff.mp hg) i j
  have hne : ((ζ : Fˣ) : F) - (((ζ⁻¹) ^ 2 : Fˣ) : F) ≠ 0 :=
    sub_ne_zero.mpr (fun h' => zeta_ne hζ (Units.ext h'))
  by_cases hi : i = e' <;> by_cases hj : j = e'
  · exact Or.inl ⟨fun _ => hj, fun _ => hi⟩
  · right
    subst hi
    simp only [betaVec, ite_true, hj, ite_false] at h
    have : (g : Matrix (Fin 3) (Fin 3) F) i j * (((ζ : Fˣ) : F) - (((ζ⁻¹) ^ 2 : Fˣ) : F)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp this).resolve_right hne
  · right
    subst hj
    simp only [betaVec, ite_true, hi, ite_false] at h
    have : (g : Matrix (Fin 3) (Fin 3) F) i j * (((ζ : Fˣ) : F) - (((ζ⁻¹) ^ 2 : Fˣ) : F)) = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp this).resolve_right hne
  · exact Or.inl ⟨fun h' => absurd h' hi, fun h' => absurd h' hj⟩

theorem fin_three_cases : ∀ a b e i : Fin 3, a ≠ b → a ≠ e → b ≠ e → i = a ∨ i = b ∨ i = e := by
  decide

end Std

section StdM

variable {e : ℕ} (hF : UnitaryFieldData 2 f F) (K₀ : Subfield F) (h₀ : UnitaryFieldData 2 e K₀)
  (hbar : ∀ c : K₀, (h₀.bar c : F) = hF.bar c)

include hbar in
theorem residual_centralizer_Sab [Finite F] (h5 : 5 ∣ 2 ^ e + 1) (hq : 4 ≤ 2 ^ f) {a b : Fin 3}
    (hab : a ≠ b) :
    inSubgroup perfectResidual (unitarySU 2 f F 3 ⊓ Subgroup.centralizer
      ((Bst K₀ ⊓ Subgroup.centralizer (Jst K₀ h₀ hab : Set (GL (Fin 3) F)) :
        Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F))) = blk hF hab := by
  obtain ⟨e', hea, heb⟩ := CFSG.RankThree.Classical.exists_fin_ne_ne (by norm_num : 3 ≤ 3) a b
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot h₀ Nat.prime_five h5
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : K₀ˣ, IsPrimitiveRoot ζ₀ 5 :=
    ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  set ζ : Fˣ := Units.map K₀.subtype.toMonoidHom ζ₀ with hζdef
  have hζ3 : ζ ^ 3 ≠ 1 := by
    intro h
    have h1 : Units.map K₀.subtype.toMonoidHom (ζ₀ ^ 3) =
        Units.map K₀.subtype.toMonoidHom 1 := by
      rw [map_pow, map_one]
      exact h
    exact hζ₀.pow_ne_one_of_pos_of_lt (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : 3 < 5)
      (Units.map_injective (f := K₀.subtype.toMonoidHom) Subtype.val_injective h1)
  have hβ : diagU (betaVec ζ e') ∈ Bst K₀ ⊓
      Subgroup.centralizer (Jst K₀ h₀ hab : Set (GL (Fin 3) F)) := by
    refine ⟨?_, ?_⟩
    · refine (mem_Bst_iff K₀).mpr ⟨fun i => if i = e' then (ζ₀⁻¹) ^ 2 else ζ₀, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = e'
        · simp only [hi, ite_true]
          have : ((ζ₀⁻¹) ^ 2) ^ 5 = ((ζ₀ ^ 5)⁻¹) ^ 2 := by group
          rw [this, hζ₀.pow_eq_one, inv_one, one_pow]
        · simp only [hi, ite_false]
          exact hζ₀.pow_eq_one
      · rw [Fin.prod_univ_three]
        fin_cases e' <;> simp <;> group
      · congr 1
        funext i
        by_cases hi : i = e' <;> simp [betaVec, hi, hζdef, map_pow, map_inv]
    · intro y hy
      have hy' : y ∈ blk hF hab := map_blk_subfield_le hF K₀ h₀ hbar hab hy
      have := blk_le_centralizer_diagU hF hab (d := betaVec ζ e')
        (by simp [betaVec, hea.symm, heb.symm]) hy'
      exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hcent : unitarySU 2 f F 3 ⊓ Subgroup.centralizer
      ((Bst K₀ ⊓ Subgroup.centralizer (Jst K₀ h₀ hab : Set (GL (Fin 3) F)) :
        Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F)) =
      unitarySU 2 f F 3 ⊓ Subgroup.centralizer ({diagU (betaVec ζ e')} : Set (GL (Fin 3) F)) := by
    apply le_antisymm
    · refine inf_le_inf_left _ (Subgroup.centralizer_le ?_)
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact hβ
    · rintro g ⟨hgS, hgC⟩
      refine ⟨hgS, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      obtain ⟨d', rfl, hd'⟩ := mem_Bst_inf_centralizer_Jst K₀ h₀ hab hy
      have hgβ : g * diagU (betaVec ζ e') = diagU (betaVec ζ e') * g :=
        Subgroup.mem_centralizer_singleton_iff.mp hgC
      refine (mul_diagU_eq_iff.mpr fun i j => ?_).symm
      rcases block_of_comm_betaVec hζ3 e' hgβ i j with hij | h0
      · have hdij : d' i = d' j := by
          by_cases hee : i = e'
          · have : j = e' := hij.mp hee
            rw [hee, this]
          · have hje : j ≠ e' := fun h' => hee (hij.mpr h')
            rcases fin_three_cases a b e' i hab hea.symm heb.symm with rfl | rfl | h'
            · rcases fin_three_cases i b e' j hab hea.symm heb.symm with rfl | rfl | h''
              · rfl
              · exact hd'
              · exact absurd h'' hje
            · rcases fin_three_cases a i e' j hab hea.symm heb.symm with rfl | rfl | h''
              · exact hd'.symm
              · rfl
              · exact absurd h'' hje
            · exact absurd h' hee
        rw [hdij]
        ring
      · rw [h0]
        ring
  rw [hcent]
  exact residual_centralizer_diagU hF hq hab hea.symm heb.symm
    (by simp [betaVec, hea.symm, heb.symm]) (by simp [betaVec, hea.symm]; exact zeta_ne hζ3)

end StdM

end CFSG.RankThree.PartOne.CTP
