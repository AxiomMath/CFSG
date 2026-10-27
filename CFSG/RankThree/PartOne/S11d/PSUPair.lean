module

public import CFSG.RankThree.PartOne.S11d.PSURational

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.OddIso CFSG.LinearGroups

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

section Basic

theorem coe_toLin_eq (g : GL (Fin n) K) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = linOf g := by
  rw [Matrix.GeneralLinearGroup.coe_toLin]
  rfl

@[expose] noncomputable def tvMat {a : Fin n → K} (ha : idForm h n a a = 0) (c : K) :
    GL (Fin n) K :=
  Matrix.GeneralLinearGroup.toLin.symm (hermTransvectionGL (idForm h n) ha c)

theorem linOf_tvMat {a : Fin n → K} (ha : idForm h n a a = 0) (c : K) :
    linOf (tvMat h ha c) = hermTransvection (idForm h n) a c := by
  rw [← coe_toLin_eq]
  change ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
    (hermTransvectionGL (idForm h n) ha c)) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem tvMat_mem_gramSU {a : Fin n → K} (ha : idForm h n a a = 0) {c : K} (hc : c + h.bar c = 0) :
    tvMat h ha c ∈ gramSU h (idGram K n) := by
  rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n)]
  change Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
    (hermTransvectionGL (idForm h n) ha c)) ∈ _
  rw [MulEquiv.apply_symm_apply]
  exact mem_sesqSpecialUnitaryGroup.mpr
    ⟨fun x y => hermTransvection_isometry (idForm_isSymm h n) ha hc x y,
      det_hermTransvection (idForm h n) ha c⟩

theorem bar_comm (σ : K ≃+* K) (c : K) : h.bar (σ c) = σ (h.bar c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem idForm_comp_σ (σ : K ≃+* K) (u v : Fin n → K) :
    idForm h n (σ ∘ u) (σ ∘ v) = σ (idForm h n u v) := by
  rw [idForm_apply, idForm_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Function.comp_apply, Function.comp_apply, map_mul, bar_comm]

theorem linOf_glAut (σ : K ≃+* K) (g : GL (Fin n) K) (v : Fin n → K) :
    linOf (glAut σ g) (σ ∘ v) = σ ∘ linOf g v := by
  rw [linOf_apply, linOf_apply, coe_glAut]
  funext i
  exact (RingHom.map_mulVec σ.toRingHom (g : Matrix (Fin n) (Fin n) K) v i).symm

theorem linOf_glAut_tvMat (σ : K ≃+* K) {a : Fin n → K} (ha : idForm h n a a = 0) (c : K) :
    linOf (glAut σ (tvMat h ha c)) = hermTransvection (idForm h n) (σ ∘ a) (σ c) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, x = σ ∘ y := ⟨σ.symm ∘ x, by funext i; simp⟩
  rw [linOf_glAut, linOf_tvMat, hermTransvection_apply, hermTransvection_apply, idForm_comp_σ]
  funext i
  simp [map_add, map_mul]

end Basic

section Fixed

variable {A : GL (Fin n) K} (hodd : Odd p)

@[expose] noncomputable def Dq (hÂp : linOf A ^ p = 1) : Subgroup (GL (Fin n) K) :=
  haveI : CharP K 2 := h.charP
  (Dfix (idForm h n) (isCompl_ker_range hodd hÂp)).comap
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem linOf_isom_A (hA : A ∈ gramSU h (idGram K n)) :
    ∀ v w, idForm h n (linOf A v) (linOf A w) = idForm h n v w :=
  linOf_isom h ((mem_gramSU_iff_unitary h).mp hA).1

theorem mem_Dq_iff (hA : A ∈ gramSU h (idGram K n)) (hÂp : linOf A ^ p = 1) (g : GL (Fin n) K) :
    g ∈ Dq h hodd hÂp ↔ g ∈ gramSU h (idGram K n) ∧
      ∀ w ∈ LinearMap.range (linOf A - 1), linOf g w = w := by
  have : CharP K 2 := h.charP
  change Matrix.GeneralLinearGroup.toLin g ∈ Dfix (idForm h n) (isCompl_ker_range hodd hÂp) ↔ _
  rw [mem_Dfix_iff' (idForm_isSymm h n) (idForm_separatingLeft h n) (linOf_isom_A h hA) hodd hÂp,
    toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) g]
  simp only [coe_toLin_eq]

theorem Dq_le_gramSU (hA : A ∈ gramSU h (idGram K n)) (hÂp : linOf A ^ p = 1) :
    Dq h hodd hÂp ≤ gramSU h (idGram K n) := fun g hg => ((mem_Dq_iff h hodd hA hÂp g).mp hg).1

theorem tvMat_mem_Dq (hA : A ∈ gramSU h (idGram K n)) (hÂp : linOf A ^ p = 1) {a : Fin n → K}
    (haV : a ∈ LinearMap.ker (linOf A - 1)) (ha : idForm h n a a = 0) {c : K}
    (hc : c + h.bar c = 0) : tvMat h ha c ∈ Dq h hodd hÂp := by
  have : CharP K 2 := h.charP
  refine (mem_Dq_iff h hodd hA hÂp _).mpr ⟨tvMat_mem_gramSU h ha hc, fun w hw => ?_⟩
  rw [linOf_tvMat, hermTransvection_apply, fix_perp (linOf_isom_A h hA) haV hw,
    mul_zero, zero_smul, add_zero]

theorem pair_Dq (hA : A ∈ gramSU h (idGram K n)) (hÂp : linOf A ^ p = 1) {σ : K ≃+* K}
    {a b : Fin n → K} (haV : a ∈ LinearMap.ker (linOf A - 1))
    (hbV : b ∈ LinearMap.ker (linOf A - 1)) (hσa : σ ∘ a = a) (hσb : σ ∘ b = b)
    (haa : idForm h n a a = 0) (hbb : idForm h n b b = 0) (hab : idForm h n a b ≠ 0) :
    ∃ t₁ ∈ Dq h hodd hÂp, glAut σ t₁ = t₁ ∧ t₁ ^ 2 = 1 ∧ t₁ ≠ 1 ∧
      ∃ t₂ ∈ Dq h hodd hÂp, glAut σ t₂ = t₂ ∧ t₂ ^ 2 = 1 ∧ t₂ ≠ 1 ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hc : (1 : K) + h.bar 1 = 0 := by rw [map_one, h11]
  have hbar1 : h.bar (idForm h n a b) = idForm h n b a := ((idForm_isSymm h n).eq a b)
  have ha0 : a ≠ 0 := fun e => hab (by rw [e, map_zero, LinearMap.zero_apply])
  have hb0 : b ≠ 0 := fun e => hab (by rw [e, map_zero])
  have hba : idForm h n b a ≠ 0 := by
    rw [← hbar1]; exact fun e => hab ((map_eq_zero h.bar).mp e)
  have hsq : ∀ (u : Fin n → K) (hu : idForm h n u u = 0), tvMat h hu 1 ^ 2 = 1 := by
    intro u hu
    apply linOf_injective
    rw [linOf_pow, linOf_one, linOf_tvMat, pow_two, Module.End.mul_eq_comp,
      hermTransvection_comp (idForm h n) hu, h11, hermTransvection_zero]
    rfl
  have hfix : ∀ (u : Fin n → K) (hu : idForm h n u u = 0), σ ∘ u = u →
      glAut σ (tvMat h hu 1) = tvMat h hu 1 := by
    intro u hu hσu
    apply linOf_injective
    rw [linOf_glAut_tvMat, linOf_tvMat, hσu, map_one]
  have hne : ∀ (u v : Fin n → K) (hu : idForm h n u u = 0), u ≠ 0 → idForm h n u v ≠ 0 →
      tvMat h hu 1 ≠ 1 := by
    intro u v hu hu0 huv hT
    have h1 := congrArg (fun g => linOf g v) hT
    simp only [linOf_tvMat, hermTransvection_apply, linOf_one, Module.End.one_apply] at h1
    have h3 : (1 * idForm h n u v) • u = 0 := by
      have := h1
      rw [add_eq_left] at this
      exact this
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact huv (by simpa using h4)
    · exact hu0 h4
  refine ⟨tvMat h haa 1, tvMat_mem_Dq h hodd hA hÂp haV haa hc, hfix a haa hσa, hsq a haa,
    hne a b haa ha0 hab, tvMat h hbb 1, tvMat_mem_Dq h hodd hA hÂp hbV hbb hc, hfix b hbb hσb,
    hsq b hbb, hne b a hbb hb0 hba, ?_⟩
  intro hcomm
  have h1 := congrArg (fun g => linOf g b) hcomm
  simp only [linOf_mul, Module.End.mul_apply, linOf_tvMat, hermTransvection_apply, map_add,
    map_smul, hbb, mul_zero, zero_smul, add_zero] at h1
  have h5 : (idForm h n a b * idForm h n b a) • b = 0 := by
    have h6 : (b + (1 * idForm h n a b) • a) - (b + (1 * idForm h n a b) •
        (a + (1 * idForm h n b a) • b)) = (-(idForm h n a b * idForm h n b a)) • b := by
      module
    have h7 : (-(idForm h n a b * idForm h n b a)) • b = 0 := by rw [← h6, h1, sub_self]
    rwa [neg_smul, neg_eq_zero] at h7
  rcases smul_eq_zero.mp h5 with h8 | h8
  · exact mul_ne_zero hab hba h8
  · exact hb0 h8

theorem exists_smul_of_hermTransvection_eq {V : Type} [AddCommGroup V] [Module K V]
    {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} (hBl : B.SeparatingLeft) {u w : V} {c : K}
    (hc : c ≠ 0) (hu : u ≠ 0) (hT : hermTransvection B u c = hermTransvection B w c) :
    ∃ κ : K, u = κ • w := by
  obtain ⟨x, hx⟩ : ∃ x, B u x ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu (hBl u hall)
  have h1 := congrArg (fun T : V →ₗ[K] V => T x) hT
  simp only [hermTransvection_apply] at h1
  have h2 : (c * B u x) • u = (c * B w x) • w := by
    have := h1
    rw [add_right_inj] at this
    exact this
  refine ⟨B w x / B u x, ?_⟩
  have hcx : c * B u x ≠ 0 := mul_ne_zero hc hx
  calc u = (c * B u x)⁻¹ • ((c * B u x) • u) := by rw [inv_smul_smul₀ hcx]
    _ = (c * B u x)⁻¹ • ((c * B w x) • w) := by rw [h2]
    _ = (B w x / B u x) • w := by
      rw [smul_smul]
      congr 1
      field_simp

theorem σ_sq_of_fix {σ : K ≃+* K} (hfix : ∀ c : K, h.bar c = c → σ c = c) (x : K) :
    σ (σ x) = x := by
  have hbb : ∀ y, h.bar (h.bar y) = y := h.bar_bar
  have ht : σ (x + h.bar x) = x + h.bar x :=
    hfix _ (by rw [map_add, hbb, add_comm])
  have hn : σ (x * h.bar x) = x * h.bar x := hfix _ (by rw [map_mul, hbb, mul_comm])
  have hbarσ : σ (h.bar x) = h.bar (σ x) := (bar_comm h σ x).symm
  have e1 : σ x + h.bar (σ x) = x + h.bar x := by rw [← hbarσ, ← map_add]; exact ht
  have e2 : σ x * h.bar (σ x) = x * h.bar x := by rw [← hbarσ, ← map_mul]; exact hn
  have hprod : (σ x - x) * (σ x - h.bar x) = 0 := by linear_combination (σ x) * e1 - e2
  rcases mul_eq_zero.mp hprod with h1 | h1
  · have : σ x = x := sub_eq_zero.mp h1
    rw [this, this]
  · have : σ x = h.bar x := sub_eq_zero.mp h1
    rw [this, hbarσ, this, hbb]

include hodd in
theorem exists_hyperbolic_pair (hA : A ∈ gramSU h (idGram K n)) (hÂp : linOf A ^ p = 1)
    (hm : 2 ≤ Module.finrank K (LinearMap.ker (linOf A - 1))) :
    ∃ a b : Fin n → K, a ∈ LinearMap.ker (linOf A - 1) ∧ b ∈ LinearMap.ker (linOf A - 1) ∧
      idForm h n a a = 0 ∧ idForm h n b b = 0 ∧ idForm h n a b = 1 := by
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hB₁ := fixSpace_isSymm (A := linOf A) (idForm_isSymm h n)
  have hBl₁ := fixSpace_sep (idForm_separatingLeft h n) (linOf_isom_A h hA) hodd hÂp
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB₁ hBl₁
  have hn : ∀ i j, idForm h n ((e i : LinearMap.ker (linOf A - 1)) : Fin n → K)
      ((e j : LinearMap.ker (linOf A - 1)) : Fin n → K) = if i = j then 1 else 0 :=
    fun i j => he i j
  let i0 : Fin (Module.finrank K (LinearMap.ker (linOf A - 1))) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K (LinearMap.ker (linOf A - 1))) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun e => by simpa [i0, i1] using congrArg Fin.val e
  have hn00 : idForm h n ((e i0 : LinearMap.ker (linOf A - 1)) : Fin n → K)
      ((e i0 : LinearMap.ker (linOf A - 1)) : Fin n → K) = 1 := by rw [hn]; simp
  have hn11 : idForm h n ((e i1 : LinearMap.ker (linOf A - 1)) : Fin n → K)
      ((e i1 : LinearMap.ker (linOf A - 1)) : Fin n → K) = 1 := by rw [hn]; simp
  have hn01 : idForm h n ((e i0 : LinearMap.ker (linOf A - 1)) : Fin n → K)
      ((e i1 : LinearMap.ker (linOf A - 1)) : Fin n → K) = 0 := by rw [hn]; simp [h01]
  have hn10 : idForm h n ((e i1 : LinearMap.ker (linOf A - 1)) : Fin n → K)
      ((e i0 : LinearMap.ker (linOf A - 1)) : Fin n → K) = 0 := by rw [hn]; simp [Ne.symm h01]
  set a₀ : LinearMap.ker (linOf A - 1) := e i0 + e i1 with ha₀def
  have ha₀ : (idForm h n).domRestrict₁₂ (LinearMap.ker (linOf A - 1))
      (LinearMap.ker (linOf A - 1)) a₀ a₀ = 0 := by
    simp only [LinearMap.domRestrict₁₂_apply, ha₀def, map_add,
      LinearMap.add_apply, hn00, hn11, hn01, hn10, add_zero, zero_add]
    exact h11
  have ha₀ne : a₀ ≠ 0 := by
    intro e0
    have : (idForm h n).domRestrict₁₂ (LinearMap.ker (linOf A - 1))
        (LinearMap.ker (linOf A - 1)) a₀ (e i0) = 1 := by
      simp only [LinearMap.domRestrict₁₂_apply, ha₀def, map_add,
        LinearMap.add_apply, hn00, hn10, add_zero]
    rw [e0, map_zero, LinearMap.zero_apply] at this
    exact zero_ne_one this
  obtain ⟨⟨b, hb1, hb2⟩, -⟩ := hermitian_hyperbolic_splitting h hB₁ hBl₁ ha₀ne ha₀
  exact ⟨a₀, b, a₀.2, b.2, ha₀, hb2, hb1⟩

theorem linOf_conj_tvMat {e : GL (Fin n) K} (he : e ∈ gramSU h (idGram K n)) (a : Fin n → K)
    (c : K) :
    linOf e * hermTransvection (idForm h n) a c * linOf e⁻¹ =
      hermTransvection (idForm h n) (linOf e a) c := by
  have hg : Matrix.GeneralLinearGroup.toLin e ∈ sesqUnitaryGroup (idForm h n) :=
    (toLin_mem_sesqUnitaryGroup_iff e).mpr ((mem_gramSU_iff_unitary h).mp he).1
  have := conj_hermTransvection hg a c
  have hinv : (((Matrix.GeneralLinearGroup.toLin e)⁻¹ : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) = linOf e⁻¹ := by
    rw [← map_inv, coe_toLin_eq]
  rw [coe_toLin_eq, hinv] at this
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  exact this

include hodd in
theorem outer_Dq (hA : A ∈ gramSU h (idGram K n)) (hÂp : linOf A ^ p = 1)
    (hm : 2 ≤ Module.finrank K (LinearMap.ker (linOf A - 1))) {σ : K ≃+* K}
    (hσ2 : ∃ x, σ (σ x) ≠ x) :
    ∀ e ∈ Dq h hodd hÂp, ¬ ∀ g ∈ Dq h hodd hÂp, glAut σ g = e * g * e⁻¹ := by
  intro e he hcon
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hc1 : (1 : K) + h.bar 1 = 0 := by rw [map_one, h11]
  have heU : e ∈ gramSU h (idGram K n) := Dq_le_gramSU h hodd hA hÂp he
  have hBl := idForm_separatingLeft h n
  have hinvE : ∀ v, linOf e⁻¹ (linOf e v) = v := fun v => by simp
  have hσne : ∀ u : Fin n → K, u ≠ 0 → σ ∘ u ≠ 0 := fun u hu e0 =>
    hu (funext fun i => σ.injective (by simpa using congrFun e0 i))
  have hline : ∀ u : Fin n → K, u ∈ LinearMap.ker (linOf A - 1) → ∀ hu : idForm h n u u = 0,
      u ≠ 0 → ∃ μ : K, linOf e⁻¹ (σ ∘ u) = μ • u := by
    intro u huV hu hu0
    have hT := hcon (tvMat h hu 1) (tvMat_mem_Dq h hodd hA hÂp huV hu hc1)
    have h1 := congrArg linOf hT
    rw [linOf_glAut_tvMat, map_one, linOf_mul, linOf_mul, linOf_tvMat,
      linOf_conj_tvMat h heU] at h1
    obtain ⟨κ, hκ⟩ := exists_smul_of_hermTransvection_eq hBl one_ne_zero (hσne u hu0) h1
    exact ⟨κ, by rw [hκ, map_smul, hinvE]⟩
  obtain ⟨a, b, haV, hbV, haa, hbb, hab⟩ := exists_hyperbolic_pair h hodd hA hÂp hm
  have hba : idForm h n b a = 1 := by rw [← (idForm_isSymm h n).eq a b, hab, map_one]
  have ha0 : a ≠ 0 := fun e0 => by
    rw [e0, map_zero, LinearMap.zero_apply] at hab
    exact zero_ne_one hab
  have hb0 : b ≠ 0 := fun e0 => by rw [e0, map_zero] at hab; exact zero_ne_one hab
  obtain ⟨μa, hμa⟩ := hline a haV haa ha0
  obtain ⟨μb, hμb⟩ := hline b hbV hbb hb0
  have hμa0 : μa ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμa
    have := congrArg (linOf e) hμa
    rw [map_zero] at this
    have h3 : linOf e (linOf e⁻¹ (σ ∘ a)) = σ ∘ a := by simp
    exact hσne a ha0 (h3.symm.trans this)
  have hrel : ∀ l : K, h.bar l = l → l ≠ 0 → σ l * μb = μa * l := by
    intro l hl hl0
    have hvV : a + l • b ∈ LinearMap.ker (linOf A - 1) :=
      Submodule.add_mem _ haV (Submodule.smul_mem _ _ hbV)
    have hvv : idForm h n (a + l • b) (a + l • b) = 0 := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
        hbb, hab, hba, hl]
      linear_combination h2 * l
    have hv0 : a + l • b ≠ 0 := by
      intro e0
      have := congrArg (idForm h n a) e0
      simp only [map_add, map_smul, smul_eq_mul, haa, hab, map_zero] at this
      exact hl0 (by simpa using this)
    obtain ⟨μ, hμ⟩ := hline _ hvV hvv hv0
    have hcomp : σ ∘ (a + l • b) = σ ∘ a + σ l • σ ∘ b := by funext i; simp
    rw [hcomp, map_add, map_smul, hμa, hμb] at hμ
    have e1 := congrArg (idForm h n a) hμ
    have e2 := congrArg (idForm h n b) hμ
    simp only [map_add, map_smul, smul_eq_mul, haa, hbb, hab, hba] at e1 e2
    linear_combination e1 - l * e2
  have hμb : μb = μa := by
    have := hrel 1 (by rw [map_one]) one_ne_zero
    rw [map_one] at this
    linear_combination this
  have hfix : ∀ l : K, h.bar l = l → σ l = l := by
    intro l hl
    by_cases hl0 : l = 0
    · rw [hl0, map_zero]
    · have := hrel l hl hl0
      rw [hμb] at this
      exact mul_right_cancel₀ hμa0 (by linear_combination this)
  obtain ⟨x, hx⟩ := hσ2
  exact hx (σ_sq_of_fix h hfix x)

end Fixed

end CFSG.RankThree.PartOne
