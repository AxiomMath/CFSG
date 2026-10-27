module

public import CFSG.Quasithin.Background.G1Module

public section

open Matrix

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F]

theorem actSub_one {n : ℕ} (A : Submodule F (Fin n → F)) :
    actSub (1 : Matrix.SpecialLinearGroup (Fin n) F) A = A := by
  ext v
  rw [mem_actSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hv
    exact ⟨v, hv, one_smul _ _⟩

theorem actSub_mul {n : ℕ} (g h : Matrix.SpecialLinearGroup (Fin n) F)
    (A : Submodule F (Fin n → F)) : actSub (g * h) A = actSub g (actSub h A) := by
  ext v
  rw [mem_actSub, mem_actSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨h • w, mem_actSub.2 ⟨w, hw, rfl⟩, (mul_smul g h w).symm⟩
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_actSub.1 hw'
    exact ⟨w, hw, mul_smul g h w⟩

theorem actSub_inv_eq {n : ℕ} {m : Matrix.SpecialLinearGroup (Fin n) F}
    {A B : Submodule F (Fin n → F)} (h : actSub m A = B) : actSub m⁻¹ B = A := by
  rw [← h, ← actSub_mul, inv_mul_cancel, actSub_one]

theorem isPoint_actSub {n : ℕ} (g : Matrix.SpecialLinearGroup (Fin n) F)
    {A : Submodule F (Fin n → F)} (hA : IsPoint A) : IsPoint (actSub g A) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F)) := by
    intro x y hxy
    have : g • x = g • y := hxy
    exact MulAction.injective g this
  unfold IsPoint at *
  rw [← hA]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj A)).symm

theorem exists_gen {n : ℕ} {A : Submodule F (Fin n → F)} (hA : IsPoint A) :
    ∃ v : Fin n → F, v ≠ 0 ∧ ∀ w, w ∈ A ↔ ∃ c : F, w = c • v := by
  obtain ⟨v, hv0, hv⟩ := (finrank_eq_one_iff' (K := F) (V := A)).1 hA
  refine ⟨v, fun h => hv0 (Subtype.ext h), fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨c, rfl⟩
    exact A.smul_mem c v.2

theorem actSub_Vi_eq_of_smul {m : Matrix.SpecialLinearGroup (Fin 2) F} {z : Fin 2}
    {v : Fin 2 → F} {A : Submodule F (Fin 2 → F)}
    (hm : m • (Pi.single z (1 : F) : Fin 2 → F) = v) (hA : ∀ w, w ∈ A ↔ ∃ c : F, w = c • v) :
    actSub m (Vi F 2 z) = A := by
  have key : ∀ c : F, m • (c • (Pi.single z (1 : F) : Fin 2 → F)) = c • v := fun c => by
    rw [smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', hm]
  ext x
  rw [mem_actSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [key]
    exact (hA _).2 ⟨c, rfl⟩
  · intro hx
    obtain ⟨c, rfl⟩ := (hA x).1 hx
    exact ⟨c • (Pi.single z (1 : F) : Fin 2 → F),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), key c⟩

theorem exists_std_pair {A₁ A₂ : Submodule F (Fin 2 → F)} (h₁ : IsPoint A₁) (h₂ : IsPoint A₂)
    (hne : A₁ ≠ A₂) : ∃ m : Matrix.SpecialLinearGroup (Fin 2) F,
      actSub m (Vi F 2 0) = A₁ ∧ actSub m (Vi F 2 1) = A₂ := by
  obtain ⟨v₁, hv₁0, hv₁⟩ := exists_gen h₁
  obtain ⟨v₂, hv₂0, hv₂⟩ := exists_gen h₂
  set d : F := v₁ 0 * v₂ 1 - v₂ 0 * v₁ 1 with hd
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hne
    have hd' : v₁ 0 * v₂ 1 = v₂ 0 * v₁ 1 := sub_eq_zero.1 hd0
    obtain ⟨a, hva⟩ : ∃ a : F, v₂ = a • v₁ := by
      by_cases h0 : v₁ 0 = 0
      · have h1 : v₁ 1 ≠ 0 := fun h1 => hv₁0 (by
          funext i
          fin_cases i
          · exact h0
          · exact h1)
        refine ⟨v₂ 1 / v₁ 1, ?_⟩
        have h2 : v₂ 0 = 0 := by
          rw [h0, zero_mul] at hd'
          exact (mul_eq_zero.1 hd'.symm).resolve_right h1
        funext i
        fin_cases i
        · simp [h2, h0]
        · simp [h1]
      · refine ⟨v₂ 0 / v₁ 0, ?_⟩
        funext i
        fin_cases i
        · show v₂ 0 = (v₂ 0 / v₁ 0) * v₁ 0
          field_simp
        · show v₂ 1 = (v₂ 0 / v₁ 0) * v₁ 1
          field_simp
          linear_combination hd'
    have ha : a ≠ 0 := by
      rintro rfl
      exact hv₂0 (by rw [hva, zero_smul])
    ext w
    rw [hv₁ w, hv₂ w]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c * a⁻¹, by rw [hva, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * a, by rw [hva, smul_smul]⟩
  let M : Matrix (Fin 2) (Fin 2) F := !![v₁ 0, d⁻¹ * v₂ 0; v₁ 1, d⁻¹ * v₂ 1]
  have hM : M.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    linear_combination hd
  let m : Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, hM⟩
  refine ⟨m, actSub_Vi_eq_of_smul (v := v₁) ?_ hv₁, actSub_Vi_eq_of_smul (v := d⁻¹ • v₂) ?_ ?_⟩
  · funext i
    rw [smul_eq_mulVec']
    change (M *ᵥ (Pi.single 0 1 : Fin 2 → F)) i = v₁ i
    fin_cases i <;> simp [M]
  · funext i
    rw [smul_eq_mulVec']
    change (M *ᵥ (Pi.single 1 1 : Fin 2 → F)) i = (d⁻¹ • v₂) i
    fin_cases i <;> simp [M]
  · intro w
    rw [hv₂ w]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c * d, by rw [smul_smul, mul_assoc, mul_inv_cancel₀ hd0, mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * d⁻¹, by rw [smul_smul]⟩

section Halves

variable {U : Type*} [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]

theorem Vhat_one_eq : Vhat F 2 1 = Vi F 2 0 := by
  ext v
  rw [mem_Vhat, mem_Vi]
  constructor
  · intro h k hk
    have : k = 1 := by fin_cases k <;> simp_all
    subst this
    exact h
  · intro h
    exact h 1 (by decide)

theorem IsFlag.eq_two {A B : Submodule F (Fin 2 → F)} (h : IsFlag A B) : A = B := by
  obtain ⟨hA, hB, hAB⟩ := h
  refine Submodule.eq_of_le_of_finrank_eq hAB ?_
  unfold IsPoint at hA
  unfold IsHyperplane at hB
  omega

theorem map_actU_mul (g h : Matrix.SpecialLinearGroup (Fin 2) F) (Y : AddSubgroup U) :
    Y.map (actU (g * h)) = (Y.map (actU h)).map (actU g) := by
  rw [AddSubgroup.map_map]
  congr 1
  ext u
  exact mul_smul g h u

theorem map_actU_one (Y : AddSubgroup U) :
    Y.map (actU (1 : Matrix.SpecialLinearGroup (Fin 2) F)) = Y := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [actU] using hy
  · intro hu
    exact ⟨u, hu, by simp [actU]⟩

theorem map_actU_stab {Y : AddSubgroup U}
    (hinv : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, actSub k (Vi F 2 0) = Vi F 2 0 →
      ∀ y ∈ Y, k • y ∈ Y)
    {k : Matrix.SpecialLinearGroup (Fin 2) F} (hk : actSub k (Vi F 2 0) = Vi F 2 0) :
    Y.map (actU k) = Y := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hinv k hk y hy
  · intro hu
    have hk' : actSub k⁻¹ (Vi F 2 0) = Vi F 2 0 := by
      have := actSub_mul k⁻¹ k (Vi F 2 0)
      rw [inv_mul_cancel, actSub_one, hk] at this
      exact this.symm
    exact ⟨k⁻¹ • u, hinv _ hk' u hu, by simp [actU]⟩

open Classical in
@[expose] noncomputable def halfMap (Y : AddSubgroup U) :
    Submodule F (Fin 2 → F) → AddSubgroup U := fun A =>
  if h : IsPoint A then
    Y.map (actU (Classical.choose (exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 h)))
  else ⊥

theorem halfMap_actSub {Y : AddSubgroup U}
    (hinv : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, actSub k (Vi F 2 0) = Vi F 2 0 →
      ∀ y ∈ Y, k • y ∈ Y)
    (h : Matrix.SpecialLinearGroup (Fin 2) F) :
    halfMap Y (actSub h (Vi F 2 0)) = Y.map (actU h) := by
  have hp : IsPoint (actSub h (Vi F 2 0)) := isPoint_actSub h (isPoint_Vi 0)
  simp only [halfMap, hp, ↓reduceDIte]
  set c := Classical.choose (exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 hp) with hcdef
  have hc : actSub c (Vi F 2 0) = actSub h (Vi F 2 0) :=
    Classical.choose_spec (exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 hp)
  have hstab : actSub (h⁻¹ * c) (Vi F 2 0) = Vi F 2 0 := by
    rw [actSub_mul, hc, ← actSub_mul, inv_mul_cancel, actSub_one]
  have e : c = h * (h⁻¹ * c) := by group
  rw [e, map_actU_mul, map_actU_stab hinv hstab]

theorem exists_G13Hyp_of_halves (Y : AddSubgroup U) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hinv : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, actSub k (Vi F 2 0) = Vi F 2 0 →
      ∀ y ∈ Y, k • y ∈ Y)
    (hcomm : commU (Rij F (0 : Fin 2) 1) ≤ Y) (hfix : Y ≤ fixU (Rij F (0 : Fin 2) 1))
    (hdisj : Y ⊓ Y.map (actU g) = ⊥) (hsup : Y ⊔ Y.map (actU g) = ⊤) :
    ∃ φ : Submodule F (Fin 2 → F) → AddSubgroup U, G13Hyp F 2 U φ ∧ φ (Vi F 2 0) = Y := by
  have h1 : halfMap Y (Vi F 2 0) = Y := by
    have := halfMap_actSub hinv 1
    rwa [actSub_one, map_actU_one] at this
  have hroot : ∀ (h t : Matrix.SpecialLinearGroup (Fin 2) F),
      t ∈ rootGroup (actSub h (Vi F 2 0)) (actSub h (Vi F 2 0)) → h⁻¹ * t * h ∈ Rij F 0 1 := by
    intro h t ht
    rw [Rij, Vhat_one_eq]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have h1 := ht.1 (h • v)
      obtain ⟨a, ha, hav⟩ := mem_actSub.1 h1
      have : (h⁻¹ * t * h) • v - v = a := by
        have e : (h⁻¹ * t * h) • v - v = h⁻¹ • (t • h • v - h • v) := by
          rw [mul_smul, mul_smul, smul_sub, inv_smul_smul]
        rw [e, ← hav, inv_smul_smul]
      rw [this]
      exact ha
    · have hhv : h • v ∈ actSub h (Vi F 2 0) := mem_actSub.2 ⟨v, hv, rfl⟩
      rw [mul_smul, mul_smul, ht.2 _ hhv, inv_smul_smul]
  by_cases hgst : actSub g (Vi F 2 0) = Vi F 2 0
  ·
    have hYg : Y.map (actU g) = Y := map_actU_stab hinv hgst
    rw [hYg, inf_idem] at hdisj
    rw [hYg, sup_idem] at hsup
    have hall : ∀ A : Submodule F (Fin 2 → F), halfMap Y A = ⊥ := by
      intro A
      by_cases hA : IsPoint A
      · obtain ⟨h, rfl⟩ := exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 hA
        rw [halfMap_actSub hinv, hdisj, AddSubgroup.map_bot]
      · simp only [halfMap, hA, ↓reduceDIte]
    have hU0 : ∀ u : U, u = 0 := by
      intro u
      have : u ∈ Y := by rw [hsup]; exact AddSubgroup.mem_top u
      rw [hdisj] at this
      exact AddSubgroup.mem_bot.1 this
    refine ⟨halfMap Y, ⟨?_, ?_, ?_, ?_, ?_⟩, h1⟩
    · intro k A hA
      rw [hall, hall, AddSubgroup.map_bot]
    · intro A B hAB
      rw [hall]
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro w ⟨t, ht, u, rfl⟩
      rw [hU0 u, smul_zero, sub_zero]
      exact AddSubgroup.zero_mem _
    · intro A B hAB D hD hDB
      rw [hall]
      exact bot_le
    · intro A₁ A₂ _ _ _
      simp [hall]
    · rw [eq_top_iff]
      intro u _
      rw [hU0 u]
      exact AddSubgroup.zero_mem _
  · refine ⟨halfMap Y, ⟨?_, ?_, ?_, ?_, ?_⟩, h1⟩
    ·
      intro k A hA
      obtain ⟨h, rfl⟩ := exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 hA
      rw [← actSub_mul, halfMap_actSub hinv, halfMap_actSub hinv, map_actU_mul]
    ·
      intro A B hAB
      have hAB' : A = B := IsFlag.eq_two hAB
      subst hAB'
      obtain ⟨h, rfl⟩ := exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 hAB.1
      rw [halfMap_actSub hinv]
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro w ⟨t, ht, u, rfl⟩
      have hs := hroot h t ht
      have hmem : (h⁻¹ * t * h) • (h⁻¹ • u) - h⁻¹ • u ∈ Y :=
        hcomm (AddSubgroup.subset_closure ⟨_, hs, h⁻¹ • u, rfl⟩)
      refine ⟨_, hmem, ?_⟩
      show h • ((h⁻¹ * t * h) • (h⁻¹ • u) - h⁻¹ • u) = t • u - u
      rw [smul_sub, ← mul_smul, ← mul_smul, smul_inv_smul]
      have e : h * (h⁻¹ * t * h) * h⁻¹ = t := by group
      rw [e]
    ·
      intro A B hAB D hD hDB
      have hAB' : A = B := IsFlag.eq_two hAB
      subst hAB'
      have hDA : D = A := by
        refine Submodule.eq_of_le_of_finrank_eq hDB ?_
        have h1 : Module.finrank F D = 1 := hD
        have h2 : Module.finrank F A = 1 := hAB.1
        omega
      subst hDA
      obtain ⟨h, rfl⟩ := exists_actSub_Vi_eq (n := 2) (le_refl 2) 0 hD
      rw [halfMap_actSub hinv]
      rintro _ ⟨y, hy, rfl⟩ t ht
      have hs := hroot h t ht
      have hsy : (h⁻¹ * t * h) • y = y := hfix hy _ hs
      show t • h • y = h • y
      have e : t * h = h * (h⁻¹ * t * h) := by group
      rw [← mul_smul, e, mul_smul, hsy]
    ·
      intro A₁ A₂ hA₁ hA₂ hne
      have hA₀' : IsPoint (actSub g (Vi F 2 0)) := isPoint_actSub g (isPoint_Vi 0)
      obtain ⟨m₀, hm₀a, hm₀b⟩ := exists_std_pair (isPoint_Vi (F := F) (n := 2) 0) hA₀' (Ne.symm hgst)
      obtain ⟨m₁, hm₁a, hm₁b⟩ := exists_std_pair hA₁ hA₂ hne
      have hk₁ : actSub (m₁ * m₀⁻¹) (Vi F 2 0) = A₁ := by
        rw [actSub_mul, actSub_inv_eq hm₀a, hm₁a]
      have hk₂ : actSub (m₁ * m₀⁻¹) (actSub g (Vi F 2 0)) = A₂ := by
        rw [actSub_mul, actSub_inv_eq hm₀b, hm₁b]
      have e1 : halfMap Y A₁ = Y.map (actU (m₁ * m₀⁻¹)) := by
        rw [← hk₁, halfMap_actSub hinv]
      have e2 : halfMap Y A₂ = (Y.map (actU g)).map (actU (m₁ * m₀⁻¹)) := by
        rw [← hk₂, ← actSub_mul, halfMap_actSub hinv, map_actU_mul]
      rw [e1, e2, ← AddSubgroup.map_inf _ _ _ (MulAction.injective (m₁ * m₀⁻¹)), hdisj,
        AddSubgroup.map_bot]
    ·
      rw [eq_top_iff, ← hsup]
      have h2 : halfMap Y (actSub g (Vi F 2 0)) = Y.map (actU g) := halfMap_actSub hinv g
      refine sup_le ?_ ?_
      · have := le_iSup₂ (f := fun (A : Submodule F (Fin 2 → F)) (_ : IsPoint A) => halfMap Y A)
          (Vi F 2 0) (isPoint_Vi 0)
        rw [h1] at this
        exact this
      · have := le_iSup₂ (f := fun (A : Submodule F (Fin 2 → F)) (_ : IsPoint A) => halfMap Y A)
          (actSub g (Vi F 2 0)) (isPoint_actSub g (isPoint_Vi 0))
        rw [h2] at this
        exact this

end Halves

end CFSG.Quasithin.G1
