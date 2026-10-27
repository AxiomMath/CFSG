module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleCoord

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

section FactorUnique

variable {G : Type*} [Group G]

theorem fu_eq_bot_or_eq {A N : Subgroup G} [IsSimpleGroup A] (hNA : N ≤ A)
    (hn : ∀ f ∈ A, ∀ n ∈ N, f * n * f⁻¹ ∈ N) : N = ⊥ ∨ N = A := by
  haveI : (N.subgroupOf A).Normal :=
    ⟨fun n hn' g => hn g.1 g.2 n.1 hn'⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNA
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hNA h

theorem fu_eq_one_of_central {A : Subgroup G} [IsSimpleGroup A] (hA : ¬ IsMulCommutative A)
    {a : G} (ha : a ∈ A) (hc : ∀ x ∈ A, a * x = x * a) : a = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · have hz : (⟨a, ha⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g.1 g.2).symm
    rw [h, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  · exfalso
    apply hA
    rw [isMulCommutative_iff]
    intro x y
    have hy : y ∈ Subgroup.center A := by rw [h]; trivial
    rw [Subgroup.mem_center_iff] at hy
    exact hy x

theorem fu_mem_sup {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {p : G} (hp : p ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, p = a * b := by
  let S : Subgroup G :=
    { carrier := {p | ∃ a ∈ A, ∃ b ∈ B, p = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h1 : b * a' = a' * b := (hAB a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h1]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hp

theorem fu_conj_mem {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {p : G} (hp : p ∈ A ⊔ B) {x : G} (hx : x ∈ A) : p * x * p⁻¹ ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := fu_mem_sup hAB hp
  have h1 : b * x = x * b := (hAB x hx b hb).symm
  have h2 : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ := by group
  rw [h2]
  exact A.mul_mem (A.mul_mem ha hx) (A.inv_mem ha)

theorem fu_mem_of_centralizes {A B : Subgroup G} [IsSimpleGroup A] (hA : ¬ IsMulCommutative A)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {p : G} (hp : p ∈ A ⊔ B)
    (hc : ∀ x ∈ A, p * x = x * p) : p ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := fu_mem_sup hAB hp
  have ha1 : a = 1 := by
    refine fu_eq_one_of_central hA ha fun x hx => ?_
    have h1 : b * x = x * b := (hAB x hx b hb).symm
    have h2 := hc x hx
    have h3 : a * x * b = x * a * b := by
      calc a * x * b = a * (x * b) := by rw [mul_assoc]
        _ = a * (b * x) := by rw [h1]
        _ = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := h2
        _ = x * a * b := by rw [mul_assoc]
    exact mul_right_cancel h3
  rw [ha1, one_mul]
  exact hb

end FactorUnique

theorem factor_unique {G : Type*} [Group G] {F₁ F₂ F₁' F₂' : Subgroup G}
    (h12 : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a) (h12' : ∀ a ∈ F₁', ∀ b ∈ F₂', a * b = b * a)
    (hinf : F₁ ⊓ F₂ = ⊥) (hinf' : F₁' ⊓ F₂' = ⊥) (hsup : F₁ ⊔ F₂ = F₁' ⊔ F₂')
    [IsSimpleGroup F₁] [IsSimpleGroup F₂] [IsSimpleGroup F₁'] [IsSimpleGroup F₂']
    (hn₁ : ¬ IsMulCommutative F₁) (hn₂ : ¬ IsMulCommutative F₂)
    (hn₁' : ¬ IsMulCommutative F₁') (hn₂' : ¬ IsMulCommutative F₂') :
    (F₁' = F₁ ∧ F₂' = F₂) ∨ (F₁' = F₂ ∧ F₂' = F₁) := by
  have h21 : ∀ a ∈ F₂, ∀ b ∈ F₁, a * b = b * a := fun a ha b hb => (h12 b hb a ha).symm
  have hF₁ : F₁ ≤ F₁ ⊔ F₂ := le_sup_left
  have hF₂ : F₂ ≤ F₁ ⊔ F₂ := le_sup_right
  have hF₁' : F₁' ≤ F₁ ⊔ F₂ := hsup ▸ le_sup_left
  have hF₂' : F₂' ≤ F₁ ⊔ F₂ := hsup ▸ le_sup_right
  have hN₁ : ∀ p ∈ F₁ ⊔ F₂, ∀ x ∈ F₁, p * x * p⁻¹ ∈ F₁ := fun p hp x hx =>
    fu_conj_mem h12 hp hx
  have hN₁' : ∀ p ∈ F₁ ⊔ F₂, ∀ x ∈ F₁', p * x * p⁻¹ ∈ F₁' := fun p hp x hx =>
    fu_conj_mem h12' (hsup ▸ hp) hx
  have hN₂' : ∀ p ∈ F₁ ⊔ F₂, ∀ x ∈ F₂', p * x * p⁻¹ ∈ F₂' := fun p hp x hx =>
    fu_conj_mem (fun a ha b hb => (h12' b hb a ha).symm) (by rw [sup_comm, ← hsup]; exact hp) hx
  have hC₁ : ∀ p ∈ F₁ ⊔ F₂, (∀ x ∈ F₁, p * x = x * p) → p ∈ F₂ := fun p hp hc =>
    fu_mem_of_centralizes hn₁ h12 hp hc
  have hC₂ : ∀ p ∈ F₁ ⊔ F₂, (∀ x ∈ F₂, p * x = x * p) → p ∈ F₁ := fun p hp hc =>
    fu_mem_of_centralizes hn₂ h21 (by rwa [sup_comm] at hp) hc
  have hne₁' : F₁' ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot F₁').mp inferInstance
  have hne₂' : F₂' ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot F₂').mp inferInstance
  rcases fu_eq_bot_or_eq (A := F₁') (N := F₁' ⊓ F₁) inf_le_left
    (fun f hf n hn => ⟨F₁'.mul_mem (F₁'.mul_mem hf hn.1) (F₁'.inv_mem hf),
      hN₁ f (hF₁' hf) n hn.2⟩) with hbot | htop
  ·
    have hcomm : ∀ a ∈ F₁', ∀ x ∈ F₁, a * x = x * a := by
      intro a ha x hx
      have h1 : a * x * a⁻¹ ∈ F₁ := hN₁ a (hF₁' ha) x hx
      have h2 : x * a⁻¹ * x⁻¹ ∈ F₁' := hN₁' x (hF₁ hx) a⁻¹ (F₁'.inv_mem ha)
      have hmem : a * x * a⁻¹ * x⁻¹ ∈ F₁' ⊓ F₁ := by
        refine ⟨?_, F₁.mul_mem h1 (F₁.inv_mem hx)⟩
        have : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
        rw [this]
        exact F₁'.mul_mem ha h2
      rw [hbot, Subgroup.mem_bot] at hmem
      calc a * x = a * x * a⁻¹ * x⁻¹ * (x * a) := by group
        _ = x * a := by rw [hmem, one_mul]
    have hle : F₁' ≤ F₂ := fun a ha => hC₁ a (hF₁' ha) (fun x hx => hcomm a ha x hx)
    have heq₁ : F₁' = F₂ :=
      (fu_eq_bot_or_eq hle (fun f hf n hn => hN₁' f (hF₂ hf) n hn)).resolve_left hne₁'
    have hle' : F₂' ≤ F₁ := fun a ha => hC₂ a (hF₂' ha) (fun x hx =>
      (h12' x (by rw [heq₁]; exact hx) a ha).symm)
    have heq₂ : F₂' = F₁ :=
      (fu_eq_bot_or_eq hle' (fun f hf n hn => hN₂' f (hF₁ hf) n hn)).resolve_left hne₂'
    exact Or.inr ⟨heq₁, heq₂⟩
  ·
    have hle : F₁' ≤ F₁ := inf_eq_left.mp htop
    have heq₁ : F₁' = F₁ :=
      (fu_eq_bot_or_eq hle (fun f hf n hn => hN₁' f (hF₁ hf) n hn)).resolve_left hne₁'
    have hle' : F₂' ≤ F₂ := fun a ha => hC₁ a (hF₂' ha) (fun x hx =>
      (h12' x (by rw [heq₁]; exact hx) a ha).symm)
    have heq₂ : F₂' = F₂ :=
      (fu_eq_bot_or_eq hle' (fun f hf n hn => hN₂' f (hF₂ hf) n hn)).resolve_left hne₂'
    exact Or.inl ⟨heq₁, heq₂⟩

section CT3

variable {K : Type} [Field K]

theorem ct3_act1_add (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act1 (A + B) T = tensor3Act1 A T + tensor3Act1 B T := by
  funext a b c
  simp [tensor3Act1, add_mul, Finset.sum_add_distrib]

theorem ct3_act2_add (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act2 (A + B) T = tensor3Act2 A T + tensor3Act2 B T := by
  funext a b c
  simp [tensor3Act2, add_mul, Finset.sum_add_distrib]

@[expose] def ct3LowSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem ct3_act1_single (b : Fin 2) (T : Tensor3 K) (a' b' c' : Fin 2) :
    tensor3Act1 (Matrix.single b 0 1) T a' b' c' = if b = b' then T a' 0 c' else 0 := by
  simp [tensor3Act1, Matrix.single_apply, Fin.sum_univ_two]

theorem ct3_act2_single (c : Fin 2) (T : Tensor3 K) (a' b' c' : Fin 2) :
    tensor3Act2 (Matrix.single c 0 1) T a' b' c' = if c = c' then T a' b' 0 else 0 := by
  simp [tensor3Act2, Matrix.single_apply, Fin.sum_univ_two]

theorem ct3_comm_single {act : Matrix (Fin 2) (Fin 2) K → Tensor3 K → Tensor3 K}
    (hadd : ∀ A B T, act (A + B) T = act A T + act B T)
    (hmul : ∀ A B T, act (A * B) T = act A (act B T)) (hone : ∀ T, act 1 T = T)
    (g : T3E K) (hcomm : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) K) (T : Tensor3 K),
      g (act (A : Matrix (Fin 2) (Fin 2) K) T) = act (A : Matrix (Fin 2) (Fin 2) K) (g T))
    (b : Fin 2) (T : Tensor3 K) :
    g (act (Matrix.single b 0 1) T) = act (Matrix.single b 0 1) (g T) := by
  have key : ∀ (E : Matrix (Fin 2) (Fin 2) K) (A : Matrix.SpecialLinearGroup (Fin 2) K),
      (A : Matrix (Fin 2) (Fin 2) K) = 1 + E → ∀ T, g (act E T) = act E (g T) := by
    intro E A hA T
    have h := hcomm A T
    rw [hA, hadd, hadd, hone, hone, map_add] at h
    exact add_left_cancel h
  have h01 := key (Matrix.single 0 1 1) (unipSL 1) (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [unipSL_apply, Matrix.single_apply])
  have h10 := key (Matrix.single 1 0 1) ct3LowSL (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ct3LowSL, Matrix.single_apply])
  have h00 : ∀ T, g (act (Matrix.single 0 0 1) T) = act (Matrix.single 0 0 1) (g T) := by
    intro T
    have e : (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) K) =
        Matrix.single 0 1 1 * Matrix.single 1 0 1 := by simp
    rw [e, hmul, hmul, h01, h10]
  fin_cases b
  · exact h00 T
  · exact h10 T

variable [CharP K 2]

theorem ct3_indT_eq (a b c : Fin 2) :
    (indT a b c : Tensor3 K) = tensor3Act1 (Matrix.single b 0 1)
      (tensor3Act2 (Matrix.single c 0 1) (indT a 0 0)) := by
  funext a' b' c'
  rw [ct3_act1_single, ct3_act2_single]
  simp only [indT]
  split_ifs <;> simp_all

theorem ct3_comm_form (g : T3E K) (hr : ∀ h ∈ rowG, g * h = h * g)
    (hc : ∀ h ∈ colG, g * h = h * g) (a b c a' b' c' : Fin 2) :
    g (indT a b c) a' b' c' = if b = b' ∧ c = c' then g (indT a 0 0) a' 0 0 else 0 := by
  have h1 : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) K) (T : Tensor3 K),
      g (tensor3Act1 (A : Matrix (Fin 2) (Fin 2) K) T) =
        tensor3Act1 (A : Matrix (Fin 2) (Fin 2) K) (g T) := fun A T => by
    have h := LinearEquiv.congr_fun (hr (act1E A) ⟨A, rfl⟩) T
    simpa [LinearEquiv.mul_apply, act1E_apply] using h
  have h2 : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) K) (T : Tensor3 K),
      g (tensor3Act2 (A : Matrix (Fin 2) (Fin 2) K) T) =
        tensor3Act2 (A : Matrix (Fin 2) (Fin 2) K) (g T) := fun A T => by
    have h := LinearEquiv.congr_fun (hc (act2E A) ⟨A, rfl⟩) T
    simpa [LinearEquiv.mul_apply, act2E_apply] using h
  have e1 := ct3_comm_single (act := tensor3Act1) ct3_act1_add tensor3Act1_mul tensor3Act1_one
    g h1
  have e2 := ct3_comm_single (act := tensor3Act2) ct3_act2_add tensor3Act2_mul tensor3Act2_one
    g h2
  rw [ct3_indT_eq a b c, e1, e2, ct3_act1_single, ct3_act2_single]
  by_cases hbb : b = b' <;> by_cases hcc : c = c' <;> simp [hbb, hcc]

theorem ct3_decomp (T : Tensor3 K) :
    T = T 0 0 0 • indT 0 0 0 + T 0 0 1 • indT 0 0 1 + T 0 1 0 • indT 0 1 0 +
      T 0 1 1 • indT 0 1 1 + T 1 0 0 • indT 1 0 0 + T 1 0 1 • indT 1 0 1 +
      T 1 1 0 • indT 1 1 0 + T 1 1 1 • indT 1 1 1 := by
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [indT]

theorem ct3_act0_indT (M : Matrix (Fin 2) (Fin 2) K) (a b c a' b' c' : Fin 2) :
    tensor3Act0 M (indT a b c) a' b' c' = if b = b' ∧ c = c' then M a' a else 0 := by
  simp only [tensor3Act0, indT]
  rw [Finset.sum_eq_single a (fun a'' _ ha'' => by simp [ha''])
    (fun h => absurd (Finset.mem_univ a) h)]
  by_cases hb : b = b'
  · by_cases hc : c = c'
    · subst hb
      subst hc
      simp
    · have hc' : ¬ c' = c := fun h => hc h.symm
      simp [hc, hc']
  · have hb' : ¬ b' = b := fun h => hb h.symm
    simp [hb, hb']

theorem ct3_eq_act0 (g : T3E K) (hr : ∀ h ∈ rowG, g * h = h * g)
    (hc : ∀ h ∈ colG, g * h = h * g) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, ∀ T, g T = tensor3Act0 M T := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, ∀ a a', M a' a = g (indT a 0 0) a' 0 0 :=
    ⟨Matrix.of fun a' a => g (indT a 0 0) a' 0 0, fun _ _ => rfl⟩
  have hbasis : ∀ a b c, g (indT a b c) = tensor3Act0 M (indT a b c) := by
    intro a b c
    funext a' b' c'
    rw [ct3_comm_form g hr hc a b c a' b' c', ct3_act0_indT, hM]
  refine ⟨M, fun T => ?_⟩
  rw [ct3_decomp T]
  simp only [map_add, map_smul, tensor3Act0_add, tensor3Act0_smul, hbasis]

theorem ct3_det (g : T3E K) (hO : g ∈ Ok 0) (M : Matrix (Fin 2) (Fin 2) K)
    (hM : ∀ T, g T = tensor3Act0 M T) : M.det = 1 := by
  have h := mem_Ok.mp hO (indT 0 0 0 + indT 1 1 1)
  rw [hM] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [Qk, tensor3Form, tensor3Act0, indT, Fin.sum_univ_two] at h
  rw [Matrix.det_fin_two]
  linear_combination h - M 0 1 * M 1 0 * h2

end CT3

section CT3Main

variable {K : Type} [Field K]

theorem ct3 [CharP K 2] (g : T3E K) (hO : g ∈ Ok 0) (hr : ∀ h ∈ rowG, g * h = h * g)
    (hc : ∀ h ∈ colG, g * h = h * g) : g ∈ slotG := by
  obtain ⟨M, hM⟩ := ct3_eq_act0 g hr hc
  have hdet := ct3_det g hO M hM
  refine ⟨(⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) K), ?_⟩
  exact LinearEquiv.ext fun T => (act0E_apply _ T).trans (hM T).symm

end CT3Main

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
