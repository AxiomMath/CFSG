module

public import CFSG.Quasithin.Background.SimsG44

public section

namespace CFSG.Quasithin.SimsG4

namespace G44Nonsplit

variable {F : Type} [Field F]

theorem exists_ne_zero_ne_one {n : ℕ} (hn : Nat.card F = 2 ^ n) (hn1 : 1 < n) :
    ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
  by_contra h
  have h01 : ∀ l : F, l ≠ 0 → l = 1 := fun l hl0 => by
    by_contra hl1
    exact h ⟨l, hl0, hl1⟩
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : F) else 0 := by
    intro l
    by_cases hl : l = 0
    · exact ⟨false, by simp [hl]⟩
    · exact ⟨true, by simp [h01 l hl]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  rw [hn, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
  omega

variable [CharP F 2]

theorem orthAct_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 3 → F) :
    orthAct g v = ![g 0 0 ^ 2 * v 0 + g 0 1 ^ 2 * v 2,
      g 0 0 * g 1 0 * v 0 + v 1 + g 0 1 * g 1 1 * v 2, g 1 0 ^ 2 * v 0 + g 1 1 ^ 2 * v 2] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  funext i
  fin_cases i <;> simp [orthAct, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (g 0 0 * g 0 1 * v 1) * h2
  · linear_combination v 1 * hdet + (g 0 1 * g 1 0 * v 1) * h2
  · linear_combination (g 1 0 * g 1 1 * v 1) * h2

theorem orthAct_line (g : Matrix.SpecialLinearGroup (Fin 2) F) (c : F) :
    orthAct g ![0, c, 0] = ![0, c, 0] := by
  rw [orthAct_apply]
  funext i
  fin_cases i <;> simp

theorem orthAct_slUpper (v : Fin 3 → F) :
    orthAct (slUpper 1) v = ![v 0 + v 2, v 1 + v 2, v 2] := by
  rw [orthAct_apply]
  funext i
  fin_cases i <;> simp [slUpper]

theorem orthAct_slLower (v : Fin 3 → F) :
    orthAct (slLower 1) v = ![v 0, v 0 + v 1, v 0 + v 2] := by
  rw [orthAct_apply]
  funext i
  fin_cases i <;> simp [slLower]

theorem not_mem_of_orthAct_invariant {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {A : Set (Fin 3 → F)}
    (hsub : ∀ v ∈ A, ∀ w ∈ A, v - w ∈ A)
    (hact : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ v ∈ A, orthAct g v ∈ A)
    (hline : ∀ c : F, ![0, c, 0] ∈ A → c = 0) (c : F) : ![0, c, 1] ∉ A := by
  intro ha₁
  have hmem : ∀ v w : Fin 3 → F, v ∈ A → v = w → w ∈ A := fun _ _ h e => e ▸ h
  have ha₂ : ![1, 1, 0] ∈ A := hmem _ _ (hsub _ (hact (slUpper 1) _ ha₁) _ ha₁) (by
    rw [orthAct_slUpper]
    funext i
    fin_cases i <;> simp)
  obtain ⟨t, ht⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin 2) F,
      (t : Matrix (Fin 2) (Fin 2) F) = !![l, 0; 0, l⁻¹] :=
    ⟨⟨!![l, 0; 0, l⁻¹], by simp [Matrix.det_fin_two, hl0]⟩, rfl⟩
  have ha₃ : ![l ^ 2, 1, 0] ∈ A := hmem _ _ (hact t _ ha₂) (by
    rw [orthAct_apply, ht]
    funext i
    fin_cases i <;> simp)
  have ha₄ : ![0, l ^ 2, l ^ 2] ∈ A := hmem _ _ (hsub _ (hact (slLower 1) _ ha₃) _ ha₃) (by
    rw [orthAct_slLower]
    funext i
    fin_cases i <;> simp)
  have ha₅ : ![l ^ 2, l ^ 2, 0] ∈ A := hmem _ _ (hsub _ (hact (slUpper 1) _ ha₄) _ ha₄) (by
    rw [orthAct_slUpper]
    funext i
    fin_cases i <;> simp)
  have ha₆ : ![0, l ^ 2 - 1, 0] ∈ A := hmem _ _ (hsub _ ha₅ _ ha₃) (by
    funext i
    fin_cases i <;> simp)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : (l - 1) ^ 2 = 0 := by linear_combination hline _ ha₆ + (1 - l) * h2
  exact hl1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq))

theorem sup_center_ne {X : Type*} [Group X] (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hφ : Function.Surjective φ) {P : Subgroup X} (ψ : ↥P ≃* Multiplicative (Fin 3 → F))
    (hψ : ∀ (g : X) (x y : ↥P), g * (x : X) * g⁻¹ = (y : X) →
      Multiplicative.toAdd (ψ y) = orthAct (φ g) (Multiplicative.toAdd (ψ x)))
    {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {W : Subgroup X} (hWP : W ≤ P) (hWn : W.Normal)
    (hWZ : W ⊓ Subgroup.center X = ⊥) : W ⊔ Subgroup.center X ≠ P := by
  intro hsup
  have hZ : ∀ (z : X) (hz : z ∈ Subgroup.center X) (hzP : z ∈ P),
      ∃ c : F, Multiplicative.toAdd (ψ ⟨z, hzP⟩) = ![0, c, 0] := by
    intro z hz hzP
    have hfix : ∀ g : X, orthAct (φ g) (Multiplicative.toAdd (ψ ⟨z, hzP⟩)) =
        Multiplicative.toAdd (ψ ⟨z, hzP⟩) := fun g =>
      (hψ g ⟨z, hzP⟩ ⟨z, hzP⟩ (by rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right])).symm
    obtain ⟨gu, hgu⟩ := hφ (slUpper 1)
    obtain ⟨gl, hgl⟩ := hφ (slLower 1)
    have e1 := congrFun (hfix gu) 1
    have e2 := congrFun (hfix gl) 1
    rw [hgu, orthAct_slUpper] at e1
    rw [hgl, orthAct_slLower] at e2
    refine ⟨Multiplicative.toAdd (ψ ⟨z, hzP⟩) 1, funext fun i => ?_⟩
    fin_cases i
    · simpa using e2
    · simp
    · simpa using e1
  obtain ⟨A, hA⟩ : ∃ A : Set (Fin 3 → F), ∀ v, v ∈ A ↔
      ∃ (w : X) (hw : w ∈ W), Multiplicative.toAdd (ψ ⟨w, hWP hw⟩) = v :=
    ⟨_, fun _ => Iff.rfl⟩
  have hsub : ∀ v ∈ A, ∀ v' ∈ A, v - v' ∈ A := by
    intro v hv v' hv'
    obtain ⟨w, hw, rfl⟩ := (hA v).mp hv
    obtain ⟨w', hw', rfl⟩ := (hA v').mp hv'
    refine (hA _).mpr ⟨w * w'⁻¹, W.mul_mem hw (W.inv_mem hw'), ?_⟩
    rw [show (⟨w * w'⁻¹, hWP (W.mul_mem hw (W.inv_mem hw'))⟩ : ↥P) =
      ⟨w, hWP hw⟩ * (⟨w', hWP hw'⟩ : ↥P)⁻¹ from rfl, map_mul, map_inv, toAdd_mul, toAdd_inv,
      sub_eq_add_neg]
  have hact : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ v ∈ A, orthAct g v ∈ A := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := (hA v).mp hv
    obtain ⟨x, rfl⟩ := hφ g
    have hc : x * w * x⁻¹ ∈ W := hWn.conj_mem w hw x
    exact (hA _).mpr ⟨x * w * x⁻¹, hc, hψ x ⟨w, hWP hw⟩ ⟨x * w * x⁻¹, hWP hc⟩ rfl⟩
  have hline : ∀ c : F, ![0, c, 0] ∈ A → c = 0 := by
    intro c hc
    obtain ⟨w, hw, hwc⟩ := (hA _).mp hc
    have hwZ : w ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      have hgw : g * w * g⁻¹ ∈ W := hWn.conj_mem w hw g
      have h := hψ g ⟨w, hWP hw⟩ ⟨g * w * g⁻¹, hWP hgw⟩ rfl
      rw [hwc, orthAct_line, ← hwc] at h
      have h' : g * w * g⁻¹ = w :=
        congrArg Subtype.val (ψ.injective (Multiplicative.toAdd.injective h))
      calc g * w = g * w * g⁻¹ * g := by rw [inv_mul_cancel_right]
        _ = w * g := by rw [h']
    have hw1 : w = 1 := by
      have hmem : w ∈ W ⊓ Subgroup.center X := Subgroup.mem_inf.mpr ⟨hw, hwZ⟩
      rwa [hWZ, Subgroup.mem_bot] at hmem
    subst hw1
    rw [show (⟨1, hWP hw⟩ : ↥P) = 1 from rfl, map_one, toAdd_one] at hwc
    simpa using (congrFun hwc 1).symm
  haveI := hWn
  have hp : ((ψ.symm (Multiplicative.ofAdd ![0, 0, 1]) : ↥P) : X) ∈ W ⊔ Subgroup.center X := by
    rw [hsup]
    exact (ψ.symm _).2
  obtain ⟨w, hw, z, hz, hwz⟩ := Subgroup.mem_sup_of_normal_left.mp hp
  have hzP : z ∈ P := by
    rw [← hsup]
    exact Subgroup.mem_sup_right hz
  obtain ⟨c, hc⟩ := hZ z hz hzP
  refine not_mem_of_orthAct_invariant hl0 hl1 hsub hact hline (-c) ((hA _).mpr ⟨w, hw, ?_⟩)
  have hpwz : ψ.symm (Multiplicative.ofAdd ![0, 0, 1]) = ⟨w, hWP hw⟩ * ⟨z, hzP⟩ :=
    Subtype.ext hwz.symm
  have h := congrArg (fun q => Multiplicative.toAdd (ψ q)) hpwz
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, map_mul, toAdd_mul, hc] at h
  rw [eq_sub_of_add_eq h.symm]
  funext i
  fin_cases i <;> simp

end G44Nonsplit

theorem g44_nonsplit {F : Type} [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (d : V ≃ₗ[F] V) (hdSp : d ∈ spGroup B) (hdT : IsTransv d) :
    1 < n → ∀ W : Subgroup ↥(xHat B d), W ≤ CFSG.pCore 2 ↥(xHat B d) → W.Normal →
      W ⊓ Subgroup.center ↥(xHat B d) = ⊥ →
      W ⊔ Subgroup.center ↥(xHat B d) ≠ CFSG.pCore 2 ↥(xHat B d) := by
  intro hn1 W hWP hWn hWZ
  obtain ⟨⟨φ, hφ, -, ψ, hψ⟩, -⟩ := g44_xHat B halt hnd hdim d hdSp hdT
  obtain ⟨l, hl0, hl1⟩ := G44Nonsplit.exists_ne_zero_ne_one hn hn1
  exact G44Nonsplit.sup_center_ne φ hφ ψ hψ hl0 hl1 hWP hWn hWZ

end CFSG.Quasithin.SimsG4
