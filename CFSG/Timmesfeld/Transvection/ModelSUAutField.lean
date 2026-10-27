module

public import CFSG.Timmesfeld.Transvection.ModelSUPerp

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem exists_anisotropic_perp [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hm : 5 ≤ m) {a d e e' : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (he : e ∈ perpPair σ a d) (he' : e' ∈ perpPair σ a d) (hee : uForm σ e e = 0)
    (he'e' : uForm σ e' e' = 0) (hee' : uForm σ e e' = 1) :
    ∃ g ∈ perpPair σ a d, uForm σ e g = 0 ∧ uForm σ e' g = 0 ∧ uForm σ g g ≠ 0 := by
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_forall_uForm_eq_zero σ ![a, d, e, e'] (by
    rw [Fintype.card_fin]
    exact Nat.lt_of_lt_of_le (by norm_num) hm)
  have hxa : uForm σ a x = 0 := by simpa using hx 0
  have hxd : uForm σ d x = 0 := by simpa using hx 1
  have hxe : uForm σ e x = 0 := by simpa using hx 2
  have hxe' : uForm σ e' x = 0 := by simpa using hx 3
  have hxP : x ∈ perpPair σ a d := ⟨hxa, hxd⟩
  by_cases hxx : uForm σ x x = 0
  · obtain ⟨y₀, hy₀⟩ := exists_uForm_eq_one (σ := σ) hx0
    have hyP : projPair σ a d y₀ ∈ perpPair σ a d := projPair_mem hσ haa hdd had y₀
    have hxy : uForm σ x (projPair σ a d y₀) = 1 := by
      rw [uForm_projPair_of_mem_perpPair hσ hxP, hy₀]
    set y' := projPair σ e e' (projPair σ a d y₀) with hy'def
    have hy'e : uForm σ e y' = 0 :=
      (projPair_mem hσ hee he'e' hee' (projPair σ a d y₀)).1
    have hy'e' : uForm σ e' y' = 0 :=
      (projPair_mem hσ hee he'e' hee' (projPair σ a d y₀)).2
    have hy'P : y' ∈ perpPair σ a d := by
      rw [hy'def, projPair]
      exact (perpPair σ a d).sub_mem ((perpPair σ a d).sub_mem hyP
        ((perpPair σ a d).smul_mem _ he)) ((perpPair σ a d).smul_mem _ he')
    have hxy' : uForm σ x y' = 1 := by
      rw [hy'def, uForm_projPair_of_mem_perpPair hσ (show x ∈ perpPair σ e e' from ⟨hxe, hxe'⟩),
        hxy]
    have hfix : σ (1 + uForm σ y' y') = 1 + uForm σ y' y' := by
      rw [map_add, map_one, uForm_conj σ hσ y' y']
    obtain ⟨c, hc⟩ := htr (1 + uForm σ y' y') hfix
    refine ⟨y' + c • x, (perpPair σ a d).add_mem hy'P ((perpPair σ a d).smul_mem c hxP),
      ?_, ?_, ?_⟩
    · rw [uForm_add_right, uForm_smul_right, hxe, mul_zero, add_zero]
      exact hy'e
    · rw [uForm_add_right, uForm_smul_right, hxe', mul_zero, add_zero]
      exact hy'e'
    · have hy'x : uForm σ y' x = 1 := by rw [← uForm_conj σ hσ, hxy', map_one]
      have hgg : uForm σ (y' + c • x) (y' + c • x) = 1 := by
        simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hxx,
          mul_zero, add_zero, hy'x, hxy', mul_one]
        linear_combination hc + CharTwo.add_self_eq_zero (uForm σ y' y')
      rw [hgg]
      exact one_ne_zero
  · exact ⟨x, hxP, hxe, hxe', hxx⟩

private theorem uForm_add_add (x y : Fin m → F) :
    uForm σ (x + y) (x + y) = uForm σ x x + uForm σ x y + uForm σ y x + uForm σ y y := by
  rw [uForm_add_left, uForm_add_right, uForm_add_right]
  abel

private theorem mulVec_phi_eigen_eq_of_isotropic_pair [CharP F 2]
    {g e f' v₁ v₂ : Fin m → F} {M : Matrix (Fin m) (Fin m) F} {φ : F ≃+* F}
    {y c μe μf κ₁ κ₂ : F} (hge : uForm σ g e = 0) (hgf : uForm σ g f' = 0)
    (hv₁ : v₁ = e + y • f' + c • g) (hv₂ : v₂ = v₁ + f')
    (hf'0 : f' ≠ 0) (hγ0 : uForm σ g g ≠ 0) (hc : c ≠ 0)
    (hμe : M *ᵥ (fun i => φ (e i)) = μe • e)
    (hμf : M *ᵥ (fun i => φ (f' i)) = μf • f')
    (hκ₁ : M *ᵥ (fun i => φ (v₁ i)) = κ₁ • v₁)
    (hκ₂ : M *ᵥ (fun i => φ (v₂ i)) = κ₂ • v₂) :
    φ c * uForm σ g (M *ᵥ fun i => φ (g i)) = μf * c * uForm σ g g := by
  subst hv₁
  subst hv₂
  have hphi₁ : (fun i => φ ((e + y • f' + c • g) i)) =
      (fun i => φ (e i)) + φ y • (fun i => φ (f' i)) + φ c • (fun i => φ (g i)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  have hphi₂ : (fun i => φ ((e + y • f' + c • g + f') i)) =
      (fun i => φ ((e + y • f' + c • g) i)) + (fun i => φ (f' i)) := by
    funext i
    simp only [Pi.add_apply, map_add]
  have hgv : uForm σ g (e + y • f' + c • g) = c * uForm σ g g := by
    simp only [uForm_add_right, uForm_smul_right, hge, hgf, mul_zero, add_zero, zero_add]
  have hgv₂ : uForm σ g (e + y • f' + c • g + f') = c * uForm σ g g := by
    rw [uForm_add_right, hgf, add_zero, hgv]
  have hsame : uForm σ g (M *ᵥ (fun i => φ ((e + y • f' + c • g + f') i))) =
      uForm σ g (M *ᵥ (fun i => φ ((e + y • f' + c • g) i))) := by
    rw [hphi₂, mulVec_add, uForm_add_right, hμf, uForm_smul_right, hgf, mul_zero, add_zero]
  have h₁ : uForm σ g (M *ᵥ (fun i => φ ((e + y • f' + c • g) i))) =
      κ₁ * (c * uForm σ g g) := by
    rw [hκ₁, uForm_smul_right, hgv]
  have h₂ : uForm σ g (M *ᵥ (fun i => φ ((e + y • f' + c • g + f') i))) =
      κ₂ * (c * uForm σ g g) := by
    rw [hκ₂, uForm_smul_right, hgv₂]
  have hκ : κ₁ = κ₂ := by
    have h := h₁.symm.trans (hsame.symm.trans h₂)
    exact mul_right_cancel₀ (mul_ne_zero hc hγ0) h
  have hf'eq : (fun i => φ (f' i)) =
      (fun i => φ ((e + y • f' + c • g + f') i)) -
        (fun i => φ ((e + y • f' + c • g) i)) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, map_add]
    ring
  have hdiff : M *ᵥ (fun i => φ (f' i)) = κ₁ • f' := by
    rw [hf'eq, mulVec_sub, hκ₂, hκ₁, hκ, ← smul_sub]
    congr 1
    abel
  have hμκ : μf = κ₁ := by
    have h : μf • f' = κ₁ • f' := by rw [← hμf, hdiff]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf'0
    refine mul_right_cancel₀ hi ?_
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun h i
  have hmain : uForm σ g (M *ᵥ (fun i => φ ((e + y • f' + c • g) i))) =
      φ c * uForm σ g (M *ᵥ fun i => φ (g i)) := by
    rw [hphi₁, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hμe, hμf]
    simp only [uForm_add_right, uForm_smul_right, hge, hgf, mul_zero, add_zero, zero_add]
  rw [← hmain, h₁, hμκ]
  ring

theorem ringEquiv_eq_refl_of_isotropic_eigen [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hm : 5 ≤ m) {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (M : Matrix (Fin m) (Fin m) F)
    (hMinj : ∀ v, M *ᵥ v = 0 → v = 0) (φ : F ≃+* F)
    (hM : ∀ u ∈ perpPair σ a d, uForm σ u u = 0 →
      ∃ μ : F, M *ᵥ (fun i => φ (u i)) = μ • u) :
    φ = RingEquiv.refl F := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨e, heP, he0, hee⟩ := (suGeomFacts_holds hσ htr hnorm hm4 haa hdd had).exists_iso
  obtain ⟨f', hfP, hff, hef⟩ :=
    (suGeomFacts_holds hσ htr hnorm hm4 haa hdd had).partner heP he0 hee
  obtain ⟨g, hgP, heg, hfg, hgg⟩ :=
    exists_anisotropic_perp hσ htr hm haa hdd had heP hfP hee hff hef
  have hf'0 : f' ≠ 0 := by
    rintro rfl
    rw [uForm_zero_right] at hef
    exact zero_ne_one hef
  have hfe : uForm σ f' e = 1 := by rw [← uForm_conj σ hσ, hef, map_one]
  have hge : uForm σ g e = 0 := by rw [← uForm_conj σ hσ, heg, map_zero]
  have hgf : uForm σ g f' = 0 := by rw [← uForm_conj σ hσ, hfg, map_zero]
  obtain ⟨μe, hμe⟩ := hM e heP hee
  obtain ⟨μf, hμf⟩ := hM f' hfP hff
  have hμf0 : μf ≠ 0 := by
    intro h
    have h0 : M *ᵥ (fun i => φ (f' i)) = 0 := by rw [hμf, h, zero_smul]
    have h1 := hMinj _ h0
    apply hf'0
    funext i
    exact (map_eq_zero φ).1 (congrFun h1 i)
  have key : ∀ c : F, c ≠ 0 →
      φ c * uForm σ g (M *ᵥ fun i => φ (g i)) = μf * c * uForm σ g g := by
    intro c hc
    obtain ⟨y, hy⟩ := htr (σ c * c * uForm σ g g) (by
      rw [map_mul, map_mul, hσ, uForm_conj σ hσ g g]
      ring)
    have hv₁P : e + y • f' + c • g ∈ perpPair σ a d :=
      (perpPair σ a d).add_mem ((perpPair σ a d).add_mem heP
        ((perpPair σ a d).smul_mem y hfP)) ((perpPair σ a d).smul_mem c hgP)
    have hv₂P : e + y • f' + c • g + f' ∈ perpPair σ a d :=
      (perpPair σ a d).add_mem hv₁P hfP
    have hv₁f : uForm σ (e + y • f' + c • g) f' = 1 := by
      simp only [uForm_add_left, uForm_smul_left, hef, hff, hgf, mul_zero, mul_one, add_zero]
    have hfv₁ : uForm σ f' (e + y • f' + c • g) = 1 := by
      rw [← uForm_conj σ hσ, hv₁f, map_one]
    have hgv₁ : uForm σ g (e + y • f' + c • g) = c * uForm σ g g := by
      simp only [uForm_add_right, uForm_smul_right, hge, hgf, mul_zero, add_zero, zero_add]
    have hv₁iso : uForm σ (e + y • f' + c • g) (e + y • f' + c • g) = 0 := by
      simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hee, hff,
        hef, hfe, heg, hge, hfg, hgf, mul_zero, mul_one, add_zero]
      linear_combination hy + CharTwo.add_self_eq_zero (σ c * c * uForm σ g g)
    have hv₂iso : uForm σ (e + y • f' + c • g + f') (e + y • f' + c • g + f') = 0 := by
      rw [uForm_add_add, hv₁iso, hv₁f, hfv₁, hff]
      simp only [zero_add, add_zero]
      exact CharTwo.add_self_eq_zero 1
    obtain ⟨κ₁, hκ₁⟩ := hM (e + y • f' + c • g) hv₁P hv₁iso
    obtain ⟨κ₂, hκ₂⟩ := hM (e + y • f' + c • g + f') hv₂P hv₂iso
    exact mulVec_phi_eigen_eq_of_isotropic_pair hge hgf rfl rfl hf'0 hgg hc hμe hμf hκ₁ hκ₂
  have hw : uForm σ g (M *ᵥ fun i => φ (g i)) = μf * uForm σ g g := by
    have h1 := key 1 one_ne_zero
    simpa using h1
  have hφc : ∀ c : F, c ≠ 0 → φ c = c := by
    intro c hc
    have h := key c hc
    rw [hw] at h
    have h0 : μf * uForm σ g g ≠ 0 := mul_ne_zero hμf0 hgg
    have h' : φ c * (μf * uForm σ g g) = c * (μf * uForm σ g g) := by
      rw [h]
      ring
    exact mul_right_cancel₀ h0 h'
  refine RingEquiv.ext fun c => ?_
  by_cases hc : c = 0
  · subst hc
    exact map_zero φ
  · exact hφc c hc

end ModelRank

end CFSG.Timmesfeld.Transvection
