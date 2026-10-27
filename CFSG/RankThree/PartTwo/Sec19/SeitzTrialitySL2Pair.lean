module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

variable {F : Type} [Field F] [Finite F] [CharP F 2]

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2 in
theorem sl2_pair_core (k : Subfield F) (hK : Nat.card F = Nat.card k ^ 3)
    (hk4 : 4 ∣ Nat.card k) {M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ c ∈ k, u2 c ∈ M) (h : Matrix.SpecialLinearGroup (Fin 2) F)
    (hr : (h : Matrix (Fin 2) (Fin 2) F) 1 0 ∉ k)
    (hconj : ∀ c ∈ k, h * u2 c * h⁻¹ ∈ M) : M = ⊤ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set r : F := (h : Matrix (Fin 2) (Fin 2) F) 1 0 with hrdef
  set p : F := (h : Matrix (Fin 2) (Fin 2) F) 0 0 with hpdef
  set s : F := (h : Matrix (Fin 2) (Fin 2) F) 0 1 with hsdef
  set t : F := (h : Matrix (Fin 2) (Fin 2) F) 1 1 with htdef
  have hr0 : r ≠ 0 := fun h0 => hr (h0 ▸ k.zero_mem)
  have hdet : p * t - s * r = 1 := by
    have := h.2
    rw [Matrix.det_fin_two] at this
    exact this
  set g : Matrix.SpecialLinearGroup (Fin 2) F := u2 (p / r) with hg
  set M' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    M.comap (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hh : (h : Matrix (Fin 2) (Fin 2) F) = !![p, s; r, t] := Matrix.eta_fin_two _
  have hgh : ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, r⁻¹; r, t] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, u2_coe, hh, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    · linear_combination p * h2
    · linear_combination hdet + (s * r) * h2
  have hE : ∀ c : F, l2 (c * r ^ 2) * (g * h) = (g * h) * u2 c := by
    intro c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul (l2 (c * r ^ 2)) (g * h),
      Matrix.SpecialLinearGroup.coe_mul (g * h) (u2 c), hgh, l2_coe, u2_coe,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  have hgcomm : ∀ c : F, g * u2 c = u2 c * g := fun c => by
    rw [hg, ← u2_add, ← u2_add, add_comm]
  have hM'u : ∀ c ∈ k, u2 c ∈ M' := by
    intro c hc
    show g⁻¹ * u2 c * g⁻¹⁻¹ ∈ M
    have e : g⁻¹ * u2 c * g⁻¹⁻¹ = u2 c := by
      rw [inv_inv, mul_assoc, ← hgcomm c, inv_mul_cancel_left]
    rw [e]
    exact hu c hc
  have hM'l : ∀ c ∈ k, l2 (c * r ^ 2) ∈ M' := by
    intro c hc
    show g⁻¹ * l2 (c * r ^ 2) * g⁻¹⁻¹ ∈ M
    have e : g⁻¹ * l2 (c * r ^ 2) * g⁻¹⁻¹ = h * u2 c * h⁻¹ := by
      rw [inv_inv]
      have hEc := hE c
      calc g⁻¹ * l2 (c * r ^ 2) * g = g⁻¹ * (l2 (c * r ^ 2) * (g * h)) * h⁻¹ := by group
        _ = g⁻¹ * ((g * h) * u2 c) * h⁻¹ := by rw [hEc]
        _ = h * u2 c * h⁻¹ := by group
    rw [e]
    exact hconj c hc
  have hr2 : r ^ 2 ∉ k := fun h' => hr (mem_subfield_of_sq_mem k h')
  have hM'top : M' = ⊤ :=
    sl2_eq_top_of_root_lines (d := 3) Nat.prime_three (by norm_num) hK hk4 hr2 hM'u hM'l
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : g * x * g⁻¹ ∈ M' := hM'top ▸ Subgroup.mem_top _
  have h3 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ M := hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e] at h3
  exact h3


open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2 in
theorem sl2_pair_subfield (k : Subfield F) (hK : Nat.card F = Nat.card k ^ 3)
    (hk4 : 4 ∣ Nat.card k) {M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hk : ∀ y : Matrix.SpecialLinearGroup (Fin 2) k,
      Matrix.SpecialLinearGroup.map k.subtype y ∈ M)
    (h : Matrix.SpecialLinearGroup (Fin 2) F)
    (hh : ∀ y : Matrix.SpecialLinearGroup (Fin 2) k,
      Matrix.SpecialLinearGroup.map k.subtype y ≠ h)
    (hconj : ∀ y : Matrix.SpecialLinearGroup (Fin 2) k,
      h * Matrix.SpecialLinearGroup.map k.subtype y * h⁻¹ ∈ M) : M = ⊤ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Matrix.SpecialLinearGroup.map k.subtype).range with hS
  have hSM : S ≤ M := by
    rintro _ ⟨y, rfl⟩
    exact hk y
  have hSconj : ∀ x ∈ S, h * x * h⁻¹ ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact hconj y
  have hu : ∀ c ∈ k, u2 c ∈ S := by
    intro c hc
    refine ⟨CFSG.LieType.Steinberg.sl2Upper (⟨c, hc⟩ : k), ?_⟩
    apply Subtype.ext
    rw [u2_coe]
    show k.subtype.mapMatrix (CFSG.LieType.Steinberg.sl2Upper (⟨c, hc⟩ : k) :
      Matrix (Fin 2) (Fin 2) k) = !![1, c; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Steinberg.sl2Upper]
  have hwdet : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2
  set w : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; 1, 0], hwdet⟩ with hwdef
  have hwm : (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl
  have hw : w ∈ S := by
    have hmapw : k.subtype.mapMatrix (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k) =
        !![0, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hwk : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k).det = 1 := by
      apply k.subtype.injective
      rw [RingHom.map_det, map_one, hmapw]
      exact hwdet
    refine ⟨⟨!![0, 1; 1, 0], hwk⟩, ?_⟩
    apply Subtype.ext
    exact hmapw
  have key : ∀ γ₁ ∈ S, ∀ γ₂ ∈ S,
      ((γ₁ * h * γ₂ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ∉ k →
        M = ⊤ := by
    intro γ₁ hγ₁ γ₂ hγ₂ hr
    refine sl2_pair_core k hK hk4 (fun c hc => hSM (hu c hc)) (γ₁ * h * γ₂) hr ?_
    intro c hc
    have h1 : γ₂ * u2 c * γ₂⁻¹ ∈ S := S.mul_mem (S.mul_mem hγ₂ (hu c hc)) (S.inv_mem hγ₂)
    have h3 := hSconj _ h1
    have h4 : γ₁ * (h * (γ₂ * u2 c * γ₂⁻¹) * h⁻¹) * γ₁⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (hSM hγ₁) h3) (M.inv_mem (hSM hγ₁))
    have e : γ₁ * h * γ₂ * u2 c * (γ₁ * h * γ₂)⁻¹ =
        γ₁ * (h * (γ₂ * u2 c * γ₂⁻¹) * h⁻¹) * γ₁⁻¹ := by group
    rw [e]
    exact h4
  by_contra hMtop
  have hent : ∃ i j : Fin 2, (h : Matrix (Fin 2) (Fin 2) F) i j ∉ k := by
    by_contra hall
    push Not at hall
    let N : Matrix (Fin 2) (Fin 2) k := Matrix.of fun i j => ⟨(h : Matrix (Fin 2) (Fin 2) F) i j, hall i j⟩
    have hdet : N.det = 1 := by
      apply k.subtype.injective
      rw [RingHom.map_det, map_one]
      have : k.subtype.mapMatrix N = (h : Matrix (Fin 2) (Fin 2) F) := by
        ext i j
        rfl
      rw [this]
      exact h.2
    apply hh ⟨N, hdet⟩
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    rfl
  obtain ⟨i, j, hij⟩ := hent
  have hwh : ((w * h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] * (h : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hwm]
  have hhw : ((h * w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hwm]
  have hwhw : ((w * h * w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] * (h : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hwm]
  fin_cases i <;> fin_cases j
  ·
    refine hMtop (key w hw 1 S.one_mem ?_)
    rw [mul_one, hwh]
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hij
  ·
    refine hMtop (key w hw w hw ?_)
    have e : ((w * h * w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
        (h : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      rw [hwhw, Matrix.eta_fin_two (h : Matrix (Fin 2) (Fin 2) F)]
      simp [Matrix.mul_fin_two]
    rw [e]
    exact hij
  ·
    refine hMtop (key 1 S.one_mem 1 S.one_mem ?_)
    simpa using hij
  ·
    refine hMtop (key 1 S.one_mem w hw ?_)
    rw [one_mul, hhw]
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hij

end Plain


section Model


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem A_le_of_pair (P : D4Par n X σ) (hn : 2 ≤ n) {S : Subgroup (C0 σ)}
    (hA0 : A0sub σ ≤ S) {h : C0 σ} (hh : h ∈ Asub σ) (hh0 : h ∉ A0sub σ)
    (hconj : ∀ y ∈ A0sub σ, h * y * h⁻¹ ∈ S) : Asub σ ≤ S := by
  haveI := P.charP
  rw [← iotaA_range P] at hh ⊢
  obtain ⟨h', rfl⟩ := hh
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) X) := S.comap (iotaA P) with hM
  have hA0mem : ∀ y : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
      iotaA P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y) ∈ A0sub σ := fun y =>
    (mem_A0sub_iff P).mpr ⟨y, rfl⟩
  have hMtop : M = ⊤ := by
    refine sl2_pair_subfield (fixSubfield σ) P.card_eq_cube (P.four_dvd_card_fix hn) ?_ h' ?_ ?_
    · intro y
      exact hA0 (hA0mem y)
    · intro y hy
      apply hh0
      rw [← hy]
      exact hA0mem y
    · intro y
      have := hconj _ (hA0mem y)
      show iotaA P (h' * Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y * h'⁻¹) ∈ S
      rw [map_mul, map_mul, map_inv]
      exact this
  rintro _ ⟨g, rfl⟩
  have : g ∈ M := hMtop ▸ Subgroup.mem_top g
  exact this

end Model

end CFSG.RankThree.PartTwo.Sec19
