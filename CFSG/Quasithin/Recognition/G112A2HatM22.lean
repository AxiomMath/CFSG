module

public import CFSG.Quasithin.Background.SmithB45M22HatModel

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour

@[expose] def minor2 (M : Matrix (Fin 3) (Fin 3) FieldFour) : Bool :=
  (List.finRange 3).any fun a => (List.finRange 3).any fun b => (List.finRange 3).any fun c =>
    (List.finRange 3).any fun d => decide (M a c * M b d - M a d * M b c ≠ 0)

theorem minor2_ok : ((List.finRange 22).all fun i => (List.finRange 22).all fun j =>
    decide (i = j) || minor2 (hatM22F i * hatM22B j)) = true := by
  decide +kernel

abbrev mat (g : ↥hatM22Γ₀) : Matrix (Fin 6) (Fin 6) FieldFour :=
  ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)

theorem minor2_eq_false_of_cols {M : Matrix (Fin 3) (Fin 3) FieldFour} (w : Fin 3 → FieldFour)
    (c : Fin 3 → FieldFour) (h : ∀ a k, M a k = c k * w a) : minor2 M = false := by
  have h0 : ∀ a b k l : Fin 3, c k * w a * (c l * w b) - c l * w a * (c k * w b) = 0 :=
    fun _ _ _ _ => by ring
  unfold minor2
  simp [h, h0]

theorem range_smul_one_sub (c : FieldFour) (hc : c ≠ 1) :
    LinearMap.range (Matrix.toLin' (c • (1 : Matrix (Fin 6) (Fin 6) FieldFour)) - LinearMap.id) =
      ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hc' : c - 1 ≠ 0 := sub_ne_zero.mpr hc
  refine ⟨(c - 1)⁻¹ • v, ?_⟩
  have h1 : c * (c - 1)⁻¹ - (c - 1)⁻¹ = 1 := by
    field_simp
  rw [LinearMap.sub_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
    LinearMap.id_apply, smul_smul, ← sub_smul, h1, one_smul]

theorem finrank_range_sub_ne_one (g : ↥hatM22Γ₀) :
    Module.finrank FieldFour (LinearMap.range (Matrix.toLin' (mat g) - LinearMap.id)) ≠ 1 := by
  set N : (Fin 6 → FieldFour) →ₗ[FieldFour] (Fin 6 → FieldFour) :=
    Matrix.toLin' (mat g) - LinearMap.id with hN
  intro h1
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp h1
  set u : Fin 6 → FieldFour := (v : Fin 6 → FieldFour) with hu
  have hline : ∀ x, ∃ c : FieldFour, N x = c • u := by
    intro x
    obtain ⟨c, hc⟩ := hv ⟨_, LinearMap.mem_range_self _ x⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  by_cases hσ : hatM22Act g = 1
  · rcases (mem_ker_hatM22Act_iff g).1 (MonoidHom.mem_ker.2 hσ) with rfl | rfl | rfl
    · have : N = 0 := by
        rw [hN]
        apply LinearMap.ext
        intro x
        rw [LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply, LinearMap.zero_apply]
        rw [show mat 1 = 1 from rfl, Matrix.one_mulVec, sub_self]
      rw [this, LinearMap.range_zero, finrank_bot] at h1
      exact zero_ne_one h1
    · rw [hN, show mat hatM22Z = ω • 1 from hatM22Z_val, range_smul_one_sub ω (by decide),
        finrank_top, Module.finrank_fin_fun] at h1
      norm_num at h1
    · rw [hN, show mat (hatM22Z ^ 2) = ω₂ • 1 from hatM22Z_sq_val,
        range_smul_one_sub ω₂ (by decide), finrank_top, Module.finrank_fin_fun] at h1
      norm_num at h1
  · obtain ⟨i, hi⟩ : ∃ i, hatM22Act g i ≠ i := by
      by_contra hcon
      push_neg at hcon
      exact hσ (Equiv.ext hcon)
    set j := hatM22Act g i with hj
    have hmov : (hatM22U i).map (Matrix.toLin' (mat g)) = hatM22U j := moves_hatM22Act g i
    have hcol : ∀ k : Fin 3, ∃ c : FieldFour,
        (hatM22F i).mulVec (fun l => hatM22B j l k) = c • (hatM22F i).mulVec u := by
      intro k
      have hk : (fun l => hatM22B j l k) ∈ hatM22U j :=
        ⟨Pi.single k 1, by
          rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
          rfl⟩
      rw [← hmov] at hk
      obtain ⟨x, hx, hxk⟩ := hk
      obtain ⟨c, hc⟩ := hline x
      have h0 : (hatM22F i).mulVec x = 0 := hatM22U_le_ker i hx
      refine ⟨c, ?_⟩
      have : (fun l => hatM22B j l k) = x + c • u := by
        rw [← hxk, ← hc, hN, LinearMap.sub_apply, LinearMap.id_apply, add_sub_cancel]
      rw [this, Matrix.mulVec_add, h0, zero_add, Matrix.mulVec_smul]
    choose c hc using hcol
    have hfalse : minor2 (hatM22F i * hatM22B j) = false := by
      apply minor2_eq_false_of_cols ((hatM22F i).mulVec u) c
      intro a k
      have := congrFun (hc k) a
      rw [Matrix.mul_apply]
      simpa [Matrix.mulVec, dotProduct] using this
    have hok := minor2_ok
    simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      decide_eq_true_eq] at hok
    rcases hok i j with h | h
    · exact hi h.symm
    · rw [hfalse] at h
      exact Bool.false_ne_true h

end CFSG.Quasithin.G112A2
