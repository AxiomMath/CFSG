module

public import CFSG.Quasithin.Vol2.Ch6NatMod
public import CFSG.Quasithin.Background.JonesParshallOrthogonal

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

section HermIrred

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {a : ℕ}

@[expose] def twistActCh6 (a : ℕ) (g : SL2 K) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  (g : Matrix (Fin 2) (Fin 2) K) * X * (frobPow a (g : Matrix (Fin 2) (Fin 2) K))ᵀ

@[expose] def wMatCh6 : SL2 K :=
  ⟨!![0, 1; 1, 0], by
    rw [det_fin_two_of]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination -h2⟩

omit [Fintype K] in
theorem hAct_uMat_sub (t : K) {X : Matrix (Fin 2) (Fin 2) K} (hX : X ∈ hermA a K) :
    twistActCh6 a (uMat t) X - X = !![sig a t * X 0 1 + t * sig a (X 0 1) + t * sig a t * X 1 1,
      t * X 1 1; sig a t * X 1 1, 0] := by
  have h10 : X 1 0 = sig a (X 0 1) := (hermA_apply hX 1 0).symm
  rw [twistActCh6, frobPow_uMat, uMat_coe]
  ext i j
  rw [Matrix.sub_apply, triple_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, h10] <;> ring

omit [Fintype K] in
theorem frobPow_wMat_ch6 :
    frobPow a ((wMatCh6 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, wMatCh6]

omit [Fintype K] in
theorem hAct_wMat (x : K) : twistActCh6 a wMatCh6 !![x, 0; 0, 0] = !![0, 0; 0, x] := by
  rw [twistActCh6, frobPow_wMat_ch6]
  ext i j
  rw [triple_apply]
  fin_cases i <;> fin_cases j <;> simp [wMatCh6]

omit [Fintype K] in
theorem sig_inv_ch6 (x : K) : sig a x⁻¹ = (sig a x)⁻¹ := map_inv₀ (sig a) x

theorem hermA_le_of_invariant_ch6 (hK : Fintype.card K = 2 ^ (2 * a)) (ha : 0 < a)
    (S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)) (hSH : S ≤ hermA a K)
    (hinv : ∀ g : SL2 K, ∀ X ∈ S, twistActCh6 a g X ∈ S)
    {X₀ : Matrix (Fin 2) (Fin 2) K} (hX₀ : X₀ ∈ S) (hX₀0 : X₀ ≠ 0) : hermA a K ≤ S := by
  have hσ : ∀ x : K, sig a (sig a x) = x := sig_sig hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨c, hc⟩ := exists_sig_ne hK ha
  set τ := sig a c + c with hτ
  have hτ0 : τ ≠ 0 := by
    intro h0
    apply hc
    linear_combination h0 - c * h2
  have hστ : sig a τ = τ := by rw [hτ, map_add, hσ, add_comm]
  have hsub : ∀ t : K, ∀ X ∈ S, twistActCh6 a (uMat t) X - X ∈ S := fun t X hX =>
    S.sub_mem (hinv _ X hX) hX
  have step1b : ∀ X ∈ S, X 1 1 = 0 → X 0 1 ≠ 0 →
      ∃ l : K, l ≠ 0 ∧ sig a l = l ∧ !![l, 0; 0, 0] ∈ S := by
    intro X hX h11 h01
    have hXH := hSH hX
    have hσβ : sig a (X 0 1) ≠ 0 := by
      intro h0
      apply h01
      rw [← hσ (X 0 1), h0, map_zero]
    set s := c * (sig a (X 0 1))⁻¹ with hs
    have hY := hsub s X hX
    rw [hAct_uMat_sub s hXH, h11] at hY
    have e1 : sig a s * X 0 1 + s * sig a (X 0 1) + s * sig a s * 0 = τ := by
      rw [hs, map_mul, sig_inv_ch6, hσ, hτ]
      field_simp
      ring
    refine ⟨τ, hτ0, hστ, ?_⟩
    have e2 : !![sig a s * X 0 1 + s * sig a (X 0 1) + s * sig a s * 0, s * 0;
        sig a s * 0, (0 : K)] = !![τ, 0; 0, 0] := by
      rw [e1]
      simp
    rwa [e2] at hY
  have step1 : ∃ l : K, l ≠ 0 ∧ sig a l = l ∧ !![l, 0; 0, 0] ∈ S := by
    have hXH := hSH hX₀
    by_cases h11 : X₀ 1 1 = 0
    · by_cases h01 : X₀ 0 1 = 0
      · refine ⟨X₀ 0 0, ?_, hermA_apply hXH 0 0, ?_⟩
        · intro h00
          apply hX₀0
          ext i j
          fin_cases i <;> fin_cases j
          · exact h00
          · exact h01
          · change X₀ 1 0 = 0
            rw [← hermA_apply hXH 1 0, h01, map_zero]
          · exact h11
        · have e : X₀ = !![X₀ 0 0, 0; 0, 0] := by
            ext i j
            fin_cases i <;> fin_cases j
            · rfl
            · exact h01
            · change X₀ 1 0 = 0
              rw [← hermA_apply hXH 1 0, h01, map_zero]
            · exact h11
          rwa [← e]
      · exact step1b X₀ hX₀ h11 h01
    · have hY := hsub 1 X₀ hX₀
      rw [hAct_uMat_sub 1 hXH] at hY
      refine step1b _ hY ?_ ?_
      · simp
      · simpa using h11
  obtain ⟨l, hl0, hσl, hl⟩ := step1
  have hE22 : !![0, 0; 0, l] ∈ S := by
    rw [← hAct_wMat]
    exact hinv _ _ hl
  have hY1 : !![l, l; l, (0 : K)] ∈ S := by
    have hY := hsub 1 _ hE22
    have hH : !![0, 0; 0, l] ∈ hermA a K := hSH hE22
    rw [hAct_uMat_sub 1 hH] at hY
    simpa using hY
  have hdiag : ∀ μ : K, sig a μ = μ → !![μ, 0; 0, 0] ∈ S := by
    intro μ hμ
    set s := μ * l⁻¹ * τ⁻¹ * c with hs
    have hZ := hsub s _ hY1
    have hH : !![l, l; l, (0 : K)] ∈ hermA a K := hSH hY1
    rw [hAct_uMat_sub s hH] at hZ
    have e1 : sig a s * l + s * sig a l + s * sig a s * 0 = μ := by
      rw [hs, map_mul, map_mul, map_mul, sig_inv_ch6, sig_inv_ch6, hμ, hσl, hστ]
      field_simp
      rw [hτ]
      ring
    have e2 : !![sig a s * l + s * sig a l + s * sig a s * 0, s * 0; sig a s * 0, (0 : K)] =
        !![μ, 0; 0, 0] := by
      rw [e1]
      simp
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      Fin.isValue] at hZ
    rwa [e2] at hZ
  have hdiag2 : ∀ μ : K, sig a μ = μ → !![0, 0; 0, μ] ∈ S := by
    intro μ hμ
    rw [← hAct_wMat]
    exact hinv _ _ (hdiag μ hμ)
  have hoff : ∀ β : K, !![0, β; sig a β, 0] ∈ S := by
    intro β
    set t := β * l⁻¹ with ht
    have hY := hsub t _ hE22
    have hH : !![0, 0; 0, l] ∈ hermA a K := hSH hE22
    rw [hAct_uMat_sub t hH] at hY
    have hD := hdiag (t * sig a t * l) (by rw [map_mul, map_mul, hσ, hσl]; ring)
    have hd := S.sub_mem hY hD
    have e : !![sig a t * 0 + t * sig a 0 + t * sig a t * l, t * l; sig a t * l, (0 : K)] -
        !![t * sig a t * l, 0; 0, 0] = !![0, β; sig a β, 0] := by
      have e1 : t * l = β := by rw [ht]; field_simp
      have e2 : sig a t * l = sig a β := by
        rw [ht, map_mul, sig_inv_ch6, hσl]; field_simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e1, e2]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      Fin.isValue] at hd
    rwa [e] at hd
  intro X hX
  have h10 : X 1 0 = sig a (X 0 1) := (hermA_apply hX 1 0).symm
  have e : X = !![X 0 0, 0; 0, 0] + !![0, 0; 0, X 1 1] + !![0, X 0 1; sig a (X 0 1), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10]
  rw [e]
  exact S.add_mem (S.add_mem (hdiag _ (hermA_apply hX 0 0)) (hdiag2 _ (hermA_apply hX 1 1)))
    (hoff _)

end HermIrred

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem IsOrthCh5.irreducible_ch6 {L V : Subgroup G} {n : ℕ} (h : IsOrthCh5 L V n) (hn : 2 ≤ n)
    (W : Subgroup G) (hWV : W ≤ V) (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ ∨ W = V := by
  classical
  obtain ⟨m, rfl, -, hc, K, _, _, _, hcard, π, hπ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 2 ^ (2 * m) := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hm : 0 < m := by omega
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv
    (D := FFModel.twistTensor m (Assembly.LowTwoRank.StatedSL 2 K)) rfl hπ
  let ev : ↥V → Matrix (Fin 2) (Fin 2) K := fun w => Multiplicative.toAdd (E w).1
  have ev_mul : ∀ w₁ w₂, ev (w₁ * w₂) = ev w₁ + ev w₂ := fun w₁ w₂ => by
    simp only [ev, map_mul]
    rfl
  have ev_one : ev 1 = 0 := by
    simp only [ev, map_one]
    rfl
  have ev_inv : ∀ w, ev w⁻¹ = -ev w := fun w => by
    simp only [ev, map_inv]
    rfl
  have ev_inj : Function.Injective ev := fun w₁ w₂ h => E.injective (Subtype.ext h)
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let S : AddSubgroup (Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {X | ∃ w : ↥V, (w : G) ∈ W ∧ ev w = X}
      add_mem' := by
        rintro _ _ ⟨w₁, h₁, rfl⟩ ⟨w₂, h₂, rfl⟩
        exact ⟨w₁ * w₂, W.mul_mem h₁ h₂, ev_mul w₁ w₂⟩
      zero_mem' := ⟨1, W.one_mem, ev_one⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, W.inv_mem hw, ev_inv w⟩ }
  have hSH : S ≤ hermA m K := by
    rintro _ ⟨w, -, rfl⟩
    exact (E w).2
  have hinv : ∀ g : SL2 K, ∀ X ∈ S, twistActCh6 m g X ∈ S := by
    rintro g _ ⟨w, hw, rfl⟩
    obtain ⟨ℓ, hℓL, hℓ⟩ := mem_autOn_iff.mp (π (slToStated g)).2
    refine ⟨((π (slToStated g) : ↥(autOn L V)) : MulAut ↥V) w, ?_, ?_⟩
    · rw [← hℓ, conjAct_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hLW hℓL) w).mp hw
    · exact congrArg Multiplicative.toAdd (hE (slToStated g) w)
  obtain ⟨w₀, hw₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  have hX₀ : ev ⟨w₀, hWV w₀.2⟩ ∈ S := ⟨⟨w₀, hWV w₀.2⟩, w₀.2, rfl⟩
  have hX₀0 : ev ⟨w₀, hWV w₀.2⟩ ≠ 0 := by
    intro h0
    apply hw₀
    rw [← ev_one] at h0
    have h3 : (⟨w₀, hWV w₀.2⟩ : ↥V) = 1 := ev_inj h0
    have h4 : (w₀ : G) = 1 := congrArg Subtype.val h3
    exact Subtype.ext h4
  have hle := hermA_le_of_invariant_ch6 hK hm S hSH hinv hX₀ hX₀0
  refine le_antisymm hWV fun v hv => ?_
  obtain ⟨w, hw, hwv⟩ := hle (E ⟨v, hv⟩).2
  have h2 : w = ⟨v, hv⟩ := ev_inj hwv
  rw [← show (w : G) = v from congrArg Subtype.val h2]
  exact hw

end CFSG.Quasithin.H13
