module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainMat
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatWt

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def OrbV (Xg : Subgroup (GL (Fin 8) (ZMod 3))) (u v : Fin 8 → ZMod 3) : Prop :=
  ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u = v

theorem eq_one_of_mulVec_single {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (h : ∀ j : Fin 8, M *ᵥ Pi.single j 1 = Pi.single j 1) : M = 1 := by
  ext i j
  have e := congrFun (h j) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at e
  rw [e, Matrix.one_apply, Pi.single_apply]

section Orbit

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))}

theorem orbV_mulVec {u v : Fin 8 → ZMod 3} (hv : OrbV Xg u v) {B : GL (Fin 8) (ZMod 3)}
    (hB : B ∈ Xg) : OrbV Xg u ((B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) := by
  obtain ⟨A, hA, rfl⟩ := hv
  exact ⟨B * A, Xg.mul_mem hB hA, by rw [Units.val_mul, ← Matrix.mulVec_mulVec]⟩

theorem orbV_mulVec_iff {u v : Fin 8 → ZMod 3} {B : GL (Fin 8) (ZMod 3)} (hB : B ∈ Xg) :
    OrbV Xg u ((B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) ↔ OrbV Xg u v := by
  refine ⟨fun hv => ?_, fun hv => orbV_mulVec hv hB⟩
  have := orbV_mulVec hv (Xg.inv_mem hB)
  rwa [inv_mulVec_mulVec] at this

end Orbit

namespace N7MatHyp

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))} (h : N7MatHyp Xg)
include h

theorem orbV_iff_repW {u v : Fin 8 → ZMod 3} (hv : wt v ≤ 7) :
    OrbV Xg u v ↔ OrbV Xg u (repW (wt v)) := by
  obtain ⟨σ, s, hs, hp, he⟩ := exists_spMat_mulVec_eq_repW v hv
  obtain ⟨P, hP, hPe⟩ := h.mem_fk hs hp
  rw [← he, ← hPe, orbV_mulVec_iff hP]

theorem orbV_iff_rep8 {u v : Fin 8 → ZMod 3} (hv : wt v = 8) :
    OrbV Xg u v ↔ OrbV Xg u (rep8 (∏ i, v i)) := by
  obtain ⟨σ, s, hs, hp, he⟩ := exists_spMat_mulVec_eq_rep8 v hv
  obtain ⟨P, hP, hPe⟩ := h.mem_fk hs hp
  rw [← he, ← hPe, orbV_mulVec_iff hP]

theorem wt_root_of_reflection (hO : ∀ v, OrbE0 Xg v ↔ (wt v = 1 ∨ wt v = 4 ∨ wt v = 7))
    {ρ : GL (Fin 8) (ZMod 3)} (hρ : ρ ∈ Xg) {u : Fin 8 → ZMod 3} (hu : u ≠ 0)
    (hρu : (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u = -u)
    (hρl : ∀ z, ∃ c : ZMod 3, (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z = c • u) :
    wt u = 2 ∨ wt u = 8 := by
  have hu147 : ¬ (wt u = 1 ∨ wt u = 4 ∨ wt u = 7) := fun hw =>
    h.false_of_reflection ((hO u).mpr hw) hρ hρu hρl
  have hpres : ∀ z, (wt z = 1 ∨ wt z = 4 ∨ wt z = 7) →
      (wt ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = 1 ∨
        wt ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = 4 ∨
        wt ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = 7) :=
    fun z hz => (hO _).mp (orbE0_mulVec ((hO z).mpr hz) hρ)
  obtain ⟨m, hm⟩ : ∃ m, u m ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext hc)
  obtain ⟨w, hw⟩ : ∃ w : Fin 8 → ZMod 3, ∀ z,
      (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z = z + (∑ j, w j * z j) • u := by
    refine ⟨fun j => u m * ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) m j, fun z => ?_⟩
    obtain ⟨c, hc⟩ := hρl z
    have e2 : ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z) m =
        ∑ j, ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) m j * z j := by
      rw [show (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z =
        ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) *ᵥ z by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
      rfl
    have hcm : ∑ j, u m * ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) m j * z j = c := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← e2, hc, Pi.smul_apply, smul_eq_mul, mul_comm c, ← mul_assoc,
        mul_self_of_ne_zero hm, one_mul]
    rw [hcm, ← hc, add_sub_cancel]
  have hwu : ∑ j, w j * u j = 1 := by
    have em := congrFun (hw u) m
    rw [hρu] at em
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at em
    exact zmod3_refl_coeff hm em
  obtain ⟨k, hwk, huk⟩ : ∃ k, w k ≠ 0 ∧ u k ≠ 0 := by
    by_contra hc
    push Not at hc
    have : ∑ j, w j * u j = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases hj : w j = 0
      · rw [hj, zero_mul]
      · rw [hc j hj, mul_zero]
    rw [hwu] at this
    exact one_ne_zero this
  have hek := hpres (Pi.single k 1) (Or.inl (wt_single k))
  rw [hw, sum_mul_single, wt_single_add_smul huk hwk] at hek
  have hle : wt u ≤ 8 := by
    unfold wt
    exact (Finset.card_le_univ _).trans (by simp)
  have hw258 : wt u = 2 ∨ wt u = 5 ∨ wt u = 8 := by
    split_ifs at hek <;> omega
  rcases hw258 with h2 | h5 | h8
  · exact Or.inl h2
  ·
    exfalso
    obtain ⟨j, hj⟩ : ∃ j, u j = 0 := by
      by_contra hc
      push Not at hc
      have := (wt_eq_iff_forall_ne_zero u).mpr hc
      omega
    have hwj : w j = 0 := by
      by_contra hwj
      have hρe := hpres (Pi.single j 1) (Or.inl (wt_single j))
      rw [hw, sum_mul_single] at hρe
      have : wt (Pi.single j 1 + w j • u) = 6 := by
        unfold wt
        have hS : (Finset.univ.filter fun i : Fin 8 =>
            (Pi.single j 1 + w j • u : Fin 8 → ZMod 3) i ≠ 0) =
            insert j (Finset.univ.filter fun i : Fin 8 => u i ≠ 0) := by
          ext i
          by_cases hi : i = j
          · subst hi
            simp [hj]
          · simp [hi, Pi.single_eq_of_ne hi, hwj]
        rw [hS, Finset.card_insert_of_notMem (by simp [hj])]
        exact congrArg (· + 1) h5
      omega
    have hρj : (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single j 1 = Pi.single j 1 := by
      rw [hw, sum_mul_single, hwj, zero_smul, add_zero]
    obtain ⟨P, hP, hPe⟩ := h.perm (Equiv.swap 0 j)
    have hPP : P⁻¹ = P := by
      apply inv_eq_of_mul_eq_one_right
      apply Units.ext
      rw [Units.val_mul, hPe, spMat_mul, Equiv.swap_mul_self, Units.val_one]
      exact (congrArg _ (funext fun _ => by simp)).trans spMat_one
    have hPe0 : (P : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single j 1 := by
      rw [hPe, spMat_mulVec]
      funext i
      by_cases hi : i = j
      · subst hi
        simp
      · have : Equiv.swap 0 j i ≠ 0 := by
          rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
          exact hi
        simp [Equiv.symm_swap, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne this]
    obtain ⟨σ, s, hs, -, -, -, hρ'⟩ := h.conj_spMat (A₀ := P) hP hρ (c := 1)
      (by rw [hPe0, hρj, one_smul])
    have hPu : wt (((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u) = 5 := by
      rw [hPP, hPe, wt_spMat_mulVec (s := 1) (fun _ => Or.inl rfl), h5]
    have hfix : ∀ i : Fin 8, spMat σ s *ᵥ Pi.single i 1 = Pi.single i 1 := by
      intro i
      obtain ⟨c, hc⟩ := hρl ((P : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single i 1)
      have e : spMat σ s *ᵥ Pi.single i 1 - Pi.single i 1 =
          c • (((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u) := by
        rw [← hρ', conj_mulVec]
        have := congrArg (fun z =>
          ((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) hc
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, inv_mulVec_mulVec] at this
        exact this
      by_contra hne
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul, sub_eq_zero] at e
        exact hne e
      have h2 : wt (spMat σ s *ᵥ Pi.single i 1 - Pi.single i 1) ≤ 2 := by
        rw [sub_eq_add_neg]
        refine (wt_add_le _ _).trans ?_
        rw [wt_neg, wt_spMat_mulVec hs, wt_single]
      rw [e, wt_smul hc0, hPu] at h2
      omega
    have hone : spMat σ s = 1 := eq_one_of_mulVec_single hfix
    have hneg :
        spMat σ s *ᵥ (((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u) =
        -(((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u) := by
      rw [← hρ', conj_mulVec, mulVec_inv_mulVec, hρu, Matrix.mulVec_neg]
    rw [hone, Matrix.one_mulVec] at hneg
    have hz : ((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u = 0 := by
      funext i
      have := congrFun hneg i
      simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
      revert this
      generalize (((P⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u) i = a
      revert a
      decide
    rw [hz] at hPu
    exact absurd hPu (by decide)
  · exact Or.inr h8

end N7MatHyp

theorem sign_eq_neg_of_ne {a b : ZMod 3} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hne : a ≠ b) : a = -b := by
  revert a b
  decide

theorem card_wt_28 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 2 ∨ wt v = 8).card = 368 := by
  decide +kernel

theorem orbit_root_seven (Xg : Subgroup (GL (Fin 8) (ZMod 3))) (h : N7MatHyp Xg)
    (hcard : 2 ^ 8 * Nat.factorial 8 < Nat.card Xg) :
    ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v : Fin 8 → ZMod 3,
      OrbV Xg (repW 2) v ↔ (wt v = 2 ∨ (wt v = 8 ∧ ∏ i, v i = ε)) := by
  classical
  obtain ⟨hX, hO⟩ := orbit_evenAll0_seven Xg h hcard
  obtain ⟨rp, hrp, hrpe⟩ := h.mem_fk (σ := Equiv.swap 0 1)
    (s := fun j => if j = 0 ∨ j = 1 then (-1 : ZMod 3) else 1) (by unfold IsSign; decide)
    (by decide)
  have hrpv : (rp : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ repW 2 = -repW 2 := by
    rw [hrpe, spMat_mulVec]
    decide
  have hrpl : ∀ z, ∃ c : ZMod 3, (rp : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z = c • repW 2 :=
    fun z => ⟨-(z 0 + z 1), by
      rw [hrpe, spMat_mulVec]
      funext i
      fin_cases i <;> simp [repW, Equiv.swap_apply_def] <;> ring⟩
  have h2 : OrbV Xg (repW 2) (repW 2) := ⟨1, Xg.one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩
  have hw28 : ∀ v, OrbV Xg (repW 2) v → wt v = 2 ∨ wt v = 8 := by
    rintro v ⟨A, hA, rfl⟩
    refine h.wt_root_of_reflection hO (ρ := A * rp * A⁻¹)
      (Xg.mul_mem (Xg.mul_mem hA hrp) (Xg.inv_mem hA)) ?_ ?_ ?_
    · intro h0
      have : repW 2 = 0 := by rw [← inv_mulVec_mulVec A (repW 2), h0, Matrix.mulVec_zero]
      exact absurd (congrFun this 0) (by decide)
    · rw [conj'_mulVec, inv_mulVec_mulVec, hrpv, Matrix.mulVec_neg]
    · intro z
      obtain ⟨c, hc⟩ := hrpl (((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z)
      refine ⟨c, ?_⟩
      rw [conj'_mulVec]
      calc (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((rp : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            (((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z)) - z =
          (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((rp : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            (((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) -
            ((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) := by
            rw [Matrix.mulVec_sub, mulVec_inv_mulVec]
        _ = c • ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ repW 2) := by
            rw [hc, Matrix.mulVec_smul]
  obtain ⟨A₀, hA₀, hA₀e⟩ := (hO (repW 7)).mpr (Or.inr (Or.inr (by decide)))
  obtain ⟨D, hD, hDe⟩ := h.mem_fk (σ := 1)
    (s := fun j => if j = 1 ∨ j = 2 then (-1 : ZMod 3) else 1) (by unfold IsSign; decide)
    (by decide)
  have hDu : (D : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ repW 2 = Pi.single 0 1 - Pi.single 1 1 := by
    rw [hDe, spMat_mulVec]
    decide
  have hp : OrbV Xg (repW 2) ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ repW 2) := ⟨A₀, hA₀, rfl⟩
  have hm : OrbV Xg (repW 2)
      ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 - Pi.single 1 1)) :=
    ⟨A₀ * D, Xg.mul_mem hA₀ hD, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, hDu]⟩
  have hsum : (A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ repW 2 +
      (A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 - Pi.single 1 1) =
      (2 : ZMod 3) • repW 7 := by
    rw [← Matrix.mulVec_add, show (repW 2 + (Pi.single 0 1 - Pi.single 1 1) : Fin 8 → ZMod 3) =
      (2 : ZMod 3) • Pi.single 0 1 by decide, Matrix.mulVec_smul, hA₀e]
  obtain ⟨v₈, hv₈, hwt₈⟩ : ∃ v₈, OrbV Xg (repW 2) v₈ ∧ wt v₈ = 8 := by
    rcases hw28 _ hp with h2' | h8
    · rcases hw28 _ hm with h2'' | h8'
      · exfalso
        have hle := wt_add_le ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ repW 2)
          ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 - Pi.single 1 1))
        rw [hsum, wt_smul (c := (2 : ZMod 3)) (by decide), h2', h2''] at hle
        have : wt (repW 7) = 7 := by decide
        omega
      · exact ⟨_, hm, h8'⟩
    · exact ⟨_, hp, h8⟩
  have hsgn : ∀ v : Fin 8 → ZMod 3, wt v = 8 → (∏ i, v i = 1 ∨ ∏ i, v i = -1) := fun v hv =>
    eq_one_or_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i _ => (wt_eq_iff_forall_ne_zero v).mp hv i)
  have hε := hsgn v₈ hwt₈
  have hrep8 : OrbV Xg (repW 2) (rep8 (∏ i, v₈ i)) := (h.orbV_iff_rep8 hwt₈).mp hv₈
  have hnot : ¬ OrbV Xg (repW 2) (rep8 (-∏ i, v₈ i)) := by
    intro hneg
    have hall : ∀ v, OrbV Xg (repW 2) v ↔ (wt v = 2 ∨ wt v = 8) := by
      intro v
      refine ⟨hw28 v, fun hv => ?_⟩
      rcases hv with hv2 | hv8
      · rw [h.orbV_iff_repW (v := v) (by omega), hv2]
        exact h2
      · rw [h.orbV_iff_rep8 hv8]
        by_cases hpe : ∏ i, v i = ∏ i, v₈ i
        · rw [hpe]
          exact hrep8
        · rw [sign_eq_neg_of_ne (hsgn v hv8) hε hpe]
          exact hneg
    have hdvd : {v : Fin 8 → ZMod 3 | OrbV Xg (repW 2) v}.ncard ∣ Nat.card Xg := by
      have h1 := MulAction.index_stabilizer ↥Xg (repW 2)
      have h2' : MulAction.orbit ↥Xg (repW 2) = {v | OrbV Xg (repW 2) v} := by
        ext v
        simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, OrbV, Subgroup.smul_def,
          Units.smul_def, Matrix.smul_eq_mulVec]
        constructor
        · rintro ⟨⟨A, hA⟩, rfl⟩
          exact ⟨A, hA, rfl⟩
        · rintro ⟨A, hA, rfl⟩
          exact ⟨⟨A, hA⟩, rfl⟩
      rw [← h2', ← h1]
      exact Subgroup.index_dvd_card _
    have hset : {v : Fin 8 → ZMod 3 | OrbV Xg (repW 2) v} = {v | wt v = 2 ∨ wt v = 8} :=
      Set.ext hall
    rw [hset, ncard_of_card card_wt_28, hX] at hdvd
    exact absurd hdvd (by decide)
  refine ⟨∏ i, v₈ i, hε, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rcases hw28 v hv with hv2 | hv8
    · exact Or.inl hv2
    · refine Or.inr ⟨hv8, ?_⟩
      by_contra hpe
      rw [h.orbV_iff_rep8 hv8, sign_eq_neg_of_ne (hsgn v hv8) hε hpe] at hv
      exact hnot hv
  · rcases hv with hv2 | ⟨hv8, hpe⟩
    · rw [h.orbV_iff_repW (v := v) (by omega), hv2]
      exact h2
    · rw [h.orbV_iff_rep8 hv8, hpe]
      exact hrep8

end CFSG.StandardType.FrameRoute.FS81

end
