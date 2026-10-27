module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem exists_nonzero_fixed {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (S : Subgroup (GL (Fin n) K)) (hS2 : IsPGroup 2 S) (X : Submodule K (Fin n → K))
    (hX : X ≠ ⊥)
    (hXS : ∀ s ∈ S, ∀ x ∈ X, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x ∈ X) :
    ∃ x ∈ X, x ≠ 0 ∧ ∀ s ∈ S, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x = x := by
  classical
  let _ : MulAction S X :=
    { smul := fun s x => ⟨((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x,
        hXS s s.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((((1 : S) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).mulVec x = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        show ((((s * t : S) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).mulVec x =
          ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
            (((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x)
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card X := by
    have hfin : Module.finrank K X ≠ 0 := by
      have : Nontrivial X := (Submodule.nontrivial_iff_ne_bot).2 hX
      exact (Module.finrank_pos_iff.mpr inferInstance).ne'
    have := Fintype.ofFinite K
    have := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := X)]
    have h2 : 2 ∣ Fintype.card K := by
      obtain ⟨m, hm, hmK⟩ := FiniteField.card K 2
      rw [hmK]
      exact dvd_pow_self 2 m.ne_zero
    exact h2.trans (dvd_pow_self _ hfin)
  obtain ⟨b, hb, hne⟩ := hS2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := X) hdvd
    (a := 0) (by
      intro s
      apply Subtype.ext
      show ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec 0 = 0
      simp)
  refine ⟨b, b.2, fun h0 => hne ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    exact h0.symm
  · have := hb ⟨s, hs⟩
    exact congrArg Subtype.val this

theorem eq_bot_of_two_group_separated {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ}
    (S : Subgroup (GL (Fin n) K)) (hSU : S ≤ unitarySU 2 f K n) (hS2 : IsPGroup 2 S)
    (P : Subgroup (GL (Fin n) K)) (hPd : ∀ g ∈ P, ∃ d : Fin n → Kˣ, diagU d = g)
    (hPS : ∀ g ∈ P, ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ g ∈ P, ent g i i ≠ ent g j j) : S = ⊥ := by
  classical
  have := h.finite
  have := h.charP
  let W : Submodule K (Fin n → K) :=
    { carrier := {v | ∀ s ∈ S, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = v}
      add_mem' := fun {a b} ha hb s hs => by rw [Matrix.mulVec_add, ha s hs, hb s hs]
      zero_mem' := fun s _ => by simp
      smul_mem' := fun c v hv s hs => by rw [Matrix.mulVec_smul, hv s hs] }
  have hWmem : ∀ v, v ∈ W ↔ ∀ s ∈ S, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = v :=
    fun v => Iff.rfl
  have hWP : ∀ g ∈ P, ∀ v ∈ W,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v ∈ W := by
    intro g hg v hv s hs
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S := hPS g⁻¹ (P.inv_mem hg) s hs
    have h1 : (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).mulVec v = v := by
      have := hv _ hs'
      simpa [Units.val_mul, inv_inv] using this
    have e : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v)
        = (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).mulVec v := by
          rw [Matrix.mulVec_mulVec]
      _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).mulVec v := by
          rw [e, Matrix.one_mul]
      _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
            ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).mulVec v) := by
          rw [Matrix.mulVec_mulVec]
          simp only [Matrix.mul_assoc]
      _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v := by rw [h1]
  have hcoord : ∀ v ∈ W, ∀ i, (Pi.single i (v i) : Fin n → K) ∈ W := by
    suffices hk : ∀ m : ℕ, ∀ v ∈ W, (Finset.univ.filter fun i => v i ≠ 0).card ≤ m →
        ∀ i, (Pi.single i (v i) : Fin n → K) ∈ W from fun v hv i => hk _ v hv le_rfl i
    intro m
    induction m with
    | zero =>
      intro v hv hcard i
      have hv0 : v = 0 := by
        funext k
        by_contra hk
        have hk' : v k ≠ 0 := fun h0 => hk (by simp [h0])
        have hmem : k ∈ Finset.univ.filter fun i => v i ≠ 0 := by simp [hk']
        have := Finset.card_pos.mpr ⟨k, hmem⟩
        omega
      subst hv0
      simp
    | succ m ih =>
      intro v hv hcard i
      by_cases hvi : v i = 0
      · rw [hvi]
        simp
      · by_cases hall : ∀ j, j ≠ i → v j = 0
        · have : v = Pi.single i (v i) := by
            funext k
            by_cases hk : k = i
            · subst hk
              simp
            · simp [Pi.single_eq_of_ne hk, hall k hk]
          rw [← this]
          exact hv
        · push Not at hall
          obtain ⟨j, hji, hvj⟩ := hall
          obtain ⟨g, hgP, hne⟩ := hsep i j hji.symm
          obtain ⟨d, hd⟩ := hPd g hgP
          subst hd
          have hdiag : ∀ w : Fin n → K, ∀ k,
              (((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec w) k = d k * w k := by
            intro w k
            simp [diagU_val, Matrix.mulVec_diagonal]
          set v' : Fin n → K := (((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v) -
            (d j : K) • v with hv'
          have hv'W : v' ∈ W := W.sub_mem (hWP _ hgP v hv) (W.smul_mem _ hv)
          have hv'k : ∀ k, v' k = ((d k : K) - d j) * v k := by
            intro k
            simp only [hv', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hdiag]
            ring
          have hcard' : (Finset.univ.filter fun k => v' k ≠ 0).card ≤ m := by
            have hsub : (Finset.univ.filter fun k => v' k ≠ 0) ⊆
                (Finset.univ.filter fun k => v k ≠ 0).erase j := by
              intro k hk
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hk ⊢
              refine ⟨?_, ?_⟩
              · rintro rfl
                apply hk
                rw [hv'k]
                ring
              · intro hvk
                apply hk
                rw [hv'k, hvk, mul_zero]
            have hjmem : j ∈ Finset.univ.filter fun k => v k ≠ 0 := by simp [hvj]
            calc _ ≤ ((Finset.univ.filter fun k => v k ≠ 0).erase j).card :=
                  Finset.card_le_card hsub
              _ = (Finset.univ.filter fun k => v k ≠ 0).card - 1 :=
                  Finset.card_erase_of_mem hjmem
              _ ≤ m := by omega
          have hcoef : ((d i : K) - d j) ≠ 0 := by
            intro h0
            apply hne
            show ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
              ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j
            simp only [diagU_val, Matrix.diagonal_apply_eq]
            exact sub_eq_zero.1 h0
          have h1 := ih v' hv'W hcard' i
          have h2 : (Pi.single i (v i) : Fin n → K) =
              ((d i : K) - d j)⁻¹ • (Pi.single i (v' i) : Fin n → K) := by
            funext k
            by_cases hk : k = i
            · subst hk
              rw [hv'k]
              simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
              field_simp
            · simp [Pi.single_eq_of_ne hk]
          rw [h2]
          exact W.smul_mem _ h1
  have hWsupp : ∀ v ∈ W, ∀ i, v i ≠ 0 → (Pi.single i 1 : Fin n → K) ∈ W := by
    intro v hv i hvi
    have e : (v i)⁻¹ • (Pi.single i (v i) : Fin n → K) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp [inv_mul_cancel₀ hvi]
      · simp [Pi.single_eq_of_ne hk]
    rw [← e]
    exact W.smul_mem _ (hcoord v hv i)
  by_cases hI : ∀ i : Fin n, (Pi.single i 1 : Fin n → K) ∈ W
  ·
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    apply Units.ext
    ext i j
    have h1 := congrFun (hI j s hs) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply, Pi.single_apply,
      eq_comm] using h1
  · exfalso
    push Not at hI
    obtain ⟨j, hj⟩ := hI
    have hrow : ∀ s ∈ S, ∀ i, (Pi.single i 1 : Fin n → K) ∈ W → ∀ k,
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k = if i = k then 1 else 0 := by
      intro s hs i hi k
      have hinv := hi (s⁻¹) (S.inv_mem hs)
      have hcol := congrFun hinv k
      have hu := ((mem_unitarySU_iff h).1 (hSU hs)).2
      have hmul : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((s⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hleft := left_inv_eq_right_inv hu hmul
      have hk : h.bar (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k) =
          if k = i then 1 else 0 := by
        have h1 : (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ k i =
            (((s⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) k i := by rw [hleft]
        simp only [Matrix.transpose_apply, Matrix.map_apply] at h1
        rw [h1]
        simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using hcol
      have := congrArg h.bar hk
      rw [h.bar_bar] at this
      rw [this]
      by_cases hik : i = k
      · subst hik
        simp
      · have : ¬ k = i := fun h' => hik h'.symm
        simp [hik, this]
    let Y : Submodule K (Fin n → K) :=
      { carrier := {y | ∀ i, (Pi.single i 1 : Fin n → K) ∈ W → y i = 0}
        add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
        zero_mem' := fun i hi => rfl
        smul_mem' := fun c y hy i hi => by simp [hy i hi] }
    have hYne : Y ≠ ⊥ := by
      intro hbot
      have hmem : (Pi.single j 1 : Fin n → K) ∈ Y := by
        intro i hi
        have hij : i ≠ j := fun hij => hj (hij ▸ hi)
        simp [Pi.single_eq_of_ne hij]
      rw [hbot] at hmem
      have := congrFun (Submodule.mem_bot K |>.1 hmem) j
      simp at this
    have hYS : ∀ s ∈ S, ∀ y ∈ Y,
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec y ∈ Y := by
      intro s hs y hy i hi
      have : (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec y) i = y i := by
        simp only [Matrix.mulVec, dotProduct, hrow s hs i hi]
        simp
      rw [this]
      exact hy i hi
    obtain ⟨y, hyY, hy0, hyfix⟩ := exists_nonzero_fixed S hS2 Y hYne hYS
    have hyW : y ∈ W := fun s hs => hyfix s hs
    apply hy0
    funext i
    by_cases hi : (Pi.single i 1 : Fin n → K) ∈ W
    · exact hyY i hi
    · by_contra hyi
      exact hi (hWsupp y hyW i hyi)

end CFSG.RankThree.PartOne.KFU
