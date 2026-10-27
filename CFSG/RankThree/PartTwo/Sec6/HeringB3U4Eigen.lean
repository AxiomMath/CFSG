module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open Matrix

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem finrank_range_toLin'_le_map (τ : K →+* K) (hτ : Function.Surjective τ)
    (M : Matrix n n K) :
    Module.finrank K (LinearMap.range (Matrix.toLin' M)) ≤
      Module.finrank K (LinearMap.range (Matrix.toLin' (M.map τ))) := by
  set E := LinearMap.range (Matrix.toLin' M) with hE
  set E' := LinearMap.range (Matrix.toLin' (M.map τ)) with hE'
  have hmem : ∀ v ∈ E, (fun i => τ (v i)) ∈ E' := by
    rintro _ ⟨w, rfl⟩
    refine ⟨fun i => τ (w i), ?_⟩
    funext i
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (RingHom.map_mulVec τ M w i).symm
  let j : E →+ E' :=
    { toFun := fun v => ⟨fun i => τ ((v : n → K) i), hmem v v.2⟩
      map_zero' := by
        apply Subtype.ext
        funext i
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        funext i
        simp }
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hab) i
    exact τ.injective this
  have hle := rank_le_of_surjective_injective τ j hτ hj (fun r m => by
    apply Subtype.ext
    funext i
    simp [j])
  exact Module.finrank_le_finrank_of_rank_le_rank (by simpa using hle) (Module.rank_lt_aleph0 _ _)

theorem finrank_range_toLin'_map_eq (τ : K ≃+* K) (M : Matrix n n K) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (M.map τ))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' M)) := by
  refine le_antisymm ?_ (finrank_range_toLin'_le_map τ.toRingHom τ.surjective M)
  have h := finrank_range_toLin'_le_map τ.symm.toRingHom τ.symm.surjective (M.map τ)
  have hM : (M.map τ).map τ.symm.toRingHom = M := by
    ext i j
    simp
  rw [hM] at h
  exact h

theorem finrank_range_toLin'_transpose (M : Matrix n n K) :
    Module.finrank K (LinearMap.range (Matrix.toLin' Mᵀ)) =
      Module.finrank K (LinearMap.range (Matrix.toLin' M)) := by
  exact Matrix.rank_transpose M

theorem eigenProj_map_transpose (τ : K →+* K) {ω : K} (hτω : τ ω = ω) {b : Matrix n n K}
    (hbt : (b.map τ)ᵀ = b ^ 2) (hb3 : b ^ 3 = 1) (hω : ω ^ 2 + ω + 1 = 0) :
    ((eigenProj b ω).map τ)ᵀ = eigenProj b (ω ^ 2) := by
  have hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination (ω ^ 2 - ω) * hω
  have hb4 : (b ^ 2) ^ 2 = b := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hb3, one_mul]
  have h2 : (b ^ 2).map τ = (b.map τ) ^ 2 := by
    rw [show (b ^ 2).map τ = τ.mapMatrix (b ^ 2) from rfl, map_pow]
    rfl
  have h1 : (eigenProj b ω).map τ = 1 + ω • b.map τ + ω ^ 2 • (b.map τ) ^ 2 := by
    ext i j
    have hb2 := congrFun (congrFun h2 i) j
    simp only [eigenProj, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, map_pow, hτω] at hb2 ⊢
    by_cases hij : i = j
    · subst hij
      simp [hb2]
    · simp [hij, hb2]
  calc ((eigenProj b ω).map τ)ᵀ
      = (1 + ω • b.map τ + ω ^ 2 • (b.map τ) ^ 2)ᵀ := by rw [h1]
    _ = 1 + ω • (b.map τ)ᵀ + ω ^ 2 • ((b.map τ)ᵀ) ^ 2 := by
        simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_pow]
    _ = 1 + ω • b ^ 2 + ω ^ 2 • (b ^ 2) ^ 2 := by rw [hbt]
    _ = eigenProj b (ω ^ 2) := by
        rw [hb4, eigenProj, hω4]
        abel

theorem finrank_eigenProj_le_two_of_swap (hn : Fintype.card n ≤ 4) (h3K : (3 : K) ≠ 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {g : Matrix n n K} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hEω : Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g ω))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g (ω ^ 2))))) :
    ∀ c : K, c ^ 3 = 1 →
      Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g c))) ≤ 2 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    apply h3K
    linear_combination hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  set E : K → Submodule K (n → K) := fun c => LinearMap.range (Matrix.toLin' (eigenProj g c))
    with hE
  have hEω' : Module.finrank K (E ω) = Module.finrank K (E (ω ^ 2)) := hEω
  have hdisj : E ω ⊓ E (ω ^ 2) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have h1 := mulVec_eq_of_mem_range_eigenProj hg3 hω3 hv.1
    have h2 := mulVec_eq_of_mem_range_eigenProj hg3 hω23 hv.2
    have hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination (ω ^ 2 - ω) * hω
    rw [hω4, h1] at h2
    have h3 : (ω ^ 2 - ω) • v = 0 := by rw [sub_smul, h2, sub_self]
    have hne : ω ^ 2 - ω ≠ 0 := by
      intro h0
      have : ω * (ω - 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h | h
      · exact hω0 h
      · exact hω1 (sub_eq_zero.mp h)
    exact (smul_eq_zero.mp h3).resolve_left hne
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (E ω) (E (ω ^ 2))
  rw [hdisj, finrank_bot] at hsup
  have hsupn : Module.finrank K ↥(E ω ⊔ E (ω ^ 2)) ≤ Fintype.card n := by
    have := Submodule.finrank_le (E ω ⊔ E (ω ^ 2))
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hker : E ω ⊔ E (ω ^ 2) ≤ LinearMap.ker (Matrix.toLin' (eigenProj g 1)) := by
    have hk : ∀ c : K, c ^ 3 = 1 → c ^ 2 + c + 1 = 0 → E c ≤
        LinearMap.ker (Matrix.toLin' (eigenProj g 1)) := by
      intro c hc hc0 v hv
      have h1 := mulVec_eq_of_mem_range_eigenProj hg3 hc hv
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      have h2 : g ^ 2 *ᵥ v = (c ^ 2) ^ 2 • v := by
        rw [sq g, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h1, smul_smul, ← sq]
      have hc4 : (c ^ 2) ^ 2 = c := by
        calc (c ^ 2) ^ 2 = c ^ 3 * c := by ring
          _ = c := by rw [hc, one_mul]
      simp only [eigenProj, one_smul, one_pow, Matrix.add_mulVec, Matrix.one_mulVec, h1, h2, hc4]
      rw [← one_smul K v, smul_smul, smul_smul, ← add_smul, ← add_smul, mul_one, mul_one]
      rw [show (1 : K) + c ^ 2 + c = c ^ 2 + c + 1 by ring, hc0, zero_smul]
    exact sup_le (hk ω hω3 hω) (hk (ω ^ 2) hω23 (by linear_combination (ω ^ 2 - ω + 1) * hω))
  have hkerle := Submodule.finrank_mono hker
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (eigenProj g 1))
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  change Module.finrank K (E 1) + _ = _ at hrank
  have hpos : 1 ≤ Module.finrank K (E ω) := by
    by_contra h0
    push Not at h0
    have h0' : Module.finrank K (E (ω ^ 2)) = 0 := by omega
    have hz : ∀ c : K, Module.finrank K (E c) = 0 → eigenProj g c = 0 := by
      intro c hc
      rw [Submodule.finrank_eq_zero, hE, LinearMap.range_eq_bot] at hc
      exact Matrix.toLin'.injective (by rw [hc, map_zero])
    have hP1 : eigenProj g 1 = (3 : K) • 1 := by
      have h := eigenProj_add_add hω g
      rwa [hz ω (by omega), hz (ω ^ 2) h0', add_zero, add_zero] at h
    have h1 := mul_eigenProj hg3 (c := 1) (one_pow 3)
    rw [one_pow, one_smul, hP1, Matrix.mul_smul, mul_one] at h1
    apply hg1
    have := congrArg (fun M : Matrix n n K => (3 : K)⁻¹ • M) h1
    simpa only [smul_smul, inv_mul_cancel₀ h3K, one_smul] using this
  have hdim : ∀ c : K, c ^ 3 = 1 → Module.finrank K (E c) ≤ 2 := by
    intro c hc
    have hfac : (c - 1) * ((c - ω) * (c - ω ^ 2)) = 0 := by
      linear_combination (c - c ^ 2) * hω + (c - 1) * hω3 + hc
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h]
      omega
    · rcases mul_eq_zero.mp h with h' | h'
      · rw [sub_eq_zero.mp h']
        omega
      · rw [sub_eq_zero.mp h']
        omega
  exact hdim

theorem eq_bot_of_commute_of_unitary [Finite K]
    (hn : Fintype.card n ≤ 4) (τ : K →+* K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hτω : τ ω = ω)
    (h3K : (3 : K) ≠ 0) {b : GL n K} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hbu : ((b : Matrix n n K).map τ)ᵀ * (b : Matrix n n K) = 1)
    (Y : Subgroup (GL n K)) (hYb : ∀ y ∈ Y, y * b = b * y) (hYp : Group.IsPerfect Y)
    (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  set bm : Matrix n n K := (b : Matrix n n K) with hbm
  have hb3m : bm ^ 3 = 1 := by
    rw [hbm, ← Units.val_pow_eq_pow_val, hb3, Units.val_one]
  have hbt : (bm.map τ)ᵀ = bm ^ 2 := by
    calc (bm.map τ)ᵀ = (bm.map τ)ᵀ * (bm * bm ^ 2) := by
          rw [← pow_succ', hb3m, mul_one]
      _ = ((bm.map τ)ᵀ * bm) * bm ^ 2 := by rw [mul_assoc]
      _ = bm ^ 2 := by rw [hbu, one_mul]
  have hb1m : bm ≠ 1 := fun h => hb1 (Units.ext h)
  have hτs : Function.Surjective τ := Finite.injective_iff_surjective.mp τ.injective
  set τe : K ≃+* K := RingEquiv.ofBijective τ ⟨τ.injective, hτs⟩ with hτe
  have hproj := eigenProj_map_transpose τ hτω hbt hb3m hω
  have hEω : Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj bm ω))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj bm (ω ^ 2)))) := by
    rw [← hproj, finrank_range_toLin'_transpose]
    exact (finrank_range_toLin'_map_eq τe _).symm
  have hdim := finrank_eigenProj_le_two_of_swap hn h3K hω hb3m hb1m hEω
  have hmap : (b : Matrix n n K).map (RingHom.id K) = bm := by
    ext i j
    rfl
  exact eq_bot_of_commute_of_map h3K (RingHom.id K) hω (g := b)
    (fun c hc => by rw [hmap]; exact hdim c hc) Y hYb hYp hY3

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
