module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUPerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem s16nt_su_cent {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    (hK : Nat.card K = 4) {n : ℕ} (hn : 4 ≤ n) {s : SUid (s16ntSuSigma K) n}
    (hcomm : ∀ (g : SUid (s16ntSuSigma K) n) (l : K),
      g • s16ntSuV0 n K = l • s16ntSuV0 n K → g * s = s * g) :
    ∃ (S : Set ↥(SUid (s16ntSuSigma K) n)) (F : Submodule (ZMod 2) (Fin n → K)),
      (∀ d ∈ S, d ∈ s16ntSuMono K n ∧ d * s = s * d) ∧ Module.finrank (ZMod 2) F ≤ n ∧
        ∀ v : Fin n → K, (∀ d ∈ S, d • v = v) → v ∈ F := by
  classical
  rcases Nat.eq_or_lt_of_le hn with rfl | h5
  ·
    choose p hpM hpv using fun π : Equiv.Perm (Fin 4) => s16nt_su_perm_mem hK π
    refine ⟨Set.range p,
      LinearMap.range (LinearMap.pi fun _ : Fin 4 => (LinearMap.id : K →ₗ[ZMod 2] K)),
      ?_, ?_, ?_⟩
    · rintro d ⟨π, rfl⟩
      refine ⟨hpM π, ?_⟩
      apply hcomm (p π) 1
      funext k
      rw [hpv π (s16ntSuV0 4 K)]
      simp [s16ntSuV0]
    · have hfin : Module.finrank (ZMod 2) K = 2 := by
        have hcard : Nat.card K = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) K :=
          Module.natCard_eq_pow_finrank
        rw [hK, Nat.card_zmod] at hcard
        exact Nat.pow_right_injective (le_refl 2) (by
          show 2 ^ Module.finrank (ZMod 2) K = 2 ^ 2
          rw [← hcard])
      calc Module.finrank (ZMod 2)
            (LinearMap.range (LinearMap.pi fun _ : Fin 4 => (LinearMap.id : K →ₗ[ZMod 2] K)))
          ≤ Module.finrank (ZMod 2) K := LinearMap.finrank_range_le _
        _ = 2 := hfin
        _ ≤ 4 := by norm_num
    · intro v hv
      rw [LinearMap.mem_range]
      have hconst : ∀ i j : Fin 4, v i = v j := by
        intro i j
        have h := hv (p (Equiv.swap i j)) (Set.mem_range_self (Equiv.swap i j))
        have h2 : v ∘ Equiv.swap i j = v := (hpv (Equiv.swap i j) v).symm.trans h
        have h3 := congrFun h2 i
        rw [Function.comp_apply, Equiv.swap_apply_left] at h3
        exact h3.symm
      refine ⟨v 0, ?_⟩
      funext i
      rw [LinearMap.pi_apply]
      exact (hconst i 0).symm
  ·
    obtain ⟨ω0, hω00, hω01, _⟩ := s16nt_su_exists_omega hK
    let ω : Kˣ := Units.mk0 ω0 hω00
    have hω_ne_one : ω ≠ 1 := by
      intro h
      exact hω01 (by simpa [ω] using congrArg (fun u : Kˣ => (u : K)) h)
    have hω3 : ω ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      simpa [ω] using s16nt_su_pow_three hK hω00
    have hω2_ne_one : ω ^ 2 ≠ 1 := by
      intro h
      have h1 : ω = 1 := by
        calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
          _ = 1 * 1 := by rw [hω3, h, inv_one]
          _ = 1 := by rw [one_mul]
      exact hω_ne_one h1
    let i' : Fin n → Fin n := fun i => if i.val < 4 then ⟨4, h5⟩ else i
    let u : Fin n → Fin n → Kˣ := fun i k =>
      if k.val < 4 then ω else if k = i' i then ω ^ 2 else 1
    have hge : ∀ i : Fin n, 4 ≤ (i' i).val := by
      intro i
      change 4 ≤ (if i.val < 4 then (⟨4, h5⟩ : Fin n) else i).val
      split_ifs with h
      · simp
      · omega
    have hu : ∀ i, ∏ k, u i k = 1 := by
      intro i
      have hprod : ∏ k, u i k =
          (∏ k ∈ Finset.univ.filter (fun k : Fin n => k.val < 4), ω) *
          (∏ k ∈ Finset.univ.filter (fun k : Fin n => ¬ k.val < 4),
            (if k = i' i then ω ^ 2 else 1)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun k : Fin n => k.val < 4) (u i)]
        congr 1
        · refine Finset.prod_congr rfl fun k hk => ?_
          have hk' : k.val < 4 := (Finset.mem_filter.mp hk).2
          change (if k.val < 4 then ω else if k = i' i then ω ^ 2 else 1 : Kˣ) = ω
          rw [if_pos hk']
        · refine Finset.prod_congr rfl fun k hk => ?_
          have hk' : ¬ k.val < 4 := (Finset.mem_filter.mp hk).2
          change (if k.val < 4 then ω else if k = i' i then ω ^ 2 else 1 : Kˣ) =
            (if k = i' i then ω ^ 2 else 1)
          rw [if_neg hk']
      rw [hprod]
      have hcard : (Finset.univ.filter (fun k : Fin n => k.val < 4)).card = 4 := by
        rw [Fin.card_filter_val_lt]
        omega
      have hmem : i' i ∈ Finset.univ.filter (fun k : Fin n => ¬ k.val < 4) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, not_lt.mpr (hge i)⟩
      rw [Finset.prod_const, hcard,
        Finset.prod_ite_eq_of_mem' (Finset.univ.filter (fun k : Fin n => ¬ k.val < 4))
          (i' i) (fun _ => ω ^ 2) hmem]
      calc ω ^ 4 * ω ^ 2 = ω ^ (4 + 2) := (pow_add ω 4 2).symm
        _ = (ω ^ 3) ^ 2 := by rw [show 4 + 2 = 3 * 2 by norm_num, pow_mul]
        _ = 1 := by rw [hω3, one_pow]
    choose d hdT hdv using fun i : Fin n => s16nt_su_diag_mem hK (u i) (hu i)
    have hcommd : ∀ i, d i * s = s * d i := by
      intro i
      apply hcomm (d i) (ω : K)
      funext k
      rw [hdv i (s16ntSuV0 n K)]
      change (u i k : K) * (if k.val < 4 then 1 else 0) =
        (ω : K) * (if k.val < 4 then 1 else 0)
      by_cases hk : k.val < 4
      · have huk : u i k = ω := by
          change (if k.val < 4 then ω else if k = i' i then ω ^ 2 else 1 : Kˣ) = ω
          rw [if_pos hk]
        rw [huk]
      · simp only [if_neg hk, mul_zero]
    refine ⟨Set.range d, ⊥, ?_, ?_, ?_⟩
    · rintro x ⟨i, rfl⟩
      exact ⟨Subgroup.le_normalizer (hdT i), hcommd i⟩
    · simp
    · intro v hv
      rw [Submodule.mem_bot]
      funext i
      have hfix : d i • v = v := hv (d i) (Set.mem_range_self i)
      have hvi : v i = (u i i : K) * v i := by
        have h := congrFun (hfix.symm.trans (hdv i v)) i
        simpa using h
      have h0 : ((u i i : K) - 1) * v i = 0 := by linear_combination -hvi
      have hne : (u i i : K) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        by_cases hi : i.val < 4
        · have hii : u i i = ω := by
            change (if i.val < 4 then ω else if i = i' i then ω ^ 2 else 1 : Kˣ) = ω
            rw [if_pos hi]
          rw [hii]
          intro hc
          exact hω_ne_one (Units.ext (by simpa using hc))
        · have hi' : i' i = i := by
            change (if i.val < 4 then (⟨4, h5⟩ : Fin n) else i) = i
            rw [if_neg hi]
          have hii : u i i = ω ^ 2 := by
            change (if i.val < 4 then ω else if i = i' i then ω ^ 2 else 1 : Kˣ) = ω ^ 2
            rw [if_neg hi, if_pos hi'.symm]
          rw [hii]
          intro hc
          exact hω2_ne_one (Units.ext (by simpa using hc))
      exact (mul_eq_zero.mp h0).resolve_left hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
