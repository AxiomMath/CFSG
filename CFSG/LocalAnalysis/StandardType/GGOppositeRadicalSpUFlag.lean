module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalStd
public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.GroupTheory.OppositeRadicals

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open CFSG.Open CFSG.LieType.BorelTits

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure IsSelfDual (F : ReflForm K V) (A : ℕ → Submodule K V) (N : ℕ) : Prop where
  mono : Monotone A
  zero : A 0 = ⊥
  top : ∀ k, N ≤ k → A k = ⊤
  perp : ∀ k ≤ N, F.perp (A k) = A (N - k)

namespace IsSelfDual

variable {F : ReflForm K V} {A : ℕ → Submodule K V} {N : ℕ}

theorem mem_perp (hA : IsSelfDual F A N) {k : ℕ} (hk : k ≤ N) {x v : V} (hx : x ∈ A k)
    (hv : v ∈ A (N - k)) : F.β x v = 0 := by
  rw [← hA.perp k hk] at hv
  exact hv x hx

theorem mem_perp' (hA : IsSelfDual F A N) {k : ℕ} (hk : k ≤ N) {x v : V} (hx : x ∈ A (N - k))
    (hv : v ∈ A k) : F.β x v = 0 := by
  have h := hA.mem_perp (k := N - k) (Nat.sub_le N k) hx (v := v)
  rw [Nat.sub_sub_self hk] at h
  exact h hv

end IsSelfDual

theorem isCompl_perp [FiniteDimensional K V] (F : ReflForm K V) {W W' : Submodule K V}
    (h : IsCompl W W') : IsCompl (F.perp W) (F.perp W') := by
  have hdis : F.perp W ⊓ F.perp W' = ⊥ := by
    rw [← F.perp_sup, h.sup_eq_top, F.perp_top]
  refine ⟨disjoint_iff.mpr hdis, codisjoint_iff.mpr ?_⟩
  have h1 := F.finrank_perp W
  have h2 := F.finrank_perp W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (F.perp W) (F.perp W')
  rw [hdis, finrank_bot] at h4
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem perp_ne_bot [FiniteDimensional K V] (F : ReflForm K V) {W : Submodule K V}
    (hW : W ≠ ⊤) : F.perp W ≠ ⊥ := by
  intro h
  apply hW
  rw [← F.perp_perp W, h, F.perp_bot]

section IsoFlag

variable {H : Type*} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)

theorem isoFlag_mono [FiniteDimensional K V] (R : Subgroup H) : Monotone (isoFlag F ρ R) := by
  intro k k' hkk'
  have hmid : isoSeq F ρ R (Module.finrank K V) ≤
      F.perp (isoSeq F ρ R (Module.finrank K V)) := isoSeq_isTotallyIsotropic F ρ R _
  unfold isoFlag
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact isoSeq_mono F ρ R hkk'
  · exact (isoSeq_mono F ρ R h1).trans (hmid.trans
      (F.perp_antitone (isoSeq_mono F ρ R (by omega))))
  · exact le_top
  · omega
  · exact F.perp_antitone (isoSeq_mono F ρ R (by omega))
  · exact le_top
  · omega
  · omega
  · exact le_top

theorem isSelfDual_isoFlag [FiniteDimensional K V] (R : Subgroup H) :
    IsSelfDual F (isoFlag F ρ R) (2 * Module.finrank K V + 1) := by
  refine ⟨isoFlag_mono F ρ R, isoFlag_zero F ρ R, fun k hk => ?_, fun k hk => ?_⟩
  · rcases hk.lt_or_eq with hk | rfl
    · rw [isoFlag, ite_eq_right (by omega), ite_eq_right (by omega)]
    · exact isoFlag_top F ρ R
  · by_cases hkd : k ≤ Module.finrank K V
    · rw [isoFlag, ite_eq_left hkd, isoFlag, ite_eq_right (by omega), ite_eq_left (by omega),
        Nat.sub_sub_self hk]
    · rw [isoFlag, ite_eq_right hkd, ite_eq_left hk, F.perp_perp, isoFlag,
        ite_eq_left (by omega)]

theorem eq_flagKernel_isoFlag_of_isRadicalPGroup [Finite H] [Finite V] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hρ : Function.Injective ρ) (hiso : IsIsometric F ρ) {Q : Subgroup H}
    (hQ : CFSG.GroupTheory.IsRadicalPGroup p ⊤ Q) :
    Q = flagKernel ρ (isoFlag F ρ Q) ∧
      (⊤ : Subgroup H) ⊓ Subgroup.normalizer (Q : Set H) = flagStab ρ (isoFlag F ρ Q) := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hker : flagKernel ρ (isoFlag F ρ Q) ≤ pCoreOf p (flagStab ρ (isoFlag F ρ Q)) :=
    flagKernel_le_pCoreOf ρ p hρ (isoFlag_zero F ρ Q) (isoFlag_top F ρ Q)
  have hle : Q ≤ flagKernel ρ (isoFlag F ρ Q) :=
    le_flagKernel_isoFlag F ρ p hiso Q hQ.isPGroup
  obtain ⟨hcore, hN⟩ := hQ.eq_of_normalizer_le le_top
    (inf_le_right.trans (normalizer_le_flagStab_isoFlag F ρ hiso Q)) (hle.trans hker)
  exact ⟨le_antisymm hle (hker.trans hcore.le), hN⟩

theorem eq_flagKernel_isoFlag_of_radical [Finite H] [Finite V] [CharP K 2]
    (hρ : Function.Injective ρ) (hiso : IsIsometric F ρ) {Q : Subgroup H}
    (hQ : GGRadicalTwo ⊤ Q) :
    Q = flagKernel ρ (isoFlag F ρ Q) ∧
      (⊤ : Subgroup H) ⊓ Subgroup.normalizer (Q : Set H) = flagStab ρ (isoFlag F ρ Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact eq_flagKernel_isoFlag_of_isRadicalPGroup F ρ 2 hρ hiso hQ

end IsoFlag

section Kernel

variable {H : Type*} [Group H] [Finite H] (ρ : H →* Module.End K V) {F : ReflForm K V}

theorem mem_flagKernel_of_sub_mem {A : ℕ → Submodule K V} (hA : Monotone A) (hA0 : A 0 = ⊥)
    {g : H} (hg : ∀ k, ∀ v ∈ A (k + 1), ρ g v - v ∈ A k) : g ∈ flagKernel ρ A := by
  refine (mem_flagKernel ρ).mpr ⟨GGOppRad.mem_flagStab_of_forall ρ fun k v hv => ?_, hg⟩
  cases k with
  | zero =>
    rw [hA0, Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  | succ k =>
    have := add_mem (hA (Nat.le_succ k) (hg k v hv)) hv
    rwa [sub_add_cancel] at this

theorem mem_flagKernel_of_apply {A : ℕ → Submodule K V} {N : ℕ} (hA : IsSelfDual F A N)
    {j : ℕ} (hj : j ≤ N) {x y y' z : V} (hx : x ∈ A j) (hz : z ∈ A j) (hy : y ∈ A (N - j))
    (hy' : y' ∈ A (N - j)) {g : H} (hg : ∀ v, ρ g v = v + F.β x v • y + F.β y' v • z) :
    g ∈ flagKernel ρ A := by
  refine mem_flagKernel_of_sub_mem ρ hA.mono hA.zero fun k v hv => ?_
  rw [hg, add_assoc, add_sub_cancel_left]
  refine add_mem ?_ ?_
  · by_cases h : F.β x v = 0
    · rw [h, zero_smul]
      exact zero_mem _
    · refine Submodule.smul_mem _ _ (hA.mono ?_ hy)
      by_contra hlt
      exact h (hA.mem_perp hj hx (hA.mono (by omega) hv))
  · by_cases h : F.β y' v = 0
    · rw [h, zero_smul]
      exact zero_mem _
    · refine Submodule.smul_mem _ _ (hA.mono ?_ hz)
      by_contra hlt
      exact h (hA.mem_perp' hj hy' (hA.mono (by omega) hv))

omit [Finite H] in
theorem ne_one_of_apply {g : H} {x y y' z : V} (hg : ∀ v, ρ g v = v + F.β x v • y + F.β y' v • z)
    {v : V} (hv : F.β x v • y + F.β y' v • z ≠ 0) : g ≠ 1 := by
  rintro rfl
  apply hv
  have := hg v
  rw [map_one, Module.End.one_apply, add_assoc, left_eq_add] at this
  exact this

end Kernel

section Opposite

variable {H : Type*} [Group H] [Finite H] (ρ : H →* Module.End K V) {F : ReflForm K V}

theorem exists_β_eq_one {x : V} (hx : x ≠ 0) : ∃ v, F.β x v = 1 := by
  by_contra h
  apply hx
  refine F.nondeg x fun v => ?_
  by_contra hv
  exact h ⟨(F.β x v)⁻¹ • v, by rw [F.smul_right, inv_mul_cancel₀ hv]⟩

theorem exists_isCompl_of_inf_eq_bot [FiniteDimensional K V]
    (htv : ∀ x : V, ∃ h : H, ∀ v, ρ h v = v + F.β x v • x)
    (hsg : ∀ x y : V, F.β x y = 0 → ∃ h : H, ∀ v, ρ h v = v + F.β x v • y + F.β y v • x)
    {A F' : ℕ → Submodule K V} {N N' : ℕ} (hA : IsSelfDual F A N) (hF' : IsSelfDual F F' N')
    (hbot : flagKernel ρ F' ⊓ flagStab ρ A = ⊥) (j : ℕ) : ∃ k, IsCompl (A k) (F' j) := by
  classical
  have h1 : ∀ g : H, g ∈ flagKernel ρ F' → (∀ i, ∀ v ∈ A i, ρ g v ∈ A i) → g = 1 := by
    intro g hg hgA
    have : g ∈ flagKernel ρ F' ⊓ flagStab ρ A :=
      ⟨hg, GGOppRad.mem_flagStab_of_forall ρ hgA⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have key : ∀ j, 2 * j ≤ N' → ∃ k, IsCompl (A k) (F' j) := by
    intro j hj
    by_cases hX : F' j = ⊥
    · exact ⟨N, by rw [hA.top N le_rfl, hX]; exact isCompl_top_bot⟩
    have hex : ∃ k, A (k + 1) ⊓ F' j ≠ ⊥ :=
      ⟨N, by rw [hA.top (N + 1) (by omega), top_inf_eq]; exact hX⟩
    set k := Nat.find hex with hk
    have hk1 : A (k + 1) ⊓ F' j ≠ ⊥ := Nat.find_spec hex
    have hk0 : A k ⊓ F' j = ⊥ := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, hA.zero, bot_inf_eq]
      · have := Nat.find_min hex (show k - 1 < k by omega)
        rwa [not_not, Nat.sub_add_cancel hpos] at this
    have hkN : k < N := by
      by_contra hkN
      rw [hA.top k (by omega), top_inf_eq] at hk0
      exact hX hk0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk1
    have hxA : x ∈ A (k + 1) := (Submodule.mem_inf.mp hx).1
    have hxF : x ∈ F' j := (Submodule.mem_inf.mp hx).2
    have hjN : j ≤ N' := by omega
    have hxF' : x ∈ F' (N' - j) := hF'.mono (by omega) hxF
    obtain ⟨t, ht⟩ := htv x
    have ht' : ∀ v, ρ t v = v + F.β x v • x + F.β x v • (0 : V) := fun v => by
      rw [ht, smul_zero, add_zero]
    have htK : t ∈ flagKernel ρ F' :=
      mem_flagKernel_of_apply ρ hF' hjN hxF (zero_mem _) hxF' hxF' ht'
    obtain ⟨w, hw⟩ := exists_β_eq_one (F := F) hx0
    have ht1 : t ≠ 1 := ne_one_of_apply ρ ht' (v := w)
      (by rw [hw, one_smul, smul_zero, add_zero]; exact hx0)
    have htA : x ∈ A (N - k) → ∀ i, ∀ v ∈ A i, ρ t v ∈ A i := by
      intro hxk i v hv
      rw [ht]
      rcases Nat.lt_or_ge k i with hki | hik
      · exact add_mem hv (Submodule.smul_mem _ _ (hA.mono hki hxA))
      · rw [hA.mem_perp' hkN.le hxk (hA.mono hik hv), zero_smul, add_zero]
        exact hv
    by_cases hcase : 2 * (k + 1) ≤ N
    · exact absurd (h1 t htK (htA (hA.mono (by omega) hxA))) ht1
    refine ⟨k, disjoint_iff.mpr hk0, codisjoint_iff.mpr ?_⟩
    by_contra hne
    have hperp := perp_ne_bot F hne
    rw [F.perp_sup, hA.perp k hkN.le, hF'.perp j hjN] at hperp
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    have hyA : y ∈ A (N - k) := (Submodule.mem_inf.mp hy).1
    have hyF : y ∈ F' (N' - j) := (Submodule.mem_inf.mp hy).2
    by_cases hdep : ∃ c : K, y = c • x
    · obtain ⟨c, rfl⟩ := hdep
      have hc : c ≠ 0 := by
        rintro rfl
        exact hy0 (zero_smul K x)
      have hxk : x ∈ A (N - k) := by
        have := Submodule.smul_mem _ c⁻¹ hyA
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      exact ht1 (h1 t htK (htA hxk))
    have hxy : F.β x y = 0 := hF'.mem_perp hjN hxF hyF
    obtain ⟨s, hs⟩ := hsg x y hxy
    have hsK : s ∈ flagKernel ρ F' :=
      mem_flagKernel_of_apply ρ hF' hjN hxF hxF hyF hyF hs
    have hsA : ∀ i, ∀ v ∈ A i, ρ s v ∈ A i := by
      intro i v hv
      rw [hs]
      rcases Nat.lt_or_ge k i with hki | hik
      · refine add_mem (add_mem hv (Submodule.smul_mem _ _ (hA.mono ?_ hyA)))
          (Submodule.smul_mem _ _ (hA.mono hki hxA))
        omega
      · rw [hA.mem_perp' hkN.le hyA (hA.mono hik hv), zero_smul, add_zero]
        rcases Nat.lt_or_ge i (N - k) with hi | hi
        · rw [hA.mem_perp (show k + 1 ≤ N by omega) hxA (hA.mono (by omega) hv), zero_smul,
            add_zero]
          exact hv
        · exact add_mem hv (Submodule.smul_mem _ _ (hA.mono hi hyA))
    have hs1 := h1 s hsK hsA
    apply hdep
    refine ⟨-F.β y w, ?_⟩
    have h2 := hs w
    rw [hs1, map_one, Module.End.one_apply, hw, one_smul, add_assoc, left_eq_add] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  by_cases hj : 2 * j ≤ N'
  · exact key j hj
  by_cases hjN : N' ≤ j
  · exact ⟨0, by rw [hA.zero, hF'.top j hjN]; exact isCompl_bot_top⟩
  obtain ⟨k, hk⟩ := key (N' - j) (by omega)
  have hk' : IsCompl (A (min k N)) (F' (N' - j)) := by
    rcases le_total k N with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h, hA.top N le_rfl, ← hA.top k h]
  have := isCompl_perp F hk'
  rw [hA.perp _ (min_le_right k N), hF'.perp _ (Nat.sub_le N' j),
    Nat.sub_sub_self (by omega)] at this
  exact ⟨_, this⟩

end Opposite

end GGOppRadSpU

end CFSG.StandardType
