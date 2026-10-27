module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUFlag
public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open CFSG.Open CFSG.LieType.BorelTits GGOppRadSpU Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type*} [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V)

theorem singSeq_eq_of_le [FiniteDimensional K V] (R : Subgroup H) {j : ℕ}
    (hj : finrank K V ≤ j) : singSeq Φ ρ R j = singSeq Φ ρ R (finrank K V) := by
  ext w
  rw [mem_singSeq, mem_singSeq, isoSeq_eq_of_le Φ.polar ρ R hj]

theorem isSelfDual_singFlag [FiniteDimensional K V] (R : Subgroup H) :
    IsSelfDual Φ.polar (singFlag Φ ρ R) (2 * finrank K V + 1) := by
  have hiso : ∀ k, Φ.polar.IsTotallyIsotropic (singSeq Φ ρ R k) := fun k =>
    (isTotallySingular_singSeq Φ ρ R k).isTotallyIsotropic
  refine ⟨monotone_nat_of_le_succ (isoCompletion_le_succ (singSeq_mono Φ ρ R) hiso _),
    singFlag_zero Φ ρ R, fun k hk => ?_, fun k hk => ?_⟩
  · rcases hk.lt_or_eq with hk | rfl
    · exact isoCompletion_of_lt hk
    · exact singFlag_top Φ ρ R
  · by_cases hkd : k ≤ finrank K V
    · rw [singFlag, isoCompletion_of_le hkd]
      have := isoCompletion_perp (F := Φ.polar) (X := singSeq Φ ρ R) hkd
      rw [this]
    · have e : singFlag Φ ρ R k = Φ.polar.perp (singSeq Φ ρ R (2 * finrank K V + 1 - k)) := by
        have := isoCompletion_perp (F := Φ.polar) (X := singSeq Φ ρ R)
          (m := finrank K V) (k := 2 * finrank K V + 1 - k) (by omega)
        rw [show 2 * finrank K V + 1 - (2 * finrank K V + 1 - k) = k by omega] at this
        exact this
      rw [e, Φ.polar.perp_perp, singFlag, isoCompletion_of_le (by omega)]

theorem isTotallySingular_singFlag (R : Subgroup H) {k : ℕ} (hk : k ≤ finrank K V) :
    Φ.IsTotallySingular (singFlag Φ ρ R k) := by
  rw [singFlag, isoCompletion_of_le hk]
  exact isTotallySingular_singSeq Φ ρ R k

variable {Φ ρ} in
theorem eq_flagKernel_singFlag_of_radical [Finite H] [Finite V] [CharP K 2]
    (hρ : Function.Injective ρ) (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v)
    (hstar : NoQuotientReflection Φ ρ) {R : Subgroup H} (hR : GGRadicalTwo ⊤ R) :
    R = flagKernel ρ (singFlag Φ ρ R) ∧
      (⊤ : Subgroup H) ⊓ Subgroup.normalizer (R : Set H) = flagStab ρ (singFlag Φ ρ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hker : flagKernel ρ (singFlag Φ ρ R) ≤ pCoreOf 2 (flagStab ρ (singFlag Φ ρ R)) :=
    flagKernel_le_pCoreOf ρ 2 hρ (singFlag_zero Φ ρ R) (singFlag_top Φ ρ R)
  have hle : R ≤ flagKernel ρ (singFlag Φ ρ R) :=
    le_flagKernel_singFlag 2 hQ hstar R hR.isPGroup
  obtain ⟨hcore, hN⟩ := hR.eq_of_normalizer_le le_top
    (inf_le_right.trans (normalizer_le_flagStab_singFlag hQ R)) (hle.trans hker)
  exact ⟨le_antisymm hle (hker.trans hcore.le), hN⟩

variable {Φ} in
theorem eichler_mem_flagKernel [Finite H] {A : ℕ → Submodule K V} {N : ℕ}
    (hA : IsSelfDual Φ.polar A N) {j : ℕ} (hj : j ≤ N) {x y : V} (hx : x ∈ A j)
    (hjN : A j ≤ A (N - j)) (hy : y ∈ A (N - j)) {g : H}
    (hg : ∀ v, ρ g v = Φ.eichler x y v) : g ∈ flagKernel ρ A := by
  refine mem_flagKernel_of_apply ρ hA hj hx (neg_mem hx) (y := y - Φ.Q y • x) (y' := y)
    (sub_mem hy (Submodule.smul_mem _ _ (hjN hx))) hy fun v => ?_
  rw [hg, QuadForm.eichler_apply, smul_neg, sub_eq_add_neg]

variable {Φ} in
theorem mem_flagStab_of_apply [Finite H] {A : ℕ → Submodule K V} {x y a b : V} {g : H}
    (hg : ∀ v, ρ g v = v + Φ.polar.β x v • a + Φ.polar.β y v • b)
    (h1 : ∀ i, a ∈ A i ∨ x ∈ Φ.polar.perp (A i))
    (h2 : ∀ i, b ∈ A i ∨ y ∈ Φ.polar.perp (A i)) : g ∈ flagStab ρ A := by
  refine GGOppRad.mem_flagStab_of_forall ρ fun i v hv => ?_
  rw [hg]
  refine add_mem (add_mem hv ?_) ?_
  · rcases h1 i with h | h
    · exact Submodule.smul_mem _ _ h
    · rw [Φ.polar_symm, h v hv, zero_smul]
      exact zero_mem _
  · rcases h2 i with h | h
    · exact Submodule.smul_mem _ _ h
    · rw [Φ.polar_symm, h v hv, zero_smul]
      exact zero_mem _

variable {Φ} in
theorem eichler_apply' (x y v : V) :
    Φ.eichler x y v = v + Φ.polar.β x v • (y - Φ.Q y • x) + Φ.polar.β y v • (-x) := by
  rw [QuadForm.eichler_apply, smul_neg, sub_eq_add_neg]

variable {Φ} in
theorem exists_eq_smul_of_eichler_eq {x y : V} (hx0 : x ≠ 0)
    (h : ∀ v, Φ.eichler x y v = v) : ∃ c : K, y = c • x := by
  obtain ⟨w, hw⟩ := exists_β_eq_one (F := Φ.polar) hx0
  have h1 := h w
  rw [QuadForm.eichler_apply, hw, one_smul] at h1
  exact ⟨Φ.Q y + Φ.polar.β y w, by linear_combination (norm := module) h1⟩

variable {Φ ρ} in
theorem isCompl_or_oriflamme [Finite H] [FiniteDimensional K V] (hV : Even (finrank K V))
    (heich : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 → ∃ h : H, ∀ v, ρ h v = Φ.eichler x y v)
    {A F' : ℕ → Submodule K V} {N N' : ℕ} (hA : IsSelfDual Φ.polar A N)
    (hF' : IsSelfDual Φ.polar F' N')
    (hAs : ∀ k, 2 * k ≤ N → Φ.IsTotallySingular (A k))
    (hFs : ∀ j, 2 * j ≤ N' → Φ.IsTotallySingular (F' j))
    (hbot : flagKernel ρ F' ⊓ flagStab ρ A = ⊥) {j : ℕ} (hj : 2 * j ≤ N') :
    (∃ k, IsCompl (A k) (F' j)) ∨
      (2 * finrank K (F' j) = finrank K V ∧ ∃ k x, 2 * k ≤ N ∧
        2 * (finrank K (A k) + 1) = finrank K V ∧ A k ⊓ F' j = ⊥ ∧ x ∈ F' j ∧ x ∉ A k ∧
        F' j ⊓ Φ.polar.perp (A k) = K ∙ x ∧
        (N = 2 * k + 1 ∨ 2 * (k + 1) ≤ N ∧ A (k + 1) = A k ⊔ K ∙ x)) := by
  classical
  by_cases hX : F' j = ⊥
  · exact Or.inl ⟨N, by rw [hA.top N le_rfl, hX]; exact isCompl_top_bot⟩
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
  have hXs : Φ.IsTotallySingular (F' j) := hFs j hj
  have hXperp : F' j ≤ F' (N' - j) := by
    rw [← hF'.perp j hjN]
    exact hXs.isTotallyIsotropic
  have hQx : Φ.Q x = 0 := hXs x hxF
  have hxk : x ∉ A k := fun h => hx0 (by
    have := Submodule.mem_inf.mpr ⟨h, hxF⟩
    rwa [hk0, Submodule.mem_bot] at this)
  have hperp : ∀ {m i : ℕ} {z : V}, z ∈ A m → i + m ≤ N → z ∈ Φ.polar.perp (A i) := by
    intro m i z hz hmi
    rw [hA.perp i (by omega)]
    exact hA.mono (by omega) hz
  have hkey : ∀ y ∈ F' (N' - j), (∀ i, y - Φ.Q y • x ∈ A i ∨ x ∈ Φ.polar.perp (A i)) →
      (∀ i, -x ∈ A i ∨ y ∈ Φ.polar.perp (A i)) → ∃ c : K, y = c • x := by
    intro y hy h1 h2
    have hxy : Φ.polar.β x y = 0 := hF'.mem_perp hjN hxF hy
    obtain ⟨g, hg⟩ := heich x y hQx hxy
    have hgK : g ∈ flagKernel ρ F' := eichler_mem_flagKernel ρ hF' hjN hxF hXperp hy hg
    have hgS : g ∈ flagStab ρ A :=
      mem_flagStab_of_apply ρ (fun v => by rw [hg, eichler_apply']) h1 h2
    have hg1 : g = 1 := by
      have : g ∈ flagKernel ρ F' ⊓ flagStab ρ A := ⟨hgK, hgS⟩
      rwa [hbot, Subgroup.mem_bot] at this
    refine exists_eq_smul_of_eichler_eq (Φ := Φ) hx0 fun v => ?_
    rw [← hg, hg1, map_one, Module.End.one_apply]
  have hspan : ∀ y : V, (∃ c : K, y = c • x) → y ∈ K ∙ x := by
    rintro y ⟨c, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
  by_cases hcase : 2 * (k + 1) ≤ N
  ·
    have hAk1s := hAs (k + 1) hcase
    have ha : Φ.polar.perp (F' j ⊔ A (k + 1)) ≤ K ∙ x := by
      intro y hy
      rw [Φ.polar.perp_sup, hF'.perp j hjN, hA.perp (k + 1) (by omega)] at hy
      obtain ⟨hyF, hyA⟩ := Submodule.mem_inf.mp hy
      refine hspan y (hkey y hyF (fun i => ?_) (fun i => ?_))
      · rcases le_total (N - (k + 1)) i with hi | hi
        · exact Or.inl (sub_mem (hA.mono hi hyA)
            (Submodule.smul_mem _ _ (hA.mono (by omega) hxA)))
        · exact Or.inr (hperp hxA (by omega))
      · rcases le_total (k + 1) i with hi | hi
        · exact Or.inl (neg_mem (hA.mono hi hxA))
        · exact Or.inr (hperp hyA (by omega))
    have hb : F' j ⊓ Φ.polar.perp (A k) = K ∙ x := by
      refine le_antisymm (fun y hy => ?_) ?_
      · obtain ⟨hyF, hyA⟩ := Submodule.mem_inf.mp hy
        rw [hA.perp k hkN.le] at hyA
        have hQy : Φ.Q y = 0 := hXs y hyF
        refine hspan y (hkey y (hXperp hyF) (fun i => ?_) (fun i => ?_))
        · rcases Nat.lt_or_ge i (N - k) with hi | hi
          · exact Or.inr (hperp hxA (by omega))
          · rw [hQy, zero_smul, sub_zero]
            exact Or.inl (hA.mono hi hyA)
        · rcases Nat.lt_or_ge i (k + 1) with hi | hi
          · exact Or.inr (hperp hyA (by omega))
          · exact Or.inl (neg_mem (hA.mono hi hxA))
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_inf.mpr ⟨hxF, hperp hxA (by omega)⟩
    have hx1 : finrank K (K ∙ x) = 1 := finrank_span_singleton hx0
    have hdX : finrank K (F' j) ≤ finrank K (A k) + 1 := by
      have := hXs.isTotallyIsotropic.finrank_add_finrank_inf_le (A k)
      rw [hk0, finrank_bot, hb, hx1] at this
      omega
    have hinf : 1 ≤ finrank K ↥(F' j ⊓ A (k + 1)) := by
      have : K ∙ x ≤ F' j ⊓ A (k + 1) := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_inf.mpr ⟨hxF, hxA⟩
      have := Submodule.finrank_mono this
      omega
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F' j) (A (k + 1))
    have h2 := Φ.polar.finrank_perp (F' j ⊔ A (k + 1))
    have h3 := Submodule.finrank_mono ha
    have h4 := hXs.two_mul_finrank_le
    have h5 := hAk1s.two_mul_finrank_le
    have hlt : finrank K (A k) < finrank K (A (k + 1)) :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hA.mono (Nat.le_succ k))
        fun h => hxk (h ▸ hxA))
    have hsup : A (k + 1) = A k ⊔ K ∙ x := by
      refine (Submodule.eq_of_le_of_finrank_eq (sup_le (hA.mono (by omega : k ≤ k + 1))
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hxA)) ?_).symm
      rw [Submodule.finrank_sup_span_singleton hxk]
      omega
    refine Or.inr ⟨by omega, k, x, by omega, by omega, hk0, hxF, hxk, hb, Or.inr ⟨hcase, hsup⟩⟩
  ·
    by_cases hcod : A k ⊔ F' j = ⊤
    · exact Or.inl ⟨k, disjoint_iff.mpr hk0, codisjoint_iff.mpr hcod⟩
    have hperp0 := perp_ne_bot Φ.polar hcod
    rw [Φ.polar.perp_sup, hA.perp k hkN.le, hF'.perp j hjN] at hperp0
    have hall : ∀ y ∈ A (N - k) ⊓ F' (N' - j), ∃ c : K, y = c • x := by
      intro y hy
      obtain ⟨hyA, hyF⟩ := Submodule.mem_inf.mp hy
      by_cases h2 : 2 * (N - k) ≤ N
      · have hQy : Φ.Q y = 0 := hAs (N - k) h2 y hyA
        refine hkey y hyF (fun i => ?_) (fun i => ?_)
        · rcases Nat.lt_or_ge i (N - k) with hi | hi
          · exact Or.inr (hperp hxA (by omega))
          · rw [hQy, zero_smul, sub_zero]
            exact Or.inl (hA.mono hi hyA)
        · rcases Nat.lt_or_ge i (k + 1) with hi | hi
          · exact Or.inr (hperp hyA (by omega))
          · exact Or.inl (neg_mem (hA.mono hi hxA))
      · have hyA' : y ∈ A (k + 1) := hA.mono (by omega) hyA
        refine hkey y hyF (fun i => ?_) (fun i => ?_)
        · rcases Nat.lt_or_ge i (k + 1) with hi | hi
          · exact Or.inr (hperp hxA (by omega))
          · exact Or.inl (sub_mem (hA.mono hi hyA')
              (Submodule.smul_mem _ _ (hA.mono hi hxA)))
        · rcases Nat.lt_or_ge i (k + 1) with hi | hi
          · exact Or.inr (hperp hyA (by omega))
          · exact Or.inl (neg_mem (hA.mono hi hxA))
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp0
    obtain ⟨c, hc⟩ := hall y hy
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hy0 (by rw [hc, zero_smul])
    have hxNk : x ∈ A (N - k) ⊓ F' (N' - j) := by
      have := Submodule.smul_mem _ c⁻¹ hy
      rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    have hNk : N = 2 * k + 1 := by
      by_contra hne
      exact hxk (hA.mono (by omega) (Submodule.mem_inf.mp hxNk).1)
    have hAks := hAs k (by omega)
    have heq : A (N - k) ⊓ F' (N' - j) = K ∙ x := by
      refine le_antisymm (fun y hy => hspan y (hall y hy)) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact hxNk
    have hx1 : finrank K (K ∙ x) = 1 := finrank_span_singleton hx0
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (A k) (F' j)
    have h2 := Φ.polar.finrank_perp (A k ⊔ F' j)
    rw [Φ.polar.perp_sup, hA.perp k hkN.le, hF'.perp j hjN, heq, hx1] at h2
    rw [hk0, finrank_bot] at h1
    have h4 := hXs.two_mul_finrank_le
    have h5 := hAks.two_mul_finrank_le
    obtain ⟨m, hm⟩ := hV
    have hAk : finrank K (A k) + 1 = m := by
      by_contra hne
      have hAm : 2 * finrank K (A k) = finrank K V := by omega
      have hpe := Φ.polar.perp_eq_self_of_two_mul_finrank hAks.isTotallyIsotropic hAm
      rw [hA.perp k hkN.le, show N - k = k + 1 by omega] at hpe
      exact hk1 (by rw [hpe, hk0])
    have hXL : F' (N' - j) = F' j := by
      refine (Submodule.eq_of_le_of_finrank_eq hXperp ?_).symm
      have := Φ.polar.finrank_perp (F' j)
      rw [hF'.perp j hjN] at this
      omega
    refine Or.inr ⟨by omega, k, x, by omega, by omega, hk0, hxF, hxk, ?_, Or.inl hNk⟩
    rw [hA.perp k hkN.le, inf_comm, ← heq, hXL]

variable {Φ ρ} in
theorem not_two_mul_finrank_singSeq_succ [FiniteDimensional K V]
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (R : Subgroup H) (k : ℕ)
    (hZ : 2 * (finrank K (singSeq Φ ρ R k) + 1) = finrank K V)
    (hL : 2 * finrank K (singSeq Φ ρ R (k + 1)) = finrank K V) : False := by
  have hW'iso := isoSeq_isTotallyIsotropic Φ.polar ρ R (k + 1)
  have hLW' := singSeq_le_isoSeq Φ ρ R (k + 1)
  have hW'L : isoSeq Φ.polar ρ R (k + 1) = singSeq Φ ρ R (k + 1) := by
    have h1 := Φ.polar.finrank_perp (isoSeq Φ.polar ρ R (k + 1))
    have h2 := Submodule.finrank_mono hW'iso
    have h3 := Submodule.finrank_mono hLW'
    exact (Submodule.eq_of_le_of_finrank_eq hLW' (by omega)).symm
  have hWZ : isoSeq Φ.polar ρ R k = singSeq Φ ρ R k := by
    refine le_antisymm (fun w hw => ⟨hw, ?_⟩) (singSeq_le_isoSeq Φ ρ R k)
    have h := isoSeq_le_succ Φ.polar ρ R k hw
    rw [hW'L] at h
    exact h.2
  have hLs := isTotallySingular_singSeq Φ ρ R (k + 1)
  have hZs := isTotallySingular_singSeq Φ ρ R k
  have hLperp : Φ.polar.perp (singSeq Φ ρ R (k + 1)) = singSeq Φ ρ R (k + 1) :=
    Φ.polar.perp_eq_self_of_two_mul_finrank hLs.isTotallyIsotropic hL
  have hPL : relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R = singSeq Φ ρ R (k + 1) := by
    have hW' : isoSeq Φ.polar ρ R (k + 1) = relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R ⊓
        Φ.polar.perp (relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R) := rfl
    refine le_antisymm ?_ (by rw [← hW'L, hW']; exact inf_le_left)
    have h1 : singSeq Φ ρ R (k + 1) ≤
        Φ.polar.perp (relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R) := by
      rw [← hW'L, hW']
      exact inf_le_right
    calc relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R
        ≤ Φ.polar.perp (Φ.polar.perp (relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R)) :=
          Φ.polar.le_perp_perp _
      _ ≤ Φ.polar.perp (singSeq Φ ρ R (k + 1)) := Φ.polar.perp_antitone h1
      _ = singSeq Φ ρ R (k + 1) := hLperp
  have hZL : singSeq Φ ρ R k < singSeq Φ ρ R (k + 1) := by
    refine lt_of_le_of_ne (singSeq_mono Φ ρ R (by omega : k ≤ k + 1)) fun h => ?_
    rw [h] at hZ
    omega
  obtain ⟨e, heL, heZ⟩ := IsConcreteLE.exists_of_lt hZL
  have heperp : e ∈ Φ.polar.perp (singSeq Φ ρ R k) := fun z hz =>
    hLs.isTotallyIsotropic heL z (singSeq_mono Φ ρ R (by omega : k ≤ k + 1) hz)
  have hefix : ∀ g ∈ R, ρ g e - e ∈ singSeq Φ ρ R k := by
    intro g hg
    have he : e ∈ relFix Φ.polar ρ (isoSeq Φ.polar ρ R k) R := hPL ▸ heL
    rw [← hWZ]
    exact he.2 g hg
  have hstab : ∀ g ∈ R, ∀ v ∈ singSeq Φ ρ R k, ρ g v ∈ singSeq Φ ρ R k := fun g hg v hv =>
    apply_mem_singSeq hQ R k (Subgroup.le_normalizer hg) hv
  have htriv := sub_mem_of_singular_fixed hQ hZs hZ hstab heperp heZ (hLs e heL) hefix
  have hle : Φ.polar.perp (singSeq Φ ρ R k) ≤ singSeq Φ ρ R (k + 1) := by
    intro w hw
    rw [← hPL]
    refine ⟨?_, fun g hg => ?_⟩
    · rw [hWZ]
      exact hw
    · rw [hWZ]
      exact htriv g hg w hw
  have h1 := Submodule.finrank_mono hle
  have h2 := Φ.polar.finrank_perp (singSeq Φ ρ R k)
  omega

end GGOppRadOmega

end CFSG.StandardType
