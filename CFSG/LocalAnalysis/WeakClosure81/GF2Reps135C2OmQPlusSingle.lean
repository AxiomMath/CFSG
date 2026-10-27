module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusLabel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQLabelPow
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

private theorem c2slomqsi_spinMatrix_apply {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    [DecidableEq σ] {Q : QuadraticForm K (σ → K)} (x : spinGroup Q) (a b : σ) :
    (spinMatrix Q x : Matrix σ σ K) a b = spinAction Q x (Pi.single b 1) a := by
  rw [coe_spinMatrix, LinearMap.toMatrix'_apply]
  rfl

private theorem c2slomqsi_t0_torusD {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    (i : Fin n) (a : Fˣ) {m : Fin n} (hm : m.val = 0) :
    (spinMatrix (quadPlus n F) (torusD F hn i a) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl m) (Sum.inl m) =
      ((a ^ longCoroot (rootIdxD n i) (rootIdxD' n i) true (rootSignD n i) m true : Fˣ) : F) := by
  rw [c2slomqsi_spinMatrix_apply, ← plusVec_true, spinAction_torusD]
  simp

private theorem c2slomqsi_spinAction_torusD_e0 {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    (i : Fin n) (a : Fˣ) {m : Fin n} (hm : m.val = 0) :
    spinAction (quadPlus n F) (torusD F hn i a) (plusVec n F m true) =
      ((spinMatrix (quadPlus n F) (torusD F hn i a) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl m) (Sum.inl m)) •
        plusVec n F m true := by
  rw [c2slomqsi_t0_torusD hn i a hm, spinAction_torusD]

private theorem c2slomqsi_t0_apply {n : ℕ} {F : Type} [Field F]
    (h : spinGroup (quadPlus n F)) {m : Fin n} (hm : m.val = 0) :
    (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl m) (Sum.inl m) =
      spinAction (quadPlus n F) h (plusVec n F m true) (Sum.inl m) := by
  rw [c2slomqsi_spinMatrix_apply, ← plusVec_true]

private theorem c2slomqsi_longCoroot_self {n : ℕ} (hn : 3 ≤ n) {m : Fin n}
    (hm : m.val = 0) :
    longCoroot (rootIdxD n m) (rootIdxD' n m) true (rootSignD n m) m true = 1 := by
  have h1 : m.val + 1 < n := by omega
  rw [rootIdxD_of_lt n h1, rootIdxD'_of_lt n h1, rootSignD_of_lt n h1]
  have hne : m ≠ (⟨m.val + 1, h1⟩ : Fin n) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  simp [longCoroot, hne]

private theorem c2slomqsi_longCoroot_ne {n : ℕ} (hn : 3 ≤ n) {m i : Fin n}
    (hm : m.val = 0) (hi : i ≠ m) :
    longCoroot (rootIdxD n i) (rootIdxD' n i) true (rootSignD n i) m true = 0 := by
  have hri : (rootIdxD n i).val ≠ 0 := by
    by_cases h : i.val + 1 < n
    · rw [rootIdxD_of_lt n h]
      intro h0
      exact hi (Fin.ext (by rw [h0, hm]))
    · rw [val_rootIdxD_of_not_lt n h]
      omega
  have hrj : (rootIdxD' n i).val ≠ 0 := by
    by_cases h : i.val + 1 < n
    · rw [rootIdxD'_of_lt n h]
      simp only [Fin.val_mk]
      omega
    · rw [val_rootIdxD'_of_not_lt n h]
      omega
  have hmi : m ≠ rootIdxD n i := by
    intro h
    have hv := congrArg Fin.val h
    rw [hm] at hv
    exact hri hv.symm
  have hmj : m ≠ rootIdxD' n i := by
    intro h
    have hv := congrArg Fin.val h
    rw [hm] at hv
    exact hrj hv.symm
  simp [longCoroot, hmi, hmj]

private theorem c2slomqsi_torusD_mem_H {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] (i : Fin n) (a : Fˣ) :
    torusD F hn i a ∈ (omPlusCurtisDatum n F hn).H := by
  rw [omPlusCurtisDatum_H hn]
  exact le_iSup (fun j => (torusD F hn j).range) i (MonoidHom.mem_range.mpr ⟨a, rfl⟩)

private theorem c2slomqsi_exists_pow_of_units_hom {F : Type} [Field F] [Finite F]
    {k : Type*} [Field k] (ι : F →+* k) (θ : Fˣ →* k) :
    ∃ c : ℕ, c < Nat.card Fˣ ∧ ∀ a : Fˣ, θ a = ι (a : F) ^ c := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have horder_g : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hinj : Function.Injective ι := RingHom.injective ι
  let φ : Fˣ →* k := ι.toMonoidHom.comp (Units.coeHom F)
  have hφ : Function.Injective φ := fun a b hab => Units.ext (hinj hab)
  have horder_ig : orderOf (ι (g : F)) = Nat.card Fˣ := by
    have h := orderOf_injective φ hφ g
    rw [horder_g] at h
    exact h
  have hprim : IsPrimitiveRoot (ι (g : F)) (Nat.card Fˣ) :=
    { pow_eq_one := by rw [← horder_ig]; exact pow_orderOf_eq_one _
      dvd_of_pow_eq_one := fun l hl => by
        rw [← horder_ig]
        exact orderOf_dvd_iff_pow_eq_one.mpr hl }
  have hzN : (θ g) ^ Nat.card Fˣ = 1 := by
    rw [← map_pow, ← horder_g, pow_orderOf_eq_one, map_one]
  obtain ⟨c, hc, hcz⟩ := hprim.eq_pow_of_pow_eq_one hzN
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨j, rfl⟩ :=
    (Submonoid.mem_powers_iff a g).mp ((mem_powers_iff_mem_zpowers).mpr (hg a))
  have hcoe : ((g ^ j : Fˣ) : F) = (g : F) ^ j := map_pow (Units.coeHom F) g j
  calc θ (g ^ j) = (θ g) ^ j := map_pow θ g j
    _ = ((ι (g : F)) ^ c) ^ j := by rw [hcz]
    _ = (ι (g : F)) ^ (c * j) := by rw [pow_mul]
    _ = (ι (g : F)) ^ (j * c) := by rw [mul_comm c j]
    _ = ((ι (g : F)) ^ j) ^ c := by rw [pow_mul]
    _ = (ι (((g ^ j : Fˣ) : F))) ^ c := by
          congr 1
          rw [hcoe, map_pow]

private theorem c2slomqsi_d'Scalar_eq_dScalar {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] {k : Type*} [Field k] (χ : spinGroup (quadPlus n F) → k)
    (i : Fin n) :
    (omPlusCurtisDatum n F hn).d'Scalar χ i = (omPlusCurtisDatum n F hn).dScalar χ i :=
  CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
    (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum hn) (plusDatum_steinbergExtras hn)
    (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn) 2
    (fun _ hγ => isPGroup_plusRootGroup n F hn hγ) χ i

theorem omq_omPlus_label_of_single {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {k : Type*} [Field k] [CharP k 2] (ι : F →+* k) {V : Type*} [AddCommGroup V]
    [Module k V] {σ : Representation k (spinGroup (quadPlus n F)) V} {y : V}
    {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ)
    (hJ : ∀ i : Fin n, μ i = (omPlusCurtisDatum n F hn).dScalar χ i ↔ i.val = 0) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ Nat.card Fˣ ∧
      (∀ h ∈ (omPlusCurtisDatum n F hn).H,
        χ h = ι ((spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) ^ c) ∧
      (c = Nat.card Fˣ → μ ⟨0, by omega⟩ = 1) ∧ (c < Nat.card Fˣ → μ ⟨0, by omega⟩ = 0) := by
  classical
  let m : Fin n := ⟨0, by omega⟩
  have hm : m.val = 0 := rfl
  let t0 : spinGroup (quadPlus n F) → F := fun h =>
    (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Sum.inl m) (Sum.inl m)
  have ht01 : t0 1 = 1 := by
    show (spinMatrix (quadPlus n F) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl m) (Sum.inl m) = 1
    rw [map_one]
    simp
  have hχmul : ∀ a ∈ (omPlusCurtisDatum n F hn).H, ∀ b ∈ (omPlusCurtisDatum n F hn).H,
      χ (a * b) = χ a * χ b := fun a ha b hb => ht.chi_mul ha hb
  have htriv : ∀ (i : Fin n), i.val ≠ 0 → ∀ a : Fˣ, χ (torusD F hn i a) = 1 := by
    intro i hi a
    by_contra hne
    have hne' : μ i ≠ (omPlusCurtisDatum n F hn).dScalar χ i := fun h => hi ((hJ i).mp h)
    have hμ0 : μ i = 0 := by
      rcases ht.mu_eq i with h | h
      · exact h
      · exact absurd (h.trans (c2slomqsi_d'Scalar_eq_dScalar hn χ i)) hne'
    have hdne : (omPlusCurtisDatum n F hn).dScalar χ i ≠ 0 := by
      intro h0
      exact hne' (by rw [hμ0, h0])
    exact absurd (omq_omPlus_dScalar_eq_zero hn χ hχmul ht.chi_one i ⟨a, hne⟩) hdne
  have hpow_card : ∀ a : Fˣ, ι (a : F) ^ Nat.card Fˣ = 1 := by
    intro a
    let φ : Fˣ →* k := ι.toMonoidHom.comp (Units.coeHom F)
    have hφ : Function.Injective φ := fun x y hxy => Units.ext (RingHom.injective ι hxy)
    have hord : orderOf (ι (a : F)) = orderOf a := orderOf_injective φ hφ a
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact orderOf_dvd_natCard a
  let θ : Fˣ →* k :=
    { toFun := fun a => χ (torusD F hn m a)
      map_one' := by
        show χ (torusD F hn m 1) = 1
        rw [map_one]
        exact ht.chi_one
      map_mul' := by
        intro a b
        show χ (torusD F hn m (a * b)) = χ (torusD F hn m a) * χ (torusD F hn m b)
        rw [map_mul]
        exact ht.chi_mul (c2slomqsi_torusD_mem_H hn m a)
          (c2slomqsi_torusD_mem_H hn m b) }
  obtain ⟨c₀, hc₀lt, hc₀val⟩ := c2slomqsi_exists_pow_of_units_hom ι θ
  have formula : ∀ (c : ℕ), (∀ (i : Fin n) (a : Fˣ),
        χ (torusD F hn i a) = ι (t0 (torusD F hn i a)) ^ c) →
      ∀ h ∈ (omPlusCurtisDatum n F hn).H, χ h = ι (t0 h) ^ c := by
    intro c hgen
    let C : spinGroup (quadPlus n F) → Prop := fun g =>
      g ∈ (omPlusCurtisDatum n F hn).H ∧
      spinAction (quadPlus n F) g (plusVec n F m true) = t0 g • plusVec n F m true ∧
      χ g = ι (t0 g) ^ c
    have key : ∀ g ∈ (omPlusCurtisDatum n F hn).H, C g := by
      intro g hg
      rw [omPlusCurtisDatum_H hn] at hg
      refine Subgroup.iSup_induction (fun i => (torusD F hn i).range) (C := C) hg ?_ ?_ ?_
      · intro i x hx
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
        refine ⟨c2slomqsi_torusD_mem_H hn i a, ?_, hgen i a⟩
        show spinAction (quadPlus n F) (torusD F hn i a) (plusVec n F m true) =
          ((spinMatrix (quadPlus n F) (torusD F hn i a) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl m) (Sum.inl m)) •
            plusVec n F m true
        exact c2slomqsi_spinAction_torusD_e0 hn i a hm
      · exact ⟨one_mem _, by rw [ht01]; simp,
          by rw [ht01, ht.chi_one, map_one, one_pow]⟩
      · intro x y hx hy
        have h1 : spinAction (quadPlus n F) (x * y) (plusVec n F m true) =
            (t0 y * t0 x) • plusVec n F m true := by
          rw [map_mul, LinearEquiv.mul_apply, hy.2.1, map_smul, hx.2.1, smul_smul]
        have ht0xy : t0 (x * y) = t0 y * t0 x := by
          rw [show t0 (x * y) =
            spinAction (quadPlus n F) (x * y) (plusVec n F m true) (Sum.inl m)
            from c2slomqsi_t0_apply (x * y) hm, h1]
          simp
        refine ⟨mul_mem hx.1 hy.1, ?_, ?_⟩
        · rw [ht0xy, h1]
        · rw [ht.chi_mul hx.1 hy.1, hx.2.2, hy.2.2, ← mul_pow, ← map_mul,
            show t0 x * t0 y = t0 (x * y) from by rw [mul_comm, ← ht0xy]]
    intro h hh
    exact (key h hh).2.2
  have hcard_pos : 1 ≤ Nat.card Fˣ := by
    haveI : Nonempty Fˣ := ⟨1⟩
    exact Nat.succ_le_of_lt Nat.card_pos
  by_cases hc₀ : c₀ = 0
  · refine ⟨Nat.card Fˣ, hcard_pos, le_rfl, ?_, ?_, ?_⟩
    · refine formula (Nat.card Fˣ) ?_
      intro i a
      by_cases hi : i = m
      · rw [hi]
        have ht0 : t0 (torusD F hn m a) = (a : F) := by
          rw [show t0 (torusD F hn m a) =
            ((a ^ longCoroot (rootIdxD n m) (rootIdxD' n m) true (rootSignD n m) m true : Fˣ)
              : F) from c2slomqsi_t0_torusD hn m a hm,
            c2slomqsi_longCoroot_self hn hm, zpow_one]
        have hchi : χ (torusD F hn m a) = 1 := by simpa [hc₀, θ] using hc₀val a
        rw [hchi, ht0]
        exact (hpow_card a).symm
      · have hival : i.val ≠ 0 := fun h => hi (Fin.ext (by rw [h, hm]))
        have ht0 : t0 (torusD F hn i a) = 1 := by
          rw [show t0 (torusD F hn i a) =
            ((a ^ longCoroot (rootIdxD n i) (rootIdxD' n i) true (rootSignD n i) m true : Fˣ)
              : F) from c2slomqsi_t0_torusD hn i a hm,
            c2slomqsi_longCoroot_ne hn hm hi, zpow_zero]
          rfl
        rw [htriv i hival a, ht0, map_one, one_pow]
    · intro _
      have hμ : μ m = (omPlusCurtisDatum n F hn).dScalar χ m := (hJ m).mpr hm
      rw [hμ]
      exact omq_omPlus_dScalar_eq_one hn χ m (fun a => by simpa [hc₀, θ] using hc₀val a)
    · intro hc
      exact absurd hc (lt_irrefl _)
  · have hc₀pos : 0 < c₀ := Nat.pos_of_ne_zero hc₀
    have hgen0 : ∃ a : Fˣ, χ (torusD F hn m a) ≠ 1 := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
      have horder_g : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
      let φ : Fˣ →* k := ι.toMonoidHom.comp (Units.coeHom F)
      have hφ : Function.Injective φ := fun x y hxy => Units.ext (RingHom.injective ι hxy)
      have horder_ig : orderOf (ι (g : F)) = Nat.card Fˣ := by
        have h := orderOf_injective φ hφ g
        rw [horder_g] at h
        exact h
      refine ⟨g, ?_⟩
      change θ g ≠ 1
      rw [hc₀val g]
      intro h
      have hdvd : orderOf (ι (g : F)) ∣ c₀ := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [horder_ig] at hdvd
      exact Nat.not_dvd_of_pos_of_lt hc₀pos hc₀lt hdvd
    refine ⟨c₀, hc₀pos, hc₀lt.le, ?_, ?_, ?_⟩
    · refine formula c₀ ?_
      intro i a
      by_cases hi : i = m
      · rw [hi]
        have ht0 : t0 (torusD F hn m a) = (a : F) := by
          rw [show t0 (torusD F hn m a) =
            ((a ^ longCoroot (rootIdxD n m) (rootIdxD' n m) true (rootSignD n m) m true : Fˣ)
              : F) from c2slomqsi_t0_torusD hn m a hm,
            c2slomqsi_longCoroot_self hn hm, zpow_one]
        have hchi : χ (torusD F hn m a) = ι (a : F) ^ c₀ := by simpa [θ] using hc₀val a
        rw [hchi, ht0]
      · have hival : i.val ≠ 0 := fun h => hi (Fin.ext (by rw [h, hm]))
        have ht0 : t0 (torusD F hn i a) = 1 := by
          rw [show t0 (torusD F hn i a) =
            ((a ^ longCoroot (rootIdxD n i) (rootIdxD' n i) true (rootSignD n i) m true : Fˣ)
              : F) from c2slomqsi_t0_torusD hn i a hm,
            c2slomqsi_longCoroot_ne hn hm hi, zpow_zero]
          rfl
        rw [htriv i hival a, ht0, map_one, one_pow]
    · intro hc
      exact absurd hc (ne_of_lt hc₀lt)
    · intro _
      have hμ : μ m = (omPlusCurtisDatum n F hn).dScalar χ m := (hJ m).mpr hm
      rw [hμ]
      exact omq_omPlus_dScalar_eq_zero hn χ hχmul ht.chi_one m hgen0

end CFSG.LocalAnalysis.WeakClosure81
