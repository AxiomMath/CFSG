module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcG2Three
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstar
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvFin
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative

private theorem smul_eq_neg_of_isRoot_of_neg
    {τ : Tag}
    {w : WeylGroup τ} (hneg : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → w • γ = -γ)
    (v : Fin τ.rank → ℤ) : w • v = -v := by
  have hsingle : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 :=
    fun i => hneg _ (isRoot_single τ i)
  have h : CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def, hsingle i]
    simp
  have hv := congrArg (fun f : Module.End ℤ (Fin τ.rank → ℤ) => f v) h
  simpa [smul_def] using hv

@[expose] noncomputable def phiTwoLangHom
    {τ : Tag} {K : Type} [Field K] {n : ℕ} [NeZero n]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ n = 1)
    (g0 : ModGL τ (AlgebraicClosure K)) :
    Multiplicative (Fin τ.rank → ZMod n) →* ModGL τ (AlgebraicClosure K) where
  toFun t := g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹
  map_one' := by
    change g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ
      (0 : Fin τ.rank → ZMod n)) * g0⁻¹ = 1
    have h0 : TableBExc.E6Three.zetaVec ζ hζ (0 : Fin τ.rank → ZMod n) = 1 := by
      funext i
      simpa [TableBExc.E6Three.zetaVec]
    rw [h0, rootDiagUnit_one]
    group
  map_mul' x y := by
    change g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ (x.toAdd + y.toAdd)) *
        g0⁻¹ =
      (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ x.toAdd) * g0⁻¹) *
        (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ y.toAdd) * g0⁻¹)
    rw [ExcFrames.zetaVec_add, rootDiagUnit_mul]
    group

theorem exists_torus_param_of_full_image
    {tau : Tag} {K H : Type} [Field K] [Group H] {n : ℕ} [NeZero n]
    (E : Subgroup H) (iota : H →* ModGL tau (AlgebraicClosure K))
    (hinj : Function.Injective iota)
    (hwhole : ∀ z : ModGL tau (AlgebraicClosure K),
      (∃ u : H, u ∈ E ∧ iota u = z) ↔
      ∃ b : Fin tau.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ n = 1) ∧ rootDiagUnit tau b = z)
    (zeta : (AlgebraicClosure K)ˣ) (hzo : orderOf zeta = n) (hz : zeta ^ n = 1) :
    ∃ T : Multiplicative (Fin tau.rank → ZMod n) →* H,
      Function.Injective T ∧ T.range = E ∧ ∀ t : Fin tau.rank → ZMod n,
        iota (T (ofAdd t)) = rootDiagUnit tau (TableBExc.E6Three.zetaVec zeta hz t) := by
  let C := phiTwoLangHom (τ := tau) hz (1 : ModGL tau (AlgebraicClosure K))
  have hC : ∀ t, C t = rootDiagUnit tau (TableBExc.E6Three.zetaVec zeta hz t.toAdd) := by
    intro t
    simp [C, phiTwoLangHom]
  have hpow : ∀ (t : Fin tau.rank → ZMod n) (j : Fin tau.rank),
      (TableBExc.E6Three.zetaVec (τ := tau) zeta hz t) j ^ n = 1 := by
    intro t j
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have hCrange : C.range ≤ iota.range := by
    rintro z ⟨t, rfl⟩
    obtain ⟨u, -, hu⟩ := (hwhole (C t)).mpr
      ⟨TableBExc.E6Three.zetaVec zeta hz t.toAdd, hpow t.toAdd, (hC t).symm⟩
    exact ⟨u, hu⟩
  let e := MonoidHom.ofInjective hinj
  let T : Multiplicative (Fin tau.rank → ZMod n) →* H :=
    e.symm.toMonoidHom.comp (C.codRestrict iota.range (fun t => hCrange ⟨t, rfl⟩))
  have hT : ∀ t, iota (T t) = C t := fun t =>
    MonoidHom.apply_ofInjective_symm hinj
      ((C.codRestrict iota.range (fun t => hCrange ⟨t, rfl⟩)) t)
  have hTrange : T.range = E := by
    apply le_antisymm
    · rintro u ⟨t, rfl⟩
      obtain ⟨u, hu, he⟩ := (hwhole (C t)).mpr
        ⟨TableBExc.E6Three.zetaVec zeta hz t.toAdd, hpow t.toAdd, (hC t).symm⟩
      have hh : T t = u := hinj ((hT t).trans he.symm)
      exact hh.symm ▸ hu
    · intro u hu
      obtain ⟨b, hb, he⟩ := (hwhole (iota u)).mp ⟨u, hu, rfl⟩
      obtain ⟨t, ht⟩ := TableBExc.E6Three.exists_zetaVec_eq hzo hz (funext hb)
      refine ⟨ofAdd t, ?_⟩
      apply hinj
      rw [hT, hC]
      change rootDiagUnit tau (TableBExc.E6Three.zetaVec zeta hz t) = _
      rw [ht]
      exact he
  refine ⟨T, ?_, hTrange, ?_⟩
  · intro t u he
    have hh : C t = C u := (hT t).symm.trans ((congrArg iota he).trans (hT u))
    rw [hC, hC] at hh
    exact Multiplicative.ext
      (TableBExc.E6Three.zetaVec_injective hzo hz (rootDiagUnit_injective hh))
  · intro t
    exact (hT (ofAdd t)).trans (hC (ofAdd t))

private theorem frobenius_rootDiagUnit_zetaVec
    {τ : Tag} {K : Type} [Field K] {n : ℕ} [NeZero n]
    (hn : n ∣ Nat.card K + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ n = 1) (t : Fin τ.rank → ZMod n) :
    Units.map (entrywiseHom Fr) (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t)) =
      (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t))⁻¹ := by
  have hq : (((Nat.card K : ℤ)) : ZMod n) = -1 := by
    have h1 : (((Nat.card K : ℤ)) : ZMod n) + 1 = 0 := by
      rw [← Int.cast_one, ← Int.cast_add]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Nat.card K + 1 : ℤ) n).2 (by exact_mod_cast hn)
    exact add_eq_zero_iff_eq_neg.mp h1
  have hmap : ∀ u : (AlgebraicClosure K)ˣ, Units.map Fr.toMonoidHom u = u ^ Nat.card K := by
    intro u
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hFr (u : AlgebraicClosure K)
  refine Units.ext ?_
  show entrywise Fr (rootDiag (TableBExc.E6Three.zetaVec ζ hζ t)) =
    rootDiag ((TableBExc.E6Three.zetaVec ζ hζ t)⁻¹)
  rw [entrywise_rootDiag]
  congr 1
  funext i
  rw [hmap, Pi.inv_apply]
  rw [TableBExc.E6Three.zetaVec, ← zpow_natCast (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
    (.ofAdd (t i))) (Nat.card K), TableBExc.E6Three.zmodPowHom_zpow, hq, neg_one_mul,
    ofAdd_neg, map_inv]

private theorem frobenius_phiTwoLangHom
    {τ : Tag} {K : Type} [Field K] {n : ℕ} [NeZero n]
    (hn : n ∣ Nat.card K + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} (hneg : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → w • γ = -γ)
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ n = 1)
    (t : Multiplicative (Fin τ.rank → ZMod n)) :
    Units.map (entrywiseHom Fr) (phiTwoLangHom hζ g0 t) = phiTwoLangHom hζ g0 t := by
  have hd : Units.map (entrywiseHom Fr) (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ
      t.toAdd)) = (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd))⁻¹ :=
    frobenius_rootDiagUnit_zetaVec hn hFr hζ t.toAdd
  have hconj : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
      rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
      (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd))⁻¹ :=
    CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane.canonicalRep_conj_rootDiagUnit_of_neg
      (K := AlgebraicClosure K) (smul_eq_neg_of_isRoot_of_neg hneg) _
  change Units.map (entrywiseHom Fr)
    (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹) =
    g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹
  rw [map_mul, map_mul, map_inv, hg0, hd]
  calc
    (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) *
        (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd))⁻¹ *
          (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
      g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd))⁻¹ *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ := by group
    _ = g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹)⁻¹ * g0⁻¹ := by group
    _ = g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹ := by
          rw [hconj, inv_inv]

theorem exists_phiTwoTorus_of_neg
    {τ : Tag} {K : Type} [Field K] [Finite K] {n : ℕ} [NeZero n] (hn : n ∣ Nat.card K + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} (hneg : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → w • γ = -γ)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = n) (hζ : ζ ^ n = 1) :
    ∃ T : Multiplicative (Fin τ.rank → ZMod n) →* adjointGroup τ K,
      Function.Injective T ∧ ∀ t : Fin τ.rank → ZMod n,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
          g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹ := by
  classical
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let φ : Multiplicative (Fin τ.rank → ZMod n) →* ModGL τ (AlgebraicClosure K) :=
    phiTwoLangHom hζ g0
  have hfix : ∀ x ∈ φ.range, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨t, rfl⟩
    exact frobenius_phiTwoLangHom hn hFr hneg hg0 hζ t
  have hle : φ.range ≤ adjointGroup τ (AlgebraicClosure K) := by
    rintro _ ⟨t, rfl⟩
    have ht : φ t = g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) *
        g0⁻¹ := rfl
    rw [ht]
    exact mul_mem (mul_mem hg0C (ExcFrames.rootDiagUnit_mem_adjointGroup _)) (inv_mem hg0C)
  have hrange : φ.range ≤ (adjointGroup τ K).map (baseChangeGL ι) :=
    hrat φ.range (by infer_instance) hle hfix
  let B : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hBrange : B.range = (adjointGroup τ K).map (baseChangeGL ι) := by
    show ((baseChangeGL ι).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hrangeB : φ.range ≤ B.range := by rwa [hBrange]
  have hBinj : Function.Injective B := by
    intro a b hab
    refine Subtype.ext (baseChangeGL_injective (f := ι) ?_)
    simpa [B] using hab
  let e : adjointGroup τ K ≃* B.range := MonoidHom.ofInjective hBinj
  let T : Multiplicative (Fin τ.rank → ZMod n) →* adjointGroup τ K :=
    e.symm.toMonoidHom.comp (φ.codRestrict B.range fun t => hrangeB ⟨t, rfl⟩)
  have hTval : ∀ t : Multiplicative (Fin τ.rank → ZMod n),
      baseChangeGL ι ((T t : adjointGroup τ K) : ModGL τ K) = φ t := by
    intro t
    change B (T t) = φ t
    exact MonoidHom.apply_ofInjective_symm hBinj
      ((φ.codRestrict B.range fun t => hrangeB ⟨t, rfl⟩) t)
  refine ⟨T, ?_, ?_⟩
  · intro a b hab
    have hφ : φ a = φ b := by rw [← hTval a, ← hTval b, hab]
    have hd : rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) =
        rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) := by
      have h := congrArg (fun x : ModGL τ (AlgebraicClosure K) => g0⁻¹ * x * g0) hφ
      have ha : φ a = g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) *
          g0⁻¹ := rfl
      have hb : φ b = g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) *
          g0⁻¹ := rfl
      rw [ha, hb] at h
      calc
        rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) =
            g0⁻¹ * (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) *
              g0⁻¹) * g0 := by group
        _ = g0⁻¹ * (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) *
              g0⁻¹) * g0 := h
        _ = rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) := by group
    have hz : TableBExc.E6Three.zetaVec ζ hζ a.toAdd =
        TableBExc.E6Three.zetaVec ζ hζ b.toAdd :=
      CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' hd
    exact Multiplicative.ext (TableBExc.E6Three.zetaVec_injective hζo hζ hz)
  · intro t
    rw [hTval]
    rfl

private theorem zetaVec_single
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    {ζ : Lˣ} (hζ : ζ ^ p = 1) (j : Fin τ.rank) :
    TableBExc.E6Three.zetaVec ζ hζ (Pi.single j (1 : ZMod p)) = Pi.mulSingle j ζ := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  funext i
  rw [TableBExc.E6Three.zetaVec_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, ZMod.val_one, pow_one, Pi.mulSingle_eq_same]
  · rw [Pi.single_eq_of_ne h, ZMod.val_zero, pow_zero, Pi.mulSingle_eq_of_ne h]

private theorem not_isUnit_prime_intCast {p : ℕ} (hp : p.Prime) : ¬ IsUnit (p : ℤ) := by
  rw [Int.isUnit_iff_abs_eq]
  have hp1 : ((p : ℕ) : ℤ) ≠ 1 := by
    intro h
    exact hp.ne_one (by exact_mod_cast h)
  simpa using hp1

theorem mem_torusGroup_of_forall_commute_zetaVec
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {y : ModGL τ L}
    (hy : y ∈ adjointGroup τ L)
    (hc : ∀ t : Fin τ.rank → ZMod p,
      y * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) =
        rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * y) :
    y ∈ torusGroup τ L := by
  classical
  let a : (Fin τ.rank → ZMod p) → Fin τ.rank → Lˣ :=
    TableBExc.E6Three.zetaVec ζ hζ
  have hfam : y ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ L a := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
    refine ⟨hy, fun t => ?_⟩
    rw [← hc t, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨w, hw, m, hm, hrm⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_mul τ L a hfam
  have hw1 : w = 1 := by
    refine ExcSplitL.eq_one_of_mem_rootCharStabilizer hp2 hζo fun j => ?_
    have h := hw (Pi.single j (1 : ZMod p))
    dsimp only [a] at h
    rwa [zetaVec_single hζ j] at h
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun α hα => ?_
    obtain ⟨hαroot, hαtriv⟩ := hα
    have hnot : ¬ ∀ j, (p : ℤ) ∣ α j :=
      CFSG.HardMathSupport.C14G2Three.not_forall_dvd_of_isRoot hαroot
        (not_isUnit_prime_intCast (Fact.out : p.Prime))
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have h1 := hαtriv (Pi.single j (1 : ZMod p))
    dsimp only [a] at h1
    rw [zetaVec_single hζ j, ExcSplitL.rootChar_mulSingle] at h1
    have h2 : (p : ℤ) ∣ α j := by
      rw [← hζo]
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    exact hj h2
  have hmT : m ∈ torusGroup τ L := by
    have hm' : m ∈ torusGroup τ L ⊔
        rootSpan τ L (CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a) := hm
    rw [hker] at hm'
    have hbot : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hrm, hw1, canonicalRep_one, mul_one]
  exact hmT

private noncomputable def conjAdjointBaseChange
    {τ : Tag} {K : Type} [Field K]
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)) :
    adjointGroup τ K →* adjointGroup τ (AlgebraicClosure K) where
  toFun x := ⟨g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0,
    mul_mem (mul_mem (inv_mem hg0C)
      (CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup _ x.2)) hg0C⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mul, map_mul]
    group

private theorem coe_conjAdjointBaseChange
    {τ : Tag} {K : Type} [Field K]
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (x : adjointGroup τ K) :
    ((conjAdjointBaseChange hg0C x : adjointGroup τ (AlgebraicClosure K)) : ModGL τ
        (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 := rfl

private theorem zetaVec_pow_eq_one
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (t : Fin τ.rank → ZMod p) :
    TableBExc.E6Three.zetaVec ζ hζ t ^ p = 1 := by
  funext i
  show (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
    (Multiplicative.ofAdd (t i))) ^ p = 1
  rw [← zpow_natCast (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
    (Multiplicative.ofAdd (t i))) p, TableBExc.E6Three.zmodPowHom_zpow,
    show ((p : ℤ) : ZMod p) = 0 by rw [Int.cast_natCast, ZMod.natCast_self],
    zero_mul, ofAdd_zero, map_one]

private theorem map_conjAdjointBaseChange_le_famCentralizer
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {V : Set (Fin τ.rank → ZMod p)} {P : Subgroup (adjointGroup τ K)}
    (hP : ∀ x ∈ P, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x) :
    P.map (conjAdjointBaseChange hg0C) ≤
      LayerSixE.famCentralizer (TableBExc.E6Three.zetaVec ζ hζ '' V) := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rintro _ ⟨x, hx, rfl⟩
  rw [LayerSixE.mem_famCentralizer]
  rintro a ⟨t, ht, rfl⟩
  change rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) *
      (g0⁻¹ * baseChangeGL ι (x : ModGL τ K) * g0) *
        (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t))⁻¹ =
    g0⁻¹ * baseChangeGL ι (x : ModGL τ K) * g0
  have hbase := congrArg (fun z : adjointGroup τ K =>
    baseChangeGL ι (z : ModGL τ K)) (hP x hx t ht)
  simp only [Subgroup.coe_mul, map_mul] at hbase
  rw [hT t] at hbase
  have hcomm : (g0⁻¹ * baseChangeGL ι (x : ModGL τ K) * g0) *
      rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) =
      rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) *
        (g0⁻¹ * baseChangeGL ι (x : ModGL τ K) * g0) := by
    calc
      (g0⁻¹ * baseChangeGL ι (x : ModGL τ K) * g0) *
          rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) =
          g0⁻¹ * (baseChangeGL ι (x : ModGL τ K) *
            (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)) * g0 := by
            group
      _ = g0⁻¹ * ((g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹) *
            baseChangeGL ι (x : ModGL τ K)) * g0 := by rw [hbase]
      _ = rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) *
            (g0⁻¹ * baseChangeGL ι (x : ModGL τ K) * g0) := by group
  rw [← hcomm]
  group

private theorem perfect_le_rootSpan_famKernel
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    (F : Set (Fin τ.rank → Lˣ)) (hFfin : F.Finite)
    (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    {Q : Subgroup (ModGL τ L)}
    (hQ : Q ≤ (LayerSixE.famCentralizer F).map (adjointGroup τ L).subtype)
    (hQperf : ⁅Q, Q⁆ = Q) :
    Q ≤ rootSpan τ L (CFSG.RankThree.PartOne.KE8F.famKernel F) := by
  classical
  obtain ⟨k, hk⟩ :=
    LayerExc.exists_ggDer_famStabilizerSubgroup_le_reflection_of_finite
      (Fact.out : p.Prime) F hFfin hF
  let X : Subgroup (ModGL τ L) := (LayerSixE.famCentralizer F).map (adjointGroup τ L).subtype
  let U : Subgroup (ModGL τ L) := rootSpan τ L (CFSG.RankThree.PartOne.KE8F.famKernel F)
  let M : Subgroup (ModGL τ L) := torusGroup τ L ⊔ U
  have hMle : X ≤ M ⊔ (LayerExc.famWeylReps (K := L) F).map
      (monomialSubgroup τ L).subtype :=
    LayerSixE.map_famCentralizer_le_sup (K := L) F
  have hYN : (LayerExc.famWeylReps (K := L) F).map (monomialSubgroup τ L).subtype ≤
      Subgroup.normalizer (M : Set (ModGL τ L)) :=
    LayerExc.map_famWeylReps_le_normalizer (K := L) F
  have hder : LayerFacts.ggDer X (k + 1) ≤ U := by
    rw [LayerFacts.ggDer_succ]
    have h1 := (LayerFacts.ggDer_mono hMle k).trans
      ((LayerExc.ggDer_sup_le_of_le_normalizer hYN k).trans
        (sup_le le_rfl (LayerExc.ggDer_map_famWeylReps_le (K := L) hk)))
    exact (Subgroup.commutator_mono h1 h1).trans
      (LayerExc.commutator_torus_sup_rootSpan_le (K := L)
        (S := CFSG.RankThree.PartOne.KE8F.famKernel F) (fun α hα => hα.1))
  have hPder : LayerFacts.ggDer Q (k + 1) = Q := LayerFacts.ggDer_of_perfect hQperf (k + 1)
  have hmono : LayerFacts.ggDer Q (k + 1) ≤ LayerFacts.ggDer X (k + 1) :=
    LayerFacts.ggDer_mono hQ (k + 1)
  rw [hPder] at hmono
  exact hmono.trans hder

private theorem famKernel_zetaVec_image_subset
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {V : Set (Fin τ.rank → ZMod p)} :
    CFSG.RankThree.PartOne.KE8F.famKernel (TableBExc.E6Three.zetaVec ζ hζ '' V) ⊆
      {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ ∀ t ∈ V, ∑ j, (γ j : ZMod p) * t j = 0} := by
  intro γ hγ
  obtain ⟨hγroot, hγtriv⟩ := hγ
  refine ⟨hγroot, fun t ht => ?_⟩
  have h1 := hγtriv (TableBExc.E6Three.zetaVec ζ hζ t) ⟨t, ht, rfl⟩
  rw [NoOffE8Five.rootChar_zetaVec hζ t γ] at h1
  have h2 : Multiplicative.ofAdd (∑ j, (γ j : ZMod p) * t j) = 1 :=
    CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ (by rw [h1, map_one])
  simpa using congrArg Multiplicative.toAdd h2

theorem conj_mem_rootSpan_of_isPerfect
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {V : Set (Fin τ.rank → ZMod p)} {P : Subgroup (adjointGroup τ K)} (hperf : ⁅P, P⁆ = P)
    (hP : ∀ x ∈ P, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x)
    {x : adjointGroup τ K} (hx : x ∈ P) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 ∈
      rootSpan τ (AlgebraicClosure K)
        {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ ∀ t ∈ V, ∑ j, (γ j : ZMod p) * t j = 0} := by
  classical
  let F : Set (Fin τ.rank → (AlgebraicClosure K)ˣ) :=
    TableBExc.E6Three.zetaVec ζ hζ '' V
  let ψ : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (adjointGroup τ (AlgebraicClosure K)).subtype.comp (conjAdjointBaseChange hg0C)
  have hPC : P.map (conjAdjointBaseChange hg0C) ≤ LayerSixE.famCentralizer F := by
    simpa only [F] using map_conjAdjointBaseChange_le_famCentralizer hg0C hζ hT hP
  have hleψ : P.map ψ ≤ (LayerSixE.famCentralizer F).map
      (adjointGroup τ (AlgebraicClosure K)).subtype := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨conjAdjointBaseChange hg0C p, hPC ⟨p, hp, rfl⟩, rfl⟩
  have hPperf' : ⁅P.map ψ, P.map ψ⁆ = P.map ψ := by
    rw [← Subgroup.map_commutator, hperf]
  have hFfin : F.Finite := by
    have hV : V.Finite := Set.toFinite V
    simpa only [F] using hV.image (TableBExc.E6Three.zetaVec ζ hζ)
  have hFpow : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1 := by
    intro a ha
    dsimp only [F] at ha
    obtain ⟨t, ht, rfl⟩ := ha
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact zetaVec_pow_eq_one hζ t
  have hmem : ψ x ∈ rootSpan τ (AlgebraicClosure K)
      (CFSG.RankThree.PartOne.KE8F.famKernel F) :=
    perfect_le_rootSpan_famKernel F hFfin hFpow hleψ hPperf' ⟨x, hx, rfl⟩
  have hsub : CFSG.RankThree.PartOne.KE8F.famKernel F ⊆
      {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ ∀ t ∈ V, ∑ j, (γ j : ZMod p) * t j = 0} := by
    simpa only [F] using famKernel_zetaVec_image_subset hζo hζ (V := V)
  have hroot := rootSpan_mono hsub hmem
  have hmem' : (conjAdjointBaseChange hg0C x : ModGL τ (AlgebraicClosure K)) ∈
      rootSpan τ (AlgebraicClosure K)
        {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ ∀ t ∈ V, ∑ j, (γ j : ZMod p) * t j = 0} := hroot
  rwa [coe_conjAdjointBaseChange] at hmem'

end CFSG.StandardType.PhiTwoRootGen

end
