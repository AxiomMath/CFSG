module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviBruhat

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

private def orbitIdx (i : Fin TwistTag.E6.tag.rank) : Fin Tag.F4.rank :=
  ⟨(TwistTag.E6.orbitIndex i).val, (TwistTag.E6.orbitIndex i).isLt⟩

private abbrev orbitF4 (b : Fin Tag.F4.rank) : Finset (Fin TwistTag.E6.tag.rank) :=
  TwistTag.E6.orbit b

private theorem orbitIdx_eq_iff {i : Fin TwistTag.E6.tag.rank} {b : Fin Tag.F4.rank} :
    orbitIdx i = b ↔ i ∈ orbitF4 b := by
  change orbitIdx i = b ↔ i ∈ TwistTag.E6.orbit b
  exact ⟨fun h => (TwistTag.E6.mem_orbit_iff).mpr (Fin.ext (congrArg Fin.val h)),
    fun h => Fin.ext (congrArg Fin.val ((TwistTag.E6.mem_orbit_iff).mp h))⟩

private theorem twE6SplitTheta_apply {p : ℕ} [NeZero p] (s : Fin Tag.F4.rank → ZMod p)
    (i : Fin TwistTag.E6.tag.rank) :
    ExcFrames.twE6SplitTheta p s i = s (orbitIdx i) := by
  show ((TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s) i : ℤ) : ZMod p) =
    s (orbitIdx i)
  have h := TwistTag.foldMap_apply_apply TwistTag.E6 (TableBExc.liftMod .F4 p s) i
  rw [h]
  show (((s (orbitIdx i)).val : ℤ) : ZMod p) = s (orbitIdx i)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem E6_symmetrizedCartan_eq :
    TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
  rw [Tag.symmetrizedCartan]
  exact one_mul _

private theorem sum_orbitIndex_mul {p : ℕ} (β : Fin TwistTag.E6.tag.rank → ℤ)
    (f : Fin Tag.F4.rank → ZMod p) :
    (∑ j, (β j : ZMod p) * f (orbitIdx j)) =
      ∑ b, ((∑ i ∈ orbitF4 b, β i : ℤ) : ZMod p) * f b := by
  classical
  have hfilter : ∀ b : Fin Tag.F4.rank,
      Finset.univ.filter (fun j : Fin TwistTag.E6.tag.rank => orbitIdx j = b) =
        orbitF4 b := by
    intro b
    ext j
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact orbitIdx_eq_iff
  calc
    (∑ j, (β j : ZMod p) * f (orbitIdx j))
        = ∑ b : Fin Tag.F4.rank, ∑ j ∈ Finset.univ.filter
            (fun j : Fin TwistTag.E6.tag.rank => orbitIdx j = b),
            (β j : ZMod p) * f (orbitIdx j) :=
          (Finset.sum_fiberwise Finset.univ
            (fun j : Fin TwistTag.E6.tag.rank => orbitIdx j)
            (fun j => (β j : ZMod p) * f (orbitIdx j))).symm
    _ = ∑ b : Fin Tag.F4.rank,
          ((∑ i ∈ orbitF4 b, β i : ℤ) : ZMod p) * f b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hfilter b]
          calc
            (∑ j ∈ orbitF4 b, (β j : ZMod p) * f (orbitIdx j))
                = ∑ j ∈ orbitF4 b, (β j : ZMod p) * f b := by
                  refine Finset.sum_congr rfl fun j hj => ?_
                  have h : orbitIdx j = b := orbitIdx_eq_iff.mpr hj
                  rw [h]
            _ = ((∑ j ∈ orbitF4 b, β j : ℤ) : ZMod p) * f b := by
                  rw [← Finset.sum_mul]
                  congr 1
                  push_cast
                  rfl

private theorem orbit_cartan_sum (i : Fin TwistTag.E6.tag.rank) (b : Fin Tag.F4.rank) :
    (∑ j ∈ orbitF4 b, Tag.E6.cartan i j) =
      Tag.F4.cartan (TwistTag.E6.orbitIndex i) b := by
  revert i b
  decide

theorem frameCoord_twE6SplitTheta {p : ℕ} [NeZero p] (s : Fin Tag.F4.rank → ZMod p) :
    ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) =
      ExcFrames.twE6SplitTheta p (fun a => ∑ b, ((Tag.F4.cartan a b : ℤ) : ZMod p) * s b) := by
  funext i
  simp only [ExcFrames.frameCoord, twE6SplitTheta_apply]
  calc
    (∑ j, ((TwistTag.E6.tag.symmetrizedCartan i j : ℤ) : ZMod p) *
        s (orbitIdx j))
        = ∑ j, ((Tag.E6.cartan i j : ℤ) : ZMod p) * s (orbitIdx j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [E6_symmetrizedCartan_eq]
          rfl
    _ = ∑ b, ((∑ k ∈ orbitF4 b, Tag.E6.cartan i k : ℤ) : ZMod p) * s b :=
          sum_orbitIndex_mul (fun k => Tag.E6.cartan i k) s
    _ = ∑ b, ((Tag.F4.cartan (TwistTag.E6.orbitIndex i) b : ℤ) : ZMod p) * s b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          exact congrArg (fun n : ℤ => ((n : ZMod p) * s b)) (orbit_cartan_sum i b)

private abbrev e6Root (k : Fin 72) : Fin TwistTag.E6.tag.rank → ℤ := C2E6Std.e6Root k

private theorem e6Root_orbit_check :
    ∀ (k : Fin 72) (a : Fin Tag.F4.rank),
      (∃ j ∈ orbitF4 a, e6Root k = Pi.single j 1 ∨ e6Root k = -Pi.single j 1) ∨
      ∃ b : Fin Tag.F4.rank, b ≠ a ∧
        (∑ i ∈ orbitF4 b, e6Root k i) ∈
          ({1, -1, 2, -2, 4, -4} : Finset ℤ) := by
  decide

private theorem zmod_int_ne_zero_of_mem {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℤ}
    (hn : n ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ)) : ((n : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hpn : p ∣ n.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hple : p ≤ 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hpn
      norm_num at hle
      omega
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have hple3 : p ≤ 3 := by omega
    interval_cases p
    norm_num at hpn

theorem mem_signedSimpleRoots_of_orbitSum_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) {a : Fin Tag.F4.rank}
    (h : ∀ b : Fin Tag.F4.rank, b ≠ a → ((∑ i ∈ TwistTag.E6.orbit b, β i : ℤ) : ZMod p) = 0) :
    β ∈ signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) := by
  obtain ⟨k, rfl⟩ := C2E6Std.exists_e6Root_eq hβ
  rcases e6Root_orbit_check k a with hin | ⟨b, hb, hn⟩
  · exact hin
  · exact absurd (h b hb) (zmod_int_ne_zero_of_mem hp2 hn)

private abbrev f4CartanMul {p : ℕ} (s : Fin Tag.F4.rank → ZMod p) :
    Fin Tag.F4.rank → ZMod p :=
  fun a => ∑ b, ((Tag.F4.cartan a b : ℤ) : ZMod p) * s b

private theorem f4CartanMul_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (f4CartanMul (p := p)) := by
  have e : f4CartanMul (p := p) =
      (Tag.F4.cartan.map (Int.castRingHom (ZMod p))).mulVec := by
    funext s a
    simp [f4CartanMul, Matrix.mulVec, dotProduct]
  have hd : (Tag.F4.cartan.map (Int.castRingHom (ZMod p))).det =
      ((Tag.F4.cartan.det : ℤ) : ZMod p) := (RingHom.map_det _ _).symm
  rw [e, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hd,
    CFSG.LieType.Chevalley.det_cartan_F4]
  simpa using (isUnit_one : IsUnit (1 : ZMod p))

private theorem f4CartanMul_surjective {p : ℕ} [Fact p.Prime] :
    Function.Surjective (f4CartanMul (p := p)) :=
  Finite.injective_iff_surjective.mp (f4CartanMul_injective (p := p))

private theorem torusAct_simple_eq_self_iff {p : ℕ} [NeZero p] (a : Fin Tag.F4.rank)
    (x : Fin Tag.F4.rank → ZMod p) :
    TableBExc.torusAct .F4 p (simple Tag.F4 a) x = x ↔ f4CartanMul x a = 0 := by
  have h : TableBExc.torusAct .F4 p (simple Tag.F4 a) x =
      x - (∑ j, ((Tag.F4.cartan a j : ℤ) : ZMod p) * x j) • Pi.single a 1 := by
    funext k
    simp only [TableBExc.torusAct, simple_smul, reflect, TableBExc.redMod, TableBExc.liftMod,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [ZMod.natCast_zmod_val, ZMod.cast_id', id_eq]
    congr 2
    by_cases hk : k = a
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [h]
  change (x - (∑ j, ((Tag.F4.cartan a j : ℤ) : ZMod p) * x j) • Pi.single a 1 = x) ↔
    (∑ j, ((Tag.F4.cartan a j : ℤ) : ZMod p) * x j) = 0
  constructor
  · intro hx
    have h' := congrFun hx a
    simpa using h'
  · intro hx
    rw [hx, zero_smul, sub_zero]

private theorem sum_frameCoord_eq {p : ℕ} [NeZero p]
    (β : Fin TwistTag.E6.tag.rank → ℤ) (s : Fin Tag.F4.rank → ZMod p) :
    (∑ j, (β j : ZMod p) *
        ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) j) =
      ∑ b, ((∑ i ∈ orbitF4 b, β i : ℤ) : ZMod p) * f4CartanMul s b := by
  rw [frameCoord_twE6SplitTheta]
  simp only [twE6SplitTheta_apply]
  exact sum_orbitIndex_mul β (f4CartanMul (p := p) s)

private theorem sum_single_mul {p : ℕ} (i : Fin TwistTag.E6.tag.rank)
    (f : Fin TwistTag.E6.tag.rank → ZMod p) :
    (∑ j, ((Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) j : ZMod p) * f j) = f i := by
  simp [Pi.single_apply]

private theorem sum_neg_single_mul {p : ℕ} (i : Fin TwistTag.E6.tag.rank)
    (f : Fin TwistTag.E6.tag.rank → ZMod p) :
    (∑ j, ((-Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) j : ZMod p) * f j) = -f i := by
  simp [Pi.single_apply]

theorem forall_fix_sum_frameCoord_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (a : Fin Tag.F4.rank) :
    (∀ s : Fin Tag.F4.rank → ZMod p, TableBExc.torusAct .F4 p (simple Tag.F4 a) s = s →
        ∑ j, (β j : ZMod p) *
          ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) j = 0) ↔
      β ∈ signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) := by
  constructor
  · intro hfix
    refine mem_signedSimpleRoots_of_orbitSum_eq_zero (p := p) hp2 hβ ?_
    intro b hb
    obtain ⟨s, hs⟩ := f4CartanMul_surjective (p := p) (Pi.single b 1)
    have hsa : f4CartanMul s a = 0 := by
      rw [hs, Pi.single_eq_of_ne (Ne.symm hb)]
    have h0 := hfix s ((torusAct_simple_eq_self_iff a s).mpr hsa)
    rw [sum_frameCoord_eq, hs] at h0
    simpa [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ] using h0
  · intro hβa s hs
    have hfix : f4CartanMul s a = 0 := (torusAct_simple_eq_self_iff a s).mp hs
    obtain ⟨i, hi, hβi | hβi⟩ := hβa
    · subst hβi
      rw [frameCoord_twE6SplitTheta]
      simp only [twE6SplitTheta_apply]
      rw [show (∑ j, ((Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) j : ZMod p) *
          f4CartanMul s (orbitIdx j)) = f4CartanMul s (orbitIdx i) from
        sum_single_mul i (fun j => f4CartanMul s (orbitIdx j))]
      rw [show orbitIdx i = a from (orbitIdx_eq_iff).mpr hi, hfix]
    · subst hβi
      rw [frameCoord_twE6SplitTheta]
      simp only [twE6SplitTheta_apply]
      rw [show (∑ j, ((-Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) j : ZMod p) *
          f4CartanMul s (orbitIdx j)) = -f4CartanMul s (orbitIdx i) from
        sum_neg_single_mul i (fun j => f4CartanMul s (orbitIdx j))]
      rw [show orbitIdx i = a from (orbitIdx_eq_iff).mpr hi, hfix]
      exact neg_zero

theorem twE6SplitFrameHom_injective_of_orderOf
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    Function.Injective (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  have hfd : ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ
      (ExcFrames.twE6SplitTheta p (Multiplicative.toAdd x)) =
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (ExcFrames.twE6SplitTheta p (Multiplicative.toAdd y)) := by
    have h' := congrArg
      (fun g : ↥(graphFixedRootGroup TwistTag.E6 K σ) => (g : ModGL TwistTag.E6.tag K)) hxy
    rw [← ofAdd_toAdd x, ← ofAdd_toAdd y] at h'
    simpa only [ExcFrames.twE6SplitFrameHom_apply] using h'
  have hfc : ExcFrames.frameCoord TwistTag.E6.tag p
      (ExcFrames.twE6SplitTheta p (Multiplicative.toAdd x)) =
      ExcFrames.frameCoord TwistTag.E6.tag p
        (ExcFrames.twE6SplitTheta p (Multiplicative.toAdd y)) := by
    apply TableBExc.E6Three.zetaVec_injective hζo hζ
    exact rootDiagUnit_injective (by simpa [ExcFrames.frameDiag] using hfd)
  have h3 : ExcFrames.twE6SplitTheta p (f4CartanMul (p := p) (Multiplicative.toAdd x)) =
      ExcFrames.twE6SplitTheta p (f4CartanMul (p := p) (Multiplicative.toAdd y)) := by
    rw [← frameCoord_twE6SplitTheta, ← frameCoord_twE6SplitTheta]
    exact hfc
  exact f4CartanMul_injective (ExcFrames.twE6SplitTheta_injective h3)

end CFSG.StandardType.TwE6SplitRootGen

end
