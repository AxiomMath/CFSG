module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveLang

public section

namespace CFSG.StandardType

namespace ExcFrames

open scoped Matrix Pointwise

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical2 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Exceptional CFSG.RankThree.Chevalley
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

section LangFrame


private theorem eq_one_of_dvd_of_dvd_three_pow {p a k : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hap : a ∣ p) (ha3 : a ∣ 3 ^ k) : a = 1 := by
  have hp : p.Prime := Fact.out
  rcases (Nat.dvd_prime hp).1 hap with h | h
  · exact h
  · rw [h] at ha3
    exact absurd (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three ha3) hp3

private theorem rootChar_zetaVec_frameCoord_single_p {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : ζ ^ p = 1) (i : Fin TwistTag.E6.tag.rank) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag p (Pi.single i 1))) γ =
      zmodPowHom ζ hζ (.ofAdd (frameCoord TwistTag.E6.tag p
        (TableBExc.redMod TwistTag.E6.tag p γ) i)) := by
  rw [NoOffE8Five.rootChar_zetaVec]
  congr 1
  have h1 : (∑ j, ((γ j : ZMod p) *
        frameCoord TwistTag.E6.tag p (Pi.single i 1) j))
      = ∑ j, ((γ j : ZMod p) * ((TwistTag.E6.tag.symmetrizedCartan j i : ℤ) : ZMod p)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [frameCoord]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (∑ j, ((γ j : ZMod p) *
        ((TwistTag.E6.tag.symmetrizedCartan j i : ℤ) : ZMod p)))
      = frameCoord TwistTag.E6.tag p (TableBExc.redMod TwistTag.E6.tag p γ) i := by
    rw [frameCoord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TableBExc.redMod, symmetrizedCartan_symm TwistTag.E6.tag j i]
    ring
  rw [h1, h2]

private theorem familyKernel_frameCoord_eq_empty_p {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    [NeZero p] {ζ : Lˣ} (hp3 : p ≠ 3) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    familyKernel (fun i : Fin TwistTag.E6.tag.rank => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag p (Pi.single i 1))) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
  have hzero : ∀ i, frameCoord TwistTag.E6.tag p
      (TableBExc.redMod TwistTag.E6.tag p γ) i = 0 := by
    intro i
    have h1 : rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag p (Pi.single i 1))) γ = 1 := hγ.2 i
    rw [rootChar_zetaVec_frameCoord_single_p hζ i γ] at h1
    have h2 : (Multiplicative.ofAdd (frameCoord TwistTag.E6.tag p
        (TableBExc.redMod TwistTag.E6.tag p γ) i) : Multiplicative (ZMod p)) = 1 :=
      zmodPowHom_injective hζo hζ (h1.trans (map_one (zmodPowHom ζ hζ)).symm)
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  have hfc : frameCoord TwistTag.E6.tag p
      (TableBExc.redMod TwistTag.E6.tag p γ) = 0 := funext hzero
  have hdet : IsUnit (((TwistTag.E6.tag).symmetrizedCartan.det : ℤ) : ZMod p) :=
    CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := p) hp3
  have hred : TableBExc.redMod TwistTag.E6.tag p γ = 0 :=
    frameCoord_injective hdet (by rw [hfc, frameCoord_zero])
  have hdvd : ∀ j, (p : ℤ) ∣ γ j := fun j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd (γ j) p).mp (by
      simpa [TableBExc.redMod] using congrFun hred j)
  let γ' : Fin TwistTag.E6.tag.rank → ℤ := fun j => γ j / (p : ℤ)
  have hgamma : γ = p • γ' := by
    funext j
    rw [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd j)).symm
  have hroot : IsRoot TwistTag.E6.tag (p • γ') := by rw [← hgamma]; exact hγ.1
  exact (Fact.out : p.Prime).ne_one (eq_one_of_isRoot_nsmul (τ := TwistTag.E6.tag) hroot)

private theorem familyStabilizer_frameCoord_eq_one_p {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    [NeZero p] {ζ : Lˣ} (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ familyStabilizer (fun i : Fin TwistTag.E6.tag.rank =>
      TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag p (Pi.single i 1)))) : w = 1 := by
  have hdet : IsUnit (((TwistTag.E6.tag).symmetrizedCartan.det : ℤ) : ZMod p) :=
    CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := p) hp3
  refine CFSG.StandardType.NoOffExc.eq_one_of_torusAct (p := p) hp2 fun x => ?_
  have hfixv : ∀ i, frameCoord TwistTag.E6.tag p (TableBExc.redMod TwistTag.E6.tag p
      (w • TableBExc.liftMod TwistTag.E6.tag p x)) i =
      frameCoord TwistTag.E6.tag p (TableBExc.redMod TwistTag.E6.tag p
        (TableBExc.liftMod TwistTag.E6.tag p x)) i := by
    intro i
    have h1 := hw i (TableBExc.liftMod TwistTag.E6.tag p x)
    rw [rootChar_zetaVec_frameCoord_single_p hζ i
        (w • TableBExc.liftMod TwistTag.E6.tag p x),
      rootChar_zetaVec_frameCoord_single_p hζ i (TableBExc.liftMod TwistTag.E6.tag p x)] at h1
    have h2 := zmodPowHom_injective hζo hζ h1
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  have hred : TableBExc.redMod TwistTag.E6.tag p
      (w • TableBExc.liftMod TwistTag.E6.tag p x) =
      TableBExc.redMod TwistTag.E6.tag p (TableBExc.liftMod TwistTag.E6.tag p x) :=
    frameCoord_injective hdet (funext hfixv)
  rw [TableBExc.torusAct]
  change TableBExc.redMod TwistTag.E6.tag p
    (w • TableBExc.liftMod TwistTag.E6.tag p x) = x
  rw [hred, TableBExc.redMod_liftMod]

private theorem mem_torusGroup_of_commute_frameDiag_p {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    [NeZero p] {ζ : Lˣ} (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {z : ModGL TwistTag.E6.tag L}
    (hz : z ∈ adjointGroup TwistTag.E6.tag L)
    (hcomm : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      z * frameDiag (τ := TwistTag.E6.tag) ζ hζ s =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s * z) :
    z ∈ torusGroup TwistTag.E6.tag L := by
  let a : Fin TwistTag.E6.tag.rank → Fin TwistTag.E6.tag.rank → Lˣ :=
    fun i => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag p (Pi.single i 1))
  have hfam : z ∈ familyCentralizer TwistTag.E6.tag L a := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun i => ?_⟩
    change rootDiagUnit TwistTag.E6.tag (a i) * z *
      (rootDiagUnit TwistTag.E6.tag (a i))⁻¹ = z
    have hfd : frameDiag (τ := TwistTag.E6.tag) ζ hζ (Pi.single i 1) =
        rootDiagUnit TwistTag.E6.tag (a i) := rfl
    rw [← hfd, ← hcomm]
    group
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul TwistTag.E6.tag L a hfam
  have hker : familyKernel a = ∅ := familyKernel_frameCoord_eq_empty_p hp3 hζo hζ
  have hstab : w = 1 := familyStabilizer_frameCoord_eq_one_p hp2 hp3 hζo hζ hw
  have hmT : m ∈ torusGroup TwistTag.E6.tag L := by
    have hm' : m ∈ torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L (familyKernel a) := hm
    rw [hker] at hm'
    have hbot : rootSpan TwistTag.E6.tag L
        (∅ : Set (Fin TwistTag.E6.tag.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hstab, canonicalRep_one, mul_one]
  exact hmT

private theorem frameDiag_mem_twistedTorus_p {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q p : ℕ} [NeZero p] (hFr : ∀ c, Fr c = c ^ q) (hp : p ∣ q + 1)
    {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (s : Fin TwistTag.E6.tag.rank → ZMod p) :
    frameDiag (τ := TwistTag.E6.tag) ζ hζ s ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl)
        (twistHom TwistTag.E6 L Fr) := by
  have htomat : toMat TwistTag.E6.tag.rank twE6TwoMat =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ, twE6PhiTwoWeyl • x =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ
        permLattice TwistTag.E6.perm x := by
    intro x
    rw [twE6PhiTwoWeyl_smul, htomat, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [twistedTorus_E6_eq_map (L := L) Fr twE6PhiTwoWeyl
    (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) hv]
  refine ⟨TableBExc.E6Three.zetaVec ζ hζ (frameCoord TwistTag.E6.tag p s), ?_, rfl⟩
  change TableBExc.E6Three.zetaVec ζ hζ (frameCoord TwistTag.E6.tag p s) ∈
    fixedCharTuples (-1) Fr
  rw [mem_fixedCharTuples_iff]
  intro u
  have hMu : (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ u
      = -u := by
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  have hroot : rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag p s)) u =
      zmodPowHom ζ hζ (.ofAdd (∑ j, ((u j : ZMod p) *
        frameCoord TwistTag.E6.tag p s j))) :=
    NoOffE8Five.rootChar_zetaVec hζ (frameCoord TwistTag.E6.tag p s) u
  have hu5 : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag p s)) u) ^ p = 1 := by
    rw [hroot, zmodPowHom_apply, ← pow_mul,
      Nat.mul_comm (∑ j, ((u j : ZMod p) * frameCoord TwistTag.E6.tag p s j)).val p,
      pow_mul, hζ, one_pow]
  have huq : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag p s)) u) ^ q =
      (rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag p s)) u)⁻¹ := by
    obtain ⟨k, hk⟩ := hp
    have hsucc : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag p s)) u) ^ (q + 1) = 1 := by
      rw [hk, pow_mul, hu5, one_pow]
    have hmul : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag p s)) u) ^ q *
        (rootChar (TableBExc.E6Three.zetaVec ζ hζ
          (frameCoord TwistTag.E6.tag p s)) u) = 1 := by
      rw [← pow_succ, hsucc]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [hMu, show -u = (-1 : ℤ) • u by simp, rootChar_zsmul,
    CFSG.RankThree.PartOne.KE.CTTorus.map_units_eq_pow hFr, huq]
  simp

private theorem natAbs_det_neg_one_sub_smul_one (q : ℕ) :
    (((-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) -
      (q : ℤ) • 1).det).natAbs = (q + 1) ^ 6 := by
  have hneg : (-1 : Matrix (Fin TwistTag.E6.tag.rank)
      (Fin TwistTag.E6.tag.rank) ℤ) = (-1 : ℤ) • 1 := by simp
  have hmat : ((-1 : Matrix (Fin TwistTag.E6.tag.rank)
        (Fin TwistTag.E6.tag.rank) ℤ) - (q : ℤ) • 1) =
      (-(q + 1 : ℤ)) • (1 : Matrix (Fin TwistTag.E6.tag.rank)
        (Fin TwistTag.E6.tag.rank) ℤ) := by
    rw [hneg, ← sub_smul]
    congr 1
    ring
  rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one,
    show Fintype.card (Fin TwistTag.E6.tag.rank) = 6 from rfl]
  have h1 : (-(q + 1 : ℤ)) ^ 6 = (((q + 1 : ℕ)) : ℤ) ^ 6 := by
    push_cast
    ring
  rw [h1, Int.natAbs_pow, Int.natAbs_natCast]

theorem exists_langFrame {f p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) :
    ∃ (ζK : Kˣ) (hζ : (Units.map (algebraMap K L).toMonoidHom ζK) ^ p = 1)
      (g₀ : ModGL TwistTag.E6.tag L)
      (T : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
        ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      orderOf ζK = p ∧ g₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      twistHom TwistTag.E6 L Fr g₀ =
        g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl ∧
      Function.Injective ι₀ ∧
      (∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
        baseChangeGL (algebraMap K L)
          ((ι₀ (Multiplicative.ofAdd s) : _) : ModGL TwistTag.E6.tag K) =
          g₀ * frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s *
            g₀⁻¹) ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      ι₀.range ≤ T ∧
      (∀ t ∈ T, t ^ p = 1 → t ∈ ι₀.range) ∧
      (∃ j : ℕ, Nat.card T * 3 ^ j = (2 ^ f + 1) ^ 6) ∧
      ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ),
        (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (by norm_num))
  haveI : Fintype K := Fintype.ofFinite K
  have hpdvd : p ∣ Nat.card K - 1 := by
    rw [hK]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ f) 1
    rw [hsq]
    exact dvd_mul_of_dvd_right hpq _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ζK, hζKord⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.exists_orderOf_eq_of_dvd_card_sub_one
      (F := K) hpdvd
  let ζ : Lˣ := Units.map (algebraMap K L).toMonoidHom ζK
  have hmapinj : Function.Injective (Units.map (algebraMap K L).toMonoidHom) := by
    intro a b h
    exact Units.ext ((algebraMap K L).injective (congrArg (fun u : Lˣ => (u : L)) h))
  have hζo : orderOf ζ = p := by
    rw [show ζ = Units.map (algebraMap K L).toMonoidHom ζK from rfl,
      orderOf_injective (Units.map (algebraMap K L).toMonoidHom) hmapinj ζK, hζKord]
  have hζ : ζ ^ p = 1 := by
    rw [← hζo, pow_orderOf_eq_one]
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [hFr c, iterateFrobenius_def]
  obtain ⟨g₀, hg₀C, hg₀_iter⟩ :=
    lang_conjugator_twisted K (ℓ := 2) (f := f) hf L twE6PhiTwoWeyl
  have hg₀ : twistHom TwistTag.E6 L Fr g₀ =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl := by
    rw [hFr_eq]
    exact hg₀_iter
  let M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ := -1
  have htomat : toMat TwistTag.E6.tag.rank twE6TwoMat = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ, twE6PhiTwoWeyl • x =
      M *ᵥ permLattice TwistTag.E6.perm x := by
    intro x
    rw [twE6PhiTwoWeyl_smul, htomat, Matrix.neg_mulVec, Matrix.one_mulVec]
  let n : ModGL TwistTag.E6.tag L :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl
  let T₀ : Subgroup (ModGL TwistTag.E6.tag L) :=
    twistedTorusOf n (twistHom TwistTag.E6 L Fr)
  let X : Subgroup (ModGL TwistTag.E6.tag L) :=
    T₀.map (MulAut.conj g₀).toMonoidHom
  have hT0eq : T₀ = (fixedCharTuples M Fr).map
      (rootDiagUnitHom TwistTag.E6.tag L) :=
    twistedTorus_E6_eq_map (L := L) Fr twE6PhiTwoWeyl M hv
  have hdetnat : (M - ((2 ^ f : ℕ) : ℤ) • 1).det.natAbs = (2 ^ f + 1) ^ 6 := by
    simpa [M] using natAbs_det_neg_one_sub_smul_one (2 ^ f)
  have hBne : (M - ((2 ^ f : ℕ) : ℤ) • 1).det ≠ 0 := by
    intro h
    have h0 : (M - ((2 ^ f : ℕ) : ℤ) • 1).det.natAbs = 0 := by rw [h]; rfl
    rw [hdetnat] at h0
    have hpos : 0 < (2 ^ f + 1) ^ 6 := pow_pos (Nat.succ_pos (2 ^ f)) 6
    omega
  have hodd2f : Odd (2 ^ f + 1) := by
    obtain ⟨k, hk⟩ := dvd_pow_self 2 (by omega : f ≠ 0)
    exact ⟨k, by omega⟩
  have hcop2 : ¬ 2 ∣ (M - ((2 ^ f : ℕ) : ℤ) • 1).det.natAbs := by
    rw [hdetnat]
    intro hd
    exact (Nat.not_even_iff_odd.mpr (hodd2f.pow)) (even_iff_two_dvd.mpr hd)
  have hcardT0 : Nat.card T₀ = (2 ^ f + 1) ^ 6 := by
    rw [hT0eq, Subgroup.card_map_of_injective
      (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)),
      natCard_fixedCharTuples M Fr hFr hBne hcop2, hdetnat]
  have hframeT0 : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      frameDiag (τ := TwistTag.E6.tag) ζ hζ s ∈ T₀ :=
    fun s => frameDiag_mem_twistedTorus_p Fr hFr hpq hζo hζ s
  have hframeX : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹ ∈ X :=
    fun s => ⟨_, hframeT0 s, rfl⟩
  have hcardX : Nat.card X = (2 ^ f + 1) ^ 6 := by
    rw [show Nat.card X = Nat.card T₀ from
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hcardT0]
  obtain ⟨hfinR, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf K hK σ hσ L Fr hFr
  set R' : Subgroup (ModGL TwistTag.E6.tag L) := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' : Subgroup (ModGL TwistTag.E6.tag L) :=
    (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L))
    with hC'
  haveI : Finite R' := hfinR
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  haveI : (C'.subgroupOf R').Normal := hnormal
  have hXR : X ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hg₀C (twistedTorusOf_le_adjointGroup n _ hy)) (inv_mem hg₀C)
    · have hyfix := (mem_twistedTorusOf.1 hy).2
      change twistHom TwistTag.E6 L Fr (g₀ * y * g₀⁻¹) = g₀ * y * g₀⁻¹
      rw [map_mul, map_mul, map_inv, hg₀]
      calc g₀ * n * twistHom TwistTag.E6 L Fr y * (g₀ * n)⁻¹
          = g₀ * (n * twistHom TwistTag.E6 L Fr y * n⁻¹) * g₀⁻¹ := by group
        _ = g₀ * y * g₀⁻¹ := by rw [hyfix]
  have hdesc : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹ ∈ C' := by
    intro s
    have hxX : g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹ ∈ X := hframeX s
    have hxp : (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) ^ p = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, frameDiag_pow, map_one]
    let y : R' := ⟨g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹, hXR hxX⟩
    have hyp : y ^ p = 1 := by
      apply Subtype.ext
      change (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) ^ p = 1
      exact hxp
    have hquot3 : Nat.card (R' ⧸ (C'.subgroupOf R')) = 3 ^ k := by
      rw [← Subgroup.index_eq_card, hk]
    have hπp : (QuotientGroup.mk' (C'.subgroupOf R') y) ^ p = 1 := by
      rw [← map_pow, hyp, map_one]
    have hordp : orderOf (QuotientGroup.mk' (C'.subgroupOf R') y) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr hπp
    have hord3 : orderOf (QuotientGroup.mk' (C'.subgroupOf R') y) ∣ 3 ^ k := by
      have h1 : orderOf (QuotientGroup.mk' (C'.subgroupOf R') y) ∣
          Nat.card (R' ⧸ (C'.subgroupOf R')) := orderOf_dvd_natCard _
      rwa [hquot3] at h1
    have hord1 := eq_one_of_dvd_of_dvd_three_pow (p := p) hp3 hordp hord3
    have hone : QuotientGroup.mk' (C'.subgroupOf R') y = 1 := orderOf_eq_one_iff.mp hord1
    have hyN : y ∈ C'.subgroupOf R' := by
      have hmem : y ∈ (QuotientGroup.mk' (C'.subgroupOf R')).ker := MonoidHom.mem_ker.mpr hone
      rwa [QuotientGroup.ker_mk'] at hmem
    exact Subgroup.mem_subgroupOf.mp hyN
  let β : (↥(graphFixedRootGroup TwistTag.E6 K σ)) →*
      ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ).subtype
  have hβinj : Function.Injective β :=
    (baseChangeGL_injective (algebraMap K L)).comp
      (Subgroup.subtype_injective (graphFixedRootGroup TwistTag.E6 K σ))
  have hβrange : β.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hXrange : X ⊓ C' ≤ β.range := by
    rw [hβrange]
    exact inf_le_right
  let T : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) := (X ⊓ C').comap β
  let ψ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* β.range :=
    { toFun := fun s => ⟨g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (Multiplicative.toAdd s) * g₀⁻¹,
        hXrange ⟨hframeX (Multiplicative.toAdd s), hdesc (Multiplicative.toAdd s)⟩⟩
      map_one' := by
        apply Subtype.ext
        change g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (Multiplicative.toAdd (1 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p))) *
          g₀⁻¹ = 1
        rw [toAdd_one, frameDiag_zero]
        group
      map_mul' := fun s t => by
        apply Subtype.ext
        change g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (Multiplicative.toAdd (s * t)) * g₀⁻¹ =
          (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd s) * g₀⁻¹) *
            (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd t) * g₀⁻¹)
        rw [toAdd_mul, frameDiag_add]
        group }
  have hψinj : Function.Injective ψ := by
    intro s t hst
    have hfd : frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd s) =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd t) := by
      have h := congrArg Subtype.val hst
      exact mul_left_cancel (mul_right_cancel h)
    exact Multiplicative.toAdd.injective
      (frameDiag_injective hζo hζ
        (CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := p) hp3) hfd)
  let e : (↥(graphFixedRootGroup TwistTag.E6 K σ)) ≃* β.range :=
    MonoidHom.ofInjective hβinj
  let ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ) := e.symm.toMonoidHom.comp ψ
  have hι₀val : ∀ s : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p),
      β (ι₀ s) = g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (Multiplicative.toAdd s) * g₀⁻¹ := by
    intro s
    have h := MonoidHom.apply_ofInjective_symm hβinj (ψ s)
    simpa [ι₀, e, ψ] using h
  have hι₀inj : Function.Injective ι₀ := by
    intro s t hst
    exact hψinj (e.symm.injective hst)
  have hmapT : T.map β = X ⊓ C' := Subgroup.map_comap_eq_self hXrange
  have hcardK : Nat.card (X.subgroupOf R') = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXR)
  have hinf_eq : (C'.subgroupOf R') ⊓ (X.subgroupOf R') = (X ⊓ C').subgroupOf R' := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact and_comm
  have hcardInf : Nat.card ((C'.subgroupOf R') ⊓ (X.subgroupOf R') : Subgroup R') =
      Nat.card T := by
    rw [hinf_eq]
    rw [show Nat.card ((X ⊓ C').subgroupOf R') =
        Nat.card (X ⊓ C' : Subgroup (ModGL TwistTag.E6.tag L)) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := X ⊓ C') (K := R')
        (le_trans (inf_le_left : X ⊓ C' ≤ X) hXR))]
    rw [← hmapT]
    exact Subgroup.card_map_of_injective hβinj
  have hrel : (C'.subgroupOf R').relIndex (X.subgroupOf R') ∣ 3 ^ k := by
    have h := Subgroup.relIndex_dvd_index_of_normal (H := C'.subgroupOf R') (K := X.subgroupOf R')
    rwa [hk] at h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hrel
  have hrelcard := Subgroup.relIndex_mul_card (H := C'.subgroupOf R') (K := X.subgroupOf R')
  have hpow : 3 ^ j * Nat.card T = Nat.card X := by
    rw [← hj, ← hcardInf, ← hcardK]
    exact hrelcard
  have hjcard : Nat.card T * 3 ^ j = (2 ^ f + 1) ^ 6 := by
    rw [mul_comm (Nat.card T) (3 ^ j), hpow, hcardX]
  have hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    apply hβinj
    rw [map_mul, map_mul]
    have hxX : β x ∈ X := (show β x ∈ X ⊓ C' from hx).1
    have hyX : β y ∈ X := (show β y ∈ X ⊓ C' from hy).1
    obtain ⟨a, ha, hxa⟩ := hxX
    obtain ⟨b, hb, hyb⟩ := hyX
    have hab : a * b = b * a := torusGroup_comm (mem_twistedTorusOf.1 ha).1
      (mem_twistedTorusOf.1 hb).1
    calc β x * β y = (g₀ * a * g₀⁻¹) * (g₀ * b * g₀⁻¹) := by
          rw [← hxa, ← hyb]
          rfl
      _ = g₀ * (a * b) * g₀⁻¹ := by group
      _ = g₀ * (b * a) * g₀⁻¹ := by rw [hab]
      _ = (g₀ * b * g₀⁻¹) * (g₀ * a * g₀⁻¹) := by group
      _ = β y * β x := by
          rw [← hyb, ← hxa]
          rfl
  have hrangeT : ι₀.range ≤ T := by
    rintro _ ⟨s, rfl⟩
    change β (ι₀ s) ∈ X ⊓ C'
    rw [hι₀val s]
    exact ⟨hframeX (Multiplicative.toAdd s), hdesc (Multiplicative.toAdd s)⟩
  have htors : ∀ t ∈ T, t ^ p = 1 → t ∈ ι₀.range := by
    intro t ht ht5
    have htX : β t ∈ X := (show β t ∈ X ⊓ C' from ht).1
    obtain ⟨y, hyT0, hxy⟩ := htX
    have hyp : y ^ p = 1 := by
      have hβt : β t = g₀ * y * g₀⁻¹ := hxy.symm
      have h1 : (g₀ * y * g₀⁻¹) ^ p = 1 := by
        rw [← hβt, ← map_pow, ht5, map_one]
      apply (MulAut.conj g₀).injective
      rw [map_pow, map_one]
      simpa only [MulAut.conj_apply] using h1
    have hyT : y ∈ torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 hyT0).1
    obtain ⟨s, hs⟩ := exists_frameDiag_of_mem (τ := TwistTag.E6.tag) (p := p)
      hζo hζ (CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := p) hp3)
      ⟨hyT, hyp⟩
    refine ⟨Multiplicative.ofAdd s, ?_⟩
    apply hβinj
    rw [hι₀val (Multiplicative.ofAdd s), toAdd_ofAdd, hs]
    exact hxy
  have hcent : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T := by
    intro c hc
    change β c ∈ X ⊓ C'
    have hc' : ∀ s, c * ι₀ s = ι₀ s * c := fun s => hc _ ⟨s, rfl⟩
    have hzcomm : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
        β c * (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) =
          (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) * β c := by
      intro s
      have h := congrArg β (hc' (Multiplicative.ofAdd s))
      simpa [map_mul, hι₀val] using h
    let y : ModGL TwistTag.E6.tag L := g₀⁻¹ * β c * g₀
    have hzC' : β c ∈ C' := by
      rw [← hβrange]
      exact ⟨c, rfl⟩
    have hzR : β c ∈ R' := hle hzC'
    have hzAdj : β c ∈ adjointGroup TwistTag.E6.tag L :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hzR).1
    have hyC : y ∈ adjointGroup TwistTag.E6.tag L :=
      mul_mem (mul_mem (inv_mem hg₀C) hzAdj) hg₀C
    have hycomm : ∀ s, y * frameDiag (τ := TwistTag.E6.tag) ζ hζ s =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s * y := by
      intro s
      have h := hzcomm s
      change (g₀⁻¹ * β c * g₀) * frameDiag (τ := TwistTag.E6.tag) ζ hζ s =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s * (g₀⁻¹ * β c * g₀)
      calc (g₀⁻¹ * β c * g₀) * frameDiag (τ := TwistTag.E6.tag) ζ hζ s
          = g₀⁻¹ * (β c * (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹)) * g₀ := by
            group
        _ = g₀⁻¹ * ((g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) * β c) * g₀ := by
            rw [h]
        _ = frameDiag (τ := TwistTag.E6.tag) ζ hζ s * (g₀⁻¹ * β c * g₀) := by group
    have hyT : y ∈ torusGroup TwistTag.E6.tag L :=
      mem_torusGroup_of_commute_frameDiag_p hp2 hp3 hζo hζ hyC hycomm
    have hzfix : twistHom TwistTag.E6 L Fr (β c) = β c :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hzR).2
    have hyT0 : y ∈ T₀ := by
      rw [mem_twistedTorusOf]
      refine ⟨hyT, ?_⟩
      have hconj : twistHom TwistTag.E6 L Fr y = n⁻¹ * y * n := by
        change twistHom TwistTag.E6 L Fr (g₀⁻¹ * β c * g₀) = n⁻¹ * y * n
        rw [map_mul, map_mul, map_inv, hg₀, hzfix]
        simp only [y, n]
        group
      rw [hconj]
      group
    exact ⟨⟨y, hyT0, by
      change g₀ * (g₀⁻¹ * β c * g₀) * g₀⁻¹ = β c
      group⟩, hzC'⟩
  exact ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hg₀, hι₀inj,
    fun s => hι₀val (Multiplicative.ofAdd s), hcommT, hrangeT, htors, ⟨j, hjcard⟩, hcent⟩

end LangFrame

end ExcFrames

end CFSG.StandardType
