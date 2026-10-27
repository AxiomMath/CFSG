module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProof
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE8Five

local instance noOffE8FiveFactFiveFD : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankFD : NeZero Tag.E8.rank := ⟨by decide⟩

section FrameDiag

variable {L : Type} [Field L]

@[expose] noncomputable def frameElt (ζ : Lˣ) (hζ : ζ ^ 5 = 1) (lam : ZMod 5) :
    Multiplicative (NoOffRest.eigE8 5 lam) →* ModGL Tag.E8 L where
  toFun s := ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
    ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5)
  map_one' := ExcFrames.frameDiag_zero ζ hζ
  map_mul' x y := by
    simp only [toAdd_mul, Submodule.coe_add]
    exact ExcFrames.frameDiag_add ζ hζ _ _

theorem frameElt_apply (ζ : Lˣ) (hζ : ζ ^ 5 = 1) (lam : ZMod 5) (s : NoOffRest.eigE8 5 lam) :
    frameElt (L := L) ζ hζ lam (Multiplicative.ofAdd s) =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) :=
  rfl

theorem frameDiag_mem_twistedTorus_iff {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {lam : ZMod 5}
    (hq : ((q : ℕ) : ZMod 5) * lam = 1) (s : Fin Tag.E8.rank → ZMod 5) :
    ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s ∈
        twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr ↔
      s ∈ NoOffRest.eigE8 5 lam := by
  have hdet : IsUnit (((Tag.E8).symmetrizedCartan.det : ℤ) : ZMod 5) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) (by norm_num)
  have hinj : Function.Injective (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ) :=
    ExcFrames.frameDiag_injective hζo hζ hdet
  have hpow : ∀ (m : ℕ) (t : Fin Tag.E8.rank → ZMod 5),
      (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ t) ^ m =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (m • t) := by
    intro m
    induction m with
    | zero => intro t; rw [pow_zero, zero_nsmul, ExcFrames.frameDiag_zero]
    | succ m ih =>
        intro t
        rw [pow_succ, ih, ← ExcFrames.frameDiag_add, ← succ_nsmul]
  have hFx : Units.map (entrywiseHom Fr) (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) =
      (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) ^ q := by
    rw [ExcFrames.frameDiag]
    rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr, ← rootDiagUnit_pow]
  have hconj := ExcFrames.canonicalRep_conj_frameDiag (τ := Tag.E8) ζ hζ
    NoOffRest.weylE8W s
  have hkey : canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W *
        Units.map (entrywiseHom Fr) (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) *
        (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W)⁻¹ =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        (q • TableBExc.torusAct Tag.E8 5 NoOffRest.weylE8W s) := by
    rw [hFx, ← conj_pow, hconj, hpow q]
  rw [mem_twistedTorus]
  constructor
  · intro h
    have hqs : q • TableBExc.torusAct Tag.E8 5 NoOffRest.weylE8W s = s := by
      apply hinj
      rw [← hkey, h.2]
    have hsm : TableBExc.torusAct Tag.E8 5 NoOffRest.weylE8W s = lam • s := by
      have h' := congrArg (fun v : Fin Tag.E8.rank → ZMod 5 => lam • v) hqs
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 5) q
        (TableBExc.torusAct Tag.E8 5 NoOffRest.weylE8W s)] at h'
      rwa [smul_smul, mul_comm, hq, one_smul] at h'
    rw [NoOffRest.mem_eigSp, NoOffRest.torusLin_apply]
    exact hsm
  · intro hs
    have hsm : TableBExc.torusAct Tag.E8 5 NoOffRest.weylE8W s = lam • s := by
      have hs' := hs
      rw [NoOffRest.mem_eigSp, NoOffRest.torusLin_apply] at hs'
      exact hs'
    refine mem_twistedTorus.2 ⟨?_, ?_⟩
    · change rootDiagUnit Tag.E8
        (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E8 5 s)) ∈
          torusGroup Tag.E8 L
      exact CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_torusGroup_E8 (K := L) _
    · rw [hkey, hinj.eq_iff, hsm, ← Nat.cast_smul_eq_nsmul (R := ZMod 5) q (lam • s),
        smul_smul, hq, one_smul]

theorem exists_frameDiag_of_mem_twistedTorus_pow {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {lam : ZMod 5}
    (hq : ((q : ℕ) : ZMod 5) * lam = 1) {x : ModGL Tag.E8 L}
    (hx : x ∈ twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr)
    (hx5 : x ^ 5 = 1) :
    ∃ s ∈ NoOffRest.eigE8 5 lam, x = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s := by
  obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) (by norm_num))
    (v := x) ⟨(mem_twistedTorus.1 hx).1, hx5⟩
  exact ⟨s, (frameDiag_mem_twistedTorus_iff hFr hζo hζ hq s).1 (hs ▸ hx), hs.symm⟩

end FrameDiag

end NoOffE8Five

end CFSG.StandardType
