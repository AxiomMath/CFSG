module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFrames

section Torus

variable {τ : Tag} {L : Type} [Field L] {p : ℕ}


@[expose] noncomputable def frameDiag [NeZero p] (ζ : Lˣ) (hζ : ζ ^ p = 1)
    (s : Fin τ.rank → ZMod p) : ModGL τ L :=
  rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ (frameCoord τ p s))

theorem zetaVec_add [NeZero p] (ζ : Lˣ) (hζ : ζ ^ p = 1) (x y : Fin τ.rank → ZMod p) :
    TableBExc.E6Three.zetaVec ζ hζ (x + y) =
      TableBExc.E6Three.zetaVec ζ hζ x * TableBExc.E6Three.zetaVec ζ hζ y := by
  funext i
  simp only [TableBExc.E6Three.zetaVec, Pi.add_apply, Pi.mul_apply, ofAdd_add, map_mul]

theorem frameDiag_add [NeZero p] (ζ : Lˣ) (hζ : ζ ^ p = 1) (s t : Fin τ.rank → ZMod p) :
    frameDiag (τ := τ) ζ hζ (s + t) = frameDiag ζ hζ s * frameDiag ζ hζ t := by
  rw [frameDiag, frameDiag, frameDiag, frameCoord_add, zetaVec_add, rootDiagUnit_mul]

theorem frameDiag_zero [NeZero p] (ζ : Lˣ) (hζ : ζ ^ p = 1) :
    frameDiag (τ := τ) ζ hζ 0 = 1 := by
  have h := frameDiag_add (τ := τ) ζ hζ 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem canonicalRep_conj_frameDiag [NeZero p] (ζ : Lˣ) (hζ : ζ ^ p = 1) (w : WeylGroup τ)
    (s : Fin τ.rank → ZMod p) :
    canonicalRep (coxeterSystem τ) L w * frameDiag ζ hζ s *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = frameDiag ζ hζ (TableBExc.torusAct τ p w s) := by
  rw [frameDiag, canonicalRep_conj_rootDiagUnit, TableBExc.E6Three.weylTuple_zetaVec,
    adAct_frameCoord, frameDiag]

theorem frameDiag_injective [Fact p.Prime] {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) :
    Function.Injective (frameDiag (τ := τ) ζ hζ) := fun _ _ h =>
  frameCoord_injective hdet (TableBExc.E6Three.zetaVec_injective hζo hζ (rootDiagUnit_injective h))

theorem frameDiag_pow [NeZero p] (ζ : Lˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    frameDiag (τ := τ) ζ hζ s ^ p = 1 := by
  rw [frameDiag, rootDiagUnit_pow, ← rootDiagUnit_one (τ := τ) (K := L)]
  congr 1
  funext i
  rw [Pi.pow_apply, TableBExc.E6Three.zetaVec_apply, Pi.one_apply, ← pow_mul, mul_comm, pow_mul,
    hζ, one_pow]

theorem exists_frameDiag_eq [Fact p.Prime] {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {a : Fin τ.rank → Lˣ}
    (ha : a ^ p = 1) : ∃ s, frameDiag (τ := τ) ζ hζ s = rootDiagUnit τ a := by
  obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ ha
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp (frameCoord_injective (τ := τ) hdet)) x
  exact ⟨s, by rw [frameDiag, hs, hx]⟩

variable (τ L p) in
@[expose] def splitPow : Set (ModGL τ L) :=
  {h | h ∈ torusGroup τ L ∧ h ^ p = 1}

theorem frameDiag_mem [NeZero p] (hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    frameDiag (τ := τ) ζ hζ s ∈ splitPow τ L p :=
  ⟨hfull _, frameDiag_pow ζ hζ s⟩

theorem exists_frameDiag_of_mem [Fact p.Prime] {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {v : ModGL τ L}
    (hv : v ∈ splitPow τ L p) : ∃ s, frameDiag (τ := τ) ζ hζ s = v := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hv.1
  have ha : a ^ p = 1 := rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hv.2, rootDiagUnit_one])
  exact exists_frameDiag_eq hζo hζ hdet ha

end Torus

end ExcFrames

end CFSG.StandardType
