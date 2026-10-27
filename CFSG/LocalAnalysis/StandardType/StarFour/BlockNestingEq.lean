module

public import CFSG.LocalAnalysis.StandardType.StarFour.FrameNesting
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSLDecomp

public section

namespace CFSG.StandardType.StarFour

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V]

private theorem natCard_specialLinearGroup_eq_of_ringEquiv
    {E E' : Type*} [CommRing E] [CommRing E'] (e : E' ≃+* E)
    {m m' : ℕ} (h : m' = m) :
    Nat.card (SpecialLinearGroup E (Fin m → E)) =
      Nat.card (SpecialLinearGroup E' (Fin m' → E')) := by
  have hmat : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) =
      Nat.card (Matrix.SpecialLinearGroup (Fin m') E') := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv
      ((Matrix.reindexRingEquiv E (finCongr h.symm)).toEquiv.trans
        (RingEquiv.mapMatrix e.symm).toEquiv) (fun M => ?_)
    change M.det = 1 ↔ (RingEquiv.mapMatrix e.symm
      (Matrix.reindex (finCongr h.symm) (finCongr h.symm) M)).det = 1
    have hdet : (RingEquiv.mapMatrix e.symm
        (Matrix.reindex (finCongr h.symm) (finCongr h.symm) M)).det = e.symm M.det := by
      rw [← RingEquiv.map_det e.symm
        (Matrix.reindex (finCongr h.symm) (finCongr h.symm) M)]
      rw [Matrix.det_reindex_self]
    rw [hdet]
    constructor
    · intro h1
      rw [h1, map_one]
    · intro h1
      have h2 := congrArg e h1
      rw [RingEquiv.apply_symm_apply, map_one] at h2
      exact h2
  calc Nat.card (SpecialLinearGroup E (Fin m → E))
      = Nat.card (Matrix.SpecialLinearGroup (Fin m) E) :=
        (Nat.card_congr
          (Matrix.SpecialLinearGroup.toLin'_equiv (n := Fin m) (R := E)).toEquiv).symm
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin m') E') := hmat
    _ = Nat.card (SpecialLinearGroup E' (Fin m' → E')) :=
        Nat.card_congr
          (Matrix.SpecialLinearGroup.toLin'_equiv (n := Fin m') (R := E')).toEquiv

theorem slOnBlock_eq_of_nesting {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (i' : Fin fr'.r)
    (ε : fr'.E i' →ₐ[F] fr.E i) (hε : Function.Bijective ε)
    (hle : fr.slOnBlock i ≤ fr'.slOnBlock i') (hmm : fr'.m i' = fr.m i) :
    fr.slOnBlock i = fr'.slOnBlock i' := by
  classical
  haveI : Finite V :=
    Finite.of_injective ((Module.finBasis F V).equivFun : V → (Fin (Module.finrank F V) → F))
      (Module.finBasis F V).equivFun.injective
  haveI : Finite (SpecialLinearGroup F V) :=
    Finite.of_injective (fun u : SpecialLinearGroup F V => (u : V → V))
      (fun u v hv => by ext x; exact congrFun hv x)
  have hcard : Nat.card (fr.slOnBlock i) = Nat.card (fr'.slOnBlock i') :=
    calc Nat.card (fr.slOnBlock i)
        = Nat.card (SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :=
          (Nat.card_congr (SemiFrame.blockMulEquiv fr i).toEquiv).symm
      _ = Nat.card (SpecialLinearGroup (fr'.E i') (Fin (fr'.m i') → fr'.E i')) :=
          natCard_specialLinearGroup_eq_of_ringEquiv
            (RingEquiv.ofBijective ε.toRingHom hε) hmm
      _ = Nat.card (fr'.slOnBlock i') :=
          Nat.card_congr (SemiFrame.blockMulEquiv fr' i').toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

end CFSG.StandardType.StarFour
