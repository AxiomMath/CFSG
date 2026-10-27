module

public import CFSG.Quasithin.Background.Harris.L2.Setup
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.Quasithin.Background.Harris.OrdinaryProofs
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {L : Subgroup (GLV V)}
  {F : Type*} [Field F]

@[expose] def endRingToEnd (φ : ↥L ≃* SL(2, F)) (ψ : EndRing (repOf L φ)) :
    Module.End (ZMod 2) V where
  toFun := ψ
  map_add' := ψ.map_add
  map_smul' c x := ZMod.map_smul ψ c x

theorem endRingToEnd_mem (φ : ↥L ≃* SL(2, F)) (ψ : EndRing (repOf L φ)) :
    endRingToEnd φ ψ ∈ endCommutant L := by
  unfold endCommutant
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  have key := (mem_endRing_iff (repOf L φ) (endRingToEnd φ ψ)).1 ⟨ψ, rfl⟩ (φ ⟨h, hh⟩)
  apply LinearMap.ext
  intro v
  have := key v
  rw [repOf_apply, repOf_apply, MulEquiv.symm_apply_apply] at this
  exact this.symm

theorem card_endCommutant (φ : ↥L ≃* SL(2, F)) :
    Nat.card (endCommutant L) = Nat.card (EndRing (repOf L φ)) := by
  symm
  refine Nat.card_eq_of_bijective (fun ψ => ⟨endRingToEnd φ ψ, endRingToEnd_mem φ ψ⟩) ⟨?_, ?_⟩
  · intro ψ ψ' h
    have h1 := congrArg (fun x : endCommutant L => (x : Module.End (ZMod 2) V)) h
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) V => f v) h1
  · rintro ⟨f, hf⟩
    have hcomm : ∀ g v, f (repOf L φ g v) = repOf L φ g (f v) := by
      intro g v
      rw [repOf_apply, repOf_apply]
      exact endCommutant_apply_comm hf (φ.symm g).2 v
    obtain ⟨ψ, hψ⟩ := (mem_endRing_iff (repOf L φ) f).2 hcomm
    refine ⟨ψ, Subtype.ext (LinearMap.ext fun v => ?_)⟩
    exact congrFun hψ v

theorem endIsField_of_card [Finite V] (hL : IsIrr L ⊤) (φ : ↥L ≃* SL(2, F)) {a : ℕ} (ha : 1 ≤ a)
    (hD : Nat.card (EndRing (repOf L φ)) = 2 ^ a) : EndIsField L a := by
  obtain ⟨e, ⟨E⟩⟩ := exists_endIsField hL
  have hcard : Nat.card (GaloisField 2 e) = Nat.card (GaloisField 2 a) := by
    rw [GaloisField.card 2 a (by omega), ← hD, ← card_endCommutant φ]
    exact (Nat.card_congr E.toEquiv).symm
  have : Fintype (GaloisField 2 e) := Fintype.ofFinite _
  have : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  obtain ⟨r⟩ : Nonempty (GaloisField 2 e ≃+* GaloisField 2 a) :=
    ⟨FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)⟩
  refine ⟨E.trans (AlgEquiv.ofRingEquiv (f := r) fun x => ?_)⟩
  exact congrFun (congrArg DFunLike.coe
    (RingHom.ext_zmod (r.toRingHom.comp (algebraMap (ZMod 2) (GaloisField 2 e)))
      (algebraMap (ZMod 2) (GaloisField 2 a)))) x

end CFSG.Quasithin.G11.Harris.L2
