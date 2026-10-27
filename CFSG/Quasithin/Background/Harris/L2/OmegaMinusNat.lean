module

public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusRep
public import CFSG.Quasithin.Background.SmithB45L2Herm
public import CFSG.Quasithin.Background.Harris.L2.Setup

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.Assembly.LowTwoRank
open Matrix
open scoped MatrixGroups

section Herm

variable {F : Type} [Field F] [CharP F 2] (s : ℕ)

theorem mem_twistedForm_of_hermA {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA s F) :
    X ∈ twistedForm (sig (F := F) s) := by
  rw [mem_hermA, frobPow_eq_map] at hX
  rw [mem_twistedForm]
  have := congrArg Matrix.transpose hX
  rw [transpose_transpose] at this
  exact this.symm

theorem mem_hermA_of_twistedForm {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ twistedForm (sig (F := F) s)) :
    X ∈ hermA s F := by
  rw [mem_twistedForm] at hX
  rw [mem_hermA, frobPow_eq_map]
  rw [RingHom.mapMatrix_apply, ← hX, transpose_transpose]

variable (F) in
@[expose] def hermToTwisted : hermA s F ≃+ twistedForm (sig (F := F) s) where
  toFun X := ⟨X.1, mem_twistedForm_of_hermA s X.2⟩
  invFun X := ⟨X.1, mem_hermA_of_twistedForm s X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem hermToTwisted_coe (X : hermA s F) :
    ((hermToTwisted F s X : twistedForm (sig (F := F) s)) : Matrix (Fin 2) (Fin 2) F) = X := rfl

theorem hermToTwisted_hermAct (hinv : ∀ x : F, sig (F := F) s (sig (F := F) s x) = x) (g : SL(2, F))
    (X : hermA s F) :
    hermToTwisted F s (hermAct s hinv g X) = twistRep hinv g (hermToTwisted F s X) := by
  apply Subtype.ext
  rw [twistRep_apply, hermToTwisted_coe, hermToTwisted_coe, hermAct_coe, frobPow_eq_map,
    RingHom.mapMatrix_apply]

end Herm

@[expose] def addEquivZMod {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ZMod 2) M]
    [Module (ZMod 2) N] (e : M ≃+ N) : M ≃ₗ[ZMod 2] N :=
  { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }

section Natural

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {L : Subgroup (GLV V)}
  {a : ℕ}

theorem natural_omega_of_orth {F : Type} [Field F] [Fintype F] [CharP F 2] (ha : 1 ≤ a)
    (φ : ↥L ≃* SL(2, F)) (hF : Fintype.card F = 2 ^ (2 * a))
    (β : V ≃+ ↥(hermA a F)) (j : ℕ)
    (hβ : ∀ g w, β (repOf L φ g w) = hermAct a (sig_sig hF) (fieldAut F j g) (β w)) :
    ∃ b c : GaloisField 2 a, (∀ s : GaloisField 2 a, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (Θ : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c)))
        (ψ : V ≃ₗ[ZMod 2] (QIdx → GaloisField 2 a)),
        (∀ (l : ↥L) (v : V), ψ ((l : GLV V) v) =
          ((Θ l : GL QIdx (GaloisField 2 a)) : Matrix QIdx QIdx (GaloisField 2 a)) *ᵥ ψ v) ∧
        (∀ (l : ↥L) (v : QIdx → GaloisField 2 a),
          StatedQuadMinus 2 (GaloisField 2 a) b c
            (((Θ l : GL QIdx (GaloisField 2 a)) : Matrix QIdx QIdx (GaloisField 2 a)) *ᵥ v) =
          StatedQuadMinus 2 (GaloisField 2 a) b c v) := by
  set σ : F →+* F := sig (F := F) a
  have ha0 : a ≠ 0 := by omega
  have hσ : ∀ x, σ x = x ^ 2 ^ a := sig_apply a
  have hF' : Nat.card F = (2 ^ a) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm, pow_mul]
  have hinv : ∀ x, σ (σ x) = x := sig_sig hF
  obtain ⟨ω, hω⟩ := exists_frob_ne ha hF' hσ
  have hcard : Nat.card (frobFixed σ) = Nat.card (GaloisField 2 a) := by
    rw [card_frobFixed ha hF' hσ, GaloisField.card 2 a ha0]
  have : Fintype (frobFixed σ) := Fintype.ofFinite _
  have : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  obtain ⟨e⟩ : Nonempty (frobFixed σ ≃+* GaloisField 2 a) :=
    ⟨FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)⟩
  obtain ⟨M, ψ, b, c, hbc, hMinj, hMrange, hψ, hQ⟩ := exists_omegaRep ha hF' hσ e hω
  refine ⟨b, c, hbc, ?_⟩
  let g₀ : ↥L ≃* SL(2, F) := φ.trans (CFSG.Quasithin.B45L2.fieldAutEquiv j)
  let Θ : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c)) :=
    g₀.trans ((MonoidHom.ofInjective hMinj).trans (MulEquiv.subgroupCongr hMrange))
  have hΘ : ∀ l : ↥L, ((Θ l : GL QIdx (GaloisField 2 a)) : Matrix QIdx QIdx (GaloisField 2 a)) =
      (M (g₀ l) : Matrix QIdx QIdx (GaloisField 2 a)) := fun l => rfl
  refine ⟨Θ, addEquivZMod ((β.trans (hermToTwisted F a)).trans ψ), fun l v => ?_, fun l v => ?_⟩
  · rw [hΘ]
    have h1 : ((l : GLV V) v) = repOf L φ (φ l) v := by
      rw [repOf_apply, MulEquiv.symm_apply_apply]
    show ψ (hermToTwisted F a (β ((l : GLV V) v))) = _ *ᵥ ψ (hermToTwisted F a (β v))
    rw [h1, hβ, hermToTwisted_hermAct, hψ]
    rfl
  · rw [hΘ]
    exact hQ _ v

end Natural

end CFSG.Quasithin.G11.Harris.L2
