module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem center_sl2_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center SL(2, F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem nonempty_mulEquiv_sl2 {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 f) :
    Nonempty (X ≃* SL(2, GaloisField 2 f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField X 2 2 f h
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans
    QuotientGroup.quotientBot)⟩

@[expose] noncomputable def repOf {F : Type*} [Field F] (L : Subgroup (GLV V))
    (φ : ↥L ≃* SL(2, F)) : Representation (ZMod 2) SL(2, F) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp φ.symm.toMonoidHom)

theorem repOf_apply {F : Type*} [Field F] (L : Subgroup (GLV V)) (φ : ↥L ≃* SL(2, F))
    (g : SL(2, F)) (v : V) : repOf L φ g v = ((φ.symm g : ↥L) : GLV V) v := rfl

theorem repOf_isIrreducible {F : Type*} [Field F] {L : Subgroup (GLV V)} (φ : ↥L ≃* SL(2, F))
    (hL : IsIrr L ⊤) : (repOf L φ).IsIrreducible := by
  rw [isIrreducible_iff]
  obtain ⟨-, hlt, hirr⟩ := hL
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  · have hinv : Invariant L U := fun l hl u hu => by
      have := hU (φ ⟨l, hl⟩) u hu
      simpa [repOf_apply] using this
    exact hirr U hinv bot_le le_top

theorem repOf_toHomUnits_injective {F : Type*} [Field F] (L : Subgroup (GLV V))
    (φ : ↥L ≃* SL(2, F)) : Function.Injective (repOf L φ).toHomUnits := by
  intro g h hgh
  have h1 : ∀ v, repOf L φ g v = repOf L φ h v := fun v => by
    have := congrArg (fun u : (Module.End (ZMod 2) V)ˣ => (u : Module.End (ZMod 2) V) v) hgh
    simpa using this
  have h2 : (φ.symm g : ↥L) = φ.symm h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact h1 v
  exact φ.symm.injective h2

theorem repOf_nontrivial {F : Type*} [Field F] [Nontrivial SL(2, F)] (L : Subgroup (GLV V))
    (φ : ↥L ≃* SL(2, F)) : ∃ g, repOf L φ g ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_ne (1 : SL(2, F))
  refine ⟨g, fun h => hg ?_⟩
  apply repOf_toHomUnits_injective L φ
  ext v
  simp [h]

theorem finrank_eq_mul_of_card {D : Type*} [Field D] [Module D V] [Finite V]
    {d : ℕ} (hD : Nat.card D = 2 ^ d) : Module.finrank (ZMod 2) V = d * Module.finrank D V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Module.Finite D V := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  have h2 := Module.natCard_eq_pow_finrank (K := D) (V := V)
  rw [Nat.card_zmod] at h1
  rw [hD, ← pow_mul] at h2
  rw [h1] at h2
  exact Nat.pow_right_injective le_rfl h2

theorem exists_descent_data {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ n) [Finite V] {L : Subgroup (GLV V)} (φ : ↥L ≃* SL(2, F))
    (hL : IsIrr L ⊤) :
    ∃ (d : ℕ) (J : Finset ℕ), 1 ≤ d ∧ Nat.card (EndRing (repOf L φ)) = 2 ^ d ∧
      J.Nonempty ∧ (∀ i ∈ J, i < n) ∧ J.image (fun i => (i + d) % n) = J ∧
      Module.finrank (EndRing (repOf L φ)) V = 2 ^ J.card ∧
      Module.finrank (ZMod 2) V = d * 2 ^ J.card := by
  classical
  have : Fact (repOf L φ).IsIrreducible := ⟨repOf_isIrreducible φ hL⟩
  have hnt : Nontrivial SL(2, F) := by
    refine ⟨⟨1, ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩⟩
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp at this
  obtain ⟨d, hd1, hDcard, hb⟩ :=
    binary_SL2_irreducible_Frobenius_descent hn hF (repOf L φ) (repOf_nontrivial L φ)
  have : Finite (EndRing (repOf L φ)) := finite_endRing (repOf L φ)
  have : Module.Finite (EndRing (repOf L φ)) V := Module.Finite.of_finite
  let b := Module.finBasis (EndRing (repOf L φ)) V
  obtain ⟨E, _, _, _, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ := hb b
  exact ⟨d, J, hd1, hDcard, hJne, hJn, hshift, hdim, by
    rw [finrank_eq_mul_of_card hDcard, hdim]⟩

end CFSG.Quasithin.G11.Harris.L2
