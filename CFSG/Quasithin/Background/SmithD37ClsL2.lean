module

public import CFSG.Quasithin.Background.SmithD37ClsDefs
public import CFSG.Quasithin.Background.SmithB45L2Class
import CFSG.Adapters.LinearSmallCatalog
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Lift CFSG.Quasithin.B45L2
open scoped MatrixGroups

theorem exists_sl2_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), 2 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (X ≃* SL(2, F)) := by
  obtain ⟨⟨-, hf, -, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn : 2 ≤ n := by
    by_contra hlt
    exact h22 (by simp [show n = 1 by omega])
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_two_of_card_eq hcard
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* SL(2, K) :=
    (QuotientGroup.quotientMulEquivOfEq B42L2.center_sl2_eq_bot).trans QuotientGroup.quotientBot
  exact ⟨K, _, _, hn, hcard, ⟨(e'.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans e₂⟩⟩

section End

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def endEquiv (θ : V ≃* Multiplicative W) :
    (V →* V) ≃ Module.End (ZMod 2) W where
  toFun φ := AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.toMultiplicative.symm (θ.toMonoidHom.comp (φ.comp θ.symm.toMonoidHom)))
  invFun ψ := θ.symm.toMonoidHom.comp
    ((AddMonoidHom.toMultiplicative (ψ : W →+ W)).comp θ.toMonoidHom)
  left_inv φ := by
    ext v
    simp
  right_inv ψ := by
    ext w
    simp

theorem endEquiv_apply (θ : V ≃* Multiplicative W) (φ : V →* V) (w : W) :
    endEquiv θ φ w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) := rfl

theorem endCard_eq {F : Type} [Field F] {L : Subgroup (MulAut V)} (θ : V ≃* Multiplicative W)
    (θL : ↥L ≃* SL(2, F)) : endCard L = Nat.card (EndRing (repOf θ θL)) := by
  rw [natCard_endRing, endCard]
  refine Nat.card_congr (Equiv.subtypeEquiv (endEquiv θ) fun φ => ?_)
  constructor
  · intro h g w
    rw [repOf_apply, repOf_apply, endEquiv_apply, endEquiv_apply, binPsi_apply, binPsi_apply]
    simp [h _ (θL.symm g).2]
  · intro h l hl v
    have := h (θL ⟨l, hl⟩) (Multiplicative.toAdd (θ v))
    rw [repOf_theta, repOf_theta, endEquiv_apply, endEquiv_apply, binPsi_apply,
      binPsi_apply] at this
    simpa using this

end End

section Class

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

theorem class_four (hF : Fintype.card F = 2 ^ 2) (ρ : Representation (ZMod 2) SL(2, F) W)
    (hirr : ρ.IsIrreducible) (hnt : ∃ g, ρ g ≠ 1) :
    (Nat.card (EndRing ρ) = 2 ^ 2 ∧ Module.finrank (EndRing ρ) W = 2) ∨
      (Nat.card (EndRing ρ) = 2 ^ 1 ∧ Module.finrank (EndRing ρ) W = 4) := by
  classical
  have hF4 : Fintype.card F = 4 := by rw [hF]; norm_num
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  let _ : Fintype (Projectivization F (Fin 2 → F)) := Fintype.ofFinite _
  have hW16 : Nat.card W = 16 := by
    obtain ⟨hcases, -, -, -, -, h16a, h16b⟩ :=
      irreducible_binary_SL2_four_module_production hF4 ρ hirr
    rcases hcases with ⟨φ, hφ⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
    · exfalso
      obtain ⟨g, hg⟩ := hnt
      exact hg (LinearMap.ext fun w => φ.injective (hφ g w))
    · rw [Nat.card_congr φ.toEquiv, h16a]
    · rw [Nat.card_congr φ.toEquiv, h16b]
  obtain ⟨d, -, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 2) (by norm_num) hF ρ hnt
  have : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨-, -, -, -, -, -, J, hJne, hJn, -, -, hdim⟩ := hdesc (Module.finBasis (EndRing ρ) W)
  have hJ2 : J.card ≤ 2 := by
    calc J.card ≤ (Finset.range 2).card :=
          Finset.card_le_card (fun i hi => Finset.mem_range.mpr (hJn i hi))
      _ = 2 := Finset.card_range 2
  have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hWd : 2 ^ (d * 2 ^ J.card) = 2 ^ 4 := by
    rw [pow_mul, ← hDcard, ← hdim, ← natCard_eq_pow_finrank (ρ := ρ), hW16]
    norm_num
  have hexp : d * 2 ^ J.card = 4 := Nat.pow_right_injective le_rfl hWd
  rcases (by omega : J.card = 1 ∨ J.card = 2) with hJ | hJ
  · rw [hJ] at hexp hdim
    exact Or.inl ⟨by rw [hDcard]; congr 1; omega, hdim⟩
  · rw [hJ] at hexp hdim
    exact Or.inr ⟨by rw [hDcard]; congr 1; omega, hdim⟩

end Class

section Offender

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {F : Type} [Field F] [Fintype F] [CharP F 2] {L : Subgroup (MulAut V)}

omit [Finite V] [Finite W] [Fintype F] [CharP F 2] in
private theorem repOf_ne_one (θ : V ≃* Multiplicative W) (θL : ↥L ≃* SL(2, F)) :
    ∃ g, repOf θ θL g ≠ 1 := by
  have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
    one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
  exact ⟨uElt 1, fun h => hne (repOf_injective θ θL (h.trans (map_one _).symm))⟩

omit [Finite V] in
theorem class_of_offender (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (θL : ↥L ≃* SL(2, F))
    {A : Subgroup (MulAut V)} (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (hA1 : A ≠ ⊥)
    (hA : IsElemAbelian2 A) (hoff : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A))
    (θ : V ≃* Multiplicative W) :
    (Nat.card (EndRing (repOf θ θL)) = 2 ^ n ∧ Module.finrank (EndRing (repOf θ θL)) W = 2) ∨
      ∃ s, n = 2 * s ∧ Nat.card (EndRing (repOf θ θL)) = 2 ^ s ∧
        Module.finrank (EndRing (repOf θ θL)) W = 4 := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · rcases class_four hF (repOf θ θL) (repOf_isIrreducible θ θL hirr) (repOf_ne_one θ θL) with
      h | h
    · exact Or.inl h
    · exact Or.inr ⟨1, rfl, h⟩
  · exact twoF_class_of_offender hirr hn3 hF θL hAN hA1 hA hoff θ

omit [Finite V] [Fintype F] [CharP F 2] in
theorem card_le_of_le (θL : ↥L ≃* SL(2, F)) [Finite F] [CharP F 2] {A : Subgroup (MulAut V)}
    (hAL : A ≤ L) (hA : IsElemAbelian2 A) : Nat.card A ≤ Nat.card F := by
  set A' : Subgroup SL(2, F) := (A.subgroupOf L).map θL.toMonoidHom
  have hcard : Nat.card A' = Nat.card A := by
    rw [Subgroup.card_map_of_injective θL.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  rw [← hcard]
  refine card_le_of_involutions A' fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := hx
  have h2 : a * a = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hA.2 _ (Subgroup.mem_subgroupOf.mp ha))
  rw [← map_mul, h2, map_one]

omit [Finite V] [Fintype F] in
theorem card_le_of_not_le (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (θL : ↥L ≃* SL(2, F)) (θ : V ≃* Multiplicative W)
    {A : Subgroup (MulAut V)} (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hAL : ¬ A ≤ L) :
    ∃ s, 1 ≤ s ∧ n = 2 * s ∧ Nat.card A ≤ 2 ^ (s + 1) := by
  classical
  set A₀ := A.map (binPsi θ).toMonoidHom with hA₀
  have : CFSG.IsElementaryAbelian 2 ↥A₀ := (isElemAbelian2_iff_map θ A).1 hA
  have : CFSG.IsElementaryAbelian 2 ↥(toUnits A₀) :=
    isElementaryAbelian_of_equiv (toUnitsEquiv A₀) inferInstance
  have hcard : Nat.card ↥(toUnits A₀) = Nat.card A := by
    rw [natCard_toUnits, hA₀, Subgroup.card_map_of_injective (binPsi θ).injective]
  have hAN' : toUnits A₀ ≤ Subgroup.normalizer
      ((repOf θ θL).toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ) := by
    rw [repOf_range]
    apply toUnits_normalizer
    rw [hA₀, ← Subgroup.map_equiv_normalizer_eq L (binPsi θ)]
    exact Subgroup.map_mono hAN
  have hAL' : ¬ toUnits A₀ ≤ (repOf θ θL).toHomUnits.range := by
    rw [repOf_range]
    intro h
    apply hAL
    intro a ha
    have hmem : (unitsEquiv (ZMod 2) W).symm (binPsi θ a) ∈ toUnits A₀ := by
      rw [mem_toUnits, MulEquiv.apply_symm_apply]
      exact ⟨a, ha, rfl⟩
    have h2 := h hmem
    rw [mem_toUnits, MulEquiv.apply_symm_apply] at h2
    obtain ⟨b, hb, hba⟩ := h2
    rwa [← (binPsi θ).injective hba]
  have hρ : Function.Injective (repOf θ θL).toHomUnits := fun g h e =>
    repOf_injective θ θL (by simpa using congrArg Units.val e)
  obtain ⟨s, hs, hns, hle, -⟩ := outer_data hn hF (repOf θ θL)
    (repOf_isIrreducible θ θL hirr) hρ (toUnits A₀) hAN' hAL'
  exact ⟨s, hs, hns, hcard ▸ hle⟩

omit [Finite V] [Fintype F] in
theorem card_le_of_orth (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) [Finite F] {s : ℕ}
    (hs : 1 ≤ s) (hF : Nat.card F = 2 ^ (2 * s)) (θL : ↥L ≃* SL(2, F))
    (θ : V ≃* Multiplicative W) {A : Subgroup (MulAut V)}
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (hA : IsElemAbelian2 A) :
    Nat.card A ≤ 2 ^ (2 * s) := by
  by_cases hAL : A ≤ L
  · exact hF ▸ card_le_of_le θL hAL hA
  · obtain ⟨s', -, hss, hle⟩ := card_le_of_not_le hirr (by omega) hF θL θ hAN hA hAL
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

end Offender

theorem cls2F_psl2_even {Q : Type} [CommGroup Q] [Finite Q] {G L E : Subgroup (MulAut Q)}
    (h : Cls2F G L E) {n : ℕ} (hn : IsPSL 2 2 n ↥L) :
    (endCard L = 2 ^ n ∧ Nat.card Q = 2 ^ (2 * n)) ∨
      ∃ s, 1 ≤ s ∧ n = 2 * s ∧ endCard L = 2 ^ s ∧ Nat.card Q = 2 ^ (4 * s) ∧
        Nat.card E ≤ 2 ^ (2 * s) := by
  classical
  obtain ⟨F, _, _, hn2, hF, ⟨θL⟩⟩ := exists_sl2_of_isPSL hn
  have : CharP F 2 := charP_two_of_card_eq hF
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (V := Q) fun v => by
    rw [← pow_two]
    exact h.exp v
  have hirr := h.hyp.2.2.2
  have hEN : E ≤ Subgroup.normalizer (L : Set (MulAut Q)) :=
    h.a2.le.trans (B42L2.le_normalizer_of_b4Hyp h.hyp)
  have : Fact (repOf θ θL).IsIrreducible := ⟨repOf_isIrreducible θ θL hirr⟩
  have hQ : Nat.card Q =
      Nat.card (EndRing (repOf θ θL)) ^ Module.finrank (EndRing (repOf θ θL)) W := by
    rw [natCard_eq θ, natCard_eq_pow_finrank (ρ := repOf θ θL)]
  rw [endCard_eq θ θL, hQ]
  rcases class_of_offender hirr hn2 hF θL hEN h.a2.ne_bot h.a2.isElemAbelian2 h.off θ with
    ⟨hD, hdim⟩ | ⟨s, hns, hD, hdim⟩
  · refine Or.inl ⟨hD, ?_⟩
    rw [hD, hdim, ← pow_mul, mul_comm]
  · refine Or.inr ⟨s, by omega, hns, hD, by rw [hD, hdim, ← pow_mul, mul_comm], ?_⟩
    exact card_le_of_orth hirr (by omega) (by rw [Nat.card_eq_fintype_card, hF, hns]) θL θ hEN
      h.a2.isElemAbelian2

theorem isPSL_two_two_two_of_five {X : Type} [Group X] (h : IsPSL 2 5 1 X) : IsPSL 2 2 2 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK5 : Nat.card K = 5 := by rw [hK, pow_one]
  have hc4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  obtain ⟨e5⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_five K hK5)
  obtain ⟨e4⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four (GaloisField 2 2)
      (by rw [hc4]; norm_num))
  refine ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hc4, ⟨?_⟩⟩
  let φ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
  exact e'.trans ((φ 2 K).symm.trans (e5.trans (e4.symm.trans (φ 2 (GaloisField 2 2)))))

theorem cls2F_psl2_five {Q : Type} [CommGroup Q] [Finite Q] {G L E : Subgroup (MulAut Q)}
    (h : Cls2F G L E) (hn : IsPSL 2 5 1 ↥L) :
    (endCard L = 4 ∧ Nat.card Q = 16) ∨ (endCard L = 2 ∧ Nat.card Q = 16 ∧ Nat.card E ≤ 4) := by
  rcases cls2F_psl2_even h (isPSL_two_two_two_of_five hn) with ⟨h1, h2⟩ |
    ⟨s, -, hs, h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2⟩
  · obtain rfl : s = 1 := by omega
    exact Or.inr ⟨h1, h2, h3⟩

end CFSG.Quasithin.SmithD37
