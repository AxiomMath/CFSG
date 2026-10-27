module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4Small
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddL28Abstract
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)
open CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

theorem isSolvable_of_card_dvd_pow_two {X : Type} [Group X] [Finite X] {k : ℕ}
    (h : Nat.card X ∣ 2 ^ k) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  have hp : IsPGroup 2 X := IsPGroup.of_card hj
  haveI := hp.isNilpotent
  infer_instance

theorem ringEquiv_eq_refl_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = RingEquiv.refl K := by
  have : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp (le_refl 1) (by rw [hK, pow_one])
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) K) := by
    have hinj : Function.Injective (ZMod.castHom (dvd_refl p) K) :=
      (ZMod.castHom (dvd_refl p) K).injective
    have : Fintype K := Fintype.ofFinite K
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩ |>.2
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  ext x
  obtain ⟨n, rfl⟩ := hsurj x
  have h := RingHom.ext_zmod (σ.toRingHom.comp (ZMod.castHom (dvd_refl p) K))
    (ZMod.castHom (dvd_refl p) K)
  exact congrArg (fun f : ZMod p →+* K => f n) h

section Rows


theorem rowOf143_of_comps {X : Type} [Group X] {q : ℕ} (hq2 : q ≠ 2)
    (hOut : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* X) → Group.IsSolvable (Outer S))
    (hcomps : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → LieCompsExport q β) :
    RowOf143 X := by
  intro S _ _ hs hna hX h3
  exact row143_of_layer hs hna h3 (hOut S hX) fun β hβ hβ1 =>
    layer_three_of_comps lieOrderBridge_holds hq2 (hcomps S hs hna hX β hβ hβ1)

theorem kT1_four_SL (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowOf143 (projSL 4 (GaloisField p 1)) := by
  have hv : (LieTypeIndex.A 3 ⟨p, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def, pow_one]
      omega
  let eX := (Census.typeAGroupEquivProjSL 3 ⟨p, 1, Fact.out, Nat.one_pos⟩ hv).symm
  refine rowOf143_of_comps (q := p) (by omega) (fun S _ _ ⟨e⟩ => ?_)
    fun S _ _ hs hna ⟨e⟩ β hβ hβ1 =>
    lieCompsOn_linearUnitary Nat.prime_three (by norm_num) S hs hna ⟨_, hv⟩ rfl ⟨e.trans eX⟩ β hβ
      hβ1 (Or.inl (by simp [lieIndexChar]; omega))
  · have hd := higher_linear_outer_order_divides_field_gcd_bound (k := GaloisField p 1)
      (Fact.out : p.Prime) le_rfl (by norm_num : 3 ≤ 4)
      (GaloisField.card p 1 one_ne_zero)
    have h8 : 2 * 1 * Nat.gcd 4 (p ^ 1 - 1) ∣ 2 ^ 3 :=
      calc 2 * 1 * Nat.gcd 4 (p ^ 1 - 1) ∣ 2 * 1 * 4 :=
            Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left 4 _)
        _ = 2 ^ 3 := by norm_num
    have hfin : Finite (Outer S) := by
      haveI : Finite (MulAut S) :=
        Finite.of_injective (fun φ : MulAut S => (φ : S → S)) DFunLike.coe_injective
      infer_instance
    refine isSolvable_of_card_dvd_pow_two (k := 3) ?_
    rw [Nat.card_congr
      (equivalence (e.trans (Sec4.projSLEquivProjectiveSL 4 (GaloisField p 1)))).toEquiv]
    exact hd.trans h8

theorem kT1_four_SU (p : ℕ) [Fact p.Prime] (hp : 3 < p) : RowOf143 (projSU 4 p 1) := by
  have hv : (LieTypeIndex.twistedA 3 ⟨p, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_twistedA (by norm_num) (by omega)
  let eX := (Census.typeTwistedAGroupEquivProjSU 3 ⟨p, 1, Fact.out, Nat.one_pos⟩ hv).symm
  refine rowOf143_of_comps (q := p) (by omega) (fun S _ _ ⟨e⟩ => ?_)
    fun S _ _ hs hna ⟨e⟩ β hβ hβ1 =>
    lieCompsOn_linearUnitary Nat.prime_three (by norm_num) S hs hna ⟨_, hv⟩ rfl ⟨e.trans eX⟩ β hβ
      hβ1 (Or.inl (by simp [lieIndexChar]; omega))
  · exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 _ hv (e.trans eX))).2

theorem excRationalLieTypes_holds : ExcRationalLieTypes :=
  excRationalLieTypes_of_residualsD excRationalLieTypesOuterD_proved excRationalLieTypesF4Two_holds

theorem isSolvable_outer_G2 (p : ℕ) [Fact p.Prime] (hp : 3 < p) (q : PrimePower) (hqp : q.p = p)
    (hqe : q.exponent = 1) (hq : (LieTypeIndex.G2 q).Valid) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group) : Group.IsSolvable (Outer S) := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hq
  have hKp : Nat.card K = p ^ 1 := by
    rw [hK, TauCeti.PrimePower.card_def, hqp, hqe]
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
    CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form
      (Fact.out : p.Prime) (by omega) le_rfl K hKp .G2 (Or.inr ⟨rfl, by omega⟩)
  let φ : Outer (adjointGroup Tag.G2 K) ≃* (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  have hsub : ∀ σ : K ≃+* K, σ = 1 := fun σ =>
    ringEquiv_eq_refl_of_card_prime (Fact.out : p.Prime) (by rw [hKp, pow_one]) σ
  have hsol : Group.IsSolvable (Outer (adjointGroup Tag.G2 K)) :=
    Group.isSolvable_of_comm fun a b => φ.injective (by rw [hsub (φ (a * b)), hsub (φ (b * a))])
  let e' : S ≃* adjointGroup Tag.G2 K := e.trans eK
  exact solvable_of_surjective (f := (equivalence e').symm.toMonoidHom)
    (equivalence e').symm.surjective

theorem kT1_four_G2 (p : ℕ) [Fact p.Prime] (hp : 3 < p) (q : PrimePower) (hqp : q.p = p)
    (hqe : q.exponent = 1) (hq : (LieTypeIndex.G2 q).Valid) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  refine rowOf143_of_comps (q := q.p) (by omega)
    (fun S _ _ ⟨e⟩ => isSolvable_outer_G2 p hp q hqp hqe hq e) fun S _ _ hs hna ⟨e⟩ β hβ hβ1 => ?_
  have hlayer : PerfectInLayer β :=
    LieSemisimple.lieSemisimpleCentExceptional S hs hna ⟨_, hq⟩ rfl ⟨e⟩ 3 Nat.prime_three
      (by norm_num) (by simp; omega) β hβ hβ1
  refine (lieCompExport_untw excRationalLieTypes_holds (τ := .G2) (Or.inl rfl)
    (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
    (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
    (fun q hq => by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hq rfl, by simp⟩)
    (fun q hv _ => (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
    (fun q hv => isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl)) q hq (by omega) e β hβ hβ1
    hlayer).toComps

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
