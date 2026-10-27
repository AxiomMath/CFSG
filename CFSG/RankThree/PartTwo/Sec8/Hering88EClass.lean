module

public import CFSG.RankThree.PartTwo.Sec8.Hering88DFinal
import CFSG.RankThree.PartTwo.Sec19.Item19Res7ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KF88Case1ClassB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → Case83One Y x A₀ d' m →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          Nonempty (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m)))

@[expose] def KF88Case1ThreeAExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Odd n' ∧ Case83One Y x A₀ d' n') →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          IsQuasisimple (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) →
          (∃ z : imageModTheta Y
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))),
            (∀ y, z * y = y * z) ∧ z ≠ 1 ∧ z ^ 3 = 1) → False

namespace Hering88E

theorem eq_one_of_central_projSL {k : ℕ} (hk : 2 ≤ k) {z : projSL 2 (GaloisField 2 k)}
    (hz : ∀ y, z * y = y * z) : z = 1 := by
  have h := Item8KFacts3.center_projSL_two_eq_bot hk
  have : z ∈ Subgroup.center (projSL 2 (GaloisField 2 k)) :=
    Subgroup.mem_center_iff.mpr fun y => (hz y).symm
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem kF88Case1ThreeAExcl_of_classB (hB : KF88Case1ClassB) : KF88Case1ThreeAExcl := by
  rintro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hc1⟩ d hdcl hdx hdA hd3 hdN hin
    hne hE _ ⟨z, hzc, hz1, -⟩
  obtain ⟨e⟩ := hB G A c L a b X n h Y hY hIJ x hx hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN
    hin hne hE
  apply hz1
  apply e.injective
  rw [map_one]
  exact eq_one_of_central_projSL (by have := hodd.pos; omega) fun y => by
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hzc y']

theorem kF88Case1ThreeA_of_excl (hE : KF88Case1ThreeAExcl) : KF88Case1ThreeA := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY hc d hdcl hdx hdA hd3 hdN hin hne hEA hq hz
  exact (hE G A c L a b X n h Y hY hIJ x hx hxY hc d hdcl hdx hdA hd3 hdN hin hne hEA hq hz).elim

theorem kF88Case1ThreeA_of_classB (hB : KF88Case1ClassB) : KF88Case1ThreeA :=
  kF88Case1ThreeA_of_excl (kF88Case1ThreeAExcl_of_classB hB)

theorem kF88Case1NontrivOne_of_classB (hB : KF88Case1ClassB) : KF88Case1NontrivOne := by
  intro G _ _ A c L a b X h1 Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hc1⟩ d hdcl hdx hdA hd3 hdN hin
    hne hE
  obtain ⟨e⟩ := hB G A c L a b X 1 h1 Y hY hIJ x hx hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN
    hin hne hE
  haveI := Sec19.Item19Res7Proof.nontrivial_of_isQuasisimple (Item87Proof.isQuasisimple_projSL_two
    (by have := hodd.pos; omega : 2 ≤ 3 * m))
  exact Item83Proof.ne_bot_of_mulEquiv e

theorem kF88Step_of_case1ClassB
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (h83 : Item83) (hF : KF84Field)
    (hB : KF88Case1ClassB) (hL : KF88LinkCoreD83) : KF88Step :=
  Hering88D.kF88Step_of_case1ShapesD83 h45 h84 h83 hF (kF88Case1ThreeA_of_classB hB)
    (kF88Case1NontrivOne_of_classB hB) hL

end Hering88E

end CFSG.RankThree.PartTwo.Sec8
