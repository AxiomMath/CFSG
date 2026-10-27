module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] def nine3Dcal (V H₀ : Subgroup G) : Set (Subgroup G) :=
  {D | ∃ h ∈ H₀, D = conjSubgroup V h}

structure Nine3T79Setup (V T A K S X : Subgroup G) (p : ℕ) (g x : G) : Prop where
  hc : Nine3Choice V T A K S X p g x
  hc' : Nine3Choice V T A K S X p g⁻¹ x
  hI : Nine3IFacts V K S
  h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5
  hN : nineH0 V K g ≤ normalizer (nineI0 V K g : Set G)

@[expose] def Nine3Thm79 (V T A K S X : Subgroup G) (p : ℕ) (g x : G) : Prop :=
  Nine3Choice V T A K S X p g x → Nine3Choice V T A K S X p g⁻¹ x → Nine3IFacts V K S →
    (Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) →
    ¬ nineH0 V K g ≤ normalizer (nineI0 V K g : Set G)

abbrev nine3G1 (V K : Subgroup G) (g : G) : Type :=
  ↥(nineH0 V K g) ⧸ fusionOddCore ↥(nineH0 V K g)

@[expose] def nine3BarV (V K : Subgroup G) (g : G) : Subgroup (nine3G1 V K g) :=
  (V.subgroupOf (nineH0 V K g)).map (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))

@[expose] def nine3BarE (V K : Subgroup G) (g : G) : Subgroup (nine3G1 V K g) :=
  ((nineI0 V K g).subgroupOf (nineH0 V K g)).map
    (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))

structure Nine3QuotHyp (H₀ : Subgroup G) {Y : Type} [Group Y] (π : ↥H₀ →* Y) : Prop where
  pcore_le : ∀ k : ↥H₀, (k : G) ∈ pCoreOf 2 H₀ → π k = 1
  two_elt : ∀ k : ↥H₀, π k = 1 → ∀ n : ℕ, orderOf k = 2 ^ n → (k : G) ∈ pCoreOf 2 H₀

@[expose] def IsOrth63ReflectionKer (X : Type) [Group X] (s : X) (O : Subgroup X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧
    ∃ b c : F, (∀ t : F, t ^ 2 + b * t + c ≠ 0) ∧
      ∃ N : Subgroup (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F),
        CFSG.PGLModel.projOmegaMinus 2 F b c ≤ N ∧
          N ≤ (CFSG.PGLModel.orthogonalMinus 2 F b c).map Matrix.ProjGenLinGroup.mk ∧
          ∃ (φ : X →* ↥N), Function.Surjective φ ∧ φ.ker = O ∧ Nat.card O = 3 ∧
            O ≤ center X ∧ ∃ r ∈ CFSG.PGLModel.orthogonalMinus 2 F b c,
              IsRankOneIn r ∧
                ((φ s : ↥N) : Matrix.ProjGenLinGroup _ F) = Matrix.ProjGenLinGroup.mk r

@[expose] def Nine3Classical (X : Type) [Group X] (s : X) (O : Subgroup X) : Prop :=
  (∃ m n : ℕ, IsSymplecticTransvection X m n s ∧ O = center X) ∨
  (∃ m n : ℕ, IsUnitaryTransvection X m n s ∧ O = center X) ∨
  (∃ m n : ℕ, IsOrthReflection X m n s ∧ O = center X) ∨
  (∃ n m : ℕ, IsWreathTransposition X n m s ∧ O = center X) ∨
  (∃ n : ℕ, IsSymTransposition X n s ∧ O = fusionOddCore X) ∨
  IsOrth63ReflectionKer X s O

end CFSG.LocalAnalysis.WeakClosure81
