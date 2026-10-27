module

public import CFSG.Quasithin.Background.C124Offender
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def ResidueRankOne (K V : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 2 ≤ n ∧ Fintype.card F = 2 ^ n ∧
    Nonempty (↥(autOn K V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F)) ∧
    ∃ hV : IsElemAbelian 2 V,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).Realizes (autI hV K)
        (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K))

@[expose] def ResidueRankTwo (K V : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(autOn K V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧
      ∃ hV : IsElemAbelian 2 V,
        ((FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Realizes (autI hV K)
            (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)) ∨
          ∃ (I : Fin 2 → Subgroup (IntMod V hV))
            (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥(autI hV K)),
            iSupIndep I ∧ (⨆ i, I i) = commV (autI hV K) ∧
            ∀ i, (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia
              (autI hV K) (I i) ⊥ π)) ∨
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 2 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(autOn K V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ∃ hV : IsElemAbelian 2 V,
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).Realizes (autI hV K)
          (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K))) ∨
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 2 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(autOn K V) ≃* ↥(quasithinG2 F)) ∧
      ∃ hV : IsElemAbelian 2 V,
        (FFModel.zornQ (quasithinG2 F)).Realizes (autI hV K)
          (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K))) ∨
  (Nonempty (↥(autOn K V) ≃* ↥(alternatingGroup (Fin 6))) ∧
      ∃ hV : IsElemAbelian 2 V,
        AlternatingNatural (autI hV K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) 6) ∨
  (IsHat ↥(autOn K V) ↥(alternatingGroup (Fin 6)) ∧
      ∃ hV : IsElemAbelian 2 V,
        TripleA6Six (autI hV K) (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)))

@[expose] def ResidueRankThree (K V : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    Nonempty (↥(autOn K V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) ∧
    ∃ hV : IsElemAbelian 2 V,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))).Realizes (autI hV K)
          (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)) ∨
        SLExteriorTwo (autI hV K) (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)) n ∨
        SumNatDual (autI hV K) (commV (autI hV K)) n ∨
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ n - 1 ∧
          DirectSumOfCopies (autI hV K) (commV (autI hV K)) ⊥
            (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) k

@[expose] def ResidueTypeI (K V : Subgroup G) : Prop :=
  ResidueRankOne K V ∨ ResidueRankTwo K V ∨ ResidueRankThree K V

noncomputable abbrev jPStar {V : Subgroup G} (hV : IsElemAbelian 2 V) (R K : Subgroup G) :
    Subgroup (MulAut (IntMod V hV)) :=
  ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R))

@[expose] def ResidueTypeII (R K V : Subgroup G) : Prop :=
  ∃ hV : IsElemAbelian 2 V, autI hV (thompsonJ R) ≤ jPStar hV R K ∧
    (∀ T : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf T (jPStar hV R K) →
      jPStar hV R K = autI hV K ⊔ T) ∧
    ((∃ n : ℕ, (n = 6 ∨ n = 8) ∧ ∃ π : Equiv.Perm (Fin n) →* ↥(jPStar hV R K),
        (FFModel.symDn n).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ σ : Equiv.Perm (Fin n),
          ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
            σ ∈ alternatingGroup (Fin n)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
          (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
            (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
          ∀ g : ↥(quasithinG2 F),
            ((π g : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
              (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆))

end CFSG.Quasithin.SmithC27
