module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCharSum
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.RankThree.Classical2
open CFSG.StandardType.OrthTorus

variable {G : Type} [Group G] [Finite G]

section


theorem qtwoDNbr_card_le_orth {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hRig : GGLabelRigidInput) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmarkK : GGInnerDiagOn Bs X) (hperf : commutator ↥X = ⊤) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (hrank : 4 ≤ lab.rank) (hpqA : p ∣ 2 ^ lab.n + 1)
    (htype : (lab.tag = .D ∧ Even lab.rank) ∨ (lab.tag = .twD ∧ Odd lab.rank)) :
    Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) * p ^ lab.rank := by
  classical
  have htag : lab.tag = .D ∨ lab.tag = .twD := htype.imp And.left And.left
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) := GGInnerDiagOn.le_normalizer hmarkK
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, eQ, ρ,
    hcard, -, hT, hdim, hplus, himage, hcompat0⟩ :=
    OrthKExactTwo.exists_quadratic_image_of_orthogonal_marking hRig hp2 hmarkK hBs hSC hΛ hhas
      htag hrank
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  letI : Nontrivial V := hNontrivial
  have hconjq : ∀ (b : ↥Bs) (z : ↥X), (QuotientGroup.mk (ggGamma X hN b z) :
      ↥X ⧸ Subgroup.center ↥X) = ρ b * QuotientGroup.mk z * (ρ b)⁻¹ := by
    intro b z
    apply eQ.injective
    rw [hcompat0 b z, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hker : ∀ b : ↥Bs, ρ b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro b hb
    have hmk : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥X)) :=
      QuotientGroup.mk'_surjective _
    have hmkker : (QuotientGroup.mk' (Subgroup.center ↥X)).ker ≤ Subgroup.center ↥X := by
      rw [QuotientGroup.ker_mk']
    have h1 : ∀ l : ↥X, (1 : MulAut (↥X ⧸ Subgroup.center ↥X))
        (QuotientGroup.mk' (Subgroup.center ↥X) l) =
        QuotientGroup.mk' (Subgroup.center ↥X) (ggGamma X hN b l) := by
      intro l
      have h := hconjq b l
      rw [hb] at h
      simp only [one_mul, inv_one, mul_one] at h
      exact h.symm
    have h2 := (SCFourCover.induced_eq_one_iff hmk hmkker hperf h1).mp rfl
    exact (ggGamma_eq_one_iff X hN b).mp h2
  let σ : (↥X ⧸ Subgroup.center ↥X) ≃* ↥(orthDerived Q) :=
    eQ.trans (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
  let EQ : Subgroup ↥(orthDerived Q) := ρ.range.map σ.toMonoidHom
  let A : Subgroup (V ≃ₗ[F] V) := EQ.map (orthDerived Q).subtype
  have hEimage : IsElemAbelian p EQ ∧
      ∀ g ∈ Subgroup.centralizer (EQ : Set ↥(orthDerived Q)), g ^ p = 1 → g ∈ EQ := by
    simpa [σ, EQ] using himage
  have hcardA : Nat.card A = Nat.card ρ.range := by
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective,
      Subgroup.card_map_of_injective σ.injective]
  have hcardBs : Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) *
      Nat.card ρ.range := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [← h]
    refine Nat.mul_le_mul_right _ ?_
    refine Nat.card_le_card_of_injective
      (fun b : ↥ρ.ker => (⟨((b.1 : ↥Bs) : G), b.1.2, hker b.1 b.2⟩ :
        ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))) ?_
    intro b b' hbb'
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) => (z : G)) hbb'
  by_cases hne : ∃ b ∈ A, b ≠ 1
  · have hAΩ : A ≤ orthDerived Q := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hApow : ∀ a ∈ A, a ^ p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [Subgroup.coe_pow] using congrArg Subtype.val (hEimage.1.2 x hx)
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hEimage.1 hx hy)
    have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
      intro g hg hgp hgc
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      apply hEimage.2 ⟨g, hg⟩
      · intro e he
        exact Subtype.ext (by
          change (e : V ≃ₗ[F] V) * g = g * (e : V ≃ₗ[F] V)
          exact (hgc (e : V ≃ₗ[F] V) ⟨e, he, rfl⟩).symm)
      · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)
    have hpqF : p ∣ Nat.card F + 1 := by rw [hcard]; exact hpqA
    obtain ⟨r, τ, hτinj, hτrange, -, -, -, -⟩ :=
      exists_torus (K := F) (V := V) (Q := Q) (p := p) (A := A) hp2 (Or.inr hpqF) hQ hT hAΩ
        hApow hAcomm hmax hne
    have hdim' : Module.finrank F V = 2 * lab.rank := hdim
    have htype' : (CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Even lab.rank) ∨
        (¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Odd lab.rank) := by
      rcases htype with ⟨hD, heven⟩ | ⟨hM, hodd⟩
      · exact Or.inl ⟨hplus.mpr hD, heven⟩
      · refine Or.inr ⟨?_, hodd⟩
        rw [hplus]
        intro h
        rw [hM] at h
        cases h
    have hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] :=
      charSum_top_modEq_one_of_witt hQ (r := lab.rank) (by omega) hdim' hpqF htype'
    have hfinrank : Module.finrank F V = 2 * r :=
      finrank_eq_two_mul_of_charSum (p := p) hp2 (Or.inr hpqF) hQ hT hAΩ hApow hAcomm hmax hne
        hτinj hτrange hchar
    have hr : r = lab.rank := by omega
    have hcardτ : Nat.card A = p ^ r := by
      rw [← hτrange, Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm, Nat.card_pi]
      simp [Nat.card_zmod]
    calc Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) *
          Nat.card ρ.range := hcardBs
      _ = Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) * p ^ lab.rank := by
        rw [← hcardA, hcardτ, hr]
  · push Not at hne
    have hA1 : Nat.card A = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((hne a.1 a.2).trans (hne b.1 b.2).symm)⟩, ⟨1⟩⟩
    have h1 : Nat.card ρ.range = 1 := hcardA ▸ hA1
    calc Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) *
          Nat.card ρ.range := hcardBs
      _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) * p ^ lab.rank := by
        rw [h1]
        exact Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)

end

end CFSG.StandardType.QTwo

end
