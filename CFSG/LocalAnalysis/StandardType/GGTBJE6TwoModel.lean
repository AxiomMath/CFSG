module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem ggE6Two_model_of_tbGroup {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* TableBExc.RecipeGroup .E6 K)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) L' ψ₀ A) :
    ∃ (e : L' ≃* adjointGroup .E6 K) (E : Subgroup (adjointGroup .E6 K)),
      IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E ∧
      (∀ g : adjointGroup .E6 K, (∀ c ∈ E, g * c = c * g) → g ^ 3 = 1 → g ∈ E) ∧
      A.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, hr, -, hsc⟩ := hA
  have hZL : Subgroup.center L' = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hq
    exact ggCenterPrime_recipe_E6_two hK hq L' ψ₀ hψ0 hker0 hperf0
  have hψ₀inj : Function.Injective ψ₀ :=
    (MonoidHom.ker_eq_bot_iff ψ₀).1 (eq_bot_iff.2 (hker0.trans hZL.le))
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hE₀ab, hcardE₀, hE₀A, hscE₀⟩ :=
    exists_innerModel_recipe_E6 (p := 3) hp
      (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
      (ggCenterPrime_recipe_E6_two hK hp) ψ₀ hψ0 hker0 hperf0 hAe hAI hsc
  let c : TableBExc.RecipeGroup .E6 K ≃* adjointGroup .E6 K := TableBExc.recipeEquiv .E6 K
  set E₀ : Subgroup (TableBExc.RecipeGroup .E6 K) := A.comap Λ with hE₀
  let E : Subgroup (adjointGroup .E6 K) := E₀.map c.toMonoidHom
  have hEab : IsElemAbelian 3 E := hE₀ab.map c.toMonoidHom
  have hcardE : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective c.injective, hcardE₀]
  have hscE : ∀ g : adjointGroup .E6 K, (∀ b ∈ E, g * b = b * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨g₀, rfl⟩ : ∃ g₀, c g₀ = g := ⟨c.symm g, c.apply_symm_apply g⟩
    refine Subgroup.mem_map_of_mem c.toMonoidHom (hscE₀ g₀ (fun b hb => ?_) ?_)
    · have h1 := hg (c b) (Subgroup.mem_map_of_mem c.toMonoidHom hb)
      exact c.injective (by rw [map_mul, map_mul]; exact h1)
    · exact c.injective (by rw [map_pow, hgp, map_one])
  let ψ : L' →* adjointGroup .E6 K := c.toMonoidHom.comp ψ₀
  have hψbij : Function.Bijective ψ := c.bijective.comp ⟨hψ₀inj, hψ0⟩
  let eL : L' ≃* adjointGroup .E6 K := MulEquiv.ofBijective ψ hψbij
  have heL : ∀ x, eL x = c (ψ₀ x) := fun x => rfl
  have hcomp : (MulAut.congr eL).toMonoidHom.comp Λ =
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).comp c.toMonoidHom := by
    refine MonoidHom.ext fun r => MulEquiv.ext fun l' => ?_
    obtain ⟨l, rfl⟩ := eL.surjective l'
    change eL (Λ r (eL.symm (eL l))) = c r * eL l * (c r)⁻¹
    rw [MulEquiv.symm_apply_apply]
    simp only [heL, hΛmap, map_mul, map_inv]
  have hAE : A.map (MulAut.congr eL).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) := by
    calc A.map (MulAut.congr eL).toMonoidHom
        = ((A.comap Λ).map Λ).map (MulAut.congr eL).toMonoidHom := by rw [hE₀A]
      _ = (A.comap Λ).map ((MulAut.congr eL).toMonoidHom.comp Λ) := Subgroup.map_map _ _ _
      _ = (A.comap Λ).map ((MulAut.conj : adjointGroup .E6 K →*
            MulAut (adjointGroup .E6 K)).comp c.toMonoidHom) := by rw [hcomp]
      _ = E.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) :=
            (Subgroup.map_map _ _ _).symm
  exact ⟨eL, E, hEab, by rw [hcardE]; exact hr, hscE, hAE⟩

theorem ggE6Two_model_of_innerDiag (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (hI : GGInnerDiagOn Bs X)
    (hX : GGHasLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hTB : commutator ↥X = ⊤ → ∀ {R : Type} [Group R] {I : Set (MulAut R)}
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I) → GGTorusLift 3 4 R →
        GGTorusTBGroup 3 4 R I X (ggQuotHom θ) (ggGamma X hN).range) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ∧
      ∃ (e : ↥X ≃* adjointGroup .E6 Fq) (E : Subgroup (adjointGroup .E6 Fq)),
        IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E6 Fq, (∀ c ∈ E, g * c = c * g) → g ^ 3 = 1 → g ∈ E) ∧
        (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E6 Fq →* MulAut (adjointGroup .E6 Fq)) := by
  classical
  have hΛ : LargeEvenInLambda2 (⟨.E6, 0, 1⟩ : LargeEvenLabel) := ⟨le_refl 1, rfl⟩
  obtain ⟨hperf, lab, _hlab, hraw⟩ := ggInnerDiagOn_relabel hRig hI hΛ hX
  obtain ⟨_, _, _, _, _, _, _, hEq, _, _⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  obtain ⟨Fq, _instFq, _finFq, hFqcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hN, hBsI⟩ := hQ
  haveI : CharP Fq 2 := charP_two_of_card hFqcard
  have hK : Nat.card Fq = 2 := by simpa using hFqcard
  have hlift : GGTorusLift 3 4 (TableBExc.RecipeGroup .E6 Fq) :=
    TableBExc.E6Three.ggTorusLift_E6_two
  have hTB' := hTB hperf θ hN (fun b hb => ggLAut_mem_of_induces X θ hN hBsI hb) hlift
  obtain ⟨e, E, hEab, h4, hsc, hAE⟩ := ggE6Two_model_of_tbGroup hK (ggQuotHom θ) _ hTB'
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, hK, e, E, hEab, h4, hsc, hAE⟩

theorem ggE6Two_model_L (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGHasLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L)) (hp3 : p = 3) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ∧
      ∃ (e : ↥L ≃* adjointGroup .E6 Fq) (E : Subgroup (adjointGroup .E6 Fq)),
        IsElemAbelian p E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E6 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E6 Fq →* MulAut (adjointGroup .E6 Fq)) := by
  subst hp3
  exact ggE6Two_model_of_innerDiag hRig hH.2.2.1.1 hL
    fun hperf {R} _ {I} θ hN hBsI hlift => ggTorusTBGroup_of_L hH.1 hperf θ hN hBsI hlift

theorem ggE6Two_model_K (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGHasLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K)) (hp3 : p = 3) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ∧
      ∃ (e : ↥K ≃* adjointGroup .E6 Fq) (E : Subgroup (adjointGroup .E6 Fq)),
        IsElemAbelian p E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E6 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E6 Fq →* MulAut (adjointGroup .E6 Fq)) := by
  subst hp3
  exact ggE6Two_model_of_innerDiag hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hK
    fun hperf {R} _ {I} θ hN hBsI hlift =>
      ggTorusTBGroup_of_nbr hH.1 hH.2.2.2.2.1 hperf θ hN hBsI hlift

end CFSG.StandardType

end
