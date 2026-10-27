module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE

public section

namespace CFSG.StandardType.E6ThreeRootGen

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.E6ThreeModel

private theorem frame_conj_E
    {K : Type} [Field K]
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {L' : Type} [Group L']
    {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)} {A : Subgroup (MulAut L')}
    {ρ ρ' : MulAut L' →* MulAut ↥(adjointGroup Tag.E6 K)}
    {γ : MulAut ↥(adjointGroup Tag.E6 K)}
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hΦ : ∀ a : A, (eFrame K ζ hζ).diag (Φ a) = ρ' a)
    (hconj : ∀ a, γ⁻¹ * ρ' a * γ = ρ a)
    (hρ : ∀ a l, ρ a (ψ₀ l) = ψ₀ (a l)) {g : ModGL Tag.E6 K}
    (hg : ∀ (x : Fin Tag.E6.rank → ZMod 3) (r : ↥(adjointGroup Tag.E6 K)),
      (((γ⁻¹ * NoOffE6Three.diag3 ζ hζ (Multiplicative.ofAdd x) * γ) r :
          ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) * (r : ModGL Tag.E6 K) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹)⁻¹) :
    ∀ (a : A) (l : L'),
      ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (Φ a))) * g⁻¹) *
          ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (Φ a))) * g⁻¹)⁻¹ := by
  intro a l
  have key : (γ⁻¹ * (eFrame K ζ hζ).diag (Φ a) * γ) (ψ₀ l) = ψ₀ ((a : MulAut L') l) := by
    rw [hΦ a, hconj]
    exact hρ a l
  have h2 := hg (Multiplicative.toAdd (Φ a)) (ψ₀ l)
  exact (congrArg Subtype.val key).symm.trans h2

theorem exists_frame_torus_E
    {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hcard : Nat.card ψ₀.ker ∣ 3) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (hatAut Tag.E6 K).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    ∃ (g : ModGL Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L'),
      g ∈ adjointGroup Tag.E6 K ∧ Function.Injective κ ∧
      (κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) ∧
      (∀ (a : A) (l : L'),
        ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹) *
            ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
            (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹)⁻¹) ∧
      (∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T) ∧
      (∀ a ∈ A, ∀ y ∈ T, a y = y) ∧
      (∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
        MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x) ∧
      (∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ u : WeylGroup Tag.E6, ∀ a b : A,
          (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
            Multiplicative.toAdd (κ b) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a))) := by
  haveI : Finite ↥(adjointGroup Tag.E6 K) := Finite.of_surjective ψ₀ hψ₀
  let D : FrameData ↥(adjointGroup Tag.E6 K) := eFrame K ζ hζ
  have hDH : D.H = (hatAut Tag.E6 K).range := rfl
  have hgood : D.Good := eFrame_good hζo hζ
  have hZ : ψ₀.ker = Subgroup.center L' :=
    BstarDesc.ker_eq_center hψ₀ hker (eFrame_center (K := K))
  let ρ : MulAut L' →* MulAut ↥(adjointGroup Tag.E6 K) := BstarDesc.descAut hψ₀ hZ
  have hρ : ∀ a l, ρ a (ψ₀ l) = ψ₀ (a l) := fun a l => BstarDesc.descAut_apply hψ₀ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ₀ hZ hperf
  have hAH' : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφH, hφ⟩ := hAH a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ₀ r
      rw [hρ, hφ]
    rw [hρφ, hDH]
    exact hφH
  obtain ⟨γ, hγH, hγ⟩ := exists_align D hgood.shape hρinj hA h5 hAH'
  let ψ' : L' →* ↥(adjointGroup Tag.E6 K) := γ.toMonoidHom.comp ψ₀
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ₀
  have hkerEq : ψ'.ker = ψ₀.ker := by
    ext l
    simp [ψ', MonoidHom.mem_ker]
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  have hcard' : Nat.card ψ'.ker = 1 ∨ Nat.card ψ'.ker = 3 := by
    have h3 : Nat.card ψ'.ker ∣ 3 := by rw [hkerEq]; exact hcard
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  let ρ' : MulAut L' →* MulAut ↥(adjointGroup Tag.E6 K) :=
    (MulAut.conj γ).toMonoidHom.comp ρ
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := by
    intro a l
    change (MulAut.conj γ (ρ a)) (γ (ψ₀ l)) = γ (ψ₀ (a l))
    rw [MulAut.conj_apply]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hρ a l]
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := fun a => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hρ'inj : Function.Injective ρ' := (MulAut.conj γ).injective.comp hρinj
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := by
    intro a ha
    rw [hρ'eq a]
    exact hγ a ha
  obtain ⟨Φ, hΦ, T, w, ⟨hbody, -⟩, -⟩ :=
    model_odd_of_good_diag D ggAbelianLift hgood hψ' hker' hcard' hρ' hρ'inj hA hsc hal
  obtain ⟨hinj, hrange, -, hTodd, hTfix, -, -, -, hreal, hinner, -, -⟩ := hbody
  have hTodd' : ∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T := by
    intro z hz hodd
    exact hTodd z (by rwa [hkerEq]) hodd
  obtain ⟨g, hgC, hg⟩ := kgFrame_exists_conj_diag (K := K) hζ (hDH ▸ hγH)
  refine ⟨g, Φ, T, hgC, hinj, hrange,
    frame_conj_E hζ hΦ (fun a => by rw [hρ'eq a]; group) hρ hg, hTodd', hTfix, hreal, hinner⟩

end CFSG.StandardType.E6ThreeRootGen

end
