module

public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveFinite
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.OmNonsplit CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

@[expose] def E8TwoFiveSetup
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    (a : Fin Tag.E8.rank → Lˣ) : Prop :=
  S.D.q = 2 ∧ rootDiagUnit Tag.E8 a ∈ S.D.torus ∧ rootDiagUnit Tag.E8 a ∈ S.Γ ∧
    (∀ i, a i ^ 5 = 1) ∧ rootDiagUnit Tag.E8 a ≠ 1

@[expose] def E8TwoFiveKernelA {L : Type} [Field L] (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) : Prop :=
  (kernelRoots χ).ncard = 40 ∧
    ∃ i₁ i₂ : KernelComponent χ, i₁ ≠ i₂ ∧ (∀ i, i = i₁ ∨ i = i₂) ∧
      compRank (componentRoots χ i₁) = 4 ∧ (componentRoots χ i₁).ncard = 20 ∧
      (ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots χ i₁ = componentRoots χ i₂ ∧
      twistKind ρ χ i₁ = .suN

@[expose] def E8TwoFiveKernelB {L : Type} [Field L] (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) : Prop :=
  (kernelRoots χ).ncard = 60 ∧
    ∃ i : KernelComponent χ, (∀ j, j = i) ∧ compRank (componentRoots χ i) = 6 ∧
      (componentRoots χ i).ncard = 60 ∧ twistKind ρ χ i = .twoD

private def IsConnIn (P : Set (Fin Tag.E8.rank → ℤ)) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P,
    Relation.EqvGen (fun a b : Fin Tag.E8.rank → ℤ => a ∈ P ∧ b ∈ P ∧ iform a b ≠ 0) x y

private def IsFrobLike (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (μ : Fin 8 → ℤ) : Prop :=
  (∀ γ, IsRoot Tag.E8 (σ γ) ↔ IsRoot Tag.E8 γ) ∧ (∀ γ δ, iform (σ γ) (σ δ) = iform γ δ) ∧
    ∀ δ, IsRoot Tag.E8 δ → (σ δ ⬝ᵥ μ) ≡ 2 * (δ ⬝ᵥ μ) [ZMOD 5]

private noncomputable def conjPerm (w : WeylGroup Tag.E8) (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) :
    Equiv.Perm (Fin Tag.E8.rank → ℤ) :=
  (MulAction.toPerm w⁻¹).trans (ρ.trans (MulAction.toPerm w))

private theorem conjPerm_smul (w : WeylGroup Tag.E8) (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (x : Fin Tag.E8.rank → ℤ) : conjPerm w ρ (w • x) = w • ρ x := by
  simp [conjPerm]

private def WeylConj {L : Type} [Field L] (w : WeylGroup Tag.E8)
    (ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) : Prop :=
  (∀ x, ρ' (w • x) = w • ρ x) ∧
    ∀ β, χ (Multiplicative.ofAdd β) = χ₀ (Multiplicative.ofAdd (w • β))

private theorem exists_primRoot5
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) :
    ∃ ζ : Lˣ, IsPrimitiveRoot (ζ : L) 5 := by
  have h5 : ((5 : ℕ) : L) ≠ 0 := by
    intro h
    have hcop : IsCoprime ((5 : ℕ) : ℤ) ((S.D.q : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 S.hpq)
    have h1 := hcop.map (Int.castRingHom L)
    simp only [eq_intCast, Int.cast_natCast] at h1
    rw [h, S.hqpow.2] at h1
    exact not_isUnit_zero (isCoprime_zero_left.1 h1)
  haveI : NeZero ((5 : ℕ) : L) := ⟨h5⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  exact ⟨hu.unit, by simpa using hζ⟩

private theorem kernelRoots_zeta {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) 5)
    (μ : Fin 8 → ℤ) :
    kernelRoots (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ μ i)) =
      {α | IsRoot Tag.E8 α ∧ (5 : ℤ) ∣ α ⬝ᵥ μ} := by
  have hζ' : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.coe_units_iff.1 hζ
  ext α
  let lam : Fin Tag.E8.rank → ℤ := μ
  have hkey : rootChar (fun i : Fin Tag.E8.rank => ζ ^ μ i) α = ζ ^ (α ⬝ᵥ μ) := by
    have h := KacData.rootChar_eq_zpow ζ lam α
    simpa [lam] using h
  rw [kernelRoots_rootCharHom]
  constructor
  · rintro ⟨hroot, h1⟩
    refine ⟨hroot, ?_⟩
    have hz : ζ ^ (α ⬝ᵥ μ) = 1 := hkey ▸ h1
    exact (hζ'.zpow_eq_one_iff_dvd (α ⬝ᵥ μ)).mp hz
  · rintro ⟨hroot, hdvd⟩
    refine ⟨hroot, ?_⟩
    have hz : ζ ^ (α ⬝ᵥ μ) = 1 := (hζ'.zpow_eq_one_iff_dvd (α ⬝ᵥ μ)).mpr hdvd
    exact hkey.symm ▸ hz

private theorem kg_eqvGen_of_conn {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) (P : Set (Fin Tag.E8.rank → ℤ))
    (hPK : P ⊆ kernelRoots χ) (hc : IsConnIn P)
    {x y : Fin Tag.E8.rank → ℤ} (hx : x ∈ P) (hy : y ∈ P) :
    Relation.EqvGen (fun a b : kernelRoots χ =>
        (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
          (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0)
      ⟨x, hPK hx⟩ ⟨y, hPK hy⟩ := by
  have keymem : ∀ a b : Fin Tag.E8.rank → ℤ,
      Relation.EqvGen (fun a b : Fin Tag.E8.rank → ℤ => a ∈ P ∧ b ∈ P ∧ iform a b ≠ 0) a b →
      (a ∈ P ↔ b ∈ P) := by
    intro a b hab
    induction hab with
    | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2
  have key : ∀ a b : Fin Tag.E8.rank → ℤ,
      Relation.EqvGen (fun a b : Fin Tag.E8.rank → ℤ => a ∈ P ∧ b ∈ P ∧ iform a b ≠ 0) a b →
      ∀ (ha : a ∈ P) (hb : b ∈ P),
        Relation.EqvGen (fun a b : kernelRoots χ =>
            (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
              (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0)
          ⟨a, hPK ha⟩ ⟨b, hPK hb⟩ := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      intro ha hb
      exact Relation.EqvGen.rel _ _ (by
        rw [dotProduct_mulVec_eq_iform]
        exact hab.2.2)
    | refl a => intro ha hb; exact Relation.EqvGen.refl _
    | symm a b hab ih =>
      intro hb ha
      exact (ih ha hb).symm
    | trans a b c hab hbc ih1 ih2 =>
      intro ha hc
      have hb : b ∈ P := (keymem a b hab).mp ha
      trans ⟨b, hPK hb⟩
      · exact ih1 ha hb
      · exact ih2 hb hc
  exact key x y (hc x hx y hy) hx hy

private theorem two_components
    {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) (P₁ P₂ : Set (Fin Tag.E8.rank → ℤ))
    (hK : kernelRoots χ = P₁ ∪ P₂) (hd : Disjoint P₁ P₂) (h₁ : P₁.Nonempty) (h₂ : P₂.Nonempty)
    (horth : ∀ x ∈ P₁, ∀ y ∈ P₂, iform x y = 0) (hc₁ : IsConnIn P₁) (hc₂ : IsConnIn P₂) :
    ∃ i₁ i₂ : KernelComponent χ, i₁ ≠ i₂ ∧ (∀ i, i = i₁ ∨ i = i₂) ∧
      componentRoots χ i₁ = P₁ ∧ componentRoots χ i₂ = P₂ := by
  have hPK₁ : P₁ ⊆ kernelRoots χ := fun a ha => by rw [hK]; exact Or.inl ha
  have hPK₂ : P₂ ⊆ kernelRoots χ := fun a ha => by rw [hK]; exact Or.inr ha
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  let i₁ : KernelComponent χ := ⟦⟨x₁, hPK₁ hx₁⟩⟧
  let i₂ : KernelComponent χ := ⟦⟨x₂, hPK₂ hx₂⟩⟧
  have key₁ : ∀ a b : kernelRoots χ,
      Relation.EqvGen (fun a b : kernelRoots χ =>
          (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
            (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0) a b →
      (a.1 ∈ P₁ ↔ b.1 ∈ P₁) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      rw [dotProduct_mulVec_eq_iform] at hxy
      constructor
      · intro hx
        by_contra hy
        have hy2 : y.1 ∈ P₂ := by
          rcases (Set.mem_union y.1 P₁ P₂).mp (by rw [← hK]; exact y.2) with h | h
          · exact absurd h hy
          · exact h
        exact hxy (horth x.1 hx y.1 hy2)
      · intro hy
        by_contra hx
        have hx2 : x.1 ∈ P₂ := by
          rcases (Set.mem_union x.1 P₁ P₂).mp (by rw [← hK]; exact x.2) with h | h
          · exact absurd h hx
          · exact h
        exact hxy (by rw [iform_comm]; exact horth y.1 hy x.1 hx2)
    | refl x => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2
  have key₂ : ∀ a b : kernelRoots χ,
      Relation.EqvGen (fun a b : kernelRoots χ =>
          (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
            (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0) a b →
      (a.1 ∈ P₂ ↔ b.1 ∈ P₂) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      rw [dotProduct_mulVec_eq_iform] at hxy
      constructor
      · intro hx
        by_contra hy
        have hy1 : y.1 ∈ P₁ := by
          rcases (Set.mem_union y.1 P₁ P₂).mp (by rw [← hK]; exact y.2) with h | h
          · exact h
          · exact absurd h hy
        exact hxy (by rw [iform_comm]; exact horth y.1 hy1 x.1 hx)
      · intro hy
        by_contra hx
        have hx1 : x.1 ∈ P₁ := by
          rcases (Set.mem_union x.1 P₁ P₂).mp (by rw [← hK]; exact x.2) with h | h
          · exact h
          · exact absurd h hx
        exact hxy (horth x.1 hx1 y.1 hy)
    | refl x => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2
  have hcomp₁ : componentRoots χ i₁ = P₁ := by
    ext y
    constructor
    · rintro ⟨hy, hyl⟩
      exact (key₁ ⟨y, hy⟩ ⟨x₁, hPK₁ hx₁⟩ (Quotient.exact hyl)).mpr hx₁
    · intro hy
      exact ⟨hPK₁ hy, (Quotient.sound (kg_eqvGen_of_conn χ P₁ hPK₁ hc₁ hx₁ hy)).symm⟩
  have hcomp₂ : componentRoots χ i₂ = P₂ := by
    ext y
    constructor
    · rintro ⟨hy, hyl⟩
      exact (key₂ ⟨y, hy⟩ ⟨x₂, hPK₂ hx₂⟩ (Quotient.exact hyl)).mpr hx₂
    · intro hy
      exact ⟨hPK₂ hy, (Quotient.sound (kg_eqvGen_of_conn χ P₂ hPK₂ hc₂ hx₂ hy)).symm⟩
  have hi : i₁ ≠ i₂ := by
    intro heq
    have hx₂ : x₁ ∈ P₂ := by
      have hx' : x₁ ∈ componentRoots χ i₁ := hcomp₁.symm ▸ hx₁
      rw [heq, hcomp₂] at hx'
      exact hx'
    exact hd.le_bot ⟨hx₁, hx₂⟩
  have hall : ∀ i, i = i₁ ∨ i = i₂ := by
    intro i
    refine Quotient.inductionOn i fun y => ?_
    by_cases hy : y.1 ∈ P₁
    · left
      have hyc : y.1 ∈ componentRoots χ i₁ := hcomp₁.symm ▸ hy
      obtain ⟨h, hh⟩ := hyc
      rw [show y = ⟨y.1, h⟩ from Subtype.ext rfl]
      exact hh
    · right
      have hy2 : y.1 ∈ P₂ := by
        rcases (Set.mem_union y.1 P₁ P₂).mp (by rw [← hK]; exact y.2) with h | h
        · exact absurd h hy
        · exact h
      have hyc : y.1 ∈ componentRoots χ i₂ := hcomp₂.symm ▸ hy2
      obtain ⟨h, hh⟩ := hyc
      rw [show y = ⟨y.1, h⟩ from Subtype.ext rfl]
      exact hh
  exact ⟨i₁, i₂, hi, hall, hcomp₁, hcomp₂⟩

private theorem one_component {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) (P : Set (Fin Tag.E8.rank → ℤ))
    (hK : kernelRoots χ = P) (h : P.Nonempty) (hc : IsConnIn P) :
    ∃ i : KernelComponent χ, (∀ j, j = i) ∧ componentRoots χ i = P := by
  have hPK : P ⊆ kernelRoots χ := fun a ha => by rw [hK]; exact ha
  obtain ⟨x, hx⟩ := h
  let i : KernelComponent χ := ⟦⟨x, hPK hx⟩⟧
  have key : ∀ a b : kernelRoots χ,
      Relation.EqvGen (fun a b : kernelRoots χ =>
          (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
            (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0) a b →
      (a.1 ∈ P ↔ b.1 ∈ P) := by
    intro a b hab
    induction hab with
    | rel x y hxy => exact ⟨fun _ => hK ▸ y.2, fun _ => hK ▸ x.2⟩
    | refl x => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2
  have hcomp : componentRoots χ i = P := by
    ext y
    constructor
    · rintro ⟨hy, hyl⟩
      exact hK ▸ hy
    · intro hy
      exact ⟨hPK hy, (Quotient.sound (kg_eqvGen_of_conn χ P hPK hc hx hy)).symm⟩
  refine ⟨i, ?_, hcomp⟩
  intro j
  refine Quotient.inductionOn j fun y => ?_
  have hy : y.1 ∈ P := hK ▸ y.2
  have hyc : y.1 ∈ componentRoots χ i := hcomp.symm ▸ hy
  obtain ⟨h, hh⟩ := hyc
  rw [show y = ⟨y.1, h⟩ from Subtype.ext rfl]
  exact hh

private theorem orbitLength_swap (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (P₁ P₂ : Set (Fin Tag.E8.rank → ℤ)) (h₁₂ : σ '' P₁ = P₂) (h₂₁ : σ '' P₂ = P₁)
    (hne : P₁ ≠ P₂) : componentOrbitLength σ P₁ = 2 := by
  unfold componentOrbitLength
  have h2 : 2 ∈ {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P₁ = P₁} := by
    refine ⟨by norm_num, ?_⟩
    have h2it : (σ : (Fin Tag.E8.rank → ℤ) → _)^[2] = σ ∘ σ := by
      simpa [Function.iterate_one] using Function.iterate_succ' (σ : (Fin Tag.E8.rank → ℤ) → _) 1
    rw [h2it, Set.image_comp, h₁₂, h₂₁]
  have hne' : ({s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P₁ = P₁}).Nonempty :=
    ⟨2, h2⟩
  have hle : sInf {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P₁ = P₁} ≤ 2 :=
    Nat.sInf_le h2
  refine le_antisymm hle ?_
  have hmem := Nat.sInf_mem hne'
  have hp : 0 < sInf {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P₁ = P₁} := hmem.1
  have hp1 : sInf {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P₁ = P₁} ≠ 1 := by
    intro h
    have h1 : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P₁ = P₁} :=
      h ▸ hmem
    rw [Set.mem_setOf_eq, Function.iterate_one] at h1
    exact hne (h1.2.symm.trans h₁₂)
  omega

private theorem orbitLength_fix (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (P : Set (Fin Tag.E8.rank → ℤ)) (h : σ '' P = P) : componentOrbitLength σ P = 1 := by
  unfold componentOrbitLength
  have h1 : 1 ∈ {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P = P} := by
    refine ⟨by norm_num, ?_⟩
    rw [Function.iterate_one]
    exact h
  have hne' : ({s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P = P}).Nonempty :=
    ⟨1, h1⟩
  have hle := Nat.sInf_le h1
  have hp : 0 < sInf {s : ℕ | 0 < s ∧ (σ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' P = P} :=
    (Nat.sInf_mem hne').1
  omega

private theorem twistKind_suN {L : Type} [Field L] (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (P : Set (Fin Tag.E8.rank → ℤ)) (hP : componentRoots χ i = P)
    (hs : componentOrbitLength σ P = 2) (hrk : compRank P = 4) (hcard : P.ncard = 20)
    (hni : ¬ twistInner P ((σ : (Fin Tag.E8.rank → ℤ) → _)^[2])) : twistKind σ χ i = .suN := by
  have hc1 : ¬ twistInner (componentRoots χ i)
      ((σ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength σ (componentRoots χ i)]) := by
    rw [hP, hs]
    exact hni
  have hc2 : ¬ ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((σ : (Fin Tag.E8.rank → ℤ) → _)^[
            2 * componentOrbitLength σ (componentRoots χ i)]))) := by
    rw [hP, hs, hrk, hcard]
    rintro (⟨h, _⟩ | ⟨_, h, _⟩) <;> omega
  have hc3 : ¬ (4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) - 1)) := by
    rw [hP, hrk, hcard]
    rintro ⟨_, h⟩
    norm_num at h
  have hc4 : 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) + 1) := by
    rw [hP, hrk, hcard]
    norm_num
  unfold twistKind
  rw [if_neg hc1, if_neg hc2, if_neg hc3, if_pos hc4]

private theorem twistKind_twoD {L : Type} [Field L] (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (P : Set (Fin Tag.E8.rank → ℤ)) (hP : componentRoots χ i = P)
    (hs : componentOrbitLength σ P = 1) (hrk : compRank P = 6) (hcard : P.ncard = 60)
    (hni : ¬ twistInner P (σ : (Fin Tag.E8.rank → ℤ) → _)) : twistKind σ χ i = .twoD := by
  have hc1 : ¬ twistInner (componentRoots χ i)
      ((σ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength σ (componentRoots χ i)]) := by
    rw [hP, hs, Function.iterate_one]
    exact hni
  have hc2 : ¬ ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((σ : (Fin Tag.E8.rank → ℤ) → _)^[
            2 * componentOrbitLength σ (componentRoots χ i)]))) := by
    rw [hP, hs, hrk, hcard]
    rintro (⟨_, h⟩ | ⟨h, _⟩) <;> omega
  have hc3 : 4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) - 1) := by
    rw [hP, hrk, hcard]
    norm_num
  unfold twistKind
  rw [if_neg hc1, if_neg hc2, if_pos hc3]

private theorem WeylConj.kernelRoots_eq
    {L : Type} [Field L] {w : WeylGroup Tag.E8} {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀) :
    kernelRoots χ₀ = (fun x => w • x) '' kernelRoots χ := by
  ext y
  constructor
  · intro hy
    refine ⟨w⁻¹ • y, ⟨?_, ?_⟩, ?_⟩
    · exact (isRoot_smul_iff w).1 (by simpa using hy.1)
    · rw [h.2, smul_inv_smul]
      exact hy.2
    · exact smul_inv_smul w y
  · rintro ⟨x, hx, rfl⟩
    refine ⟨IsRoot.smul hx.1 w, ?_⟩
    rw [← h.2]
    exact hx.2

private theorem kg_eqvGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b ↔ s (f a) (f b)) :
    ∀ a b, Relation.EqvGen r a b → Relation.EqvGen s (f a) (f b) := by
  intro a b hab
  induction hab with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ ((h x y).mp hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ih1 ih2 =>
    trans (f y)
    · exact ih1
    · exact ih2

private theorem WeylConj.component_equiv
    {L : Type} [Field L] {w : WeylGroup Tag.E8}
    {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀) :
    ∃ e : KernelComponent χ ≃ KernelComponent χ₀,
      ∀ i, componentRoots χ₀ (e i) = (fun x => w • x) '' componentRoots χ i := by
  have hmemF : ∀ a : kernelRoots χ, w • (a : Fin Tag.E8.rank → ℤ) ∈ kernelRoots χ₀ := by
    intro a
    rw [WeylConj.kernelRoots_eq h]
    exact ⟨(a : Fin Tag.E8.rank → ℤ), a.2, rfl⟩
  have hmemG : ∀ b : kernelRoots χ₀, w⁻¹ • (b : Fin Tag.E8.rank → ℤ) ∈ kernelRoots χ := by
    intro b
    refine ⟨?_, ?_⟩
    · exact (isRoot_smul_iff w⁻¹).2 b.2.1
    · rw [h.2, smul_inv_smul]
      exact b.2.2
  let F : kernelRoots χ ≃ kernelRoots χ₀ :=
    { toFun := fun a => ⟨w • (a : Fin Tag.E8.rank → ℤ), hmemF a⟩
      invFun := fun b => ⟨w⁻¹ • (b : Fin Tag.E8.rank → ℤ), hmemG b⟩
      left_inv := fun a => Subtype.ext (inv_smul_smul w (a : Fin Tag.E8.rank → ℤ))
      right_inv := fun b => Subtype.ext (smul_inv_smul w (b : Fin Tag.E8.rank → ℤ)) }
  have hpoint : ∀ a b : kernelRoots χ,
      (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
          (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0 ↔
        (F a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
          (Matrix.mulVec Tag.E8.symmetrizedCartan (F b : Fin Tag.E8.rank → ℤ)) ≠ 0 := by
    intro a b
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform]
    have h1 : (F a : Fin Tag.E8.rank → ℤ) = w • (a : Fin Tag.E8.rank → ℤ) := rfl
    have h2 : (F b : Fin Tag.E8.rank → ℤ) = w • (b : Fin Tag.E8.rank → ℤ) := rfl
    rw [h1, h2, iform_smul]
  have hpointG : ∀ c d : kernelRoots χ₀,
      (c : Fin Tag.E8.rank → ℤ) ⬝ᵥ
          (Matrix.mulVec Tag.E8.symmetrizedCartan (d : Fin Tag.E8.rank → ℤ)) ≠ 0 ↔
        (F.symm c : Fin Tag.E8.rank → ℤ) ⬝ᵥ
          (Matrix.mulVec Tag.E8.symmetrizedCartan (F.symm d : Fin Tag.E8.rank → ℤ)) ≠ 0 := by
    intro c d
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform]
    have h1 : (F.symm c : Fin Tag.E8.rank → ℤ) = w⁻¹ • (c : Fin Tag.E8.rank → ℤ) := rfl
    have h2 : (F.symm d : Fin Tag.E8.rank → ℤ) = w⁻¹ • (d : Fin Tag.E8.rank → ℤ) := rfl
    rw [h1, h2, iform_smul]
  have hEq : ∀ a b : kernelRoots χ,
      (kernelRootSetoid χ).r a b ↔ (kernelRootSetoid χ₀).r (F a) (F b) := by
    intro a b
    constructor
    · intro h'
      exact kg_eqvGen_map F (fun a b => hpoint a b) a b h'
    · intro h'
      have h'' : Relation.EqvGen (fun a b : kernelRoots χ =>
          (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
            (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0)
          (F.symm (F a)) (F.symm (F b)) :=
        kg_eqvGen_map F.symm (fun c d => hpointG c d) (F a) (F b) h'
      have h''' : Relation.EqvGen (fun a b : kernelRoots χ =>
          (a : Fin Tag.E8.rank → ℤ) ⬝ᵥ
            (Matrix.mulVec Tag.E8.symmetrizedCartan (b : Fin Tag.E8.rank → ℤ)) ≠ 0) a b := by
        simpa [Equiv.symm_apply_apply] using h''
      exact h'''
  have key : ∀ a b : kernelRoots χ,
      (⟦F b⟧ : KernelComponent χ₀) = ⟦F a⟧ ↔ (⟦b⟧ : KernelComponent χ) = ⟦a⟧ := by
    intro a b
    constructor
    · intro hh
      exact (Quotient.congr F hEq).injective (by
        rw [Quotient.congr_mk, Quotient.congr_mk, hh])
    · intro hh
      rw [← Quotient.congr_mk F hEq b, ← Quotient.congr_mk F hEq a, hh]
  refine ⟨Quotient.congr F hEq, ?_⟩
  intro i
  refine Quotient.inductionOn i fun a => ?_
  rw [Quotient.congr_mk]
  apply Set.ext
  intro y
  constructor
  · rintro ⟨hy, hyi⟩
    refine ⟨w⁻¹ • y, ⟨hmemG ⟨y, hy⟩, ?_⟩, ?_⟩
    · apply (key a ⟨w⁻¹ • y, hmemG ⟨y, hy⟩⟩).1
      have hFeq : F ⟨w⁻¹ • y, hmemG ⟨y, hy⟩⟩ = ⟨y, hy⟩ :=
        Subtype.ext (by
          change w • (w⁻¹ • y) = y
          exact smul_inv_smul w y)
      rw [hFeq, hyi]
    · exact smul_inv_smul w y
  · rintro ⟨x, ⟨hx, hxi⟩, hxy⟩
    subst y
    refine ⟨hmemF ⟨x, hx⟩, ?_⟩
    exact (key a ⟨x, hx⟩).2 hxi

private noncomputable def kg_weylLin (w : WeylGroup Tag.E8) :
    (Fin Tag.E8.rank → ℚ) →ₗ[ℚ] (Fin Tag.E8.rank → ℚ) :=
  Matrix.toLin' (Matrix.of fun i j =>
    (((w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) i : ℤ) : ℚ))

private theorem kg_weylLin_apply (w : WeylGroup Tag.E8) (γ : Fin Tag.E8.rank → ℤ) :
    kg_weylLin w (fun i => (γ i : ℚ)) = fun i => ((w • γ) i : ℚ) := by
  have hγ : γ = ∑ j, γ j • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • γ = ∑ j, γ j • (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by
    conv_lhs => rw [hγ]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm w (γ j) _
  funext i
  rw [kg_weylLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hw]
  simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem kg_compRank_image_le (w : WeylGroup Tag.E8) (Ψ : Set (Fin Tag.E8.rank → ℤ)) :
    compRank ((fun α => w • α) '' Ψ) ≤ compRank Ψ := by
  unfold compRank
  have h : (fun γ (i : Fin Tag.E8.rank) => (γ i : ℚ)) '' ((fun α => w • α) '' Ψ) =
      kg_weylLin w '' ((fun γ (i : Fin Tag.E8.rank) => (γ i : ℚ)) '' Ψ) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun γ _ => (kg_weylLin_apply w γ).symm
  rw [h, Submodule.span_image]
  exact Submodule.finrank_map_le _ _

private theorem compRank_smul_image (w : WeylGroup Tag.E8) (P : Set (Fin Tag.E8.rank → ℤ)) :
    compRank ((fun x => w • x) '' P) = compRank P := by
  refine le_antisymm (kg_compRank_image_le w P) ?_
  have h := kg_compRank_image_le w⁻¹ ((fun x => w • x) '' P)
  rwa [Set.image_image, show (fun x => w⁻¹ • w • x) = id from funext fun x => inv_smul_smul w x,
    Set.image_id] at h

private theorem WeylConj.orbitLength_eq {L : Type} [Field L] {w : WeylGroup Tag.E8}
    {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀)
    (P : Set (Fin Tag.E8.rank → ℤ)) :
    componentOrbitLength ρ' ((fun x => w • x) '' P) = componentOrbitLength ρ P := by
  have hiter : ∀ (s : ℕ) (Q : Set (Fin Tag.E8.rank → ℤ)),
      (ρ' : (Fin Tag.E8.rank → ℤ) → _)^[s] '' ((fun x => w • x) '' Q) =
        (fun x => w • x) '' ((ρ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' Q) := by
    intro s
    induction s with
    | zero => intro Q; simp
    | succ s ih =>
      intro Q
      have hs' : (ρ' : (Fin Tag.E8.rank → ℤ) → _)^[s + 1] =
          ρ' ∘ (ρ' : (Fin Tag.E8.rank → ℤ) → _)^[s] := by
        simpa [Function.iterate_one] using
          Function.iterate_succ' (ρ' : (Fin Tag.E8.rank → ℤ) → _) s
      have hs : (ρ : (Fin Tag.E8.rank → ℤ) → _)^[s + 1] =
          ρ ∘ (ρ : (Fin Tag.E8.rank → ℤ) → _)^[s] := by
        simpa [Function.iterate_one] using
          Function.iterate_succ' (ρ : (Fin Tag.E8.rank → ℤ) → _) s
      have himg : ∀ R : Set (Fin Tag.E8.rank → ℤ),
          (ρ' : (Fin Tag.E8.rank → ℤ) → _) '' ((fun x => w • x) '' R) =
            (fun x => w • x) '' ((ρ : (Fin Tag.E8.rank → ℤ) → _) '' R) := by
        intro R
        rw [← Set.image_comp, ← Set.image_comp]
        congr 1
        funext x
        exact h.1 x
      rw [hs', hs, Set.image_comp, Set.image_comp, ih, himg]
  unfold componentOrbitLength
  congr 1
  ext s
  constructor
  · rintro ⟨hpos, hs⟩
    exact ⟨hpos, Set.image_injective.2 (MulAction.injective w) (by rwa [hiter s P] at hs)⟩
  · rintro ⟨hpos, hs⟩
    exact ⟨hpos, by rw [hiter s P, hs]⟩

private theorem kg_rootReflection_smul
    (w : WeylGroup Tag.E8) (γ : Fin Tag.E8.rank → ℤ) :
    rootReflection (w • γ) = w * rootReflection γ * w⁻¹ := by
  by_cases hγ : IsRoot Tag.E8 γ
  · exact rootReflection_smul_root w hγ
  · have hwγ : ¬ IsRoot Tag.E8 (w • γ) := fun hh => hγ ((isRoot_smul_iff w).1 hh)
    simp [rootReflection, hγ, hwγ]

private theorem WeylConj.twistInner_iff
    {L : Type} [Field L] {w : WeylGroup Tag.E8}
    {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀)
    (P : Set (Fin Tag.E8.rank → ℤ)) (n : ℕ) :
    twistInner ((fun x => w • x) '' P) ((ρ' : (Fin Tag.E8.rank → ℤ) → _)^[n]) ↔
      twistInner P ((ρ : (Fin Tag.E8.rank → ℤ) → _)^[n]) := by
  have hiter : ∀ (m : ℕ) (x : Fin Tag.E8.rank → ℤ),
      (ρ' : (Fin Tag.E8.rank → ℤ) → _)^[m] (w • x) =
        w • (ρ : (Fin Tag.E8.rank → ℤ) → _)^[m] x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h.1]
  have hconj : ∀ x ∈ Subgroup.closure
        {s : WeylGroup Tag.E8 | ∃ δ ∈ (fun x => w • x) '' P, s = rootReflection δ},
      w⁻¹ * x * w ∈ Subgroup.closure
        {s : WeylGroup Tag.E8 | ∃ γ ∈ P, s = rootReflection γ} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨δ, hδ, rfl⟩ := hy
      obtain ⟨γ, hγP, rfl⟩ := hδ
      have hc : w⁻¹ * rootReflection (w • γ) * w = rootReflection γ := by
        rw [kg_rootReflection_smul w γ]
        group
      rw [hc]
      exact Subgroup.subset_closure ⟨γ, hγP, rfl⟩
    | one => simp
    | mul a b ha hb iha ihb =>
      have hc : w⁻¹ * (a * b) * w = (w⁻¹ * a * w) * (w⁻¹ * b * w) := by group
      rw [hc]
      exact mul_mem iha ihb
    | inv a ha iha =>
      have hc : w⁻¹ * a⁻¹ * w = (w⁻¹ * a * w)⁻¹ := by group
      rw [hc]
      exact inv_mem iha
  have hconj' : ∀ x ∈ Subgroup.closure
        {s : WeylGroup Tag.E8 | ∃ γ ∈ P, s = rootReflection γ},
      w * x * w⁻¹ ∈ Subgroup.closure
        {s : WeylGroup Tag.E8 | ∃ δ ∈ (fun x => w • x) '' P, s = rootReflection δ} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, hγP, rfl⟩ := hy
      have hc : w * rootReflection γ * w⁻¹ = rootReflection (w • γ) := by
        rw [kg_rootReflection_smul w γ]
      rw [hc]
      exact Subgroup.subset_closure ⟨w • γ, ⟨γ, hγP, rfl⟩, rfl⟩
    | one => simp
    | mul a b ha hb iha ihb =>
      have hc : w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
      rw [hc]
      exact mul_mem iha ihb
    | inv a ha iha =>
      have hc : w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ := by group
      rw [hc]
      exact inv_mem iha
  constructor
  · rintro ⟨v, hv, hfix⟩
    refine ⟨w⁻¹ * v * w, hconj v hv, fun γ hγ => ?_⟩
    have hwγ : w • γ ∈ (fun x => w • x) '' P := ⟨γ, hγ, rfl⟩
    have h1 := hfix (w • γ) hwγ
    calc (ρ : (Fin Tag.E8.rank → ℤ) → _)^[n] γ =
          w⁻¹ • ((ρ')^[n] (w • γ)) := by rw [hiter n γ, inv_smul_smul]
      _ = w⁻¹ • (v • (w • γ)) := by rw [h1]
      _ = (w⁻¹ * v * w) • γ := by rw [← mul_smul, ← mul_smul]
  · rintro ⟨v, hv, hfix⟩
    refine ⟨w * v * w⁻¹, hconj' v hv, fun γ hγ => ?_⟩
    obtain ⟨δ, hδP, rfl⟩ := hγ
    calc (ρ')^[n] (w • δ) = w • ((ρ)^[n] δ) := hiter n δ
      _ = w • (v • δ) := by rw [hfix δ hδP]
      _ = (w * v * w⁻¹) • (w • δ) := by
          rw [← mul_smul, ← mul_smul]
          congr 1
          group

private theorem WeylConj.twistKind_eq
    {L : Type} [Field L] {w : WeylGroup Tag.E8} {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀)
    (i : KernelComponent χ) (i₀ : KernelComponent χ₀)
    (hi : componentRoots χ₀ i₀ = (fun x => w • x) '' componentRoots χ i) :
    twistKind ρ' χ₀ i₀ = twistKind ρ χ i := by
  unfold twistKind
  rw [hi, compRank_smul_image, Set.ncard_image_of_injective _ (MulAction.injective w),
    WeylConj.orbitLength_eq h]
  rw [WeylConj.twistInner_iff h, WeylConj.twistInner_iff h]

private theorem kernelA_of_weyl
    {L : Type} [Field L] {w : WeylGroup Tag.E8} {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀) :
    E8TwoFiveKernelA ρ' χ₀ → E8TwoFiveKernelA ρ χ := by
  intro hA
  obtain ⟨hncard, i₁', i₂', hne', hall', hrk', hcard', himg', hkind'⟩ := hA
  obtain ⟨e, he⟩ := WeylConj.component_equiv h
  have hnc : (kernelRoots χ).ncard = 40 := by
    have h1 := WeylConj.kernelRoots_eq h
    rw [h1, Set.ncard_image_of_injective _ (MulAction.injective w)] at hncard
    exact hncard
  have he₁ : componentRoots χ₀ i₁' =
      (fun x => w • x) '' componentRoots χ (e.symm i₁') := by
    rw [← he (e.symm i₁'), Equiv.apply_symm_apply]
  have he₂ : componentRoots χ₀ i₂' =
      (fun x => w • x) '' componentRoots χ (e.symm i₂') := by
    rw [← he (e.symm i₂'), Equiv.apply_symm_apply]
  refine ⟨hnc, e.symm i₁', e.symm i₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    exact hne' (e.symm.injective hh)
  · intro i
    rcases hall' (e i) with hh | hh
    · left
      rw [← Equiv.symm_apply_apply e i, hh]
    · right
      rw [← Equiv.symm_apply_apply e i, hh]
  · have hh := hrk'
    rw [he₁, compRank_smul_image] at hh
    exact hh
  · have hh := hcard'
    rw [he₁, Set.ncard_image_of_injective _ (MulAction.injective w)] at hh
    exact hh
  · have himage : (ρ' : (Fin Tag.E8.rank → ℤ) → _) ''
        ((fun x => w • x) '' componentRoots χ (e.symm i₁')) =
        (fun x => w • x) '' ((ρ : (Fin Tag.E8.rank → ℤ) → _) ''
          componentRoots χ (e.symm i₁')) := by
      rw [← Set.image_comp, ← Set.image_comp]
      congr 1
      funext x
      exact h.1 x
    have hfinal : (fun x => w • x) '' ((ρ : (Fin Tag.E8.rank → ℤ) → _) ''
          componentRoots χ (e.symm i₁')) =
        (fun x => w • x) '' componentRoots χ (e.symm i₂') := by
      rw [← himage, ← he₁, himg', he₂]
    exact Set.image_injective.2 (MulAction.injective w) hfinal
  · rw [← WeylConj.twistKind_eq h (e.symm i₁') i₁' he₁]
    exact hkind'

private theorem kernelB_of_weyl
    {L : Type} [Field L] {w : WeylGroup Tag.E8} {ρ ρ' : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    {χ χ₀ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ} (h : WeylConj w ρ ρ' χ χ₀) :
    E8TwoFiveKernelB ρ' χ₀ → E8TwoFiveKernelB ρ χ := by
  intro hB
  obtain ⟨hncard, i', hall', hrk', hcard', hkind'⟩ := hB
  obtain ⟨e, he⟩ := WeylConj.component_equiv h
  have hnc : (kernelRoots χ).ncard = 60 := by
    have h1 := WeylConj.kernelRoots_eq h
    rw [h1, Set.ncard_image_of_injective _ (MulAction.injective w)] at hncard
    exact hncard
  have he' : componentRoots χ₀ i' =
      (fun x => w • x) '' componentRoots χ (e.symm i') := by
    rw [← he (e.symm i'), Equiv.apply_symm_apply]
  refine ⟨hnc, e.symm i', ?_, ?_, ?_, ?_⟩
  · intro j
    rw [← Equiv.symm_apply_apply e j, hall' (e j)]
  · have hh := hrk'
    rw [he', compRank_smul_image] at hh
    exact hh
  · have hh := hcard'
    rw [he', Set.ncard_image_of_injective _ (MulAction.injective w)] at hh
    exact hh
  · rw [← WeylConj.twistKind_eq h (e.symm i') i' he']
    exact hkind'

private theorem isFrobLike_conj
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) 5) (w : WeylGroup Tag.E8)
    (μ : Fin 8 → ℤ) (hχ : ∀ β, rootChar a β = ζ ^ ((w • β) ⬝ᵥ μ)) :
    IsFrobLike (conjPerm w S.ρ) μ := by
  obtain ⟨hq, hT, _hΓ, _ha5, _hne⟩ := h
  have hσ : ∀ x : Fin Tag.E8.rank → ℤ, conjPerm w S.ρ x = w • S.ρ (w⁻¹ • x) := by
    intro x
    have h1 := conjPerm_smul w S.ρ (w⁻¹ • x)
    rwa [smul_inv_smul] at h1
  have hζ' : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.coe_units_iff.1 hζ
  refine ⟨?_, ?_, ?_⟩
  · intro γ
    rw [hσ, isRoot_smul_iff w, S.frob.isRoot_iff, isRoot_smul_iff w⁻¹]
  · intro γ δ
    rw [hσ, hσ, iform_smul, S.frob.iform_eq, iform_smul]
  · intro δ hδ
    let lam : Fin Tag.E8.rank → ℤ := μ
    have hχ' : ∀ β : Fin Tag.E8.rank → ℤ, rootChar a β = ζ ^ ((w • β) ⬝ᵥ lam) :=
      fun β => hχ β
    set γ : Fin Tag.E8.rank → ℤ := w⁻¹ • δ with hγdef
    have hγ : IsRoot Tag.E8 γ := by
      rw [hγdef]
      exact (isRoot_smul_iff w⁻¹).2 hδ
    have h1 := S.frob.rootChar_eq a hT γ hγ
    rw [hq] at h1
    rw [hχ' (S.ρ γ), hχ' γ] at h1
    have h2 : (ζ ^ ((w • γ) ⬝ᵥ lam)) ^ 2 = ζ ^ (2 * ((w • γ) ⬝ᵥ lam)) := by
      rw [pow_two, ← zpow_add, two_mul]
    have hwγ : w • γ = δ := by rw [hγdef, smul_inv_smul]
    have hz : ζ ^ ((conjPerm w S.ρ δ) ⬝ᵥ lam) = ζ ^ (2 * (δ ⬝ᵥ lam)) := by
      have hwS : w • S.ρ γ = conjPerm w S.ρ δ := by
        rw [hγdef]
        exact (hσ δ).symm
      rw [← hwS, ← hwγ]
      exact h1.trans h2
    have hz1 : ζ ^ ((conjPerm w S.ρ δ) ⬝ᵥ lam - 2 * (δ ⬝ᵥ lam)) = 1 := by
      rw [zpow_sub, hz]
      group
    have hdvd : (5 : ℤ) ∣ (conjPerm w S.ρ δ) ⬝ᵥ lam - 2 * (δ ⬝ᵥ lam) :=
      (hζ'.zpow_eq_one_iff_dvd _).mp hz1
    change (conjPerm w S.ρ δ) ⬝ᵥ lam ≡ 2 * (δ ⬝ᵥ lam) [ZMOD 5]
    rw [Int.modEq_iff_dvd]
    simpa only [neg_sub] using dvd_neg.mpr hdvd

private def kerA1 : Set (Fin Tag.E8.rank → ℤ) :=
  {γ | IsRoot Tag.E8 γ ∧ γ (4 : Fin 8) = 0 ∧ γ (5 : Fin 8) = 0 ∧ γ (6 : Fin 8) = 0 ∧
    γ (7 : Fin 8) = 0}

private def kerA2 : Set (Fin Tag.E8.rank → ℤ) :=
  {γ | IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ (4 : Fin 8) ∧
    ¬ (γ (4 : Fin 8) = 0 ∧ γ (5 : Fin 8) = 0 ∧ γ (6 : Fin 8) = 0 ∧
      γ (7 : Fin 8) = 0)}

private def kf_pA1 (γ : Fin Tag.E8.rank → ℤ) : Prop :=
  γ (4 : Fin 8) = 0 ∧ γ (5 : Fin 8) = 0 ∧ γ (6 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0

private def kf_pA2 (γ : Fin Tag.E8.rank → ℤ) : Prop :=
  (5 : ℤ) ∣ γ (4 : Fin 8) ∧ ¬ kf_pA1 γ

private instance kf_decA1 (l : List ℤ) : Decidable (kf_pA1 (E8TwoFiveFin.vecOf l)) := by
  unfold kf_pA1; infer_instance

private instance kf_decA2 (l : List ℤ) : Decidable (kf_pA2 (E8TwoFiveFin.vecOf l)) := by
  unfold kf_pA2 kf_pA1; infer_instance

private theorem kf_kerA1_eq :
    kerA1 = {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ ∧ kf_pA1 γ} := by
  ext γ; simp [kerA1, kf_pA1]

private theorem kf_kerA2_eq :
    kerA2 = {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ ∧ kf_pA2 γ} := by
  ext γ; simp [kerA2, kf_pA2, kf_pA1]

private theorem kf_e1_mem : ([1, 0, 0, 0, 0, 0, 0, 0] : List ℤ) ∈ E8TwoFiveFin.rootsL := by
  decide +kernel

private theorem kf_theta_mem : ([2, 3, 4, 6, 5, 4, 3, 2] : List ℤ) ∈ E8TwoFiveFin.rootsL := by
  decide +kernel

private theorem kf_orth_list : ∀ lx ∈ E8TwoFiveFin.rootsL, ∀ ly ∈ E8TwoFiveFin.rootsL,
    kf_pA1 (E8TwoFiveFin.vecOf lx) → kf_pA2 (E8TwoFiveFin.vecOf ly) →
      E8TwoFiveFin.formL lx ly = 0 := by
  decide +kernel

private theorem kf_kerA_orth_vec :
    ∀ x : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 x → kf_pA1 x →
      ∀ y : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 y → kf_pA2 y → iform x y = 0 := by
  refine (E8TwoFiveFin.forall_root_iff _).2 fun lx hlx hpx => ?_
  refine (E8TwoFiveFin.forall_root_iff _).2 fun ly hly hpy => ?_
  rw [E8TwoFiveFin.iform_vecOf hlx hly]
  exact kf_orth_list lx hlx ly hly hpx hpy

private theorem kerA_iff (γ : Fin Tag.E8.rank → ℤ) :
    (IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ ⬝ᵥ e8TwoFiveKac5A) ↔ γ ∈ kerA1 ∨ γ ∈ kerA2 := by
  rw [dotProduct_e8TwoFiveKac5A]
  constructor
  · rintro ⟨hγ, h5⟩
    by_cases h : kf_pA1 γ
    · exact Or.inl (by rw [kf_kerA1_eq]; exact ⟨hγ, h⟩)
    · exact Or.inr (by rw [kf_kerA2_eq]; exact ⟨hγ, h5, h⟩)
  · rintro (h1 | h2)
    · rw [kf_kerA1_eq] at h1
      simp only [Set.mem_setOf_eq, kf_pA1] at h1
      exact ⟨h1.1, by rw [h1.2.1]; exact dvd_zero 5⟩
    · rw [kf_kerA2_eq] at h2
      simp only [Set.mem_setOf_eq, kf_pA2] at h2
      exact ⟨h2.1, h2.2.1⟩

private theorem kerA_union {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) 5) :
    kernelRoots (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ e8TwoFiveKac5A i)) =
      kerA1 ∪ kerA2 := by
  rw [kernelRoots_zeta hζ e8TwoFiveKac5A]
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact kerA_iff γ

private theorem kerA_disjoint : Disjoint kerA1 kerA2 := by
  rw [Set.disjoint_left]
  intro γ h1 h2
  rw [kf_kerA1_eq] at h1
  rw [kf_kerA2_eq] at h2
  simp only [Set.mem_setOf_eq, kf_pA2] at h2
  exact h2.2.2 h1.2

private theorem kerA1_nonempty : kerA1.Nonempty := by
  refine ⟨E8TwoFiveFin.vecOf [1, 0, 0, 0, 0, 0, 0, 0], ?_⟩
  rw [kf_kerA1_eq]
  exact ⟨E8TwoFiveFin.isRoot_vecOf kf_e1_mem, by decide +kernel⟩

private theorem kerA2_nonempty : kerA2.Nonempty := by
  refine ⟨E8TwoFiveFin.vecOf [2, 3, 4, 6, 5, 4, 3, 2], ?_⟩
  rw [kf_kerA2_eq]
  exact ⟨E8TwoFiveFin.isRoot_vecOf kf_theta_mem, by decide +kernel⟩

private theorem kerA_ncard : kerA1.ncard = 20 ∧ kerA2.ncard = 20 := by
  constructor
  · rw [kf_kerA1_eq, E8TwoFiveFin.ncard_root_filter kf_pA1]
    decide +kernel
  · rw [kf_kerA2_eq, E8TwoFiveFin.ncard_root_filter kf_pA2]
    decide +kernel

private theorem kerA_orth :
    ∀ x ∈ kerA1, ∀ y ∈ kerA2, iform x y = 0 := by
  intro x hx y hy
  rw [kf_kerA1_eq] at hx
  rw [kf_kerA2_eq] at hy
  simp only [Set.mem_setOf_eq] at hx hy
  exact kf_kerA_orth_vec x hx.1 hx.2 y hy.1 hy.2

private theorem kf_isConnIn_of_hub (P : Set (Fin Tag.E8.rank → ℤ)) (r₀ : Fin Tag.E8.rank → ℤ)
    (hr₀ : r₀ ∈ P)
    (hub : ∀ y ∈ P, y = r₀ ∨ iform r₀ y ≠ 0 ∨
      ∃ z ∈ P, iform r₀ z ≠ 0 ∧ iform z y ≠ 0) :
    IsConnIn P := by
  unfold IsConnIn
  intro x hx y hy
  have hstep : ∀ t ∈ P, Relation.EqvGen (fun a b => a ∈ P ∧ b ∈ P ∧ iform a b ≠ 0) r₀ t := by
    intro t ht
    rcases hub t ht with h | h | ⟨z, hz, h1, h2⟩
    · rw [h]; exact Relation.EqvGen.refl r₀
    · exact Relation.EqvGen.rel r₀ t ⟨hr₀, ht, h⟩
    · exact Relation.EqvGen.trans r₀ z t (Relation.EqvGen.rel r₀ z ⟨hr₀, hz, h1⟩)
        (Relation.EqvGen.rel z t ⟨hz, ht, h2⟩)
  exact Relation.EqvGen.trans x r₀ y (Relation.EqvGen.symm r₀ x (hstep x hx)) (hstep y hy)

private theorem kf_hub_vec
    {P : (Fin Tag.E8.rank → ℤ) → Prop} {rL : List ℤ}
    (hrL : rL ∈ E8TwoFiveFin.rootsL)
    (hlist : ∀ ly ∈ E8TwoFiveFin.rootsL, P (E8TwoFiveFin.vecOf ly) →
      ly = rL ∨ E8TwoFiveFin.formL rL ly ≠ 0 ∨
      ∃ lz ∈ E8TwoFiveFin.rootsL, P (E8TwoFiveFin.vecOf lz) ∧
        E8TwoFiveFin.formL rL lz ≠ 0 ∧ E8TwoFiveFin.formL lz ly ≠ 0) :
    ∀ y, IsRoot Tag.E8 y → P y →
      y = E8TwoFiveFin.vecOf rL ∨ iform (E8TwoFiveFin.vecOf rL) y ≠ 0 ∨
      ∃ z, IsRoot Tag.E8 z ∧ P z ∧
        iform (E8TwoFiveFin.vecOf rL) z ≠ 0 ∧ iform z y ≠ 0 := by
  refine (E8TwoFiveFin.forall_root_iff _).2 fun ly hly hpy => ?_
  rcases hlist ly hly hpy with h | h | ⟨lz, hzl, hpz, h1, h2⟩
  · left
    rw [h]
  · right; left
    rwa [E8TwoFiveFin.iform_vecOf hrL hly]
  · right; right
    refine (E8TwoFiveFin.exists_root_iff
      (fun z => P z ∧ iform (E8TwoFiveFin.vecOf rL) z ≠ 0 ∧
        iform z (E8TwoFiveFin.vecOf ly) ≠ 0)).2 ?_
    exact ⟨lz, hzl, hpz, by rwa [E8TwoFiveFin.iform_vecOf hrL hzl],
      by rwa [E8TwoFiveFin.iform_vecOf hzl hly]⟩

private theorem kf_hubA1_list :
    ∀ ly ∈ E8TwoFiveFin.rootsL, kf_pA1 (E8TwoFiveFin.vecOf ly) →
      ly = [1, 0, 0, 0, 0, 0, 0, 0] ∨
        E8TwoFiveFin.formL [1, 0, 0, 0, 0, 0, 0, 0] ly ≠ 0 ∨
        ∃ lz ∈ E8TwoFiveFin.rootsL, kf_pA1 (E8TwoFiveFin.vecOf lz) ∧
          E8TwoFiveFin.formL [1, 0, 0, 0, 0, 0, 0, 0] lz ≠ 0 ∧
          E8TwoFiveFin.formL lz ly ≠ 0 := by
  decide +kernel

private theorem kf_hubA2_list :
    ∀ ly ∈ E8TwoFiveFin.rootsL, kf_pA2 (E8TwoFiveFin.vecOf ly) →
      ly = [2, 3, 4, 6, 5, 4, 3, 2] ∨
        E8TwoFiveFin.formL [2, 3, 4, 6, 5, 4, 3, 2] ly ≠ 0 ∨
        ∃ lz ∈ E8TwoFiveFin.rootsL, kf_pA2 (E8TwoFiveFin.vecOf lz) ∧
          E8TwoFiveFin.formL [2, 3, 4, 6, 5, 4, 3, 2] lz ≠ 0 ∧
          E8TwoFiveFin.formL lz ly ≠ 0 := by
  decide +kernel

private theorem kf_conn_kerA1 : IsConnIn kerA1 := by
  rw [kf_kerA1_eq]
  refine kf_isConnIn_of_hub _ (E8TwoFiveFin.vecOf [1, 0, 0, 0, 0, 0, 0, 0])
    ⟨E8TwoFiveFin.isRoot_vecOf kf_e1_mem, by decide +kernel⟩ ?_
  intro y hy
  rcases kf_hub_vec kf_e1_mem kf_hubA1_list y hy.1 hy.2 with h | h | ⟨z, hzr, hpz, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨z, ⟨hzr, hpz⟩, h1, h2⟩)

private theorem kf_conn_kerA2 : IsConnIn kerA2 := by
  rw [kf_kerA2_eq]
  refine kf_isConnIn_of_hub _ (E8TwoFiveFin.vecOf [2, 3, 4, 6, 5, 4, 3, 2])
    ⟨E8TwoFiveFin.isRoot_vecOf kf_theta_mem, by decide +kernel⟩ ?_
  intro y hy
  rcases kf_hub_vec kf_theta_mem kf_hubA2_list y hy.1 hy.2 with h | h | ⟨z, hzr, hpz, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨z, ⟨hzr, hpz⟩, h1, h2⟩)

private theorem kerA_conn : IsConnIn kerA1 ∧ IsConnIn kerA2 := by
  exact ⟨kf_conn_kerA1, kf_conn_kerA2⟩

private def kf_castA (i : Fin 4) : Fin Tag.E8.rank :=
  Fin.castLE (by decide +kernel : 4 ≤ Tag.E8.rank) i

private noncomputable def kf_bA (i : Fin 4) : Fin Tag.E8.rank → ℚ := Pi.single (kf_castA i) 1

private theorem kf_castA_inj : Function.Injective kf_castA :=
  Fin.castLE_injective (by decide +kernel : 4 ≤ Tag.E8.rank)

private theorem kf_bA_self (i : Fin 4) : kf_bA i (kf_castA i) = 1 := by
  simp [kf_bA, Pi.single_eq_same]

private theorem kf_bA_ne {i : Fin 4} {j : Fin Tag.E8.rank} (h : j ≠ kf_castA i) :
    kf_bA i j = 0 := by
  simp [kf_bA, Pi.single_eq_of_ne h]

private theorem kf_castA_cases (j : Fin Tag.E8.rank) (hj : ∀ i : Fin 4, kf_castA i ≠ j) :
    j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
  fin_cases j
  · exact absurd rfl (hj 0)
  · exact absurd rfl (hj 1)
  · exact absurd rfl (hj 2)
  · exact absurd rfl (hj 3)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem kf_bA_lin : LinearIndependent ℚ kf_bA := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (kf_castA i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have h2 : ∑ j : Fin 4, g j * kf_bA j (kf_castA i) = g i := by
    rw [Finset.sum_eq_single i]
    · rw [kf_bA_self, mul_one]
    · intro j _ hj
      rw [kf_bA_ne (fun he => hj (kf_castA_inj he).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h2] at h
  exact h

private theorem kf_single_zero_of_lt {j k : Fin Tag.E8.rank}
    (hk : 4 ≤ (k : ℕ)) (hj : (j : ℕ) < 4) :
    (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) k = 0 := by
  rw [Pi.single_eq_of_ne]
  rintro h
  have hv := congrArg Fin.val h
  omega

private theorem kf_single_mem_kerA1 {j : Fin Tag.E8.rank} (hj : (j : ℕ) < 4) :
    (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) ∈ kerA1 := by
  rw [kf_kerA1_eq]
  refine ⟨IsRoot.basis j, ?_⟩
  unfold kf_pA1
  exact ⟨kf_single_zero_of_lt (by decide +kernel) hj,
    kf_single_zero_of_lt (by decide +kernel) hj,
    kf_single_zero_of_lt (by decide +kernel) hj,
    kf_single_zero_of_lt (by decide +kernel) hj⟩

private theorem kf_toRat_sum_A (γ : Fin Tag.E8.rank → ℤ)
    (h4 : γ (4 : Fin 8) = 0) (h5 : γ (5 : Fin 8) = 0)
    (h6 : γ (6 : Fin 8) = 0) (h7 : γ (7 : Fin 8) = 0) :
    (fun j => (γ j : ℚ)) = ∑ i : Fin 4, (γ (kf_castA i) : ℚ) • kf_bA i := by
  funext j
  rw [Finset.sum_apply]
  by_cases hj : ∃ i : Fin 4, kf_castA i = j
  · obtain ⟨i₀, rfl⟩ := hj
    rw [Finset.sum_eq_single i₀]
    · rw [Pi.smul_apply, smul_eq_mul, kf_bA_self, mul_one]
    · intro i _ hi
      rw [Pi.smul_apply, smul_eq_mul, kf_bA_ne (fun he => hi (kf_castA_inj he).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  · push Not at hj
    have h0 : (γ j : ℚ) = 0 := by
      rcases kf_castA_cases j hj with h | h | h | h
      · rw [h]; exact_mod_cast h4
      · rw [h]; exact_mod_cast h5
      · rw [h]; exact_mod_cast h6
      · rw [h]; exact_mod_cast h7
    rw [h0]
    exact (Finset.sum_eq_zero fun i _ => by
      rw [Pi.smul_apply, smul_eq_mul, kf_bA_ne (fun he => hj i he.symm), mul_zero]).symm

private theorem kf_finrank_bA :
    Module.finrank ℚ (Submodule.span ℚ (Set.range kf_bA)) = 4 := by
  rw [finrank_span_eq_card kf_bA_lin, Fintype.card_fin]

private theorem kf_S_le_T_A :
    Submodule.span ℚ ((fun γ (i : Fin Tag.E8.rank) => (γ i : ℚ)) '' kerA1) ≤
      Submodule.span ℚ (Set.range kf_bA) := by
  rw [Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  change (fun j => (γ j : ℚ)) ∈ Submodule.span ℚ (Set.range kf_bA)
  rw [kf_kerA1_eq] at hγ
  simp only [Set.mem_setOf_eq, kf_pA1] at hγ
  rw [kf_toRat_sum_A γ hγ.2.1 hγ.2.2.1 hγ.2.2.2.1 hγ.2.2.2.2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem kf_T_le_S_A :
    Submodule.span ℚ (Set.range kf_bA) ≤
      Submodule.span ℚ ((fun γ (i : Fin Tag.E8.rank) => (γ i : ℚ)) '' kerA1) := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine Submodule.subset_span
    ⟨Pi.single (kf_castA i) (1 : ℤ), kf_single_mem_kerA1 (j := kf_castA i) i.2, ?_⟩
  funext j
  simp [kf_bA, Pi.single_apply]

private theorem kerA1_rank : compRank kerA1 = 4 := by
  unfold compRank
  rw [le_antisymm kf_S_le_T_A kf_T_le_S_A, kf_finrank_bA]

private def kf_kerA1L : List (List ℤ) :=
  [[-1, -1, -1, -1, 0, 0, 0, 0], [-1, 0, -1, -1, 0, 0, 0, 0],
   [-1, 0, -1, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, -1, -1, -1, 0, 0, 0, 0],
   [0, -1, 0, -1, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0]]

private theorem kf_kerA1L_mem : ∀ l ∈ kf_kerA1L,
    l ∈ E8TwoFiveFin.rootsL ∧ kf_pA1 (E8TwoFiveFin.vecOf l) := by
  decide +kernel

private theorem kf_kerA1L_in_kerA1 {l : List ℤ}
    (h : l ∈ kf_kerA1L) : E8TwoFiveFin.vecOf l ∈ kerA1 := by
  obtain ⟨hl, hp⟩ := kf_kerA1L_mem l h
  rw [kf_kerA1_eq]
  exact ⟨E8TwoFiveFin.isRoot_vecOf hl, hp⟩

private def kf_profileL (l : List ℤ) : List ℤ :=
  kf_kerA1L.map (fun lb => E8TwoFiveFin.formL l lb)

private theorem kf_profile_list : ∀ lg ∈ E8TwoFiveFin.rootsL, ∀ lg' ∈ E8TwoFiveFin.rootsL,
    kf_profileL lg = kf_profileL lg' →
      E8TwoFiveFin.vecOf lg (4 : Fin 8) % 5 = E8TwoFiveFin.vecOf lg' (4 : Fin 8) % 5 := by
  decide +kernel

private theorem kerA_profile :
    ∀ g g' : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 g → IsRoot Tag.E8 g' →
      (∀ b ∈ kerA1, iform g b = iform g' b) →
        (g ⬝ᵥ e8TwoFiveKac5A) % 5 = (g' ⬝ᵥ e8TwoFiveKac5A) % 5 := by
  intro g g' hg hg' hprof
  rw [dotProduct_e8TwoFiveKac5A, dotProduct_e8TwoFiveKac5A]
  have hgmem : List.ofFn g ∈ E8TwoFiveFin.rootsL :=
    (E8TwoFiveFin.isRoot_iff_mem_rootsL g).1 hg
  have hg'mem : List.ofFn g' ∈ E8TwoFiveFin.rootsL :=
    (E8TwoFiveFin.isRoot_iff_mem_rootsL g').1 hg'
  have hmap : kf_profileL (List.ofFn g) = kf_profileL (List.ofFn g') := by
    unfold kf_profileL
    refine List.map_congr_left fun lb hlb => ?_
    have hlb' : lb ∈ E8TwoFiveFin.rootsL := (kf_kerA1L_mem lb hlb).1
    have hmem : E8TwoFiveFin.vecOf lb ∈ kerA1 := kf_kerA1L_in_kerA1 hlb
    have e1 : E8TwoFiveFin.formL (List.ofFn g) lb = iform g (E8TwoFiveFin.vecOf lb) := by
      rw [← E8TwoFiveFin.iform_vecOf hgmem hlb', E8TwoFiveFin.vecOf_ofFn]
    have e2 : E8TwoFiveFin.formL (List.ofFn g') lb = iform g' (E8TwoFiveFin.vecOf lb) := by
      rw [← E8TwoFiveFin.iform_vecOf hg'mem hlb', E8TwoFiveFin.vecOf_ofFn]
    rw [e1, e2, hprof _ hmem]
  have hres := kf_profile_list (List.ofFn g) hgmem (List.ofFn g') hg'mem hmap
  rwa [E8TwoFiveFin.vecOf_ofFn, E8TwoFiveFin.vecOf_ofFn] at hres

private theorem kf_e5_mem : ([0, 0, 0, 0, 1, 0, 0, 0] : List ℤ) ∈ E8TwoFiveFin.rootsL := by
  decide +kernel

private theorem kf_type_count6 :
    (E8TwoFiveFin.rootsL.filter fun lb =>
      decide (kf_pA1 (E8TwoFiveFin.vecOf lb) ∧
        iform (E8TwoFiveFin.vecOf [0, 0, 0, 0, 1, 0, 0, 0])
          (E8TwoFiveFin.vecOf lb) = 1)).length = 6 := by
  decide +kernel

private theorem kf_type_ne_list : ∀ lg ∈ E8TwoFiveFin.rootsL,
    E8TwoFiveFin.vecOf lg (4 : Fin 8) % 5 = 2 →
    (E8TwoFiveFin.rootsL.filter fun lb =>
      decide (kf_pA1 (E8TwoFiveFin.vecOf lb) ∧
        iform (E8TwoFiveFin.vecOf lg) (E8TwoFiveFin.vecOf lb) = 1)).length ≠ 6 := by
  decide +kernel

private theorem kerA_type :
    (∃ g₀ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 g₀ ∧ (g₀ ⬝ᵥ e8TwoFiveKac5A) % 5 = 1 ∧
      {b ∈ kerA1 | iform g₀ b = 1}.ncard = 6) ∧
      ∀ g : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 g → (g ⬝ᵥ e8TwoFiveKac5A) % 5 = 2 →
        {b ∈ kerA1 | iform g b = 1}.ncard ≠ 6 := by
  constructor
  · refine ⟨E8TwoFiveFin.vecOf [0, 0, 0, 0, 1, 0, 0, 0],
      E8TwoFiveFin.isRoot_vecOf kf_e5_mem, ?_, ?_⟩
    · rw [dotProduct_e8TwoFiveKac5A]; decide +kernel
    · have hset : {b : Fin Tag.E8.rank → ℤ | b ∈ kerA1 ∧
          iform (E8TwoFiveFin.vecOf [0, 0, 0, 0, 1, 0, 0, 0]) b = 1} =
          {b : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 b ∧
            (kf_pA1 b ∧ iform (E8TwoFiveFin.vecOf [0, 0, 0, 0, 1, 0, 0, 0]) b = 1)} := by
        ext b; rw [kf_kerA1_eq]; simp only [Set.mem_setOf_eq]; tauto
      rw [hset, E8TwoFiveFin.ncard_root_filter
        (fun b => kf_pA1 b ∧ iform (E8TwoFiveFin.vecOf [0, 0, 0, 0, 1, 0, 0, 0]) b = 1)]
      exact kf_type_count6
  · intro g hg h2
    have hgmem : List.ofFn g ∈ E8TwoFiveFin.rootsL :=
      (E8TwoFiveFin.isRoot_iff_mem_rootsL g).1 hg
    have hset : {b : Fin Tag.E8.rank → ℤ | b ∈ kerA1 ∧ iform g b = 1} =
        {b : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 b ∧ (kf_pA1 b ∧ iform g b = 1)} := by
      ext b; rw [kf_kerA1_eq]; simp only [Set.mem_setOf_eq]; tauto
    rw [hset, E8TwoFiveFin.ncard_root_filter (fun b => kf_pA1 b ∧ iform g b = 1)]
    have h2' : E8TwoFiveFin.vecOf (List.ofFn g) (4 : Fin 8) % 5 = 2 := by
      have h3 : g (4 : Fin 8) % 5 = 2 :=
        (congrArg (fun x : ℤ => x % 5) (dotProduct_e8TwoFiveKac5A g)).symm.trans h2
      rwa [E8TwoFiveFin.vecOf_ofFn]
    have hgf : (E8TwoFiveFin.rootsL.filter fun lb =>
        decide (kf_pA1 (E8TwoFiveFin.vecOf lb) ∧ iform g (E8TwoFiveFin.vecOf lb) = 1)) =
        (E8TwoFiveFin.rootsL.filter fun lb =>
        decide (kf_pA1 (E8TwoFiveFin.vecOf lb) ∧
          iform (E8TwoFiveFin.vecOf (List.ofFn g)) (E8TwoFiveFin.vecOf lb) = 1)) := by
      apply List.filter_congr
      intro lb _
      rw [E8TwoFiveFin.vecOf_ofFn]
    rw [hgf]
    exact kf_type_ne_list (List.ofFn g) hgmem h2'

private def kerB : Set (Fin Tag.E8.rank → ℤ) :=
  {γ | IsRoot Tag.E8 γ ∧ γ (0 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0}

private theorem kf_kerB_eq :
    kerB = {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ ∧
      γ (0 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0} := by
  ext γ; simp [kerB]

private theorem kf_kerB_list : ∀ l ∈ E8TwoFiveFin.rootsL,
    (5 : ℤ) ∣ E8TwoFiveFin.vecOf l (0 : Fin 8) + E8TwoFiveFin.vecOf l (7 : Fin 8) →
      E8TwoFiveFin.vecOf l (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf l (7 : Fin 8) = 0 := by
  decide +kernel

private theorem kf_kerB_coords (γ : Fin Tag.E8.rank → ℤ)
    (hγ : IsRoot Tag.E8 γ) (h5 : (5 : ℤ) ∣ γ (0 : Fin 8) + γ (7 : Fin 8)) :
    γ (0 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0 :=
  (E8TwoFiveFin.forall_root_iff (fun g => (5 : ℤ) ∣ g (0 : Fin 8) + g (7 : Fin 8) →
    g (0 : Fin 8) = 0 ∧ g (7 : Fin 8) = 0)).2 (fun l hl => kf_kerB_list l hl) γ hγ h5

private theorem kf_e2_mem : ([0, 1, 0, 0, 0, 0, 0, 0] : List ℤ) ∈ E8TwoFiveFin.rootsL := by
  decide +kernel

private theorem kerB_iff (γ : Fin Tag.E8.rank → ℤ) :
    (IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ ⬝ᵥ e8TwoFiveKac5B) ↔ γ ∈ kerB := by
  rw [dotProduct_e8TwoFiveKac5B]
  constructor
  · rintro ⟨hγ, h5⟩
    rw [kf_kerB_eq]
    exact ⟨hγ, kf_kerB_coords γ hγ h5⟩
  · intro h
    rw [kf_kerB_eq] at h
    obtain ⟨hγ, h0, h7⟩ := h
    exact ⟨hγ, by rw [h0, h7]; exact dvd_zero 5⟩

private theorem kerB_union {L : Type} [Field L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) 5) :
    kernelRoots (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ e8TwoFiveKac5B i)) = kerB := by
  rw [kernelRoots_zeta hζ e8TwoFiveKac5B]
  ext γ
  simp only [Set.mem_setOf_eq]
  exact kerB_iff γ

private theorem kerB_nonempty : kerB.Nonempty := by
  refine ⟨E8TwoFiveFin.vecOf [0, 1, 0, 0, 0, 0, 0, 0], ?_⟩
  rw [kf_kerB_eq]
  exact ⟨E8TwoFiveFin.isRoot_vecOf kf_e2_mem, by decide +kernel⟩

private theorem kerB_ncard : kerB.ncard = 60 := by
  rw [kf_kerB_eq, E8TwoFiveFin.ncard_root_filter
    (fun γ : Fin Tag.E8.rank → ℤ => γ (0 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0)]
  decide +kernel

private theorem kf_hubB_list :
    ∀ ly ∈ E8TwoFiveFin.rootsL,
      (E8TwoFiveFin.vecOf ly (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf ly (7 : Fin 8) = 0) →
      ly = [0, 1, 0, 0, 0, 0, 0, 0] ∨
        E8TwoFiveFin.formL [0, 1, 0, 0, 0, 0, 0, 0] ly ≠ 0 ∨
        ∃ lz ∈ E8TwoFiveFin.rootsL,
          (E8TwoFiveFin.vecOf lz (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lz (7 : Fin 8) = 0) ∧
          E8TwoFiveFin.formL [0, 1, 0, 0, 0, 0, 0, 0] lz ≠ 0 ∧
          E8TwoFiveFin.formL lz ly ≠ 0 := by
  decide +kernel

private theorem kf_conn_kerB : IsConnIn kerB := by
  rw [kf_kerB_eq]
  refine kf_isConnIn_of_hub _ (E8TwoFiveFin.vecOf [0, 1, 0, 0, 0, 0, 0, 0])
    ⟨E8TwoFiveFin.isRoot_vecOf kf_e2_mem, by decide +kernel⟩ ?_
  intro y hy
  rcases kf_hub_vec (P := fun γ : Fin Tag.E8.rank → ℤ =>
      γ (0 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0)
      kf_e2_mem kf_hubB_list y hy.1 hy.2 with h | h | ⟨z, hzr, hpz, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨z, ⟨hzr, hpz⟩, h1, h2⟩)

private theorem kerB_conn : IsConnIn kerB := by
  exact kf_conn_kerB

private def kf_castB (i : Fin 6) : Fin Tag.E8.rank :=
  Fin.castLE (by decide +kernel : 7 ≤ Tag.E8.rank) (Fin.succ i)

private theorem kf_castB_val (i : Fin 6) : (kf_castB i : ℕ) = i.val + 1 := rfl

private noncomputable def kf_bB (i : Fin 6) : Fin Tag.E8.rank → ℚ := Pi.single (kf_castB i) 1

private theorem kf_castB_inj : Function.Injective kf_castB := by
  intro i j h
  have h2 := congrArg Fin.val h
  simp only [kf_castB_val] at h2
  exact Fin.ext (by omega)

private theorem kf_bB_self (i : Fin 6) : kf_bB i (kf_castB i) = 1 := by
  simp [kf_bB, Pi.single_eq_same]

private theorem kf_bB_ne {i : Fin 6} {j : Fin Tag.E8.rank} (h : j ≠ kf_castB i) :
    kf_bB i j = 0 := by
  simp [kf_bB, Pi.single_eq_of_ne h]

private theorem kf_castB_cases (j : Fin Tag.E8.rank) (hj : ∀ i : Fin 6, kf_castB i ≠ j) :
    j = 0 ∨ j = 7 := by
  fin_cases j
  · exact Or.inl rfl
  · exact absurd rfl (hj 0)
  · exact absurd rfl (hj 1)
  · exact absurd rfl (hj 2)
  · exact absurd rfl (hj 3)
  · exact absurd rfl (hj 4)
  · exact absurd rfl (hj 5)
  · exact Or.inr rfl

private theorem kf_bB_lin : LinearIndependent ℚ kf_bB := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (kf_castB i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have h2 : ∑ j : Fin 6, g j * kf_bB j (kf_castB i) = g i := by
    rw [Finset.sum_eq_single i]
    · rw [kf_bB_self, mul_one]
    · intro j _ hj
      rw [kf_bB_ne (fun he => hj (kf_castB_inj he).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h2] at h
  exact h

private theorem kf_castB_ne_zero (i : Fin 6) : kf_castB i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [kf_castB_val] at hv
  have hz : ((0 : Fin Tag.E8.rank) : ℕ) = 0 := by decide +kernel
  rw [hz] at hv
  omega

private theorem kf_castB_ne_seven (i : Fin 6) : kf_castB i ≠ 7 := by
  intro h
  have hv := congrArg Fin.val h
  rw [kf_castB_val] at hv
  have h7 : ((7 : Fin Tag.E8.rank) : ℕ) = 7 := by decide +kernel
  rw [h7] at hv
  have := i.2
  omega

private theorem kf_single_zero_kerB {j k : Fin Tag.E8.rank}
    (hk : k = 0 ∨ k = 7) (h0 : j ≠ 0) (h7 : j ≠ 7) :
    (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) k = 0 := by
  rw [Pi.single_eq_of_ne]
  rintro h
  rcases hk with rfl | rfl
  · exact h0 h.symm
  · exact h7 h.symm

private theorem kf_single_mem_kerB {j : Fin Tag.E8.rank} (h0 : j ≠ 0) (h7 : j ≠ 7) :
    (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) ∈ kerB := by
  rw [kf_kerB_eq]
  refine ⟨IsRoot.basis j, ?_, ?_⟩
  · show (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) (0 : Fin Tag.E8.rank) = 0
    exact kf_single_zero_kerB (Or.inl rfl) h0 h7
  · show (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) (7 : Fin Tag.E8.rank) = 0
    exact kf_single_zero_kerB (Or.inr rfl) h0 h7

private theorem kf_toRat_sum_B (γ : Fin Tag.E8.rank → ℤ)
    (h0 : γ (0 : Fin 8) = 0) (h7 : γ (7 : Fin 8) = 0) :
    (fun j => (γ j : ℚ)) = ∑ i : Fin 6, (γ (kf_castB i) : ℚ) • kf_bB i := by
  funext j
  rw [Finset.sum_apply]
  by_cases hj : ∃ i : Fin 6, kf_castB i = j
  · obtain ⟨i₀, rfl⟩ := hj
    rw [Finset.sum_eq_single i₀]
    · rw [Pi.smul_apply, smul_eq_mul, kf_bB_self, mul_one]
    · intro i _ hi
      rw [Pi.smul_apply, smul_eq_mul, kf_bB_ne (fun he => hi (kf_castB_inj he).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  · push Not at hj
    have hz : (γ j : ℚ) = 0 := by
      rcases kf_castB_cases j hj with h | h
      · rw [h]; exact_mod_cast h0
      · rw [h]; exact_mod_cast h7
    rw [hz]
    exact (Finset.sum_eq_zero fun i _ => by
      rw [Pi.smul_apply, smul_eq_mul, kf_bB_ne (fun he => hj i he.symm), mul_zero]).symm

private theorem kf_finrank_bB :
    Module.finrank ℚ (Submodule.span ℚ (Set.range kf_bB)) = 6 := by
  rw [finrank_span_eq_card kf_bB_lin, Fintype.card_fin]

private theorem kf_S_le_T_B :
    Submodule.span ℚ ((fun γ (i : Fin Tag.E8.rank) => (γ i : ℚ)) '' kerB) ≤
      Submodule.span ℚ (Set.range kf_bB) := by
  rw [Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  change (fun j => (γ j : ℚ)) ∈ Submodule.span ℚ (Set.range kf_bB)
  rw [kf_kerB_eq] at hγ
  simp only [Set.mem_setOf_eq] at hγ
  rw [kf_toRat_sum_B γ hγ.2.1 hγ.2.2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem kf_T_le_S_B :
    Submodule.span ℚ (Set.range kf_bB) ≤
      Submodule.span ℚ ((fun γ (i : Fin Tag.E8.rank) => (γ i : ℚ)) '' kerB) := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine Submodule.subset_span
    ⟨Pi.single (kf_castB i) (1 : ℤ),
      kf_single_mem_kerB (kf_castB_ne_zero i) (kf_castB_ne_seven i), ?_⟩
  funext j
  simp [kf_bB, Pi.single_apply]

private theorem kerB_rank : compRank kerB = 6 := by
  unfold compRank
  rw [le_antisymm kf_S_le_T_B kf_T_le_S_B, kf_finrank_bB]

private def kf_g1L : List ℤ := [-2, -3, -4, -6, -5, -4, -3, -2]
private def kf_g2L : List ℤ := [2, 2, 3, 4, 3, 2, 1, 0]
private def kf_dL : List ℤ := [-1, -3, -3, -5, -4, -3, -2, -1]

private theorem kf_g1L_mem : kf_g1L ∈ E8TwoFiveFin.rootsL := by decide +kernel
private theorem kf_g2L_mem : kf_g2L ∈ E8TwoFiveFin.rootsL := by decide +kernel
private theorem kf_dL_mem : kf_dL ∈ E8TwoFiveFin.rootsL := by decide +kernel

private theorem kf_g1L_u : (E8TwoFiveFin.vecOf kf_g1L (0 : Fin 8) +
    E8TwoFiveFin.vecOf kf_g1L (7 : Fin 8)) % 5 = 1 := by decide +kernel

private theorem kf_g2L_u : (E8TwoFiveFin.vecOf kf_g2L (0 : Fin 8) +
    E8TwoFiveFin.vecOf kf_g2L (7 : Fin 8)) % 5 = 2 := by decide +kernel

private theorem kf_B_orth_list : ∀ lb ∈ E8TwoFiveFin.rootsL,
    (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) →
      E8TwoFiveFin.formL kf_g1L lb = 0 ∧ E8TwoFiveFin.formL kf_g2L lb = 0 := by
  decide +kernel

private theorem kf_B_unique_list :
    ∀ lg ∈ E8TwoFiveFin.rootsL,
      (E8TwoFiveFin.vecOf lg (0 : Fin 8) + E8TwoFiveFin.vecOf lg (7 : Fin 8)) % 5 = 2 →
      (∀ lb ∈ E8TwoFiveFin.rootsL,
        (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) →
          E8TwoFiveFin.formL lg lb = 0) →
      lg = kf_g2L := by
  decide +kernel

private def kf_step (acc : Bool × List (List ℤ × Bool)) (p : List ℤ × Bool) :
    Bool × List (List ℤ × Bool) :=
  (acc.1 && acc.2.all (fun q => !(p.1 == q.1) || (p.2 == q.2)), p :: acc.2)

private def kf_good (l : List (List ℤ × Bool)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p.2 = q.2

private theorem kf_good_cons {p : List ℤ × Bool} {l : List (List ℤ × Bool)}
    (h : l.all (fun q => !(p.1 == q.1) || (p.2 == q.2)) = true) (hl : kf_good l) :
    kf_good (p :: l) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with ha | ha
  · rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha, hb']
    · rw [ha] at hab ⊢
      have hq := List.all_eq_true.mp h b hb'
      have hbeq : (p.1 == b.1) = true := by rw [beq_iff_eq]; exact hab
      rw [hbeq] at hq
      simp only [Bool.not_true, Bool.false_or] at hq
      exact beq_iff_eq.mp hq
  · rcases List.mem_cons.mp hb with hb' | hb'
    · rw [hb'] at hab ⊢
      have hq := List.all_eq_true.mp h a ha
      have hbeq : (p.1 == a.1) = true := by rw [beq_iff_eq]; exact hab.symm
      rw [hbeq] at hq
      simp only [Bool.not_true, Bool.false_or] at hq
      exact (beq_iff_eq.mp hq).symm
    · exact hl a ha b hb' hab

private theorem kf_good_nil : kf_good ([] : List (List ℤ × Bool)) := by
  intro p hp; simp at hp

private theorem kf_fold_flag : ∀ (l : List (List ℤ × Bool)) (acc : Bool × List (List ℤ × Bool)),
    (l.foldl kf_step acc).1 = true → acc.1 = true := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons p ps ih =>
    intro acc h
    have h' := ih (kf_step acc p) h
    simp only [kf_step, Bool.and_eq_true] at h'
    exact h'.1

private theorem kf_fold_good : ∀ (l : List (List ℤ × Bool)) (acc : Bool × List (List ℤ × Bool)),
    acc.1 = true → kf_good acc.2 → (l.foldl kf_step acc).1 = true →
      kf_good (l.foldl kf_step acc).2 := by
  intro l
  induction l with
  | nil => intro acc h1 h2 h3; exact h2
  | cons p ps ih =>
    intro acc h1 h2 h3
    have hstep1 : (kf_step acc p).1 = true := kf_fold_flag ps (kf_step acc p) h3
    have hall : acc.2.all (fun q => !(p.1 == q.1) || (p.2 == q.2)) = true := by
      simp only [kf_step, Bool.and_eq_true] at hstep1
      exact hstep1.2
    have hgood : kf_good (kf_step acc p).2 := by
      change kf_good (p :: acc.2)
      exact kf_good_cons hall h2
    exact ih (kf_step acc p) hstep1 hgood h3

private theorem kf_fold_mem : ∀ (l : List (List ℤ × Bool)) (acc : Bool × List (List ℤ × Bool)),
    (∀ p ∈ acc.2, p ∈ (l.foldl kf_step acc).2) ∧
    (∀ p ∈ l, p ∈ (l.foldl kf_step acc).2) := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨fun p hp => hp, fun p hp => by simp at hp⟩
  | cons p ps ih =>
    intro acc
    obtain ⟨ihacc, ihps⟩ := ih (kf_step acc p)
    refine ⟨?_, ?_⟩
    · intro q hq
      exact ihacc q (by change q ∈ p :: acc.2; exact List.mem_cons_of_mem p hq)
    · intro q hq
      rcases List.mem_cons.mp hq with hpq | hq
      · subst q
        exact ihacc p (by change p ∈ p :: acc.2; exact List.mem_cons_self)
      · exact ihps q hq

private theorem kf_check_sound (l : List (List ℤ × Bool)) :
    (l.foldl kf_step (true, [])).1 = true → kf_good l := by
  intro h p hp q hq heq
  have hgood := kf_fold_good l (true, []) rfl kf_good_nil h
  have hmem := (kf_fold_mem l (true, [])).2
  exact hgood p (hmem p hp) q (hmem q hq) heq

private def kf_kerBL : List (List ℤ) :=
  (E8TwoFiveFin.rootsL.filter fun lb =>
    decide (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧
      E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0)).take 11

private def kf_profileB (l : List ℤ) : List ℤ :=
  kf_kerBL.map (fun lb => E8TwoFiveFin.formL l lb)

private def kf_B_profU : List (List ℤ × Bool) :=
  (E8TwoFiveFin.rootsL.filter fun lg =>
    decide (∃ lb ∈ E8TwoFiveFin.rootsL,
      (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) ∧
        E8TwoFiveFin.formL lg lb ≠ 0)).map (fun lg =>
    (kf_profileB lg, decide (E8TwoFiveFin.formL lg kf_g2L = 0)))

private theorem kf_B_profU_good : kf_good kf_B_profU :=
  kf_check_sound kf_B_profU (by decide +kernel)

private theorem kf_B_delta_list :
    (∃ lb ∈ E8TwoFiveFin.rootsL,
      (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) ∧
        E8TwoFiveFin.formL kf_dL lb ≠ 0) ∧
      E8TwoFiveFin.formL kf_dL kf_g1L ≠ 0 ∧ E8TwoFiveFin.formL kf_dL kf_g2L = 0 := by
  decide +kernel

private theorem kerB_profile :
    ∃ γ₁ γ₂ : Fin Tag.E8.rank → ℤ, γ₁ = E8TwoFiveFin.vecOf [-2, -3, -4, -6, -5, -4, -3, -2] ∧
      γ₂ = E8TwoFiveFin.vecOf [2, 2, 3, 4, 3, 2, 1, 0] ∧ IsRoot Tag.E8 γ₁ ∧ IsRoot Tag.E8 γ₂ ∧
      (γ₁ ⬝ᵥ e8TwoFiveKac5B) % 5 = 1 ∧ (γ₂ ⬝ᵥ e8TwoFiveKac5B) % 5 = 2 ∧
      (∀ b ∈ kerB, iform γ₁ b = 0 ∧ iform γ₂ b = 0) ∧
      (∀ g : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 g → (∀ b ∈ kerB, iform g b = 0) →
        (g ⬝ᵥ e8TwoFiveKac5B) % 5 = 2 → g = γ₂) ∧
      (∀ g g' : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 g → IsRoot Tag.E8 g' →
        (∃ b ∈ kerB, iform g b ≠ 0) → (∀ b ∈ kerB, iform g b = iform g' b) →
          (iform g γ₂ = 0 ↔ iform g' γ₂ = 0)) ∧
      ∃ δ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 δ ∧ (∃ b ∈ kerB, iform δ b ≠ 0) ∧
        iform δ γ₁ ≠ 0 ∧ iform δ γ₂ = 0 := by
  refine ⟨E8TwoFiveFin.vecOf kf_g1L, E8TwoFiveFin.vecOf kf_g2L, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact E8TwoFiveFin.isRoot_vecOf kf_g1L_mem
  · exact E8TwoFiveFin.isRoot_vecOf kf_g2L_mem
  · exact (congrArg (fun x : ℤ => x % 5) (dotProduct_e8TwoFiveKac5B _)).trans kf_g1L_u
  · exact (congrArg (fun x : ℤ => x % 5) (dotProduct_e8TwoFiveKac5B _)).trans kf_g2L_u
  · intro b hb
    rw [kf_kerB_eq] at hb
    simp only [Set.mem_setOf_eq] at hb
    have hbmem : List.ofFn b ∈ E8TwoFiveFin.rootsL :=
      (E8TwoFiveFin.isRoot_iff_mem_rootsL b).1 hb.1
    have hb0 : E8TwoFiveFin.vecOf (List.ofFn b) (0 : Fin 8) = 0 := by
      rw [E8TwoFiveFin.vecOf_ofFn]; exact hb.2.1
    have hb7 : E8TwoFiveFin.vecOf (List.ofFn b) (7 : Fin 8) = 0 := by
      rw [E8TwoFiveFin.vecOf_ofFn]; exact hb.2.2
    obtain ⟨e1, e2⟩ := kf_B_orth_list (List.ofFn b) hbmem ⟨hb0, hb7⟩
    constructor
    · rw [← E8TwoFiveFin.vecOf_ofFn b, E8TwoFiveFin.iform_vecOf kf_g1L_mem hbmem]
      exact e1
    · rw [← E8TwoFiveFin.vecOf_ofFn b, E8TwoFiveFin.iform_vecOf kf_g2L_mem hbmem]
      exact e2
  · intro g hg horth hu
    have hgmem : List.ofFn g ∈ E8TwoFiveFin.rootsL :=
      (E8TwoFiveFin.isRoot_iff_mem_rootsL g).1 hg
    have h2 : (E8TwoFiveFin.vecOf (List.ofFn g) (0 : Fin 8) +
        E8TwoFiveFin.vecOf (List.ofFn g) (7 : Fin 8)) % 5 = 2 := by
      rw [E8TwoFiveFin.vecOf_ofFn]
      exact (congrArg (fun x : ℤ => x % 5) (dotProduct_e8TwoFiveKac5B g)).symm.trans hu
    have hlist : ∀ lb ∈ E8TwoFiveFin.rootsL,
        (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) →
          E8TwoFiveFin.formL (List.ofFn g) lb = 0 := by
      intro lb hlb hq
      have hq' : E8TwoFiveFin.vecOf lb ∈ kerB := by
        rw [kf_kerB_eq]
        exact ⟨E8TwoFiveFin.isRoot_vecOf hlb, hq⟩
      have hzero := horth (E8TwoFiveFin.vecOf lb) hq'
      have e : E8TwoFiveFin.formL (List.ofFn g) lb = iform g (E8TwoFiveFin.vecOf lb) := by
        rw [← E8TwoFiveFin.iform_vecOf hgmem hlb, E8TwoFiveFin.vecOf_ofFn]
      rw [e, hzero]
    have hres := kf_B_unique_list (List.ofFn g) hgmem h2 hlist
    rw [← E8TwoFiveFin.vecOf_ofFn g, hres]
  · intro g g' hg hg' hne hprof
    have hgmem : List.ofFn g ∈ E8TwoFiveFin.rootsL :=
      (E8TwoFiveFin.isRoot_iff_mem_rootsL g).1 hg
    have hg'mem : List.ofFn g' ∈ E8TwoFiveFin.rootsL :=
      (E8TwoFiveFin.isRoot_iff_mem_rootsL g').1 hg'
    have hneL : ∃ lb ∈ E8TwoFiveFin.rootsL,
        (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) ∧
          E8TwoFiveFin.formL (List.ofFn g) lb ≠ 0 := by
      obtain ⟨b, hb, hbne⟩ := hne
      rw [kf_kerB_eq] at hb
      simp only [Set.mem_setOf_eq] at hb
      have hbmem : List.ofFn b ∈ E8TwoFiveFin.rootsL :=
        (E8TwoFiveFin.isRoot_iff_mem_rootsL b).1 hb.1
      have hb0 : E8TwoFiveFin.vecOf (List.ofFn b) (0 : Fin 8) = 0 := by
        rw [E8TwoFiveFin.vecOf_ofFn]; exact hb.2.1
      have hb7 : E8TwoFiveFin.vecOf (List.ofFn b) (7 : Fin 8) = 0 := by
        rw [E8TwoFiveFin.vecOf_ofFn]; exact hb.2.2
      refine ⟨List.ofFn b, hbmem, ⟨hb0, hb7⟩, ?_⟩
      have e : E8TwoFiveFin.formL (List.ofFn g) (List.ofFn b) = iform g b := by
        rw [← E8TwoFiveFin.iform_vecOf hgmem hbmem, E8TwoFiveFin.vecOf_ofFn,
          E8TwoFiveFin.vecOf_ofFn]
      rw [e]
      exact hbne
    have hprofL : ∀ lb ∈ E8TwoFiveFin.rootsL,
        (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) →
          E8TwoFiveFin.formL (List.ofFn g) lb = E8TwoFiveFin.formL (List.ofFn g') lb := by
      intro lb hlb hq
      have hq' : E8TwoFiveFin.vecOf lb ∈ kerB := by
        rw [kf_kerB_eq]
        exact ⟨E8TwoFiveFin.isRoot_vecOf hlb, hq⟩
      have heq := hprof (E8TwoFiveFin.vecOf lb) hq'
      have e1 : E8TwoFiveFin.formL (List.ofFn g) lb = iform g (E8TwoFiveFin.vecOf lb) := by
        rw [← E8TwoFiveFin.iform_vecOf hgmem hlb, E8TwoFiveFin.vecOf_ofFn]
      have e2 : E8TwoFiveFin.formL (List.ofFn g') lb = iform g' (E8TwoFiveFin.vecOf lb) := by
        rw [← E8TwoFiveFin.iform_vecOf hg'mem hlb, E8TwoFiveFin.vecOf_ofFn]
      rw [e1, e2, heq]
    have hneL' : ∃ lb ∈ E8TwoFiveFin.rootsL,
        (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧ E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0) ∧
          E8TwoFiveFin.formL (List.ofFn g') lb ≠ 0 := by
      obtain ⟨lb, hlb, hq, hd⟩ := hneL
      exact ⟨lb, hlb, hq, by rw [← hprofL lb hlb hq]; exact hd⟩
    have hmem : (kf_profileB (List.ofFn g), decide (E8TwoFiveFin.formL (List.ofFn g) kf_g2L = 0))
        ∈ kf_B_profU := by
      rw [kf_B_profU, List.mem_map]
      refine ⟨List.ofFn g, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hgmem, decide_eq_true hneL⟩
    have hmem' : (kf_profileB (List.ofFn g'),
        decide (E8TwoFiveFin.formL (List.ofFn g') kf_g2L = 0)) ∈ kf_B_profU := by
      rw [kf_B_profU, List.mem_map]
      refine ⟨List.ofFn g', ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hg'mem, decide_eq_true hneL'⟩
    have hprof_eq : kf_profileB (List.ofFn g) = kf_profileB (List.ofFn g') := by
      unfold kf_profileB
      refine List.map_congr_left fun lb hlb => ?_
      have hmemf : lb ∈ E8TwoFiveFin.rootsL.filter (fun lb =>
          decide (E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧
            E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0)) := List.mem_of_mem_take hlb
      have hlb' : lb ∈ E8TwoFiveFin.rootsL := List.mem_of_mem_filter hmemf
      have hq : E8TwoFiveFin.vecOf lb (0 : Fin 8) = 0 ∧
          E8TwoFiveFin.vecOf lb (7 : Fin 8) = 0 := by
        have h := (List.mem_filter.mp hmemf).2
        simpa using h
      exact hprofL lb hlb' hq
    have hbool : decide (E8TwoFiveFin.formL (List.ofFn g) kf_g2L = 0) =
        decide (E8TwoFiveFin.formL (List.ofFn g') kf_g2L = 0) :=
      kf_B_profU_good _ hmem _ hmem' hprof_eq
    have eg : iform g (E8TwoFiveFin.vecOf kf_g2L) = E8TwoFiveFin.formL (List.ofFn g) kf_g2L := by
      rw [← E8TwoFiveFin.vecOf_ofFn g]; exact E8TwoFiveFin.iform_vecOf hgmem kf_g2L_mem
    have eg' : iform g' (E8TwoFiveFin.vecOf kf_g2L) =
        E8TwoFiveFin.formL (List.ofFn g') kf_g2L := by
      rw [← E8TwoFiveFin.vecOf_ofFn g']; exact E8TwoFiveFin.iform_vecOf hg'mem kf_g2L_mem
    rw [eg, eg']
    constructor
    · intro hA
      have hAt : decide (E8TwoFiveFin.formL (List.ofFn g) kf_g2L = 0) = true := decide_eq_true hA
      rw [hbool] at hAt
      exact of_decide_eq_true hAt
    · intro hB
      have hBt : decide (E8TwoFiveFin.formL (List.ofFn g') kf_g2L = 0) = true := decide_eq_true hB
      rw [← hbool] at hBt
      exact of_decide_eq_true hBt
  · refine ⟨E8TwoFiveFin.vecOf kf_dL, E8TwoFiveFin.isRoot_vecOf kf_dL_mem, ?_, ?_, ?_⟩
    · obtain ⟨lb, hlb, hq, hnz⟩ := kf_B_delta_list.1
      refine ⟨E8TwoFiveFin.vecOf lb, ?_, ?_⟩
      · rw [kf_kerB_eq]; exact ⟨E8TwoFiveFin.isRoot_vecOf hlb, hq⟩
      · rw [E8TwoFiveFin.iform_vecOf kf_dL_mem hlb]; exact hnz
    · rw [E8TwoFiveFin.iform_vecOf kf_dL_mem kf_g1L_mem]
      exact kf_B_delta_list.2.1
    · rw [E8TwoFiveFin.iform_vecOf kf_dL_mem kf_g2L_mem]
      exact kf_B_delta_list.2.2

private theorem ks_stable_image
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) {μ : Fin 8 → ℤ} (hσ : IsFrobLike σ μ) :
    σ '' {γ | IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ ⬝ᵥ μ} =
      {γ | IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ ⬝ᵥ μ} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxroot, hx5⟩, rfl⟩
    refine ⟨(hσ.1 x).2 hxroot, ?_⟩
    have hmod : (σ x ⬝ᵥ μ) ≡ 2 * (x ⬝ᵥ μ) [ZMOD 5] := hσ.2.2 x hxroot
    obtain ⟨k, hk⟩ := hmod.dvd
    obtain ⟨m, hm⟩ := hx5
    exact ⟨2 * m - k, by omega⟩
  · rintro ⟨hyroot, hy5⟩
    have hsymm : σ (σ.symm y) = y := σ.apply_symm_apply y
    refine ⟨σ.symm y, ?_, hsymm⟩
    have hroot : IsRoot Tag.E8 (σ.symm y) := by
      have h1 : IsRoot Tag.E8 (σ (σ.symm y)) := by rw [hsymm]; exact hyroot
      exact (hσ.1 (σ.symm y)).mp h1
    refine ⟨hroot, ?_⟩
    have hmod : (σ (σ.symm y) ⬝ᵥ μ) ≡ 2 * (σ.symm y ⬝ᵥ μ) [ZMOD 5] :=
      hσ.2.2 (σ.symm y) hroot
    rw [hsymm] at hmod
    obtain ⟨k, hk⟩ := hmod.dvd
    obtain ⟨m, hm⟩ := hy5
    have h2u : (5 : ℤ) ∣ 2 * (σ.symm y ⬝ᵥ μ) := ⟨k + m, by omega⟩
    have hp : Prime (5 : ℤ) := by norm_num
    rcases hp.dvd_mul.mp h2u with h | h
    · norm_num at h
    · exact h

private theorem ks_iform_iterate
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hiso : ∀ γ δ, iform (σ γ) (σ δ) = iform γ δ) :
    ∀ (n : ℕ) (x y : Fin Tag.E8.rank → ℤ),
      iform (((σ : (Fin Tag.E8.rank → ℤ) → _)^[n]) x)
        (((σ : (Fin Tag.E8.rank → ℤ) → _)^[n]) y) = iform x y := by
  intro n
  induction n with
  | zero => intro x y; rfl
  | succ n ih =>
    intro x y
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [hiso, ih]

private theorem ks_modEq_two
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) {μ : Fin 8 → ℤ} (hσ : IsFrobLike σ μ)
    {g : Fin Tag.E8.rank → ℤ} (hg : IsRoot Tag.E8 g) :
    (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g ⬝ᵥ μ) ≡ 4 * (g ⬝ᵥ μ) [ZMOD 5] := by
  have h1 : (σ g ⬝ᵥ μ) ≡ 2 * (g ⬝ᵥ μ) [ZMOD 5] := hσ.2.2 g hg
  have h2 : (σ (σ g) ⬝ᵥ μ) ≡ 2 * (σ g ⬝ᵥ μ) [ZMOD 5] :=
    hσ.2.2 (σ g) ((hσ.1 g).2 hg)
  have h2' : (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g ⬝ᵥ μ) ≡
      2 * (σ g ⬝ᵥ μ) [ZMOD 5] := by
    change (σ (σ g) ⬝ᵥ μ) ≡ 2 * (σ g ⬝ᵥ μ) [ZMOD 5]
    exact h2
  refine h2'.trans ?_
  have h := h1.mul_left 2
  rw [show 2 * (2 * (g ⬝ᵥ μ)) = 4 * (g ⬝ᵥ μ) by ring] at h
  exact h

private theorem ks_eqvGen_iff {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (hstep : ∀ a b, R a b → (P a ↔ P b)) {a b : α} (h : Relation.EqvGen R a b) :
    P a ↔ P b := by
  induction h with
  | rel a b hab => exact hstep a b hab
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

private theorem kerA_stable (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hσ : IsFrobLike σ e8TwoFiveKac5A) : σ '' (kerA1 ∪ kerA2) = kerA1 ∪ kerA2 := by
  have hset : kerA1 ∪ kerA2 =
      {γ | IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ ⬝ᵥ e8TwoFiveKac5A} := by
    ext γ
    exact (kerA_iff γ).symm
  rw [hset]
  exact ks_stable_image σ hσ

private theorem ks_symmCartan (i j : Fin 8) :
    Tag.E8.symmetrizedCartan i j = Tag.E8.symmetrizedCartan j i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem ks_iform_comm_E8 (x y : Fin Tag.E8.rank → ℤ) :
    iform x y = iform y x := by
  simp only [iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ks_symmCartan j i]
  ring

private theorem ks_same_piece
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hσ : IsFrobLike σ e8TwoFiveKac5A)
    {a b : Fin Tag.E8.rank → ℤ} (ha : a ∈ kerA1) (hb : b ∈ kerA1)
    (hne : iform a b ≠ 0) :
    (σ a ∈ kerA1 ∧ σ b ∈ kerA1) ∨ (σ a ∈ kerA2 ∧ σ b ∈ kerA2) := by
  have hstable := kerA_stable σ hσ
  have hma : σ a ∈ kerA1 ∪ kerA2 := by
    rw [← hstable]
    exact ⟨a, Or.inl ha, rfl⟩
  have hmb : σ b ∈ kerA1 ∪ kerA2 := by
    rw [← hstable]
    exact ⟨b, Or.inl hb, rfl⟩
  rcases hma with ha1 | ha2 <;> rcases hmb with hb1 | hb2
  · exact Or.inl ⟨ha1, hb1⟩
  · exfalso
    have h0 : iform (σ a) (σ b) = 0 := kerA_orth (σ a) ha1 (σ b) hb2
    rw [hσ.2.1] at h0
    exact hne h0
  · exfalso
    have h0 : iform (σ b) (σ a) = 0 := kerA_orth (σ b) hb1 (σ a) ha2
    rw [hσ.2.1, ks_iform_comm_E8 b a] at h0
    exact hne h0
  · exact Or.inr ⟨ha2, hb2⟩

private theorem kerA_image (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hσ : IsFrobLike σ e8TwoFiveKac5A) : σ '' kerA1 = kerA1 ∨ σ '' kerA1 = kerA2 := by
  have hstable := kerA_stable σ hσ
  have hsub : σ '' kerA1 ⊆ kerA1 ∪ kerA2 := by
    rw [← hstable]
    exact Set.image_mono Set.subset_union_left
  have hcard : (σ '' kerA1).ncard = kerA1.ncard :=
    Set.ncard_image_of_injective _ σ.injective
  have hfin1 : kerA1.Finite := Set.finite_of_ncard_pos (by rw [kerA_ncard.1]; norm_num)
  have hfin2 : kerA2.Finite := Set.finite_of_ncard_pos (by rw [kerA_ncard.2]; norm_num)
  have hnotA : ∀ z, z ∈ kerA2 → z ∉ kerA1 := by
    intro z hz2 hz1
    have hz : z ∈ kerA1 ∩ kerA2 := ⟨hz1, hz2⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp kerA_disjoint] at hz
    exact hz
  have hnotB : ∀ z, z ∈ kerA1 → z ∉ kerA2 := by
    intro z hz1 hz2
    exact hnotA z hz2 hz1
  have hstep1 : ∀ a b, a ∈ kerA1 ∧ b ∈ kerA1 ∧ iform a b ≠ 0 →
      (σ a ∈ kerA1 ↔ σ b ∈ kerA1) := by
    rintro a b ⟨ha, hb, hne⟩
    rcases ks_same_piece σ hσ ha hb hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact ⟨fun h => absurd h (hnotA (σ a) h1), fun h => absurd h (hnotA (σ b) h2)⟩
  have hstep2 : ∀ a b, a ∈ kerA1 ∧ b ∈ kerA1 ∧ iform a b ≠ 0 →
      (σ a ∈ kerA2 ↔ σ b ∈ kerA2) := by
    rintro a b ⟨ha, hb, hne⟩
    rcases ks_same_piece σ hσ ha hb hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => absurd h (hnotB (σ a) h1), fun h => absurd h (hnotB (σ b) h2)⟩
    · exact ⟨fun _ => h2, fun _ => h1⟩
  obtain ⟨y₀, hy₀⟩ := kerA1_nonempty
  have hx₀ : σ y₀ ∈ σ '' kerA1 := ⟨y₀, hy₀, rfl⟩
  rcases hsub hx₀ with hx₀ | hx₀
  · left
    have hsub1 : σ '' kerA1 ⊆ kerA1 := by
      rintro x ⟨y, hy, rfl⟩
      exact (ks_eqvGen_iff hstep1 (kerA_conn.1 y₀ hy₀ y hy)).mp hx₀
    exact Set.eq_of_subset_of_ncard_le hsub1 (le_of_eq hcard.symm) hfin1
  · right
    have hsub2 : σ '' kerA1 ⊆ kerA2 := by
      rintro x ⟨y, hy, rfl⟩
      exact (ks_eqvGen_iff hstep2 (kerA_conn.1 y₀ hy₀ y hy)).mp hx₀
    refine Set.eq_of_subset_of_ncard_le hsub2 ?_ hfin2
    exact le_of_eq (by simp [hcard, kerA_ncard.1, kerA_ncard.2])
private theorem kerA_not_fix (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hσ : IsFrobLike σ e8TwoFiveKac5A) : σ '' kerA1 ≠ kerA1 := by
  intro hfix
  obtain ⟨g₀, hg₀root, hg₀u, hg₀card⟩ := kerA_type.1
  have hσg₀root : IsRoot Tag.E8 (σ g₀) := (hσ.1 g₀).2 hg₀root
  have hσg₀u : (σ g₀ ⬝ᵥ e8TwoFiveKac5A) % 5 = 2 := by
    have h1 : (σ g₀ ⬝ᵥ e8TwoFiveKac5A) ≡ 2 * (g₀ ⬝ᵥ e8TwoFiveKac5A) [ZMOD 5] :=
      hσ.2.2 g₀ hg₀root
    have hg₀mod : (g₀ ⬝ᵥ e8TwoFiveKac5A) ≡ 1 [ZMOD 5] := hg₀u
    have h2 : 2 * (g₀ ⬝ᵥ e8TwoFiveKac5A) ≡ 2 [ZMOD 5] := by
      simpa using hg₀mod.mul_left 2
    have htarget : (σ g₀ ⬝ᵥ e8TwoFiveKac5A) ≡ 2 [ZMOD 5] := h1.trans h2
    have h := htarget
    change (σ g₀ ⬝ᵥ e8TwoFiveKac5A) % 5 = (2 : ℤ) % 5 at h
    rw [h]
    norm_num
  have himg : σ '' {c ∈ kerA1 | iform g₀ c = 1} =
      {b ∈ kerA1 | iform (σ g₀) b = 1} := by
    ext b
    constructor
    · rintro ⟨c, ⟨hc, hc1⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have : σ c ∈ σ '' kerA1 := ⟨c, hc, rfl⟩
        rwa [hfix] at this
      · have hiso : iform (σ g₀) (σ c) = iform g₀ c := hσ.2.1 g₀ c
        rw [hiso, hc1]
    · intro hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [← hfix] at hb1
      obtain ⟨c, hc, hceq⟩ := hb1
      refine ⟨c, ⟨hc, ?_⟩, hceq⟩
      have hiso : iform (σ g₀) (σ c) = iform g₀ c := hσ.2.1 g₀ c
      rw [← hiso, hceq]
      exact hb2
  have hne6 := kerA_type.2 (σ g₀) hσg₀root hσg₀u
  apply hne6
  rw [← himg, Set.ncard_image_of_injective _ σ.injective, hg₀card]

private theorem kerA_swap_back
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hσ : IsFrobLike σ e8TwoFiveKac5A)
    (h : σ '' kerA1 = kerA2) : σ '' kerA2 = kerA1 := by
  have hstable := kerA_stable σ hσ
  have hdisjmem : ∀ z, z ∈ kerA1 → z ∈ kerA2 → False := by
    intro z hz1 hz2
    have hz : z ∈ kerA1 ∩ kerA2 := ⟨hz1, hz2⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp kerA_disjoint] at hz
    exact hz
  ext x
  constructor
  · rintro ⟨c, hc2, rfl⟩
    have hmem : σ c ∈ σ '' (kerA1 ∪ kerA2) := ⟨c, Or.inr hc2, rfl⟩
    rw [hstable] at hmem
    rcases hmem with h1 | h2
    · exact h1
    · exfalso
      rw [← h] at h2
      obtain ⟨d, hd1, hd⟩ := h2
      have hdc : d = c := σ.injective hd
      rw [hdc] at hd1
      exact hdisjmem c hd1 hc2
  · intro hx
    have hmem : x ∈ σ '' (kerA1 ∪ kerA2) := by
      rw [hstable]
      exact Or.inl hx
    obtain ⟨c, hc, hcx⟩ := hmem
    rcases hc with hc1 | hc2
    · exfalso
      have hxc : x ∈ kerA2 := by
        rw [← h]
        exact ⟨c, hc1, hcx⟩
      exact hdisjmem x hx hxc
    · exact ⟨c, hc2, hcx⟩

private theorem kerA_not_inner
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hσ : IsFrobLike σ e8TwoFiveKac5A) :
    ¬ twistInner kerA1 ((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) := by
  rintro ⟨w, hw, hwact⟩
  have hnotA : ∀ z, z ∈ kerA2 → z ∉ kerA1 := by
    intro z hz2 hz1
    have hz : z ∈ kerA1 ∩ kerA2 := ⟨hz1, hz2⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp kerA_disjoint] at hz
    exact hz
  let H : Subgroup (WeylGroup Tag.E8) :=
    { carrier := {v | (∀ x ∈ kerA1, v • x ∈ kerA1 ∧ v⁻¹ • x ∈ kerA1) ∧
          ∀ x : Fin Tag.E8.rank → ℤ, (v • x) (4 : Fin 8) = x (4 : Fin 8)}
      one_mem' := by
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ⟨by simpa using hx, by simpa using hx⟩
        · intro x
          rw [one_smul]
      mul_mem' := by
        rintro v u ⟨hv1, hv2⟩ ⟨hu1, hu2⟩
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ⟨by simpa [mul_smul] using (hv1 (u • x) (hu1 x hx).1).1,
            by simpa [mul_inv_rev, mul_smul] using (hu1 (v⁻¹ • x) (hv1 x hx).2).2⟩
        · intro x
          calc ((v * u) • x) (4 : Fin 8) = (v • (u • x)) (4 : Fin 8) :=
                congrArg (fun f : Fin Tag.E8.rank → ℤ => f (4 : Fin 8)) (mul_smul v u x)
            _ = (u • x) (4 : Fin 8) := hv2 (u • x)
            _ = x (4 : Fin 8) := hu2 x
      inv_mem' := by
        rintro v ⟨hv1, hv2⟩
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ⟨(hv1 x hx).2, by simpa using (hv1 x hx).1⟩
        · intro x
          have h := (hv2 (v⁻¹ • x)).symm
          have h2 := congrArg (fun f : Fin Tag.E8.rank → ℤ => f (4 : Fin 8))
            (smul_inv_smul v x)
          exact h.trans h2 }
  have hgen : {s : WeylGroup Tag.E8 | ∃ γ ∈ kerA1, s = rootReflection γ} ⊆ H := by
    rintro s ⟨γ, hγ, rfl⟩
    obtain ⟨hγroot, hγ4, hγ5, hγ6, hγ7⟩ :
        IsRoot Tag.E8 γ ∧ γ (4 : Fin 8) = 0 ∧ γ (5 : Fin 8) = 0 ∧
          γ (6 : Fin 8) = 0 ∧ γ (7 : Fin 8) = 0 := hγ
    have hγ0 : γ ⬝ᵥ e8TwoFiveKac5A = 0 :=
      (dotProduct_e8TwoFiveKac5A γ).trans hγ4
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨hxroot, hx4, hx5, hx6, hx7⟩ :
          IsRoot Tag.E8 x ∧ x (4 : Fin 8) = 0 ∧ x (5 : Fin 8) = 0 ∧
            x (6 : Fin 8) = 0 ∧ x (7 : Fin 8) = 0 := hx
      have hmem : rootReflection γ • x ∈ kerA1 := by
        refine ⟨IsRoot.smul hxroot (rootReflection γ), ?_, ?_, ?_, ?_⟩
        · rw [rootReflection_smul hγroot]
          show x (4 : Fin 8) - corootPair γ x • γ (4 : Fin 8) = 0
          rw [hx4, hγ4, smul_zero, sub_zero]
        · rw [rootReflection_smul hγroot]
          show x (5 : Fin 8) - corootPair γ x • γ (5 : Fin 8) = 0
          rw [hx5, hγ5, smul_zero, sub_zero]
        · rw [rootReflection_smul hγroot]
          show x (6 : Fin 8) - corootPair γ x • γ (6 : Fin 8) = 0
          rw [hx6, hγ6, smul_zero, sub_zero]
        · rw [rootReflection_smul hγroot]
          show x (7 : Fin 8) - corootPair γ x • γ (7 : Fin 8) = 0
          rw [hx7, hγ7, smul_zero, sub_zero]
      exact ⟨hmem, by rw [rootReflection_inv hγroot]; exact hmem⟩
    · intro x
      rw [rootReflection_smul hγroot]
      show x (4 : Fin 8) - corootPair γ x • γ (4 : Fin 8) = x (4 : Fin 8)
      rw [hγ4, smul_zero, sub_zero]
  have hwH : w ∈ H := (Subgroup.closure_le H).2 hgen hw
  obtain ⟨g₀, hg₀root, hg₀u, hg₀card⟩ := kerA_type.1
  have hprof : ∀ b ∈ kerA1,
      iform (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀) b = iform (w • g₀) b := by
    intro b hb
    have hc : w⁻¹ • b ∈ kerA1 := (hwH.1 b hb).2
    have hwc : w • (w⁻¹ • b) = b := smul_inv_smul w b
    have hσ2c : ((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) (w⁻¹ • b) = b := by
      have h := hwact (w⁻¹ • b) hc
      rwa [hwc] at h
    have hiso := ks_iform_iterate σ hσ.2.1 2 g₀ (w⁻¹ • b)
    rw [hσ2c] at hiso
    have hwiso : iform (w • g₀) b = iform g₀ (w⁻¹ • b) := by
      have h := iform_smul w g₀ (w⁻¹ • b)
      rwa [hwc] at h
    rw [hiso, hwiso]
  have hrootsig : IsRoot Tag.E8 (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀) := by
    have h1 : IsRoot Tag.E8 (σ g₀) := (hσ.1 g₀).2 hg₀root
    change IsRoot Tag.E8 (σ (σ g₀))
    exact (hσ.1 (σ g₀)).2 h1
  have hrootw : IsRoot Tag.E8 (w • g₀) := IsRoot.smul hg₀root w
  have hprof_eq := kerA_profile (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀) (w • g₀)
    hrootsig hrootw hprof
  have hw4 : (w • g₀) (4 : Fin 8) = g₀ (4 : Fin 8) := hwH.2 g₀
  have hw_eq : (w • g₀) ⬝ᵥ e8TwoFiveKac5A = g₀ ⬝ᵥ e8TwoFiveKac5A :=
    ((dotProduct_e8TwoFiveKac5A (w • g₀)).trans hw4).trans
      (dotProduct_e8TwoFiveKac5A g₀).symm
  have hw_mod : ((w • g₀) ⬝ᵥ e8TwoFiveKac5A) % 5 = 1 := by
    rw [hw_eq]
    exact hg₀u
  have hmod4 : (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀ ⬝ᵥ e8TwoFiveKac5A) % 5 = 4 := by
    have h4 := ks_modEq_two σ hσ hg₀root
    have hg0mod : (g₀ ⬝ᵥ e8TwoFiveKac5A) ≡ 1 [ZMOD 5] := hg₀u
    have h4' : (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀ ⬝ᵥ e8TwoFiveKac5A) ≡
        4 [ZMOD 5] := by
      refine h4.trans ?_
      have h := hg0mod.mul_left 4
      rw [show (4 : ℤ) * 1 = 4 by ring] at h
      exact h
    have h := h4'
    change (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀ ⬝ᵥ e8TwoFiveKac5A) % 5 =
      (4 : ℤ) % 5 at h
    rw [h]
    norm_num
  have hmod1 : (((σ : (Fin Tag.E8.rank → ℤ) → _)^[2]) g₀ ⬝ᵥ e8TwoFiveKac5A) % 5 = 1 := by
    have h := hprof_eq
    rw [hw_mod] at h
    exact h
  omega

private theorem kernelA_normal
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) 5)
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hσ : IsFrobLike σ e8TwoFiveKac5A) :
    E8TwoFiveKernelA σ (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ e8TwoFiveKac5A i)) := by
  let χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ :=
    rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ e8TwoFiveKac5A i)
  have hK : kernelRoots χ = kerA1 ∪ kerA2 := kerA_union hζ
  have hne : kerA1 ≠ kerA2 := by
    intro heq
    obtain ⟨a, ha⟩ := kerA1_nonempty
    have ha2 : a ∈ kerA2 := heq ▸ ha
    have hz : a ∈ kerA1 ∩ kerA2 := ⟨ha, ha2⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp kerA_disjoint] at hz
    exact hz
  have h12 : σ '' kerA1 = kerA2 := by
    rcases kerA_image σ hσ with h | h
    · exact absurd h (kerA_not_fix σ hσ)
    · exact h
  have h21 : σ '' kerA2 = kerA1 := kerA_swap_back σ hσ h12
  have hfin1 : kerA1.Finite := Set.finite_of_ncard_pos (by rw [kerA_ncard.1]; norm_num)
  have hfin2 : kerA2.Finite := Set.finite_of_ncard_pos (by rw [kerA_ncard.2]; norm_num)
  have hncard : (kernelRoots χ).ncard = 40 := by
    rw [hK, Set.ncard_union_eq kerA_disjoint hfin1 hfin2, kerA_ncard.1, kerA_ncard.2]
  obtain ⟨i₁, i₂, hne', hall, hP₁, hP₂⟩ :=
    two_components χ kerA1 kerA2 hK kerA_disjoint kerA1_nonempty kerA2_nonempty kerA_orth
      kerA_conn.1 kerA_conn.2
  unfold E8TwoFiveKernelA
  refine ⟨hncard, i₁, i₂, hne', hall, ?_, ?_, ?_, ?_⟩
  · rw [hP₁, kerA1_rank]
  · rw [hP₁, kerA_ncard.1]
  · rw [hP₁, hP₂]
    exact h12
  · exact twistKind_suN σ χ i₁ kerA1 hP₁
      (orbitLength_swap σ kerA1 kerA2 h12 h21 hne) kerA1_rank (kerA_ncard.1)
      (kerA_not_inner σ hσ)

private theorem kerB_stable (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hσ : IsFrobLike σ e8TwoFiveKac5B) : σ '' kerB = kerB := by
  have hset : kerB = {γ | IsRoot Tag.E8 γ ∧ (5 : ℤ) ∣ γ ⬝ᵥ e8TwoFiveKac5B} := by
    ext γ
    exact (kerB_iff γ).symm
  rw [hset]
  exact ks_stable_image σ hσ

private theorem kerB_not_inner
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hσ : IsFrobLike σ e8TwoFiveKac5B) :
    ¬ twistInner kerB (σ : (Fin Tag.E8.rank → ℤ) → _) := by
  rintro ⟨w, hw, hwact⟩
  obtain ⟨γ₁, γ₂, _hγ₁def, _hγ₂def, hγ₁root, hγ₂root, hγ₁u, hγ₂u, horth, huniq, hprof,
    δ, hδroot, hδne, hδγ₁, hδγ₂⟩ := kerB_profile
  let H : Subgroup (WeylGroup Tag.E8) :=
    { carrier := {v | (∀ x ∈ kerB, v • x ∈ kerB ∧ v⁻¹ • x ∈ kerB) ∧
          ∀ x : Fin Tag.E8.rank → ℤ, (∀ b ∈ kerB, iform x b = 0) → v • x = x}
      one_mem' := by
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ⟨by simpa using hx, by simpa using hx⟩
        · intro x _
          rw [one_smul]
      mul_mem' := by
        rintro v u ⟨hv1, hv2⟩ ⟨hu1, hu2⟩
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ⟨by simpa [mul_smul] using (hv1 (u • x) (hu1 x hx).1).1,
            by simpa [mul_inv_rev, mul_smul] using (hu1 (v⁻¹ • x) (hv1 x hx).2).2⟩
        · intro x hxorth
          calc (v * u) • x = v • (u • x) := mul_smul v u x
            _ = v • x := by rw [hu2 x hxorth]
            _ = x := hv2 x hxorth
      inv_mem' := by
        rintro v ⟨hv1, hv2⟩
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ⟨(hv1 x hx).2, by simpa using (hv1 x hx).1⟩
        · intro x hxorth
          have hxorth' : ∀ b ∈ kerB, iform (v⁻¹ • x) b = 0 := by
            intro b hb
            have hb' : v • b ∈ kerB := (hv1 b hb).1
            have h := iform_smul v (v⁻¹ • x) b
            rw [smul_inv_smul] at h
            rw [← h]
            exact hxorth (v • b) hb'
          have h := hv2 (v⁻¹ • x) hxorth'
          rw [smul_inv_smul] at h
          exact h.symm }
  have hgen : {s : WeylGroup Tag.E8 | ∃ b ∈ kerB, s = rootReflection b} ⊆ H := by
    rintro s ⟨b, hb, rfl⟩
    have hbunpack : IsRoot Tag.E8 b ∧ b (0 : Fin 8) = 0 ∧ b (7 : Fin 8) = 0 := hb
    obtain ⟨hbroot, hb0, hb7⟩ := hbunpack
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨hxroot, hx0, hx7⟩ : IsRoot Tag.E8 x ∧ x (0 : Fin 8) = 0 ∧
          x (7 : Fin 8) = 0 := hx
      have hmem : rootReflection b • x ∈ kerB := by
        refine ⟨IsRoot.smul hxroot (rootReflection b), ?_, ?_⟩
        · rw [rootReflection_smul hbroot]
          show x (0 : Fin 8) - corootPair b x • b (0 : Fin 8) = 0
          rw [hx0, hb0, smul_zero, sub_zero]
        · rw [rootReflection_smul hbroot]
          show x (7 : Fin 8) - corootPair b x • b (7 : Fin 8) = 0
          rw [hx7, hb7, smul_zero, sub_zero]
      exact ⟨hmem, by rw [rootReflection_inv hbroot]; exact hmem⟩
    · intro x hxorth
      exact rootReflection_smul_of_iform_eq_zero hbroot
        ((iform_comm b x).trans (hxorth b hb))
  have hwH : w ∈ H := (Subgroup.closure_le H).2 hgen hw
  have hstable : σ '' kerB = kerB := kerB_stable σ hσ
  have hsymm_mem : ∀ b ∈ kerB, σ.symm b ∈ kerB := by
    intro b hb
    have hb' : b ∈ σ '' kerB := by rw [hstable]; exact hb
    obtain ⟨c, hc, hceq⟩ := hb'
    have hsc : σ.symm b = c := by
      rw [← hceq]
      simp
    rw [hsc]
    exact hc
  have hwγ₂ : w • γ₂ = γ₂ := hwH.2 γ₂ (fun b hb => (horth b hb).2)
  have hσγ₁root : IsRoot Tag.E8 (σ γ₁) := (hσ.1 γ₁).2 hγ₁root
  have hσγ₁orth : ∀ b ∈ kerB, iform (σ γ₁) b = 0 := by
    intro b hb
    have hc : σ.symm b ∈ kerB := hsymm_mem b hb
    have hiso := hσ.2.1 γ₁ (σ.symm b)
    rw [show σ (σ.symm b) = b from σ.apply_symm_apply b] at hiso
    rw [hiso]
    exact (horth (σ.symm b) hc).1
  have hσγ₁u : (σ γ₁ ⬝ᵥ e8TwoFiveKac5B) % 5 = 2 := by
    have h1 : (σ γ₁ ⬝ᵥ e8TwoFiveKac5B) ≡ 2 * (γ₁ ⬝ᵥ e8TwoFiveKac5B) [ZMOD 5] :=
      hσ.2.2 γ₁ hγ₁root
    have hγ1mod : (γ₁ ⬝ᵥ e8TwoFiveKac5B) ≡ 1 [ZMOD 5] := hγ₁u
    have h2 : 2 * (γ₁ ⬝ᵥ e8TwoFiveKac5B) ≡ 2 [ZMOD 5] := by
      simpa using hγ1mod.mul_left 2
    have htarget : (σ γ₁ ⬝ᵥ e8TwoFiveKac5B) ≡ 2 [ZMOD 5] := h1.trans h2
    have hh := htarget
    change (σ γ₁ ⬝ᵥ e8TwoFiveKac5B) % 5 = (2 : ℤ) % 5 at hh
    rw [hh]
    norm_num
  have hσγ₁ : σ γ₁ = γ₂ := huniq (σ γ₁) hσγ₁root hσγ₁orth hσγ₁u
  have hsame : ∀ b ∈ kerB, iform (σ δ) b = iform (w • δ) b := by
    intro b hb
    have hc : w⁻¹ • b ∈ kerB := (hwH.1 b hb).2
    have hwc : w • (w⁻¹ • b) = b := smul_inv_smul w b
    have hσc : σ (w⁻¹ • b) = b := by
      have h := hwact (w⁻¹ • b) hc
      rwa [hwc] at h
    have hiso1 := hσ.2.1 δ (w⁻¹ • b)
    rw [hσc] at hiso1
    have hiso2 := iform_smul w δ (w⁻¹ • b)
    rw [hwc] at hiso2
    exact hiso1.trans hiso2.symm
  have hσδroot : IsRoot Tag.E8 (σ δ) := (hσ.1 δ).2 hδroot
  have hwδroot : IsRoot Tag.E8 (w • δ) := IsRoot.smul hδroot w
  have hneσδ : ∃ b ∈ kerB, iform (σ δ) b ≠ 0 := by
    obtain ⟨c, hc, hcne⟩ := hδne
    refine ⟨σ c, ?_, ?_⟩
    · have hmem : σ c ∈ σ '' kerB := ⟨c, hc, rfl⟩
      rw [hstable] at hmem
      exact hmem
    · have hiso := hσ.2.1 δ c
      rwa [hiso]
  have hiff := hprof (σ δ) (w • δ) hσδroot hwδroot hneσδ hsame
  have hleft : iform (σ δ) γ₂ ≠ 0 := by
    rw [← hσγ₁]
    rw [hσ.2.1]
    exact hδγ₁
  have hright : iform (w • δ) γ₂ = 0 := by
    rw [← hwγ₂, iform_smul w δ γ₂]
    exact hδγ₂
  exact hleft (hiff.mpr hright)

private theorem kernelB_normal
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) 5)
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hσ : IsFrobLike σ e8TwoFiveKac5B) :
    E8TwoFiveKernelB σ (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ e8TwoFiveKac5B i)) := by
  let χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ :=
    rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ e8TwoFiveKac5B i)
  have hK : kernelRoots χ = kerB := kerB_union hζ
  obtain ⟨i, hall, hP⟩ := one_component χ kerB hK kerB_nonempty kerB_conn
  unfold E8TwoFiveKernelB
  refine ⟨?_, i, hall, ?_, ?_, ?_⟩
  · rw [hK, kerB_ncard]
  · rw [hP, kerB_rank]
  · rw [hP, kerB_ncard]
  · exact twistKind_twoD σ χ i kerB hP
      (orbitLength_fix σ kerB (kerB_stable σ hσ)) kerB_rank kerB_ncard
      (kerB_not_inner σ hσ)

private theorem kacSetup
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) :
    ∃ (ζ : Lˣ) (w : WeylGroup Tag.E8) (μ : Fin 8 → ℤ), IsPrimitiveRoot (ζ : L) 5 ∧
      (∀ β, rootChar a β = ζ ^ ((w • β) ⬝ᵥ μ)) ∧ IsFrobLike (conjPerm w S.ρ) μ ∧
      WeylConj w S.ρ (conjPerm w S.ρ) (rootCharHom a)
        (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ μ i)) ∧
      (μ = e8TwoFiveKac5A ∨ μ = e8TwoFiveKac5B) := by
  obtain ⟨hq, hT, hΓ, ha5, hne⟩ := h
  obtain ⟨ζ, hζ⟩ := exists_primRoot5 S
  obtain ⟨w, μ, hμ, hχ⟩ := kacE8.exists_weyl_normal (p := 5) (by norm_num) hζ a ha5
  have hfl : IsFrobLike (conjPerm w S.ρ) μ :=
    isFrobLike_conj S ⟨hq, hT, hΓ, ha5, hne⟩ hζ w μ hχ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    refine hne ?_
    have ha1 : a = 1 := by
      funext i
      have h1 := hχ (Pi.single i 1)
      have h2 : rootChar a (Pi.single i 1 : Fin Tag.E8.rank → ℤ) = a i := by
        simpa using rootChar_nsmul_single a i 1
      rw [h2] at h1
      simpa using h1
    subst ha1
    exact Units.ext rootDiag_one
  have hW : WeylConj w S.ρ (conjPerm w S.ρ) (rootCharHom a)
      (rootCharHom (fun i : Fin Tag.E8.rank => ζ ^ μ i)) :=
    ⟨fun x => conjPerm_smul w S.ρ x, fun β => by
      show rootChar a β = rootChar (fun i : Fin Tag.E8.rank => ζ ^ μ i) (w • β)
      rw [hχ β, KacData.rootChar_eq_zpow]⟩
  exact ⟨ζ, w, μ, hζ, hχ, hfl, hW,
    e8TwoFive_fstable_kac μ hμ hμ0 (conjPerm w S.ρ) hfl.1 hfl.2.1 hfl.2.2⟩

private theorem kerB_orth_roots :
    ∀ g : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 g → (∀ b ∈ kerB, iform g b = 0) →
      g = E8TwoFiveFin.vecOf [-2, -3, -4, -6, -5, -4, -3, -2] ∨
      g = -E8TwoFiveFin.vecOf [-2, -3, -4, -6, -5, -4, -3, -2] ∨
      g = E8TwoFiveFin.vecOf [2, 2, 3, 4, 3, 2, 1, 0] ∨
      g = -E8TwoFiveFin.vecOf [2, 2, 3, 4, 3, 2, 1, 0] := by
  rw [E8TwoFiveFin.forall_root_iff]
  intro l hl h
  have hB : ∀ l' ∈ E8TwoFiveFin.rootsL, l'.getD 0 0 = 0 → l'.getD 7 0 = 0 →
      E8TwoFiveFin.formL l l' = 0 := by
    intro l' hl' h0 h7
    have hb : E8TwoFiveFin.vecOf l' ∈ kerB := ⟨E8TwoFiveFin.isRoot_vecOf hl', h0, h7⟩
    have := h _ hb
    rwa [E8TwoFiveFin.iform_vecOf hl hl'] at this
  have key : ∀ l ∈ E8TwoFiveFin.rootsL,
      (∀ l' ∈ E8TwoFiveFin.rootsL, l'.getD 0 0 = 0 → l'.getD 7 0 = 0 →
        E8TwoFiveFin.formL l l' = 0) →
      l = [-2, -3, -4, -6, -5, -4, -3, -2] ∨ l = [2, 3, 4, 6, 5, 4, 3, 2] ∨
        l = [2, 2, 3, 4, 3, 2, 1, 0] ∨ l = [-2, -2, -3, -4, -3, -2, -1, 0] := by
    decide +kernel
  rcases key l hl hB with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr (Or.inl ?_)
    funext i
    fin_cases i <;> rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr ?_))
    funext i
    fin_cases i <;> rfl

private theorem kerB_orth_lattice :
    ∀ z : Fin Tag.E8.rank → ℤ, (∀ b ∈ kerB, iform z b = 0) →
      ∃ m n : ℤ, z = m • E8TwoFiveFin.vecOf [-2, -3, -4, -6, -5, -4, -3, -2] +
        n • E8TwoFiveFin.vecOf [2, 2, 3, 4, 3, 2, 1, 0] := by
  intro z hz
  have hz' : ∀ s : List ℤ, s ∈ E8TwoFiveFin.rootsL → s.getD 0 0 = 0 → s.getD 7 0 = 0 →
      E8TwoFiveFin.dotL (E8TwoFiveFin.cartanL.map fun row => E8TwoFiveFin.dotL row (List.ofFn z))
        s = 0 := by
    intro s hs h0 h7
    have := hz (E8TwoFiveFin.vecOf s) ⟨E8TwoFiveFin.isRoot_vecOf hs, h0, h7⟩
    rw [E8TwoFiveFin.iform_eq_dotL,
      E8TwoFiveFin.ofFn_vecOf (E8TwoFiveFin.length_of_mem_rootsL hs)] at this
    exact this
  have e2 := hz' [0, 1, 0, 0, 0, 0, 0, 0] (by decide +kernel) rfl rfl
  have e3 := hz' [0, 0, 1, 0, 0, 0, 0, 0] (by decide +kernel) rfl rfl
  have e4 := hz' [0, 0, 0, 1, 0, 0, 0, 0] (by decide +kernel) rfl rfl
  have e5 := hz' [0, 0, 0, 0, 1, 0, 0, 0] (by decide +kernel) rfl rfl
  have e6 := hz' [0, 0, 0, 0, 0, 1, 0, 0] (by decide +kernel) rfl rfl
  have e7 := hz' [0, 0, 0, 0, 0, 0, 1, 0] (by decide +kernel) rfl rfl
  have hofn : List.ofFn z = [z (0 : Fin 8), z (1 : Fin 8), z (2 : Fin 8), z (3 : Fin 8),
      z (4 : Fin 8), z (5 : Fin 8), z (6 : Fin 8), z (7 : Fin 8)] := rfl
  rw [hofn] at e2 e3 e4 e5 e6 e7
  simp [E8TwoFiveFin.dotL, E8TwoFiveFin.cartanL] at e2 e3 e4 e5 e6 e7
  have hp7 : z (7 : Fin 8) % 2 = 0 := by omega
  have hp0 : (z (0 : Fin 8) - z (7 : Fin 8)) % 2 = 0 := by omega
  refine ⟨-(z (7 : Fin 8)) / 2, (z (0 : Fin 8) - z (7 : Fin 8)) / 2, ?_⟩
  have a0 : z (0 : Fin 8) = z (0 : Fin Tag.E8.rank) := rfl
  have a1 : z (1 : Fin 8) = z ⟨1, by decide +kernel⟩ := rfl
  have a2 : z (2 : Fin 8) = z ⟨2, by decide +kernel⟩ := rfl
  have a3 : z (3 : Fin 8) = z ⟨3, by decide +kernel⟩ := rfl
  have a4 : z (4 : Fin 8) = z ⟨4, by decide +kernel⟩ := rfl
  have a5 : z (5 : Fin 8) = z ⟨5, by decide +kernel⟩ := rfl
  have a6 : z (6 : Fin 8) = z ⟨6, by decide +kernel⟩ := rfl
  have a7 : z (7 : Fin 8) = z ⟨7, by decide +kernel⟩ := rfl
  funext i
  fin_cases i <;> simp [E8TwoFiveFin.vecOf] <;> omega

private theorem kerB_eq_parabolic :
    kerB = parabolicRoots Tag.E8 {j : Fin Tag.E8.rank | 1 ≤ j.val ∧ j.val ≤ 6} := by
  ext γ
  constructor
  · rintro ⟨hγ, h0, h7⟩
    refine ⟨hγ, fun i hi => ?_⟩
    have hlt : i.val < 8 := i.isLt
    have hv : i.val = 0 ∨ i.val = 7 := by
      simp only [Set.mem_setOf_eq, not_and_or, not_le] at hi
      omega
    rcases hv with hv | hv
    · have : i = (0 : Fin 8) := Fin.ext hv
      rw [this]
      exact h0
    · have : i = (7 : Fin 8) := Fin.ext hv
      rw [this]
      exact h7
  · rintro ⟨hγ, hJ⟩
    refine ⟨hγ, hJ (0 : Fin 8) ?_, hJ (7 : Fin 8) ?_⟩
    · show ¬ (1 ≤ (0 : Fin 8).val ∧ (0 : Fin 8).val ≤ 6)
      decide +kernel
    · show ¬ (1 ≤ (7 : Fin 8).val ∧ (7 : Fin 8).val ≤ 6)
      decide +kernel

theorem e8TwoFive_kernelType
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a) :
    E8TwoFiveKernelA S.ρ (rootCharHom a) ∨ E8TwoFiveKernelB S.ρ (rootCharHom a) := by
  obtain ⟨ζ, w, μ, hζ, -, hfl, hW, hμ⟩ := kacSetup S h
  rcases hμ with rfl | rfl
  · exact Or.inl (kernelA_of_weyl hW (kernelA_normal hζ _ hfl))
  · exact Or.inr (kernelB_of_weyl hW (kernelB_normal hζ _ hfl))

theorem e8TwoFive_kernelB_data
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hB : E8TwoFiveKernelB S.ρ (rootCharHom a)) :
    ∃ (v : WeylGroup Tag.E8) (ζ : Lˣ) (l₁ l₂ : Fin Tag.E8.rank → ℤ),
      IsPrimitiveRoot (ζ : L) 5 ∧
      l₁ = v • E8TwoFiveFin.vecOf [-2, -3, -4, -6, -5, -4, -3, -2] ∧
      l₂ = v • E8TwoFiveFin.vecOf [2, 2, 3, 4, 3, 2, 1, 0] ∧
      kernelRoots (rootCharHom a) = (fun x => v • x) ''
        parabolicRoots Tag.E8 {j : Fin Tag.E8.rank | 1 ≤ j.val ∧ j.val ≤ 6} ∧
      IsRoot Tag.E8 l₁ ∧ IsRoot Tag.E8 l₂ ∧
      (∀ β ∈ kernelRoots (rootCharHom a), iform β l₁ = 0 ∧ iform β l₂ = 0) ∧
      S.ρ l₁ = l₂ ∧ S.ρ l₂ = -l₁ ∧ rootChar a l₁ = ζ ∧ rootChar a l₂ = ζ ^ 2 ∧
      ∀ y : Fin Tag.E8.rank → ℤ, (∀ β ∈ kernelRoots (rootCharHom a), iform β y = 0) →
        ∃ m n : ℤ, y = m • l₁ + n • l₂ := by
  obtain ⟨ζ, w, μ, hζ, hχ, hfl, hW, hμ⟩ := kacSetup S h
  rcases hμ with rfl | rfl
  · exfalso
    have hA := (kernelA_of_weyl hW (kernelA_normal hζ _ hfl)).1
    have hB' := hB.1
    omega
  · obtain ⟨γ₁, γ₂, h₁, h₂, hr₁, hr₂, hu₁, hu₂, horth, huniq, -, -⟩ := kerB_profile
    have hz5 : ζ ^ (5 : ℤ) = 1 := by
      apply Units.ext
      simpa using hζ.pow_eq_one
    have hstab : conjPerm w S.ρ '' kerB = kerB := kerB_stable _ hfl
    have hσorth : ∀ g, (∀ b ∈ kerB, iform g b = 0) →
        ∀ b ∈ kerB, iform (conjPerm w S.ρ g) b = 0 := by
      intro g hg b hb
      rw [← hstab] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      rw [hfl.2.1]
      exact hg b' hb'
    have hu1 : (conjPerm w S.ρ γ₁ ⬝ᵥ e8TwoFiveKac5B) % 5 = 2 := by
      have := hfl.2.2 γ₁ hr₁
      unfold Int.ModEq at this
      omega
    have hs1 : conjPerm w S.ρ γ₁ = γ₂ :=
      huniq _ ((hfl.1 γ₁).2 hr₁) (hσorth γ₁ fun b hb => (horth b hb).1) hu1
    have hs2 : conjPerm w S.ρ γ₂ = -γ₁ := by
      have hr : IsRoot Tag.E8 (conjPerm w S.ρ γ₂) := (hfl.1 γ₂).2 hr₂
      have hu : (conjPerm w S.ρ γ₂ ⬝ᵥ e8TwoFiveKac5B) % 5 = 4 := by
        have := hfl.2.2 γ₂ hr₂
        unfold Int.ModEq at this
        omega
      have hcases := kerB_orth_roots _ hr (hσorth γ₂ fun b hb => (horth b hb).2)
      rw [← h₁, ← h₂] at hcases
      rcases hcases with hc | hc | hc | hc
      · rw [hc] at hu
        omega
      · exact hc
      · rw [hc] at hu
        omega
      · have hneg : (-γ₂) ⬝ᵥ e8TwoFiveKac5B = -(γ₂ ⬝ᵥ e8TwoFiveKac5B) := neg_dotProduct _ _
        rw [hc, hneg] at hu
        omega
    have h0 : kerB = (fun x => w • x) '' kernelRoots (rootCharHom a) := by
      have := WeylConj.kernelRoots_eq hW
      rwa [kerB_union hζ] at this
    have hKb : ∀ k ∈ kernelRoots (rootCharHom a), w • k ∈ kerB := by
      intro k hk
      rw [h0]
      exact ⟨k, hk, rfl⟩
    have hbK : ∀ b ∈ kerB, ∃ k ∈ kernelRoots (rootCharHom a), w • k = b := by
      intro b hb
      rw [h0] at hb
      exact hb
    refine ⟨w⁻¹, ζ, w⁻¹ • γ₁, w⁻¹ • γ₂, hζ, by rw [h₁], by rw [h₂], ?_, (isRoot_smul_iff w⁻¹).2 hr₁,
      (isRoot_smul_iff w⁻¹).2 hr₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hK : kernelRoots (rootCharHom a) = (fun x => w⁻¹ • x) '' kerB := by
        ext x
        constructor
        · intro hx
          exact ⟨w • x, hKb x hx, inv_smul_smul w x⟩
        · rintro ⟨b, hb, rfl⟩
          obtain ⟨k, hk, rfl⟩ := hbK b hb
          simpa using hk
      rw [hK, kerB_eq_parabolic]
    · intro β hβ
      have e1 : iform β (w⁻¹ • γ₁) = iform (w • β) γ₁ := by
        rw [← iform_smul w β (w⁻¹ • γ₁), smul_inv_smul]
      have e2 : iform β (w⁻¹ • γ₂) = iform (w • β) γ₂ := by
        rw [← iform_smul w β (w⁻¹ • γ₂), smul_inv_smul]
      rw [e1, e2, iform_comm (w • β) γ₁, iform_comm (w • β) γ₂]
      exact horth _ (hKb β hβ)
    · have e := conjPerm_smul w S.ρ (w⁻¹ • γ₁)
      rw [smul_inv_smul, hs1] at e
      rw [e, inv_smul_smul]
    · have e := conjPerm_smul w S.ρ (w⁻¹ • γ₂)
      rw [smul_inv_smul, hs2] at e
      calc S.ρ (w⁻¹ • γ₂) = w⁻¹ • w • S.ρ (w⁻¹ • γ₂) := (inv_smul_smul _ _).symm
        _ = w⁻¹ • (-γ₁) := by rw [← e]
        _ = -(w⁻¹ • γ₁) := smul_neg _ _
    · rw [hχ, smul_inv_smul, zpow_eq_zpow_emod _ hz5, hu₁, zpow_one]
    · rw [hχ, smul_inv_smul, zpow_eq_zpow_emod _ hz5, hu₂]
      norm_num
    · intro y hy
      have hy' : ∀ b ∈ kerB, iform (w • y) b = 0 := by
        intro b hb
        obtain ⟨k, hk, rfl⟩ := hbK b hb
        rw [iform_smul, iform_comm]
        exact hy k hk
      obtain ⟨m, n, hmn⟩ := kerB_orth_lattice _ hy'
      refine ⟨m, n, ?_⟩
      rw [← h₁, ← h₂] at hmn
      calc y = w⁻¹ • w • y := (inv_smul_smul w y).symm
        _ = w⁻¹ • (m • γ₁ + n • γ₂) := by rw [hmn]
        _ = m • (w⁻¹ • γ₁) + n • (w⁻¹ • γ₂) := by
          rw [smul_add, smul_comm w⁻¹ m, smul_comm w⁻¹ n]

end FieldFiveE8

end CFSG.StandardType
