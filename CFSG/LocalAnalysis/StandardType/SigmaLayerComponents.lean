module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import CFSG.RankThree.PartOne.KE.SigmaEmbedCore
import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

section Layers

variable {C M : Type*} [Group C] [Group M]

theorem exists_map_eq_of_isComponentOf_of_layers [Finite C] {A : Subgroup C} (ψ : A →* M)
    (hψ : Function.Injective ψ) {ι : Type*} (P : ι → Subgroup M) (hle : ∀ i, P i ≤ ψ.range)
    (hq : ∀ i, CFSG.IsQuasisimple (P i))
    (hnorm : ∀ i, ∀ d : A, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) {Z : Set M}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hcent : ∀ d : A, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z) {X : Subgroup C}
    (hX : IsComponentOf X A) : ∃ i, (X.subgroupOf A).map ψ = P i ∧ Nonempty (X ≃* P i) := by
  obtain ⟨i, hi⟩ := E6Nonsplit.exists_eq_comap_of_isComponent ψ hψ P hle hq hnorm hZ hcent
    ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).1 hX)
  have hmap : (X.subgroupOf A).map ψ = P i := by
    rw [hi, Subgroup.map_comap_eq, inf_of_le_right (hle i)]
  exact ⟨i, hmap, ⟨(Subgroup.subgroupOfEquivOfLe hX.1).symm.trans
    (((X.subgroupOf A).equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr hmap))⟩⟩

end Layers

section Sigma


theorem sigma_components_of_stab {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]
    {ι' : Type} (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (Φ : ModGL τ L →* ModGL τ L) (hιΦ : ∀ y, Φ (ι y) = ι y)
    (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (P : ι' → Subgroup (ModGL τ L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints n Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S)
    {x : C} (hx : orderOf x = p) (c : C)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g0⁻¹ * ι (c * x * c⁻¹) * g0 →
      rootCharKernel a ⊆ S) :
    ∃ ψ : Subgroup.centralizer ({x} : Set C) →* ModGL τ L, Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0) ∧ (∀ i, P i ≤ ψ.range) ∧
      (∀ i, ∀ d : Subgroup.centralizer ({x} : Set C), ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) ∧
      ∀ X : Subgroup C, IsComponentOf X (Subgroup.centralizer ({x} : Set C)) →
        ∃ i, (X.subgroupOf (Subgroup.centralizer ({x} : Set C))).map ψ = P i ∧
          Nonempty (X ≃* P i) := by
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, hψn⟩ := sigma_embedding_core_of_stab ι hι hιC Φ hιΦ
    n g0 hg0C hg0 hperf hp hstab hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hx c hc hkerZ
  have hZ : ∀ a ∈ (subtorusSigma n Φ S : Set (ModGL τ L)), ∀ b ∈ (subtorusSigma n Φ S :
      Set (ModGL τ L)), a * b = b * a := fun a ha b hb =>
    CFSG.RankThree.PartOne.KE.torusGroup_comm
      (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf n Φ S ha)).1
      (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf n Φ S hb)).1
  exact ⟨ψ, hψinj, hψ, hPψ, hψn, fun X hX => exists_map_eq_of_isComponentOf_of_layers ψ hψinj P
    hPψ hPq hψn hZ (fun d hd => hPcent (ψ d) (hψHQ d) (mem_twistedFixedPoints.2 (hψR d)) hd) hX⟩

end Sigma

end CFSG.StandardType
