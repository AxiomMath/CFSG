module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenActorTools
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusLayerCore
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl RootSpace
  CFSG.LieType.AlgebraicGroups EvenF4QPlus CFSG.RankThree.LocalRank EvenF4Actors
  CFSG.RankThree.GroupTheory.SteinbergBY
open scoped Pointwise

namespace EvenF4CyclotomicFourActors

variable {f : ℕ} (K : Type) [Field K]

theorem odd_centralizer_of_empty_kernel {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + 1) [Finite K] [CharP K 2] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 3)) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ)
    (x c : adjointGroup .F4 K) (hx : orderOf x = p) (x' : ModGL .F4 Ω)
    (hx' : x' = g⁻¹ * baseChangeGL (algebraMap K Ω) ((c * x * c⁻¹ : adjointGroup .F4 K) :
      ModGL .F4 K) * g)
    (hx'T : x' ∈ T₀) (hempty : {α | IsRoot .F4 α ∧ torusRootChar x' α = 1} = ∅) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨K₄, hK₄⟩ := exists_intermediateField_finrank K Ω 4
  have hx'ψ : x' = qplusConjTransport Ω g⁻¹ c x := by
    rw [hx', qplusConjTransport_apply, inv_inv]
  have hx'ord : orderOf x' = p := by
    rw [hx'ψ, orderOf_injective _ (qplusConjTransport_injective g⁻¹ c), hx]
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n hn
  obtain ⟨-, -, -, hprime, hchar⟩ :=
    hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨-, -, -, hT₀odd, -⟩ := hchar ‹_› K₄ hK₄
  obtain ⟨-, -, -, hdich⟩ := hprime p hp hp3 hpd
  obtain ⟨-, -, hreg⟩ := hdich x' hx'T hx'ord _ rfl
  have hD := map_centralizer_qplusConjTransport (K₂ := Ω) g⁻¹ c x
  rw [← hΓ, ← hx'ψ, hreg hempty] at hD
  rw [← Subgroup.card_map_of_injective (qplusConjTransport_injective g⁻¹ c), hD]
  exact hT₀odd

theorem exists_conj_mem_torus {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + 1) [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 3)) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ)
    (P₀ : Subgroup (adjointGroup .F4 K)) (hP₀ : IsPGroup p P₀) :
    ∃ c : adjointGroup .F4 K, ∀ x ∈ P₀,
      g⁻¹ * baseChangeGL (algebraMap K Ω) ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * g ∈
        T₀ := by
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n hn
  obtain ⟨-, -, -, hprime, -⟩ :=
    hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨-, hconj, -, -⟩ := hprime p hp hp3 hpd
  obtain ⟨c, hc⟩ := hconj P₀ hP₀
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨t₀, ht₀, he⟩ := hc ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have he' : baseChangeGL (algebraMap K Ω) ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) =
      g * t₀ * g⁻¹ := he.symm
  have e : g⁻¹ * (g * t₀ * g⁻¹) * g = t₀ := by group
  rw [he', e]
  exact ht₀

end EvenF4CyclotomicFourActors

open EvenF4CyclotomicFourActors

end CFSG.RankThree.Chevalley
