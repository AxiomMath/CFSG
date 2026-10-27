module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkRank
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSpNs

public section

namespace CFSG.StandardType

namespace WitOmBlk

open CFSG.Assembly Matrix Module QuadraticMap SUTB NoOffOm OrdPNsGen OrdPNsOm
open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem bstarWit_of_component {G Γ : Type} [Group G] [Finite G] [Group Γ] {p : ℕ}
    {Bs : Subgroup G}
    (t : StatedLieTag) (f : ℕ) (φ : Γ →* G) (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range)
    {a : Γ} (ha1 : a ≠ 1) (haB : φ a ∈ Bs) {U : Subgroup Γ} (hUq : CFSG.IsQuasisimple ↥U)
    (hUa : ∀ l ∈ U, l * a = a * l) (hUn : ∀ g : Γ, g * a = a * g → ∀ l ∈ U, g * l * g⁻¹ ∈ U)
    {F : Fin p × Fin p → Γ} (hF : ∀ c : Γ, φ c ∈ Bs → (∀ l ∈ U, c * l = l * c) → c ∈ Set.range F) :
    GGSixBstarWit p Bs φ.range t f (φ a) := by
  have hker : φ.ker ≤ Subgroup.center Γ := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]
    exact bot_le
  have hle : U.map φ ≤ φ.range ⊓ Subgroup.centralizer {φ a} := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨⟨l, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, hUa l hl]
  refine ⟨haB, fun h => ha1 (hφ (h.trans (map_one φ).symm)), U.map φ,
    ⟨hle, ?_, SURepair.isQuasisimple_map_of_isQuasisimple hker hUq⟩, Or.inl ?_⟩
  · refine IsSubnormal.step hle ?_ (IsSubnormal.refl _)
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ y ⟨l, hl, rfl⟩ ⟨⟨c, rfl⟩, hyc⟩
    have hc : c * a = a * c := hφ (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hyc
      rw [map_mul, map_mul]
      exact this)
    exact ⟨c * l * c⁻¹, hUn c hc l hl, by rw [map_mul, map_mul, map_inv]⟩
  · have hsub : ((Bs ⊓ Subgroup.centralizer (U.map φ : Set G) : Subgroup G) : Set G) ⊆
        Set.range (φ ∘ F) := by
      rintro β ⟨hβB, hβc⟩
      obtain ⟨c, rfl⟩ := hBφ hβB
      have hcU : ∀ l ∈ U, c * l = l * c := fun l hl => hφ (by
        rw [map_mul, map_mul]
        exact (Subgroup.mem_centralizer_iff.mp hβc _ ⟨l, hl, rfl⟩).symm)
      obtain ⟨q, hq⟩ := hF c hβB hcU
      exact ⟨q, by rw [Function.comp_apply, hq]⟩
    calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (U.map φ : Set G) : Subgroup G)
        ≤ Nat.card (Set.range (φ ∘ F)) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card (Fin p × Fin p) := Finite.card_range_le _
      _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, _root_.sq]

section Model

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem matrixLinearIso_apply (X : GL (Fin d) K) (v : Fin d → K) :
    matrixLinearIso X v = glin X v := by
  rw [glin_apply]
  rfl

theorem mem_orthDerived_iff {X : GL (Fin d) K} :
    matrixLinearIso X ∈ CFSG.RankThree.Classical2.orthDerived Q ↔ X ∈ matrixDerived Q := by
  rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q]
  constructor
  · rintro ⟨Y, hY, hYX⟩
    rwa [matrixLinearIso.injective hYX] at hY
  · intro hX
    exact ⟨X, hX, rfl⟩

end Model

section Lin

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_of_eqOn_sup [FiniteDimensional K V] {U₁ U₂ : Submodule K V}
    (hU : NondegOn (polarBilin Q) (U₁ ⊔ U₂)) {f₁ f₂ : Module.End K V}
    (h₁ : ∀ x ∈ U₁, f₁ x = f₂ x) (h₂ : ∀ x ∈ U₂, f₁ x = f₂ x)
    (h₃ : ∀ y ∈ (U₁ ⊔ U₂).orthogonalBilin (polarBilin Q), f₁ y = f₂ y) : f₁ = f₂ := by
  ext v
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_add_orth hU v
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  simp only [map_add, h₁ x₁ hx₁, h₂ x₂ hx₂, h₃ y hy]

theorem one_le_of_not_dvd [Finite K] {p m : ℕ} (hp : p.Prime)
    (hm : Nat.lcm 2 (OrdPNS.ordQ K p) = 2 * m + 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (hpq' : ¬ p ∣ Nat.card K + 1) : 1 ≤ m := by
  by_contra h0
  have hm0 : m = 0 := by omega
  rw [hm0] at hm
  have hdvd : OrdPNS.ordQ K p ∣ 2 := by
    have := Nat.dvd_lcm_right 2 (OrdPNS.ordQ K p)
    rwa [hm] at this
  have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [OrdPNS.ordQ_def] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : (((Nat.card K : ℕ) : ZMod p) - 1) * (((Nat.card K : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp h2 with h | h
  · apply hpq
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, Nat.cast_one]
    exact h
  · apply hpq'
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h

end Lin

end WitOmBlk

end CFSG.StandardType
