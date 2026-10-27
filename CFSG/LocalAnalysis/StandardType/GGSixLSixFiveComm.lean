module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveData

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section CommData

variable {G : Type} [Group G]

@[expose] def GGSixRootTwoCommData (D J V : Subgroup G) (r : G) : Prop :=
  r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ 4 ≤ Nat.card V ∧ r ∉ Subgroup.centralizer (J : Set G) ∧
    (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) ∧
    ∀ e ∈ D, e ≠ 1 →
      ⁅V, pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e}⁆ ≤
        Subgroup.zpowers r

variable [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem GGSixCtxV2.rootTwoData_of_commData (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {V : Subgroup G} {r : G} (hd : GGSixRootTwoCommData D J V r) :
    GGSixRootTwoData J V r := by
  obtain ⟨hrV, hVJ, hV, hV4, hrZ, hconj, hcomm⟩ := hd
  have : Fact p.Prime := ⟨h.prime⟩
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hrZ (Subgroup.one_mem _)
  have hr2 : orderOf r = 2 := orderOf_eq_prime (hV.2 r hrV) hr1
  have hDr : D ≤ Subgroup.centralizer ({r} : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (h.le_centralizer_J he) r (hVJ hrV)).symm
  have hVr : V ≤ Subgroup.centralizer ({r} : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hV.1.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨r, hrV⟩)
  have hVP := ggLe_pCoreOf_two_of_perE h.charTwo h.ne_two hr2 h.d_elem h.card_d hDr hVr
    fun e he he1 => ⟨V, le_rfl, Or.inr (hcomm e he he1)⟩
  exact ⟨hrV, hVJ, hV, hV4, hrZ, hconj, hVP⟩

end CommData

section Inputs

@[expose] def GGSixPCompRootCommInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
      (∃ R : Subgroup G, GGSixRootFourData p D J R) ∨
        (∃ (V : Subgroup G) (r : G), GGSixRootTwoPerData p B x L D J V r) ∨
        (∃ (V : Subgroup G) (r : G), GGSixRootTwoCommData D J V r) ∨
        ∀ d ∈ D, d ≠ 1 → ∀ A : Subgroup G,
          LargeEvenPComponent p (Subgroup.centralizer {d}) A → J ≤ A →
          A = J ⊔ LargeEvenPPrimeCoreOf p A → Odd (Nat.card (LargeEvenPPrimeCoreOf p A)) →
            LargeEvenPPrimeCoreOf p A ≤ Subgroup.centralizer (J : Set G)

theorem ggSixPCompRootInput_of_comm (h : GGSixPCompRootCommInput) : GGSixPCompRootInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd hZJ hZK
  rcases h G p B Bs x L D J t n f ψ hctx hodd hZJ hZK with hR | ⟨V, r, hV⟩ | ⟨V, r, hV⟩ | hc
  · exact Or.inl hR
  · exact Or.inr (Or.inl ⟨V, r, hctx.rootTwoData_of_perData hV⟩)
  · exact Or.inr (Or.inl ⟨V, r, hctx.rootTwoData_of_commData hV⟩)
  · exact Or.inr (Or.inr hc)

end Inputs

end CFSG.StandardType
