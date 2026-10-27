module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Fixed
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {G : Type*} [Group G] [Finite G]

theorem hypB_of_isDirectProduct {p : ℕ} (hp : p.Prime) {H W D : Subgroup G} {Ω : Set (Subgroup G)}
    (hH : signalizerMcBrideHypothesisB p H) (hDH : D ≤ H) (hW : IsDirectProduct Ω W)
    (hiso : ∀ X ∈ Ω, Nonempty (↥X ≃* ↥D)) (hcop : Nat.Coprime p (Nat.card W)) :
    signalizerMcBrideHypothesisB p W := by
  refine ⟨hp, hcop, ?_⟩
  intro K L hKW hLK hN hsimple hnc
  have h1 : IsSectionOf (↥K ⧸ L.subgroupOf K) ↥K :=
    IsSectionOf.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have h2 : IsSectionOf ↥K ↥W :=
    (IsSectionOf.refl ↥K).of_injective (Subgroup.inclusion hKW) (Subgroup.inclusion_injective hKW)
  have h3 : IsSectionOf (↥K ⧸ L.subgroupOf K) ((X : ↥Ω) → (X : Subgroup G)) :=
    (h1.trans h2).trans (IsSectionOf.of_mulEquiv hW.equiv)
  obtain ⟨X, hX⟩ := IsSectionOf.of_pi hnc h3
  have h4 : IsSectionOf (↥K ⧸ L.subgroupOf K) ↥D :=
    hX.trans (IsSectionOf.of_mulEquiv (hiso X.1 X.2).some.symm)
  have h5 : IsSectionOf (↥K ⧸ L.subgroupOf K) ↥H :=
    h4.of_injective (Subgroup.inclusion hDH) (Subgroup.inclusion_injective hDH)
  exact signalizerMcBrideHypothesisA_of_isSectionOf hH h5 hnc

theorem card_inf_centralizer_of_isRegFam {p : ℕ} (hp : p.Prime) {A W : Subgroup G}
    {Ω : Set (Subgroup G)} {m : ℕ} (hΩ : IsRegFam A W Ω ⊥) (hAab : IsMulCommutative A)
    (hAcard : Nat.card A = p ^ 3) (hm : ∀ X ∈ Ω, Nat.card X = m) {a : G} (ha : a ∈ A)
    (hap : Nat.card (Subgroup.zpowers a) = p) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ({a} : Set G)) = m ^ (p ^ 2) := by
  have hFA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hFN : Subgroup.zpowers a ⊓ ⊥ = ⊥ := inf_bot_eq _
  have hsm := hΩ.smear_family hAab hFA hFN
  have hmem : ∀ Y ∈ {Y | ∃ L ∈ Ω, Y = smear L (Subgroup.zpowers a)}, Nat.card Y = m := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨e⟩ := hΩ.nonempty_mulEquiv_smear hFA hFN hL
    rw [Nat.card_congr e.toEquiv]
    exact hm L hL
  have hc := hsm.card_eq_pow hmem
  have horb := hsm.card_mul_card
  rw [bot_sup_eq, hap, hAcard] at horb
  have hn : Nat.card {Y | ∃ L ∈ Ω, Y = smear L (Subgroup.zpowers a)} = p ^ 2 :=
    Nat.eq_of_mul_eq_mul_right hp.pos (by rw [horb]; ring)
  rw [hn] at hc
  have hcent : Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent]
  exact hc

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
