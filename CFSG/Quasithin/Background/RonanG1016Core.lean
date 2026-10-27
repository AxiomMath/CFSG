module

public import CFSG.Quasithin.Background.RonanG1016Conv
public import CFSG.Quasithin.Background.RonanG1016Sym
public import CFSG.Quasithin.Background.RonanG1016Cases

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

open CFSG.ComponentClassification.OutcomeLocal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mclaughlin_core [Finite V] {H K : Subgroup (GLV V)} {a : GLV V} {J : Submodule (ZMod 2) V}
    (hJ : IsIrr K J) (hHK : H ≤ K) (haK : a ∈ K) (hKH : K ≤ H ⊔ Subgroup.zpowers a)
    (ha2 : a * a = 1) (hHnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hHJ : Invariant H J) (hfaith : FaithfulOn H J) (hHne : H ≠ ⊥)
    (hε : ∀ ε : ↥K →* ℤˣ, ∀ (h : GLV V) (hh : h ∈ H), ε ⟨h, hHK hh⟩ = 1)
    (h3 : 3 ≤ Module.finrank (ZMod 2) ↥J)
    (hT : K ≤ normalClosure K (Subgroup.zpowers a)) (haT : IsTransvOn J a) :
    AutAll H J ∨ (SelfDual K J ∧ (CFSG.Quasithin.RonanG1016.InducesSp K J ∨
      CFSG.Quasithin.RonanG1016.InducesOrth K J ∨
      ∃ n, CFSG.Quasithin.RonanG1016.IsSymNaturalSub K J n)) := by
  have hgen := hgen_of_le_normalClosure hJ.1 haT haK hT
  by_cases htop : restrictRange K J hJ.1 = ⊤
  · exact Or.inl (autAll_of_top hJ hHnorm hHJ hfaith hHne h3 htop)
  · right
    refine ⟨selfDual_of_ne_top hJ hgen (by omega) htop, ?_⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hN : ∀ h ∈ H, a * h * a ∈ H := fun h hh => by
      have := hHnorm a haK h hh
      rwa [hai] at this
    rcases mclaughlin_cases hJ hgen with h | ⟨f, hnd, halt, hf⟩ | ⟨Q, hQ, hQe⟩ | ⟨hev, hsym⟩
    · exact absurd h htop
    · exact Or.inl (sp_body hJ f hnd halt (mem_restrictRange_of_bilin hJ f hf))
    · exact Or.inr (Or.inl (orth_body hJ Q hQ (mem_restrictRange_of_orth hJ Q hQe)))
    · right
      right
      obtain ⟨k, hk⟩ := hev
      rcases hsym with ⟨β, hβ⟩ | ⟨β, hβ⟩
      · have hf : FaithfulOn K J := faithfulOn_of_perm (n := Module.finrank (ZMod 2) ↥J + 1)
          (by omega) (sumZeroRep _) (sumZeroRep_injective' (by omega)) hJ.1 β hβ hHK haK hKH ha2
          hN hfaith hε
        exact ⟨_, isSymNatural_of_sumZero (by omega) ⟨k, by omega⟩ hJ.1 hf β hβ⟩
      · have hf : FaithfulOn K J := faithfulOn_of_perm (n := Module.finrank (ZMod 2) ↥J + 2)
          (by omega) (heartRep _) (heartRep_injective' (by omega)) hJ.1 β hβ hHK haK hKH ha2
          hN hfaith hε
        exact ⟨_, isSymNatural_of_heart (by omega) ⟨k + 1, by omega⟩ hJ.1 hf β hβ⟩

end G11

end CFSG.Quasithin
