module

public import CFSG.Quasithin.Recognition.G112M13Irr
public import CFSG.Quasithin.Recognition.G112M13G118
public import CFSG.Quasithin.Recognition.G112M13Chain
import CFSG.Quasithin.Background.G118CanonNineF4
import CFSG.Quasithin.Background.SzG11G64Nat
import CFSG.Milestones.ASVolI.G10
import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
import CFSG.Quasithin.Background.G119Fix
import CFSG.Quasithin.Background.G119Index
import CFSG.Quasithin.Background.G119Transv

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

section G11_8


theorem as_G_11_8M
    : G_11_8M := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  have hQ : CFSG.Quasithin.G11.Canon.QContainsM
      (fun {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) =>
          G112FaithfulWithU33M B Γ X) :=
    { c2 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 1 refine Or.inr ?_
        exact Or.inl h
      c4 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 3 refine Or.inr ?_
        exact Or.inl h
      c5 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 4 refine Or.inr ?_
        exact Or.inl h
      c6 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 5 refine Or.inr ?_
        exact Or.inl h
      c6' := fun _ _ _ h => Or.inr h
      c7 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 6 refine Or.inr ?_
        exact Or.inl h
      c10 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 10 refine Or.inr ?_
        exact Or.inl h
      c11 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 11 refine Or.inr ?_
        exact Or.inl h
      c13 := fun _ _ _ h => by
        obtain ⟨hd, N, hN, hi, hH, hirr⟩ := h
        refine Or.inl ?_
        iterate 13 refine Or.inr ?_
        exact CFSG.Quasithin.G112A2.concl13ModN_of_irr N hd hN hi hH hirr }
  have hC9 : CFSG.Quasithin.G11.Canon.G118NineContains
      (fun {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) =>
          G112FaithfulWithU33M B Γ X) :=
    { c9 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 9 refine Or.inr ?_
        exact Or.inl h }
  exact CFSG.Quasithin.G11.Canon.g11_8_canonM hQ hC9 CFSG.Quasithin.G11.Canon.g118NineInput_holds
    V B Γ v₁ W X X₀ L ⟨⟨cs.cx.hyp, cs.cx.sqtk, cs.h108, cs.numConj⟩, cs.cx.notConcl⟩ I hI

end G11_8

section G11_9


theorem g119Canonical_fullM
    :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetupM B Γ v₁ W X X₀ L →
        ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
          (∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
            ∃ Ix : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) Ix ∧ Ix ≤ B.orthogonal I ∧
              Ix ≠ I ∧ conjSub x Ix = Ix ∧
              ∃ c : V, Ix ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x Ix c) ∧
          (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ IsNatAltModule (normalClosure Γ L) I n) ∧
          (centralizerIn X (normalClosure Γ L)).relIndex X = 2 ∧
          ∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
            3 ≤ Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers x) ⊓ I) := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  obtain ⟨⟨k, hk, hk2⟩, hfix⟩ := as_G_11_8M V B Γ v₁ W X X₀ L cs I hI
  have hne : I ≠ ⊥ := fun hbot => by
    have hlt := hI.1.2.2.1
    rw [hbot, inf_bot_eq] at hlt
    exact lt_irrefl _ hlt
  have hpos : 0 < Module.finrank (ZMod 2) I :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrank : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V := by
    rw [hk]
    exact Nat.mul_lt_mul_of_pos_right hk2 hpos
  have hcent : ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i := fun x hx =>
    CFSG.Quasithin.G11.G118.fixes_of_mem_centralizerIn cs.h108 hI hx
  have c : CFSG.Quasithin.G11.G119Ctx B Γ v₁ W X X₀ L I := by
    obtain ⟨hirrP, hv₁, hinvX, -, hhom, hiso, -, hfaith, hnot⟩ := hI
    refine ⟨cs.h108, cs.cx.sqtk, hirrP, hv₁, hinvX, hhom, ?_, hfaith, hnot, hrank, hfix, hcent⟩
    rcases hiso with h | h
    · exfalso
      have h1 : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) V := by
        rw [h]
        exact finrank_top (ZMod 2) V
      omega
    · exact h
  have h14c : CFSG.Quasithin.G11.G1014Concl B Γ v₁ W X L := as_G_10_14 V B Γ v₁ W X X₀ L cs.h108
  have hE : CFSG.Quasithin.G11.G119E11Use :=
    CFSG.Quasithin.G11.g119_e11Use_of_e11Stmt CFSG.Quasithin.G11.e11
  have hrk : ∀ (y : GLV V) (hy : y ∈ X), y ∉ centralizerIn X (normalClosure Γ L) →
      Module.finrank (ZMod 2) (LinearMap.range (commMap y I (c.conjSub_I hy))) = 1 := by
    intro y hy hyC
    obtain ⟨J, hJ, hle, hne, hfixJ⟩ := c.exists_fixed hE hy
    exact c.finrank_commMap_I h14c hy hyC hJ hle hne hfixJ
  obtain ⟨x₀, hx₀, hx₀C⟩ := c.exists_not_central
  obtain ⟨n, hn5, hn8, hnat, hdec⟩ :=
    c.natural_package_of_b5 CFSG.Quasithin.asB56_holds hx₀ (hrk x₀ hx₀ hx₀C)
  have h4 : 4 ≤ Module.finrank (ZMod 2) I := by
    obtain ⟨θ, β, hrange, hker, -, -⟩ := hnat
    have := g119_four_le_finrank_range_of_ker hn5 β hker
    rwa [hrange, finrank_top] at this
  refine ⟨?_, ⟨n, hn5, hn8, c.isNatAltModule_of_natSym hx₀ (hrk x₀ hx₀ hx₀C) hnat hdec⟩,
    c.relIndex_eq_two hx₀ hx₀C hrk hnat, ?_⟩
  · intro x hx hxC
    obtain ⟨J, hJ, hle, hne, hfixJ⟩ := c.exists_fixed hE hx
    obtain ⟨c', hc1, hc2⟩ := c.transvection_Ix h14c hx hxC hJ hle hne hfixJ
    exact ⟨J, hJ, hle, hne, hfixJ, c', hc1, hc2⟩
  · intro x hx hxC
    exact c.three_le_finrank_fixed hx (hrk x hx hxC) h4

theorem as_G_11_9M
    : G_11_9M := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  obtain ⟨h1, h2, h3, -⟩ := g119Canonical_fullM V B Γ v₁ W X X₀ L cs I hI
  exact ⟨h1, h2, h3⟩

end G11_9

end CFSG.ASVolI
