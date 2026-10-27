module

public import CFSG.Quasithin.EmptyFaithful.S143VFin
public import CFSG.Quasithin.EmptyFaithful.SzN28Lt
public import CFSG.Quasithin.EmptyFaithful.S142Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
open scoped commutatorElement

@[expose] def Lemma14315SolvableS8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      Group.IsSolvable ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ∨
        ∃ g : G, GoodElt128 T (yOfL22 T M) g ∧
          G112Concl8S8 D.B (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
            (D.img (rconj (Hyp1281Two.wOfU T M) g))

@[expose] def S8NoTrivialX0 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → G112Concl8S8 B Γ X → X₀ ≠ ⊥

namespace SzN28

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem img_rconj_centerOf_eq_bot (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T (yOfL22 T M) g)
    (D : HatModel T M) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) :
    D.img (rconj (centerOf (uOfL22 T M)) g) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  obtain ⟨y, hyX, hyN, rfl⟩ := HatModel.mem_img.mp hγ
  rw [Subgroup.mem_bot]
  have hyV : y ∈ VZ T M := by
    have h1 : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M :=
      (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
    rw [hZU] at hyX
    exact h1 hyX
  have hyU : y ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hyV
  exact (D.rho_eq_one_iff ⟨y, hyN⟩).mpr fun u hu =>
    (Hyp1281Two.uOfL22_le_centralizerHat h hyU).2.2 u hu

theorem lemma14315Solvable_of_s8 (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hP : Lemma14315SolvableS8) (hF : S8NoTrivialX0) :
    Lemma14315Solvable := by
  intro G _ _ T M hyp hnot hnab D
  rcases hP G T M hyp hnot hnab D with hsolv | ⟨g, hg, h8⟩
  · exact hsolv
  · exfalso
    have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
    obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
    by_cases hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T
    · have hyp3 := h1281.lemma_12_8_12_three hnab hg D haV haZ
      exact hF D.V D.B _ _ _ _ _ hyp3 h8 (img_rconj_centerOf_eq_bot h1281 hnab hg D hZU)
    · exact false_of_lt_s8 h1281 hnab hg D
        (lt_of_le_of_ne h1281.omegaOneCenter_le_centerOf_uOfL22 (Ne.symm hZU)) h8

end SzN28

end CFSG.Quasithin
