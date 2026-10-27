module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Cases
import CFSG.Quasithin.Background.GoldschmidtShultLink

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem isCalL0_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsCalL0 X) :
    IsCalL0 Y := by
  rcases h with ⟨n, hn, t, m, h⟩ | h | h | h | h | h | h
  · exact Or.inl ⟨n, hn, t, m, CFSG.Blueprint.LieModel.of_mulEquiv e h⟩
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.Blueprint.LieModel.of_mulEquiv e h))))))
  · obtain ⟨e'⟩ := (h : Nonempty (X ≃* alternatingGroup (Fin 9)))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩)))))

theorem not_hasCompFactor_of_sylowOvergroups (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a)
    {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} (hK : CFSG.Open.IsKGroup Q)
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hLnot : ¬ IsCalL0 ↥L) (hT : IsSylowIn 2 T ⊤)
    (hP : ∀ (S : Sylow 2 ↥L) (Y : Subgroup ↥L), (S : Subgroup ↥L) ≤ Y → Y < ⊤ →
      ¬ HasCompFactor Y IsCalL0)
    {X : Subgroup Q} (hTX : T ≤ X) : ¬ HasCompFactor X IsCalL0 := by
  have := hLn
  have hKL : CFSG.Open.IsKGroup ↥L := hK.of_injective L.subtype L.subtype_injective
  have hcat := hKL.isCatalogGroup_of_surjective ⊤ hLnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer (hS _ hLs hLnab hcat))
  have hTL : IsSylowIn 2 (T ⊓ L) L := CFSG.Quasithin.Shult.isSylowTwoOf_inf_normal hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨M, _, hcf, hM⟩
  obtain ⟨-, -, hnab⟩ := hL0 M hM
  have h1 := isCompositionFactor_subgroupOf_of_isSolvable_quot (isSolvable_quotient_subgroupOf hq X)
    ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr Subgroup.topEquiv).2 hcf) hnab
  have h2 : E1.IsCompositionFactor ↥(X.subgroupOf L) M :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      ((subgroupOfEquivOfLe le_top).trans (CFSG.Quasithin.Vol2.Ch11.SecB.interEquiv X L))).1 h1
  by_cases hXL : X.subgroupOf L = ⊤
  ·
    rw [hXL] at h2
    have := hLs
    obtain ⟨e⟩ := isCompositionFactor_mulEquiv_of_isSimpleGroup
      ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr Subgroup.topEquiv).1 h2)
    exact hLnot (isCalL0_of_mulEquiv e.symm hM)
  ·
    refine hP hTL.toSylow (X.subgroupOf L) ?_ (lt_top_iff_ne_top.2 hXL) ⟨M, inferInstance, h2, hM⟩
    intro x hx
    rw [IsSylowIn.coe_toSylow, mem_subgroupOf] at hx
    rw [mem_subgroupOf]
    exact hTX hx.1

theorem asch54Case_of_sylowOvergroups (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a)
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → ∀ (S : Sylow 2 X) (Y : Subgroup X),
      (S : Subgroup X) ≤ Y → Y < ⊤ → ¬ HasCompFactor Y IsCalL0) :
    Asch54Case P := by
  intro Q _ _ L T hKQ hLn hLs hLnab hC hPL hLL0 hT hnu
  left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact lGen_eq_top_of_not_hasUniqueMaxOver
    (fun X hTX _ => not_hasCompFactor_of_sylowOvergroups hS hL0 hKQ hLn hLs hLnab hC hLL0 hT
      (hP ↥L hPL) hTX)
    (lt_top_of_isSylowIn_of_not_isSolvable hT (not_isSolvable_of_simple_normal L hLs hLnab)) hnu

end CFSG.LocalAnalysis.WeakClosure81
