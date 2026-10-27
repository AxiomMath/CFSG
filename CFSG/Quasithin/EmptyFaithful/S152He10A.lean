module

public import CFSG.Quasithin.Background.C129Used
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S152He9A5

public section

namespace CFSG.Quasithin.He10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem hypC23_sup {G₀ R M₁ L : Subgroup G} (hyp : HypC23 G₀ R M₁) (hLG : L ≤ G₀)
    (hsyl : IsSylowTwoOf R (R ⊔ L)) : HypC23 (R ⊔ L) R (M₁ ⊓ (R ⊔ L)) := by
  have hRG : R ≤ G₀ := hyp.radical.1
  have hH : R ⊔ L ≤ G₀ := sup_le hRG hLG
  refine ⟨hyp.sqtk.mono hH, ?_, inf_le_right, ?_, ?_⟩
  · exact isTwoRadicalIn_of_sylow hsyl.1 hsyl.2.1 hsyl.2.2 hyp.radical.2.1
  · exact le_inf ((C2Nine.cgsIn_mono_left hH R).trans hyp.cgs) (cgsIn_le _ R)
  · have hRM : R ≤ M₁ := fun x hx =>
      hyp.cgs (inf_normalizer_le_cgsIn hyp.radical.2.1 ⟨hRG hx, Subgroup.le_normalizer hx⟩)
    have hRM' : R ≤ M₁ ⊓ (R ⊔ L) := le_inf hRM le_sup_left
    refine A4.isSylowTwoOf_mono hyp.sylow (le_conjClosure R _) ?_
    exact conjClosure_le fun h hh z hz => mem_conjClosure hh.1 hz

theorem charTwo_sup {G₀ R M₁ L : Subgroup G} (hyp : HypC23 G₀ R M₁) (hLG : L ≤ G₀)
    (hchar : CharTwo G₀) : CharTwo (R ⊔ L) :=
  C2Push.charTwo_of_pCoreOf_le hchar ((c2_1_pCore_le hyp.radical).trans le_sup_left)
    (sup_le hyp.radical.1 hLG)

theorem eq_of_isBlock2_of_quasisimple {G₀ R L B : Subgroup G} (hL : L ∈ cComp G₀)
    (hR2 : IsPGroup 2 R) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hB : IsBlock2 (R ⊔ L) B) (hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : B = L := by
  have hBperf : ⁅B, B⁆ = B :=
    C1GN.isShort2_perfect_of_perfect_quotient hB.1 (Group.isPerfect_def.mp hBq.1)
  have hBL : B ≤ L := C2Push.le_of_perfect_le_sup hR2 hRL hBperf (by rw [sup_comm]; exact hB.2.1)
  have hsubH : IsSubnormal B (R ⊔ L) := IsBlock2.isSubnormal hB
  have hsubL : IsSubnormal B L := A3.subnormal_of_le_of_le hsubH hBL le_sup_right
  have hsubG : IsSubnormal B G₀ := A3.subnormal_trans hsubL (subnormal_of_mem_cComp hL)
  have hBne : B ≠ ⊥ := by
    intro hB0
    have h1 : Subsingleton ↥B := by rw [hB0]; infer_instance
    have h2 : Subsingleton (↥B ⧸ CFSG.pCore 2 ↥B) :=
      (QuotientGroup.mk'_surjective _).subsingleton
    obtain ⟨a, b, hab⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hBq).exists_pair_ne
    exact hab (Subsingleton.elim _ _)
  by_contra hne
  exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hBL hne) hBne hBperf hsubG

theorem isChi0Block_or_all_A3 (h129 : ASC129StatementUsed G) {G₀ R M₁ L : Subgroup G}
    (hyp : HypC23 G₀ R M₁) (hchar : CharTwo G₀) (hL : L ∈ cComp G₀)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf R (R ⊔ L)) :
    IsChi0Block (R ⊔ L) L ∨
      ∃ (r : ℕ) (Lb : Fin r → Subgroup G),
        (∀ i, IsBlock2 (R ⊔ L) (Lb i) ∧ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3) ∧
        ∀ h ∈ R ⊔ L, ∃ m ∈ M₁ ⊓ (R ⊔ L), ∃ x : Fin r → G,
          (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod := by
  have hLG : L ≤ G₀ := le_of_mem_cComp hL
  have hH := hypC23_sup hyp hLG hsyl
  have hcT := charTwo_sup hyp hLG hchar
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 (R ⊔ L) R (M₁ ⊓ (R ⊔ L)) hH.sqtk hcT hsyl hH.cgs hH.le
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  · left
    obtain ⟨i, hi⟩ := hq
    have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
      ((hLb i).1.1.1.2.2.2.1).resolve_right hi
    have heq := eq_of_isBlock2_of_quasisimple hL hyp.radical.isPGroup hRL (hLb i).1.1 hBq
    have h := (hLb i).1
    rw [heq] at h
    exact h
  · right
    push Not at hq
    exact ⟨r, Lb, fun i => ⟨(hLb i).1.1, hq i⟩, hprod⟩

end CFSG.Quasithin.He10
