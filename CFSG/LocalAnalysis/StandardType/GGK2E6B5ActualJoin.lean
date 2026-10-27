module

public import CFSG.LocalAnalysis.StandardType.GGK2E6B5C2SPModel
public import CFSG.LocalAnalysis.StandardType.GGK2E6C2SPClosure
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CAssembly
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem K_only_E6_dependent_L_B5_join_raw
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    {MK : CoxeterMatrix Γ} {CK : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {φ : Γ → MulAut ↥Bs} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (e5 : Fin 5 ≃ Γ) (hMK : MK = (CoxeterMatrix.B 5).reindex e5)
    (hCK : GGIntCartan MK CK)
    (hpair : ∀ i j : Γ, α i (h j) = (CK i j : ZMod 3))
    (hlin : ∀ (i : Γ) (w : V),
      ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (fK : MK.Group ≃* ↥(ggAutomizer L Bs))
    (hclos : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hD2 : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  letI := Fact.mk (by norm_num : Nat.Prime 3)
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := l05nDD1_x_ne_one hH
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  let xv : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hxv : xv ≠ 0 := by
    intro h0
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      exact ι.injective (by simpa [xv] using h0)
    exact hx1 (by simpa using congrArg Subtype.val h1)
  have hαx : ∀ i : Γ, α i xv = 0 := by
    intro i
    have hmem : φ i ∈ ggAutomizer L Bs := by
      rw [hclos]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hfix := ggResI_automizer_fix hxBs hLx (φ i) hmem
    have hfixlin : ggLin (p := 3) ι (φ i) xv = xv := by
      dsimp only [xv]
      exact (ggLin_fix_iff (p := 3) ι (φ i) ⟨x, hxBs⟩).mp hfix
    exact ggResI_alpha_eq_zero (p := 3) (by norm_num) (hlin i)
      (by rw [hpair i i, hCK.1 i]; norm_num) hfixlin
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcardV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcardBs
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hv6 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hv6
    exact Nat.pow_right_injective (by omega : 2 ≤ 3) hv6.symm
  have hMK' : MK.reindex e5.symm = CoxeterMatrix.B 5 := by
    rw [hMK]
    ext i j
    simp [CoxeterMatrix.reindex_apply]
  have hC' : GGIntCartan (CoxeterMatrix.B 5)
      (Matrix.reindex e5.symm e5.symm CK) := by
    simpa [hMK'] using hCK.reindex e5.symm
  have hBC : (∀ i j : Fin 5, α (e5 i) (h (e5 j)) =
        (CartanMatrix.B 5 i j : ZMod 3)) ∨
      (∀ i j : Fin 5, α (e5 i) (h (e5 j)) =
        (CartanMatrix.C 5 i j : ZMod 3)) := by
    rcases hC'.eq_or_eq_transpose (ggIntCartan_B 5)
      (ggAtMostOneMultipleEdge_B 5) with hB | hC
    · left
      intro i j
      rw [hpair]
      have := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℤ => M i j) hB
      have hz : CK (e5 i) (e5 j) = CartanMatrix.B 5 i j := by
        simpa [Matrix.reindex_apply] using this
      rw [hz]
    · right
      intro i j
      rw [hpair]
      have := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℤ => M i j) hC
      have hz : CK (e5 i) (e5 j) = CartanMatrix.B 5 j i := by
        simpa [Matrix.reindex_apply, Matrix.transpose_apply] using this
      rw [← CartanMatrix.B_transpose, Matrix.transpose_apply, hz]
  let u : Fin 5 → V := fun i => h (e5 i)
  let β : Fin 5 → Module.Dual (ZMod 3) V := fun i => α (e5 i)
  have hφ : ∀ i, β i (u i) = 2 := by
    intro i
    rw [hpair, hCK.1]
    norm_num
  obtain ⟨b, hb0, hC2SP⟩ := exists_b5_c2sp_model_of_cartan
    (u := u) (α := β) (x := xv) hφ hBC hxv (fun i => hαx (e5 i)) hdim
  have hC2SPg : ∀ i : Fin 5, C2SP 3 b (ggLin (p := 3) ι (φ (e5 i))) := by
    intro i
    have heq : ggLin (p := 3) ι (φ (e5 i)) = Module.reflection (hφ i) := by
      ext w
      simpa [β, u, Module.reflection_apply] using hlin (e5 i) w
    rw [heq]
    exact hC2SP i
  have hcardMK : Nat.card MK.Group = 3840 := by
    rw [hMK]
    rw [Nat.card_congr ((CoxeterMatrix.B 5).reindexGroupEquiv e5).toEquiv]
    rw [ggCoxeterB_card 5 (by norm_num)]
    norm_num
  have hcardA : Nat.card (ggAutomizer L Bs) = 3840 := by
    rw [← Nat.card_congr fK.toEquiv]
    exact hcardMK
  have hALmodel : ∀ a : V ≃ₗ[ZMod 3] V,
      a ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι) ↔ C2SP 3 b a := by
    have hclos' : ggAutomizer L Bs =
        Subgroup.closure (Set.range fun i : Fin 5 => φ (e5 i)) := by
      rw [hclos]
      congr 1
      ext a
      constructor
      · rintro ⟨o, rfl⟩
        refine ⟨e5.symm o, ?_⟩
        simp
      · rintro ⟨i, rfl⟩
        exact ⟨e5 i, rfl⟩
    haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
    have heq := c2spSubgroup_eq_of_closure_card (E := ↥Bs) (b := b) ι
      (A := ggAutomizer L Bs) (g := fun i : Fin 5 => φ (e5 i)) hclos' hC2SPg hcardA
    intro a
    rw [heq]
    rfl
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S :=
    ggLNoncyclicInput_holds (G := G) 3 B x L hH.1.1
  exact ggResLeviExact2_join_of_signedModel hH rfl ι b hxBs (by norm_num : 5 ≤ 5)
    hb0.symm hALmodel hnc (Or.inr hD2)

end CFSG.StandardType

end
