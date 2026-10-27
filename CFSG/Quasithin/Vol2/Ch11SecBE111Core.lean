module

public import CFSG.Quasithin.Vol2.Ch11SecBE111Sec
public import CFSG.Quasithin.Background.E1Param

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def E111Reduced (G : Type) [Group G] (X T : Subgroup G) : Prop :=
  X.Normal ∧ X ≠ ⊥ ∧ (∀ N : Subgroup G, N.Normal → N ≤ X → N = ⊥ ∨ N = X) ∧
    (∃ a b : ↥X, a * b ≠ b * a) ∧ Subgroup.centralizer (X : Set G) = ⊥ ∧
    IsSylowIn 2 T ⊤ ∧ X ⊔ T = ⊤

@[expose] def E111CoreMulti : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (X T : Subgroup G), 1 ≤ n →
    ASInputs.E111Hyp G n →
    (∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → ASInputs.E111Hyp G' n →
      E1.InE n (⊤ : Subgroup G')) →
    E111Reduced G X T → ¬ IsSimpleGroup ↥X → E1.InEFor n ⊤ T

theorem inEFor_of_reduced_simple {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    {X T : Subgroup G} (hR : E111Reduced G X T) (hXs : IsSimpleGroup ↥X)
    (hH : ASInputs.E111Hyp G n) : E1.InEFor n ⊤ T := by
  obtain ⟨hXn, -, -, hnab, hC, hT, hXT⟩ := hR
  have : X.Normal := hXn
  set φ : G →* MulAut ↥X := MulAut.conjNormal with hφ
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : G)) (MonoidHom.mem_ker.mp hg)
      simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hC] at hgC
    exact hgC
  set I := (MulAut.conj : ↥X →* MulAut ↥X).range with hI
  set B := T.map φ with hB
  have hXI : X.map φ = I := by
    ext f
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      ext y
      simp [hφ, MulAut.conjNormal_apply, MulAut.conj_apply]
    · rintro ⟨x, rfl⟩
      refine ⟨x, x.2, ?_⟩
      ext y
      simp [hφ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hrange : φ.range = I ⊔ B := by
    rw [MonoidHom.range_eq_map, ← hXT, Subgroup.map_sup, hXI]
  have hB2 : IsPGroup 2 ↥B := hT.2.1.map φ
  have hTX : IsSylowIn 2 (T ⊓ X) X := by
    have hN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hXn]
    have h := B6.isSylowTwoOf_inf_normal
      (⟨hT.1, hT.2.1, hT.2.2⟩ : QuasithinUnique.IsSylowTwoOf T ⊤) le_top hN
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hBI : IsSylowIn 2 (B ⊓ I) I := by
    rw [← hXI, hB, ← Subgroup.map_inf _ _ _ hφi]
    exact (E1.isSylowIn_map_of_injective hφi).mpr hTX
  have hsec := (e111Hyp_iff_secAll n).mp hH
  have hXq : IsSimpleGroup (↥X ⧸ (⊥ : Subgroup ↥X)) :=
    (MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).mpr hXs
  have hP0 := hsec X ⊥ (Subgroup.Normal.isSubnormal hXn) hXq
    (nonabelian_of_mulEquiv QuotientGroup.quotientBot hnab)
  have hPX : E111Prop n ↥X := isoInv_e111Prop n _ _ QuotientGroup.quotientBot.symm hP0
  have hle := hPX inferInstance B hB2 hBI
  have heq : E1.nParam (⊤ : Subgroup G) = E1.nParam φ.range := by
    rw [E1.nParam_subgroupOf φ.range]
    exact E1.Eleven.nParam_top_mulEquiv (MonoidHom.ofInjective hφi)
  have h1 : E1.nParam (⊤ : Subgroup G) ≤ n := by
    rw [heq, hrange]
    exact hle
  exact (E1.nParam_le_iff (by omega)).mp h1 T hT

end CFSG.Quasithin.Vol2.Ch11.SecB
