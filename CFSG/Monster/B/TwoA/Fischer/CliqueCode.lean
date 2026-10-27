module

public import CFSG.Monster.B.TwoA.Fischer.CliqueCodeBlocks
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.LinearAlgebra.Projectivization.Independence

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary
open scoped IsMulCommutative LinearAlgebra.Projectivization MatrixGroups

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem eq_span_planePts_of_isTotIso {A : Submodule F4 UnitarySix.V} (hA : IsTotIso A) :
    A = Submodule.span F4 ((fun p : IsoPt => p.1.rep) '' planePts A) := by
  apply le_antisymm
  · intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact Submodule.zero_mem _
    · have hvi : herm v v = 0 := hA v hv v hv
      obtain ⟨c, hc⟩ := rep_pt hv0 hvi
      have h1 : (pt v hv0 hvi).1.rep ∈
          Submodule.span F4 ((fun p : IsoPt => p.1.rep) '' planePts A) :=
        Submodule.subset_span ⟨_, (pt_mem_planePts hv0 hvi).2 hv, rfl⟩
      rw [← hc] at h1
      exact (Submodule.smul_mem_iff' _ c).1 h1
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hp

theorem eq_of_planePts_eq {A A' : Submodule F4 UnitarySix.V} (hA : IsTotIso A)
    (hA' : IsTotIso A') (h : planePts A = planePts A') : A = A' := by
  rw [eq_span_planePts_of_isTotIso hA, eq_span_planePts_of_isTotIso hA', h]

theorem finrank_span_rep_pair {p q : IsoPt} (h : p ≠ q) :
    Module.finrank F4 (Submodule.span F4 {p.1.rep, q.1.rep}) = 2 := by
  have hind := (Projectivization.independent_pair_iff_ne p.1 q.1).2 fun e => h (Subtype.ext e)
  rw [Projectivization.independent_iff] at hind
  have hli : LinearIndependent F4 ![p.1.rep, q.1.rep] := by
    convert hind using 1
    funext i
    fin_cases i <;> rfl
  have := finrank_span_eq_card hli
  rwa [Fintype.card_fin, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union] at this

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u)

theorem mem_insert_iff_tau (P : Set IsoPt) {v : V} (hv : v ∈ (sliceGraph lab Y).neighborSet u) :
    v ∈ insert u (Subtype.val '' (L.τ ⁻¹' P)) ↔ L.τ ⟨v, hv⟩ ∈ P := by
  constructor
  · rintro (h | ⟨w, hw, hwv⟩)
    · exact absurd h.symm hv.2.2.1
    · rwa [show w = ⟨v, hv⟩ from Subtype.ext hwv] at hw
  · intro h
    exact Set.mem_insert_of_mem _ ⟨⟨v, hv⟩, h, rfl⟩

end LocalChart

theorem ncard_mul_eq_of_double_count {C : Set V} (hfin : C.Finite) {ℬ : Set (Set V)} {k r : ℕ}
    (hB : ∀ B ∈ ℬ, B ⊆ C ∧ B.ncard = k) (hr : ∀ z ∈ C, {B ∈ ℬ | z ∈ B}.ncard = r) :
    ℬ.ncard * k = C.ncard * r := by
  classical
  have hℬ : ℬ.Finite := hfin.finite_subsets.subset fun B hB' => (hB B hB').1
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun B z => z ∈ B)
    (s := hℬ.toFinset) (t := hfin.toFinset)
  have h1 : ∀ B ∈ hℬ.toFinset,
      (Finset.bipartiteAbove (fun B z => z ∈ B) hfin.toFinset B).card = k := by
    intro B hB'
    rw [Set.Finite.mem_toFinset] at hB'
    rw [← (hB B hB').2, ← Set.ncard_coe_finset]
    congr 1
    ext z
    rw [Finset.mem_coe, Finset.mem_bipartiteAbove, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨(hB B hB').1 h, h⟩⟩
  have h2 : ∀ z ∈ hfin.toFinset,
      (Finset.bipartiteBelow (fun B z => z ∈ B) hℬ.toFinset z).card = r := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [← hr z hz, ← Set.ncard_coe_finset]
    congr 1
    ext B
    rw [Finset.mem_coe, Finset.mem_bipartiteBelow, Set.Finite.mem_toFinset]
    rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← Set.ncard_eq_toFinset_card ℬ hℬ,
    ← Set.ncard_eq_toFinset_card C hfin] at key
  exact key

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem existsUnique_block {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {T : Set V} (hTC : T ⊆ C)
    (hT : T.ncard = 3) : ∃! B, B ∈ cliqueBlocks lab C ∧ T ⊆ B := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.1 hT
  have hx : x ∈ C := hTC (by simp)
  have hy : y ∈ C := hTC (by simp)
  have hz : z ∈ C := hTC (by simp)
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hx)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hx
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  have ny : y ∈ (sliceGraph lab Y).neighborSet x :=
    mem_neighborSet_of_mem_clique hC.1.2 hx hy (Ne.symm hxy)
  have nz : z ∈ (sliceGraph lab Y).neighborSet x :=
    mem_neighborSet_of_mem_clique hC.1.2 hx hz (Ne.symm hxz)
  have hpy := L.mem_planePts_of_mem g hWe ⟨y, ny⟩ hy
  have hpz := L.mem_planePts_of_mem g hWe ⟨z, nz⟩ hz
  have hne : L.τ ⟨y, ny⟩ ≠ L.τ ⟨z, nz⟩ := fun e =>
    hyz (congrArg (fun w : (sliceGraph lab Y).neighborSet x => (w : V)) (L.τ.injective e))
  set A := Submodule.span F4 {(L.τ ⟨y, ny⟩).1.rep, (L.τ ⟨z, nz⟩).1.rep} with hA
  have hAW : A ≤ smulSub g W0 := by
    rw [hA, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact hpy
    · exact hpz
  have hA2 : Module.finrank F4 A = 2 := finrank_span_rep_pair hne
  have hyA : L.τ ⟨y, ny⟩ ∈ planePts A := Submodule.subset_span (by simp)
  have hzA : L.τ ⟨z, nz⟩ ∈ planePts A := Submodule.subset_span (by simp)
  refine ⟨insert x (Subtype.val '' (L.τ ⁻¹' planePts A)),
    ⟨((L.mem_cliqueBlocks_and_mem_iff hS hC hx g hWe _).2 ⟨A, hAW, hA2, rfl⟩).1, ?_⟩, ?_⟩
  · intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Set.mem_insert _ _
    · exact (L.mem_insert_iff_tau _ ny).2 hyA
    · exact (L.mem_insert_iff_tau _ nz).2 hzA
  · rintro B' ⟨hB', hTB'⟩
    obtain ⟨A', hA'W, hA'2, rfl⟩ :=
      (L.mem_cliqueBlocks_and_mem_iff hS hC hx g hWe B').1 ⟨hB', hTB' (by simp)⟩
    have hyA' := (L.mem_insert_iff_tau _ ny).1 (hTB' (by simp))
    have hzA' := (L.mem_insert_iff_tau _ nz).1 (hTB' (by simp))
    have hle : A ≤ A' := by
      rw [hA, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hyA'
      · exact hzA'
    rw [Submodule.eq_of_le_of_finrank_eq hle (by rw [hA2, hA'2])]

theorem ncard_blocks_mem {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {u : V} (hu : u ∈ C) :
    {B ∈ cliqueBlocks lab C | u ∈ B}.ncard = 21 := by
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  have e : {B ∈ cliqueBlocks lab C | u ∈ B} =
      (fun A => insert u (Subtype.val '' (L.τ ⁻¹' planePts A))) ''
        {A : Submodule F4 UnitarySix.V | A ≤ smulSub g W0 ∧ Module.finrank F4 A = 2} := by
    ext B
    rw [Set.mem_ofPred_eq, L.mem_cliqueBlocks_and_mem_iff hS hC hu g hWe]
    constructor
    · rintro ⟨A, hAW, hA, rfl⟩
      exact ⟨A, ⟨hAW, hA⟩, rfl⟩
    · rintro ⟨A, ⟨hAW, hA⟩, rfl⟩
      exact ⟨A, hAW, hA, rfl⟩
  rw [e, Set.InjOn.ncard_image, ncard_lines hW]
  rintro A ⟨hAW, -⟩ A' ⟨hA'W, -⟩ h
  dsimp only at h
  refine eq_of_planePts_eq (hW.2.mono hAW) (hW.2.mono hA'W) (Set.ext fun p => ?_)
  obtain ⟨w, rfl⟩ := L.τ.surjective p
  exact (L.mem_insert_iff_tau _ w.2).symm.trans (h ▸ L.mem_insert_iff_tau _ w.2)

theorem mem_range_restrL_iff_setStab {C : Set V} (hC : IsSliceMaxClique lab Y C) {u : V}
    (hu : u ∈ C) (L : LocalChart act lab Y u) {W : Submodule F4 UnitarySix.V}
    (hWe : L.img C = planePts W) (σ : Equiv.Perm (planePts W)) :
    σ ∈ (restrL W).range ↔ ∃ a ∈ setStab act lab Y C, act a u = u ∧
      ∀ (p : planePts W) (z z' : (sliceGraph lab Y).neighborSet u),
        L.τ z = p → (z' : V) = act a z → (σ p : IsoPt) = L.τ z' := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := L.surj x
    refine ⟨b, (L.mem_setStab_iff hS hC hu hWe b).2 (by rw [hb]; exact x.2), b.2.2,
      fun p z z' hzp hz' => ?_⟩
    rw [restrL_apply, ← hzp, L.equivariant b z z' hz', hb]
  · rintro ⟨a, ha, hau, h⟩
    set b : sliceStab act lab Y u := ⟨a, ha.1, hau⟩
    have hbW : L.φ b ∈ stabL W := (L.mem_setStab_iff hS hC hu hWe b).1 ha
    refine ⟨⟨L.φ b, hbW⟩, Equiv.ext fun p => Subtype.ext ?_⟩
    rw [restrL_apply]
    have hz : L.τ (L.τ.symm p) = p := L.τ.apply_symm_apply p
    set z' : (sliceGraph lab Y).neighborSet u :=
      ⟨act a (L.τ.symm p), hS.act_mem_neighborSet b.2 (L.τ.symm p).2⟩
    rw [h p (L.τ.symm p) z' hz rfl, L.equivariant b (L.τ.symm p) z' rfl, hz]

theorem exists_setStab_pair {C : Set V} (hC : IsSliceMaxClique lab Y C) {u x₁ x₂ y₁ y₂ : V}
    (hu : u ∈ C) (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) (hy₁ : y₁ ∈ C) (hy₂ : y₂ ∈ C) (hx₁u : x₁ ≠ u)
    (hx₂u : x₂ ≠ u) (hy₁u : y₁ ≠ u) (hy₂u : y₂ ≠ u) (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) :
    ∃ a ∈ setStab act lab Y C, act a u = u ∧ act a x₁ = y₁ ∧ act a x₂ = y₂ := by
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  have n : ∀ {v : V}, v ∈ C → v ≠ u → v ∈ (sliceGraph lab Y).neighborSet u :=
    fun hv hvu => mem_neighborSet_of_mem_clique hC.1.2 hu hv hvu
  let P : ∀ {v : V}, v ∈ C → v ≠ u → planePts (smulSub g W0) := fun hv hvu =>
    ⟨L.τ ⟨_, n hv hvu⟩, L.mem_planePts_of_mem g hWe _ hv⟩
  have hPinj : ∀ {v v' : V} (hv : v ∈ C) (hvu : v ≠ u) (hv' : v' ∈ C) (hv'u : v' ≠ u),
      eW g (P hv hvu) = eW g (P hv' hv'u) → v = v' := fun hv hvu hv' hv'u e =>
    congrArg (fun w : (sliceGraph lab Y).neighborSet u => (w : V))
      (L.τ.injective (congrArg Subtype.val ((eW g).injective e)))
  have htwo := (linear_projective_action (K := F4) (n := 3) (by norm_num)).2.2.2.2.2.1
  obtain ⟨A, hA₁, hA₂⟩ := MulAction.is_two_pretransitive_iff.1 htwo
    (fun e => hx (hPinj hx₁ hx₁u hx₂ hx₂u e)) (fun e => hy (hPinj hy₁ hy₁u hy₂ hy₂u e))
  set σ : Equiv.Perm (planePts (smulSub g W0)) :=
    ((eW g).trans (MulAction.toPerm A)).trans (eW g).symm with hσdef
  have hσ : σ ∈ (restrL (smulSub g W0)).range :=
    (mem_range_restrL_iff g σ).2 ⟨A, fun p => by simp [σ]⟩
  obtain ⟨a, ha, hau, hact⟩ := (hS.mem_range_restrL_iff_setStab hC hu L hWe σ).1 hσ
  have hσx₁ : σ (P hx₁ hx₁u) = P hy₁ hy₁u := by
    rw [hσdef, Equiv.trans_apply, Equiv.trans_apply, MulAction.toPerm_apply, hA₁,
      Equiv.symm_apply_apply]
  have hσx₂ : σ (P hx₂ hx₂u) = P hy₂ hy₂u := by
    rw [hσdef, Equiv.trans_apply, Equiv.trans_apply, MulAction.toPerm_apply, hA₂,
      Equiv.symm_apply_apply]
  have hb : a ∈ sliceStab act lab Y u := ⟨ha.1, hau⟩
  refine ⟨a, ha, hau, ?_, ?_⟩
  · have h1 := hact (P hx₁ hx₁u) ⟨x₁, n hx₁ hx₁u⟩ ⟨act a x₁, hS.act_mem_neighborSet hb
      (n hx₁ hx₁u)⟩ rfl rfl
    rw [hσx₁] at h1
    exact (congrArg (fun w : (sliceGraph lab Y).neighborSet u => (w : V))
      (L.τ.injective h1)).symm
  · have h1 := hact (P hx₂ hx₂u) ⟨x₂, n hx₂ hx₂u⟩ ⟨act a x₂, hS.act_mem_neighborSet hb
      (n hx₂ hx₂u)⟩ rfl rfl
    rw [hσx₂] at h1
    exact (congrArg (fun w : (sliceGraph lab Y).neighborSet u => (w : V))
      (L.τ.injective h1)).symm

theorem isMultiplyPretransitive_three {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    MulAction.IsMultiplyPretransitive (setStabPerm act lab Y C).range C 3 := by
  refine ⟨fun x y => ?_⟩
  have hne : ∀ (f : Fin 3 ↪ C) (i j : Fin 3), i ≠ j → ((f i : C) : V) ≠ f j :=
    fun f i j hij h => hij (f.injective (Subtype.ext h))
  obtain ⟨a₁, ha₁, h₁⟩ := hS.exists_setStab hC (x 0).2 (y 0).2
  have hx' : ∀ i, act a₁ (x i) ∈ C := fun i => (ha₁.2 _).2 (x i).2
  have hx'ne : ∀ i j : Fin 3, i ≠ j → act a₁ (x i) ≠ act a₁ (x j) :=
    fun i j hij h => hne x i j hij ((act a₁).injective h)
  obtain ⟨a₂, ha₂, h20, h21, h22⟩ := hS.exists_setStab_pair hC (y 0).2 (hx' 1) (hx' 2) (y 1).2
    (y 2).2 (fun h => hx'ne 1 0 (by decide) (h.trans h₁.symm))
    (fun h => hx'ne 2 0 (by decide) (h.trans h₁.symm)) (hne y 1 0 (by decide))
    (hne y 2 0 (by decide)) (hx'ne 1 2 (by decide)) (hne y 1 2 (by decide))
  refine ⟨⟨setStabPerm act lab Y C ⟨a₂ * a₁, (setStab act lab Y C).mul_mem ha₂ ha₁⟩, ⟨_, rfl⟩⟩,
    Function.Embedding.ext fun i => Subtype.ext ?_⟩
  rw [Function.Embedding.smul_apply, Subgroup.smul_def, Equiv.Perm.smul_def, setStabPerm_apply,
    map_mul, Equiv.Perm.mul_apply]
  fin_cases i
  · change act a₂ (act a₁ (x 0)) = y 0
    rw [h₁, h20]
  · exact h21
  · exact h22

theorem clique_code_steiner_design {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)),
      Function.Surjective (cliqueLabelMap lab C) ∧ Nat.card C = 22 ∧
      Module.finrank (ZMod 2) (cliqueCode lab C) = 12 ∧
      (∀ f ∈ cliqueCode lab C, f ≠ 0 → 6 ≤ f.support.card) ∧
      (∃ f ∈ cliqueCode lab C, f.support.card = 6) ∧
      (∀ B ∈ cliqueBlocks lab C, B ⊆ C ∧ B.ncard = 6) ∧
      (∀ T ⊆ C, T.ncard = 3 → ∃! B, B ∈ cliqueBlocks lab C ∧ T ⊆ B) ∧
      (cliqueBlocks lab C).ncard = 77 ∧
      (∀ z ∈ C, {B ∈ cliqueBlocks lab C | z ∈ B}.ncard = 21) ∧
      (∀ u ∈ C, ∀ L : LocalChart act lab Y u, ∀ W : Submodule F4 UnitarySix.V, IsMaxIso W →
        L.τ '' {z | (z : V) ∈ C} = planePts W →
        ∀ B : Set V, (B ∈ cliqueBlocks lab C ∧ u ∈ B) ↔
          ∃ A : Submodule F4 UnitarySix.V, A ≤ W ∧ Module.finrank F4 A = 2 ∧
            B = insert u (Subtype.val '' (L.τ ⁻¹' planePts A))) ∧
      (∀ a : setStab act lab Y C, ∀ f ∈ cliqueCode lab C,
        Finsupp.mapDomain (setStabPerm act lab Y C a) f ∈ cliqueCode lab C) ∧
      (∀ a ∈ setStab act lab Y C, ∀ B ∈ cliqueBlocks lab C, act a '' B ∈ cliqueBlocks lab C) ∧
      MulAction.IsMultiplyPretransitive (setStabPerm act lab Y C).range C 3 ∧
      Nat.card (setStabPerm act lab Y C).range = 443520 ∧
      (∀ u ∈ C, ∀ L : LocalChart act lab Y u, ∀ W : Submodule F4 UnitarySix.V, IsMaxIso W →
        L.τ '' {z | (z : V) ∈ C} = planePts W →
        (∀ σ : Equiv.Perm (planePts W), σ ∈ (restrL W).range ↔
          ∃ a ∈ setStab act lab Y C, act a u = u ∧
            ∀ (p : planePts W) (z z' : (sliceGraph lab Y).neighborSet u),
              L.τ z = p → (z' : V) = act a z → (σ p : IsoPt) = L.τ z') ∧
        ∃ (e : planePts W ≃ ℙ F4 (Fin 3 → F4)) (θ : (restrL W).range ≃* PSL(3, F4)),
          ∀ (σ : (restrL W).range) (p : planePts W),
            e ((σ : Equiv.Perm (planePts W)) p) = θ σ • e p) := by
  obtain ⟨-, hFC, hcl, -, hR, -, -, -⟩ := hS.maximal_clique_stabilizer_kernel.2.2 C hC
  have inst : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)) :=
    hS.isElementaryAbelian_closure hC.1.1 hC.1.2
  have hCfin : C.Finite := hS.finite.subset hC.1.1
  have : Finite C := hCfin.to_subtype
  have hR' : Nat.card (Subgroup.closure (lab '' C)) = 2 ^ 10 := by
    rw [← hcl]
    exact hR
  have : Finite (Subgroup.closure (lab '' C)) :=
    Nat.finite_of_card_ne_zero (by rw [hR']; norm_num)
  have h22 : C.ncard = 22 := hS.ncard_eq_of_isSliceMaxClique hC
  have hB6 : ∀ B ∈ cliqueBlocks lab C, B ⊆ C ∧ B.ncard = 6 := by
    intro B hB
    obtain ⟨T, -, hT6, rfl⟩ := (mem_cliqueBlocks_iff B).1 hB
    refine ⟨?_, ?_⟩
    · rintro _ ⟨z, -, rfl⟩
      exact z.2
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset, hT6]
  have h21 : ∀ z ∈ C, {B ∈ cliqueBlocks lab C | z ∈ B}.ncard = 21 :=
    fun z hz => hS.ncard_blocks_mem hC hz
  refine ⟨inst, cliqueLabelMap_surjective, by rw [Nat.card_coe_set_eq, h22], ?_, ?_, ?_, hB6,
    fun T hTC hT => hS.existsUnique_block hC hTC hT, ?_, h21, ?_, ?_, ?_,
    hS.isMultiplyPretransitive_three hC, hFC, ?_⟩
  · have h := finrank_cliqueCode (lab := lab) (C := C) hR'
    rw [Nat.card_coe_set_eq, h22] at h
    omega
  · intro f hf hf0
    exact hS.six_le_card_of_sum_eq_zero hC (Finsupp.support_nonempty_iff.2 hf0)
      ((mem_cliqueCode_iff f).1 hf)
  · classical
    obtain ⟨u, hu⟩ := hS.nonempty_of_isSliceMaxClique hC
    obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
    obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
    obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
    obtain ⟨A, hAW, hA⟩ := Set.nonempty_of_ncard_ne_zero (by rw [ncard_lines hW]; norm_num)
    obtain ⟨T, huT, hT5, hT0, -⟩ := L.exists_word_of_line hS hC hu g hWe hAW hA
    refine ⟨indicWord (insert ⟨u, hu⟩ T), ?_, ?_⟩
    · rw [mem_cliqueCode_iff, support_indicWord]
      convert hT0
    · rw [support_indicWord]
      convert congrArg (· + 1) hT5 using 1
      exact Finset.card_insert_of_notMem huT
  · have h := ncard_mul_eq_of_double_count hCfin hB6 h21
    rw [h22] at h
    omega
  · intro u hu L W hW hWe B
    obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
    exact L.mem_cliqueBlocks_and_mem_iff hS hC hu g hWe B
  · intro a f hf
    exact mapDomain_mem_cliqueCode hS.lab_act (fun x hx => (a.2.2 x).2 hx) _ (fun _ => rfl) hf
  · intro a ha B hB
    exact image_mem_cliqueBlocks hS.lab_act (fun x hx => (ha.2 x).2 hx)
      (setStabPerm act lab Y C ⟨a, ha⟩) (fun _ => rfl) hB
  · intro u hu L W hW hWe
    exact ⟨hS.mem_range_restrL_iff_setStab hC hu L hWe, exists_levi_mulEquiv hW⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
