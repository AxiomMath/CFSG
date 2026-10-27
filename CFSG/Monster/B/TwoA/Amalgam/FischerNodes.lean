module

public import CFSG.Monster.B.TwoA.Amalgam.FischerSliceNative
public import CFSG.Monster.B.TwoA.Fischer.AffineCayley
public import CFSG.Monster.B.TwoA.Fischer.SliceSimple
public import CFSG.Monster.B.TwoA.Fischer.CliqueM22
public import CFSG.Monster.B.TwoA.Fischer.SplitAffineM22Main

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
open scoped IsMulCommutative

section Slice

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem native_Fischer_maximal_clique_stabilizer_kernel :
    ∀ v w : CVert, w ∈ sphereThree v →
    (∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      (Subtype.val '' D).ncard = 22) ∧
    (∀ (u u' : CVert) (D D' : Set (cgraph.commonNeighbors v w)),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D → u ∈ Subtype.val '' D →
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D' → u' ∈ Subtype.val '' D' →
      ∃ a ∈ cnGroup v w, cvPerm a u = u' ∧ cvPerm a '' (Subtype.val '' D) = Subtype.val '' D') ∧
    ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      (∀ x ∈ (Subtype.val '' D), ∀ y ∈ (Subtype.val '' D), ∃ a ∈ setStab cvPerm clabelS
          (cgraph.commonNeighbors v w) (Subtype.val '' D), cvPerm a x = y) ∧
      Nat.card (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
          (Subtype.val '' D)).range = 443520 ∧
      ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) = Subgroup.closure
          (clabelS '' (Subtype.val '' D)) ∧
      CFSG.IsElementaryAbelian 2 (ptStab cvPerm clabelS (cgraph.commonNeighbors v w)
          (Subtype.val '' D)) ∧
      Nat.card (ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) = 2 ^ 10 ∧
      Nat.card (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
          = 454164480 ∧
      11 ∣ Nat.card (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
          (Subtype.val '' D)).range ∧
      ∀ u ∈ (Subtype.val '' D), ∀ L : LocalChart cvPerm clabelS (cgraph.commonNeighbors v w) u,
        ∃ W : Submodule F4 UnitarySix.V, IsMaxIso W ∧
          L.τ '' {z | (z : CVert) ∈ (Subtype.val '' D)} = planePts W ∧
          ((ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)).subgroupOf
              (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u)).map L.φ = kerL W ∧
          Subgroup.zpowers (clabelS u) ≤ ptStab cvPerm clabelS (cgraph.commonNeighbors v w)
              (Subtype.val '' D) ∧
          ∀ a : sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u, (a : Shat) ∈ ptStab cvPerm
              clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) →
            (L.φ a = 1 ↔ (a : Shat) ∈ Subgroup.zpowers (clabelS u)) := by
  intro v w hw
  obtain ⟨h1, h2, h3⟩ := (native_isFischerSlice hw).maximal_clique_stabilizer_kernel
  exact ⟨fun D hD => h1 _ ((isSliceMaxClique_image_iff hw D).2 hD),
    fun u u' D D' hD hu hD' hu' => h2 u u' _ _ ((isSliceMaxClique_image_iff hw D).2 hD) hu
      ((isSliceMaxClique_image_iff hw D').2 hD') hu',
    fun D hD => h3 _ ((isSliceMaxClique_image_iff hw D).2 hD)⟩

theorem native_Fischer_clique_code_Steiner_design :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (clabelS '' (Subtype.val '' D))),
        Function.Surjective (cliqueLabelMap clabelS (Subtype.val '' D)) ∧ Nat.card
            (Subtype.val '' D) = 22 ∧
        Module.finrank (ZMod 2) (cliqueCode clabelS (Subtype.val '' D)) = 12 ∧
        (∀ f ∈ cliqueCode clabelS (Subtype.val '' D), f ≠ 0 → 6 ≤ f.support.card) ∧
        (∃ f ∈ cliqueCode clabelS (Subtype.val '' D), f.support.card = 6) ∧
        (∀ B ∈ cliqueBlocks clabelS (Subtype.val '' D), B ⊆ (Subtype.val '' D) ∧ B.ncard = 6) ∧
        (∀ T ⊆ (Subtype.val '' D), T.ncard = 3 → ∃! B, B ∈ cliqueBlocks clabelS
            (Subtype.val '' D) ∧ T ⊆ B) ∧
        (cliqueBlocks clabelS (Subtype.val '' D)).ncard = 77 ∧
        (∀ z ∈ (Subtype.val '' D), {B ∈ cliqueBlocks clabelS (Subtype.val '' D) | z ∈
            B}.ncard = 21) ∧
        (∀ u ∈ (Subtype.val '' D), ∀ L : LocalChart cvPerm clabelS (cgraph.commonNeighbors v w) u,
            ∀ W : Submodule F4 UnitarySix.V, IsMaxIso W →
          L.τ '' {z | (z : CVert) ∈ (Subtype.val '' D)} = planePts W →
          ∀ B : Set CVert, (B ∈ cliqueBlocks clabelS (Subtype.val '' D) ∧ u ∈ B) ↔
            ∃ A : Submodule F4 UnitarySix.V, A ≤ W ∧ Module.finrank F4 A = 2 ∧
              B = insert u (Subtype.val '' (L.τ ⁻¹' planePts A))) ∧
        (∀ a : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D), ∀ f ∈
            cliqueCode clabelS (Subtype.val '' D),
          Finsupp.mapDomain (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
              (Subtype.val '' D) a) f ∈ cliqueCode clabelS (Subtype.val '' D)) ∧
        (∀ a ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D), ∀ B ∈
            cliqueBlocks clabelS (Subtype.val '' D), cvPerm a '' B ∈ cliqueBlocks clabelS
                (Subtype.val '' D)) ∧
        MulAction.IsMultiplyPretransitive (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
            (Subtype.val '' D)).range (Subtype.val '' D) 3 ∧
        Nat.card (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
            (Subtype.val '' D)).range = 443520 ∧
        (∀ u ∈ (Subtype.val '' D), ∀ L : LocalChart cvPerm clabelS (cgraph.commonNeighbors v w) u,
            ∀ W : Submodule F4 UnitarySix.V, IsMaxIso W →
          L.τ '' {z | (z : CVert) ∈ (Subtype.val '' D)} = planePts W →
          (∀ σ : Equiv.Perm (planePts W), σ ∈ (restrL W).range ↔
            ∃ a ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D),
                cvPerm a u = u ∧
              ∀ (p : planePts W)
                  (z z' : (sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet u),
                L.τ z = p → (z' : CVert) = cvPerm a z → (σ p : IsoPt) = L.τ z') ∧
          ∃ (e : planePts W ≃ ℙ F4 (Fin 3 → F4)) (θ : (restrL W).range ≃* PSL(3, F4)),
            ∀ (σ : (restrL W).range) (p : planePts W),
              e ((σ : Equiv.Perm (planePts W)) p) = θ σ • e p) :=
  fun _ _ hw D hD =>
    (native_isFischerSlice hw).clique_code_steiner_design ((isSliceMaxClique_image_iff hw D).2 hD)

theorem native_Fischer_clique_hexad_fibers :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (clabelS '' (Subtype.val '' D))),
        (∀ x ∈ (cgraph.commonNeighbors v w), x ∉ (Subtype.val '' D) → (Subtype.val '' D) ∩
            (sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet x = ∅ ∨
          (Subtype.val '' D) ∩ (sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet x ∈
              cliqueBlocks clabelS (Subtype.val '' D)) ∧
        (∀ B ∈ cliqueBlocks clabelS (Subtype.val '' D), (hexadFiber clabelS
            (cgraph.commonNeighbors v w) (Subtype.val '' D) B).ncard = 32 ∧
          (∀ r ∈ ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D), ∀ x ∈
              hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B,
            cvPerm r x ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B) ∧
          (∀ x ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B, ∀ y ∈
              hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B,
            ∃ r ∈ ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D),
                cvPerm r x = y) ∧
          (∀ x ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B,
            ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓ actStab cvPerm
                x = Subgroup.closure (clabelS '' B)) ∧
          Nat.card (Subgroup.closure (clabelS '' B)) = 32) ∧
        (cgraph.commonNeighbors v w) = (Subtype.val '' D) ∪ (⋃ B ∈ cliqueBlocks clabelS
            (Subtype.val '' D), hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)
                B) ∪ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅ ∧
        Disjoint (Subtype.val '' D) (⋃ B ∈ cliqueBlocks clabelS (Subtype.val '' D), hexadFiber
            clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B) ∧
        Disjoint (Subtype.val '' D) (hexadFiber clabelS (cgraph.commonNeighbors v w)
            (Subtype.val '' D) ∅) ∧
        Disjoint (⋃ B ∈ cliqueBlocks clabelS (Subtype.val '' D), hexadFiber clabelS
            (cgraph.commonNeighbors v w) (Subtype.val '' D) B) (hexadFiber clabelS
                (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅) ∧
        (∀ B ∈ cliqueBlocks clabelS (Subtype.val '' D), ∀ B' ∈ cliqueBlocks clabelS
            (Subtype.val '' D), B ≠ B' →
          Disjoint (hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B)
              (hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B')) ∧
        (Subtype.val '' D).ncard = 22 ∧
        (⋃ B ∈ cliqueBlocks clabelS (Subtype.val '' D), hexadFiber clabelS (cgraph.commonNeighbors
            v w) (Subtype.val '' D) B).ncard = 2464 ∧
        (hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅).ncard = 1024 ∧
        (∀ a ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D),
            cvPerm a '' hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅ =
              hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅) ∧
        (∀ a ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D), ∀ B ∈
            cliqueBlocks clabelS (Subtype.val '' D),
          cvPerm a '' B ∈ cliqueBlocks clabelS (Subtype.val '' D) ∧
            cvPerm a '' hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) B =
                hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)
                  (cvPerm a '' B)) :=
  fun _ _ hw D hD =>
    (native_isFischerSlice hw).clique_hexad_fibers ((isSliceMaxClique_image_iff hw D).2 hD)

theorem native_Fischer_affine_orbit_Cayley_graph :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D → ∀ x : CVert,
      x ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅ →
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (clabelS '' (Subtype.val '' D))),
        ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) = labelLayer clabelS
            (Subtype.val '' D) 0 ∪ labelLayer clabelS (Subtype.val '' D) 1 ∪ labelLayer clabelS
                (Subtype.val '' D) 2 ∪
          labelLayer clabelS (Subtype.val '' D) 3 ∧
        labelLayer clabelS (Subtype.val '' D) 0 = {1} ∧ labelLayer clabelS (Subtype.val '' D) 1 =
            clabelS '' (Subtype.val '' D) ∧
        labelLayer clabelS (Subtype.val '' D) 2 = {r | ∃ a ∈ (Subtype.val '' D), ∃ b ∈
            (Subtype.val '' D), a ≠ b ∧ r = clabelS a * clabelS b} ∧
        hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅ =
            ⋃ i < 4, (fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) i ∧
        ((fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) 0).ncard = 1 ∧
        ((fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) 1).ncard = 22 ∧
        ((fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) 2).ncard = 231 ∧
        ((fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) 3).ncard = 770 ∧
        (∀ y ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅, ∀ y' ∈
            hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅,
          (∃ k ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓ actStab
              cvPerm x, cvPerm k y = y') ↔
            ∃ i < 4, y ∈ (fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) i ∧
              y' ∈ (fun r => cvPerm r x) '' labelLayer clabelS (Subtype.val '' D) i) ∧
        (∀ r ∈ ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D), ∀ s ∈ ptStab
            cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D),
          (sliceGraph clabelS (cgraph.commonNeighbors v w)).Adj (cvPerm r x) (cvPerm s x) ↔ r * s ∈
              labelLayer clabelS (Subtype.val '' D) 2) ∧
        (∀ B ∈ cliqueBlocks clabelS (Subtype.val '' D),
          ((sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet x ∩ hexadFiber clabelS
              (cgraph.commonNeighbors v w) (Subtype.val '' D) B).ncard = 6) ∧
        (∀ B ∈ cliqueBlocks clabelS (Subtype.val '' D), ∀ y ∈ hexadFiber clabelS
            (cgraph.commonNeighbors v w) (Subtype.val '' D) B,
          ((sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet y ∩ hexadFiber clabelS
              (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅).ncard = 192) ∧
        (∀ k ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓ actStab
            cvPerm x, Commute (clabelS x) k) ∧
        (∀ a ∈ (Subtype.val '' D), cvPerm (clabelS x) a = cvPerm (clabelS a) x ∧ cvPerm (clabelS x)
            (cvPerm (clabelS a) x) = a) ∧
        cvPerm (clabelS x) x = x ∧
        (∀ r ∈ labelLayer clabelS (Subtype.val '' D) 2, cvPerm (clabelS x) (cvPerm r x) =
            cvPerm r x) ∧
        (∀ r ∈ labelLayer clabelS (Subtype.val '' D) 3, cvPerm (clabelS x) (cvPerm r x) ≠
            cvPerm r x) ∧
        cvPerm (clabelS x) '' (Subtype.val '' D) =
            (fun a => cvPerm (clabelS a) x) '' (Subtype.val '' D) ∧
        cvPerm (clabelS x) '' (Subtype.val '' D) ⊆ hexadFiber clabelS (cgraph.commonNeighbors v w)
            (Subtype.val '' D) ∅ ∧
        IsSliceMaxClique clabelS (cgraph.commonNeighbors v w)
            (cvPerm (clabelS x) '' (Subtype.val '' D)) ∧
        (cvPerm (clabelS x) '' (Subtype.val '' D)).ncard = 22 :=
  fun _ _ hw D hD _ hx =>
    (native_isFischerSlice hw).affine_orbit_cayley_graph ((isSliceMaxClique_image_iff hw D).2 hD)
      hx

theorem native_three_transposition_group_primitive_and_radical_free :
    ∀ v w : CVert, ∀ hw : w ∈ sphereThree v,
    (letI : MulAction (cnGroup v w) (cgraph.commonNeighbors v w) :=
        (native_isFischerSlice hw).mulAction;
      MulAction.IsPreprimitive (cnGroup v w) (cgraph.commonNeighbors v w)) ∧
    (∀ N : Subgroup (cnGroup v w), N.Normal → N ≠ ⊥ →
      ∀ y ∈ (cgraph.commonNeighbors v w), ∀ z ∈ (cgraph.commonNeighbors v w),
        ∃ n ∈ N, cvPerm (n : Shat) y = z) ∧
    (∀ N : Subgroup (cnGroup v w), N.Normal → Group.IsSolvable N → N = ⊥) ∧
    ∀ p : ℕ, p.Prime → CFSG.pCore p (cnGroup v w) = ⊥ :=
  fun _ _ hw => (native_isFischerSlice hw).primitive_and_radical_free

theorem native_three_transposition_group_simple_derived_socle :
    ∀ v w : CVert, w ∈ sphereThree v →
    IsSimpleGroup (commutator (cnGroup v w)) ∧
    ¬ IsMulCommutative (commutator (cnGroup v w)) ∧
    (∀ N : Subgroup (cnGroup v w), N.Normal → N ≠ ⊥ → commutator (cnGroup v w) ≤ N) ∧
    (∀ N : Subgroup (cnGroup v w), (N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup (cnGroup v w),
      M.Normal → M ≠ ⊥ → M ≤ N → M = N) ↔ N = commutator (cnGroup v w)) ∧
    ((commutator (cnGroup v w)).index = 1 ∨ (commutator (cnGroup v w)).index = 2) ∧
    Function.Injective (MulAut.conjNormal (H := commutator (cnGroup v w))) ∧
    (Nat.card (commutator (cnGroup v w)) = 64561751654400 ∨
      Nat.card (commutator (cnGroup v w)) = 32280875827200) ∧
    (∀ N : Subgroup (cnGroup v w), N.Normal → N ≠ ⊥ → N ≠ ⊤ → N.index = 2) ∧
    (commutator (cnGroup v w) ≠ ⊤ → ∀ (u : CVert) (hu : u ∈ (cgraph.commonNeighbors v w)),
      (⟨clabelS u, lab_mem_sliceGroup (lab := clabelS) hu⟩ : cnGroup v w) ∉ commutator
          (cnGroup v w) ∧
      (∀ g ∈ (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u).subgroupOf (cnGroup v w),
        Commute g ⟨clabelS u, lab_mem_sliceGroup (lab := clabelS) hu⟩) ∧
      Subgroup.zpowers (⟨clabelS u, lab_mem_sliceGroup (lab := clabelS) hu⟩ : cnGroup v w) ⊓
        (commutator (cnGroup v w) ⊓
          (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u).subgroupOf (cnGroup v w)) =
        ⊥ ∧
      Subgroup.zpowers (⟨clabelS u, lab_mem_sliceGroup (lab := clabelS) hu⟩ : cnGroup v w) ⊔
        (commutator (cnGroup v w) ⊓
          (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u).subgroupOf (cnGroup v w)) =
        (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u).subgroupOf (cnGroup v w) ∧
      Nonempty (↥(commutator (cnGroup v w) ⊓
        (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u).subgroupOf (cnGroup v w)) ≃*
          ProjSU)) :=
  fun _ _ hw => (native_isFischerSlice hw).simple_derived_socle

theorem native_three_transposition_group_simple :
    ∀ v w : CVert, w ∈ sphereThree v →
    IsSimpleGroup (cnGroup v w) ∧ ¬ IsMulCommutative (cnGroup v w) ∧
    Nat.card (cnGroup v w) = 64561751654400 ∧
    commutator (cnGroup v w) = ⊤ ∧
    (∃ D : ConjClasses (cnGroup v w),
      D.carrier = {g : cnGroup v w | (g : Shat) ∈ clabelS '' (cgraph.commonNeighbors v w)}) ∧
    (clabelS '' (cgraph.commonNeighbors v w)).ncard = 3510 ∧
    (∀ y ∈ (cgraph.commonNeighbors v w), orderOf (clabelS y) = 2) ∧
    Subgroup.closure {g : cnGroup v w | (g : Shat) ∈ clabelS '' (cgraph.commonNeighbors v w)} = ⊤ ∧
    (∀ y ∈ (cgraph.commonNeighbors v w), ∀ z ∈ (cgraph.commonNeighbors v w),
        orderOf (clabelS y * clabelS z) ∈ ({1, 2, 3} : Finset ℕ)) ∧
    (∀ y ∈ (cgraph.commonNeighbors v w), ∀ z ∈ (cgraph.commonNeighbors v w), y ≠ z →
        (orderOf (clabelS y * clabelS z) = 2 ↔
          (sliceGraph clabelS (cgraph.commonNeighbors v w)).Adj y z)) ∧
    ∀ [Fintype (cgraph.commonNeighbors v w)] [DecidableRel
        ((sliceGraph clabelS (cgraph.commonNeighbors v w)).induce
            (cgraph.commonNeighbors v w)).Adj],
      ((sliceGraph clabelS (cgraph.commonNeighbors v w)).induce
          (cgraph.commonNeighbors v w)).IsSRGWith 3510 693 180 126 :=
  fun _ _ hw => (native_isFischerSlice hw).simple

end Slice

section M22

open CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22

theorem native_Fischer_clique_catalog_M22_quotient :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (clabelS '' (Subtype.val '' D))),
      ∃ (η : (Subtype.val '' D) ≃ X₀)
        (θ : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⧸
          (ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)).subgroupOf
            (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) ≃*
          CFSG.Blueprint.NativeSporadic.M22),
        (∀ T : Finset (Subtype.val '' D), Subtype.val '' (T : Set (Subtype.val '' D)) ∈
            cliqueBlocks clabelS (Subtype.val '' D) ↔
          T.image (fun z => (η z : Fin 24)) ∈ ℬ₀) ∧
        (∀ (f : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
            (z : (Subtype.val '' D)),
          (η (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) f z) :
              Fin 24) = psiHom (θ f) (η z)) ∧
        ∀ σ : Equiv.Perm X₀, σ ∈ P0in.map resHom ↔
          ∃ f : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D),
            ∀ z : (Subtype.val '' D), σ (η z) =
              η (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) f z) :=
  fun _ _ hw D hD => by
    have hC := (isSliceMaxClique_image_iff hw D).2 hD
    have inst := (native_isFischerSlice hw).isElementaryAbelian_closure hC.1.1 hC.1.2
    exact ⟨inst, (native_isFischerSlice hw).clique_catalog_M22_quotient hC⟩

theorem native_Fischer_clique_exact_binary_M22_module :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (clabelS '' (Subtype.val '' D))),
      ∀ (η : (Subtype.val '' D) ≃ X₀)
        (θ : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⧸
          (ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)).subgroupOf
            (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) ≃*
          CFSG.Blueprint.NativeSporadic.M22),
        (∀ T : Finset (Subtype.val '' D), Subtype.val '' (T : Set (Subtype.val '' D)) ∈
            cliqueBlocks clabelS (Subtype.val '' D) ↔
          T.image (fun z => (η z : Fin 24)) ∈ ℬ₀) →
        (∀ (f : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
            (z : (Subtype.val '' D)),
          (η (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) f z) :
              Fin 24) = psiHom (θ f) (η z)) →
        ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) =
            Subgroup.closure (clabelS '' (Subtype.val '' D)) ∧
        (∃! φ : Additive (Subgroup.closure (clabelS '' (Subtype.val '' D))) ≃ₗ[ZMod 2] W₀,
          ∀ z : (Subtype.val '' D), φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) ∧
        (∀ φ : Additive (Subgroup.closure (clabelS '' (Subtype.val '' D))) ≃ₗ[ZMod 2] W₀,
          (∀ z : (Subtype.val '' D), φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) →
          ∀ (f : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
            (r : Subgroup.closure (clabelS '' (Subtype.val '' D)))
            (h : (f : Shat) * r * (f : Shat)⁻¹ ∈
              Subgroup.closure (clabelS '' (Subtype.val '' D))),
            φ (Additive.ofMul ⟨(f : Shat) * r * (f : Shat)⁻¹, h⟩) =
              rhoW (θ f) (φ (Additive.ofMul r))) ∧
        Module.finrank (ZMod 2) W₀ = 10 ∧
        (∀ g : CFSG.Blueprint.NativeSporadic.M22, (∀ y : W₀, rhoW g y = y) → g = 1) ∧
        (∀ U : Submodule (ZMod 2) W₀, (∀ g, U ≤ U.comap (rhoW g)) → U = ⊥ ∨ U = ⊤) ∧
        (∀ N : Subgroup Shat, N ≤ Subgroup.closure (clabelS '' (Subtype.val '' D)) →
          (∀ f ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D),
            ∀ n ∈ N, f * n * f⁻¹ ∈ N) →
          N = ⊥ ∨ N = Subgroup.closure (clabelS '' (Subtype.val '' D))) ∧
        _root_.commutator
            (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) = ⊤ ∧
        Subgroup.center
            (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) = ⊥ :=
  fun _ _ hw D hD => by
    have hC := (isSliceMaxClique_image_iff hw D).2 hD
    have inst := (native_isFischerSlice hw).isElementaryAbelian_closure hC.1.1 hC.1.2
    exact ⟨inst, fun η θ hη hθ =>
      (native_isFischerSlice hw).clique_exact_binary_M22_module hC η θ hη hθ⟩

theorem native_Fischer_clique_split_pinned_M22_affine_action :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (clabelS '' (Subtype.val '' D))),
      ∀ (η : (Subtype.val '' D) ≃ X₀)
        (θ : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⧸
          (ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)).subgroupOf
            (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) ≃*
          CFSG.Blueprint.NativeSporadic.M22),
        (∀ T : Finset (Subtype.val '' D), Subtype.val '' (T : Set (Subtype.val '' D)) ∈
            cliqueBlocks clabelS (Subtype.val '' D) ↔
          T.image (fun z => (η z : Fin 24)) ∈ ℬ₀) →
        (∀ (f : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
            (z : (Subtype.val '' D)),
          (η (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) f z) :
              Fin 24) = psiHom (θ f) (η z)) →
        ∀ φ : Additive (Subgroup.closure (clabelS '' (Subtype.val '' D))) ≃ₗ[ZMod 2] W₀,
        (∀ z : (Subtype.val '' D), φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) →
        (∀ x ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅,
          ∀ y ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅,
          ∃! r, r ∈ ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∧
            cvPerm r x = y) ∧
        ∀ x ∈ hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅,
          ((ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)).subgroupOf
              (setStab cvPerm clabelS (cgraph.commonNeighbors v w)
                (Subtype.val '' D))).IsComplement'
            ((setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓
                actStab cvPerm x).subgroupOf
              (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))) ∧
          (∃ eK : ↥(setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓
                actStab cvPerm x) ≃* CFSG.Blueprint.NativeSporadic.M22,
            (∀ k, eK k = θ (Subgroup.inclusion inf_le_left k)) ∧
            ∀ (k : ↥(setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓
                actStab cvPerm x)) (z : (Subtype.val '' D)),
              (η (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)
                  (Subgroup.inclusion inf_le_left k) z) : Fin 24) =
                psiHom (eK k) (η z)) ∧
          ∃ (Ψ : ↥(setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) ≃*
              Multiplicative W₀ ⋊[repMulAut rhoW] CFSG.Blueprint.NativeSporadic.M22)
            (c : ↥(hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅) ≃ W₀),
            (∀ (r : Subgroup.closure (clabelS '' (Subtype.val '' D))) (k : Shat)
              (hk : k ∈ setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ⊓
                actStab cvPerm x)
              (h : (r : Shat) * k ∈
                setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)),
              Ψ ⟨(r : Shat) * k, h⟩ = ⟨Multiplicative.ofAdd (φ (Additive.ofMul r)),
                θ (QuotientGroup.mk (⟨k, hk.1⟩ :
                  setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)))⟩) ∧
            (∀ (r : Subgroup.closure (clabelS '' (Subtype.val '' D)))
              (h : cvPerm (r : Shat) x ∈
                hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅),
              c ⟨cvPerm (r : Shat) x, h⟩ = φ (Additive.ofMul r)) ∧
            (∀ (z : (Subtype.val '' D))
              (h : cvPerm (clabelS z) x ∈
                hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅),
              c ⟨cvPerm (clabelS z) x, h⟩ = K₀.mkQ (e (η z))) ∧
            ∀ (f : setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
              (y : ↥(hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅))
              (h : cvPerm (f : Shat) y ∈
                hexadFiber clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ∅),
              c ⟨cvPerm (f : Shat) y, h⟩ =
                Multiplicative.toAdd (Ψ f).left + rhoW (Ψ f).right (c y) :=
  fun _ _ hw D hD => by
    have hC := (isSliceMaxClique_image_iff hw D).2 hD
    have inst := (native_isFischerSlice hw).isElementaryAbelian_closure hC.1.1 hC.1.2
    exact ⟨inst, fun η θ hη hθ φ hφ =>
      (native_isFischerSlice hw).clique_split_pinned_M22 hC η θ hη hθ φ hφ⟩

end M22

end CFSG.Monster.B.TwoA.Amalgam
