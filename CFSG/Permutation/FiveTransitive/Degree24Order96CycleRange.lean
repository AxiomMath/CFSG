module

public import CFSG.Permutation.FiveTransitive.Degree24Order96CycleTransfer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private theorem normalizer_cycleSupport_ker_le_centralizer_cycle_ker
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3) :
    ((normalizerCycleSupportMap
        X P R r hRgenerated hrOrder).comp
      R.normalizerMonoidHom.ker.subtype).ker ≤
      (FiveTransitive.NormalizerGoursat.centralizerCycleMap
        X P R r).ker := by
  classical
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let C : Subgroup N :=
    R.normalizerMonoidHom.ker
  let g : Equiv.Perm X := (r : P)
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  let ψ :
      N →*
        Equiv.Perm (cycleSupportFinset g) :=
    normalizerCycleSupportMap
      X P R r hRgenerated hrOrder
  let χ :
      C →*
        Equiv.Perm gSupport.cycleFactorsFinset :=
    FiveTransitive.NormalizerGoursat.centralizerCycleMap
      X P R r
  intro q hq
  rw [MonoidHom.mem_ker] at hq ⊢
  have hψq : ψ (q : N) = 1 := by
    change
      (normalizerCycleSupportMap
        X P R r hRgenerated hrOrder) (q : N) = 1
    rw [show
      (q : N) =
        R.normalizerMonoidHom.ker.subtype q by
          rfl]
    simpa only [MonoidHom.comp_apply] using hq
  apply Equiv.ext
  intro a
  apply cycleFactor_support_injective gSupport
  let qN : N := q
  let qP : P := qN
  let qPerm : Equiv.Perm X := qP
  let qSupport :
      Equiv.Perm g.support :=
    (FiveTransitive.NormalizerGoursat.centralizerSupportMap
      X P R r q).1
  let e : g.support ↪ X :=
    Function.Embedding.subtype
      (fun x : X => x ∈ g.support)
  let b : Finset X := a.1.support.map e
  have hb : b ∈ cycleSupportFinset g := by
    simpa only [b, e, gSupport, g] using
      subtype_cycleFactor_support_mem_cycleSupportFinset
        g a
  let b₀ : cycleSupportFinset g := ⟨b, hb⟩
  have hψApply :
      ((ψ qN) b₀).1 = b := by
    have happ :=
      congrFun
        (congrArg DFunLike.coe hψq) b₀
    exact congrArg Subtype.val happ
  have hbFixed : qP • b = b := by
    calc
      qP • b =
          ((normalizerCycleSupportMap
            X P R r hRgenerated hrOrder qN) b₀).1 :=
        (normalizerCycleSupportMap_apply_val
          X P R r hRgenerated hrOrder qN b₀).symm
      _ = b := by
        simpa only [ψ, qN, N, g, b₀] using hψApply
  have hqSupportVal
      (x : g.support) :
      (qSupport x).1 = qPerm x.1 := by
    rfl
  have hmapMem
      (x : g.support) :
      x ∈ a.1.support ↔ x.1 ∈ b := by
    constructor
    · intro hx
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ :=
        Finset.mem_map.mp hx
      have hyx' : y = x :=
        e.injective hyx
      simpa only [hyx'] using hy
  have hqInvariant
      (x : g.support) :
      qSupport x ∈ a.1.support ↔
        x ∈ a.1.support := by
    rw [hmapMem, hmapMem, hqSupportVal]
    change qP • x.1 ∈ b ↔ x.1 ∈ b
    calc
      qP • x.1 ∈ b ↔
          qP • x.1 ∈ qP • b := by
        rw [hbFixed]
      _ ↔ x.1 ∈ b :=
        Finset.smul_mem_smul_finset_iff qP
  have hsupportFixed :
      a.1.support.map qSupport.toEmbedding =
        a.1.support := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ :=
        Finset.mem_map.mp hy
      rw [← hxy]
      exact (hqInvariant x).2 hx
    · intro hy
      refine
        Finset.mem_map.mpr
          ⟨qSupport⁻¹ y, ?_, ?_⟩
      · have hqInv :=
          (hqInvariant (qSupport⁻¹ y)).1
            (by simpa using hy)
        exact hqInv
      · simp
  change
    (qSupport * a.1 * qSupport⁻¹).support =
      a.1.support
  rw [Equiv.Perm.support_conj]
  exact hsupportFixed

theorem centralizer_cycle_range_card_le_normalizer_cycleSupport_range_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3) :
    Nat.card
        (FiveTransitive.NormalizerGoursat.centralizerCycleMap
          X P R r).range ≤
      Nat.card
        (normalizerCycleSupportMap
          X P R r hRgenerated hrOrder).range := by
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let C : Subgroup N :=
    R.normalizerMonoidHom.ker
  let ψ :
      N →*
        Equiv.Perm
          (cycleSupportFinset
            ((r : P) : Equiv.Perm X)) :=
    normalizerCycleSupportMap
      X P R r hRgenerated hrOrder
  let ψC :
      C →*
        Equiv.Perm
          (cycleSupportFinset
            ((r : P) : Equiv.Perm X)) :=
    ψ.comp C.subtype
  let χ :=
    FiveTransitive.NormalizerGoursat.centralizerCycleMap
      X P R r
  have hker : ψC.ker ≤ χ.ker := by
    simpa only [ψC, ψ, χ, C, N] using
      normalizer_cycleSupport_ker_le_centralizer_cycle_ker
        X P R r hRgenerated hrOrder
  have hrangeLe : ψC.range ≤ ψ.range := by
    rintro z ⟨q, rfl⟩
    exact ⟨q.1, rfl⟩
  have hRangeCardLe :
      Nat.card ψC.range ≤ Nat.card ψ.range := by
    exact
      Nat.card_le_card_of_injective
        (fun z : ψC.range =>
          (⟨z.1, hrangeLe z.2⟩ : ψ.range))
        (fun _ _ hab =>
          Subtype.ext
            (congrArg
              (fun z : ψ.range => z.1) hab))
  calc
    Nat.card χ.range =
        χ.ker.index :=
      (Subgroup.index_ker χ).symm
    _ ≤ ψC.ker.index :=
      Subgroup.index_antitone hker
    _ = Nat.card ψC.range :=
      Subgroup.index_ker ψC
    _ ≤ Nat.card ψ.range := hRangeCardLe

end FiveTransitive.Degree24

end CFSG
