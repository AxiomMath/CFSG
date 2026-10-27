module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

structure Cfg4Setting (X L : Subgroup (MulAut W)) (Z : Subgroup W) : Prop where
  sq : ∀ w : W, w ^ 2 = 1
  elem : IsElemAbelianOfRank 3 3 ↥L
  le : L ≤ X
  norm : ∀ x ∈ X, L.map (MulAut.conj x).toMonoidHom = L
  rk_eq : rk ↥Z = 2
  indep : sSupIndep (conjSubs X Z)
  sup_eq : sSup (conjSubs X Z) = ⊤
  ncard_eq : (conjSubs X Z).ncard = 4
  perm : ∀ π : Equiv.Perm ↥(conjSubs X Z), ∃ g ∈ X, ∀ Y : ↥(conjSubs X Z),
    (Y : Subgroup W).map g.toMonoidHom = (π Y : Subgroup W)

theorem s16c167_cfg4_map_mem {X : Subgroup (MulAut W)} {Z : Subgroup W} {g : MulAut W}
    (hg : g ∈ X) {Y : Subgroup W} (hY : Y ∈ conjSubs X Z) :
    Y.map g.toMonoidHom ∈ conjSubs X Z := by
  obtain ⟨h, hh, rfl⟩ := hY
  refine ⟨g * h, X.mul_mem hg hh, ?_⟩
  show (Z.map h.toMonoidHom).map g.toMonoidHom = Z.map (g * h).toMonoidHom
  rw [Subgroup.map_map]
  rfl

theorem s16c167_cfg4_transitive {X : Subgroup (MulAut W)} {Z : Subgroup W} {Y Y' : Subgroup W}
    (hY : Y ∈ conjSubs X Z) (hY' : Y' ∈ conjSubs X Z) :
    ∃ g ∈ X, Y.map g.toMonoidHom = Y' := by
  obtain ⟨h, hh, rfl⟩ := hY
  obtain ⟨h', hh', rfl⟩ := hY'
  refine ⟨h' * h⁻¹, X.mul_mem hh' (X.inv_mem hh), ?_⟩
  show (Z.map h.toMonoidHom).map (h' * h⁻¹).toMonoidHom = Z.map h'.toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext m
  simp [MulAut.mul_apply]

theorem s16c167_cfg4_inf_eq_bot {S : Set (Subgroup W)} (hind : sSupIndep S) {Y₁ Y₂ : Subgroup W}
    (h₁ : Y₁ ∈ S) (h₂ : Y₂ ∈ S) (hne : Y₁ ≠ Y₂) : Y₁ ⊓ Y₂ = ⊥ := by
  exact disjoint_iff.mp (hind.pairwiseDisjoint h₁ h₂ hne)

theorem s16c167_cfg4_rk_mem {X : Subgroup (MulAut W)} {Z : Subgroup W} {Y : Subgroup W}
    (hY : Y ∈ conjSubs X Z) : rk ↥Y = rk ↥Z := by
  obtain ⟨g, -, rfl⟩ := hY
  exact rk_map_aut_eq Z g

theorem s16c167_cfg4_centSub_conj (x : MulAut W) (Y : Subgroup W) :
    (centSub Y).map (MulAut.conj x).toMonoidHom = centSub (Y.map x.toMonoidHom) := by
  ext y
  simp only [Subgroup.mem_map, mem_centSub, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩ u hu
    obtain ⟨v, hv, rfl⟩ := hu
    show (x * z * x⁻¹) (x v) = x v
    simp [MulAut.mul_apply, hz v hv]
  · intro h
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · intro v hv
      have h1 : y (x v) = x v := h (x v) (Subgroup.mem_map_of_mem _ hv)
      show (x⁻¹ * y * x) v = v
      simp [MulAut.mul_apply, h1]
    · change x * (x⁻¹ * y * x) * x⁻¹ = y
      group

theorem s16c167_cfg4_perm4_normal {α : Type} [Fintype α] (hα : Fintype.card α = 4)
    (N : Subgroup (Equiv.Perm α)) [N.Normal] (h3 : ∀ x ∈ N, x ^ 3 = 1) : N = ⊥ := by
  classical
  by_contra hNbot
  obtain ⟨x, hxN, hxne⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hNbot
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hx3 : x ^ 3 = 1 := h3 x hxN
  have hxorder : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hxcycle : x.IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order ?_ ?_
    · rw [hxorder]
      exact Nat.prime_three
    · have hle := x.support.card_le_univ
      rw [hα] at hle
      rw [hxorder]
      omega
  have hxthree : x.IsThreeCycle := by
    rw [← card_support_eq_three_iff]
    have h := x.lcm_cycleType
    rw [hxcycle.cycleType, Multiset.lcm_singleton, normalize_eq, hxorder] at h
    exact h
  have hle : alternatingGroup α ≤ N := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    refine (Subgroup.closure_le N).2 ?_
    intro y hy
    have hconj : IsConj x y :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hxthree.cycleType, hy.cycleType])
    obtain ⟨c, hc⟩ := hconj
    have hxy : (c : Equiv.Perm α) * x * (c : Equiv.Perm α)⁻¹ = y := by
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hxy]
    exact (inferInstance : N.Normal).conj_mem x hxN c
  let e : α ≃ Fin 4 := Fintype.equivFinOfCardEq hα
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  let y : Equiv.Perm α := e.symm.permCongrHom τ
  have hy2 : y ^ 2 = 1 := by
    show (e.symm.permCongrHom τ) ^ 2 = 1
    rw [← map_pow, show τ ^ 2 = 1 by decide, map_one]
  have hyne : y ≠ 1 := by
    intro hy1
    have h2 : y (e.symm 0) = e.symm 1 := by
      show e.symm.permCongr τ (e.symm 0) = e.symm 1
      rw [Equiv.permCongr_apply]
      simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
      rw [show τ 0 = 1 by decide]
    have h1 : y (e.symm 0) = e.symm 0 := by rw [hy1]; rfl
    have h01 : e.symm 0 = e.symm 1 := h1.symm.trans h2
    exact (by decide : (0 : Fin 4) ≠ 1) (e.symm.injective h01)
  have hyalt : y ∈ alternatingGroup α := by
    rw [Equiv.Perm.mem_alternatingGroup]
    show Equiv.Perm.sign (e.symm.permCongr τ) = 1
    rw [Equiv.Perm.sign_permCongr, map_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have hyN : y ∈ N := hle hyalt
  have hy3 : y ^ 3 = 1 := h3 y hyN
  have hyc : y ^ 3 = y := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hy2, one_mul]
  rw [hyc] at hy3
  exact hyne hy3

theorem s16c167_cfg4_stab [Finite W] {X L : Subgroup (MulAut W)} {Z : Subgroup W}
    (F : Cfg4Setting X L Z) {Y : Subgroup W} (hY : Y ∈ conjSubs X Z) : L ≤ stabSub Y := by
  classical
  intro x hx
  let C := conjSubs X Z
  have hfin : C.Finite := by
    apply Set.finite_of_ncard_ne_zero
    show (conjSubs X Z).ncard ≠ 0
    rw [F.ncard_eq]
    norm_num
  haveI : Fintype ↥C := hfin.fintype
  have hcard : Fintype.card ↥C = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, F.ncard_eq]
  letI : MulAction ↥X ↥C :=
    { smul := fun g Y => ⟨Y.1.map g.1.toMonoidHom, s16c167_cfg4_map_mem g.2 Y.2⟩
      one_smul := fun Y => by
        apply Subtype.ext
        change Y.1.map (MonoidHom.id W) = Y.1
        rw [Subgroup.map_id]
      mul_smul := fun g h Y => by
        apply Subtype.ext
        show Y.1.map ((g * h : ↥X)).1.toMonoidHom =
          (Y.1.map h.1.toMonoidHom).map g.1.toMonoidHom
        rw [Subgroup.map_map]
        rfl }
  have htoPerm : ∀ (g : ↥X) (U : ↥C),
      (((MulAction.toPermHom ↥X ↥C) g) U : Subgroup W) = U.1.map g.1.toMonoidHom := by
    intro g U
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
    rfl
  have hsurj : Function.Surjective (MulAction.toPermHom ↥X ↥C) := by
    intro π
    obtain ⟨g, hg, hgperm⟩ := F.perm π
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Equiv.ext
    intro U
    apply Subtype.ext
    rw [htoPerm]
    exact hgperm U
  let N : Subgroup (Equiv.Perm ↥C) := (L.subgroupOf X).map (MulAction.toPermHom ↥X ↥C)
  have hsubnormal : (L.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff F.le]
    intro h k hh hk
    have hmem : MulAut.conj k h ∈ L.map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    rw [F.norm k hk] at hmem
    simpa [MulAut.conj_apply] using hmem
  haveI : N.Normal := Subgroup.Normal.map hsubnormal (MulAction.toPermHom ↥X ↥C) hsurj
  have hcube : ∀ l ∈ L, l ^ 3 = 1 := by
    intro l hl
    obtain ⟨φ⟩ := F.elem
    have h1 : (⟨l, hl⟩ : ↥L) ^ 3 = 1 := by
      apply φ.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      ext i
      have h3 : (3 : ZMod 3) = 0 := by decide
      simp [h3]
    simpa using congrArg Subtype.val h1
  have hN3 : ∀ y ∈ N, y ^ 3 = 1 := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    rw [← map_pow, ← map_one (MulAction.toPermHom ↥X ↥C)]
    congr 1
    apply Subtype.ext
    simpa using hcube l.1 (Subgroup.mem_subgroupOf.mp hl)
  have hNbot : N = ⊥ := s16c167_cfg4_perm4_normal hcard N hN3
  have hxmem : (MulAction.toPermHom ↥X ↥C) ⟨x, F.le hx⟩ ∈ N :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hx1 : (MulAction.toPermHom ↥X ↥C) ⟨x, F.le hx⟩ = 1 := by
    rw [hNbot] at hxmem
    simpa using hxmem
  have hYmap : Y.map x.toMonoidHom = Y := by
    have h1 := congrArg (fun p : Equiv.Perm ↥C => p ⟨Y, hY⟩) hx1
    have h2 := congrArg Subtype.val h1
    rw [htoPerm] at h2
    simpa using h2
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have hxu : x u ∈ Y.map x.toMonoidHom := by rw [hYmap]; exact hu
    rw [Subgroup.mem_map] at hxu
    obtain ⟨v, hv, hvu⟩ := hxu
    have hvu' : v = u := x.injective hvu
    rwa [hvu'] at hv
  · intro hu
    rw [← hYmap]
    exact Subgroup.mem_map_of_mem _ hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
