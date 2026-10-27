module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv
import CFSG.Walter.W67.Section5.P56AbAut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1Cent_eq_top_of_index_lt_five {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] [Group.IsPerfect (X ⧸ N)] {H : Subgroup X} (hNH : N ≤ H) (hH : H.index < 5) :
    H = ⊤ := by
  have hker : N ≤ (MulAction.toPermHom X (X ⧸ H)).ker := by
    rw [← Subgroup.normalCore_eq_ker]
    exact Subgroup.normal_le_normalCore.mpr hNH
  have hcard : Nat.card (X ⧸ H) ≤ 4 := by
    rw [← Subgroup.index_eq_card]
    omega
  have h1 : ∀ x : X, MulAction.toPermHom X (X ⧸ H) x = 1 := fun x => by
    have := CFSG.GH74.GLS.IVK.GHInv.perfect_hom_perm_eq_one hcard
      (QuotientGroup.lift N (MulAction.toPermHom X (X ⧸ H)) hker) (QuotientGroup.mk x)
    simpa using this
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (MulAction.toPermHom X (X ⧸ H)).ker := MonoidHom.mem_ker.mpr (h1 x)
  rw [← Subgroup.normalCore_eq_ker] at hx
  exact H.normalCore_le hx

theorem res1Cent_le_centralizer_of_card_le_four {G : Type*} [Group G] [Finite G]
    {L U : Subgroup G} [Group.IsPerfect L] (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hU : Nat.card U ≤ 4) : L ≤ Subgroup.centralizer (U : Set G) := by
  intro l hl
  have h1 : (MulAut.toPerm U).comp (CFSG.Walter.W67.P56Ab.conjAut L U hLU) ⟨l, hl⟩ = 1 :=
    CFSG.GH74.GLS.IVK.GHInv.perfect_hom_perm_eq_one hU _ _
  have h2 : CFSG.Walter.W67.P56Ab.conjAut L U hLU ⟨l, hl⟩ = 1 := by
    refine MulEquiv.ext fun u => ?_
    exact congrArg (fun σ : Equiv.Perm U => σ u) h1
  have h3 := (CFSG.Walter.W67.P56Ab.conjAut_eq_one_iff L U hLU ⟨l, hl⟩).mp h2
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h3 u hu).symm

theorem res1Cent_le_centralizer_of_sq {G : Type*} [Group G] [Finite G] {L U : Subgroup G}
    [Group.IsPerfect L] (hU : IsPGroup 2 U) (hUc : IsMulCommutative U)
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hfix : ∀ l ∈ L, ∀ u ∈ U, u ^ 2 = 1 → l * u * l⁻¹ = u) :
    L ≤ Subgroup.centralizer (U : Set G) := by
  set f : L →* MulAut U := CFSG.Walter.W67.P56Ab.conjAut L U hLU with hf
  have hcomm : ∀ a b : U, a * b = b * a := fun a b => hUc.is_comm.comm a b
  have hpg : IsPGroup 2 f.range := by
    rintro ⟨_, l, rfl⟩
    have hα : ∀ x : U, x ^ 2 = 1 → f l x = x := fun x hx => by
      apply Subtype.ext
      rw [hf, CFSG.Walter.W67.P56Ab.conjAut_apply_coe]
      exact hfix l l.2 x x.2 (by simpa using congrArg Subtype.val hx)
    have hαj : ∀ j : ℕ, ∀ x : U, x ^ 2 = 1 → (f l ^ j) x = x := fun j x hx => by
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, MulAut.mul_apply, hα x hx, ih]
    have hl0 : orderOf (f l) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (orderOf_map_dvd f l) (orderOf_pos l)).ne'
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hl0
    have hord : orderOf (f l ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) ⟨m, hkm⟩, hkm,
        Nat.mul_div_cancel_left m (pow_pos two_pos k)]
    have hcop : Nat.Coprime (orderOf (f l ^ 2 ^ k)) 2 := by
      rw [hord]
      exact Nat.coprime_two_right.mpr hm
    have h1 : f l ^ 2 ^ k = 1 :=
      CFSG.Walter.W67.P56Ab.eq_one_of_forall_pow_eq_one hU hcomm _ hcop (hαj _)
    exact ⟨k, Subtype.ext (by simpa using h1)⟩
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hnil : Group.IsNilpotent f.range := hpg.isNilpotent
  have hsub : Subsingleton f.range := by
    by_contra hne
    rw [not_subsingleton_iff_nontrivial] at hne
    exact Group.IsPerfect.not_isNilpotent f.range hnil
  intro l hl
  have h1 : f ⟨l, hl⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨l, hl⟩, ⟨l, hl⟩, rfl⟩ : f.range) 1)
  have h2 := (CFSG.Walter.W67.P56Ab.conjAut_eq_one_iff L U hLU ⟨l, hl⟩).mp h1
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h2 u hu).symm

theorem res1Cent_mem_closure_sq {G : Type*} [Group G] {U : Subgroup G} (hUc : IsMulCommutative U)
    {x : G} (hx : x ∈ Subgroup.closure {u | u ∈ U ∧ u ^ 2 = 1}) : x ∈ U ∧ x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem U, one_pow 2⟩
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y :=
      congrArg Subtype.val (hUc.is_comm.comm (⟨x, hx.1⟩ : U) ⟨y, hy.1⟩)
    rw [hxy.mul_pow, hx.2, hy.2, one_mul]
  | inv x _ hx => exact ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem res1Cent_le_normalizer_closure_sq {G : Type*} [Group G] {X U : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    X ≤ Subgroup.normalizer (Subgroup.closure {u | u ∈ U ∧ u ^ 2 = 1} : Set G) := by
  have key : ∀ y ∈ Subgroup.normalizer (U : Set G),
      ∀ h ∈ Subgroup.closure {u | u ∈ U ∧ u ^ 2 = 1},
        y * h * y⁻¹ ∈ Subgroup.closure {u | u ∈ U ∧ u ^ 2 = 1} := by
    intro y hy h hh
    induction hh using Subgroup.closure_induction with
    | mem u hu =>
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hy u).mp hu.1, ?_⟩
      rw [conj_pow, hu.2, mul_one, mul_inv_cancel]
    | one => simp
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact mul_mem ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ha
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key x (hXU hx) h hh, fun hh => ?_⟩
  have := key x⁻¹ (inv_mem (hXU hx)) _ hh
  have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem res1Cent_eight_le_card {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (hU : IsPGroup 2 U) (h4 : ¬ Nat.card U ≤ 4) : 8 ≤ Nat.card U := by
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  rw [hn] at h4 ⊢
  by_contra h8
  have hn3 : n < 3 := by
    by_contra h
    exact h8 (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp h))
  interval_cases n <;> simp at h4

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
