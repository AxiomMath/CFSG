module

public import CFSG.Quasithin.Background.F7TwoE2Base
public import CFSG.Quasithin.Background.F7TwoInvDefs
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

section Simple

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem center_eq_bot_of_isComponent (hrad : CFSG.solvableRadical Γ = ⊥) {L : Subgroup Γ}
    (hL : CFSG.IsComponent L) : Subgroup.center ↥L = ⊥ := by
  set Z : Subgroup Γ := (Subgroup.center ↥L).map L.subtype with hZ
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hZn : (Z.subgroupOf L).Normal := by
    have : Z.subgroupOf L = Subgroup.center ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [this]
    infer_instance
  have hZsub : IsSubnormal Z ⊤ :=
    A3.subnormal_top_iff.mpr (Subgroup.IsSubnormal.step Z L hZL hL.2 hZn)
  have hZs : Group.IsSolvable ↥Z := by
    let e : Subgroup.center ↥L ≃* ↥Z :=
      Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have h1 := le_solvRad_of_subnormal hZsub hZs
  rw [← A3.solvableRadical_eq_solvRad_top, hrad] at h1
  rw [eq_bot_iff]
  intro z hz
  have : (z : Γ) ∈ Z := ⟨z, hz, rfl⟩
  have h2 : (z : Γ) = 1 := Subgroup.mem_bot.mp (h1 this)
  exact Subgroup.mem_bot.mpr (Subtype.ext h2)

theorem isSimpleGroup_of_isComponent (hrad : CFSG.solvableRadical Γ = ⊥) {L : Subgroup Γ}
    (hL : CFSG.IsComponent L) : IsSimpleGroup ↥L := by
  have hZ := center_eq_bot_of_isComponent hrad hL
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

omit [Finite Γ] in
theorem exists_mul_ne_of_isComponent {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    ∃ x y : ↥L, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hL.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem not_isPGroup_two_of_isComponent {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    ¬ IsPGroup 2 ↥L := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have : Group.IsPerfect ↥L := hL.1.1
  have : Group.IsNilpotent ↥L := hP.isNilpotent
  exact Group.IsPerfect.not_isSolvable ↥L inferInstance

end Simple

theorem closure_not_two_power_eq_top {L : Type*} [Group L] [IsSimpleGroup L]
    (h : ¬ IsPGroup 2 L) : Subgroup.closure {y : L | ¬ ∃ k : ℕ, y ^ 2 ^ k = 1} = ⊤ := by
  set N := Subgroup.closure {y : L | ¬ ∃ k : ℕ, y ^ 2 ^ k = 1} with hN
  have hconj : ∀ g y : L, (¬ ∃ k : ℕ, y ^ 2 ^ k = 1) → ¬ ∃ k : ℕ, (g * y * g⁻¹) ^ 2 ^ k = 1 := by
    rintro g y hy ⟨k, hk⟩
    exact hy ⟨k, by rwa [conj_pow, conj_eq_one_iff] at hk⟩
  have hnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hconj g y hy)
    | one => simp
    | mul y z _ _ hy hz =>
      have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hy
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exfalso
    have hnot : ¬ ∀ g : L, ∃ k : ℕ, g ^ 2 ^ k = 1 := h
    push Not at hnot
    obtain ⟨g, hg⟩ := hnot
    have hgN : g ∈ N := Subgroup.subset_closure fun ⟨k, hk⟩ => hg k hk
    rw [hbot, Subgroup.mem_bot] at hgN
    exact hg 0 (by simpa using hgN)
  · exact htop

theorem le_closure_nonTwoConj_of_swap {Γ : Type*} [Group Γ] [Finite Γ]
    (hrad : CFSG.solvableRadical Γ = ⊥) {L : Subgroup Γ} (hL : CFSG.IsComponent L)
    {B : Subgroup Γ} {b : Γ} (hbB : b ∈ B) (hbL : b ∉ Subgroup.normalizer (L : Set Γ)) :
    L ≤ Subgroup.closure (nonTwoConj B ⊤) := by
  have hZ := center_eq_bot_of_isComponent hrad hL
  have hL' : CFSG.IsComponent (conjSub b L) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hL
  have hne : conjSub b L ≠ L := fun h => hbL (conjSub_eq_iff_mem_normalizer.mp h)
  have hcomm : ⁅L, conjSub b L⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL hL').resolve_left (Ne.symm hne)
  have hcomm' : ∀ l ∈ L, ∀ l' ∈ conjSub b L, l * l' = l' * l := fun l hl l' hl' => by
    have h1 := Subgroup.commutator_mem_commutator hl hl'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have key : ∀ y ∈ L, (¬ ∃ k : ℕ, y ^ 2 ^ k = 1) → y ∈ nonTwoConj B ⊤ := by
    intro y hyL hy
    rw [mem_nonTwoConj_top]
    intro hP
    apply hy
    have hdP : (y⁻¹ * b * y) * b⁻¹ ∈ B ⊔ conjSubgroup B y := by
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (B.inv_mem hbB))
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hbB
    obtain ⟨k, hk⟩ := pow_eq_one_of_mem_isPGroup hP hdP
    have hc : Commute y⁻¹ (b * y * b⁻¹) :=
      hcomm' _ (L.inv_mem hyL) _ (mem_conjSub_of_mem hyL)
    have hdd : (y⁻¹ * b * y) * b⁻¹ = y⁻¹ * (b * y * b⁻¹) := by group
    rw [hdd, hc.mul_pow, inv_pow, conj_pow] at hk
    have h1 : y ^ 2 ^ k = b * y ^ 2 ^ k * b⁻¹ := inv_mul_eq_one.mp hk
    have hzL : y ^ 2 ^ k ∈ L := L.pow_mem hyL _
    have hz' : y ^ 2 ^ k ∈ conjSub b L := by
      rw [mem_conjSub_iff]
      have e : b⁻¹ * y ^ 2 ^ k * b = y ^ 2 ^ k :=
        calc b⁻¹ * y ^ 2 ^ k * b = b⁻¹ * (b * y ^ 2 ^ k * b⁻¹) * b := by rw [← h1]
          _ = y ^ 2 ^ k := by group
      rw [e]
      exact hzL
    have hcen : (⟨y ^ 2 ^ k, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm' g g.2 _ hz')
    rw [hZ, Subgroup.mem_bot] at hcen
    exact ⟨k, congrArg Subtype.val hcen⟩
  have := isSimpleGroup_of_isComponent hrad hL
  have hgen := closure_not_two_power_eq_top (L := ↥L) (not_isPGroup_two_of_isComponent hL)
  have hsub : {y : ↥L | ¬ ∃ k : ℕ, y ^ 2 ^ k = 1} ⊆
      ((Subgroup.closure (nonTwoConj B ⊤)).comap L.subtype : Set ↥L) := by
    intro y hy
    refine Subgroup.subset_closure (key y y.2 ?_)
    rintro ⟨k, hk⟩
    exact hy ⟨k, Subtype.ext (by simpa using hk)⟩
  have hle : (⊤ : Subgroup ↥L) ≤ (Subgroup.closure (nonTwoConj B ⊤)).comap L.subtype :=
    hgen ▸ (Subgroup.closure_le _).mpr hsub
  intro x hx
  exact hle (Subgroup.mem_top (⟨x, hx⟩ : ↥L))

theorem le_closure_nonTwoConj_of_invGen {Γ : Type*} [Group Γ] {L B : Subgroup Γ} {a : Γ}
    (haB : a ∈ B) (hgen : InvGen L a) : L ≤ Subgroup.closure (nonTwoConj B ⊤) := by
  rw [← show Subgroup.closure (invXi L a) = L from hgen]
  refine (Subgroup.closure_le _).mpr fun x ⟨_, hx⟩ => ?_
  have hx' : x⁻¹ ∈ nonTwoConj B ⊤ := by
    rw [mem_nonTwoConj_top]
    intro hP2
    refine hx (hP2.to_le ?_)
    rw [Subgroup.zpowers_le]
    have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left haB) (Subgroup.mem_sup_right ?_)
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using B.inv_mem haB
  simpa using Subgroup.inv_mem _ (Subgroup.subset_closure hx')

end CFSG.Quasithin.F7Two
