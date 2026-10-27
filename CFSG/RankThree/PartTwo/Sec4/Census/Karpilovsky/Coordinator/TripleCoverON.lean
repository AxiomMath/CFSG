module

public import CFSG.RankThree.Native.ONTripleCent
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

theorem orderOf_zG_eq_three :
    orderOf zG = 3 := by
  rw [← modelEquiv_zF]
  exact (MulEquiv.orderOf_eq modelEquiv zF).trans orderOf_zF

theorem zG_mem_commutator :
    zG ∈ commutator GM := by
  rw [← comm_x0_x3, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem isPerfect_of_isSimpleGroup_of_not_prime' {B : Type} [Group B] [IsSimpleGroup B]
    (hB : ¬ (Nat.card B).Prime) : Group.IsPerfect B := by
  have hnab : ∃ a b : B, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := hc }
    exact hB (IsSimpleGroup.prime_card (α := B))
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator B) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ commutator B := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h1, Subgroup.mem_bot] at h2
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · exact h1

theorem isPerfect_ON :
    Group.IsPerfect (CFSG.Blueprint.NativeSporadic.Carrier .ONan) := by
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  refine isPerfect_of_isSimpleGroup_of_not_prime' (B := CFSG.Blueprint.NativeSporadic.ON) ?_
  rw [CFSG.Sporadic.ON.card_ON_eq]
  intro h
  have h2 := (Nat.Prime.eq_one_or_self_of_dvd h 2 (by norm_num))
  omega

theorem exists_hom_ON :
    ∃ φ : GM →* CFSG.Blueprint.NativeSporadic.Carrier .ONan,
      Function.Surjective φ ∧ φ.ker = zpowers zG := by
  obtain ⟨e⟩ := nonempty_equiv_PON
  let e' : PON.Group ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan := e.symm
  let f : GM →* PON.Group := piON.comp modelEquiv.symm.toMonoidHom
  have hf : Function.Surjective f := piON_surjective.comp modelEquiv.symm.surjective
  refine ⟨e'.toMonoidHom.comp f, e'.surjective.comp hf, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_piON,
    MulEquiv.coe_toMonoidHom, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← modelEquiv_zF, ← map_zpow, hk, MulEquiv.apply_symm_apply]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← modelEquiv_zF, ← map_zpow, MulEquiv.symm_apply_apply]

theorem isPerfect_GM :
    Group.IsPerfect GM := by
  obtain ⟨φ, hφ, hker⟩ := exists_hom_ON
  have hP := isPerfect_ON
  have hmap : (commutator GM).map φ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
      ← commutator_def]
    exact hP.commutator_eq_top
  have hsup : commutator GM ⊔ φ.ker = ⊤ := by
    have h := Subgroup.comap_map_eq φ (commutator GM)
    rw [hmap, Subgroup.comap_top] at h
    exact h.symm
  have hle : φ.ker ≤ commutator GM := by
    rw [hker, zpowers_le]
    exact zG_mem_commutator
  refine ⟨?_⟩
  rw [← hsup]
  exact (sup_eq_left.2 hle).symm

theorem three_dvd_card_hopfMultiplier_ON :
    3 ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) := by
  obtain ⟨φ, hφ, hker⟩ := exists_hom_ON
  have hcard : Nat.card φ.ker = 3 := by
    rw [hker, Nat.card_zpowers, orderOf_zG_eq_three]
  have hcen : φ.ker ≤ Subgroup.center GM := by
    rw [hker, zpowers_le, Subgroup.mem_center_iff]
    intro g
    exact (zG_central g).symm
  have h := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier (isPerfect_GM) φ hφ hcen
  rwa [hcard] at h

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
