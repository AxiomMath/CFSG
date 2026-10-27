module

public import CFSG.RankThree.GF2n.Stroth78.Sec4Three

import CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid
import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec3Six
import CFSG.RankThree.GF2n.Stroth78.Sec4FiveStepA
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Perm
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Struct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions Equiv Equiv.Perm
open CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem rhoZ_commutator_Xsub_eq_one_s6 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1)
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (hΨ : ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap)
    (hΨα : Ψ (alphaInX S h hα₀) = swap 0 1) :
    ∀ x ∈ commutator ↥(Xsub S a), rhoZ S (x : Hbar z) = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0c, hx0⟩ := hcon
  have hR2 : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two S h h217 h3
  let ρ : ↥(Xsub S a) →* MulAut ↥(ZQ z) := (rhoZ S).comp (Xsub S a).subtype
  have hρ : ∀ x : ↥(Xsub S a), ρ x = rhoZ S (x : Hbar z) := fun x => rfl
  let d : ↥(Xsub S a) := alphaInX S h hα₀
  have hP := pair_Xsub S h h217 h3
  have hdD : d ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀ hα₀1)
  have hself : ∀ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), x * x = 1 := by
    intro x hx
    have h1 := pow_orderOf_eq_one x
    rw [hP.2.2.1 x hx, pow_two] at h1
    exact h1
  have hclass : ∀ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)),
      ∃ g : ↥(Xsub S a), x = g * d * g⁻¹ := by
    intro x hx
    obtain ⟨e, he⟩ := hP.2.1
    have hde : d ∈ {x | IsConj e x} := he ▸ hdD
    have hxe : x ∈ {x | IsConj e x} := he ▸ hx
    obtain ⟨c, hc⟩ := isConj_iff.mp ((IsConj.symm hde).trans hxe)
    exact ⟨c, hc.symm⟩
  have hx0ρ : ρ x0 ≠ 1 := by rw [hρ]; exact hx0
  have hne1 : ∀ e ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), ρ e ≠ 1 := by
    intro e he he1
    obtain ⟨g1, hg1⟩ := hclass e he
    have hρd : ρ d = 1 := by
      have h1 : ρ g1 * ρ d * (ρ g1)⁻¹ = 1 := by rw [← map_inv, ← map_mul, ← map_mul, ← hg1, he1]
      have h2 : ρ g1 * ρ d = ρ g1 * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h1
      exact mul_left_cancel h2
    have hDker : ∀ y ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), ρ y = 1 := by
      intro y hy
      obtain ⟨g, rfl⟩ := hclass y hy
      rw [map_mul, map_mul, hρd, mul_one, map_inv, mul_inv_cancel]
    have hker : Subgroup.closure (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) ≤ ρ.ker :=
      (Subgroup.closure_le _).mpr fun y hy => hDker y hy
    rw [hP.2.2.2.2] at hker
    exact hx0ρ (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x0)))
  have hsignX : ∀ x ∈ commutator ↥(Xsub S a), Ψ x ∈ alternatingGroup (Fin 6) := by
    intro x hx
    have h1 : (Perm.sign.comp Ψ.toMonoidHom) x = 1 :=
      MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker (Perm.sign.comp Ψ.toMonoidHom) hx)
    exact mem_alternatingGroup.mpr h1
  have hinj : Set.InjOn ρ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := by
    intro e he e' he' hee'
    by_contra hne
    have hmem : e * e' ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, ← hee', ← map_mul, hself e he, map_one]
    have hΨe := (hΨ e).mp he
    have hΨe' := (hΨ e').mp he'
    have hee'1 : e * e' ≠ 1 := by
      intro h1
      apply hne
      have h2 : e' = e⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, inv_eq_of_mul_eq_one_left (hself e he)]
    have hA : Ψ (e * e') ∈ alternatingGroup (Fin 6) := by
      rw [map_mul]
      exact mul_mem_alternatingGroup_of_isSwap hΨe hΨe'
    have hKn : ((ρ.ker).map Ψ.toMonoidHom).Normal :=
      Subgroup.Normal.map (MonoidHom.normal_ker ρ) _ Ψ.surjective
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI hN : (((ρ.ker).map Ψ.toMonoidHom).subgroupOf (alternatingGroup (Fin 6))).Normal :=
      hKn.subgroupOf _
    rcases Subgroup.Normal.eq_bot_or_eq_top
      (((ρ.ker).map Ψ.toMonoidHom).subgroupOf (alternatingGroup (Fin 6))) with hb | ht
    · have hmemN : (⟨Ψ (e * e'), hA⟩ : alternatingGroup (Fin 6)) ∈
          ((ρ.ker).map Ψ.toMonoidHom).subgroupOf (alternatingGroup (Fin 6)) :=
        Subgroup.mem_subgroupOf.mpr ⟨e * e', hmem, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmemN
      exact hee'1 (Ψ.injective (by simpa using congrArg Subtype.val hmemN))
    · have hmemN : (⟨Ψ x0, hsignX x0 hx0c⟩ : alternatingGroup (Fin 6)) ∈
          ((ρ.ker).map Ψ.toMonoidHom).subgroupOf (alternatingGroup (Fin 6)) := by
        rw [ht]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_subgroupOf.mp hmemN
      have : k = x0 := Ψ.injective hkx
      exact hx0ρ (this ▸ MonoidHom.mem_ker.mp hk)
  have hsep : ∀ e ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)),
      ∀ e' ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), e ≠ e' →
        ∃ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), x * e ≠ e * x ∧ x * e' = e' * x := by
    intro e he e' he' hne
    obtain ⟨y, hy, h1, h2⟩ := exists_swap_separating ((hΨ e).mp he) ((hΨ e').mp he')
      (fun h' => hne (Ψ.injective h'))
    refine ⟨Ψ.symm y, (hΨ _).mpr (by simpa using hy), fun hc => h1 ?_, ?_⟩
    · have h4 := congrArg Ψ hc
      simpa [map_mul] using h4
    · apply Ψ.injective
      simpa [map_mul] using h2
  obtain ⟨c₀, hc₀⟩ := rhoZ_diff_eq_or S h hR2.le hα₀
  have hρd : ρ d = rhoZ S α₀ := rfl
  have htv : ∀ e ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), ∃ c : ↥(ZQ z), ∀ u,
      ρ e u = u ∨ ρ e u = u * c := by
    intro e he
    obtain ⟨g, rfl⟩ := hclass e he
    refine ⟨ρ g c₀, ?_⟩
    rw [map_mul, map_mul, map_inv, hρd]
    exact tv_conj hc₀
  choose! C hC using htv
  have hCinj : Set.InjOn C (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    center_injOn (ZQ_mul_self S) ρ hself hP.2.2.2.1 C hC hne1 hinj hsep
  have hR : ∀ r ∈ Rbar S a, (∀ u : ↥(ZQ z), rhoZ S r u = u) → r = 1 :=
    forall_Rbar_eq_one_of_rhoZ_Xsub S h h217 ⟨(x0 : Hbar z), x0.2, hx0⟩
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod_s6 S Ψ hΨ
  have hcomm6 : ∀ i j : Fin 6, 2 ≤ i.val → 2 ≤ j.val →
      swap i j * swap 0 1 = swap 0 1 * swap i j := by
    decide +kernel
  have key : ∀ l ∈ Lbar S a, (ψ l).1 = 1 ∨ (ψ l).1 = d := by
    intro l hl
    have hl_eq : l = ((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z) := by
      have h1 := hψ (ψ l)
      rwa [MulEquiv.symm_apply_apply] at h1
    have hconj : ∀ y : ↥(Xsub S a),
        l * (y : Hbar z) * l⁻¹ = ((ψ l).1 : Hbar z) * y * ((ψ l).1 : Hbar z)⁻¹ := by
      intro y
      have hc : ((ψ l).2 : Hbar z) * y = y * ((ψ l).2 : Hbar z) :=
        (Subgroup.mem_centralizer_iff.mp (ψ l).2.2 y y.2).symm
      have hcy : ((ψ l).2 : Hbar z) * y * ((ψ l).2 : Hbar z)⁻¹ = y := by rw [hc]; group
      calc l * (y : Hbar z) * l⁻¹
          = (((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z)) * y *
              (((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z))⁻¹ := by rw [← hl_eq]
        _ = ((ψ l).1 : Hbar z) * (((ψ l).2 : Hbar z) * y * ((ψ l).2 : Hbar z)⁻¹) *
              ((ψ l).1 : Hbar z)⁻¹ := by group
        _ = ((ψ l).1 : Hbar z) * y * ((ψ l).1 : Hbar z)⁻¹ := by rw [hcy]
    have hlα : l * α₀ = α₀ * l :=
      (Subgroup.mem_centralizer_iff.mp (Lbar_le_centralizer_alphaInX S h hα₀ hl) α₀
        (Set.mem_singleton _)).symm
    have hπd : ((ψ l).1 : Hbar z) * α₀ = α₀ * ((ψ l).1 : Hbar z) := by
      have hcα : ((ψ l).2 : Hbar z) * α₀ = α₀ * ((ψ l).2 : Hbar z) :=
        (Subgroup.mem_centralizer_iff.mp (ψ l).2.2 d d.2).symm
      refine mul_right_cancel (b := ((ψ l).2 : Hbar z)) ?_
      calc ((ψ l).1 : Hbar z) * α₀ * ((ψ l).2 : Hbar z)
          = ((ψ l).1 : Hbar z) * (α₀ * ((ψ l).2 : Hbar z)) := by group
        _ = ((ψ l).1 : Hbar z) * (((ψ l).2 : Hbar z) * α₀) := by rw [hcα]
        _ = (((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z)) * α₀ := by group
        _ = l * α₀ := by rw [← hl_eq]
        _ = α₀ * l := hlα
        _ = α₀ * (((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z)) := by rw [← hl_eq]
        _ = α₀ * ((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z) := by group
    have h01 : Ψ (ψ l).1 * swap 0 1 = swap 0 1 * Ψ (ψ l).1 := by
      rw [← hΨα, ← map_mul, ← map_mul]
      exact congrArg Ψ (Subtype.ext hπd)
    have hx : ∀ i j : Fin 6, 2 ≤ i.val → 2 ≤ j.val → i ≠ j →
        Ψ (ψ l).1 * swap i j = swap i j * Ψ (ψ l).1 := by
      intro i j hi hj hij
      let e : ↥(Xsub S a) := Ψ.symm (swap i j)
      have hΨe : Ψ e = swap i j := Ψ.apply_symm_apply _
      have heD : e ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
        (hΨ e).mpr (by rw [hΨe]; exact ⟨i, j, hij, rfl⟩)
      have hed : e * d = d * e := by
        apply Ψ.injective
        rw [map_mul, map_mul, hΨα, hΨe]
        exact hcomm6 i j hi hj
      have hσ : ∀ u, ρ d u = u → rhoZ S l u = u := by
        intro u hu
        refine rhoZ_Lbar_eq_self_of_forall_Rbar S h hR (fun r hr => ?_) hl
        rcases Sec4Five.eq_one_or_eq_of_mem_Rbar S hR2 hα₀ hα₀1 hr with rfl | rfl
        · rw [map_one]; rfl
        · exact hu
      have hfix := eq_self_of_equivariant (ZQ_mul_self S) ρ C hC hne1 hCinj (rhoZ S l)
        (fun y => MulAut.conjNormal l y)
        (fun y hy => by
          have h1 := Eset_conj_mem S a (hy : (y : Hbar z) ∈ Eset S a) l
          show ((MulAut.conjNormal l y : ↥(Xsub S a)) : Hbar z) ∈ Eset S a
          rw [MulAut.conjNormal_apply]
          exact h1)
        (fun y hy => by
          show rhoZ S ((MulAut.conjNormal l y : ↥(Xsub S a)) : Hbar z) = _
          rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
          rfl) hdD hσ e heD hed
      have h1 : l * (e : Hbar z) * l⁻¹ = (e : Hbar z) := by
        have := congrArg Subtype.val hfix
        rwa [MulAut.conjNormal_apply] at this
      rw [hconj e] at h1
      have h2 : (ψ l).1 * e * ((ψ l).1)⁻¹ = e := by
        apply Subtype.ext
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
      have h3 := congrArg Ψ h2
      rw [map_mul, map_mul, map_inv, hΨe] at h3
      calc Ψ (ψ l).1 * swap i j = (Ψ (ψ l).1 * swap i j * (Ψ (ψ l).1)⁻¹) * Ψ (ψ l).1 := by group
        _ = swap i j * Ψ (ψ l).1 := by rw [h3]
    rcases eq_one_or_eq_swap_of_commute (Ψ (ψ l).1) hx h01 with h1 | h1
    · left; exact Ψ.injective (by rw [h1, map_one])
    · right; exact Ψ.injective (by rw [h1, hΨα])
  obtain ⟨k, hk, hkle⟩ := card_Lbar_eq_mul_card_map S ψ hψ
  have h2 := card_inf_centralizer_le_two S h h217
  have hmap : Nat.card ↥((Lbar S a).map ((MonoidHom.fst _ _).comp ψ.toMonoidHom)) ≤ 2 := by
    have hsub : (((Lbar S a).map ((MonoidHom.fst _ _).comp ψ.toMonoidHom) :
        Subgroup ↥(Xsub S a)) : Set ↥(Xsub S a)) ⊆ ({1, d} : Set ↥(Xsub S a)) := by
      rintro _ ⟨l, hl, rfl⟩
      rcases key l hl with h1 | h1
      · left; exact h1
      · right; exact h1
    have hle1 : Nat.card ↥((Lbar S a).map ((MonoidHom.fst _ _).comp ψ.toMonoidHom)) ≤
        Nat.card ↥({1, d} : Set ↥(Xsub S a)) :=
      Nat.card_mono (Set.toFinite _) hsub
    have hle2 : Nat.card ↥({1, d} : Set ↥(Xsub S a)) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc ({1, d} : Set ↥(Xsub S a)).ncard ≤ ({d} : Set ↥(Xsub S a)).ncard + 1 :=
            Set.ncard_insert_le _ _
        _ = 1 + 1 := by rw [Set.ncard_singleton]
        _ = 2 := rfl
    exact hle1.trans hle2
  refine false_of_card_Lbar_le_four S h ?_
  rw [hk]
  exact (Nat.mul_le_mul (hkle.trans h2) hmap).trans (by norm_num)

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
