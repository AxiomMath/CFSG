module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtNat
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtUI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open scoped IsMulCommutative

namespace Lem1227Lt

namespace Ten

@[expose] def wedgeStab : Subgroup G5 where
  carrier := {g | wedgeRep g e01 = e01}
  one_mem' := by
    show wedgeRep 1 e01 = e01
    rw [map_one]
    rfl
  mul_mem' {a b} ha hb := by
    have ha' : wedgeRep a e01 = e01 := ha
    have hb' : wedgeRep b e01 = e01 := hb
    show wedgeRep (a * b) e01 = e01
    rw [← act_act wedgeRep a b e01, hb', ha']
  inv_mem' {a} ha := by
    have ha' : wedgeRep a e01 = e01 := ha
    show wedgeRep a⁻¹ e01 = e01
    calc wedgeRep a⁻¹ e01 = wedgeRep a⁻¹ (wedgeRep a e01) := by rw [ha']
      _ = wedgeRep (a⁻¹ * a) e01 := act_act wedgeRep _ _ _
      _ = e01 := by
        rw [inv_mul_cancel, map_one]
        rfl

theorem mem_wedgeStab {g : G5} : g ∈ wedgeStab ↔ wedgeRep g e01 = e01 := Iff.rfl

theorem unitriangular_le_wedgeStab : unitriangular 5 (ZMod 2) ≤ wedgeStab := by
  intro u hu
  refine e01_mem_fixU u ?_
  rw [mem_Ugrp]
  intro a b
  refine ⟨fun hab => hu.1 a b hab, fun hab => ?_⟩
  subst hab
  exact hu.2 a

theorem wedgeStab_eq : wedgeStab = stabilizer (flagSpace 5 (ZMod 2) 2) := by
  have hK : Nat.card (ZMod 2) = 2 := SL.card_zmod_two
  have hU : upperTriangular 5 (ZMod 2) ≤ wedgeStab :=
    (upperTriangular_le_unitriangular hK).trans unitriangular_le_wedgeStab
  obtain ⟨hQ, -⟩ := borel_overgroups wedgeStab hU
  have hcuts : borelOvergroupCuts wedgeStab = {2} := by
    ext c
    simp only [borelOvergroupCuts, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi, hin, hnot⟩
      by_contra hc2
      apply hnot
      have : c = 1 ∨ c = 3 ∨ c = 4 := by omega
      show wedgeRep (reflection 5 (ZMod 2) c hi hin) e01 = e01
      rw [wedgeRep_apply', coe_reflection]
      rcases this with rfl | rfl | rfl <;> decide +kernel
    · rintro rfl
      refine ⟨by norm_num, by norm_num, fun h => ?_⟩
      have h' : wedgeRep (reflection 5 (ZMod 2) 2 (by norm_num) (by norm_num)) e01 = e01 := h
      rw [wedgeRep_apply', coe_reflection] at h'
      revert h'
      decide +kernel
  rw [hQ, hcuts, flagStabilizer_singleton]

theorem exists_mulEquiv_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : ∀ a, f a = 1 ↔ g a = 1) : ∃ γ : B ≃* C, ∀ a, γ (f a) = g a := by
  have hk : f.ker = g.ker := by
    ext a
    exact hker a
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)), fun a => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) =
      (QuotientGroup.mk a : A ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MulEquiv.trans_apply, h1]
  rfl

theorem exists_conj_sylow {X : Type*} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp₁, hi₁⟩ := isSylowTwoOf_top_iff'.mp h₁
  obtain ⟨hp₂, hi₂⟩ := isSylowTwoOf_top_iff'.mp h₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hp₁.toSylow hi₁) (hp₂.toSylow hi₂)
  exact ⟨g, (congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg)⟩

theorem wedgeRep_inv_apply (g : G5) (x : Fin 10 → ZMod 2) : wedgeRep g⁻¹ (wedgeRep g x) = x := by
  rw [act_act, inv_mul_cancel, map_one]
  rfl

theorem wedgeRep_apply_inv (g : G5) (x : Fin 10 → ZMod 2) : wedgeRep g (wedgeRep g⁻¹ x) = x := by
  rw [act_act, mul_inv_cancel, map_one]
  rfl

theorem adjust_coords {V' : Type*} [CommGroup V'] {H' : Subgroup (MulAut V')}
    (e₁ : V' ≃ (Fin 10 → ZMod 2)) (γ₁ : ↥H' ≃* G5) (he1 : e₁ 1 = 0)
    (hγ₁ : ∀ (h : ↥H') (v : V'), e₁ ((h : MulAut V') v) = wedgeRep (γ₁ h) (e₁ v)) (g₀ : G5) :
    ∃ e : V' ≃ (Fin 10 → ZMod 2), e 1 = 0 ∧
      ∀ (h : ↥H') (v : V'), e ((h : MulAut V') v) =
        wedgeRep ((γ₁.trans (MulAut.conj g₀)) h) (e v) := by
  refine ⟨⟨fun v => wedgeRep g₀ (e₁ v), fun w => e₁.symm (wedgeRep g₀⁻¹ w), fun v => ?_,
    fun w => ?_⟩, ?_, fun h v => ?_⟩
  · simp only [wedgeRep_inv_apply, Equiv.symm_apply_apply]
  · simp only [Equiv.apply_symm_apply, wedgeRep_apply_inv]
  · show wedgeRep g₀ (e₁ 1) = 0
    rw [he1, map_zero]
  · show wedgeRep g₀ (e₁ ((h : MulAut V') v)) = _
    rw [hγ₁, act_act]
    show wedgeRep (g₀ * γ₁ h) (e₁ v) = wedgeRep (g₀ * γ₁ h * g₀⁻¹) (wedgeRep g₀ (e₁ v))
    rw [act_act, inv_mul_cancel_right]

section Main

variable {G : Type} [Group G] [Finite G] {T K Y H M₀ V : Subgroup G}

theorem false_of_ten
    [IsMulCommutative ↥V]
    (h1223 : Hyp1223 G T Y V) (h : LtHyp G T K Y) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (hfam : B69.E22Fam ↥(E2.star M₀ H K))
    (e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* G5) (hcard : Nat.card ↥V = 2 ^ 10)
    (hirrU : IsIrreducibleUnder Y V) : False := by
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := h1223.irrPlus.2.2.1
  have hsimple : IsSimpleGroup G5 := isSimpleGroup_sl_zmodTwo (n := 5) (by norm_num)
  have hnonab : ∃ a b : G5, a * b ≠ b * a :=
    sl_nonabelian_of_card_two SL.card_zmod_two (by norm_num)
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    Lem8.center_eq_bot_of_mulEquiv e (center_eq_bot_of_simple hnonab)
  let ρ' : ↥Y →* ↥(autOn Y V) := (A4.actionOn V Y hYV).codRestrict (autOn Y V)
    (fun y => (A4.mem_autOn_iff hYV).2 ⟨y, rfl⟩)
  have hρs : Function.Surjective ρ' := by
    rintro ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := (A4.mem_autOn_iff hYV).1 ha
    exact ⟨y, rfl⟩
  have hρ1 : ∀ y : ↥Y, ρ' y = 1 ↔ y ∈ CFSG.pCore 2 ↥Y := by
    intro y
    constructor
    · intro hy
      exact ker_actionOn_le_pCore h1223 hYV e y (congrArg Subtype.val hy)
    · intro hy
      exact Subtype.ext (actionOn_eq_one_of_mem_pCore h1223 hYV hy)
  obtain ⟨γ₀, -⟩ := exists_mulEquiv_of_ker_eq ρ' (e.toMonoidHom.comp (piY Y)) hρs
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun y => by
      rw [hρ1]
      show y ∈ CFSG.pCore 2 ↥Y ↔ e (QuotientGroup.mk y) = 1
      rw [MulEquiv.map_eq_one_iff]
      exact (QuotientGroup.eq_one_iff y).symm)
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    have := (Vol2.Ch11.SecA.reducedAggregate_props (Y ⊔ T)).1 (v : G) (h1223.irrPlus.1 v.2)
    simpa using this)
  have hirr : ∀ J : Subgroup ↥V, (∀ g ∈ autOn Y V, ∀ w ∈ J, (g : MulAut ↥V) w ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    rcases hirrU.2 (J.map V.subtype) (Subgroup.map_subtype_le J)
      (le_normalizer_map_of_invariant hYV hJ) with h1 | h1
    · left
      rw [eq_bot_iff]
      intro w hw
      have hw' : (w : G) ∈ J.map V.subtype := ⟨w, hw, rfl⟩
      rw [h1, Subgroup.mem_bot] at hw'
      exact Subgroup.mem_bot.2 (Subtype.ext hw')
    · right
      rw [eq_top_iff]
      intro w _
      have hw' : (w : G) ∈ J.map V.subtype := by rw [h1]; exact w.2
      obtain ⟨w', hw', hww'⟩ := hw'
      rw [← Subtype.ext hww']
      exact hw'
  obtain ⟨e₁, γ₁, he₁1, hγ₁⟩ := Orbit.exists_wedge_coords hV2 hcard γ₀ hirr
  let φ₂ : ↥Y →* G5 := γ₁.toMonoidHom.comp ρ'
  have hφ₂s : Function.Surjective φ₂ := γ₁.surjective.comp hρs
  obtain ⟨g₀, hg₀⟩ := exists_conj_sylow (isSylow_imgS h φ₂ hφ₂s)
    (SL.isSylowTwoOf_unitriangular (by norm_num : 1 ≤ 5))
  obtain ⟨e', he'1, hγ'⟩ := adjust_coords e₁ γ₁ he₁1 hγ₁ g₀
  let γ : ↥(autOn Y V) ≃* G5 := γ₁.trans (MulAut.conj g₀)
  let φ : ↥Y →* G5 := γ.toMonoidHom.comp ρ'
  have hφs : Function.Surjective φ := γ.surjective.comp hρs
  have hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    intro y
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← hρ1]
    show γ (ρ' y) = 1 ↔ ρ' y = 1
    exact MulEquiv.map_eq_one_iff γ
  have hS : imgS T Y φ = unitriangular 5 (ZMod 2) := by
    rw [← hg₀]
    simp only [imgS, Subgroup.map_map]
    rfl
  obtain ⟨m, hm, -, Θ, hΘ⟩ := sl_data h (by norm_num : 4 ≤ 5) (le_refl 5) φ hk hS
  refine false_of_sl_model h hKH hHK hmin hker hq hlist hfam φ hφs hk hm Θ hΘ ?_
  intro t α hα _
  set v₀ : ↥V := e'.symm e01 with hv₀
  have hev₀ : e' v₀ = e01 := e'.apply_symm_apply _
  have hF1 : ∀ (y : ↥Y) (v : ↥V), e' (A4.actionOn V Y hYV y v) = wedgeRep (φ y) (e' v) :=
    fun y v => hγ' (ρ' y) v
  have hF2 : ∀ y : ↥Y, φ y ∈ wedgeStab ↔ A4.actionOn V Y hYV y v₀ = v₀ := by
    intro y
    rw [mem_wedgeStab]
    have h1 : wedgeRep (φ y) e01 = e' (A4.actionOn V Y hYV y v₀) := by rw [hF1, hev₀]
    rw [h1]
    constructor
    · intro h2
      apply e'.injective
      rw [h2, hev₀]
    · intro h2
      rw [h2, hev₀]
  have hTU : ∀ y : ↥Y, (y : G) ∈ T → φ y ∈ unitriangular 5 (ZMod 2) := by
    intro y hy
    rw [← hS]
    exact ⟨y, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hy, y.2⟩), rfl⟩
  have hUT : ∀ u ∈ unitriangular 5 (ZMod 2), ∃ y : ↥Y, (y : G) ∈ T ∧ φ y = u := by
    intro u hu
    rw [← hS] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    exact ⟨y, (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1, rfl⟩
  set ct : MulAut ↥V := A4.actionOn V T hTV t with hct
  have hctv : ct v₀ = v₀ := by
    have hfix : e' (ct v₀) ∈ fixU wedgeRep := by
      intro u hu
      have hu' : u ∈ unitriangular 5 (ZMod 2) := by
        have hu1 := mem_Ugrp.1 hu
        exact ⟨fun i j hij => (hu1 i j).1 hij, fun i => (hu1 i i).2 rfl⟩
      obtain ⟨y₁, hy₁T, rfl⟩ := hUT u hu'
      rw [← hF1]
      congr 1
      have hy₂T : ((conjY h t⁻¹ y₁ : ↥Y) : G) ∈ T := by
        rw [coe_conjY]
        exact T.mul_mem (T.mul_mem (t⁻¹ : ↥T).2 hy₁T) (T.inv_mem (t⁻¹ : ↥T).2)
      have h2 : A4.actionOn V Y hYV (conjY h t⁻¹ y₁) v₀ = v₀ :=
        (hF2 _).1 (unitriangular_le_wedgeStab (hTU _ hy₂T))
      rw [actionOn_conjY h hYV hTV t⁻¹ y₁, map_inv] at h2
      simp only [MulAut.mul_apply, MulAut.inv_def] at h2
      exact (MulEquiv.symm_apply_eq ct).1 h2
    rcases wedge_fix hfix with h0 | h1
    · exfalso
      have h3 : ct v₀ = 1 := e'.injective (h0.trans he'1.symm)
      have h4 : v₀ = 1 := ct.injective (h3.trans (map_one ct).symm)
      apply e01_ne
      rw [← hev₀, h4, he'1]
    · exact e'.injective (h1.trans hev₀.symm)
  have hαstab : ∀ g : G5, g ∈ wedgeStab ↔ α g ∈ wedgeStab := by
    intro g
    obtain ⟨y, rfl⟩ := hφs g
    rw [hα, hF2, hF2, actionOn_conjY h hYV hTV t y]
    simp only [MulAut.mul_apply, MulAut.inv_def]
    have hctinv : ct.symm v₀ = v₀ := (MulEquiv.symm_apply_eq ct).2 hctv.symm
    rw [hctinv]
    constructor
    · intro h2
      rw [h2, hctv]
    · intro h2
      exact ct.injective (h2.trans hctv.symm)
  have hstab : (stabilizer (flagSpace 5 (ZMod 2) 2)).map α.toMonoidHom =
      stabilizer (flagSpace 5 (ZMod 2) 2) := by
    rw [← wedgeStab_eq]
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hαstab g).1 hg
    · intro hz
      obtain ⟨g, rfl⟩ := α.surjective z
      exact ⟨g, (hαstab g).2 hz, rfl⟩
  exact SL.inner_of_stabilizer (by norm_num) (by norm_num) (by norm_num) (by norm_num) α hstab

end Main

end Ten

end Lem1227Lt

end CFSG.Quasithin.H13
