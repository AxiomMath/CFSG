module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAltTenGoursat
import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eight70_equiv_alt5_prod {p : ℕ} {H X : Subgroup G} (hXH : X ≤ H) (hX : ⁅X, X⁆ = X)
    (h5 : 2 ≤ CFSG.Open.pRank 5 X)
    (hXK : X ⊓ (CFSG.pPrimeCore p ↥H).map H.subtype = ⊥)
    (f : ↥((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) →*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) (hf : Function.Injective f) :
    Nonempty (↥X ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  let Xbar : Subgroup (↥H ⧸ (CFSG.pPrimeCore p ↥H)) :=
    (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
  let φ : ↥X →* ↥Xbar :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hXH)).codRestrict Xbar
      (fun x => ⟨Subgroup.inclusion hXH x, x.2, rfl⟩)
  let g : ↥X →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) := f.comp φ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have hπeq : ((Subgroup.inclusion hXH x : ↥H) :
        ↥H ⧸ (CFSG.pPrimeCore p ↥H)) =
        ((Subgroup.inclusion hXH y : ↥H) : ↥H ⧸ (CFSG.pPrimeCore p ↥H)) :=
      congrArg Subtype.val hxy
    have h1 : ((Subgroup.inclusion hXH x * (Subgroup.inclusion hXH y)⁻¹ : ↥H) :
        ↥H ⧸ (CFSG.pPrimeCore p ↥H)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπeq, mul_inv_cancel]
    have hKmem : Subgroup.inclusion hXH x * (Subgroup.inclusion hXH y)⁻¹ ∈
        CFSG.pPrimeCore p ↥H := (QuotientGroup.eq_one_iff _).mp h1
    have hXmem : x.val * y.val⁻¹ ∈ X := X.mul_mem x.2 (X.inv_mem y.2)
    have hKmap : x.val * y.val⁻¹ ∈ (CFSG.pPrimeCore p ↥H).map H.subtype := by
      refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXH x * (Subgroup.inclusion hXH y)⁻¹,
        hKmem, ?_⟩
      simp
    have hbot : x.val * y.val⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hXK]
      exact ⟨hXmem, hKmap⟩
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
  have hg : Function.Injective g := hf.comp hφinj
  let U : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := g.range
  have hUtop : (⊤ : Subgroup ↥X).map g = U := Subgroup.map_top g
  have hpU : CFSG.Open.pRank 5 U = CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) := by
    rw [← hUtop]
    exact CFSG.LocalAnalysis.GLTheoremA.T123C.pRank_map_eq hg 5 ⊤
  have hpX : CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 5 X := by
    have h := CFSG.LocalAnalysis.GLTheoremA.T123C.pRank_map_eq (f := X.subtype)
      X.subtype_injective 5 ⊤
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have hperf : ⁅U, U⁆ = U := by
    have htop : ⁅(⊤ : Subgroup ↥X), ⊤⁆ = ⊤ :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.top_iff.mpr (Subgroup.isPerfect_iff.mpr hX))
    rw [← hUtop, ← Subgroup.map_commutator, htop]
  have h5U : 2 ≤ CFSG.Open.pRank 5 U := by
    rw [hpU, hpX]
    exact h5
  have hUt : U = ⊤ := eq_top_of_perfect_of_two_le_pRank_five U hperf h5U
  have hgsurj : Function.Surjective g := MonoidHom.range_eq_top.mp hUt
  exact ⟨MulEquiv.ofBijective g ⟨hg, hgsurj⟩⟩

theorem eight70_split {X : Subgroup G}
    (hX : Nonempty (↥X ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    ∃ X₁ X₂ : Subgroup G, X₁ ≤ X ∧ X₂ ≤ X ∧ X₁ ⊔ X₂ = X ∧ X₁ ⊓ X₂ = ⊥ ∧
      Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)) ∧ Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)) ∧
      (∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) ∧ 2 ≤ CFSG.Open.pRank 3 X := by
  obtain ⟨e⟩ := hX
  let inlR : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).range
  let inrR : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).range
  let X₁ : Subgroup G := (inlR.map e.symm.toMonoidHom).map X.subtype
  let X₂ : Subgroup G := (inrR.map e.symm.toMonoidHom).map X.subtype
  have hX₁X : X₁ ≤ X := Subgroup.map_subtype_le _
  have hX₂X : X₂ ≤ X := Subgroup.map_subtype_le _
  have hinl : Function.Injective
      (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) := by
    intro a b h
    simpa using congrArg Prod.fst h
  have hsupR : inlR ⊔ inrR = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h1 : (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) a ∈ inlR :=
      ⟨a, rfl⟩
    have h2 : (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) b ∈ inrR :=
      ⟨b, rfl⟩
    have h : (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) a *
        (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) b = (a, b) := by
      ext <;> simp [MonoidHom.inl_apply, MonoidHom.inr_apply]
    rw [← h]
    exact Subgroup.mul_mem_sup h1 h2
  have hinfR : inlR ⊓ inrR = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨u, v⟩ h
    change (u, v) ∈ (MonoidHom.inl (alternatingGroup (Fin 5))
        (alternatingGroup (Fin 5))).range ⊓
      (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).range at h
    rw [Subgroup.mem_inf, MonoidHom.mem_range, MonoidHom.mem_range] at h
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := h
    rw [MonoidHom.inl_apply] at hc
    rw [MonoidHom.inr_apply] at hd
    rw [Subgroup.mem_bot]
    ext <;> simp_all
  have hsup : X₁ ⊔ X₂ = X := by
    change ((inlR.map e.symm.toMonoidHom).map X.subtype) ⊔
      ((inrR.map e.symm.toMonoidHom).map X.subtype) = X
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, hsupR,
      Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hinf : X₁ ⊓ X₂ = ⊥ := by
    change ((inlR.map e.symm.toMonoidHom).map X.subtype) ⊓
      ((inrR.map e.symm.toMonoidHom).map X.subtype) = ⊥
    rw [← Subgroup.map_inf_eq (inlR.map e.symm.toMonoidHom)
        (inrR.map e.symm.toMonoidHom) X.subtype X.subtype_injective,
      ← Subgroup.map_inf_eq inlR inrR e.symm.toMonoidHom e.symm.injective, hinfR,
      Subgroup.map_bot, Subgroup.map_bot]
  have hX₁equiv : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)) := by
    have hA1 : alternatingGroup (Fin 5) ≃* ↥X₁ :=
      (MonoidHom.ofInjective (f := MonoidHom.inl (alternatingGroup (Fin 5))
        (alternatingGroup (Fin 5))) hinl).trans
        ((Subgroup.equivMapOfInjective inlR e.symm.toMonoidHom e.symm.injective).trans
          (Subgroup.equivMapOfInjective (inlR.map e.symm.toMonoidHom) X.subtype
            X.subtype_injective))
    exact ⟨hA1.symm⟩
  have hX₂equiv : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)) := by
    have hinr : Function.Injective
        (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) := by
      intro a b h
      simpa using congrArg Prod.snd h
    have hA2 : alternatingGroup (Fin 5) ≃* ↥X₂ :=
      (MonoidHom.ofInjective (f := MonoidHom.inr (alternatingGroup (Fin 5))
        (alternatingGroup (Fin 5))) hinr).trans
        ((Subgroup.equivMapOfInjective inrR e.symm.toMonoidHom e.symm.injective).trans
          (Subgroup.equivMapOfInjective (inrR.map e.symm.toMonoidHom) X.subtype
            X.subtype_injective))
    exact ⟨hA2.symm⟩
  have hX₁card : Nat.card ↥X₁ = 60 := by
    rw [Nat.card_congr hX₁equiv.some.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hX₂card : Nat.card ↥X₂ = 60 := by
    rw [Nat.card_congr hX₂equiv.some.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := by
    intro x hx y hy
    have hxX : x ∈ X := hX₁X hx
    have hyX : y ∈ X := hX₂X hy
    have hx2 : (e ⟨x, hxX⟩).2 = 1 := by
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      have harg : (⟨X.subtype (e.symm.toMonoidHom w), hxX⟩ : ↥X) = e.symm w := rfl
      rw [harg, MulEquiv.apply_symm_apply]
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hw
      simp [MonoidHom.inl_apply]
    have hy1 : (e ⟨y, hyX⟩).1 = 1 := by
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      have harg : (⟨X.subtype (e.symm.toMonoidHom w), hyX⟩ : ↥X) = e.symm w := rfl
      rw [harg, MulEquiv.apply_symm_apply]
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hw
      simp [MonoidHom.inr_apply]
    have hprod : e ⟨x, hxX⟩ * e ⟨y, hyX⟩ = e ⟨y, hyX⟩ * e ⟨x, hxX⟩ := by
      ext <;> simp [hx2, hy1]
    have h := congrArg e.symm hprod
    simp only [map_mul, MulEquiv.symm_apply_apply] at h
    exact Subtype.ext_iff.mp h
  have h3X : 2 ≤ CFSG.Open.pRank 3 X := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P₁, hP₁card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X₁) 3 (n := 1) (by
      rw [hX₁card]; norm_num)
    obtain ⟨P₂, hP₂card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X₂) 3 (n := 1) (by
      rw [hX₂card]; norm_num)
    let A₁ : Subgroup G := P₁.map X₁.subtype
    let A₂ : Subgroup G := P₂.map X₂.subtype
    have hA₁X₁ : A₁ ≤ X₁ := Subgroup.map_subtype_le P₁
    have hA₂X₂ : A₂ ≤ X₂ := Subgroup.map_subtype_le P₂
    have hA₁card : Nat.card A₁ = 3 := by
      rw [Subgroup.card_map_of_injective X₁.subtype_injective, hP₁card, pow_one]
    have hA₂card : Nat.card A₂ = 3 := by
      rw [Subgroup.card_map_of_injective X₂.subtype_injective, hP₂card, pow_one]
    have hAinf : A₁ ⊓ A₂ = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact inf_le_inf hA₁X₁ hA₂X₂
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.two_le_pRank Nat.prime_three hA₁card
      hA₂card (fun a ha b hb => hcomm a (hA₁X₁ ha) b (hA₂X₂ hb)) hAinf
      (hA₁X₁.trans hX₁X) (hA₂X₂.trans hX₂X)
  exact ⟨X₁, X₂, hX₁X, hX₂X, hsup, hinf, hX₁equiv, hX₂equiv, hcomm, h3X⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
