module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Sec5
public import CFSG.CGT.PushingUpLit.A78.OppSL2
public import CFSG.CGT.PushingUpLit.A78.BenderTI

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS
open CFSG.CGT.PushingUpLit.A78
open scoped MatrixGroups

variable {G : Type} [Group G] {A B : Subgroup G}

private theorem isElemAbRankOne_utri_ltri (F : Type) [Field F] [CharP F 2] :
    IsElemAbRankOne (utri F) (ltri F) := by
  have h := isElemAbRankOne_upper_lower F
  rwa [← CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent,
    ← CFSG.RankThree.GF2n.Tim81.Sec2.ltri_eq_lowerUnipotent] at h

private theorem opposite_utri_ltri (F : Type) [Field F] [CharP F 2] :
    Opposite (utri F) (ltri F) := by
  have h := isElemAbRankOne_utri_ltri F
  exact ⟨h.ne, h.moufang, h.moufang'⟩

private theorem map_symm_map_eq_subgroupOf {F : Type} [Field F]
    (φ : ↥(A ⊔ B) ≃* SL(2, F)) {C : Subgroup G} {U : Subgroup (SL(2, F))}
    (hC : (C.subgroupOf (A ⊔ B)).map φ.toMonoidHom = U) :
    U.map φ.symm.toMonoidHom = C.subgroupOf (A ⊔ B) := by
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  rw [map_symm_map_mulEquiv, hC]

theorem IsL2Gen.opposite (h : IsL2Gen A B) : Opposite A B := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  have hA' : (utri F).map φ.symm.toMonoidHom = A.subgroupOf (A ⊔ B) :=
    map_symm_map_eq_subgroupOf φ hA
  have hB' : (ltri F).map φ.symm.toMonoidHom = B.subgroupOf (A ⊔ B) :=
    map_symm_map_eq_subgroupOf φ hB
  have hH : Opposite (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) := by
    have hUL := opposite_utri_ltri F
    have hmap := opposite_map_of_injective (Y := SL(2, F)) (G := ↥(A ⊔ B))
      φ.symm.toMonoidHom φ.symm.injective hUL
    rwa [hA', hB'] at hmap
  have hmap := opposite_map_of_injective (Y := ↥(A ⊔ B)) (G := G)
    (A ⊔ B).subtype (A ⊔ B).subtype_injective hH
  rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le le_sup_right] at hmap

theorem IsL2Gen.ne (h : IsL2Gen A B) : A ≠ B := h.opposite.1

theorem IsL2Gen.inf_eq_bot (h : IsL2Gen A B) : A ⊓ B = ⊥ := h.opposite.inf_eq_bot

theorem IsL2Gen.isElemAbelian (h : IsL2Gen A B) : IsElemAbelian 2 A := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  rw [← Subgroup.map_subgroupOf_eq_of_le (le_sup_left : A ≤ A ⊔ B),
    ← map_symm_map_eq_subgroupOf φ hA]
  exact ((isElemAbelian_utri (F := F)).map φ.symm.toMonoidHom).map (A ⊔ B).subtype

private theorem IsL2Gen.ne_bot (h : IsL2Gen A B) : A ≠ ⊥ := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hCharP
  have hA' : (utri F).map φ.symm.toMonoidHom = A.subgroupOf (A ⊔ B) :=
    map_symm_map_eq_subgroupOf φ hA
  intro hbot
  have hmem : φ.symm (utriElt (1 : F)) ∈ A.subgroupOf (A ⊔ B) := by
    rw [← hA']
    exact Subgroup.mem_map_of_mem φ.symm.toMonoidHom (utriElt_mem_utri 1)
  have hmem' : φ.symm (utriElt (1 : F)) ∈ (⊥ : Subgroup ↥(A ⊔ B)) := by
    simpa [hbot] using hmem
  have h1 : φ.symm (utriElt (1 : F)) = 1 := Subgroup.mem_bot.mp hmem'
  have h2 : utriElt (1 : F) = 1 := by
    rw [← φ.apply_symm_apply (utriElt (1 : F)), h1, map_one]
  exact utriElt_ne_one one_ne_zero h2

theorem IsL2Gen.not_commuting (h : IsL2Gen A B) : ¬ Commuting A B :=
  h.opposite.not_commuting h.ne_bot

theorem IsL2Gen.commutator_ne_bot (h : IsL2Gen A B) : ⁅A, B⁆ ≠ ⊥ := by
  intro hbot
  exact h.not_commuting (commuting_iff_commutator_eq_bot.mpr hbot)

private theorem IsL2Gen.commutator_eq_bot_of_commuting (h : IsL2Gen A B)
    (hc : Commuting ⁅A, B⁆ (A ⊔ B)) : ⁅A, B⁆ = ⊥ := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  let H : Subgroup G := A ⊔ B
  have hCle : ⁅A, B⁆ ≤ H := Subgroup.commutator_le_of_le le_sup_left le_sup_right
  have hcenter : (⁅A, B⁆).subgroupOf H ≤ Subgroup.center H := by
    intro c hcC
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hc c (Subgroup.mem_subgroupOf.mp hcC) x x.2).eq.symm
  have hmaple : ((⁅A, B⁆).subgroupOf H).map φ.toMonoidHom ≤
      (Subgroup.center H).map φ.toMonoidHom := Subgroup.map_mono hcenter
  have hcenter_map : (Subgroup.center H).map φ.toMonoidHom = Subgroup.center (SL(2, F)) :=
    Subgroup.map_center_eq φ
  rw [hcenter_map, CFSG.Timmesfeld.RankOne.center_SL2_eq_bot] at hmaple
  have hsub : (⁅A, B⁆).subgroupOf H = ⊥ := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [le_bot_iff.mp hmaple, Subgroup.map_bot]
  rw [← Subgroup.map_subgroupOf_eq_of_le hCle, hsub, Subgroup.map_bot]

theorem IsL2Gen.not_special (h : IsL2Gen A B) (R : Set (Subgroup G)) :
    ¬ Special R A B := by
  intro hsp
  exact h.not_commuting (commuting_iff_commutator_eq_bot.mpr
    (h.commutator_eq_bot_of_commuting (hsp.2.1.sup_right hsp.2.2)))

theorem IsL2Gen.exists_conj (h : IsL2Gen A B) :
    ∃ x ∈ A ⊔ B, B = conjSubgroup x A := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  let H : Subgroup G := A ⊔ B
  let xH : H := φ.symm (wElt : SL(2, F))
  have hWH : conjSubgroup xH (A.subgroupOf H) = B.subgroupOf H := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [map_conjSubgroup, hA, hB]
    simpa [xH] using conjSubgroup_wElt_utri
  refine ⟨(xH : G), xH.2, ?_⟩
  have hmap := congrArg (Subgroup.map H.subtype) hWH
  rw [map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le le_sup_right] at hmap
  exact hmap.symm

theorem IsL2Gen.card_eq (h : IsL2Gen A B) : Nat.card B = Nat.card A := by
  obtain ⟨x, -, rfl⟩ := h.exists_conj
  exact Subgroup.card_map_of_injective (MulAut.conj x).injective

private theorem exists_join_equiv_map {X Y : Type*} [Group X] [Group Y]
    {A B : Subgroup X} (f : X →* Y) (hf : Function.Injective f) :
    ∃ g : ↥(A ⊔ B) ≃* ↥(A.map f ⊔ B.map f),
      (A.subgroupOf (A ⊔ B)).map g.toMonoidHom =
        (A.map f).subgroupOf (A.map f ⊔ B.map f) ∧
      (B.subgroupOf (A ⊔ B)).map g.toMonoidHom =
        (B.map f).subgroupOf (A.map f ⊔ B.map f) := by
  let e := Subgroup.equivMapOfInjective (A ⊔ B) f hf
  let g : ↥(A ⊔ B) ≃* ↥(A.map f ⊔ B.map f) :=
    e.trans (MulEquiv.subgroupCongr (Subgroup.map_sup A B f))
  have hAg : (A.subgroupOf (A ⊔ B)).map g.toMonoidHom =
      (A.map f).subgroupOf (A.map f ⊔ B.map f) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subtype.ext_iff, g, e,
      MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply]
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩,
      fun ⟨a, ha, hay⟩ => ⟨⟨a, Subgroup.mem_sup_left ha⟩, ha, hay⟩⟩
  have hBg : (B.subgroupOf (A ⊔ B)).map g.toMonoidHom =
      (B.map f).subgroupOf (A.map f ⊔ B.map f) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subtype.ext_iff, g, e,
      MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply]
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩,
      fun ⟨b, hb, hby⟩ => ⟨⟨b, Subgroup.mem_sup_right hb⟩, hb, hby⟩⟩
  exact ⟨g, hAg, hBg⟩

private theorem IsL2Gen.map_of_injective {G' : Type} [Group G'] (h : IsL2Gen A B)
    (e : G →* G') (he : Function.Injective e) : IsL2Gen (A.map e) (B.map e) := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  obtain ⟨g, hAg, hBg⟩ := exists_join_equiv_map (A := A) (B := B) e he
  have hcomp : g.symm.toMonoidHom.comp g.toMonoidHom = MonoidHom.id ↥(A ⊔ B) := by
    ext x
    simp
  have hAsymm : ((A.map e).subgroupOf (A.map e ⊔ B.map e)).map g.symm.toMonoidHom =
      A.subgroupOf (A ⊔ B) := by
    rw [← hAg, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hBsymm : ((B.map e).subgroupOf (A.map e ⊔ B.map e)).map g.symm.toMonoidHom =
      B.subgroupOf (A ⊔ B) := by
    rw [← hBg, Subgroup.map_map, hcomp, Subgroup.map_id]
  let eH : ↥(A ⊔ B) →* G' := e.comp (A ⊔ B).subtype
  have heH : Function.Injective eH := he.comp (A ⊔ B).subtype_injective
  have hAmap : (A.subgroupOf (A ⊔ B)).map eH = A.map e := by
    rw [show eH = e.comp (A ⊔ B).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  have hcardA : Nat.card F = Nat.card (A.map e) := by
    rw [hcard, ← hAmap, Subgroup.card_map_of_injective (f := eH) heH,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv]
  let φ' : ↥(A.map e ⊔ B.map e) ≃* SL(2, F) := g.symm.trans φ
  refine ⟨F, hField, hFin, hCharP, φ', hcardA, ?_, ?_⟩
  · rw [show φ'.toMonoidHom = φ.toMonoidHom.comp g.symm.toMonoidHom from rfl,
      ← Subgroup.map_map, hAsymm, hA]
  · rw [show φ'.toMonoidHom = φ.toMonoidHom.comp g.symm.toMonoidHom from rfl,
      ← Subgroup.map_map, hBsymm, hB]

theorem IsL2Gen.conj (h : IsL2Gen A B) (g : G) :
    IsL2Gen (conjSubgroup g A) (conjSubgroup g B) := by
  change IsL2Gen (A.map (MulAut.conj g).toMonoidHom)
    (B.map (MulAut.conj g).toMonoidHom)
  exact h.map_of_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

private theorem IsL2Gen.comap_of_injective {G' : Type} [Group G'] {X : Type} [Group X]
    {A B : Subgroup X} (f : X →* G') (hf : Function.Injective f)
    (h : IsL2Gen (A.map f) (B.map f)) : IsL2Gen A B := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  obtain ⟨g, hAg, hBg⟩ := exists_join_equiv_map (A := A) (B := B) f hf
  let φ' : ↥(A ⊔ B) ≃* SL(2, F) := g.trans φ
  refine ⟨F, hField, hFin, hCharP, φ', ?_, ?_, ?_⟩
  · rw [hcard, Subgroup.card_map_of_injective (f := f) hf]
  · rw [show φ'.toMonoidHom = φ.toMonoidHom.comp g.toMonoidHom from rfl,
      ← Subgroup.map_map, hAg, hA]
  · rw [show φ'.toMonoidHom = φ.toMonoidHom.comp g.toMonoidHom from rfl,
      ← Subgroup.map_map, hBg, hB]

theorem IsL2Gen.subgroupOf (h : IsL2Gen A B) {K : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) :
    IsL2Gen (A.subgroupOf K) (B.subgroupOf K) := by
  have h' : IsL2Gen ((A.subgroupOf K).map K.subtype) ((B.subgroupOf K).map K.subtype) := by
    rw [Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB]
    exact h
  exact h'.comap_of_injective K.subtype K.subtype_injective

theorem IsL2Gen.map {G' : Type} [Group G'] (h : IsL2Gen A B) (e : G →* G')
    (he : (A ⊔ B) ⊓ e.ker = ⊥) : IsL2Gen (A.map e) (B.map e) := by
  let H : Subgroup G := A ⊔ B
  let eH : H →* G' := e.comp H.subtype
  have heH : Function.Injective eH := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hker : eH.ker = e.ker.subgroupOf H := rfl
    rw [hker, Subgroup.subgroupOf_eq_bot]
    rw [disjoint_iff, inf_comm]
    exact he
  have hH : IsL2Gen (A.subgroupOf H) (B.subgroupOf H) :=
    h.subgroupOf le_sup_left le_sup_right
  have h' := hH.map_of_injective eH heH
  have hAe : (A.subgroupOf H).map eH = A.map e := by
    rw [show eH = e.comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  have hBe : (B.subgroupOf H).map eH = B.map e := by
    rw [show eH = e.comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  rwa [hAe, hBe] at h'

theorem IsL2Gen.isSimpleGroup (h : IsL2Gen A B) (h4 : 4 ≤ Nat.card A) :
    IsSimpleGroup ↥(A ⊔ B) := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  have h4' : 4 ≤ Nat.card F := by
    rw [hcard]
    exact h4
  haveI : IsSimpleGroup (SL(2, F)) := isSimpleGroup_SL2_charTwo F h4'
  exact φ.isSimpleGroup

theorem IsL2Gen.ker_inf_eq_bot {G' : Type} [Group G'] (h : IsL2Gen A B)
    (h4 : 4 ≤ Nat.card A) (e : G →* G') (hA : ¬ A ≤ e.ker) :
    (A ⊔ B) ⊓ e.ker = ⊥ := by
  let H : Subgroup G := A ⊔ B
  let f : H →* G' := e.comp H.subtype
  haveI : IsSimpleGroup H := h.isSimpleGroup h4
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
    · exact hbot
    · exfalso
      apply hA
      intro a ha
      have haH : a ∈ H := Subgroup.mem_sup_left ha
      have hmem : (⟨a, haH⟩ : H) ∈ f.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      simpa [f] using MonoidHom.mem_ker.mp hmem
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxH, hxker⟩ := Subgroup.mem_inf.mp hx
  have hmem : (⟨x, hxH⟩ : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    simpa [f] using MonoidHom.mem_ker.mp hxker
  rw [hker, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

end CFSG.RankThree.GF2n.Tim81
