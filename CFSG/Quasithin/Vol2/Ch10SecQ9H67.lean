module

public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.Quasithin.EmptyFaithful.A38c14HatM22

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  CFSG.Quasithin.A38c14
open scoped commutatorElement
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace M22Block

abbrev Agrp : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ p5Gens}).subgroupOf Mgrp

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem isQuasisimple_Mgrp :
    CFSG.IsQuasisimple ↥Mgrp := by
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have : IsSimpleGroup ↥Mgrp := (MulEquiv.subgroupCongr mGens_closure).isSimpleGroup
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  let _ : CommGroup ↥Mgrp := { (inferInstance : Group ↥Mgrp) with mul_comm := h }
  have hp := IsSimpleGroup.prime_card (α := ↥Mgrp)
  rw [card_Mgrp] at hp
  norm_num at hp

theorem card_eq {Y : Type} [Group Y] {B : Subgroup Y}
    (h1 : IsElemAbelianOfRank 2 4 ↥(CFSG.pCore 2 ↥B)) (h2 : IsAlt 5 (ModO2 B)) :
    Nat.card ↥B = 960 := by
  obtain ⟨e⟩ := h2
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), Nat.card_congr e.toEquiv,
    card_alt5, card_of_isE2 h1]
  norm_num

theorem eq_or_card (hq : CFSG.IsQuasisimple ↥Mgrp)
    {B : Subgroup ↥Mgrp} (hB : B ∈ lFamily Ugrp) (hBtop : B ≠ ⊤) :
    B = Agrp ∨ Nat.card ↥B = 5760 := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hB' : B ∈ cComp (B ⊔ Ugrp) := hB
  have hPne : B ⊔ Ugrp ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hPns : ¬ Group.IsSolvable ↥(B ⊔ Ugrp) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ Ugrp))
        (Subgroup.inclusion_injective _))
  obtain ⟨j, hj, hLM, hPL, hcardj⟩ :=
    cert.overgroup_cases_idx (rawIsEnc 22) hck (B ⊔ Ugrp) le_sup_right
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [hlen] at hj
  have hM : Nat.card Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  interval_cases j
  ·
    have h128 : cert.sizes.getD 0 0 = 128 := rfl
    rw [h128] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 0) (by rw [hcardj]; norm_num)
  ·
    have h384 : cert.sizes.getD 1 0 = 384 := rfl
    rw [h384] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 1) (by rw [hcardj]; norm_num)
  ·
    have h1920 : cert.sizes.getD 2 0 = 1920 := rfl
    rw [h1920] at hcardj
    have ha := List.all_eq_true.mp incl5 2 (by simp)
    simp only [h1920, bne_self_eq_false, Bool.false_or] at ha
    have hlen2 : 2 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[2] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen2
    have hAL : Subgroup.closure {g | g ∈ p5Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen2] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext5
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]}⁆ ≤
          Subgroup.closure {g | g ∈ p5Gens} :=
      commutator_le_of_card_eq_two_mul hAL (by rw [hcardj, hAcard])
    have hperf : ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ =
        Subgroup.closure {g | g ∈ p5Gens} := perfect_of_perfOK (rawIsEnc 22) perf5_ok
    have hsimple := Seven.alt5_simple
    have hext := isExt_of_perfectCore_ext (M := Mgrp) hB hAL hLM hcomm hperf hPL
      Seven.alt5_nonabelian V hVc hVsq hVcard e
    have hBc : Nat.card ↥B = 960 := by
      have := card_of_isExt_alt card_alt5 hext
      omega
    have hAM : Subgroup.closure {g | g ∈ p5Gens} ≤ Mgrp := hAL.trans hLM
    have hle : B ≤ Agrp := by
      have h1 : B ≤ perfectCore (B ⊔ Ugrp) :=
        le_perfectCore_of_perfect le_sup_left (perfect_of_mem_cComp hB')
      rwa [hPL, perfectCore_subgroupOf_eq hAL hLM hcomm hperf] at h1
    left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hBc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hAcard]
  ·
    have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
    rw [h5760] at hcardj
    have ha := List.all_eq_true.mp incl6 3 (by simp)
    simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
    have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
    have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen3] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext6
    have hLA := Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, hAcard])
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]}⁆ ≤
          Subgroup.closure {g | g ∈ l6Gens} := by
      rw [← hLA]
      exact commutator_self_le _
    have hperf : ⁅Subgroup.closure {g | g ∈ l6Gens}, Subgroup.closure {g | g ∈ l6Gens}⁆ =
        Subgroup.closure {g | g ∈ l6Gens} := perfect_of_perfOK (rawIsEnc 22) perf6_ok
    have hsimple := Seven.alt6_simple
    have hext := isExt_of_perfectCore_ext (M := Mgrp) hB hAL hLM hcomm hperf hPL
      Seven.alt6_nonabelian V hVc hVsq hVcard e
    right
    have := card_of_isExt_alt card_alt6 hext
    omega
  ·
    have h443520 : cert.sizes.getD 4 0 = 443520 := rfl
    rw [h443520] at hcardj
    exfalso
    apply hPne
    have heq := Subgroup.eq_of_le_of_card_ge hLM (by rw [hM]; exact hcardj.symm.le)
    rw [hPL]
    exact (congrArg (fun K => K.subgroupOf Mgrp) heq).trans (Subgroup.subgroupOf_self Mgrp)
  ·
    have h384 : cert.sizes.getD 5 0 = 384 := rfl
    rw [h384] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 1) (by rw [hcardj]; norm_num)

theorem commutatorElement_mul_center {X : Type} [Group X] (a b : X) {z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w)) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * ((b * w) * z) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by rw [← hz' (b * w)]
    _ = a * b * (w * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * w) * (w⁻¹ * b⁻¹) := by rw [← hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_commutator_comap {X Z : Type} [Group X] [Group Z] (π : X →* Z)
    (hker : π.ker ≤ Subgroup.center X) {B : Subgroup X} (hB : ⁅B, B⁆ = B) :
    B = ⁅(B.map π).comap π, (B.map π).comap π⁆ := by
  refine le_antisymm ?_ ?_
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ _ := Subgroup.commutator_mono (Subgroup.le_comap_map π B) (Subgroup.le_comap_map π B)
  · rw [Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    obtain ⟨b₁, hb₁, he₁⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hh₁)
    obtain ⟨b₂, hb₂, he₂⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hh₂)
    have hz₁ : b₁⁻¹ * h₁ ∈ Subgroup.center X :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, he₁, inv_mul_cancel])
    have hz₂ : b₂⁻¹ * h₂ ∈ Subgroup.center X :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, he₂, inv_mul_cancel])
    have e₁ : h₁ = b₁ * (b₁⁻¹ * h₁) := by group
    have e₂ : h₂ = b₂ * (b₂⁻¹ * h₂) := by group
    rw [e₁, e₂, commutatorElement_mul_center b₁ b₂ hz₁ hz₂, ← hB]
    exact Subgroup.commutator_mem_commutator hb₁ hb₂

end M22Block

theorem kgMathieuNatBlock_holds :
    KGMathieuNatBlock := by
  intro Y _ _ hY T hT B₁ hB₁ B₂ hB₂ hnat
  have hqM := M22Block.isQuasisimple_Mgrp
  obtain ⟨π, hπ, hker⟩ : ∃ π : Y →* ↥Mgrp, Function.Surjective π ∧
      π.ker ≤ Subgroup.center Y := by
    rcases hY with hY | ⟨-, -, ⟨e⟩⟩
    · obtain ⟨e⟩ : Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := hY
      let e1 : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
      let e' : Y ≃* ↥Mgrp := e1.trans (MulEquiv.subgroupCongr mGens_closure.symm)
      refine ⟨e'.toMonoidHom, e'.surjective, fun x hx => ?_⟩
      have h1 : x = 1 := e'.injective ((MonoidHom.mem_ker.mp hx).trans (map_one e').symm)
      rw [h1]
      exact Subgroup.one_mem _
    · let e1 : Y ⧸ Subgroup.center Y ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
      let e2 : Y ⧸ Subgroup.center Y ≃* ↥Mgrp :=
        e1.trans (MulEquiv.subgroupCongr mGens_closure.symm)
      refine ⟨e2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)),
        e2.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
      have h1 : e2 (QuotientGroup.mk x) = 1 := hx
      rwa [e2.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  have hTb : IsSylowTwoOf (T.map π) ⊤ := A312.isSylowTwoOf_top_map π hπ hT
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hTb isSylowTwoOf_Ugrp
  have key : ∀ B ∈ lFamily T, Nat.card ↥B = 960 →
      (B.map π).map (MulAut.conj g).toMonoidHom = M22Block.Agrp := by
    intro B hB hBc
    have h1 := map_mem_lFamily π hker hB
    have h2 : (B.map π).map (MulAut.conj g).toMonoidHom ∈ lFamily Ugrp := by
      have := cComp_map_mulEquiv (MulAut.conj g)
        (show B.map π ∈ cComp (B.map π ⊔ T.map π) from h1)
      rw [Subgroup.map_sup, hg] at this
      exact this
    have hle : Nat.card ↥((B.map π).map (MulAut.conj g).toMonoidHom) ≤ 960 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, ← hBc]
      exact Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective B)
    have hne : (B.map π).map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
      intro h
      rw [h, Subgroup.card_top, card_Mgrp] at hle
      omega
    rcases M22Block.eq_or_card hqM h2 hne with h | h
    · exact h
    · omega
  have hc₁ := M22Block.card_eq (hnat B₁ (Or.inl rfl)).1 (hnat B₁ (Or.inl rfl)).2.1
  have hc₂ := M22Block.card_eq (hnat B₂ (Or.inr rfl)).1 (hnat B₂ (Or.inr rfl)).2.1
  have heq : B₁.map π = B₂.map π :=
    Subgroup.map_injective (MulAut.conj g).injective
      ((key B₁ hB₁ hc₁).trans (key B₂ hB₂ hc₂).symm)
  calc B₁ = ⁅(B₁.map π).comap π, (B₁.map π).comap π⁆ :=
        M22Block.eq_commutator_comap π hker
          (perfect_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ T) from hB₁))
    _ = ⁅(B₂.map π).comap π, (B₂.map π).comap π⁆ := by rw [heq]
    _ = B₂ := (M22Block.eq_commutator_comap π hker
          (perfect_of_mem_cComp (show B₂ ∈ cComp (B₂ ⊔ T) from hB₂))).symm

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
