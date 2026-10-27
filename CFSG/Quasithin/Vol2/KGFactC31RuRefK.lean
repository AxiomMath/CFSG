
module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefKBase

public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

section Facts

theorem card_ruC_normalizer64_le :
    Nat.card ↥(ruC ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060)))) ≤ 12288 := by
  set H := ruC ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) with hH
  have hHC : H ≤ ruC := inf_le_left
  set H' := H.subgroupOf ruC
  let f : Fin 20 → ↥ruC ⧸ H' := fun i =>
    QuotientGroup.mk ⟨wG (conj64W.getD i []), conj64W_memC _ (by
      rw [List.getD_eq_getElem _ _ (by rw [conj64W_length]; exact i.2)]
      exact List.getElem_mem _)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hij
    have hn := hij.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hn
    apply conj64_distinct i.2 j.2 hne'
    set ci := wG (conj64W.getD i [])
    set cj := wG (conj64W.getD j [])
    have e : u64.map (MulAut.conj (ci⁻¹ * cj)).toMonoidHom = u64 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
    calc u64.map (MulAut.conj ci).toMonoidHom
        = (u64.map (MulAut.conj (ci⁻¹ * cj)).toMonoidHom).map (MulAut.conj ci).toMonoidHom := by
          rw [e]
      _ = u64.map (MulAut.conj cj).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          refine MonoidHom.ext fun x => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
  have h20 : 20 ≤ H'.index := by
    rw [Subgroup.index]
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hmul := H'.card_mul_index
  rw [card_subgroupOf_of_le hHC, card_ruC] at hmul
  have hpos : 0 < Nat.card H := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : 12289 * 20 ≤ Nat.card H * H'.index := Nat.mul_le_mul hlt h20
  omega

theorem sq_commut_memE {g h : Equiv.Perm (Fin 4060)}
    (hg : g ∈ ruKGens) (hh : h ∈ ruKGens) : g * g ∈ ruESub ∧ g * h * g⁻¹ * h⁻¹ ∈ ruESub := by
  obtain ⟨i, hi, rfl⟩ := mem_ruKGens_iff.mp hg
  obtain ⟨j, hj, rfl⟩ := mem_ruKGens_iff.mp hh
  rw [← uE_eq]
  exact refFacts.ruK_sq_commut i hi j hj

theorem isSpecial2Group_ruK :
    CFSG.Quasithin.IsSpecial2Group 3 8 ↥ruK := by
  set Z := Subgroup.center ↥ruK with hZ
  set s : Set ↥ruK := ((↑) : ↥ruK → Equiv.Perm (Fin 4060)) ⁻¹' {g | g ∈ ruKGens} with hs
  have hscl : Subgroup.closure s = ⊤ := Subgroup.closure_closure_coe_preimage
  have hgen : ∀ a ∈ s, ∀ b ∈ s, a * a ∈ Z ∧ a * b * a⁻¹ * b⁻¹ ∈ Z := by
    intro a ha b hb
    have h := sq_commut_memE ha hb
    exact ⟨(mem_center_ruK_iff _).mpr h.1, (mem_center_ruK_iff _).mpr h.2⟩
  have htop : Subgroup.closure ((QuotientGroup.mk' Z) '' s) = ⊤ := by
    rw [← MonoidHom.map_closure, hscl, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective Z)]
  have hc : ∀ g ∈ (QuotientGroup.mk' Z) '' s, ∀ h ∈ (QuotientGroup.mk' Z) '' s,
      g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := (hgen a ha b hb).2
    rw [← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    simp only [QuotientGroup.mk'_apply]
    calc (a : ↥ruK ⧸ Z) * b = ((a : ↥ruK ⧸ Z) * b * (a : ↥ruK ⧸ Z)⁻¹ * (b : ↥ruK ⧸ Z)⁻¹) *
          (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hsq : ∀ g ∈ (QuotientGroup.mk' Z) '' s, g * g = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := (hgen a ha a ha).1
    rw [← QuotientGroup.eq_one_iff] at h1
    simpa using h1
  have hQcomm : ∀ x y : ↥ruK ⧸ Z, x * y = y * x := fun x y =>
    comm_of_gens' _ hc x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y)
  have hQsq : ∀ x : ↥ruK ⧸ Z, x * x = 1 := fun x =>
    sq_of_gens' _ hc hsq x (htop ▸ Subgroup.mem_top x)
  have hle : commutator ↥ruK ≤ Z := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hQcomm (a : ↥ruK ⧸ Z) b]
    group
  have hk : ∀ a < 8, ruKGens.getD a 1 ∈ ruK := fun a _ => ruKGens_getD_mem a
  have hEle : uE ≤ (commutator ↥ruK).map ruK.subtype := by
    refine refSub_le_of_forall fun i => ?_
    obtain ⟨i, hi⟩ := i
    have key : ∀ a b, a < 8 → b < 8 →
        vE ⟨i, hi⟩ = ruKGens.getD a 1 * ruKGens.getD b 1 * (ruKGens.getD a 1)⁻¹ *
          (ruKGens.getD b 1)⁻¹ →
        vE ⟨i, hi⟩ ∈ (commutator ↥ruK).map ruK.subtype := by
      intro a b ha hb h
      rw [h]
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨_, hk a ha⟩ : ↥ruK))
        (Subgroup.mem_top (⟨_, hk b hb⟩ : ↥ruK))
      rw [commutatorElement_def] at hc
      exact ⟨_, by rw [commutator_def]; exact hc, rfl⟩
    have hv := refFacts.vE_commut
    interval_cases i
    · exact key 3 4 (by norm_num) (by norm_num) hv.1
    · exact key 3 1 (by norm_num) (by norm_num) hv.2.1
    · exact key 4 0 (by norm_num) (by norm_num) hv.2.2
  have hcardZ : Nat.card Z = 8 := card_center_ruK
  have hcomm : commutator ↥ruK = Z := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardZ]
    have h1 := Subgroup.card_le_of_le hEle
    rw [card_refSub hvE, Subgroup.card_map_of_injective ruK.subtype_injective] at h1
    exact le_trans (by norm_num) h1
  refine ⟨by rw [hcardZ]; norm_num, hcomm, isE2_of_card' hQcomm hQsq ?_⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [card_ruK, hcardZ] at h
  rw [show (2 : ℕ) ^ 8 = 256 by norm_num]
  omega

theorem ruN_le_closure : ruN ≤ Subgroup.closure {xE, nE * xE * nE⁻¹} := by
  have hmem : ∀ w, evalSigned [xE, nE * xE * nE⁻¹] w ∈ Subgroup.closure {xE, nE * xE * nE⁻¹} :=
    evalSigned_mem fun g hg => Subgroup.subset_closure (by simpa using hg)
  rw [ruN, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [refFacts.ruNs_words.1]
    exact hmem _
  · rw [refFacts.ruNs_words.2]
    exact hmem _

theorem cQ_memJ :
    cQ ∈ ruJ :=
  refFacts.cQ_memJ

theorem commut_not_mem :
    x32 * cQ * x32⁻¹ * cQ⁻¹ ∉ Subgroup.centralizer (u32 : Set (Equiv.Perm (Fin 4060))) :=
  refFacts.commut_not_mem

theorem exists_conj_r30 {v : Equiv.Perm (Fin 4060)} (hv : v ∈ u32) (h1 : v ≠ 1)
    (hz : v ≠ ruZ) : ∃ c ∈ ruC, c * r30 * c⁻¹ = v :=
  refFacts.exists_conj_r30 v hv h1 hz

end Facts

end CFSG.Quasithin.KGC31.Ru

end
