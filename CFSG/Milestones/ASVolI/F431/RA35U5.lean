module

public import CFSG.Milestones.ASVolI.F431.RA35V
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieE
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocE
public import CFSG.Milestones.ASVolI.F431.AInvSpAll
public import CFSG.Milestones.ASVolI.F431.BCoreU5Chart
public import CFSG.Milestones.ASVolI.F431.RA35Gen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ClassicalGroups.UnitaryFlag

section U5

set_option linter.unusedSectionVars false

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4r_U5_top_nonfused (hyp : HypF_4_31 .U5 f Gp M₁ M₂ β ε z) (hGp : Gp = ⊤) :
    ∃ v : ↥(M₁ ⊓ M₂), (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ v ≠ 1 ∧ v * v = 1 ∧
      ¬ IsConj z (bM β ε v) := by
  classical
  haveI := hyp.amalgam.finite
  obtain ⟨K, fK, h, Ψ, h1, h2⟩ := burnsideF4m_U5_chart hyp.amalgam.toHypF_4_4g
  haveI : CharP K 2 := h.charP
  set ψ : hypPSU h 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Gp.subtype_injective.comp Ψ.injective
  set U := hypProjUnitriangular h 2 1 with hUdef
  set P1 := H13.Sec53F.Unit.u5PtP h with hP1def
  set P2 := H13.Sec53F.Unit.u5LnP h with hP2def
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (P1 ⊓ P2).map ψ := by
    rw [Subgroup.map_inf _ _ _ hψ, ← h1, ← h2, inf_inf_distrib_left]
  have hUP1 : U ≤ P1 := Un.OL5.U_le_u5PtP h
  have hUP2 : U ≤ P2 := Un.U_le_u5LnP
  have hUsyl : IsSylowTwoOf U (P1 ⊓ P2) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right Un.isSylowTwoOf_U_u5LnP (le_inf hUP1 hUP2)
      inf_le_right
  have hUsylB : IsSylowTwoOf (U.map ψ) (Gp ⊓ (M₁ ⊓ M₂)) := by
    rw [hB]
    exact burnsideF4m_isSylowTwoOf_map_inj ψ hψ hUsyl
  obtain ⟨hSyl, -⟩ := burnsideF4j_sylow_data hyp.amalgam
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSsylB : IsSylowTwoOf S (Gp ⊓ (M₁ ⊓ M₂)) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right hSyl hSB inf_le_left
  have hSU : S ≤ U.map ψ := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hUsylB
  have hSeq : U.map ψ = S := burnsideF4j_eq_of_sylow_le hSsylB hUsylB.2.1 hSU hUsylB.1
  set V : Subgroup E := (Un.v5Y h).map ψ with hVdef
  have hVeq : V = ctr (pCoreOf 2 (Gp ⊓ M₂)) := by
    rw [h2, burnsideF4j_pCoreOf_map ψ hψ, burnsideF4j_ctr_map ψ hψ, hVdef,
      Un.v5Y_eq_centerOf_pCoreOf]
    rfl
  have hVS : V ≤ S := by
    rw [← hSeq]
    exact Subgroup.map_mono Un.v5Y_le_U
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, Un.v5Y_comm ha hb]
  have hVsq : ∀ a ∈ V, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have ha2 : a * a = 1 := by
      have := Un.v5Y_sq ha
      rwa [pow_two] at this
    rw [← map_mul, ha2, map_one]
  have hVu : ∀ A : Subgroup E, A ≤ S → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card A = Nat.card V → A = V := by
    intro A hAS hAab hAsq hAcard
    have hArange : A ≤ ψ.range := fun a ha => by
      obtain ⟨u, -, rfl⟩ := (hSeq ▸ hAS ha : a ∈ U.map ψ)
      exact ⟨u, rfl⟩
    set A' := A.comap ψ with hA'def
    have hAA' : A'.map ψ = A := Subgroup.map_comap_eq_self hArange
    have hA'U : A' ≤ U := by
      intro u hu
      obtain ⟨u', hu', he⟩ := (hSeq ▸ hAS hu : ψ u ∈ U.map ψ)
      rw [← hψ he]
      exact hu'
    have hA'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
      intro a ha b hb
      apply hψ
      rw [map_mul, map_mul]
      exact hAab _ ha _ hb
    have hA'sq : ∀ a ∈ A', a ^ 2 = 1 := by
      intro a ha
      apply hψ
      rw [map_pow, sq, map_one]
      exact hAsq _ ha
    have hA'card : Nat.card A' = Nat.card (Un.v5Y h) := by
      have e1 : Nat.card A = Nat.card A' := by
        rw [← hAA', Subgroup.card_map_of_injective hψ]
      have e2 : Nat.card V = Nat.card (Un.v5Y h) := Subgroup.card_map_of_injective hψ
      rw [← e1, hAcard, e2]
    have hA'V := Un.V4_unique_Y hA'U hA'ab hA'sq hA'card
    rw [← hAA', hA'V]
  have hmemB : ∀ {u : hypPSU h 2 1}, u ∈ U → ψ u ∈ M₁ ⊓ M₂ := by
    intro u hu
    have : ψ u ∈ Gp ⊓ (M₁ ⊓ M₂) := hB ▸ ⟨u, ⟨hUP1 hu, hUP2 hu⟩, rfl⟩
    exact this.2
  set w : ↥(M₁ ⊓ M₂) := ⟨ψ (Un.z5Y h), hmemB Un.z5Y_mem_U⟩ with hwdef
  set v : ↥(M₁ ⊓ M₂) := ⟨ψ (Un.t5Y h), hmemB Un.t5Y_mem_U⟩ with hvdef
  have hwV : (w : E) ∈ V := ⟨Un.z5Y h, Un.z5Y_mem_v5Y, rfl⟩
  have hvV : (v : E) ∈ V := ⟨Un.t5Y h, Un.t5Y_mem_v5Y, rfl⟩
  have hvS : (v : E) ∈ S := hVS hvV
  have hwS : (w : E) ∈ S := hVS hwV
  have ht1 : Un.t5Y h ≠ 1 := by
    intro h0
    have := Un.orderOf_t5Y (h := h)
    rw [h0, orderOf_one] at this
    exact absurd this (by decide)
  refine ⟨v, hvS, ?_, ?_, ?_⟩
  · intro h0
    apply ht1
    apply hψ
    rw [map_one]
    exact congrArg Subtype.val h0
  · apply Subtype.ext
    show ψ (Un.t5Y h) * ψ (Un.t5Y h) = 1
    exact hVsq _ hvV
  · intro hcz
    obtain ⟨x, hxZ, hxz, hx1, hx2⟩ := burnsideF4r_zbar hyp (by decide)
    have hwZ : (w : E) ∈ ctr S := by
      refine ⟨hwS, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      obtain ⟨u, hu, rfl⟩ := (hSeq ▸ hs : s ∈ U.map ψ)
      show ψ u * ψ (Un.z5Y h) = ψ (Un.z5Y h) * ψ u
      rw [← map_mul, ← map_mul, Un.L5.z5Y_cent hu]
    have hw1 : w ≠ 1 := by
      intro h0
      have hz1 : Un.z5Y h = 1 := hψ (by rw [map_one]; exact congrArg Subtype.val h0)
      have := Un.orderOf_z5Y (h := h)
      rw [hz1, orderOf_one] at this
      exact absurd this (by decide)
    have hw2 : w * w = 1 := Subtype.ext (hVsq _ hwV)
    have hSGp : ∀ {y : E}, y ∈ S → y ∈ Gp := fun hy => (hSB hy).1
    have hxw := burnsideF4r_conj_of_same_type hyp.amalgam (by decide) (by decide) (by decide)
      (hSGp hxZ.1) (hSGp hwS) (fun h0 => hx1 (Subtype.ext h0)) (congrArg Subtype.val hx2)
      (fun h0 => hw1 (Subtype.ext h0)) (congrArg Subtype.val hw2)
      ⟨fun _ => ⟨1, Gp.one_mem, by rw [one_mul, inv_one, mul_one]; exact hwZ⟩,
        fun _ => ⟨1, Gp.one_mem, by rw [one_mul, inv_one, mul_one]; exact hxZ⟩⟩
    have hfw := burnsideF4j_F_4_35_forward hyp x w hxZ.1 hwS hxw
    rw [hxz] at hfw
    have hwv : IsConj (bM β ε w) (bM β ε v) := hfw.symm.trans hcz
    obtain ⟨m, hm, hmw⟩ := burnsideF4r_conj_M2_of_V hyp (Or.inr rfl) hGp hVeq hVS hVab hVsq
      hVu hwV hvV hwv
    have hmG : m ∈ Gp ⊓ M₂ := ⟨by rw [hGp]; exact Subgroup.mem_top _, hm⟩
    rw [h2] at hmG
    obtain ⟨m', -, rfl⟩ := hmG
    apply Un.noconj_Y (MulAut.conj m')
    apply hψ
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact hmw

end U5

end CFSG.ASVolI
