module

public import CFSG.Sporadic.SuzRecog.C1ModelT0

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.C1Model

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

@[expose] noncomputable def e3x : Equiv.Perm (Fin 1782) := wPerm C1ModelData.e3Word

@[expose] noncomputable def e3 : Equiv.Perm (Fin 1782) := e3x * wPerm [1] * e3x⁻¹

@[expose] noncomputable def centE3 : Subgroup (Equiv.Perm (Fin 1782)) := centralizer {e3} ⊓ invE 1

@[expose] noncomputable def ce3Gen (i : ℕ) : Equiv.Perm (Fin 1782) :=
  decPerm (C1ModelData.ce3Decs.getD i ([], 0))

@[expose] noncomputable def CT0 : Subgroup (Equiv.Perm (Fin 1782)) :=
  centralizer (T0 : Set (Equiv.Perm (Fin 1782))) ⊓ invE 1

@[expose] noncomputable def C0 : Subgroup (Equiv.Perm (Fin 1782)) := centralizer {Model.w0} ⊓ CT0

@[expose] noncomputable def A40 : Subgroup (Equiv.Perm (Fin 1782)) :=
  centralizer (J0 : Set (Equiv.Perm (Fin 1782))) ⊓ suzM

section Cent

theorem cent_parts : (∀ i < 2, comp 1782 ce3Tabs[i]! e3T = comp 1782 e3T ce3Tabs[i]!) ∧
    enumOK 1782 ct0Gens ct0Enum = true ∧ ct0Enum.tabs.size = 192 ∧
    (∀ i < 3, commT0 ct0Gens[i]! = true) ∧ invsOK 1782 cosTabs cosInvs = true ∧
    (∀ a < 48, ∀ b < a, ∃ i < 4, cosKey a i ≠ cosKey b i) ∧
    a4Tabs.size = 12 ∧ yTabs.size = 24 ∧ c0Tabs.size = 16 ∧
    (∀ i < 16, comp 1782 c0Tabs[i]! r1T = comp 1782 r1T c0Tabs[i]!) ∧
    enumOK 1782 #[w0T, rhoT] a4Enum = true ∧ a4Enum.tabs.size = 12 := by
  have h := c1Cent_check
  unfold centCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨fun i hi => beq_iff_eq.mp (allBelow_eq_true.mp h1 i hi), h2, beq_iff_eq.mp h3,
    fun i hi => allBelow_eq_true.mp h4 i hi, h5, fun a ha b hb => ?_, beq_iff_eq.mp h7,
    beq_iff_eq.mp h8, beq_iff_eq.mp h9, fun i hi => beq_iff_eq.mp (allBelow_eq_true.mp h10 i hi),
    h11, beq_iff_eq.mp h12⟩
  have hk := allBelow_eq_true.mp (allBelow_eq_true.mp h6 a ha) b hb
  rw [Bool.not_eq_true'] at hk
  by_contra hne
  push Not at hne
  have : allBelow 4 (fun i => cosKey a i == cosKey b i) = true :=
    allBelow_eq_true.mpr fun i hi => beq_iff_eq.mpr (hne i hi)
  rw [this] at hk
  exact Bool.noConfusion hk

theorem cent_a4Tabs : a4Tabs.size = 12 := cent_parts.2.2.2.2.2.2.1

theorem cent_c0Tabs : c0Tabs.size = 16 := cent_parts.2.2.2.2.2.2.2.2.1

theorem cent_c0r1 : ∀ i < 16, comp 1782 c0Tabs[i]! r1T = comp 1782 r1T c0Tabs[i]! :=
  cent_parts.2.2.2.2.2.2.2.2.2.1

theorem cent_a4Enum : enumOK 1782 #[w0T, rhoT] a4Enum = true :=
  cent_parts.2.2.2.2.2.2.2.2.2.2.1

theorem cent_a4Size : a4Enum.tabs.size = 12 := cent_parts.2.2.2.2.2.2.2.2.2.2.2

theorem e3x_mem_invE : e3x ∈ invE 1 := wPerm_mem (by decide)

theorem tabRep_e3x : TabRep e3xT e3x := tabRep_cWord (by decide)

theorem tabRep_e3xI : TabRep e3xI e3x⁻¹ :=
  tabRep_e3x.inv t0_parts.2.2.2.2.1 t0_parts.2.2.2.2.2.1

theorem tabRep_e3 : TabRep e3T e3 :=
  tabRep_e3x.conjTab (tabRep_cWord (by decide)) tabRep_e3xI

theorem e3_mem_T0 : e3 ∈ T0 := by
  obtain ⟨g, hg, hrep⟩ := enumerates_T0.sound _ (mem_of_found t0_parts.2.2.2.2.2.2)
  rwa [tabRep_e3.perm_eq hrep]

theorem card_centE3 : Nat.card centE3 = 9216 := by
  have h := LocalR.card_centralizer_lambda (i := 2) (by norm_num)
  have e : LocalR.lambdaSizes[2]! = 360 := rfl
  rw [e] at h
  rw [centE3, e3, card_centralizer_inf_conj (invE 1) e3x_mem_invE, inf_comm,
    show wPerm [1] = ((LocalR.lambdaElt 2 : ↥(invE 1)) : Equiv.Perm (Fin 1782)) from rfl,
    ← LocalR.card_centralizer_coe]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h.trans (by norm_num))

theorem ce3Decs_ok {i : ℕ} (hi : i < 2) : (∀ k ∈ (C1ModelData.ce3Decs.getD i ([], 0)).1, k < 10) ∧
    (C1ModelData.ce3Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem tabRep_ce3Tab {i : ℕ} (hi : i < 2) : TabRep (ce3Tab i) (ce3Gen i) :=
  tabRep_decTab (ce3Decs_ok hi).1 (ce3Decs_ok hi).2

theorem ce3Tabs_get {i : ℕ} (hi : i < 2) : ce3Tabs[i]! = ce3Tab i := getElem!_ofFn' _ hi

theorem ce3Gen_mem_centE3 {i : ℕ} (hi : i < 2) : ce3Gen i ∈ centE3 := by
  have h := cent_parts.1 i hi
  rw [ce3Tabs_get hi] at h
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    ((((tabRep_ce3Tab hi).comp tabRep_e3).eq_iff (tabRep_e3.comp (tabRep_ce3Tab hi))).mp h),
    decPerm_mem (ce3Decs_ok hi).1⟩

theorem commT0_iff {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    commT0 t = true ↔ g ∈ centralizer {x | ∃ i < 4, t0Gen i = x} := by
  rw [commT0, allBelow_eq_true, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨i, hi, rfl⟩
    have hT := tabRep_t0Tab hi
    have := h i hi
    rw [t0Tabs_get hi] at this
    exact (((ht.comp hT).beq_iff (hT.comp ht)).mp this).symm
  · intro h i hi
    have hT := tabRep_t0Tab hi
    rw [t0Tabs_get hi]
    exact ((ht.comp hT).beq_iff (hT.comp ht)).mpr (h _ ⟨i, hi, rfl⟩).symm

theorem centralizer_T0_eq :
    centralizer (T0 : Set (Equiv.Perm (Fin 1782))) = centralizer {x | ∃ i < 4, t0Gen i = x} := by
  rw [T0_eq, centralizer_closure]

theorem CT0_le_centE3 : CT0 ≤ centE3 := fun _ hg =>
  mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (mem_inf.mp hg).1 e3 e3_mem_T0).symm, (mem_inf.mp hg).2⟩

theorem CT0_le_invE : CT0 ≤ invE 1 := inf_le_right

theorem rep_ce3 : ∀ k < ce3Tabs.size, Rep 1782 ce3Tabs[k]! (ce3Gen k) := by
  intro k hk
  have hk' : k < 2 := by simpa [ce3Tabs] using hk
  rw [ce3Tabs_get hk']
  exact (tabRep_ce3Tab hk').2

theorem word_mem_centE3 {w : List ℕ} (hw : ∀ k ∈ w, k < 2) : (w.map ce3Gen).prod ∈ centE3 :=
  list_prod_mem fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact ce3Gen_mem_centE3 (hw k hk)

theorem tabRep_ce3Word {w : List ℕ} (hw : ∀ k ∈ w, k < 2) :
    TabRep (wordTab 1782 ce3Tabs w) (w.map ce3Gen).prod :=
  tabRep_wordTab rep_ce3 w fun k hk => by simpa [ce3Tabs] using hw k hk

@[expose] noncomputable def ct0Gen (i : ℕ) : Equiv.Perm (Fin 1782) :=
  ((C1ModelData.ct0Words.getD i []).map ce3Gen).prod

@[expose] noncomputable def cosRep (a : ℕ) : Equiv.Perm (Fin 1782) :=
  ((C1ModelData.cosWords.getD a []).map ce3Gen).prod

theorem ct0Words_ok {i : ℕ} (hi : i < 3) : ∀ k ∈ C1ModelData.ct0Words.getD i [], k < 2 := by
  interval_cases i <;> decide

theorem cosWords_ok (a : ℕ) : ∀ k ∈ C1ModelData.cosWords.getD a [], k < 2 := by
  rcases Nat.lt_or_ge a 48 with h | h
  · interval_cases a <;> decide
  · rw [List.getD_eq_default _ _ (by simp [C1ModelData.cosWords]; omega)]
    decide

theorem tabRep_ct0Gen {i : ℕ} (hi : i < 3) : TabRep ct0Gens[i]! (ct0Gen i) := by
  rw [show ct0Gens[i]! = ct0Tab i from getElem!_ofFn' _ hi]
  exact tabRep_ce3Word (ct0Words_ok hi)

theorem tabRep_cosTab {a : ℕ} (ha : a < 48) : TabRep cosTabs[a]! (cosRep a) := by
  rw [show cosTabs[a]! = cosTab a from getElem!_ofFn' _ ha]
  exact tabRep_ce3Word (cosWords_ok a)

theorem cosRep_mem_centE3 (a : ℕ) : cosRep a ∈ centE3 := word_mem_centE3 (cosWords_ok a)

theorem ct0Gen_mem_CT0 {i : ℕ} (hi : i < 3) : ct0Gen i ∈ CT0 := by
  refine mem_inf.mpr ⟨?_, (mem_inf.mp (word_mem_centE3 (ct0Words_ok hi))).2⟩
  rw [centralizer_T0_eq]
  exact (commT0_iff (tabRep_ct0Gen hi)).mp (cent_parts.2.2.2.1 i hi)

theorem enumerates_closure_ct0Gen :
    Enumerates (closure {g | ∃ i < 3, ct0Gen i = g}) ct0Enum.tabs.toList := by
  have hsize : ct0Gens.size = 3 := Array.size_ofFn
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) cent_parts.2.1
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨i, by rw [hsize]; exact hi, tabRep_ct0Gen hi⟩
  · rw [hsize] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, tabRep_ct0Gen hj⟩

theorem closure_ct0Gen_le :
    closure {g | ∃ i < 3, ct0Gen i = g} ≤ CT0 := by
  rw [closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ct0Gen_mem_CT0 hi

theorem tabRep_cosKey {a i : ℕ} (ha : a < 48) (hi : i < 4) :
    TabRep (cosKey a i) (cosRep a * t0Gen i * (cosRep a)⁻¹) := by
  have hc := tabRep_cosTab ha
  have hci := invsOK_spec cent_parts.2.2.2.2.1 (by simpa [cosTabs] using ha) hc
  rw [cosKey, t0Tabs_get hi]
  exact hc.conjTab (tabRep_t0Tab hi) hci

theorem cosRep_inj {a b : ℕ} (ha : a < 48) (hb : b < 48)
    (h : (cosRep b)⁻¹ * cosRep a ∈ CT0) : a = b := by
  have hc : ∀ i < 4, cosRep a * t0Gen i * (cosRep a)⁻¹ = cosRep b * t0Gen i * (cosRep b)⁻¹ := by
    intro i hi
    have hm := mem_centralizer_iff.mp (mem_inf.mp h).1 (t0Gen i) (t0Gen_mem_T0 hi)
    have e : cosRep a * t0Gen i = cosRep b * t0Gen i * (cosRep b)⁻¹ * cosRep a := by
      calc cosRep a * t0Gen i = cosRep b * ((cosRep b)⁻¹ * cosRep a * t0Gen i) := by group
        _ = cosRep b * (t0Gen i * ((cosRep b)⁻¹ * cosRep a)) := by rw [hm]
        _ = cosRep b * t0Gen i * (cosRep b)⁻¹ * cosRep a := by group
    rw [e]
    group
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hab | hab
  · obtain ⟨i, hi, hk⟩ := cent_parts.2.2.2.2.2.1 b hb a hab
    exact hk (((tabRep_cosKey hb hi).eq_iff (tabRep_cosKey ha hi)).mpr (hc i hi).symm)
  · obtain ⟨i, hi, hk⟩ := cent_parts.2.2.2.2.2.1 a ha b hab
    exact hk (((tabRep_cosKey ha hi).eq_iff (tabRep_cosKey hb hi)).mpr (hc i hi))

theorem card_CT0_le : Nat.card CT0 ≤ 192 := by
  let f : Fin 48 × CT0 → centE3 := fun p =>
    ⟨cosRep p.1 * p.2, mul_mem (cosRep_mem_centE3 p.1) (CT0_le_centE3 p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, c⟩ ⟨b, c'⟩ e
    have e' : cosRep a * c = cosRep b * c' := congrArg Subtype.val e
    have hm : (cosRep b)⁻¹ * cosRep a ∈ CT0 := by
      have : (cosRep b)⁻¹ * cosRep a =
          (c' : Equiv.Perm (Fin 1782)) * (c : Equiv.Perm (Fin 1782))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e', mul_inv_cancel_right]
      rw [this]
      exact mul_mem c'.2 (inv_mem c.2)
    have hab : a = b := Fin.ext (cosRep_inj a.2 b.2 hm)
    subst hab
    have hcc : c = c' := Subtype.ext (mul_left_cancel e')
    rw [hcc]
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fin, card_centE3] at h
  omega

theorem card_CT0 : Nat.card CT0 = 192 := by
  refine le_antisymm card_CT0_le ?_
  have h := card_le_of_le closure_ct0Gen_le
  rwa [enumerates_closure_ct0Gen.card, Array.length_toList, cent_parts.2.2.1] at h

theorem CT0_eq : CT0 = closure {g | ∃ i < 3, ct0Gen i = g} :=
  (eq_of_le_of_card_ge closure_ct0Gen_le (by
    rw [card_CT0, enumerates_closure_ct0Gen.card, Array.length_toList, cent_parts.2.2.1])).symm

theorem enumerates_CT0 : Enumerates CT0 ct0Tabs.toList := by
  rw [CT0_eq]
  exact enumerates_closure_ct0Gen

theorem enumerates_C0 : Enumerates C0 c0Tabs.toList := by
  have h := enumerates_V0.filter (K := centralizer {x | ∃ i < 4, t0Gen i = x}) commT0
    fun t g ht => commT0_iff ht
  have e : centralizer {x | ∃ i < 4, t0Gen i = x} ⊓ V0 = C0 := by
    rw [← centralizer_T0_eq]
    ext g
    simp only [C0, CT0, V0, mem_inf]
    tauto
  rw [e] at h
  rwa [c0Tabs, Array.toList_filter]

theorem card_C0 : Nat.card C0 = 16 := by
  rw [enumerates_C0.card, Array.length_toList, cent_c0Tabs]

theorem C0_le_V0 : C0 ≤ V0 := fun _ hg =>
  mem_inf.mpr ⟨(mem_inf.mp hg).1, CT0_le_invE (mem_inf.mp hg).2⟩

theorem C0_le_centralizer_r1 : C0 ≤ centralizer {r1} := by
  intro g hg
  obtain ⟨k, hk, hrep⟩ := enumerates_C0.exists_pos hg
  rw [cent_c0Tabs] at hk
  exact mem_centralizer_singleton_iff.mpr
    (((hrep.comp tabRep_r1).eq_iff (tabRep_r1.comp hrep)).mp (cent_c0r1 k hk))

theorem centralizer_J0_eq :
    centralizer (J0 : Set (Equiv.Perm (Fin 1782))) = centralizer {suzInv 1, zJ0} := by
  rw [J0_eq, centralizer_closure]

theorem A40_le : A40 ≤ centralizer {zJ0} ⊓ CT0 := fun g hg => by
  obtain ⟨hJ, hM⟩ := mem_inf.mp hg
  have hc := mem_centralizer_iff.mp hJ
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hc zJ0 zJ0_mem_J0).symm,
    mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => hc t (T0_le_J0 ht),
      mem_invE_iff.mpr ⟨(hc _ suzInv_one_mem_J0).symm, hM⟩⟩⟩

theorem enumerates_A4 :
    Enumerates (centralizer {zJ0} ⊓ CT0) a4Tabs.toList := by
  have h := enumerates_CT0.filter (K := centralizer {zJ0})
    (fun x => comp 1782 x zT == comp 1782 zT x) fun t g ht => by
      rw [mem_centralizer_singleton_iff]
      exact (ht.comp tabRep_zJ0).beq_iff (tabRep_zJ0.comp ht)
  rwa [a4Tabs, Array.toList_filter]

theorem mem_A40_of_comm {g : Equiv.Perm (Fin 1782)}
    (hg : g ∈ invE 1) (hz : zJ0 * g = g * zJ0) : g ∈ A40 := by
  refine mem_inf.mpr ⟨?_, invE_le_suzM hg⟩
  rw [centralizer_J0_eq, mem_centralizer_iff]
  rintro h (rfl | rfl)
  · exact (mem_invE_iff.mp hg).1.symm
  · exact hz

theorem closure_le_A40 :
    closure ({Model.w0, Model.rho1} : Set (Equiv.Perm (Fin 1782))) ≤ A40 := by
  rw [closure_le]
  rintro g (rfl | rfl)
  · exact mem_A40_of_comm w0_mem_invE zJ0_comm.1
  · exact mem_A40_of_comm rho1_mem_invE zJ0_comm.2.2

theorem enumerates_closure_A4 :
    Enumerates (closure ({Model.w0, Model.rho1} : Set (Equiv.Perm (Fin 1782))))
      a4Enum.tabs.toList := by
  have hsize : (#[w0T, rhoT] : Array Tab).size = 2 := rfl
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) cent_a4Enum
  · rcases ha with rfl | rfl
    · exact ⟨0, by rw [hsize]; norm_num, by rw [getElem!_pair_zero]; exact tabRep_w0⟩
    · exact ⟨1, by rw [hsize]; norm_num, by rw [getElem!_pair_one]; exact tabRep_rho1⟩
  · rw [hsize] at hj
    interval_cases j
    · exact ⟨_, Set.mem_insert _ _, by rw [getElem!_pair_zero]; exact tabRep_w0⟩
    · exact ⟨_, Set.mem_insert_of_mem _ rfl, by rw [getElem!_pair_one]; exact tabRep_rho1⟩

theorem card_A40 :
    Nat.card A40 = 12 := by
  refine le_antisymm ?_ ?_
  · have h := card_le_of_le A40_le
    rwa [enumerates_A4.card, Array.length_toList, cent_a4Tabs] at h
  · have h := card_le_of_le closure_le_A40
    rwa [enumerates_closure_A4.card, Array.length_toList, cent_a4Size] at h

theorem A40_eq :
    A40 = closure ({Model.w0, Model.rho1} : Set (Equiv.Perm (Fin 1782))) :=
  (eq_of_le_of_card_ge closure_le_A40 (by
    rw [card_A40, enumerates_closure_A4.card, Array.length_toList,
      cent_a4Size])).symm

theorem R0_le_A40 : Model.R0 ≤ A40 := by
  rw [R0_eq, closure_le]
  rintro g (rfl | rfl)
  · exact closure_le_A40 (subset_closure (Set.mem_insert _ _))
  · have hr : Model.rho1 ∈ closure ({Model.w0, Model.rho1} : Set (Equiv.Perm (Fin 1782))) :=
      subset_closure (Set.mem_insert_of_mem _ rfl)
    exact closure_le_A40 (mul_mem (mul_mem hr (subset_closure (Set.mem_insert _ _)))
      (inv_mem hr))

end Cent

end CFSG.Sporadic.SuzRecog.C1Model
