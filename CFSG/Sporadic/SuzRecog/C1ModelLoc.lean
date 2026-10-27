module

public import CFSG.Sporadic.SuzRecog.LocalRModel
public import CFSG.Sporadic.SuzRecog.C1ModelCent

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.C1Model

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

@[expose] noncomputable def kPerm (i : ℕ) : Equiv.Perm (Fin 1782) := wPerm (C1ModelData.kWords.getD i [])

section Loc


theorem isJ_iff {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    isJ t = true ↔ g * r1 = r1 * g ∧ g * Model.rho1 = Model.rho1 * g := by
  rw [isJ, Bool.and_eq_true, (ht.comp tabRep_r1).beq_iff (tabRep_r1.comp ht),
    (ht.comp tabRep_rho1).beq_iff (tabRep_rho1.comp ht)]

theorem isJ_of_mem_T0 {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) (hg : g ∈ T0) :
    isJ t = true :=
  (isJ_iff ht).mpr ⟨(mem_J0_iff.mp (T0_le_J0 hg)).2.1, (mem_J0_iff.mp (T0_le_J0 hg)).2.2.1⟩

theorem conjEq_iff {c u y : Tab} {C U Y : Equiv.Perm (Fin 1782)} (hc : TabRep c C)
    (hu : TabRep u U) (hy : TabRep y Y) : conjEq c u y = true ↔ C * U = Y * C := by
  rw [conjEq, Bool.and_eq_true, (hc.comp hu).beq_iff (hy.comp hc)]
  refine ⟨fun h => h.2, fun h => ⟨allBelow_eq_true.mpr fun i hi => ?_, h⟩⟩
  have e := (hc.comp hu).tab_eq (h ▸ hy.comp hc)
  have h1 := TabRep.comp_getElem! (n := 1782) c u ⟨i, by omega⟩
  have h2 := TabRep.comp_getElem! (n := 1782) y c ⟨i, by omega⟩
  rw [beq_iff_eq, ← h1, ← h2, e]

theorem tabRep_kTab {i : ℕ} (hi : i < 8) : TabRep (kTab i) (kPerm i) :=
  tabRep_cWord (by interval_cases i <;> decide)

theorem kTabs_get {i : ℕ} (hi : i < 8) : kTabs[i]! = kTab i := getElem!_ofFn' _ hi

theorem kPerm_mem {i : ℕ} (hi : i < 8) : kPerm i ∈ invE 1 :=
  wPerm_mem (by interval_cases i <;> decide)

theorem tabRep_c0Invs {i : ℕ} {g : Equiv.Perm (Fin 1782)} (hg : TabRep c0Tabs[i]! g)
    (h : (c0Invs[i]!).size = 1782 ∧ comp 1782 c0Invs[i]! c0Tabs[i]! = idTab 1782) :
    TabRep c0Invs[i]! g⁻¹ :=
  hg.inv h.1 h.2

theorem loc_parts :
    (∀ i < 16, (c0Invs[i]!).size = 1782 ∧ comp 1782 c0Invs[i]! c0Tabs[i]! = idTab 1782) ∧
    ∀ k < 512, found (indexOf tcTabs) tcTabs v0Enum.tabs[k]! = true ∨
      ((invTab 1782 v0Enum.tabs[k]!).size = 1782 ∧
        comp 1782 (invTab 1782 v0Enum.tabs[k]!) v0Enum.tabs[k]! = idTab 1782 ∧
        (∃ i < 16, isJ (comp 1782 (comp 1782 (comp 1782 v0Enum.tabs[k]! c0Tabs[i]!)
          (invTab 1782 v0Enum.tabs[k]!)) c0Invs[i]!) = false) ∧
        ∃ j < t0Invols.size, comp 1782 t0Invols[j]!
            (conjTab 1782 v0Enum.tabs[k]! (invTab 1782 v0Enum.tabs[k]!) t0Invols[j]!) ≠
          comp 1782 (conjTab 1782 v0Enum.tabs[k]! (invTab 1782 v0Enum.tabs[k]!) t0Invols[j]!)
            t0Invols[j]!) := by
  have h := c1Loc_check
  unfold locCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, allBelow_eq_true, anyBelow_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact ⟨h.1, fun k hk => (h.2 k hk).imp id fun h' => ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩⟩

theorem mem_tcTabs {t : Tab} (ht : t ∈ tcTabs.toList) :
    ∃ m < 1024, t = comp 1782 t0Enum.tabs[m / 16]! c0Tabs[m % 16]! := by
  obtain ⟨m, hm, rfl⟩ := exists_getElem!_of_mem ht
  have hm' : m < 1024 := by simpa [tcTabs] using hm
  exact ⟨m, hm', getElem!_ofFn' _ hm'⟩

theorem outside_spec {x : Equiv.Perm (Fin 1782)} (hx : x ∈ V0)
    (hout : ¬ ∃ t ∈ T0, ∃ c ∈ C0, x = t * c) :
    (∃ c ∈ C0, x * c * x⁻¹ * c⁻¹ ∉ T0) ∧
      ∃ e ∈ T0, e * e = 1 ∧ e * (x * e * x⁻¹) ≠ x * e * x⁻¹ * e := by
  obtain ⟨k, hk, hrep⟩ := enumerates_V0.exists_pos hx
  rw [v0_parts.2.1] at hk
  rcases loc_parts.2 k hk with h | ⟨h1, h2, ⟨i, hi, h3⟩, ⟨j, hj, h4⟩⟩
  · exfalso
    obtain ⟨m, hm, he⟩ := mem_tcTabs (mem_of_found h)
    have hT : m / 16 < t0Enum.tabs.size := by rw [t0_parts.2.1]; omega
    have hC : m % 16 < c0Tabs.size := by rw [cent_c0Tabs]; omega
    obtain ⟨t, ht, htr⟩ := enumerates_T0.exists_elt hT
    obtain ⟨c, hc, hcr⟩ := enumerates_C0.exists_elt hC
    exact hout ⟨t, ht, c, hc, hrep.perm_eq (he ▸ htr.comp hcr)⟩
  · have hxi : TabRep (invTab 1782 v0Enum.tabs[k]!) x⁻¹ := hrep.inv h1 h2
    have hi' : i < c0Tabs.size := by rw [cent_c0Tabs]; exact hi
    obtain ⟨c, hc, hcr⟩ := enumerates_C0.exists_elt hi'
    have hci := tabRep_c0Invs hcr (loc_parts.1 i hi)
    refine ⟨⟨c, hc, fun hmem => ?_⟩, ?_⟩
    · have := isJ_of_mem_T0 (((hrep.comp hcr).comp hxi).comp hci) hmem
      rw [h3] at this
      exact Bool.false_ne_true this
    · have hmem : t0Invols[j]! ∈ t0Enum.tabs.toList.filter
          (fun e => comp 1782 e e == idTab 1782) := by
        rw [← Array.toList_filter]
        exact getElem!_mem hj
      rw [List.mem_filter] at hmem
      obtain ⟨e, he, her⟩ := enumerates_T0.sound _ hmem.1
      refine ⟨e, he, (her.comp her).perm_eq ((beq_iff_eq.mp hmem.2) ▸ TabRep.idTab), fun hc' => h4 ?_⟩
      have hy := hrep.conjTab her hxi
      exact (her.comp hy).tab_eq (hc' ▸ hy.comp her)

theorem rho_parts {i : ℕ} (hi : i < 16) (hc : rhoCond (indexOf t0Enum.tabs) c0Tabs[i]! = true)
    {s : ℕ} (hs : s < 2) : ∃ j < 8,
      comp 1782 kTabs[j]! w0T =
        comp 1782 (if s = 0 then c0Tabs[i]! else comp 1782 w0T c0Tabs[i]!) kTabs[j]! ∧
      ∀ m < 512,
        rhoCand (comp 1782 kTabs[j]! v0Enum.tabs[m]!) c0Tabs[i]! (comp 1782 w0T c0Tabs[i]!) = true := by
  have h := c1Rho_check
  unfold rhoCheck at h
  dsimp only at h
  have h' := allBelow_eq_true.mp h i hi
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h'
  rcases h' with h' | h'
  · rw [hc] at h'
    exact Bool.noConfusion h'
  · obtain ⟨j, hj, hjj⟩ := anyBelow_eq_true.mp (allBelow_eq_true.mp h' s hs)
    rw [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hjj
    exact ⟨j, hj, hjj.1, hjj.2⟩

theorem rhoCond_eq_true {u : Tab} (h1 : comp 1782 u u = idTab 1782) (h2 : u ≠ idTab 1782)
    (h3 : u ≠ w0T) (h4 : found (indexOf t0Enum.tabs) t0Enum.tabs u = false)
    (h5 : found (indexOf t0Enum.tabs) t0Enum.tabs (comp 1782 w0T u) = false) :
    rhoCond (indexOf t0Enum.tabs) u = true := by
  have e1 : (comp 1782 u u == idTab 1782) = true := beq_iff_eq.mpr h1
  have e2 : (u == idTab 1782) = false := beq_eq_false_iff_ne.mpr h2
  have e3 : (u == w0T) = false := beq_eq_false_iff_ne.mpr h3
  rw [rhoCond, e1, e2, e3, h4, h5]
  rfl

theorem rhoTail_spec {c : Tab} {C : Equiv.Perm (Fin 1782)} (hc : TabRep c C)
    (h : rhoTail c = true) :
    C * C * Model.w0 = Model.w0 * (C * C) ∨
      (C * (C * C) * Model.w0 = Model.w0 * (C * (C * C)) ∧
        (C * (C * C) ≠ 1 ∨ C ∈ centralizer {x | ∃ i < 4, t0Gen i = x})) := by
  have hc2 := hc.comp hc
  have hc3 := hc.comp hc2
  have e1 := (hc2.comp tabRep_w0).beq_iff (tabRep_w0.comp hc2)
  have e2 := (hc3.comp tabRep_w0).beq_iff (tabRep_w0.comp hc3)
  have e3 := hc3.beq_iff (TabRep.idTab (n := 1782))
  have e4 := commT0_iff hc
  unfold rhoTail at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨h, h' | h'⟩
  · exact Or.inl (e1.mp h)
  · refine Or.inr ⟨e2.mp h, Or.inl fun h1 => ?_⟩
    rw [e3.mpr h1] at h'
    exact Bool.noConfusion h'
  · exact Or.inr ⟨e2.mp h, Or.inr (e4.mp h')⟩

theorem rhoCand_spec {c u l : Tab} {C U L : Equiv.Perm (Fin 1782)} (hc : TabRep c C)
    (hu : TabRep u U) (hl : TabRep l L) (h : rhoCand c u l = true)
    (hconj : C * U = Model.w0 * C ∨ C * U = U * C ∨ C * U = L * C) :
    C * C * Model.w0 = Model.w0 * (C * C) ∨
      (C * (C * C) * Model.w0 = Model.w0 * (C * (C * C)) ∧
        (C * (C * C) ≠ 1 ∨ C ∈ centralizer {x | ∃ i < 4, t0Gen i = x})) := by
  have hA : (conjEq c u w0T || conjEq c u u || conjEq c u l) = true := by
    rw [Bool.or_eq_true, Bool.or_eq_true, conjEq_iff hc hu tabRep_w0, conjEq_iff hc hu hu,
      conjEq_iff hc hu hl]
    rcases hconj with h' | h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
    · exact Or.inr h'
  rw [rhoCand, hA, Bool.not_true, Bool.false_or] at h
  exact rhoTail_spec hc h

theorem orderOf_dvd_of_pow_two {c : Equiv.Perm (Fin 1782)} {a b : ℕ} (hodd : Odd (orderOf c))
    (h : c ^ (a * 2 ^ b) = 1) : orderOf c ∣ a := by
  have hdvd := orderOf_dvd_of_pow_eq_one h
  have hcop : Nat.Coprime (orderOf c) (2 ^ b) := Nat.Coprime.pow_right _ hodd.coprime_two_right
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem pow_512_of_mem_V0 {g : Equiv.Perm (Fin 1782)} (hg : g ∈ V0) : g ^ 512 = 1 := by
  have h := pow_card_eq_one' (G := V0) (x := ⟨g, hg⟩)
  rw [card_V0] at h
  have h2 := congrArg (fun y : V0 => (y : Equiv.Perm (Fin 1782))) h
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  exact h2

theorem rho_spec {u : Equiv.Perm (Fin 1782)} (hu : u ∈ C0) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hul : u ≠ Model.w0) (huT : u ∉ T0) (hluT : Model.w0 * u ∉ T0) {c : Equiv.Perm (Fin 1782)}
    (hc : c ∈ invE 1) (hodd : Odd (orderOf c))
    (h1 : c * Model.w0 * c⁻¹ = u ∨ c * Model.w0 * c⁻¹ = Model.w0 * u)
    (h2 : c * u * c⁻¹ = Model.w0 ∨ c * u * c⁻¹ = u ∨ c * u * c⁻¹ = Model.w0 * u) :
    c ∈ centralizer (T0 : Set (Equiv.Perm (Fin 1782))) := by
  obtain ⟨i, hi, hur⟩ := enumerates_C0.exists_pos hu
  rw [cent_c0Tabs] at hi
  have hlur : TabRep (comp 1782 w0T c0Tabs[i]!) (Model.w0 * u) := tabRep_w0.comp hur
  have hnf : ∀ {t : Tab} {g : Equiv.Perm (Fin 1782)}, TabRep t g → g ∉ T0 →
      found (indexOf t0Enum.tabs) t0Enum.tabs t = false := fun {t g} ht hg => by
    cases hf : found (indexOf t0Enum.tabs) t0Enum.tabs t
    · rfl
    · obtain ⟨g', hg', hr⟩ := enumerates_T0.sound _ (mem_of_found hf)
      exact absurd (ht.perm_eq hr ▸ hg') hg
  have hcond := rhoCond_eq_true ((hur.comp hur).tab_eq (hu2 ▸ TabRep.idTab))
    (fun h => hu1 ((hur.eq_iff TabRep.idTab).mp h)) (fun h => hul ((hur.eq_iff tabRep_w0).mp h))
    (hnf hur huT) (hnf hlur hluT)
  obtain ⟨s, hs, W, hWr, hW⟩ : ∃ s < 2, ∃ W : Equiv.Perm (Fin 1782),
      TabRep (if s = 0 then c0Tabs[i]! else comp 1782 w0T c0Tabs[i]!) W ∧
        c * Model.w0 * c⁻¹ = W := by
    rcases h1 with h1 | h1
    · exact ⟨0, by norm_num, u, by simp only [↓reduceIte]; exact hur, h1⟩
    · exact ⟨1, by norm_num, Model.w0 * u, by simp only [one_ne_zero, ↓reduceIte]; exact hlur, h1⟩
  have hrp := rho_parts hi hcond hs
  obtain ⟨j, hj, hkj, hm⟩ := hrp
  have hkr : TabRep kTabs[j]! (kPerm j) := by rw [kTabs_get hj]; exact tabRep_kTab hj
  have hkW : kPerm j * Model.w0 = W * kPerm j :=
    ((hkr.comp tabRep_w0).eq_iff (hWr.comp hkr)).mp hkj
  have hcw : c * Model.w0 = W * c := by rw [← hW, inv_mul_cancel_right]
  have hvV : (kPerm j)⁻¹ * c ∈ V0 := by
    refine mem_V0_iff.mpr ⟨?_, mul_mem (inv_mem (kPerm_mem hj)) hc⟩
    have hk' : (kPerm j)⁻¹ * W = Model.w0 * (kPerm j)⁻¹ := by
      calc (kPerm j)⁻¹ * W = (kPerm j)⁻¹ * (W * kPerm j) * (kPerm j)⁻¹ := by group
        _ = (kPerm j)⁻¹ * (kPerm j * Model.w0) * (kPerm j)⁻¹ := by rw [hkW]
        _ = Model.w0 * (kPerm j)⁻¹ := by group
    rw [mul_assoc, hcw, ← mul_assoc, hk', mul_assoc]
  obtain ⟨m, hm', hvr⟩ := enumerates_V0.exists_pos hvV
  rw [v0_parts.2.1] at hm'
  have hcr : TabRep (comp 1782 kTabs[j]! v0Enum.tabs[m]!) c := by
    have := hkr.comp hvr
    rwa [mul_inv_cancel_left] at this
  have hconj : c * u = Model.w0 * c ∨ c * u = u * c ∨ c * u = Model.w0 * u * c := by
    rcases h2 with h2 | h2 | h2
    · exact Or.inl (mul_inv_eq_iff_eq_mul.mp h2)
    · exact Or.inr (Or.inl (mul_inv_eq_iff_eq_mul.mp h2))
    · exact Or.inr (Or.inr (mul_inv_eq_iff_eq_mul.mp h2))
  rcases rhoCand_spec hcr hur hlur (hm m hm') hconj with h | ⟨h, h'⟩
  ·
    exfalso
    have hc2V : c * c ∈ V0 := mem_V0_iff.mpr ⟨h, mul_mem hc hc⟩
    have hpow : c ^ (1 * 2 ^ 10) = 1 := by
      rw [show 1 * 2 ^ 10 = 2 * 512 by norm_num, pow_mul, sq]
      exact pow_512_of_mem_V0 hc2V
    have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (orderOf_dvd_of_pow_two hodd hpow))
    rw [hc1, one_mul, inv_one, mul_one] at h1
    rcases h1 with h1 | h1
    · exact hul h1.symm
    · exact hu1 (by
        calc u = Model.w0 * (Model.w0 * u) := by rw [← mul_assoc, w0_mul_self, one_mul]
          _ = 1 := by rw [← h1, w0_mul_self])
  ·
    have hc3V : c * (c * c) ∈ V0 := mem_V0_iff.mpr ⟨h, mul_mem hc (mul_mem hc hc)⟩
    have e3 : c ^ 3 = c * (c * c) := by rw [pow_succ', pow_two]
    have hpow : c ^ (3 * 2 ^ 9) = 1 := by
      rw [show 3 * 2 ^ 9 = 3 * 512 by norm_num, pow_mul, e3]
      exact pow_512_of_mem_V0 hc3V
    have h3 : c * (c * c) = 1 := by
      rw [← e3]
      exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_of_pow_two hodd hpow)
    rcases h' with h' | h'
    · exact absurd h3 h'
    · rw [centralizer_T0_eq]
      exact h'

theorem mem_centralizer_w0E {x : ↥(invE 1)} :
    x ∈ centralizer ({w0E} : Set ↥(invE 1)) ↔ (x : Equiv.Perm (Fin 1782)) ∈ V0 := by
  rw [mem_centralizer_singleton_iff, mem_V0_iff]
  exact ⟨fun h => ⟨congrArg Subtype.val h, x.2⟩, fun h => Subtype.ext h.1⟩

theorem mem_centralizer_T0E {x : ↥(invE 1)} :
    x ∈ centralizer ((T0.subgroupOf (invE 1) : Subgroup ↥(invE 1)) : Set ↥(invE 1)) ↔
      (x : Equiv.Perm (Fin 1782)) ∈ centralizer (T0 : Set (Equiv.Perm (Fin 1782))) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, T0_le_invE ht⟩ (mem_subgroupOf.mpr ht))
  · intro h t ht
    exact Subtype.ext (h t (mem_subgroupOf.mp ht))

theorem mem_locC {x : ↥(invE 1)} :
    x ∈ LocalR.locC w0E (T0.subgroupOf (invE 1)) ↔ (x : Equiv.Perm (Fin 1782)) ∈ C0 := by
  rw [LocalR.locC, mem_inf, mem_centralizer_w0E, mem_centralizer_T0E]
  simp only [C0, CT0, V0, mem_inf]
  exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

theorem map_locC :
    (LocalR.locC w0E (T0.subgroupOf (invE 1))).map (invE 1).subtype = C0 := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_locC.mp hx
  · intro hg
    exact ⟨⟨g, CT0_le_invE (mem_inf.mp hg).2⟩, mem_locC.mpr hg, rfl⟩

theorem map_centralizer_T0E :
    (centralizer ((T0.subgroupOf (invE 1) : Subgroup ↥(invE 1)) : Set ↥(invE 1))).map
      (invE 1).subtype = CT0 := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_inf.mpr ⟨mem_centralizer_T0E.mp hx, x.2⟩
  · intro hg
    exact ⟨⟨g, CT0_le_invE hg⟩, mem_centralizer_T0E.mpr (mem_inf.mp hg).1, rfl⟩

theorem mem_sup_of_mul {t c : Equiv.Perm (Fin 1782)} (ht : t ∈ T0) (hc : c ∈ C0)
    {x : ↥(invE 1)} (hx : (x : Equiv.Perm (Fin 1782)) = t * c) :
    x ∈ T0.subgroupOf (invE 1) ⊔ LocalR.locC w0E (T0.subgroupOf (invE 1)) := by
  have hcE : c ∈ invE 1 := CT0_le_invE (mem_inf.mp hc).2
  have e : x = ⟨t, T0_le_invE ht⟩ * ⟨c, hcE⟩ := Subtype.ext hx
  rw [e]
  exact mul_mem (mem_sup_left (mem_subgroupOf.mpr ht)) (mem_sup_right (mem_locC.mpr hc))

theorem locModel_w0 : LocalR.LocModel w0E (T0.subgroupOf (invE 1)) where
  card_V := by
    rw [LocalR.card_centralizer_coe (invE 1) w0E, inf_comm]
    exact card_V0
  T_le := fun x hx => mem_centralizer_w0E.mpr (T0_le_V0 (mem_subgroupOf.mp hx))
  card_T := by
    rw [Nat.card_congr (subgroupOfEquivOfLe T0_le_invE).toEquiv, card_T0]
  mem_T := by
    intro u hu hu2 hconj
    have hu2' : orderOf (u : Equiv.Perm (Fin 1782)) = 2 := by rwa [Subgroup.orderOf_coe]
    refine mem_subgroupOf.mpr (mem_T0_of_fix (mem_centralizer_w0E.mp hu) ?_ ?_ ?_)
    · rw [← pow_two, ← hu2', pow_orderOf_eq_one]
    · intro h
      rw [h, orderOf_one] at hu2'
      exact absurd hu2' (by norm_num)
    · intro h
      exact hconj (((LocalR.isConj_lambda4_iff u hu2).mpr h).trans isConj_lambda4_w0)
  card_C := by
    rw [← card_map_of_injective (invE 1).subtype_injective, map_locC, card_C0]
  act_C := by
    intro x hx hxT
    have hout : ¬ ∃ t ∈ T0, ∃ c ∈ C0, (x : Equiv.Perm (Fin 1782)) = t * c :=
      fun ⟨t, ht, c, hc, he⟩ => hxT (mem_sup_of_mul ht hc he)
    obtain ⟨c, hc, hnot⟩ := (outside_spec (mem_centralizer_w0E.mp hx) hout).1
    exact ⟨⟨c, CT0_le_invE (mem_inf.mp hc).2⟩, mem_locC.mpr hc, fun h => hnot (mem_subgroupOf.mp h)⟩
  exists_inv := by
    refine ⟨⟨tau0, tau0_mem_invE⟩, mem_centralizer_w0E.mpr tau0_mem_V0, fun h => ?_,
      Subtype.ext tau0_mul_self⟩
    have hle : T0.subgroupOf (invE 1) ⊔ LocalR.locC w0E (T0.subgroupOf (invE 1)) ≤
        centralizer ({⟨r1, r1_mem_invE⟩} : Set ↥(invE 1)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_J0_iff.mp (T0_le_J0 (mem_subgroupOf.mp hx))).2.1)
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp (C0_le_centralizer_r1 (mem_locC.mp hx))))
    exact tau0_not_comm_r1 (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hle h)))
  swap := by
    intro x hx hxT
    have hout : ¬ ∃ t ∈ T0, ∃ c ∈ C0, (x : Equiv.Perm (Fin 1782)) = t * c :=
      fun ⟨t, ht, c, hc, he⟩ => hxT (mem_sup_of_mul ht hc he)
    obtain ⟨e, he, he2, hne⟩ := (outside_spec (mem_centralizer_w0E.mp hx) hout).2
    exact ⟨⟨e, T0_le_invE he⟩, mem_subgroupOf.mpr he, Subtype.ext he2,
      fun h => hne (congrArg Subtype.val h)⟩
  rho := by
    intro u hu hu2 hu1 hul huT hluT c hodd h1 h2
    have hodd' : Odd (orderOf (c : Equiv.Perm (Fin 1782))) := by rwa [Subgroup.orderOf_coe]
    refine mem_centralizer_T0E.mpr (rho_spec (mem_locC.mp hu) (congrArg Subtype.val hu2)
      (fun h => hu1 (Subtype.ext h)) (fun h => hul (Subtype.ext h))
      (fun h => huT (mem_subgroupOf.mpr h)) (fun h => hluT (mem_subgroupOf.mpr h)) c.2 hodd'
      ?_ ?_)
    · rcases h1 with h1 | h1
      · exact Or.inl (congrArg Subtype.val h1)
      · exact Or.inr (congrArg Subtype.val h1)
    · rcases h2 with h2 | h2 | h2
      · exact Or.inl (congrArg Subtype.val h2)
      · exact Or.inr (Or.inl (congrArg Subtype.val h2))
      · exact Or.inr (Or.inr (congrArg Subtype.val h2))
  card_cent_T := by
    rw [← card_map_of_injective (invE 1).subtype_injective, map_centralizer_T0E, card_CT0]

end Loc

end CFSG.Sporadic.SuzRecog.C1Model
