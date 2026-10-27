module

public import CFSG.Sporadic.ONOddCore.SylowEightCheck
public import CFSG.Sporadic.Schreier.ONSylowCenter
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSporadicEight

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure)

section General

variable {G H : Type*} [Group G] [Group H]

theorem map_closure_squares (f : G →* H) :
    (Subgroup.closure {x : G | ∃ t, t ^ 2 = x}).map f =
      Subgroup.closure {y : H | ∃ s ∈ f.range, s ^ 2 = y} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨f t, ⟨t, rfl⟩, (map_pow f t 2).symm⟩
  · rintro ⟨s, ⟨t, rfl⟩, rfl⟩
    exact ⟨t ^ 2, ⟨t, rfl⟩, map_pow f t 2⟩

theorem map_closure_involutions (f : G →* H) (hf : Function.Injective f) (K : Subgroup G) :
    (Subgroup.closure {x : G | x ∈ K ∧ x ^ 2 = 1}).map f =
      Subgroup.closure {y : H | y ∈ K.map f ∧ y ^ 2 = 1} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxK, hx2⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxK, hf ?_⟩, rfl⟩
    rw [map_pow, hy2, map_one]

theorem characteristic_omega_squares :
    (Subgroup.closure {x : G | x ∈ Subgroup.closure {x : G | ∃ t, t ^ 2 = x} ∧
      x ^ 2 = 1}).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hD : (Subgroup.closure {x : G | ∃ t, t ^ 2 = x}).map φ.toMonoidHom =
      Subgroup.closure {x : G | ∃ t, t ^ 2 = x} := by
    rw [map_closure_squares, MonoidHom.range_eq_top.2 φ.surjective]
    simp
  rw [map_closure_involutions _ φ.injective, hD]

end General

abbrev sqT :
    Subgroup onT := Subgroup.closure {x : onT | ∃ t, t ^ 2 = x}

abbrev omegaT :
    Subgroup onT := Subgroup.closure {x : onT | x ∈ sqT ∧ x ^ 2 = 1}

abbrev sqP :
    Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {x | ∃ t ∈ onT, t ^ 2 = x}

abbrev omegaP :
    Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {x | x ∈ sqP ∧ x ^ 2 = 1}

theorem sqT_map :
    sqT.map onT.subtype = sqP := by
  rw [map_closure_squares, Subgroup.range_subtype]

theorem omegaT_map :
    omegaT.map onT.subtype = omegaP := by
  rw [map_closure_involutions _ onT.subtype_injective, sqT_map]

abbrev sq32 : Subgroup (Equiv.Perm (Fin 32)) :=
  Subgroup.closure {y | ∃ s ∈ onT32Chain.originalSubgroup, s ^ 2 = y}

abbrev omega32 : Subgroup (Equiv.Perm (Fin 32)) :=
  Subgroup.closure {y | y ∈ sq32 ∧ y ^ 2 = 1}

theorem sqT_rho :
    sqT.map rhoT = sq32 := by
  rw [map_closure_squares, rhoT_range]

theorem omegaT_rho :
    omegaT.map rhoT = omega32 := by
  rw [map_closure_involutions _ rhoT_injective, sqT_rho]

theorem sqTabs_size : sqTabs.size = t32Enum.tabs.size := Array.size_map ..

theorem sqTabs_get {k : ℕ} (hk : k < t32Enum.tabs.size) :
    sqTabs[k]! = comp 32 t32Enum.tabs[k]! t32Enum.tabs[k]! := by
  rw [getElem!_pos sqTabs k (by rw [sqTabs_size]; exact hk), getElem!_pos _ k hk]
  simp [sqTabs]

theorem sq32_enumerates :
    Enumerates sq32 sqEnum.tabs.toList := by
  refine enumerates_closure ?_ ?_ sylow_eight_cert.1
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hrep⟩ := t32_enumerates.exists_pos hs
    exact ⟨k, by rw [sqTabs_size]; exact hk, by rw [sqTabs_get hk, sq]; exact hrep.comp hrep⟩
  · intro j hj
    rw [sqTabs_size] at hj
    obtain ⟨s, hs, hrep⟩ := t32_enumerates.exists_elt hj
    exact ⟨s ^ 2, ⟨s, hs, rfl⟩, by rw [sqTabs_get hj, sq]; exact hrep.comp hrep⟩

theorem card_sq32 :
    Nat.card sq32 = 64 := by
  rw [sq32_enumerates.card, Array.length_toList, sylow_eight_cert.2.1]

theorem mem_omegaTabs {t : Tab} :
    t ∈ omegaTabs.toList ↔ t ∈ sqEnum.tabs.toList ∧ comp 32 t t = idTab 32 := by
  rw [omegaTabs, Array.toList_filter, List.mem_filter, beq_iff_eq]

theorem omega32_enumerates :
    Enumerates omega32 omegaEnum.tabs.toList := by
  refine enumerates_closure ?_ ?_ sylow_eight_cert.2.2.1
  · rintro y ⟨hy, hy2⟩
    obtain ⟨t, ht, hrep⟩ := sq32_enumerates.complete y hy
    have hsq : comp 32 t t = idTab 32 :=
      (hrep.comp hrep).tab_eq (by rw [← sq, hy2]; exact TabRep.idTab)
    have hmem : t ∈ omegaTabs.toList := mem_omegaTabs.2 ⟨ht, hsq⟩
    obtain ⟨k, hk, hkt⟩ := CFSG.ComponentClassification.PSL3Four.exists_getElem!_of_mem hmem
    exact ⟨k, hk, hkt ▸ hrep⟩
  · intro j hj
    have hmem := mem_omegaTabs.1 (CFSG.ComponentClassification.PSL3Four.getElem!_mem hj)
    obtain ⟨y, hy, hrep⟩ := sq32_enumerates.sound _ hmem.1
    refine ⟨y, ⟨hy, ?_⟩, hrep⟩
    have h := hrep.comp hrep
    rw [hmem.2] at h
    rw [sq]
    exact h.perm_eq TabRep.idTab

theorem card_omega32 :
    Nat.card omega32 = 8 := by
  rw [omega32_enumerates.card, Array.length_toList, sylow_eight_cert.2.2.2.1]

theorem omega32_comm_cert :
    ∀ a ∈ omegaEnum.tabs, ∀ b ∈ omegaEnum.tabs,
    comp 32 a b = comp 32 b a := by
  intro a ha b hb
  have h := sylow_eight_cert.2.2.2.2.1
  rw [Array.all_eq_true'] at h
  have h' := h a ha
  rw [Array.all_eq_true'] at h'
  exact beq_iff_eq.1 (h' b hb)

theorem omega32_sq_cert :
    ∀ a ∈ omegaEnum.tabs, comp 32 a a = idTab 32 := by
  intro a ha
  have h := sylow_eight_cert.2.2.2.2.2
  rw [Array.all_eq_true'] at h
  exact beq_iff_eq.1 (h a ha)

theorem omega32_facts
    {a b : Equiv.Perm (Fin 32)} (ha : a ∈ omega32) (hb : b ∈ omega32) :
    a * b = b * a ∧ a ^ 2 = 1 := by
  obtain ⟨ta, hta, hra⟩ := omega32_enumerates.complete a ha
  obtain ⟨tb, htb, hrb⟩ := omega32_enumerates.complete b hb
  have hab := omega32_comm_cert ta (Array.mem_toList_iff.1 hta) tb (Array.mem_toList_iff.1 htb)
  have haa := omega32_sq_cert ta (Array.mem_toList_iff.1 hta)
  have h1 : TabRep (comp 32 ta tb) (b * a) := by
    rw [hab]
    exact hrb.comp hra
  have h2 : TabRep (comp 32 ta ta) (1 : Equiv.Perm (Fin 32)) := by
    rw [haa]
    exact TabRep.idTab
  refine ⟨(hra.comp hrb).perm_eq h1, ?_⟩
  rw [sq]
  exact (hra.comp hra).perm_eq h2

@[expose] def omegaTEquiv :
    omegaT ≃* omega32 :=
  (omegaT.equivMapOfInjective rhoT rhoT_injective).trans (MulEquiv.subgroupCongr omegaT_rho)

@[expose] def omegaPEquiv :
    omegaP ≃* omegaT :=
  (MulEquiv.subgroupCongr omegaT_map).symm.trans
    (omegaT.equivMapOfInjective onT.subtype onT.subtype_injective).symm

theorem card_omegaP :
    Nat.card omegaP = 8 := by
  rw [Nat.card_congr (omegaPEquiv.trans omegaTEquiv).toEquiv, card_omega32]

theorem card_sqP :
    Nat.card sqP = 64 := by
  rw [← sqT_map, Subgroup.card_map_of_injective onT.subtype_injective,
    ← Subgroup.card_map_of_injective rhoT_injective, sqT_rho, card_sq32]

theorem omegaP_elementary :
    CFSG.IsElementaryAbelian 2 omegaP := by
  set e := omegaPEquiv.trans omegaTEquiv
  have key : ∀ a b : omegaP, a * b = b * a ∧ a ^ 2 = 1 := by
    intro a b
    have h := omega32_facts (e a).2 (e b).2
    constructor
    · apply e.injective
      apply Subtype.ext
      rw [map_mul, map_mul]
      exact h.1
    · apply e.injective
      apply Subtype.ext
      rw [map_pow, map_one]
      exact h.2
  exact { toIsMulCommutative := ⟨⟨fun a b => (key a b).1⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => (key a a).2 }

theorem omegaP_subgroupOf :
    omegaP.subgroupOf onT = omegaT := by
  rw [← omegaT_map]
  exact Subgroup.comap_map_eq_self_of_injective onT.subtype_injective omegaT

theorem glq_on_sylow_characteristic_elementary_eight :
    CFSG.ComponentClassification.UnbalancedCorr.ONSylowCharacteristicElementaryEight :=
  ⟨card_sqP, omegaP_elementary, card_omegaP, by
    rw [omegaP_subgroupOf]
    exact characteristic_omega_squares⟩

end CFSG.Sporadic.ONOddCore
