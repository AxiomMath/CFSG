module

public import CFSG.Quasithin.Background.RonanE43M22Lat

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.E2P B6
  CFSG.Quasithin.E2P.SporB CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

section M22


theorem m22_data' : ∃ A V P : Subgroup ↥Mgrp, IsSylowTwoOf Ugrp ⊤ ∧ IsA5Ext A V ∧ Ugrp ≤ P ∧
    Nat.card P = 3 * Nat.card Ugrp ∧ (A ⊔ Ugrp) ⊔ P = ⊤ ∧
    (∀ α : MulAut ↥Mgrp, Ugrp.map α.toMonoidHom = Ugrp →
      A.map α.toMonoidHom = A ∧ P.map α.toMonoidHom = P) ∧
    Nat.card A = 960 ∧ Nat.card P = 384 := by
  obtain ⟨V', hV'⟩ := m22_A5
  refine ⟨Am, V'.subgroupOf Mgrp, Pm 5, m22_isSylow, ?_, m22_U_le_Pm 5 (by norm_num), ?_, ?_, ?_,
    m22_Am_card, ?_⟩
  · exact IsA5Ext.subgroupOf hV' m22_hAM
  · have hcU : Nat.card Ugrp = 128 := by rw [m22_Pm_zero, m22_Pm_card 0 (by norm_num)]; rfl
    rw [m22_Pm_card 5 (by norm_num), hcU]
    rfl
  · rw [m22_Am_sup_U]
    exact m22_two_sup_five'
  · intro α hα
    exact ⟨m22_inv_Am α hα, m22_inv_five α hα⟩
  · rw [m22_Pm_card 5 (by norm_num)]
    rfl

variable {H : Type} [Group H] [Finite H]

theorem m22_pull_data {T L : Subgroup H} (hT : IsSylowIn 2 T ⊤) (hK : L.Normal)
    (e₀ : ↥L ≃* ↥Mgrp) :
    ∃ Ah Vh Ph : Subgroup H, Ah ≤ L ∧ Ph ≤ L ∧ IsA5Ext Ah Vh ∧
      T ≤ Subgroup.normalizer (Ah : Set H) ∧ T ≤ Subgroup.normalizer (Ph : Set H) ∧
      T ⊓ L ≤ Ph ∧ Nat.card Ph = 3 * Nat.card ↥(T ⊓ L) ∧ Nat.card Ah = 960 ∧
      Nat.card Ph = 384 ∧ L ≤ (Ah ⊔ (T ⊓ L)) ⊔ Ph := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, V', P, hS, hA5, hSP, hP3, hgen, hinv, hAcard, hPcard⟩ := m22_data'
  have hSK : IsSylowTwoOf (T ⊓ L) L :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e, he⟩ := exists_equiv_sylow e₀ hSK hS
  have hα : ∀ t ∈ T, Ugrp.map (autK e t).toMonoidHom = Ugrp := fun t ht => by
    rw [← he]
    exact map_autK_of_mem_normalizer' e inf_le_right (le_normalizer_inf hK ht)
  let pull : Subgroup ↥Mgrp → Subgroup H := fun P => (P.map e.symm.toMonoidHom).map L.subtype
  have hpullS : pull Ugrp = T ⊓ L := by
    show (Ugrp.map e.symm.toMonoidHom).map L.subtype = T ⊓ L
    rw [← he]
    exact pull_map e inf_le_right
  have hpullcard : ∀ P : Subgroup ↥Mgrp, Nat.card (pull P) = Nat.card P := fun P => by
    show Nat.card ((P.map e.symm.toMonoidHom).map L.subtype) = Nat.card P
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hTn : ∀ Y : Subgroup ↥Mgrp,
      (∀ α : MulAut ↥Mgrp, Ugrp.map α.toMonoidHom = Ugrp → Y.map α.toMonoidHom = Y) →
      T ≤ Subgroup.normalizer ((pull Y : Subgroup H) : Set H) :=
    fun Y hY t ht => mem_normalizer_pull e (hY _ (hα t ht))
  let f : ↥Mgrp →* H := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hpull_eq : ∀ Y : Subgroup ↥Mgrp, pull Y = Y.map f := fun Y => by
    show (Y.map e.symm.toMonoidHom).map L.subtype = Y.map f
    rw [Subgroup.map_map]
  have hA5G : IsA5Ext (pull A) (pull V') := by
    rw [hpull_eq, hpull_eq]
    exact hA5.map f hf
  have hSP' : T ⊓ L ≤ pull P := by
    rw [← hpullS]
    exact pull_mono e hSP
  have hS' : Nat.card ↥(T ⊓ L) = Nat.card Ugrp := by rw [← hpullS, hpullcard]
  refine ⟨pull A, pull V', pull P, pull_le e A, pull_le e P, hA5G,
    hTn A fun α hα' => (hinv α hα').1, hTn P fun α hα' => (hinv α hα').2, hSP', ?_, ?_, ?_, ?_⟩
  · rw [hpullcard, hP3, hS']
  · rw [hpullcard, hAcard]
  · rw [hpullcard, hPcard]
  · have h1 : pull ((A ⊔ Ugrp) ⊔ P) = L := by
      rw [hgen]
      exact pull_top e
    have h2 : pull ((A ⊔ Ugrp) ⊔ P) = (pull A ⊔ pull Ugrp) ⊔ pull P := by
      simp only [pull, Subgroup.map_sup]
    have h3 : L = (pull A ⊔ (T ⊓ L)) ⊔ pull P := by
      rw [← hpullS]
      exact h1.symm.trans h2
    exact h3.le

end M22

end CFSG.Quasithin.RonanE43
