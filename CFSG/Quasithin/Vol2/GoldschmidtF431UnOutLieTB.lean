module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieT

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem tfc_cj_fa_comm {s z : Xg h} {φ : K ≃+* K} (hs : s * z = z * s) (hφ : fa h φ z = z) :
    cj h s * fa h φ * cj h z = cj h z * (cj h s * fa h φ) := by
  have e1 : fa h φ * cj h z = cj h z * fa h φ := by
    have e := fa_mul_cj_mul_inv h φ z
    rw [hφ] at e
    calc fa h φ * cj h z = fa h φ * cj h z * (fa h φ)⁻¹ * fa h φ := by group
      _ = cj h z * fa h φ := by rw [e]
  have e2 : cj h s * cj h z = cj h z * cj h s := by rw [← cj_mul, ← cj_mul, hs]
  calc cj h s * fa h φ * cj h z = cj h s * (fa h φ * cj h z) := by rw [mul_assoc]
    _ = cj h s * (cj h z * fa h φ) := by rw [e1]
    _ = (cj h s * cj h z) * fa h φ := by rw [mul_assoc]
    _ = (cj h z * cj h s) * fa h φ := by rw [e2]
    _ = cj h z * (cj h s * fa h φ) := by rw [mul_assoc]

theorem tfc_le_centralizer_z1 (F : Subgroup (K ≃+* K)) :
    Ssd h (Psy h) (fStab_Psy h) F ≤
      Subgroup.centralizer ({cj h (z1X h)} : Set (MulAut (Xg h))) := by
  rintro _ ⟨s, hs, φ, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact tfc_cj_fa_comm h (tfc_comm_z1X h hs) (fa_z1X h φ)

@[expose] def tfc_CPz2 : Subgroup (Xg h) :=
  Psy h ⊓ Subgroup.centralizer ({z2X h} : Set (Xg h))

theorem tfc_fStab_CPz2 : FStab h (tfc_CPz2 h) := by
  intro φ x
  rw [tfc_CPz2, Subgroup.mem_inf, Subgroup.mem_inf, fStab_Psy h φ x,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ?_
  have e : fa h φ x * z2X h = z2X h * fa h φ x ↔ fa h φ (x * z2X h) = fa h φ (z2X h * x) := by
    rw [map_mul, map_mul, fa_z2X]
  rw [e, (fa h φ).injective.eq_iff]

theorem tfc_Ssd_CPz2_le (F : Subgroup (K ≃+* K)) :
    Ssd h (tfc_CPz2 h) (tfc_fStab_CPz2 h) F ≤ Ssd h (Psy h) (fStab_Psy h) F ⊓
      Subgroup.centralizer ({cj h (z2X h)} : Set (MulAut (Xg h))) := by
  rintro _ ⟨s, hs, φ, hφ, rfl⟩
  exact ⟨⟨s, hs.1, φ, hφ, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2
    (tfc_cj_fa_comm h (Subgroup.mem_centralizer_singleton_iff.1 hs.2) (fa_z2X h φ))⟩

theorem tfc_lt_card_CPz2 : (2 ^ f) ^ 4 < Nat.card (tfc_CPz2 h) := by
  rw [← tfc_card_A1X h]
  refine Subgroup.card_lt_of_lt (lt_of_le_of_ne ?_ ?_)
  · intro s hs
    exact ⟨Subgroup.mem_subgroupOf.2 (miyamotoA1_le_P h (Subgroup.mem_subgroupOf.1 hs)),
      Subgroup.mem_centralizer_singleton_iff.2 (tfc_comm_z2X_A1X h hs)⟩
  · intro e
    refine tfc_u_not_mem_A1X h ?_
    rw [e]
    exact ⟨tfc_u_mem_Psy h, Subgroup.mem_centralizer_singleton_iff.2 (tfc_comm_z2X_u h)⟩

include h in
theorem tfc_card_pos (F : Subgroup (K ≃+* K)) : 0 < Nat.card F := by
  have := finite_aut h
  exact Nat.card_pos

theorem Tf_lt_z (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) :
    Nat.card ↥(spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h)) <
      Nat.card ↥(Ssd h (Psy h) (fStab_Psy h) F₂ ⊓
        Subgroup.centralizer ({cj h (z1X h)} : Set (MulAut (Xg h)))) := by
  rw [inf_eq_left.2 (tfc_le_centralizer_z1 h F₂), spTf_Ssd, card_Ssd, card_Ssd, tfc_card_Pfx,
    tfc_card_Psy]
  refine Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right ?_ (by norm_num))
    (tfc_card_pos h F₂)
  exact Nat.one_lt_pow (by omega) (by norm_num)

theorem Tf_lt_t (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) :
    Nat.card ↥(spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h)) <
      Nat.card ↥(Ssd h (Psy h) (fStab_Psy h) F₂ ⊓
        Subgroup.centralizer ({cj h (z2X h)} : Set (MulAut (Xg h)))) := by
  have _ := hf
  rw [spTf_Ssd, card_Ssd, tfc_card_Pfx]
  refine lt_of_lt_of_le ?_ (Subgroup.card_le_of_le (tfc_Ssd_CPz2_le h F₂))
  rw [card_Ssd]
  exact Nat.mul_lt_mul_of_pos_right (tfc_lt_card_CPz2 h) (tfc_card_pos h F₂)

end CFSG.Quasithin.H13.F431.Un.OL
