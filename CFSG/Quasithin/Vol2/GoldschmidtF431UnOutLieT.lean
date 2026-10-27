module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieBar

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem tfc_card_sg {M : Subgroup (GL (Fin 4) K)} (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    Nat.card (sg h M) = Nat.card M :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv

theorem tfc_card_Psy : Nat.card (Psy h) = (2 ^ f) ^ 6 := by
  rw [Psy, tfc_card_sg h (miyamotoUnipotent_le_SU h false false), card_miyamotoP]

theorem tfc_card_A1X : Nat.card (A1X h) = (2 ^ f) ^ 4 := by
  rw [A1X, tfc_card_sg h (miyamotoUnipotent_le_SU h true false), card_miyamotoA1]

theorem tfc_mem_P (a b c d : h.fixedField) : miyamotoXGL h a b c d ∈ miyamotoP h := by
  have ha : h.bar (a : K) = a := a.2
  have hb : h.bar (b : K) = b := b.2
  have hc : h.bar (c : K) = c := c.2
  have hd : h.bar (d : K) = d := d.2
  refine (miyamotoXGL_mem_P h).2 ⟨hb, ?_⟩
  rw [ha, hc, hd]
  linear_combination ((d : K) + a * c) * (CharTwo.two_eq_zero : (2 : K) = 0)

@[expose] def tfc_xF (v : h.fixedField × h.fixedField × h.fixedField × h.fixedField) : Xg h :=
  ⟨miyamotoXGL h v.1 v.2.1 v.2.2.1 v.2.2.2,
    miyamotoUnipotent_le_SU h false false (tfc_mem_P h v.1 v.2.1 v.2.2.1 v.2.2.2)⟩

theorem tfc_coe_xF (v : h.fixedField × h.fixedField × h.fixedField × h.fixedField) :
    ((tfc_xF h v : Xg h) : GL (Fin 4) K) = miyamotoXGL h v.1 v.2.1 v.2.2.1 v.2.2.2 := rfl

theorem tfc_xF_injective : Function.Injective (tfc_xF h) := by
  intro v w e
  have e1 := congrArg (fun x : Xg h => (x : GL (Fin 4) K)) e
  obtain ⟨h1, h2, h3, h4⟩ := (miyamotoXGL_inj h).1 e1
  exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Prod.ext (Subtype.ext h3)
    (Subtype.ext h4)))

theorem tfc_xF_mem_Pfx (v : h.fixedField × h.fixedField × h.fixedField × h.fixedField) :
    tfc_xF h v ∈ Pfx h := by
  refine ⟨Subgroup.mem_subgroupOf.2 (tfc_mem_P h _ _ _ _), Subtype.ext ?_⟩
  rw [coe_miyamotoFieldAut_apply, tfc_coe_xF, glAut_miyamotoXGL]
  have ha : h.bar (v.1 : K) = v.1 := v.1.2
  have hb : h.bar (v.2.1 : K) = v.2.1 := v.2.1.2
  have hc : h.bar (v.2.2.1 : K) = v.2.2.1 := v.2.2.1.2
  have hd : h.bar (v.2.2.2 : K) = v.2.2.2 := v.2.2.2.2
  simp only [miyamotoBarEquiv_apply, ha, hb, hc, hd]

theorem tfc_exists_xF {g : Xg h} (hg : g ∈ Pfx h) : ∃ v, tfc_xF h v = g := by
  obtain ⟨hgP, hgf⟩ := hg
  obtain ⟨a, b, c, d, hb, hd, e⟩ := (mem_P h).1 (Subgroup.mem_subgroupOf.1 hgP)
  have e2 := congrArg (fun x : Xg h => (x : GL (Fin 4) K)) hgf
  simp only [coe_miyamotoFieldAut_apply, e, glAut_miyamotoXGL, miyamotoBarEquiv_apply] at e2
  obtain ⟨h1, h2, h3, h4⟩ := (miyamotoXGL_inj h).1 e2
  exact ⟨(⟨a, h1⟩, ⟨b, h2⟩, ⟨c, h3⟩, ⟨d, h4⟩), Subtype.ext e.symm⟩

theorem tfc_mem_Pfx_iff {g : Xg h} : g ∈ Pfx h ↔ ∃ v, tfc_xF h v = g :=
  ⟨tfc_exists_xF h, fun ⟨v, hv⟩ => hv ▸ tfc_xF_mem_Pfx h v⟩

theorem tfc_card_Pfx : Nat.card (Pfx h) = (2 ^ f) ^ 4 := by
  have key := card_eq_of_param (H := Pfx h) (tfc_xF h) (tfc_xF_injective h)
    (fun _ => tfc_mem_Pfx_iff h)
  rw [key, Nat.card_prod, Nat.card_prod, Nat.card_prod, h.card_fixedField]
  ring

theorem tfc_comm_z1X {s : Xg h} (hs : s ∈ Psy h) : s * z1X h = z1X h * s := by
  have hz : (z1X h : GL (Fin 4) K) ∈ CFSG.centerIn (miyamotoP h) := by
    rw [centerIn_miyamotoP]
    exact z1X_mem_ZX h
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hz.2 _ (Subgroup.mem_subgroupOf.1 hs))

theorem tfc_comm_z2X_A1X {s : Xg h} (hs : s ∈ A1X h) : s * z2X h = z2X h * s := by
  obtain ⟨b, c, d, hb, hd, e⟩ := (mem_A1 h).1 (Subgroup.mem_subgroupOf.1 hs)
  have hc : ⁅miyamotoXGL h 0 b c d, miyamotoXGL h 0 0 1 0⁆ = 1 := by
    rw [miyamotoXGL_commutator h hb (map_zero _), ← miyamotoXGL_zero h, miyamotoXGL_inj]
    exact ⟨rfl, rfl, by simp, by simp⟩
  exact Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_z2X, e]
    exact commutatorElement_eq_one_iff_mul_comm.1 hc)

@[expose] def tfc_u : Xg h := tfc_xF h (1, 0, 0, 0)

theorem tfc_u_mem_Psy : tfc_u h ∈ Psy h := Subgroup.mem_subgroupOf.2 (tfc_mem_P h 1 0 0 0)

theorem tfc_u_not_mem_A1X : tfc_u h ∉ A1X h := by
  intro hu
  have := ((miyamotoXGL_mem_A1 h).1 (Subgroup.mem_subgroupOf.1 hu)).1
  exact one_ne_zero this

theorem tfc_comm_z2X_u : tfc_u h * z2X h = z2X h * tfc_u h := by
  have hc : ⁅miyamotoXGL h 1 0 0 0, miyamotoXGL h 0 0 1 0⁆ = 1 := by
    rw [miyamotoXGL_commutator h (map_zero _) (map_zero _), ← miyamotoXGL_zero h,
      miyamotoXGL_inj]
    refine ⟨rfl, rfl, by simp, ?_⟩
    simp [CharTwo.add_self_eq_zero]
  exact Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_z2X]
    exact commutatorElement_eq_one_iff_mul_comm.1 hc)

end CFSG.Quasithin.H13.F431.Un.OL
