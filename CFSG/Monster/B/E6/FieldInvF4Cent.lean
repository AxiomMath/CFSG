module

public import CFSG.Monster.B.E6.FieldInvF4Levi
public import CFSG.Monster.B.E6.FieldInvF4Radical

public noncomputable section

namespace CFSG.Monster.B.E6.FieldInvF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

theorem stdRadical_firstJ_le_stdGroup :
    stdRadical firstJ ≤ stdGroup :=
  (stdRadical_le_nativeParabolic firstJ).trans (nativeParabolic_le_stdGroup firstJ)

theorem stdLevi_firstJ_le_stdGroup :
    stdLevi firstJ ≤ stdGroup :=
  (stdLevi_le_nativeParabolic two_mem_firstJ).trans (nativeParabolic_le_stdGroup firstJ)

abbrev leviJ :
    Subgroup (ModGL Tag.E6 K) := stdLevi firstJ ⊓ groupJ

abbrev radJ :
    Subgroup (ModGL Tag.E6 K) := stdRadical firstJ ⊓ groupJ

theorem mem_leviJ
    {g : ModGL Tag.E6 K} : g ∈ leviJ ↔ g ∈ stdLevi firstJ ∧ betaGL g = g :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, stdLevi_firstJ_le_stdGroup h.1, h.2⟩⟩

theorem mem_radJ
    {g : ModGL Tag.E6 K} : g ∈ radJ ↔ g ∈ stdRadical firstJ ∧ betaGL g = g :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, stdRadical_firstJ_le_stdGroup h.1, h.2⟩⟩

theorem card_leviJ :
    Nat.card leviJ = 1451520 := by
  rw [← card_leviFix]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x, (mem_leviJ.mp x.2).1⟩, (mem_leviJ.mp x.2).2⟩
      invFun := fun l => ⟨l.1, mem_leviJ.mpr ⟨l.1.2, l.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

abbrev centJ :
    Subgroup (ModGL Tag.E6 K) := groupJ ⊓ Subgroup.centralizer {rootInvM}

theorem mem_centJ_iff
    {g : ModGL Tag.E6 K} :
    g ∈ centJ ↔ g ∈ nativeParabolic firstJ ∧ betaGL g = g := by
  constructor
  · rintro ⟨hJ, hc⟩
    refine ⟨?_, hJ.2⟩
    rw [← centralizer_inf_stdGroup]
    exact ⟨hc, hJ.1⟩
  · rintro ⟨hP, hβ⟩
    refine ⟨⟨nativeParabolic_le_stdGroup firstJ hP, hβ⟩, nativeParabolic_firstJ_le_centralizer hP⟩

theorem centJ_le_groupJ :
    centJ ≤ groupJ := inf_le_left

theorem radJ_le_centJ :
    radJ ≤ centJ := fun _ h =>
  mem_centJ_iff.mpr ⟨stdRadical_le_nativeParabolic firstJ h.1, h.2.2⟩

theorem leviJ_le_centJ :
    leviJ ≤ centJ := fun _ h =>
  mem_centJ_iff.mpr ⟨stdLevi_le_nativeParabolic two_mem_firstJ h.1, h.2.2⟩

@[expose] def centMul
    (p : radJ × leviJ) : centJ :=
  ⟨p.1 * p.2, mul_mem (radJ_le_centJ p.1.2) (leviJ_le_centJ p.2.2)⟩

theorem centMul_injective :
    Function.Injective centMul := by
  rintro ⟨q, l⟩ ⟨q', l'⟩ h
  have e : (q : ModGL Tag.E6 K) * l = q' * l' := congrArg Subtype.val h
  have hm : (q' : ModGL Tag.E6 K)⁻¹ * q = l' * (l : ModGL Tag.E6 K)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
  have h1 : (q' : ModGL Tag.E6 K)⁻¹ * q ∈ stdRadical firstJ ⊓ stdLevi firstJ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (mem_radJ.mp q'.2).1) (mem_radJ.mp q.2).1,
      hm ▸ mul_mem (mem_leviJ.mp l'.2).1 (inv_mem (mem_leviJ.mp l.2).1)⟩
  rw [stdRadical_inf_stdLevi, Subgroup.mem_bot, inv_mul_eq_one] at h1
  have h2 : (l : ModGL Tag.E6 K) = l' := by
    rw [h1] at e
    exact mul_left_cancel e
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2)

theorem centMul_surjective :
    Function.Surjective centMul := by
  rintro ⟨g, hg⟩
  obtain ⟨hP, hβ⟩ := mem_centJ_iff.mp hg
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hgql⟩, huniq⟩ := existsUnique_stdRadical_mul_stdLevi two_mem_firstJ hP
  have h := huniq (betaGL q, betaGL l)
    ⟨betaGL_mem_stdRadical hq, betaGL_mem_stdLevi hl, by rw [← map_mul, ← hgql, hβ]⟩
  have hq' : betaGL q = q := congrArg Prod.fst h
  have hl' : betaGL l = l := congrArg Prod.snd h
  exact ⟨(⟨q, mem_radJ.mpr ⟨hq, hq'⟩⟩, ⟨l, mem_leviJ.mpr ⟨hl, hl'⟩⟩), Subtype.ext hgql.symm⟩

theorem bijective_centMul :
    Function.Bijective centMul :=
  ⟨centMul_injective, centMul_surjective⟩

theorem card_centJ :
    Nat.card centJ = 47563407360 := by
  rw [← Nat.card_eq_of_bijective centMul bijective_centMul, Nat.card_prod,
    card_stdRadical_inf_groupJ, card_leviJ]
  norm_num

end CFSG.Monster.B.E6.FieldInvF4
