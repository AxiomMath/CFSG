module

public import CFSG.Quasithin.Recognition.WBN.Weyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSet

import CFSG.LocalAnalysis.EvenBN.U4.RootF1Abelian
import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoB
import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYam
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Torus

public section

namespace CFSG.Quasithin.WBN

open CFSG.Quasithin.H13.F431.Un.OL CFSG.LocalAnalysis CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

private theorem bar_eq_of_pow_sub_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {a : Kˣ} (ha : a ^ (2 ^ f - 1) = 1) :
    h.bar (a : K) = (a : K) := by
  rw [h.bar_apply]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have ha' : (a : K) ^ (2 ^ f - 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ha
    simpa using this
  calc (a : K) ^ 2 ^ f = (a : K) ^ (2 ^ f - 1) * (a : K) := by
        rw [← pow_succ, Nat.sub_add_cancel hq]
    _ = 1 * (a : K) := by rw [ha']
    _ = (a : K) := one_mul _

private theorem conj_r2r1_miyamotoIHom {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (p : Kˣ × Kˣ) :
    (miyamotoR2 K * miyamotoR1 K) * miyamotoIHom h p * (miyamotoR2 K * miyamotoR1 K)⁻¹ =
      miyamotoIHom h (p.2, (Units.map h.bar.toMonoidHom p.1)⁻¹) := by
  have hr1 : (miyamotoR1 K)⁻¹ = miyamotoR1 K :=
    inv_eq_of_mul_eq_one_right (miyamotoR1_mul_self (K := K))
  have hr2 : (miyamotoR2 K)⁻¹ = miyamotoR2 K :=
    inv_eq_of_mul_eq_one_right (miyamotoR2_mul_self (K := K))
  have h1 : miyamotoR1 K * miyamotoIHom h p * (miyamotoR1 K)⁻¹ =
      miyamotoIHom h p.swap := by
    simpa [hr1] using miyamotoR1_conj_miyamotoIHom h p
  have h2 : miyamotoR2 K * miyamotoIHom h p.swap * (miyamotoR2 K)⁻¹ =
      miyamotoIHom h (p.2, (Units.map h.bar.toMonoidHom p.1)⁻¹) := by
    simpa [hr2] using miyamotoR2_conj_miyamotoIHom h p.swap
  calc (miyamotoR2 K * miyamotoR1 K) * miyamotoIHom h p *
        (miyamotoR2 K * miyamotoR1 K)⁻¹
      = miyamotoR2 K * (miyamotoR1 K * miyamotoIHom h p * (miyamotoR1 K)⁻¹) *
          (miyamotoR2 K)⁻¹ := by group
    _ = miyamotoR2 K * miyamotoIHom h p.swap * (miyamotoR2 K)⁻¹ := by rw [h1]
    _ = miyamotoIHom h (p.2, (Units.map h.bar.toMonoidHom p.1)⁻¹) := h2

private theorem conj_r2r1_sq_miyamotoIHom {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (p : Kˣ × Kˣ) :
    ((miyamotoR2 K * miyamotoR1 K) ^ 2) * miyamotoIHom h p *
        (((miyamotoR2 K * miyamotoR1 K) ^ 2))⁻¹ =
      miyamotoIHom h ((Units.map h.bar.toMonoidHom p.1)⁻¹,
        (Units.map h.bar.toMonoidHom p.2)⁻¹) := by
  have h1 := conj_r2r1_miyamotoIHom h p
  have h2 := conj_r2r1_miyamotoIHom h (p.2, (Units.map h.bar.toMonoidHom p.1)⁻¹)
  calc ((miyamotoR2 K * miyamotoR1 K) ^ 2) * miyamotoIHom h p *
        (((miyamotoR2 K * miyamotoR1 K) ^ 2))⁻¹
      = (miyamotoR2 K * miyamotoR1 K) *
          ((miyamotoR2 K * miyamotoR1 K) * miyamotoIHom h p *
            (miyamotoR2 K * miyamotoR1 K)⁻¹) * (miyamotoR2 K * miyamotoR1 K)⁻¹ := by
        rw [pow_two]; group
    _ = (miyamotoR2 K * miyamotoR1 K) *
          miyamotoIHom h (p.2, (Units.map h.bar.toMonoidHom p.1)⁻¹) *
          (miyamotoR2 K * miyamotoR1 K)⁻¹ := by rw [h1]
    _ = miyamotoIHom h ((Units.map h.bar.toMonoidHom p.1)⁻¹,
          (Units.map h.bar.toMonoidHom p.2)⁻¹) := h2

private theorem conj_r2r1_sq_miyamotoIHom_eq_inv {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (p : Kˣ × Kˣ)
    (hp1 : p.1 ^ (2 ^ f - 1) = 1) (hp2 : p.2 ^ (2 ^ f - 1) = 1) :
    ((miyamotoR2 K * miyamotoR1 K) ^ 2) * miyamotoIHom h p *
        (((miyamotoR2 K * miyamotoR1 K) ^ 2))⁻¹ = (miyamotoIHom h p)⁻¹ := by
  rw [conj_r2r1_sq_miyamotoIHom h p]
  have hb1 : Units.map h.bar.toMonoidHom p.1 = p.1 :=
    Units.ext (by simpa using bar_eq_of_pow_sub_one h hp1)
  have hb2 : Units.map h.bar.toMonoidHom p.2 = p.2 :=
    Units.ext (by simpa using bar_eq_of_pow_sub_one h hp2)
  rw [hb1, hb2, ← map_inv]
  rfl

private theorem mem_normalizer_IX_of_conj {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {r : GL (Fin 4) K} (hr : r ∈ gramSU h (miyamotoJ4 K))
    (hrinv : r⁻¹ = r) (hconj : ∀ g ∈ miyamotoI h, r⁻¹ * g * r ∈ miyamotoI h) :
    (⟨r, hr⟩ : Xg h) ∈ Subgroup.normalizer (IX h : Set (Xg h)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyI : (y : GL (Fin 4) K) ∈ miyamotoI h := hy
    show ((⟨r, hr⟩ * y * (⟨r, hr⟩ : Xg h)⁻¹ : Xg h) : GL (Fin 4) K) ∈ miyamotoI h
    change r * (y : GL (Fin 4) K) * r⁻¹ ∈ miyamotoI h
    simpa [hrinv] using hconj _ hyI
  · intro hy
    show (y : GL (Fin 4) K) ∈ miyamotoI h
    have hyI : ((⟨r, hr⟩ * y * (⟨r, hr⟩ : Xg h)⁻¹ : Xg h) : GL (Fin 4) K) ∈
        miyamotoI h := hy
    change r * (y : GL (Fin 4) K) * r⁻¹ ∈ miyamotoI h at hyI
    have hh := hconj _ hyI
    change r⁻¹ * (r * (y : GL (Fin 4) K) * r⁻¹) * r ∈ miyamotoI h at hh
    have hsq : r * r = 1 := by
      simpa [hrinv] using mul_inv_cancel r
    have e : r⁻¹ * (r * (y : GL (Fin 4) K) * r⁻¹) * r = (y : GL (Fin 4) K) := by
      rw [hrinv]
      calc r * (r * (y : GL (Fin 4) K) * r) * r =
          (r * r) * (y : GL (Fin 4) K) * (r * r) := by group
        _ = (y : GL (Fin 4) K) := by rw [hsq, one_mul, mul_one]
    rwa [e] at hh

private theorem r2X_mem_normalizer_IX {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) [CharP K 2] :
    r2X h ∈ Subgroup.normalizer (IX h : Set (Xg h)) :=
  mem_normalizer_IX_of_conj h (miyamotoR2_mem_gramSU h)
    (inv_eq_of_mul_eq_one_right (miyamotoR2_mul_self (K := K)))
    (fun g hg => miyamotoR2_conj_mem_I h hg)

private theorem r1X_mem_normalizer_IX {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) [CharP K 2] :
    r1X h ∈ Subgroup.normalizer (IX h : Set (Xg h)) :=
  mem_normalizer_IX_of_conj h (miyamotoR1_mem_gramSU h)
    (inv_eq_of_mul_eq_one_right (miyamotoR1_mul_self (K := K)))
    (fun g hg => miyamotoR1_conj_mem_I h hg)

theorem invertsByWeyl_u4 {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    [CharP K 2] :
    InvertsByWeyl (CFSG.Quasithin.H13.F431.Un.OL.Pt h) (CFSG.Quasithin.H13.F431.Un.OL.Ln h)
      (2 ^ f - 1) := by
  haveI : Finite (Xg h) := finite_gramSU_miyamotoJ4 h
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨by norm_num, by have := h.one_le; omega⟩) odd_one
  have hIX : Nat.card (IX h) = Nat.card (miyamotoI h) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (miyamotoI_le_gramSU h)).toEquiv
  refine InvertsByWeyl.of_torus (U := Psy h) (H := IX h) hodd
    (isSylowTwoOf_Psy h).2.1 ?_ ?_ (hIX ▸ odd_card_miyamotoI h)
    (n₀ := r2X h) (n₁ := r1X h) (r2X_mem_Pt h) (r1X_mem_Ln h)
    (r2X_mem_normalizer_IX h) (r1X_mem_normalizer_IX h) 2 ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Psy_le_Pt_inf_Ln h)).2
      (Pt_inf_Ln_le_normalizer_Psy h)
  · rw [← normalizer_Psy_eq h]
    exact le_antisymm (normalizer_Psy_le h) (Pt_inf_Ln_le_normalizer_Psy h)
  · intro x hx hxm
    obtain ⟨p, -, hp⟩ := Subgroup.mem_map.mp
      (show (x : GL (Fin 4) K) ∈ (miyamotoIParam h).ker.map (miyamotoIHom h) from hx)
    have hxpow : (x : GL (Fin 4) K) ^ (2 ^ f - 1) = 1 := by
      rw [← Subgroup.coe_pow, hxm, Subgroup.coe_one]
    have hp1 : p ^ (2 ^ f - 1) = 1 := by
      apply miyamotoIHom_injective h
      rw [map_pow, hp, hxpow, map_one]
    have hp1' : p.1 ^ (2 ^ f - 1) = 1 := by
      have := congrArg (fun q : Kˣ × Kˣ => q.1) hp1
      simpa using this
    have hp2' : p.2 ^ (2 ^ f - 1) = 1 := by
      have := congrArg (fun q : Kˣ × Kˣ => q.2) hp1
      simpa using this
    apply Subtype.ext
    change ((miyamotoR2 K * miyamotoR1 K) ^ 2) * (x : GL (Fin 4) K) *
      (((miyamotoR2 K * miyamotoR1 K) ^ 2))⁻¹ = ((x : GL (Fin 4) K))⁻¹
    rw [← hp, conj_r2r1_sq_miyamotoIHom_eq_inv h p hp1' hp2']

theorem allInvertsByWeyl_u4 {f : ℕ} (hf : 2 ≤ f) :
    AllInvertsByWeyl (CFSG.Quasithin.IsLieOverTwo .PSU 4 f) (2 ^ f - 1) := by
  intro Y _ hY T M₁ M₂ hpair
  obtain ⟨K, hField, h, hChar, -, ⟨e⟩, S⟩ :=
    CFSG.Quasithin.H13.F431.Un.OL.exists_model_yamStd hf hY
  letI : Field K := hField
  letI : CharP K 2 := hChar
  haveI : Finite (CFSG.Quasithin.H13.F431.Un.OL.Xg h) :=
    CFSG.LocalAnalysis.EvenBN.U4.finite_gramSU_miyamotoJ4 h
  exact InvertsByWeyl.of_yamStd S (invertsByWeyl_u4 h) e hpair

end CFSG.Quasithin.WBN
