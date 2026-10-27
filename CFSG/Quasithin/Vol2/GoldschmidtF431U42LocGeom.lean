module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLine
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocKer

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

@[expose] def Vconj (m : Y) : Subgroup Y := Vsub.map (MulAut.conj m).toMonoidHom

theorem mem_Vconj {m a : Y} : a ∈ Vconj m ↔ m⁻¹ * a * m ∈ Vsub := by
  simp only [Vconj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [mul_assoc] using hv
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem Vconj_eq_closure (m : Y) :
    Vconj m = Subgroup.closure {g | ∃ q : Fin 45, q ∈ (m : P45) '' L0S ∧ g = sY q} := by
  rw [Vconj, Vsub, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨(m : P45) p, ⟨p, hp, rfl⟩, sY_conj m p⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, sY_conj m p⟩

theorem Vconj_eq_of_image_eq {m m' : Y}
    (h : (m : P45) '' L0S = (m' : P45) '' L0S) : Vconj m = Vconj m' := by
  rw [Vconj_eq_closure, Vconj_eq_closure, h]

theorem sY_mem_Vconj {m : Y} {q : Fin 45}
    (hq : q ∈ (m : P45) '' L0S) : sY q ∈ Vconj m := by
  rw [Vconj_eq_closure]
  exact Subgroup.subset_closure ⟨q, hq, rfl⟩

theorem sY_mem_Vsub {p : Fin 45} (hp : p ∈ L0S) :
    sY p ∈ Vsub := Subgroup.subset_closure ⟨p, hp, rfl⟩

theorem comp_tp_zero_fifteen : comp (tpTab.getD 0 []) (tpTab.getD 15 []) = t0L := by
  decide +kernel

theorem tY_eq_sY : tY = sY 0 * sY 15 := by
  refine Subtype.ext (eq_of_repL repL_t45 ?_)
  rw [← comp_tp_zero_fifteen]
  exact repL_mul (repL_sY 0) (repL_sY 15)

theorem tY_mem_Vsub : tY ∈ Vsub := by
  rw [tY_eq_sY]
  exact Vsub.mul_mem (sY_mem_Vsub zero_mem_L0S) (sY_mem_Vsub ((mem_L0S_iff 15).2 (by simp)))

theorem sY_inj {p q : Fin 45} (h : sY p = sY q) : p = q :=
  sT_injective (congrArg Subtype.val h)

theorem orderOf_eq_two_of_sq {a : Y} (h : a * a = 1) (h1 : a ≠ 1) : orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem comm_of_mem_P1 {a : Y} (haP : a ∈ P1) :
    xY * a * xY⁻¹ = a := by
  have h : a ∈ Subgroup.centralizer ({xY} : Set Y) := by rw [centralizer_x]; exact haP
  have h' := Subgroup.mem_centralizer_singleton_iff.1 h
  calc xY * a * xY⁻¹ = a * xY * xY⁻¹ := by rw [← h']
    _ = a := by group

theorem fixSet_eq_of_mem_Vconj
    {m a : Y} (ha : a ∈ Vconj m) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hx : ¬ IsConj xY a) :
    fixSet a = (m : P45) '' L0S := by
  have hvV : m⁻¹ * a * m ∈ Vsub := mem_Vconj.1 ha
  have hav : a = m * (m⁻¹ * a * m) * m⁻¹ := by group
  have hv2 : (m⁻¹ * a * m) * (m⁻¹ * a * m) = 1 := by
    calc (m⁻¹ * a * m) * (m⁻¹ * a * m) = m⁻¹ * (a * a) * m := by group
      _ = 1 := by rw [ha2]; group
  have hv1 : m⁻¹ * a * m ≠ 1 := by
    intro h
    apply ha1
    rw [hav, h]
    group
  have hxv : ¬ IsConj xY (m⁻¹ * a * m) := fun h => hx (h.trans (isConj_iff.2 ⟨m, hav.symm⟩))
  rcases classes (orderOf_eq_two_of_sq hv2 hv1) with h | h
  · exact absurd h hxv
  · have hcard := fixSet_eq_image_of_isConj_tY h
    have hsub : L0S ⊆ fixSet (m⁻¹ * a * m) := fun p hp => Vsub_fix hvV p hp
    have heq : L0S = fixSet (m⁻¹ * a * m) :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, L0S_ncard]) (Set.toFinite _)
    rw [hav, fixSet_conj, ← heq]

theorem exists_P1_conj_of_involution
    {a : Y} (haP : a ∈ P1) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hx : ¬ IsConj xY a) :
    ∃ m ∈ P1, a ∈ Vconj m := by
  rcases classes (orderOf_eq_two_of_sq ha2 ha1) with h | h
  · exact absurd h hx
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hac : a ∈ Vconj c := by
    rw [mem_Vconj, ← hc]
    simpa [mul_assoc] using tY_mem_Vsub
  have hfix : fixSet a = (c : P45) '' L0S := by rw [← hc, fixSet_conj, fixSet_tY]
  have hstab : (sY 0 : P45) '' ((c : P45) '' L0S) = (c : P45) '' L0S := by
    have h2 := fixSet_conj xY a
    rw [comm_of_mem_P1 haP, hfix] at h2
    rw [sY_zero]
    exact h2.symm
  have h0 := mem_line_of_fix hstab
  obtain ⟨j, hj, hjc⟩ := exists_line_eq_image c
  have h0j : (0 : Fin 45) ∈ lnS j := hjc ▸ h0
  obtain ⟨m, hmP, hm⟩ := exists_P1_line hj h0j
  refine ⟨m, hmP, ?_⟩
  rw [Vconj_eq_of_image_eq (hm.trans hjc.symm)]
  exact hac

theorem exists_P1_conj_of_transvection
    {a : Y} (haP : a ∈ P1) (ha : IsConj xY a) : ∃ m ∈ P1, ∃ q ∈ L0S, a = m * sY q * m⁻¹ := by
  obtain ⟨q0, rfl⟩ := exists_sY_of_isConj ha
  have h1 : sY ((xY : P45) q0) = sY q0 := by
    rw [← sY_conj]
    exact comm_of_mem_P1 haP
  have h2 : x45 q0 = q0 := sY_inj h1
  obtain ⟨j, hj, h0, hq0⟩ := exists_line_of_fix_x h2
  obtain ⟨m, hmP, hm⟩ := exists_P1_line hj h0
  rw [← hm] at hq0
  obtain ⟨q, hq, rfl⟩ := hq0
  exact ⟨m, hmP, q, hq, (sY_conj m q).symm⟩

theorem mem_Vconj_of_comm
    {m a a' : Y} (ha : a ∈ Vconj m) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hx : ¬ IsConj xY a)
    (ha' : IsConj xY a') (hcomm : a * a' = a' * a) : a' ∈ Vconj m := by
  obtain ⟨q, rfl⟩ := exists_sY_of_isConj ha'
  have hfix := fixSet_eq_of_mem_Vconj ha ha2 ha1 hx
  have h1 : sY q * a * (sY q)⁻¹ = a := by
    calc sY q * a * (sY q)⁻¹ = a * sY q * (sY q)⁻¹ := by rw [← hcomm]
      _ = a := by group
  have h2 := fixSet_conj (sY q) a
  rw [h1, hfix] at h2
  exact sY_mem_Vconj (mem_line_of_fix h2.symm)

end CFSG.Quasithin.H13.F431.U42
