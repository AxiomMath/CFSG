module

public import CFSG.Quasithin.H13.HSLocOrb
public import CFSG.RankThree.Native.HSMcLAut

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native


@[expose] noncomputable def k1 : PG := wAB ga gb (kWords.getD 0 [])

@[expose] noncomputable def k2 : PG := wAB ga gb (kWords.getD 1 [])

theorem kTabs_eq : kTabs = #[tabW 100 AB (kWords.getD 0 []), tabW 100 AB (kWords.getD 1 [])] := rfl

theorem kWords0_mem : kWords.getD 0 [] ∈ kWords := by decide +kernel

theorem kWords1_mem : kWords.getD 1 [] ∈ kWords := by decide +kernel

theorem T_k1 : T k1 = kTabs.getD 0 #[] := by
  rw [k1, T_wAB (kWords_lt _ kWords0_mem), kTabs_eq]
  rfl

theorem T_k2 : T k2 = kTabs.getD 1 #[] := by
  rw [k2, T_wAB (kWords_lt _ kWords1_mem), kTabs_eq]
  rfl

theorem k_props :
    (k1 ∈ Mg ∧ act 100 k1 0 = 0 ∧ act 100 k1 1 = 1) ∧
      (k2 ∈ Mg ∧ act 100 k2 0 = 0 ∧ act 100 k2 1 = 1) := by
  obtain ⟨-, -, -, -, hkm, -⟩ := Certificates.certificate589206
  simp only [kInM, Array.all_eq_true', Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hkm
  have h1 := hkm (tabW 100 AB (kWords.getD 0 [])) (by rw [kTabs_eq]; simp)
  have h2 := hkm (tabW 100 AB (kWords.getD 1 [])) (by rw [kTabs_eq]; simp)
  have e1 : tabW 100 AB (kWords.getD 0 []) = T k1 := (T_wAB (kWords_lt _ kWords0_mem)).symm
  have e2 : tabW 100 AB (kWords.getD 1 []) = T k2 := (T_wAB (kWords_lt _ kWords1_mem)).symm
  rw [e1] at h1
  rw [e2] at h2
  simp only [img_T] at h1 h2
  exact ⟨⟨(mSpec.mem_iff k1).mpr h1.2, h1.1.1, h1.1.2⟩, ⟨(mSpec.mem_iff k2).mpr h2.2, h2.1.1, h2.1.2⟩⟩

theorem R_cases {r : Equiv.Perm (Fin 100)} (hr : r ∈ hs100R) :
    r ∈ hs100P ∨ ∃ p ∈ hs100P, r = hs100U * p := by
  have hu2 : hs100U * hs100U = 1 := by rw [← sq]; exact hs100U_sq
  have huinv : hs100U⁻¹ = hs100U := inv_eq_of_mul_eq_one_right hu2
  have hconj : ∀ p ∈ hs100P, hs100U⁻¹ * p * hs100U ∈ hs100P := by
    intro p hp
    have := hs100U_conj_mem hp
    rw [huinv] at this ⊢
    exact this
  unfold hs100R at hr
  induction hr using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Or.inl mem_hs100A
    · exact Or.inl mem_hs100B
    · exact Or.inr ⟨1, hs100P.one_mem, (mul_one _).symm⟩
  | one => exact Or.inl hs100P.one_mem
  | mul y z _ _ hy hz =>
    rcases hy with hy | ⟨p, hp, rfl⟩ <;> rcases hz with hz | ⟨q, hq, rfl⟩
    · exact Or.inl (hs100P.mul_mem hy hz)
    · refine Or.inr ⟨(hs100U⁻¹ * y * hs100U) * q, hs100P.mul_mem (hconj y hy) hq, ?_⟩
      group
    · exact Or.inr ⟨p * z, hs100P.mul_mem hp hz, by rw [mul_assoc]⟩
    · refine Or.inl ?_
      have := hs100P.mul_mem (hs100U_conj_mem hp) hq
      rw [show hs100U * p * (hs100U * q) = hs100U * p * hs100U⁻¹ * q by rw [huinv]; group]
      exact this
  | inv y _ hy =>
    rcases hy with hy | ⟨p, hp, rfl⟩
    · exact Or.inl (hs100P.inv_mem hy)
    · refine Or.inr ⟨hs100U⁻¹ * p⁻¹ * hs100U, hconj _ (hs100P.inv_mem hp), ?_⟩
      calc (hs100U * p)⁻¹ = p⁻¹ * hs100U⁻¹ := mul_inv_rev _ _
        _ = p⁻¹ * hs100U := by rw [huinv]
        _ = hs100U * (hs100U⁻¹ * p⁻¹ * hs100U) := by group

theorem kU_lt : kU < 3850 := by decide

theorem T_hs100U : T hs100U = uTab := by
  refine T_eq_of_smul (size_hs100Arr 15) fun i => ?_
  rw [Equiv.Perm.smul_def]
  exact rep_hs100U i

theorem uinv_orbit {f : ℕ} (hf : f ∈ F0) :
    ∃ f' ∈ F0, act 100 hs100U⁻¹ f' = act 100 (treeElt kU) f := by
  obtain ⟨-, -, -, -, -, hku, -⟩ := Certificates.certificate589206
  simp only [kUOK, beq_iff_eq] at hku
  rw [orbF_getD kU_lt] at hku
  have hx : act 100 (treeElt kU) f < 100 := act_lt _ (F0_lt f hf)
  have hmem := (mem_of_maskOf_eq hku hx).mp (List.mem_map_of_mem (f := act 100 (treeElt kU)) hf)
  obtain ⟨f', hf', hf'e⟩ := List.mem_map.mp hmem
  refine ⟨f', hf', ?_⟩
  rw [← img_T, T_inv, T_hs100U]
  exact hf'e

theorem T_coe (g : PG) : T (g : Equiv.Perm (Fin 100)) = T g := rfl

theorem w_pres :
    Pres ((hs100U : Equiv.Perm (Fin 100)) * ((treeElt kU : PG) : Equiv.Perm (Fin 100))) := by
  unfold Pres
  intro f hf
  obtain ⟨f', hf', he⟩ := uinv_orbit hf
  have hfl := F0_lt f hf
  have hg : act 100 ((treeElt kU : PG) : Equiv.Perm (Fin 100)) f = act 100 (treeElt kU) f := rfl
  rw [act_mul _ _ hfl, hg, ← he, ← act_mul _ _ (F0_lt f' hf'), mul_inv_cancel,
    act_one (F0_lt f' hf')]
  exact hf'

theorem R_step {r : Equiv.Perm (Fin 100)} (hr : r ∈ hs100R) (hpres : Pres r)
    (h1 : r * (k1 : Equiv.Perm (Fin 100)) = (k1 : Equiv.Perm (Fin 100)) * r)
    (h2 : r * (k2 : Equiv.Perm (Fin 100)) = (k2 : Equiv.Perm (Fin 100)) * r) : r = 1 := by
  obtain ⟨-, -, -, -, -, -, hcent, hcentw, -⟩ := Certificates.certificate589206
  simp only [centOK, List.all_eq_true] at hcent
  simp only [centWOK, List.all_eq_true] at hcentw
  rcases R_cases hr with hrP | ⟨p, hp, rfl⟩
  ·
    let q : PG := ⟨r, hrP⟩
    have hqP : Pres q := hpres
    have hqM : q ∈ Mg := mem_Mg_iff.mpr hqP
    have hc1 : commT (T q) (kTabs.getD 0 #[]) = true := by
      rw [← T_k1]; exact commT_iff.mpr (Subtype.ext h1)
    have hc2 : commT (T q) (kTabs.getD 1 #[]) = true := by
      rw [← T_k2]; exact commT_iff.mpr (Subtype.ext h2)
    have h := hcent (T q) ((mSpec.mem_iff q).mp hqM)
    simp only [hc1, hc2, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    have hq1 : q = 1 := eq_of_T (h.trans T_one.symm)
    exact congrArg Subtype.val hq1
  ·
    let p' : PG := ⟨p, hp⟩
    let g : PG := treeElt kU
    let m : PG := g⁻¹ * p'
    have hw := w_pres
    have hmP : Pres (m : Equiv.Perm (Fin 100)) := by
      have := Pres.mul (Pres.inv hw) hpres
      have e : ((hs100U * (g : Equiv.Perm (Fin 100)))⁻¹ * (hs100U * p)) = (m : Equiv.Perm (Fin 100)) := by
        simp only [m, p', g, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [e] at this
    have hmM : m ∈ Mg := mem_Mg_iff.mpr (by unfold Pres at hmP ⊢; exact hmP)
    have hrm : hs100U * p = (hs100U * (g : Equiv.Perm (Fin 100))) * (m : Equiv.Perm (Fin 100)) := by
      simp only [m, p', g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hT : T (hs100U * p) = compT wTab (T m) := by
      rw [hrm, T_mul, T_mul, T_hs100U, T_coe, wTab, treeElems_getD kU_lt]
      rfl
    have hc1 : commT (compT wTab (T m)) (kTabs.getD 0 #[]) = true := by
      rw [← hT, ← T_k1, ← T_coe]; exact commT_iff.mpr h1
    have hc2 : commT (compT wTab (T m)) (kTabs.getD 1 #[]) = true := by
      rw [← hT, ← T_k2, ← T_coe]; exact commT_iff.mpr h2
    have h := hcentw (T m) ((mSpec.mem_iff m).mp hmM)
    rw [hc1, hc2] at h
    simp at h

end CFSG.Quasithin.H13.LocDbl.HSLoc
