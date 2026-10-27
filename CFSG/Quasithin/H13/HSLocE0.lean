module

public import CFSG.Quasithin.H13.HSLocNorm
public import Certificates.Certificate589207

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native CFSG.Open


@[expose] def E0g : Subgroup PG where
  carrier := {z | ∀ f ∈ F0, act 100 z f = f}
  one_mem' := fun f hf => act_one (F0_lt f hf)
  mul_mem' {a b} ha hb f hf := by
    rw [act_mul _ _ (F0_lt f hf), hb f hf, ha f hf]
  inv_mem' {a} ha f hf := by
    have h := ha f hf
    have := act_inv_act a (F0_lt f hf)
    rwa [h] at this

theorem E0g_le_Mg : E0g ≤ Mg := fun z hz => mem_Mg_iff.mpr fun f hf => by
  rw [hz f hf]; exact hf

theorem mem_e0Elems_iff {t : Array ℕ} : t ∈ e0Elems ↔ ∃ z ∈ E0g, T z = t := by
  constructor
  · intro ht
    rw [e0Elems, List.mem_filter] at ht
    obtain ⟨z, hzM, hzt⟩ := mSpec.exists_of_mem t ht.1
    refine ⟨z, fun f hf => ?_, hzt⟩
    have h := List.all_eq_true.mp ht.2 f hf
    rw [← hzt, img_T] at h
    exact beq_iff_eq.mp h
  · rintro ⟨z, hz, rfl⟩
    rw [e0Elems, List.mem_filter]
    refine ⟨(mSpec.mem_iff z).mp (E0g_le_Mg hz), ?_⟩
    exact List.all_eq_true.mpr fun f hf => by rw [img_T]; exact beq_iff_eq.mpr (hz f hf)

theorem e0OK_parts : e0Elems.length = 16 ∧ (∀ t ∈ cent0List, t ∈ e0Elems) ∧ outList.length ≤ 16 := by
  have h := Certificates.certificate589207.1
  simp only [e0OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_E0g_le : Nat.card E0g ≤ 16 := by
  classical
  haveI : Fintype PG := Fintype.ofFinite PG
  let S : Finset PG := Finset.univ.filter (· ∈ E0g)
  have hS : S.card = Nat.card E0g := by
    simp [S, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : S.image T ⊆ e0Elems.toFinset := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    have hz' : z ∈ E0g := by simpa [S] using hz
    exact List.mem_toFinset.mpr (mem_e0Elems_iff.mpr ⟨z, hz', rfl⟩)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b hab => eq_of_T hab)] at hc
  have := List.toFinset_card_le e0Elems
  have hl := e0OK_parts.1
  omega

theorem E0g_conj_eq {E : Subgroup PG} {X : PG} (hX : HasFix E X) (hEcard : Nat.card E = 16) :
    E.map (MulAut.conj X⁻¹).toMonoidHom = E0g := by
  have hle : E.map (MulAut.conj X⁻¹).toMonoidHom ≤ E0g := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    intro f hf
    have e : (MulAut.conj X⁻¹).toMonoidHom z = X⁻¹ * z * X := by simp [MulAut.conj_apply]
    rw [e]
    have hfl := F0_lt f hf
    have hq : act 100 X f < 100 := act_lt _ hfl
    have hfix := (hX _ hq).mpr (List.mem_map_of_mem hf) z hz
    rw [act_conj' X z hfl, hfix, act_inv_act X hfl]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj X⁻¹).injective, hEcard]
  exact card_E0g_le

theorem R_pres_cases {r : Equiv.Perm (Fin 100)} (hr : r ∈ hs100R) (hpres : Pres r) :
    (∃ q : PG, q ∈ Mg ∧ r = (q : Equiv.Perm (Fin 100))) ∨
      ∃ m : PG, m ∈ Mg ∧
        r = hs100U * ((treeElt kU : PG) : Equiv.Perm (Fin 100)) * (m : Equiv.Perm (Fin 100)) := by
  rcases R_cases hr with hrP | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨⟨r, hrP⟩, mem_Mg_iff.mpr hpres, rfl⟩
  · right
    let p' : PG := ⟨p, hp⟩
    let g : PG := treeElt kU
    let m : PG := g⁻¹ * p'
    have hw := w_pres
    have hmP : Pres (m : Equiv.Perm (Fin 100)) := by
      have := Pres.mul (Pres.inv hw) hpres
      have e : ((hs100U * (g : Equiv.Perm (Fin 100)))⁻¹ * (hs100U * p)) =
          (m : Equiv.Perm (Fin 100)) := by
        simp only [m, p', g, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [e] at this
    refine ⟨m, mem_Mg_iff.mpr (by unfold Pres at hmP ⊢; exact hmP), ?_⟩
    simp only [m, p', g, Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem T_wm (m : PG) :
    T (hs100U * ((treeElt kU : PG) : Equiv.Perm (Fin 100)) * (m : Equiv.Perm (Fin 100))) =
      compT wTab (T m) := by
  rw [T_mul, T_mul, T_hs100U, T_coe, wTab, treeElems_getD kU_lt, T_coe]

theorem out_dichotomy {E : Subgroup PG} {X : PG} (hX : HasFix E X) (hEcard : Nat.card E = 16)
    {r : Equiv.Perm (Fin 100)} (hr : r ∈ hs100R)
    (hrE : ∀ z ∈ E, r * (z : Equiv.Perm (Fin 100)) = (z : Equiv.Perm (Fin 100)) * r) :
    (∃ z ∈ E, r = (z : Equiv.Perm (Fin 100))) ∨
      T ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) ∈ outList := by
  have hXR : (X : Equiv.Perm (Fin 100)) ∈ hs100R := hs100P_le_R X.2
  have hr' : (X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100)) ∈ hs100R :=
    hs100R.mul_mem (hs100R.mul_mem (hs100R.inv_mem hXR) hr) hXR
  have hpres : Pres ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) :=
    pres_of_hasFix hX fun z hz => ⟨z, hz, (hrE z hz).symm⟩
  have hE0 := E0g_conj_eq hX hEcard
  have hcomm : ∀ z₀ ∈ E0g,
      ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) * (z₀ : Equiv.Perm (Fin 100)) =
        (z₀ : Equiv.Perm (Fin 100)) *
          ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) := by
    intro z₀ hz₀
    rw [← hE0] at hz₀
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz₀
    have e : (MulAut.conj X⁻¹).toMonoidHom z = X⁻¹ * z * X := by simp [MulAut.conj_apply]
    rw [e]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc _ = (X : Equiv.Perm (Fin 100))⁻¹ * (r * (z : Equiv.Perm (Fin 100))) *
          (X : Equiv.Perm (Fin 100)) := by group
      _ = (X : Equiv.Perm (Fin 100))⁻¹ * ((z : Equiv.Perm (Fin 100)) * r) *
          (X : Equiv.Perm (Fin 100)) := by rw [hrE z hz]
      _ = _ := by group
  obtain ⟨-, hcent0, -⟩ := e0OK_parts
  rcases R_pres_cases hr' hpres with ⟨q, hqM, hrq⟩ | ⟨m, hmM, hrm⟩
  · left
    have hqc : T q ∈ cent0List := by
      rw [cent0List, List.mem_filter]
      refine ⟨(mSpec.mem_iff q).mp hqM, ?_⟩
      refine List.all_eq_true.mpr fun t ht => ?_
      obtain ⟨z₀, hz₀, rfl⟩ := mem_e0Elems_iff.mp ht
      refine commT_iff.mpr (Subtype.ext ?_)
      have := hcomm z₀ hz₀
      rw [hrq] at this
      exact this
    obtain ⟨z₀, hz₀, hzq⟩ := mem_e0Elems_iff.mp (hcent0 _ hqc)
    have hq : q = z₀ := eq_of_T hzq.symm
    rw [← hE0] at hz₀
    obtain ⟨z, hz, hzz⟩ := Subgroup.mem_map.mp hz₀
    refine ⟨z, hz, ?_⟩
    have e1 : (MulAut.conj X⁻¹).toMonoidHom z = X⁻¹ * z * X := by simp [MulAut.conj_apply]
    rw [e1] at hzz
    have e2 : (X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100)) =
        (X : Equiv.Perm (Fin 100))⁻¹ * (z : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100)) := by
      rw [hrq, hq, ← hzz]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc r = (X : Equiv.Perm (Fin 100)) *
          ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) *
          (X : Equiv.Perm (Fin 100))⁻¹ := by group
      _ = (X : Equiv.Perm (Fin 100)) *
          ((X : Equiv.Perm (Fin 100))⁻¹ * (z : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100))) *
          (X : Equiv.Perm (Fin 100))⁻¹ := by rw [e2]
      _ = z := by group
  · right
    have hT : T ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) =
        compT wTab (T m) := by
      rw [hrm, T_wm]
    rw [hT, outList, List.mem_map]
    refine ⟨T m, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨(mSpec.mem_iff m).mp hmM, ?_⟩
    refine List.all_eq_true.mpr fun t ht => ?_
    obtain ⟨z₀, hz₀, rfl⟩ := mem_e0Elems_iff.mp ht
    rw [← hT]
    exact commT_iff.mpr (hcomm z₀ hz₀)

end CFSG.Quasithin.H13.LocDbl.HSLoc
