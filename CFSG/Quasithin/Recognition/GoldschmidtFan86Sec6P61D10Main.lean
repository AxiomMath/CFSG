module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61D10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ivl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61D10A

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph P514 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan61_two_d10 (F : FanTree Γ G) (h40 : Fan40 F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h514 : Fan514 F) (h53b : Fan53b F) (h55a : Fan55a F) (h57a : Fan57a F)
    (h58a : Fan58aT F) {T : Track Γ G} {z : G} {a : ℤ} (C : Cfg61 T z a 2)
    (hctx : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2)))
    (hD : ∀ g ∈ MulAction.stabilizer G (T.line.vert (a + 2)) ⊓
      MulAction.stabilizer G (T.line.vert (a + 1)), g * g ∈ nbrStab Γ G (T.line.vert (a + 2))) :
    False := by
  have hv5 := cfg_v5 F C
  have hv3' := cfg_v3_succ F C
  have hz2 : z * z = 1 := C.cinv.2.1
  have hz3C := isCoreFix_lab T 2 C.core
  have hz3ZZ := lab_mem_ZZ T C.zz 2
  have hz3sq : lab T z 2 * lab T z 2 = 1 := lab_mul_self T hz2 2
  obtain ⟨hu1, hu2, hucen⟩ := h57a h40 T.line z (lab T z 2) a (a + 2) (a - 2) (a + 2 + 2)
    (a + 2 * 2) (a + 2 + 2 * 2) (a - 2 + 2 * 2) (a + 2 + 2 + 2 * 2) C.zz hz3ZZ C.core hz3C
    (by ring)
  obtain ⟨-, -, hvcen⟩ := h57a h40 T.line.rev (lab T z 2) z (-(a + 2 + 2 * 2)) (-(a + 2 * 2))
    (-(a + 2 + 2 + 2 * 2)) (-(a - 2 + 2 * 2)) (-(a + 2)) (-a) (-(a + 2 + 2)) (-(a - 2))
    (Line.ZZ_rev hz3ZZ) (Line.ZZ_rev C.zz) hz3C.rev C.core.rev (by ring)
  obtain ⟨u, hu⟩ : ∃ u : G, u = fcomm z (lab T z 2) := ⟨_, rfl⟩
  rw [← hu] at hu1 hu2 hucen
  have huinv : fcomm (lab T z 2) z = u := by
    rw [hu, ← fcomm_inv]
    exact inv_eq_of_mul_eq_one_right (by rw [← hu]; exact hu2)
  rw [huinv, Line.rev_edgeCirc T.line F, show -(-(a + 2 * 2)) - 1 = a + 2 + 1 by ring] at hvcen
  have hadjo : Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := hctx.adj
  obtain ⟨k, hk, hkα⟩ := F.loc_trans (T.line.vert (a + 2)) (T.line.vert (a + 1))
    (T.line.vert (a + 2 + 1)) hadjo.symm (T.line.adj (a + 2))
  have hsq1 : ∀ g ∈ MulAction.stabilizer G (T.line.vert (a + 2)) ⊓
      MulAction.stabilizer G (T.line.vert (a + 2 + 1)),
      g * g ∈ nbrStab Γ G (T.line.vert (a + 2)) := by
    have := dih_transport F hD k
    rwa [MulAction.mem_stabilizer_iff.1 hk, hkα] at this
  have hsq2 : ∀ g ∈ MulAction.stabilizer G (T.line.vert (a + 2 + 1 + 1)) ⊓
      MulAction.stabilizer G (T.line.vert (a + 2 + 1)),
      g * g ∈ nbrStab Γ G (T.line.vert (a + 2 + 1 + 1)) := by
    have := dih_transport F hD T.τ
    rw [T.trans (a + 2), T.trans (a + 1), show a + 2 + 2 = a + 2 + 1 + 1 by ring,
      show a + 1 + 2 = a + 2 + 1 by ring] at this
    exact this
  have hne5 : valence Γ (T.line.vert (a + 2 + 1)) ≠ 5 := by
    rw [hv3']
    norm_num
  have hcen1 : u ∈ Cen (T.line.edgeStab (G := G) (a + 2) : Set G) :=
    cen_edgeStab_five T.line hv5 hsq1 hucen
  have hcen2 : u ∈ Cen (T.line.edgeStab (G := G) (a + 2 + 1) : Set G) :=
    cen_edgeStab_ne_five T.line hne5 hsq2 hvcen
  have huZZ : u ∈ T.line.ZZ := ⟨hu2, a + 2, hcen1⟩
  have hfu := fix_six F h40 h510 h511 h514 h53b h55a h58a C huZZ hu1 hcen1 hcen2
  have hz₁ZZ := lab_mem_ZZ T C.zz 1
  have hz₁core := isCore_lab T 1 C.core.core
  have hz₁c1 : lab T z 1 ∈ Cen (T.line.edgeStab (G := G) (a + 2) : Set G) :=
    hz₁core.2.2.1 (a + 2) (by omega) (by omega)
  have hz₁c2 : lab T z 1 ∈ Cen (T.line.edgeStab (G := G) (a + 2 + 1) : Set G) :=
    hz₁core.2.2.1 (a + 2 + 1) (by omega) (by omega)
  have hcomm : lab T z 1 * u = u * lab T z 1 := hcen1.2 _ hz₁c1.1
  have hz1sq : lab T z 1 * lab T z 1 = 1 := lab_mul_self T hz2 1
  have hwb2 : (lab T z 1 * u) * (lab T z 1 * u) = 1 := by
    calc (lab T z 1 * u) * (lab T z 1 * u) = lab T z 1 * (u * lab T z 1) * u := by
          simp only [mul_assoc]
      _ = lab T z 1 * (lab T z 1 * u) * u := by rw [hcomm]
      _ = (lab T z 1 * lab T z 1) * (u * u) := by simp only [mul_assoc]
      _ = 1 := by rw [hz1sq, hu2, one_mul]
  have hz3o : lab T z 2 • T.line.vert (a + 2) = T.line.vert (a + 2) :=
    (mem_fixIdx_lab T z 2 (a + 2)).2 ((C.core.fix _).2 ⟨by omega, by omega⟩)
  have hz3s : lab T z 2 • T.line.vert (a + 2 + 1) = T.line.vert (a + 2 + 1) :=
    (mem_fixIdx_lab T z 2 (a + 2 + 1)).2 ((C.core.fix _).2 ⟨by omega, by omega⟩)
  have hz3α : lab T z 2 • T.line.vert (a + 1) ≠ T.line.vert (a + 1) := by
    intro h
    have := (C.core.fix _).1 ((mem_fixIdx_lab T z 2 (a + 1)).1 h)
    omega
  have hnb : T.line.vert (a + 1) ≠ T.line.vert (a + 2 + 1) := by
    have := T.line.nb (a + 1)
    rwa [show a + 1 + 2 = a + 2 + 1 by ring] at this
  have hu_eq : u = z * (lab T z 2 * z * (lab T z 2)⁻¹) := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hz3i : (lab T z 2)⁻¹ = lab T z 2 := inv_eq_of_mul_eq_one_right hz3sq
    simp only [hu, fcomm, hzi, hz3i, mul_assoc]
  have hwb1 : lab T z 1 * u ≠ 1 := by
    intro h
    have h' : u * lab T z 1 = 1 := by rw [← hcomm]; exact h
    refine prod3_ne_one F hctx (p := T.line.vert (a + 1)) (q := lab T z 2 • T.line.vert (a + 1))
      (s := T.line.vert (a + 2 + 1)) hadjo.symm ?_ (T.line.adj (a + 2)) hz3α.symm hnb ?_ ?_
    · have := (F.adj_smul (lab T z 2) _ _).2 hadjo.symm
      rwa [hz3o] at this
    · intro h3
      apply hnb
      have h4 : lab T z 2 • T.line.vert (a + 1) = lab T z 2 • T.line.vert (a + 2 + 1) := by
        rw [h3, hz3s]
      exact MulAction.injective _ h4
    · rw [P514.Lb_self C.cinv, P514.Lb_eq C.cinv (g := lab T z 2) rfl,
        (lab_one_eq T C.cinv).symm]
      rw [hu_eq] at h'
      exact h'
  have hwbZZ : lab T z 1 * u ∈ T.line.ZZ := ⟨hwb2, a + 2, (cen_mul hz₁c1 hcen1)⟩
  have hfw := fix_six F h40 h510 h511 h514 h53b h55a h58a C hwbZZ hwb1 (cen_mul hz₁c1 hcen1)
    (cen_mul hz₁c2 hcen2)
  have e : u * (lab T z 1 * u) = lab T z 1 := by
    calc u * (lab T z 1 * u) = (u * lab T z 1) * u := by rw [mul_assoc]
      _ = (lab T z 1 * u) * u := by rw [← hcomm]
      _ = lab T z 1 * (u * u) := by rw [mul_assoc]
      _ = lab T z 1 := by rw [hu2, mul_one]
  have hfv : ∀ i, i ∈ T.line.fixIdx (u * (lab T z 1 * u)) ↔ a ≤ i ∧ i ≤ a + 6 := by
    intro i
    rw [e, mem_fixIdx_lab, C.core.fix]
    omega
  have key := prod_left_iv F T.line hu2 hwb2 (tL₁ := a) (tR₁ := a + 6) (tL₂ := a)
    (tR₂ := a + 6) (tLv := a) (tRv := a + 6) (c := a + 2) hfu hfw hfv (by omega) (by omega)
    (by omega) (by omega)
  have := key.2.2 rfl
  omega

end P61

end CFSG.Quasithin.Fan86
