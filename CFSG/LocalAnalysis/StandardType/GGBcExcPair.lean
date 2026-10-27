module

public import CFSG.LocalAnalysis.StandardType.GGBcDefs
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private abbrev bcxpTypeCheck (T : GGKacType) (tw : Bool) (d : ℕ) : Prop :=
  ∀ s ∈ ggKacSupports (k0DiagOf T).marks.length,
  ∀ a ∈ (k0DiagOf T).omega, ∀ a0 ∈ (k0DiagOf T).omega,
    let rho := k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf T) tw d))
    ∀ x ∈ ggKacShShapes (k0DiagOf T) s rho d,
      x.1 = .A ∨ x.1 = .D ∨ x.1 = .E6 ∨ x.1 = .E7 ∨ x.1 = .E8

private theorem bcxpTypeCheck_E6_false_1 : bcxpTypeCheck .E6 false 1 := by decide +kernel
private theorem bcxpTypeCheck_E6_false_2 : bcxpTypeCheck .E6 false 2 := by decide +kernel
private theorem bcxpTypeCheck_E6_true_1 : bcxpTypeCheck .E6 true 1 := by decide +kernel
private theorem bcxpTypeCheck_E6_true_2 : bcxpTypeCheck .E6 true 2 := by decide +kernel
private theorem bcxpTypeCheck_E7_1 : bcxpTypeCheck .E7 false 1 := by decide +kernel
private theorem bcxpTypeCheck_E7_2 : bcxpTypeCheck .E7 false 2 := by decide +kernel
private theorem bcxpTypeCheck_E8_1 : bcxpTypeCheck .E8 false 1 := by decide +kernel
private theorem bcxpTypeCheck_E8_2 : bcxpTypeCheck .E8 false 2 := by decide +kernel

private abbrev bcxpF4ShapeCheck (d : ℕ) : Prop :=
  ∀ s ∈ ggKacSupports 5,
  ∀ a ∈ (k0DiagOf .F4).omega, ∀ a0 ∈ (k0DiagOf .F4).omega,
    let rho := k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf .F4) false d))
    ∀ x ∈ ggKacShShapes (k0DiagOf .F4) s rho d, x.2.2.2 = 1

private theorem bcxpF4ShapeCheck_1 : bcxpF4ShapeCheck 1 := by decide +kernel
private theorem bcxpF4ShapeCheck_2 : bcxpF4ShapeCheck 2 := by decide +kernel

private theorem bcxpF4_zero :
    ∀ s ∈ ggKacSupports 5,
      ∀ c ∈ k0Comps (k0DiagOf .F4) ((List.range 5).filter (fun i => decide (s.getD i 0 = 0))),
        (k0CompType (k0DiagOf .F4) c).1 = .C → 3 ≤ (k0CompType (k0DiagOf .F4) c).2 →
          (c = [1, 2, 3] ∧ (k0CompType (k0DiagOf .F4) c).2 = 3) ∨
          (c = [2, 3, 4] ∧ (k0CompType (k0DiagOf .F4) c).2 = 3) ∨
          (c = [0, 1, 2, 3] ∧ (k0CompType (k0DiagOf .F4) c).2 = 4) := by decide +kernel

private theorem bcxpF4_sub :
    ∀ s ∈ ggKacSupports 5,
      ∀ c ∈ k0Comps (k0DiagOf .F4) ((List.range 5).filter (fun i => decide (s.getD i 0 = 0))),
        ∀ i ∈ c, s.getD i 0 = 0 := by decide +kernel

private theorem bcxpF4_tag :
    ∀ s ∈ ggKacSupports 5,
      ∀ c ∈ k0Comps (k0DiagOf .F4) ((List.range 5).filter (fun i => decide (s.getD i 0 = 0))),
        (k0CompType (k0DiagOf .F4) c).1 = .A ∨ (k0CompType (k0DiagOf .F4) c).1 = .D ∨
        (k0CompType (k0DiagOf .F4) c).1 = .E6 ∨ (k0CompType (k0DiagOf .F4) c).1 = .E7 ∨
        (k0CompType (k0DiagOf .F4) c).1 = .E8 ∨ (k0CompType (k0DiagOf .F4) c).1 = .G2 ∨
        (k0CompType (k0DiagOf .F4) c).1 = .C ∨ (k0CompType (k0DiagOf .F4) c).1 = .F4 :=
  by decide +kernel

private theorem bcxpLabel_tag_not_BC {fam : LargeEvenLieTag} {r tw nEff : ℕ}
    (hfam : fam = .A ∨ fam = .D ∨ fam = .E6 ∨ fam = .E7 ∨ fam = .E8) :
    (k0LabelOf fam r tw nEff).lab.tag ≠ .B ∧ (k0LabelOf fam r tw nEff).lab.tag ≠ .C := by
  rcases hfam with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [k0LabelOf]
  all_goals try split
  all_goals try split
  all_goals simp

private theorem bcxpLabel_BC {fam : LargeEvenLieTag} {r tw nEff : ℕ}
    (hfam : fam = .A ∨ fam = .D ∨ fam = .E6 ∨ fam = .E7 ∨ fam = .E8 ∨ fam = .G2 ∨
      fam = .C ∨ fam = .F4)
    (hBC : (k0LabelOf fam r tw nEff).lab.tag = .B ∨ (k0LabelOf fam r tw nEff).lab.tag = .C) :
    fam = .C ∧ (k0LabelOf fam r tw nEff).lab.rank = r ∧
      (k0LabelOf fam r tw nEff).lab.n = nEff := by
  rcases hfam with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [k0LabelOf] at hBC ⊢
  all_goals try split at hBC
  all_goals try split at hBC
  all_goals try split
  all_goals simp_all

private theorem bcxp_orbit_not_BC {T : GGKacType} {tw : Bool} {p n d : ℕ} {D : GGKacDatum}
    {o : GGKacOrbit} (hraw : D ∈ k0RawDatums (k0DiagOf T) tw p n d)
    (ho : o ∈ D.orbits) (hcheck : bcxpTypeCheck T tw d) :
    o.lab.tag ≠ .B ∧ o.lab.tag ≠ .C := by
  obtain ⟨s, base, a0, a, rho, hs, hbase, ha0, -, ha, -, hrho, hDdef⟩ := ggKacShRawClass hraw
  rw [hDdef] at ho
  obtain ⟨x, hx, ho_eq⟩ := ggKacSh_orbit_mem_shapes ho
  have hlen := ggKacShVecs_length _ _ _ hs
  have hs' : ggKacShIndicator s ∈ ggKacSupports (k0DiagOf T).marks.length := by
    rw [← hlen]; exact ggKacShIndicator_supports s
  have hshape : ggKacShShapes (k0DiagOf T) (ggKacShIndicator s) rho d =
      ggKacShShapes (k0DiagOf T) s rho d :=
    ggKacShShapes_congr (fun i => ggKacShIndicator_zero s i)
  have hx' : x ∈ ggKacShShapes (k0DiagOf T) (ggKacShIndicator s) rho d := by rw [hshape]; exact hx
  have hrho' : rho = k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf T) tw d)) := by rw [hrho, hbase]
  have hx'' : x ∈ ggKacShShapes (k0DiagOf T) (ggKacShIndicator s) (k0pMul a (k0pMul a0
      (k0Rho0 (k0DiagOf T) tw d))) d := by rw [← hrho']; exact hx'
  have hfam := hcheck (ggKacShIndicator s) hs' a ha a0 ha0 x hx''
  rw [ho_eq]
  exact bcxpLabel_tag_not_BC hfam

private theorem bcxp_orbit_F4_eq {p n d : ℕ} {D : GGKacDatum} {o : GGKacOrbit}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hd : d = 1 ∨ d = 2)
    (hraw : D ∈ k0RawDatums (k0DiagOf .F4) false p n d)
    (ho : o ∈ D.orbits) (hBC : o.lab.tag = .B ∨ o.lab.tag = .C) (h3 : 3 ≤ o.lab.rank) :
    o.lab = ⟨.C, 3, n⟩ := by
  obtain ⟨s, base, a0, a, rho, hs, hbase, ha0, -, ha, -, hrho, hDdef⟩ := ggKacShRawClass hraw
  rw [hDdef] at ho
  obtain ⟨x, hx, ho_eq⟩ := ggKacSh_orbit_mem_shapes ho
  have hlen : s.length = 5 := by simpa [k0DiagOf, k0F4Diag] using ggKacShVecs_length _ _ _ hs
  have hs' : ggKacShIndicator s ∈ ggKacSupports 5 := by
    rw [← hlen]; exact ggKacShIndicator_supports s
  have hshape : ggKacShShapes (k0DiagOf .F4) (ggKacShIndicator s) rho d =
      ggKacShShapes (k0DiagOf .F4) s rho d :=
    ggKacShShapes_congr (fun i => ggKacShIndicator_zero s i)
  have hx' : x ∈ ggKacShShapes (k0DiagOf .F4) (ggKacShIndicator s) rho d := by rw [hshape]; exact hx
  have hrho' : rho = k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf .F4) false d)) := by rw [hrho, hbase]
  have hx'' : x ∈ ggKacShShapes (k0DiagOf .F4) (ggKacShIndicator s) (k0pMul a (k0pMul a0
      (k0Rho0 (k0DiagOf .F4) false d))) d := by rw [← hrho']; exact hx'
  have hk1 : x.2.2.2 = 1 := by
    rcases hd with rfl | rfl
    · exact bcxpF4ShapeCheck_1 (ggKacShIndicator s) hs' a ha a0 ha0 x hx''
    · exact bcxpF4ShapeCheck_2 (ggKacShIndicator s) hs' a ha a0 ha0 x hx''
  obtain ⟨orb, -, hc_mem, hx1, hx2, -⟩ := ggKacShShape_data hx'
  have hmem := bcxpF4_tag (ggKacShIndicator s) hs' (orb.headD []) hc_mem
  rw [← hx1] at hmem
  have hBC' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab.tag = .B ∨
      (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab.tag = .C := by
    rw [ho_eq] at hBC; exact hBC
  obtain ⟨hfamC, hrank, -⟩ := bcxpLabel_BC hmem hBC'
  have hfamC' : (k0CompType (k0DiagOf .F4) (orb.headD [])).1 = .C := by
    rw [← hx1]; exact hfamC
  have hrank3 : 3 ≤ (k0CompType (k0DiagOf .F4) (orb.headD [])).2 := by
    have h := h3
    rw [ho_eq, hrank, hx2] at h
    exact h
  have hcomp := bcxpF4_zero (ggKacShIndicator s) hs' (orb.headD []) hc_mem hfamC' hrank3
  have hrank_eq3 : (k0CompType (k0DiagOf .F4) (orb.headD [])).2 = 3 := by
    rcases hcomp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hc0123, h4⟩
    · exact h
    · exact h
    · exfalso
      have hsub := bcxpF4_sub (ggKacShIndicator s) hs' (orb.headD []) hc_mem
      have hs0 : s.getD 0 0 = 0 :=
        (ggKacShIndicator_zero s 0).mp (hsub 0 (by rw [hc0123]; simp))
      have hs1 : s.getD 1 0 = 0 :=
        (ggKacShIndicator_zero s 1).mp (hsub 1 (by rw [hc0123]; simp))
      have hs2 : s.getD 2 0 = 0 :=
        (ggKacShIndicator_zero s 2).mp (hsub 2 (by rw [hc0123]; simp))
      have hs3 : s.getD 3 0 = 0 :=
        (ggKacShIndicator_zero s 3).mp (hsub 3 (by rw [hc0123]; simp))
      have hsum : 2 * s.getD 4 0 = p := by
        have h := ggKacShVecs_sum (k0DiagOf .F4).marks p s hs
        change (∑ i : Fin 5, [1, 2, 3, 4, 2].getD (i : ℕ) 0 * s.getD (i : ℕ) 0) = p at h
        rw [Fin.sum_univ_five] at h
        simp only [Fin.val_ofNat, Nat.reduceMod, Fin.val_zero, Fin.val_one] at h
        norm_num at h
        rw [List.getD_eq_getElem?_getD] at hs0 hs1 hs2 hs3
        rw [List.getD_eq_getElem?_getD]
        omega
      have hdvd : 2 ∣ p := ⟨s.getD 4 0, hsum.symm⟩
      have hp2eq : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp hdvd).symm
      exact hp2 hp2eq
  rw [ho_eq, hfamC, hk1, hx2, hrank_eq3]
  simp only [k0LabelOf]
  split
  · exfalso; omega
  · simp

private theorem bcxpIso_C3 {lab lab' : LargeEvenLabel} {n : ℕ}
    (hiso : GGLabelIso lab lab') (h : lab' = ⟨.C, 3, n⟩) :
    (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ lab.n = n := by
  rcases hiso with h1 | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · subst h1; rw [h]; exact ⟨Or.inr rfl, rfl, rfl⟩
  · obtain ⟨hB, -, hr, hn⟩ := hBC
    rw [h] at hr hn
    simp only at hr hn
    exact ⟨hB, hr, hn⟩
  · obtain ⟨-, h2⟩ := hDA; rw [h2] at h; simp at h
  · obtain ⟨-, h2⟩ := hAD; rw [h2] at h; simp at h
  · obtain ⟨-, h2⟩ := hD3A3; rw [h2] at h; simp at h
  · obtain ⟨-, h2⟩ := hA3D3; rw [h2] at h; simp at h
  · obtain ⟨-, h2⟩ := hD2A1; rw [h2] at h; simp at h
  · obtain ⟨h1, -⟩ := hA1D2; rw [h1] at h; simp at h

private theorem bcxpIso_BC {lab lab' : LargeEvenLabel}
    (hiso : GGLabelIso lab lab') (hB : lab.tag = .B ∨ lab.tag = .C) (h3 : 3 ≤ lab.rank) :
    (lab'.tag = .B ∨ lab'.tag = .C) ∧ 3 ≤ lab'.rank := by
  rcases hiso with h1 | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · subst h1; exact ⟨hB, h3⟩
  · obtain ⟨-, hB', hr, -⟩ := hBC
    exact ⟨hB', by omega⟩
  · obtain ⟨h1, -⟩ := hDA; rw [h1] at hB; simp at hB
  · obtain ⟨h1, -⟩ := hAD; rw [h1] at hB; simp at hB
  · obtain ⟨h1, -⟩ := hD3A3; rw [h1] at hB; simp at hB
  · obtain ⟨h1, -⟩ := hA3D3; rw [h1] at hB; simp at hB
  · obtain ⟨h1, -⟩ := hD2A1; rw [h1] at hB; simp at hB
  · obtain ⟨-, h2⟩ := hA1D2; rw [h2] at hB; simp at hB

private theorem bcxpF4_label_eq {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .F4) :
    lab = ⟨.F4, 0, lab.n⟩ := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hΛ
  subst htag
  have hr : r = 0 := by simpa using hΛ.2
  subst hr
  rfl

private theorem bcxp_row_F4 {p : ℕ} {labJ labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (htag : labX.tag = .F4)
    (hiso : GGLabelIso labJ ⟨.C, 3, labX.n⟩)
    (hbranch : p ∣ 2 ^ labX.n - 1 ∨ p ∣ 2 ^ labX.n + 1) :
    GGTablePRow p labJ labX := by
  obtain ⟨hBC', hr, hn'⟩ := bcxpIso_C3 hiso rfl
  have hlabXeq : labX = ⟨.F4, 0, labX.n⟩ := bcxpF4_label_eq hΛX htag
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
  refine ⟨hBC', ?_, ?_, ?_⟩
  · rwa [hn']
  · rw [hr]; norm_num
  · refine Or.inr ⟨hr, ?_⟩
    rw [hlabXeq, hn']

theorem ggBcExcPairRK_holds
    (hBS : GGK0ExcBS) : GGBcExcPairRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hpair⟩ := hr
  obtain ⟨hBC, h3⟩ := hreg
  obtain ⟨hlocCore, -, -, -, -, -, -, -⟩ := hd.1
  obtain ⟨D, hDval, ha, -, -, -⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x; simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hlocCore.2.2.2.1
  obtain ⟨o, ho, -, -, hΛo, hlabo⟩ := ha J hJfix
  obtain ⟨T, tw, hty, hDmem⟩ := hDval
  have hbranch : p ∣ 2 ^ labX.n - 1 ∨ p ∣ 2 ^ labX.n + 1 := hpair.2.2.1
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hcontra {T' : GGKacType} {tw' : Bool} {d' : ℕ}
      (hraw' : D ∈ k0RawDatums (k0DiagOf T') tw' p labX.n d')
      (hchk : bcxpTypeCheck T' tw' d') : False := by
    have hnot := bcxp_orbit_not_BC hraw' ho hchk
    exact (bcxpIso_BC hiso hBC h3).1.elim hnot.1 hnot.2
  have hBCo : o.lab.tag = .B ∨ o.lab.tag = .C := (bcxpIso_BC hiso hBC h3).1
  have h3o : 3 ≤ o.lab.rank := (bcxpIso_BC hiso hBC h3).2
  rcases hpair.2.2.2 with htag | htag | htag | htag | htag
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E6, false) := by
      obtain ⟨t, r, nn⟩ := labX
      simp only at htag
      subst htag
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hraw0 := ggKacSh_mem_rawDatums hDmem hbranch
    by_cases h1 : p ∣ 2 ^ labX.n - 1
    · have hraw1 : D ∈ k0RawDatums (k0DiagOf .E6) false p labX.n 1 := by
        simpa only [if_pos h1] using hraw0
      exact False.elim (hcontra hraw1 bcxpTypeCheck_E6_false_1)
    · have hraw2 : D ∈ k0RawDatums (k0DiagOf .E6) false p labX.n 2 := by
        simpa only [if_neg h1] using hraw0
      exact False.elim (hcontra hraw2 bcxpTypeCheck_E6_false_2)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E6, true) := by
      obtain ⟨t, r, nn⟩ := labX
      simp only at htag
      subst htag
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hraw0 := ggKacSh_mem_rawDatums hDmem hbranch
    by_cases h1 : p ∣ 2 ^ labX.n - 1
    · have hraw1 : D ∈ k0RawDatums (k0DiagOf .E6) true p labX.n 1 := by
        simpa only [if_pos h1] using hraw0
      exact False.elim (hcontra hraw1 bcxpTypeCheck_E6_true_1)
    · have hraw2 : D ∈ k0RawDatums (k0DiagOf .E6) true p labX.n 2 := by
        simpa only [if_neg h1] using hraw0
      exact False.elim (hcontra hraw2 bcxpTypeCheck_E6_true_2)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E7, false) := by
      obtain ⟨t, r, nn⟩ := labX
      simp only at htag
      subst htag
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hraw0 := ggKacSh_mem_rawDatums hDmem hbranch
    by_cases h1 : p ∣ 2 ^ labX.n - 1
    · have hraw1 : D ∈ k0RawDatums (k0DiagOf .E7) false p labX.n 1 := by
        simpa only [if_pos h1] using hraw0
      exact False.elim (hcontra hraw1 bcxpTypeCheck_E7_1)
    · have hraw2 : D ∈ k0RawDatums (k0DiagOf .E7) false p labX.n 2 := by
        simpa only [if_neg h1] using hraw0
      exact False.elim (hcontra hraw2 bcxpTypeCheck_E7_2)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E8, false) := by
      obtain ⟨t, r, nn⟩ := labX
      simp only at htag
      subst htag
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hraw0 := ggKacSh_mem_rawDatums hDmem hbranch
    by_cases h1 : p ∣ 2 ^ labX.n - 1
    · have hraw1 : D ∈ k0RawDatums (k0DiagOf .E8) false p labX.n 1 := by
        simpa only [if_pos h1] using hraw0
      exact False.elim (hcontra hraw1 bcxpTypeCheck_E8_1)
    · have hraw2 : D ∈ k0RawDatums (k0DiagOf .E8) false p labX.n 2 := by
        simpa only [if_neg h1] using hraw0
      exact False.elim (hcontra hraw2 bcxpTypeCheck_E8_2)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.F4, false) := by
      obtain ⟨t, r, nn⟩ := labX
      simp only at htag
      subst htag
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hraw0 := ggKacSh_mem_rawDatums hDmem hbranch
    by_cases h1 : p ∣ 2 ^ labX.n - 1
    · have hraw1 : D ∈ k0RawDatums (k0DiagOf .F4) false p labX.n 1 := by
        simpa only [if_pos h1] using hraw0
      have hoC3 := bcxp_orbit_F4_eq hp hp2 (Or.inl rfl) hraw1 ho hBCo h3o
      have hiso' := hiso
      rw [hoC3] at hiso'
      exact ⟨labJ, labX, hΛJ, hΛX, bcxp_row_F4 hΛX htag hiso' hbranch, hhJ, hhX⟩
    · have hraw2 : D ∈ k0RawDatums (k0DiagOf .F4) false p labX.n 2 := by
        simpa only [if_neg h1] using hraw0
      have hoC3 := bcxp_orbit_F4_eq hp hp2 (Or.inr rfl) hraw2 ho hBCo h3o
      have hiso' := hiso
      rw [hoC3] at hiso'
      exact ⟨labJ, labX, hΛJ, hΛX, bcxp_row_F4 hΛX htag hiso' hbranch, hhJ, hhX⟩

end CFSG.StandardType

end
