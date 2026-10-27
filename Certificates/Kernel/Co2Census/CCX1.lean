module

public import Certificates.Kernel.Co2Census.CCX7
public import Certificates.Kernel.Co2Census.CCKX1
public import Certificates.Kernel.Co2Census.CCSqrt

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem cR1 : cR 1 = cE 0 26805 := rfl

theorem repK_r1 : repK ((cR 1 : Cz) : K) R1 := by
  rw [cR1]
  exact repK_cE QK_eq (by norm_num) 26805

theorem X1_D' : dlK QKt (mulV (SK 26805) (QKt 0)) = (List.range 32).map X1Dt := X1_D

theorem hex26805 : ∀ i < 23040, ∃ s ∈ centS0 (sElt 26805), repK s (C26805Pt i) :=
  (rec_elt C26805_tree C26805_root C26805_misc cent_26805).1

noncomputable def s1E (j : ℕ) : Cz :=
  if h : j < 23040 then ⟨recS hex26805 j, S0_le_Cz (recS_spec hex26805 h).1.1⟩ else 1

theorem repK_s1 {j : ℕ} (hj : j < 23040) : repK ((s1E j : Cz) : K) (C26805Pt j) := by
  simp only [s1E, dif_pos hj]
  exact (recS_spec hex26805 hj).2

theorem cR1_val : ((cR 1 : Cz) : K) = sElt 26805 := by
  have h := repK_r1
  have h1 := F1_misc_spec.2.2.2.2.2.1
  rw [R1, h1] at h
  rw [show mulV (SK 26805) IDP = SK 26805 by
    exact repK_unique (by have := repK_mul (repK_sElt 26805) repK_one; rwa [mul_one] at this)
      (repK_sElt 26805)] at h
  exact repK_fun h (repK_sElt 26805)

theorem s1E_spec {j : ℕ} (hj : j < 23040) :
    repK (piC (s1E j)) (C26805Pt j) ∧ s1E j * cE 0 26805 = cE 0 26805 * s1E j := by
  have hs := recS_spec hex26805 hj
  refine ⟨?_, ?_⟩
  · simp only [s1E, dif_pos hj]
    rw [piC_S0 hs.1.1]
    exact hs.2
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, show ((cE 0 26805 : Cz) : K) = sElt 26805 from cR1_val]
    simp only [s1E, dif_pos hj]
    exact hs.1.2

theorem mem_D1 {d : Cz} : d ∈ DCi 1 ↔ ∃ t < 32, d = qE (X1Dt t) := by
  rw [mem_DCi_iff cR1 (by norm_num)]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [X1_D'] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
    exact ⟨t, List.mem_range.1 ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, by rw [X1_D']; exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩, rfl⟩

theorem X1D_lt {t : ℕ} (ht : t < 32) : X1Dt t < 512 := by
  have : X1Dt t ∈ dlK QKt R1 := by
    rw [X1_D]
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩
  exact ((mem_dlK repK_r1).1 this).1

theorem mem_X1 {u : Cz} (hu : u ∈ XC 1) : ∃ j < 23040, ∃ t < 32, u = s1E j * qE (X1Dt t) := by
  obtain ⟨j, hj, e, he, rfl⟩ := mem_Xg (by norm_num) cent_26805 (fun j hj => s1E_spec hj)
    (Subgroup.mem_centralizer_singleton_iff.1 hu)
  have he' : e ∈ (List.range 32).map X1Dt := by rwa [← X1_D']
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he'
  exact ⟨j, hj, t, List.mem_range.1 ht, rfl⟩

theorem c1_comm : ∀ a ∈ DCi 1, ∀ b ∈ DCi 1, a * b = b * a := by
  intro a ha b hb
  obtain ⟨t, ht, rfl⟩ := mem_D1.1 ha
  obtain ⟨t', ht', rfl⟩ := mem_D1.1 hb
  have h := X1_abel (32 * t + t') (by omega)
  rw [show (32 * t + t') / 32 = t by omega, show (32 * t + t') % 32 = t' by omega] at h
  exact qE_comm (repK_qE (X1D_lt ht)) (repK_qE (X1D_lt ht')) h

theorem X1_pts' (j : ℕ) (hj : j < 23040) :
    (∃ g < 32, X1Gdt g = j) ∨ (X1Wt j < 32 ∧ commK (C26805Pt j) (QKt (X1Dt (X1Wt j))) = false) := by
  have h := X1_pts j hj
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Nat.beq_eq, Bool.and_eq_true,
    Nat.blt_eq, Bool.not_eq_true'] at h
  exact h

theorem X1_good' (g t : ℕ) (hg : g < 32) (ht : t < 32) :
    X1Gdt g < 23040 ∧ commK (C26805Pt (X1Gdt g)) (QKt (X1Dt t)) = true ∧
      mulV (mulV (C26805Pt (X1Gdt g)) (QKt (X1Dt t))) (mulV (C26805Pt (X1Gdt g)) (QKt (X1Dt t))) =
        IDP := by
  have h := X1_good (32 * g + t) (by omega)
  rw [show (32 * g + t) / 32 = g by omega, show (32 * g + t) % 32 = t by omega] at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem good1_of_cxd {y : Cz} (hy : y ∈ Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1) :
    ∃ g < 32, ∃ t < 32, y = s1E (X1Gdt g) * qE (X1Dt t) := by
  obtain ⟨hyD, hyX⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨j, hj, t, ht, rfl⟩ := mem_X1 hyX
  rcases X1_pts' j hj with ⟨g, hg, rfl⟩ | ⟨hw, hnc⟩
  · exact ⟨g, hg, t, ht, rfl⟩
  · exfalso
    apply qE_ncomm (repK_s1 hj) (repK_qE (X1D_lt hw)) hnc
    have hd : (qE (X1Dt (X1Wt j)) : Cz) ∈ DCi 1 := mem_D1.2 ⟨_, hw, rfl⟩
    have hdt : (qE (X1Dt t) : Cz) ∈ DCi 1 := mem_D1.2 ⟨_, ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hyD _ hd
    have h2 := c1_comm _ hd _ hdt
    set q := (qE (X1Dt t) : Cz)
    set d := (qE (X1Dt (X1Wt j)) : Cz)
    have hc : q⁻¹ * d = d * q⁻¹ := (show Commute d q from h2).symm.inv_left.eq
    calc s1E j * d = s1E j * q * (q⁻¹ * d) := by group
      _ = s1E j * q * (d * q⁻¹) := by rw [hc]
      _ = s1E j * q * d * q⁻¹ := by group
      _ = d * (s1E j * q) * q⁻¹ := by rw [← h1]
      _ = d * s1E j := by group

theorem c1_cxd_card : Nat.card (Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1 : Subgroup Cz) ≤
    1024 := by
  classical
  change Nat.card ↥((Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1 : Subgroup Cz) : Set Cz) ≤ _
  rw [Nat.card_coe_set_eq]
  let F : ℕ × ℕ → Cz := fun p => s1E (X1Gdt p.1) * qE (X1Dt p.2)
  have hsub : ((Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1 : Subgroup Cz) : Set Cz) ⊆
      ((Finset.range 32 ×ˢ Finset.range 32).image F : Set Cz) := by
    intro y hy
    obtain ⟨g, hg, t, ht, rfl⟩ := good1_of_cxd hy
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(g, t), Finset.mem_product.2
      ⟨Finset.mem_range.2 hg, Finset.mem_range.2 ht⟩, rfl⟩)
  calc Set.ncard ((Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1 : Subgroup Cz) : Set Cz)
      ≤ Set.ncard ((Finset.range 32 ×ˢ Finset.range 32).image F : Set Cz) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ (Finset.range 32 ×ˢ Finset.range 32).card := by
        rw [Set.ncard_coe_finset]
        exact Finset.card_image_le
    _ = 1024 := by simp

theorem c1_cxd_sq : ∀ y ∈ Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1, y * y = 1 := by
  intro y hy
  obtain ⟨g, hg, t, ht, rfl⟩ := good1_of_cxd hy
  obtain ⟨hlt, -, hsq⟩ := X1_good' g t hg ht
  have hR := repK_czmul (repK_s1 hlt) (repK_qE (X1D_lt ht))
  exact (cz_eq_iff (repK_czmul hR hR) repK_one').2 hsq

theorem c1_hmin : ∀ N : Subgroup Cz, N ≤ DCi 1 → (∀ x ∈ XC 1, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
    N ≠ ⊥ → zCz ∈ N := by
  intro N hND hNX hN
  obtain ⟨d, hdN, hd1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN
  obtain ⟨t, ht, rfl⟩ := mem_D1.1 (hND hdN)
  have hc := X1_hcov t ht
  simp only [Bool.or_eq_true, Nat.beq_eq, List.any_eq_true, List.mem_range] at hc
  rcases hc with h0 | ⟨c, hc, hce⟩
  · exact absurd (by rw [h0]; exact qE0 : (qE (X1Dt t) : Cz) = 1) hd1
  have hm := X1_hmin c hc
  unfold hmin1OK at hm
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
  obtain ⟨⟨-, hx⟩, hp⟩ := hm
  rw [hce] at hp
  obtain ⟨hrows, hmem⟩ := certElt_facts repK_r1 (repK_qE (X1D_lt ht)) _ (certXOK_spec hx)
  have htN := hmem N hdN fun x hx' n hn =>
    hNX x (Subgroup.mem_centralizer_singleton_iff.2 hx') n hn
  have e := (cz_eq_iff hrows repK_zCz).2 hp
  rw [← e]
  exact htN

theorem X1_misc' : commK (mulV (SK 225319) (QKt 0)) R1 = true ∧
    (∀ t < 32, commK (mulV (SK 225319) (QKt 0)) (QKt (X1Dt t)) = true) ∧
    invEK QKt (mulV (SK 225319) (QKt 0)) = 80 ∧ fld21 (X1Tt 0) 0 < 512 ∧
    mulV (mulV (SK (fld21 (X1Tt 0) 1)) (QKt (fld21 (X1Tt 0) 0)))
        (mulV (mulV (SK 26805) (QKt 32)) (mulV (SK 0) (QKt 256))) =
      mulV R1 (mulV (SK (fld21 (X1Tt 0) 1)) (QKt (fld21 (X1Tt 0) 0))) := by
  have h := X1_misc
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1, h.2.2⟩

theorem c1_j : ∃ j ∈ Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1, invEInv j = 80 := by
  obtain ⟨h1, h2, h3, -, -⟩ := X1_misc'
  have hJ := repK_cE QK_eq (by norm_num : 0 < 512) 225319
  refine ⟨cE 0 225319, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_,
    Subgroup.mem_centralizer_singleton_iff.2 (qE_comm hJ repK_r1 h1)⟩,
    (invEInv_eqK hJ).trans h3⟩
  obtain ⟨t, ht, rfl⟩ := mem_D1.1 hd
  exact (qE_comm hJ (repK_qE (X1D_lt ht)) (h2 t ht)).symm

theorem c1_two : ∃ h : Cz, h * (cR 2 * zCz) * h⁻¹ = cR 1 := by
  obtain ⟨-, -, -, hlt, hH⟩ := X1_misc'
  set h := cE (fld21 (X1Tt 0) 0) (fld21 (X1Tt 0) 1)
  have hh := repK_cE QK_eq hlt (fld21 (X1Tt 0) 1)
  have hr2 : repK ((cR 2 : Cz) : K) (mulV (SK 26805) (QKt 32)) := by
    rw [show cR 2 = cE 32 26805 from rfl]
    exact repK_cE QK_eq (by norm_num) 26805
  have e : h * (cR 2 * zCz) = cR 1 * h :=
    (cz_eq_iff (repK_czmul hh (repK_czmul hr2 repK_zCz)) (repK_czmul repK_r1 hh)).2 hH
  exact ⟨h, by rw [e, mul_inv_cancel_right]⟩

end CC

end CertificateChecks.KernelCo2Census

end
