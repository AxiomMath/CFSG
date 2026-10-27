module

public import Certificates.Kernel.Co2Census.CCXCert
public import Certificates.Kernel.Co2Census.CCKX7
public import Certificates.Kernel.Co2Census.CCK6

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem cR7 : cR 7 = cE 13 1082 := rfl

theorem repK_r7 : repK ((cR 7 : Cz) : K) R7 := by
  rw [cR7]
  exact repK_cE QK_eq (by norm_num) 1082

theorem X7_D' : dlK QKt (mulV (SK 1082) (QKt 13)) = (List.range 32).map X7Dt := X7_D

theorem hex1082 : ∀ i < 1536, ∃ s ∈ centS0 (sElt 1082), repK s (C1082Pt i) :=
  (rec_elt C1082_tree C1082_root C1082_misc cent_1082).1

theorem X7_lift' (j : ℕ) (hj : j < 1536) :
    (X7Lt j < 512 ∧ commK (x7 j) R7 = true) ∧
      ((∃ g < 32, X7Gdt g = j) ∨ (X7Wt j < 32 ∧ commK (x7 j) (QKt (X7Dt (X7Wt j))) = false)) := by
  have h := X7_lift j hj
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, List.any_eq_true,
    List.mem_range, Nat.beq_eq, Bool.not_eq_true'] at h
  exact h

theorem hL7 : ∀ j < 1536, X7Lt j < 512 ∧ commK (mulV (C1082Pt j) (QKt (X7Lt j))) R7 = true :=
  fun j hj => (X7_lift' j hj).1

noncomputable abbrev x7E (j : ℕ) : Cz := liftX hex1082 X7Lt j

theorem repK_x7 {j : ℕ} (hj : j < 1536) : repK ((x7E j : Cz) : K) (x7 j) :=
  (liftX_spec hex1082 hj (hL7 j hj).1).1

theorem x7E_mem {j : ℕ} (hj : j < 1536) : x7E j ∈ XC 7 :=
  Subgroup.mem_centralizer_singleton_iff.2 (liftX_comm (by norm_num) hex1082 hL7 hj)

theorem mem_X7 {u : Cz} (hu : u ∈ XC 7) : ∃ j < 1536, ∃ t < 32, u = x7E j * qE (X7Dt t) := by
  obtain ⟨j, hj, e, he, rfl⟩ := mem_X (by norm_num) cent_1082 hex1082 hL7
    (Subgroup.mem_centralizer_singleton_iff.1 hu)
  have he' : e ∈ (List.range 32).map X7Dt := by rwa [← X7_D']
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he'
  exact ⟨j, hj, t, List.mem_range.1 ht, rfl⟩

theorem mem_D7 {d : Cz} : d ∈ DCi 7 ↔ ∃ t < 32, d = qE (X7Dt t) := by
  rw [mem_DCi_iff cR7 (by norm_num)]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [X7_D'] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
    exact ⟨t, List.mem_range.1 ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, by rw [X7_D']; exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩, rfl⟩

theorem X7D_lt {t : ℕ} (ht : t < 32) : X7Dt t < 512 := by
  have : X7Dt t ∈ dlK QKt R7 := by
    rw [X7_D]
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩
  exact ((mem_dlK repK_r7).1 this).1

theorem qE_comm {a b : Cz} {A B : ℕ} (ha : repK (a : K) A) (hb : repK (b : K) B)
    (h : commK A B = true) : a * b = b * a := by
  unfold commK at h
  exact (cz_eq_iff (repK_czmul ha hb) (repK_czmul hb ha)).2 (Nat.eq_of_beq_eq_true h)

theorem qE_ncomm {a b : Cz} {A B : ℕ} (ha : repK (a : K) A) (hb : repK (b : K) B)
    (h : commK A B = false) : a * b ≠ b * a := by
  unfold commK at h
  exact fun e => Nat.ne_of_beq_eq_false h ((cz_eq_iff (repK_czmul ha hb) (repK_czmul hb ha)).1 e)

theorem c7_comm : ∀ a ∈ DCi 7, ∀ b ∈ DCi 7, a * b = b * a := by
  intro a ha b hb
  obtain ⟨t, ht, rfl⟩ := mem_D7.1 ha
  obtain ⟨t', ht', rfl⟩ := mem_D7.1 hb
  have h := X7_abel (32 * t + t') (by omega)
  rw [show (32 * t + t') / 32 = t by omega, show (32 * t + t') % 32 = t' by omega] at h
  exact qE_comm (repK_qE (X7D_lt ht)) (repK_qE (X7D_lt ht')) h

theorem natCard_D7 : Nat.card (DCi 7) = 32 := by
  have h := K7_rep
  rw [natCard_DCi', cR7]
  exact (rep_facts (by norm_num) h).2.2.2.1

theorem good_of_cxd {y : Cz} (hy : y ∈ Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7) :
    ∃ g < 32, ∃ t < 32, y = x7E (X7Gdt g) * qE (X7Dt t) := by
  obtain ⟨hyD, hyX⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨j, hj, t, ht, rfl⟩ := mem_X7 hyX
  rcases (X7_lift' j hj).2 with ⟨g, hg, rfl⟩ | ⟨hw, hnc⟩
  · exact ⟨g, hg, t, ht, rfl⟩
  · exfalso
    apply qE_ncomm (repK_x7 hj) (repK_qE (X7D_lt hw)) hnc
    have hd : (qE (X7Dt (X7Wt j)) : Cz) ∈ DCi 7 := mem_D7.2 ⟨_, hw, rfl⟩
    have hdt : (qE (X7Dt t) : Cz) ∈ DCi 7 := mem_D7.2 ⟨_, ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hyD _ hd
    have h2 := c7_comm _ hd _ hdt
    set q := (qE (X7Dt t) : Cz)
    set d := (qE (X7Dt (X7Wt j)) : Cz)
    have hc : q⁻¹ * d = d * q⁻¹ := (show Commute d q from h2).symm.inv_left.eq
    calc x7E j * d = x7E j * q * (q⁻¹ * d) := by group
      _ = x7E j * q * (d * q⁻¹) := by rw [hc]
      _ = x7E j * q * d * q⁻¹ := by group
      _ = d * (x7E j * q) * q⁻¹ := by rw [← h1]
      _ = d * x7E j := by group

theorem c7_cxd : Nat.card (Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 : Subgroup Cz) ≤
    Nat.card (DCi 7) ^ 2 := by
  classical
  rw [natCard_D7]
  change Nat.card ↥((Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 : Subgroup Cz) : Set Cz) ≤ _
  rw [Nat.card_coe_set_eq]
  let F : ℕ × ℕ → Cz := fun p => x7E (X7Gdt p.1) * qE (X7Dt p.2)
  have hsub : ((Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 : Subgroup Cz) : Set Cz) ⊆
      ((Finset.range 32 ×ˢ Finset.range 32).image F : Set Cz) := by
    intro y hy
    obtain ⟨g, hg, t, ht, rfl⟩ := good_of_cxd hy
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(g, t), Finset.mem_product.2
      ⟨Finset.mem_range.2 hg, Finset.mem_range.2 ht⟩, rfl⟩)
  calc Set.ncard ((Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 : Subgroup Cz) : Set Cz)
      ≤ Set.ncard ((Finset.range 32 ×ˢ Finset.range 32).image F : Set Cz) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ (Finset.range 32 ×ˢ Finset.range 32).card := by
        rw [Set.ncard_coe_finset]
        exact Finset.card_image_le
    _ = 32 ^ 2 := by simp

theorem c7_zd : Nat.card {d : Cz // d ∈ DCi 7 ∧ ∀ x ∈ XC 7, x * d = d * x} ≤ 2 := by
  have key : ∀ d : Cz, d ∈ DCi 7 → (∀ x ∈ XC 7, x * d = d * x) →
      d ∈ ({(qE 0 : Cz), (qE 256 : Cz)} : Set Cz) := by
    intro d hd hcen
    obtain ⟨t, ht, rfl⟩ := mem_D7.1 hd
    have h := X7_zd t ht
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq,
      Bool.not_eq_true'] at h
    rcases h with (h | h) | ⟨hj, hnc⟩
    · left
      rw [h]
    · right
      rw [h]
      exact Set.mem_singleton _
    · exact absurd (hcen _ (x7E_mem hj)) (qE_ncomm (repK_x7 hj) (repK_qE (X7D_lt ht)) hnc)
  calc Nat.card {d : Cz // d ∈ DCi 7 ∧ ∀ x ∈ XC 7, x * d = d * x}
      ≤ Nat.card ({(qE 0 : Cz), (qE 256 : Cz)} : Set Cz) :=
        Nat.card_le_card_of_injective (fun d => ⟨d.1, key d.1 d.2.1 d.2.2⟩)
          (fun a b h => Subtype.ext (Subtype.mk.inj h))
    _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

noncomputable def za7E (a : ℕ) : Cz := cE (ZA7.getD a (0, 0)).1 (ZA7.getD a (0, 0)).2

theorem ZA7_lt : ∀ a < 8, (ZA7.getD a (0, 0)).1 < 512 := by decide

theorem repK_za7 {a : ℕ} (ha : a < 8) : repK ((za7E a : Cz) : K) (za7 a) :=
  repK_cE QK_eq (ZA7_lt a ha) _

theorem c7_za : 8 ≤ Nat.card {a : Cz // a ∈ Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 ∧
    ∀ x ∈ XC 7, x * a = a * x} := by
  have hfacts : ∀ a < 8, (commK (za7 a) R7 = true ∧
      (∀ t < 32, commK (za7 a) (QKt (X7Dt t)) = true) ∧
      (∀ j < 1536, commK (za7 a) (x7 j) = true)) ∧ ∀ b < a, za7 b ≠ za7 a := by
    intro a ha
    have h := X7_za a ha
    simp only [letB_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      Bool.not_eq_true'] at h
    exact ⟨⟨h.1.1.1, h.1.1.2, h.1.2⟩, fun b hb => Nat.ne_of_beq_eq_false (h.2 b hb)⟩
  have hmem : ∀ a < 8, za7E a ∈ Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 ∧
      ∀ x ∈ XC 7, x * za7E a = za7E a * x := by
    intro a ha
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hfacts a ha
    have hy := repK_za7 ha
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_,
      Subgroup.mem_centralizer_singleton_iff.2 (qE_comm hy repK_r7 h1)⟩, fun x hx => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := mem_D7.1 hd
      exact (qE_comm hy (repK_qE (X7D_lt ht)) (h2 t ht)).symm
    · obtain ⟨j, hj, t, ht, rfl⟩ := mem_X7 hx
      have e1 := qE_comm hy (repK_x7 hj) (h3 j hj)
      have e2 := qE_comm hy (repK_qE (X7D_lt ht)) (h2 t ht)
      rw [mul_assoc, ← e2, ← mul_assoc, ← e1, mul_assoc]
  let f : Fin 8 → {a : Cz // a ∈ Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 ∧
      ∀ x ∈ XC 7, x * a = a * x} := fun a => ⟨za7E a, hmem a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : za7E a = za7E b := congrArg Subtype.val hab
    have eR := (cz_eq_iff (repK_za7 a.2) (repK_za7 b.2)).1 e
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : (a : ℕ) = b => hne (Fin.ext h)) with h | h
    · exact (hfacts b b.2).2 a h eR
    · exact (hfacts a a.2).2 b h eR.symm
  calc 8 = Nat.card (Fin 8) := (Nat.card_fin 8).symm
    _ ≤ _ := Nat.card_le_card_of_injective f hf

theorem hmin7OK_spec {c : ℕ} (h : hmin7OK c = true) :
    fld21 (X7Ht c) 0 < 512 ∧ certXOK QKt 5 (X7Ht c) R7 (fld21 (X7Ht c) 4) = true ∧
      (fld21 (X7Ht c) 1 = 0 →
        certProd QKt 5 (X7Ht c) (QKt (fld21 (X7Ht c) 0)) (fld21 (X7Ht c) 4) =
          mulV (SK 0) (QKt 256)) ∧
      (fld21 (X7Ht c) 1 ≠ 0 →
        certProd QKt 5 (X7Ht c) (QKt (fld21 (X7Ht c) 0)) (fld21 (X7Ht c) 4) ≠ IDP ∧
        fld21 (X7Ht c) 2 < 512 ∧
        mulV (mulV (SK (fld21 (X7Ht c) 3)) (QKt (fld21 (X7Ht c) 2)))
            (mulV R7 (certProd QKt 5 (X7Ht c) (QKt (fld21 (X7Ht c) 0)) (fld21 (X7Ht c) 4))) =
          mulV R7 (mulV (SK (fld21 (X7Ht c) 3)) (QKt (fld21 (X7Ht c) 2)))) := by
  unfold hmin7OK at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun hk => ?_, fun hk => ?_⟩
  · rw [if_pos hk, Nat.beq_eq] at h3
    exact h3
  · rw [if_neg hk] at h3
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq] at h3
    exact ⟨Nat.ne_of_beq_eq_false h3.1.1, h3.1.2, h3.2⟩

theorem c7_hmin : ∀ N : Subgroup Cz, N ≤ DCi 7 → (∀ x ∈ XC 7, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
    N ≠ ⊥ → zCz ∉ N → ∃ d ∈ N, d ≠ 1 ∧ ∃ h : Cz, h * (cR 7 * d) * h⁻¹ = cR 7 := by
  intro N hND hNX hN hzN
  obtain ⟨d, hdN, hd1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN
  obtain ⟨t, ht, rfl⟩ := mem_D7.1 (hND hdN)
  have hc := X7_hcov t ht
  simp only [Bool.or_eq_true, Nat.beq_eq, List.any_eq_true, List.mem_range] at hc
  rcases hc with h0 | ⟨c, hc, hce⟩
  · exact absurd (by rw [h0]; exact qE0 : (qE (X7Dt t) : Cz) = 1) hd1
  obtain ⟨-, hx, hk0, hk1⟩ := hmin7OK_spec (X7_hmin c hc)
  rw [hce] at hk0 hk1
  have hd := repK_qE (X7D_lt ht)
  obtain ⟨hrows, hmem⟩ := certElt_facts repK_r7 hd _ (certXOK_spec hx)
  have htN := hmem N hdN fun x hx' n hn =>
    hNX x (Subgroup.mem_centralizer_singleton_iff.2 hx') n hn
  by_cases hk : fld21 (X7Ht c) 1 = 0
  · exfalso
    apply hzN
    have e := (cz_eq_iff hrows repK_zCz).2 (hk0 hk)
    rw [← e]
    exact htN
  · obtain ⟨hne, hlt, hH⟩ := hk1 hk
    refine ⟨_, htN, fun e => hne ((cz_eq_iff hrows repK_one').1 e), ?_⟩
    set h := cE (fld21 (X7Ht c) 2) (fld21 (X7Ht c) 3)
    have hh := repK_cE QK_eq hlt (fld21 (X7Ht c) 3)
    have e : h * (cR 7 * _) = cR 7 * h :=
      (cz_eq_iff (repK_czmul hh (repK_czmul repK_r7 hrows)) (repK_czmul repK_r7 hh)).2 hH
    exact ⟨h, by rw [e, mul_inv_cancel_right]⟩

end CC

end CertificateChecks.KernelCo2Census

end
