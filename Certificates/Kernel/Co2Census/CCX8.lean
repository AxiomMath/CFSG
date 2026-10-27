module

public import Certificates.Kernel.Co2Census.CCXGlue
public import Certificates.Kernel.Co2Census.CCKX8
public import CFSG.Sporadic.Co2Smith.CCFacts
public import CFSG.Sporadic.Co2Smith.FusionC

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

theorem card_sub_enum {G : Type*} [Group G] {X : Subgroup G} {N : ℕ} (f : ℕ → G)
    (hmem : ∀ k < N, f k ∈ X) (hsurj : ∀ u ∈ X, ∃ k < N, f k = u)
    (hinj : ∀ k < N, ∀ k' < N, f k = f k' → k = k') (P : G → Prop) [DecidablePred P] :
    Nat.card {u : X // P u} = ((Finset.range N).filter fun k => P (f k)).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun u => ⟨Classical.choose (hsurj u.1 u.1.2), Finset.mem_filter.2
        ⟨Finset.mem_range.2 (Classical.choose_spec (hsurj u.1 u.1.2)).1, by
          rw [(Classical.choose_spec (hsurj u.1 u.1.2)).2]
          exact u.2⟩⟩
      invFun := fun k => ⟨⟨f k.1, hmem _ (Finset.mem_range.1 (Finset.mem_filter.1 k.2).1)⟩,
        (Finset.mem_filter.1 k.2).2⟩
      left_inv := fun u => Subtype.ext (Subtype.ext (Classical.choose_spec (hsurj u.1 u.1.2)).2)
      right_inv := fun k => Subtype.ext ?_ }
  have h1 := Classical.choose_spec (hsurj (f k.1) (hmem _ (Finset.mem_range.1
    (Finset.mem_filter.1 k.2).1)))
  exact hinj _ h1.1 _ (Finset.mem_range.1 (Finset.mem_filter.1 k.2).1) h1.2

theorem strict_inj' {V : ℕ → ℕ} {n : ℕ} (h : ∀ g < n, V g < V (g + 1)) :
    ∀ g ≤ n, ∀ g' ≤ n, V g = V g' → g = g' := by
  have mono : ∀ a b, a < b → b ≤ n → V a < V b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
      · exact (ih h1 (by omega)).trans (h b (by omega))
      · rw [h1]
        exact h b (by omega)
  intro g hg g' hg' e
  rcases lt_trichotomy g g' with h1 | h1 | h1
  · exact absurd e (ne_of_lt (mono _ _ h1 hg'))
  · exact h1
  · exact absurd e.symm (ne_of_lt (mono _ _ h1 hg))

section CC


theorem hex144 : ∀ i < 384, ∃ s ∈ centS0 (sElt 144), repK s (C144Pt i) :=
  (rec_elt C144_tree C144_root C144_misc cent_144).1

theorem hL8 : ∀ j < 384, X8Lt j < 512 ∧ commK (mulV (C144Pt j) (QKt (X8Lt j)))
    (mulV (SK 144) (QKt 0)) = true := by
  intro j hj
  have h := X8_lift j hj
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h

noncomputable def u8E (k : ℕ) : Cz := liftX hex144 X8Lt (k / 16) * qE (D8.getD (k % 16) 0)

theorem D8_nodup : D8.Nodup := by decide

theorem D8_lt : ∀ e ∈ D8, e < 512 := by decide

theorem D8_mem {t : ℕ} (ht : t < 16) : D8.getD t 0 ∈ D8 := by
  rw [List.getD_eq_getElem _ _ (by rw [show D8.length = 16 by rfl]; exact ht)]
  exact List.getElem_mem _

theorem repK_u8 {k : ℕ} (hk : k < 6144) : repK ((u8E k : Cz) : K) (u8 k) := by
  have hj : k / 16 < 384 := by omega
  have ht : D8.getD (k % 16) 0 < 512 := D8_lt _ (D8_mem (by omega))
  exact repK_czmul (liftX_spec hex144 hj (hL8 _ hj).1).1 (repK_qE ht)

theorem mem_D8 {e : ℕ} : e ∈ D8 ↔ e < 512 ∧ (qE e : Cz) * cE 0 144 = cE 0 144 * qE e := by
  rw [← X8_D]
  exact mem_dlK (repK_cE QK_eq (by norm_num) 144)

theorem u8E_mem {k : ℕ} (hk : k < 6144) : u8E k ∈ XC 8 := by
  have hj : k / 16 < 384 := by omega
  have hm : D8.getD (k % 16) 0 ∈ D8 := D8_mem (by omega)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := liftX_comm (by norm_num) hex144 hL8 hj
  have h2 := (mem_D8.1 hm).2
  change u8E k * cE 0 144 = cE 0 144 * u8E k
  unfold u8E
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem u8E_surj : ∀ u ∈ XC 8, ∃ k < 6144, u8E k = u := by
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff] at hu
  obtain ⟨j, hj, e, he, rfl⟩ := mem_X (by norm_num) cent_144 hex144 hL8 hu
  change e ∈ dlK QKt R8 at he
  rw [X8_D] at he
  have ht : D8.idxOf e < 16 := List.idxOf_lt_length_of_mem he
  refine ⟨16 * j + D8.idxOf e, by omega, ?_⟩
  unfold u8E
  rw [show (16 * j + D8.idxOf e) / 16 = j by omega, show (16 * j + D8.idxOf e) % 16 =
    D8.idxOf e by omega, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem he),
    List.getElem_idxOf]

theorem u8E_inj : ∀ k < 6144, ∀ k' < 6144, u8E k = u8E k' → k = k' := by
  intro k hk k' hk' h
  have hinj := (rec_elt C144_tree C144_root C144_misc cent_144).2
  obtain ⟨h1, h2⟩ := liftX_inj hex144 hinj (fun j hj => (hL8 j hj).1) (by omega) (by omega) h
  have ht : D8.getD (k % 16) 0 < 512 := D8_lt _ (D8_mem (by omega))
  have ht' : D8.getD (k' % 16) 0 < 512 := D8_lt _ (D8_mem (by omega))
  have h3 := qE_injOn ht ht' (Subtype.ext h2)
  rw [List.getD_eq_getElem _ _ (by rw [show D8.length = 16 by rfl]; omega),
    List.getD_eq_getElem _ _ (by rw [show D8.length = 16 by rfl]; omega)] at h3
  have h4 := (List.Nodup.getElem_inj_iff D8_nodup).1 h3
  omega

theorem sqrtIn_eq {y : XC 8} {R : ℕ} (hy : repK ((y : Cz) : K) R) :
    sqrtIn y = ((Finset.range 6144).filter fun k => X8Vt (X8Gt k) = R).card := by
  classical
  unfold sqrtIn
  have e1 : Nat.card {u : XC 8 // u * u = y} = Nat.card {u : XC 8 // (u : Cz) * u = y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [← Subgroup.coe_mul, Subtype.ext_iff])
  rw [e1, card_sub_enum u8E (fun k hk => u8E_mem hk) u8E_surj u8E_inj
    (fun u => u * u = (y : Cz))]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have hs := X8_sq k hk'
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hs
  rw [cz_eq_iff (repK_czmul (repK_u8 hk') (repK_u8 hk')) hy, hs.2]

theorem cnt_eq (g : ℕ) : ((List.range 6144).filter fun k => Nat.beq (X8Gt k) g).length =
    ((Finset.range 6144).filter fun k => X8Gt k = g).card := by
  rw [length_filter_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k _
  rw [Nat.beq_eq]

theorem X8_inc' : ∀ g < 168, X8Vt g < X8Vt (g + 1) := fun g hg => by
  have h := X8_inc g hg
  rwa [Nat.blt_eq] at h

theorem filter_V {R g0 : ℕ} (hg0 : g0 < 169) (hR : X8Vt g0 = R) :
    ((Finset.range 6144).filter fun k => X8Vt (X8Gt k) = R) =
      (Finset.range 6144).filter fun k => X8Gt k = g0 := by
  apply Finset.filter_congr
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have hs := X8_sq k hk'
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hs
  rw [← hR]
  have h1 := hs.1
  exact ⟨fun h => strict_inj' X8_inc' (X8Gt k) (by omega) g0 (by omega) h, fun h => by rw [h]⟩

theorem w8_rows : repK ((qE 269 : Cz) : K) (QKt 269) := repK_qE (by norm_num)

theorem X8_misc' : X8wt 0 < 169 ∧ X8Vt (X8wt 0) = QKt 269 ∧
    ((List.range 6144).filter fun k => Nat.beq (X8Gt k) (X8wt 0)).length = 384 ∧
    commK (QKt 269) R8 = true ∧ QKt 269 ≠ IDP ∧ fld21 (X8Ht 0) 0 < 512 ∧
    mulV (mulV (SK (fld21 (X8Ht 0) 1)) (QKt (fld21 (X8Ht 0) 0))) (mulV R8 (QKt 269)) =
      mulV R8 (mulV (SK (fld21 (X8Ht 0) 1)) (QKt (fld21 (X8Ht 0) 0))) := by
  have h := X8_misc
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, Nat.ne_of_beq_eq_false h5, h6, h7⟩

theorem sqrtIn_eq_384 (y : XC 8) (hw : (qE 269 : Cz) ∈ XC 8) :
    sqrtIn y = 384 ↔ y = ⟨qE 269, hw⟩ := by
  obtain ⟨hlt, hV, hcnt, -, -, -, -⟩ := X8_misc'
  obtain ⟨e, he, n, -, hyc⟩ := exists_cE (y : Cz)
  have hyR : repK ((y : Cz) : K) (mulV (SK n) (QKt e)) := hyc ▸ repK_cE QK_eq he n
  rw [sqrtIn_eq hyR]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (by rw [h]; norm_num)
    have hk' := Finset.mem_filter.1 hk
    have hs := X8_sq k (Finset.mem_range.1 hk'.1)
    simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hs
    rw [filter_V hs.1 hk'.2, ← cnt_eq] at h
    have hc := X8_cnt (X8Gt k) hs.1
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
    rcases hc with hc | hc
    · apply Subtype.ext
      apply (cz_eq_iff hyR w8_rows).2
      rw [← hk'.2, hc, hV]
    · exact absurd h (Nat.ne_of_beq_eq_false hc)
  · rintro rfl
    rw [filter_V hlt (hV.trans (repK_unique w8_rows hyR)), ← cnt_eq, hcnt]

theorem cc_c3 : ∃ w : Cz, w ∈ CFSG.pCore 2 Cz ∧ w ≠ 1 ∧ w * cR 8 = cR 8 * w ∧
    (∃ h : Cz, h * (cR 8 * w) * h⁻¹ = cR 8) ∧
    ∀ hw : w ∈ XC 8, ∀ α : XC 8 ≃* XC 8, α ⟨w, hw⟩ = ⟨w, hw⟩ := by
  obtain ⟨-, -, -, hc, hne, hlt, hH⟩ := X8_misc'
  have hr : repK ((cR 8 : Cz) : K) R8 := by
    rw [show cR 8 = cE 0 144 from rfl]
    exact repK_cE QK_eq (by norm_num) 144
  have hcomm : (qE 269 : Cz) * cR 8 = cR 8 * qE 269 := by
    unfold commK at hc
    exact (cz_eq_iff (repK_czmul w8_rows hr) (repK_czmul hr w8_rows)).2 (Nat.eq_of_beq_eq_true hc)
  refine ⟨qE 269, (qE 269).2, fun e => hne ((cz_eq_iff w8_rows repK_one').1 e), hcomm, ?_,
    fun hw α => ?_⟩
  · set h := cE (fld21 (X8Ht 0) 0) (fld21 (X8Ht 0) 1)
    have hh := repK_cE QK_eq hlt (fld21 (X8Ht 0) 1)
    have e : h * (cR 8 * qE 269) = cR 8 * h :=
      (cz_eq_iff (repK_czmul hh (repK_czmul hr w8_rows)) (repK_czmul hr hh)).2 hH
    exact ⟨h, by rw [e, mul_inv_cancel_right]⟩
  · exact (sqrtIn_eq_384 _ hw).1 ((sqrtIn_mulEquiv α _).trans ((sqrtIn_eq_384 _ hw).2 rfl))

end CC

end CertificateChecks.KernelCo2Census

end
