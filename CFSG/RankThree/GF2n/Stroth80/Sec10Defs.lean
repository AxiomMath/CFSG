module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec10Hyp (hc : Ctx M Q Z B) (n : ℕ) : Prop where
  width : Width Q Z n
  n_gt : 2 < n
  noA2 : NoA2 Q Z (LB M Q B)
  gen : GenByB M Q B
  alt : ∀ t ∈ LB M Q B, t ∉ Q → Rt M (LB M Q B) t = LB M Q B ∨ SLlike hc t
  ex : ∃ t ∈ LB M Q B, t ∉ Q ∧ SLlike hc t

omit [Finite G] in
@[expose] def Good101 (M Q Z B : Subgroup G) (t : G) : Prop :=
  (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = t) ∧ t ∈ M ∧ t ∉ Q ∧ t ∈ QB B ∧
    Rt M (LB M Q B) t ≠ LB M Q B

omit [Finite G] in
@[expose] def Good103 (M Q Z B : Subgroup G) (t : G) : Prop :=
  Good101 M Q Z B t ∧ Vt M (LB M Q B) B Z t = (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z

theorem Good101.mem_LB {t : G} (h : Good101 M Q Z B t) : t ∈ LB M Q B := by
  unfold LB
  exact Subgroup.mem_sup_right ⟨h.2.2.2.1, h.2.1⟩

theorem Sec10Hyp.toSec5 {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) : Sec5Hyp hc n t :=
  ⟨H.width, H.n_gt, H.noA2, H.gen, ht, htQ⟩

theorem SLlike.exists_SLMNat {hc : Ctx M Q Z B} {t : G} (h : SLlike hc t) :
    ∃ m : ℕ, 2 ≤ m ∧ SLMNat hc t m := by
  obtain ⟨m, hm, h | ⟨hm2, hsp⟩⟩ := h
  · exact ⟨m, hm, h⟩
  · subst hm2
    obtain ⟨K, fK, finK, hK, hrep⟩ := hsp
    exact ⟨2, le_rfl, K, fK, finK, hK, NaturalRep.sp_one_to_sl_two hrep⟩

theorem SLMNat.toSLNat {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : SLMNat hc t m) (hm : 2 ≤ m) :
    SLNat hc t := by
  obtain ⟨K, fK, finK, hK, hrep⟩ := h
  exact ⟨K, fK, finK, hK, m, hm, hrep⟩

theorem Sec10Hyp.slLike {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : Good101 M Q Z B t) : SLlike hc t := by
  rcases H.alt t ht.mem_LB ht.2.2.1 with h | h
  · exact absurd h ht.2.2.2.2
  · exact h

theorem SLMNat.card_Vt {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : SLMNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1) := by
  obtain ⟨K, fK, finK, hK, hrep⟩ := h
  obtain ⟨φ, -, -, -, hN, ψ, -⟩ := hrep
  haveI : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card (↥(Vt M (LB M Q B) B Z t) ⧸
      Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card K ^ m := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      ← Nat.card_eq_fintype_card (α := K)]
  have h2 : Nat.card (Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sec39_Z_le_Vt (M := M) (L := LB M Q B)
      (B := B) (Z := Z) (t := t))).toEquiv
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Z.subgroupOf (Vt M (LB M Q B) B Z t))
  rw [h1, h2, hK] at h3
  rw [h3, pow_succ]

theorem SLMNat.unique {hc : Ctx M Q Z B} {t : G} {m m' : ℕ} (h : SLMNat hc t m)
    (h' : SLMNat hc t m') : m = m' := by
  have hq : 2 ≤ Nat.card Z := by
    have := hc.hyp.q4
    omega
  have e : Nat.card Z ^ (m + 1) = Nat.card Z ^ (m' + 1) :=
    (SLMNat.card_Vt h).symm.trans (SLMNat.card_Vt h')
  have := Nat.pow_right_injective hq e
  omega

private theorem mul_mem_conj_LB_iff (hc : Ctx M Q Z B) {t y m : G} (hy : y ∈ Q) (hm : m ∈ M) :
    t * y ∈ conjSubgroup m (LB M Q B) ↔ t ∈ conjSubgroup m (LB M Q B) := by
  have hyL : y ∈ conjSubgroup m (LB M Q B) := by
    rw [mem_conjSubgroup]
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hm)) y).mp hy
    exact sec39_Q_le_LB (by simpa using h)
  exact (conjSubgroup m (LB M Q B)).mul_mem_cancel_right hyL

theorem Rt_mul_of_mem_Q (hc : Ctx M Q Z B) {t y : G} (hy : y ∈ Q) :
    Rt M (LB M Q B) (t * y) = Rt M (LB M Q B) t :=
  iSup_congr fun _ => iSup_congr fun hm =>
    iSup_congr_Prop (mul_mem_conj_LB_iff hc hy hm) fun _ => rfl

theorem Vt_mul_of_mem_Q (hc : Ctx M Q Z B) {t y : G} (hy : y ∈ Q) :
    Vt M (LB M Q B) B Z (t * y) = Vt M (LB M Q B) B Z t :=
  congrArg (Z ⊔ ·) <| iSup_congr fun _ => iSup_congr fun hm =>
    iSup_congr_Prop (mul_mem_conj_LB_iff hc hy hm) fun _ => rfl

theorem Ctx.CN_mul_of_mem_Q (hc : Ctx M Q Z B) {t y : G} (hy : y ∈ Q) :
    hc.CN (t * y) = hc.CN t := by
  ext r
  change r ∈ CNt M (LB M Q B) B Z (t * y) ↔ r ∈ CNt M (LB M Q B) B Z t
  simp only [CNt, Rt_mul_of_mem_Q hc hy, Vt_mul_of_mem_Q hc hy]

theorem SLMNat.mul_of_mem_Q {hc : Ctx M Q Z B} {t y : G} {m : ℕ} (hy : y ∈ Q) :
    SLMNat hc (t * y) m ↔ SLMNat hc t m := by
  unfold SLMNat
  rw [Rt_mul_of_mem_Q hc hy, Vt_mul_of_mem_Q hc hy, Ctx.CN_mul_of_mem_Q hc hy]

end CFSG.RankThree.GF2n.Stroth80
