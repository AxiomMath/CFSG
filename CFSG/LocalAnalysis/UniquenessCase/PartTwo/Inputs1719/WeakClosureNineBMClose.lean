module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

variable {i : Fin 4}

@[expose] def CloseInvChk (tLit : List (List ℕ)) (Es : List (List (List ℕ))) (ws : List (List ℕ)) :
    Bool :=
  tLit.length == ws.length &&
  (tLit.zip ws).all fun p => !(cinvol p.1) || Es.any (fun E => E.contains p.1) ||
    (tLit.contains p.2 && !(ccomm p.1 (cconj p.2 p.1)))

theorem mem_of_normal_elab {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit)
    {Es : List (List (List ℕ))} {ws : List (List ℕ)} (h : CloseInvChk tLit Es ws = true)
    {E : Subgroup ↥(GB i)} (hET : E ≤ Tb i) (hTE : Tb i ≤ normalizer (E : Set ↥(GB i)))
    (hEe : IsElemAbelian 2 E) {x : ↥(GB i)} (hx : x ∈ E) (hx1 : x ≠ 1) :
    ∃ L ∈ Es, code x.1 ∈ L := by
  simp only [CloseInvChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true, List.contains_iff_mem] at h
  obtain ⟨hlen, hall⟩ := h
  have hxc : code x.1 ∈ tLit := (mem_Tb_iff i hT x).1 (hET hx)
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hxc
  have hk' : k < ws.length := hlen ▸ hk
  have hz : (code x.1, ws[k]) ∈ tLit.zip ws := by
    rw [← hkx]
    exact List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩
  have hinv : cinvol (code x.1) = true := by
    rw [cinvol_iff]
    refine ⟨fun h1 => hx1 (Subtype.ext h1), ?_⟩
    rw [← Subgroup.coe_mul, ← pow_two, hEe.2 x hx]
    rfl
  rcases hall _ hz with (h1 | h1) | ⟨h1, h2⟩
  · rw [hinv] at h1
    exact absurd h1 (by decide)
  · exact h1
  · exfalso
    simp only at h1 h2
    obtain ⟨w, hwT, hwc⟩ := exists_Tb i hT h1
    have hwx : w * x * w⁻¹ ∈ E := (mem_normalizer_iff.1 (hTE hwT) x).1 hx
    have hc : x * (w * x * w⁻¹) = (w * x * w⁻¹) * x := by
      have := hEe.1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨_, hwx⟩)
    have h3 : ccomm (code x.1) (cconj (code w.1) (code x.1)) = true := by
      rw [← code_conj, ccomm_iff]
      have := congrArg Subtype.val hc
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    rw [← hwc, h3] at h2
    exact Bool.noConfusion h2

@[expose] def xsub (i : Fin 4) (L : List (List ℕ)) (h1 : cid ∈ L)
    (hm : ∀ c ∈ L, ∀ d ∈ L, Core.cmul c d ∈ L) : Subgroup ↥(GB i) where
  carrier := {x | code x.1 ∈ L}
  one_mem' := by
    change code (1 : P16) ∈ L
    rw [code_one]
    exact h1
  mul_mem' := by
    intro a b ha hb
    change code (a.1 * b.1) ∈ L
    rw [code_mul]
    exact hm _ ha _ hb
  inv_mem' := by
    intro a ha
    have hpow : ∀ n : ℕ, code (a ^ n).1 ∈ L := by
      intro n
      induction n with
      | zero => rw [pow_zero, Subgroup.coe_one, code_one]; exact h1
      | succ n ih => rw [pow_succ, Subgroup.coe_mul, code_mul]; exact hm _ ih _ ha
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)))
    change code (a⁻¹).1 ∈ L
    rw [← hn]
    exact hpow n

@[expose] def ce4 (a b : List ℕ) : List (List ℕ) := [cid, a, b, Core.cmul a b]

@[expose] def SubsChk (qL : List (List ℕ)) (subs : List (List (List ℕ)))
    (idx : List (List (ℕ × ℕ × ℕ × ℕ))) : Bool :=
  subs.all (fun W => W.contains cid && W.all qL.contains && NFA6.Core.nodupB W &&
    W.all fun x => W.all fun y => W.contains (Core.cmul x y)) &&
  qL.length == idx.length &&
  (qL.zip idx).all fun pa => pa.2.length == qL.length && (qL.zip pa.2).all fun pb =>
    pa.1 == cid || pb.1 == cid || pa.1 == pb.1 ||
    (decide (pb.2.1 < subs.length) && (subs.getD pb.2.1 []).length == 4 &&
      NFA6.Core.setEq (ce4 pa.1 pb.1) (subs.getD pb.2.1 []) &&
      [pb.2.2.1, pb.2.2.2.1, pb.2.2.2.2].all (fun k => decide (k < subs.length) &&
        (subs.getD k []).length == 8 && (subs.getD k []).contains pa.1 &&
        (subs.getD k []).contains pb.1) &&
      qL.all fun c => (ce4 pa.1 pb.1).contains c ||
        [pb.2.2.1, pb.2.2.2.1, pb.2.2.2.2].any fun k => (subs.getD k []).contains c)

theorem nodup_of_nodupB' : ∀ {l : List (List ℕ)}, NFA6.Core.nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [NFA6.Core.nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodup_of_nodupB' h.2⟩
    rw [List.contains_iff_mem.mpr ha] at h
    exact Bool.noConfusion h.1

theorem setEq_mem' {E F : List (List ℕ)} (h : NFA6.Core.setEq E F = true) (c : List ℕ) :
    c ∈ E ↔ c ∈ F := by
  simp only [NFA6.Core.setEq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1 c, h.2 c⟩

theorem subsChk_parts {qL : List (List ℕ)} {subs : List (List (List ℕ))}
    {idx : List (List (ℕ × ℕ × ℕ × ℕ))} (h : SubsChk qL subs idx = true) :
    (∀ W ∈ subs, cid ∈ W ∧ (∀ c ∈ W, c ∈ qL) ∧ W.Nodup ∧
      ∀ x ∈ W, ∀ y ∈ W, Core.cmul x y ∈ W) ∧
    qL.length = idx.length ∧
    ∀ ia (hia : ia < qL.length) ib (hib : ib < qL.length),
      qL[ia] = cid ∨ qL[ib] = cid ∨ qL[ia] = qL[ib] ∨
      ((idx.getD ia []).getD ib (0, 0, 0, 0)).1 < subs.length ∧
      (subs.getD ((idx.getD ia []).getD ib (0, 0, 0, 0)).1 []).length = 4 ∧
      (∀ c, c ∈ ce4 qL[ia] qL[ib] ↔ c ∈ subs.getD ((idx.getD ia []).getD ib (0, 0, 0, 0)).1 []) ∧
      (∀ k ∈ [((idx.getD ia []).getD ib (0, 0, 0, 0)).2.1,
          ((idx.getD ia []).getD ib (0, 0, 0, 0)).2.2.1,
          ((idx.getD ia []).getD ib (0, 0, 0, 0)).2.2.2],
        k < subs.length ∧ (subs.getD k []).length = 8 ∧ qL[ia] ∈ subs.getD k [] ∧
          qL[ib] ∈ subs.getD k []) ∧
      ∀ c ∈ qL, c ∈ ce4 qL[ia] qL[ib] ∨
        ∃ k ∈ [((idx.getD ia []).getD ib (0, 0, 0, 0)).2.1,
          ((idx.getD ia []).getD ib (0, 0, 0, 0)).2.2.1,
          ((idx.getD ia []).getD ib (0, 0, 0, 0)).2.2.2], c ∈ subs.getD k [] := by
  simp only [SubsChk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq,
    Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hsubs, hlen⟩, hpairs⟩ := h
  refine ⟨fun W hW => ?_, hlen, fun ia hia ib hib => ?_⟩
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hsubs W hW
    exact ⟨h1, h2, nodup_of_nodupB' h3, h4⟩
  · have hia' : ia < idx.length := hlen ▸ hia
    have hz : (qL[ia], idx[ia]) ∈ qL.zip idx := List.mem_iff_getElem.2 ⟨ia, by simp [hia, hia'], by simp⟩
    obtain ⟨hl2, hrow⟩ := hpairs _ hz
    have hib' : ib < idx[ia].length := by simp only at hl2; omega
    have hz2 : (qL[ib], idx[ia][ib]) ∈ qL.zip idx[ia] :=
      List.mem_iff_getElem.2 ⟨ib, by simp [hib, hib'], by simp⟩
    have hgi : (idx.getD ia []).getD ib (0, 0, 0, 0) = idx[ia][ib] := by
      rw [List.getD_eq_getElem _ _ hia', List.getD_eq_getElem _ _ hib']
    rw [hgi]
    rcases hrow _ hz2 with ((h1 | h1) | h1) | ⟨⟨⟨⟨⟨hk, hl⟩, hs⟩, h8⟩, hcov⟩⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · refine Or.inr (Or.inr (Or.inr ⟨hk, hl, setEq_mem' hs, fun k hk' => ?_, fun c hc => ?_⟩))
      · obtain ⟨⟨⟨h5, h6⟩, h7⟩, h8'⟩ := h8 k hk'
        exact ⟨h5, h6, h7, h8'⟩
      · rcases hcov c hc with h5 | h5
        · exact Or.inl h5
        · exact Or.inr h5

theorem xdesc_xsub {Q : Subgroup ↥(GB i)} {qL : List (List ℕ)} (hQ : XDesc Q qL)
    {W : List (List ℕ)} (h1 : cid ∈ W) (h2 : ∀ c ∈ W, c ∈ qL)
    (hm : ∀ c ∈ W, ∀ d ∈ W, Core.cmul c d ∈ W) : XDesc (xsub i W h1 hm) W :=
  ⟨fun _ => Iff.rfl, fun c hc => by
    obtain ⟨x, -, rfl⟩ := hQ.surj c (h2 c hc)
    exact ⟨x, hc, rfl⟩⟩

theorem mem_ce4_iff {a b x : ↥(GB i)} :
    code x.1 ∈ ce4 (code a.1) (code b.1) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  simp only [ce4, List.mem_cons, List.not_mem_nil, or_false, ← code_one, ← code_mul, code_inj,
    ← Subgroup.coe_one, ← Subgroup.coe_mul]
  simp only [Subtype.ext_iff, Subgroup.coe_one]

theorem exists_listed {Q : Subgroup ↥(GB i)} {qL : List (List ℕ)} (hQ : XDesc Q qL)
    (hQnd : qL.Nodup) (hQ16 : qL.length = 16) {subs : List (List (List ℕ))}
    {idx : List (List (ℕ × ℕ × ℕ × ℕ))} (h : SubsChk qL subs idx = true)
    {U : Subgroup ↥(GB i)} (hUQ : U ≤ Q) (hU4 : 4 ≤ Nat.card U) :
    U = Q ∨ ∃ k < subs.length, XDesc U (subs.getD k []) := by
  obtain ⟨hsubs, -, hpairs⟩ := subsChk_parts h
  have hQc : Nat.card Q = 16 := by rw [hQ.card hQnd, hQ16]
  have hdvd : Nat.card U ∣ 16 := by
    have := card_dvd_of_le hUQ
    rwa [hQc] at this
  have hW : ∀ k < subs.length, ∃ W : Subgroup ↥(GB i), W ≤ Q ∧ XDesc W (subs.getD k []) ∧
      Nat.card W = (subs.getD k []).length := by
    intro k hk
    have hmem : subs.getD k [] ∈ subs := by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    obtain ⟨h1, h2, h3, h4⟩ := hsubs _ hmem
    refine ⟨xsub i _ h1 h4, fun x hx => (hQ.mem x).2 (h2 _ hx), xdesc_xsub hQ h1 h2 h4, ?_⟩
    exact (xdesc_xsub hQ h1 h2 h4).card h3
  have hcases : Nat.card U = 4 ∨ Nat.card U = 8 ∨ Nat.card U = 16 := by
    have hle16 : Nat.card U ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨n, hn⟩ : ∃ n, Nat.card U = n := ⟨_, rfl⟩
    rw [hn] at hdvd hle16 hU4 ⊢
    interval_cases n <;> omega
  rcases hcases with h4 | h8 | h16
  rotate_right
  · exact Or.inl (eq_of_le_of_card_ge hUQ (by rw [hQc, h16]))
  all_goals right
  all_goals
    obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := NFF7.exists_ne_one_ne_of_four_le hU4
    obtain ⟨ia, hia, hiaa⟩ := List.getElem_of_mem ((hQ.mem a).1 (hUQ ha))
    obtain ⟨ib, hib, hibb⟩ := List.getElem_of_mem ((hQ.mem b).1 (hUQ hb))
    have hca : code a.1 ≠ cid := fun e => ha1 (Subtype.ext (code_injective (e.trans code_one.symm)))
    have hcb : code b.1 ≠ cid := fun e => hb1 (Subtype.ext (code_injective (e.trans code_one.symm)))
    have hcab : code a.1 ≠ code b.1 := fun e => hab (Subtype.ext (code_injective e))
    rcases hpairs ia hia ib hib with e | e | e | ⟨hk4, hl4, hs4, h8s, hcov⟩
    · exact absurd (hiaa.symm.trans e) hca
    · exact absurd (hibb.symm.trans e) hcb
    · exact absurd (hiaa.symm.trans (e.trans hibb)) hcab
    rw [hiaa, hibb] at hs4 h8s hcov
    obtain ⟨W4, hW4Q, hW4d, hW4c⟩ := hW _ hk4
    have hW4U : W4 ≤ U := by
      intro x hx
      rcases mem_ce4_iff.1 ((hs4 _).2 ((hW4d.mem x).1 hx)) with rfl | rfl | rfl | rfl
      · exact one_mem U
      · exact ha
      · exact hb
      · exact mul_mem ha hb
  · refine ⟨_, hk4, ?_⟩
    have hEq : W4 = U := eq_of_le_of_card_ge hW4U (by rw [hW4c, hl4, h4])
    exact hEq ▸ hW4d
  ·
    have hlt : ¬ U ≤ W4 := fun hle => by
      have := card_le_of_le hle
      rw [hW4c, hl4, h8] at this
      omega
    obtain ⟨c, hcU, hcW⟩ := SetLike.not_le_iff_exists.1 hlt
    have hcq : code c.1 ∈ qL := (hQ.mem c).1 (hUQ hcU)
    rcases hcov _ hcq with h5 | ⟨k, hk, hck⟩
    · exact absurd ((hW4d.mem c).2 ((hs4 _).1 h5)) hcW
    obtain ⟨hk8, hl8, hak, hbk⟩ := h8s k hk
    obtain ⟨W8, hW8Q, hW8d, hW8c⟩ := hW _ hk8
    refine ⟨k, hk8, ?_⟩
    have haW : a ∈ W8 := (hW8d.mem a).2 hak
    have hbW : b ∈ W8 := (hW8d.mem b).2 hbk
    have hcW8 : c ∈ W8 := (hW8d.mem c).2 hck
    have hW4W8 : W4 ≤ W8 := by
      intro x hx
      rcases mem_ce4_iff.1 ((hs4 _).2 ((hW4d.mem x).1 hx)) with rfl | rfl | rfl | rfl
      · exact one_mem W8
      · exact haW
      · exact hbW
      · exact mul_mem haW hbW
    have hle : W4 ≤ U ⊓ W8 := le_inf hW4U hW4W8
    have hne : W4 ≠ U ⊓ W8 := fun e => hcW (e ▸ ⟨hcU, hcW8⟩)
    have hlt' : Nat.card W4 < Nat.card (U ⊓ W8 : Subgroup ↥(GB i)) := by
      refine lt_of_le_of_ne (card_le_of_le hle) fun e => hne ?_
      exact eq_of_le_of_card_ge hle e.ge
    have hd1 : Nat.card W4 ∣ Nat.card (U ⊓ W8 : Subgroup ↥(GB i)) := card_dvd_of_le hle
    have hd2 : Nat.card (U ⊓ W8 : Subgroup ↥(GB i)) ∣ 8 := h8 ▸ card_dvd_of_le inf_le_left
    rw [hW4c, hl4] at hlt' hd1
    have h8' : Nat.card (U ⊓ W8 : Subgroup ↥(GB i)) = 8 := by
      obtain ⟨m, hm⟩ := hd1
      have : m ∣ 2 := by
        have h42 := hd2
        rw [hm] at h42
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) (by simpa using h42 : 4 * m ∣ 4 * 2)
      have hm2 : m = 1 ∨ m = 2 := (Nat.dvd_prime Nat.prime_two).1 this
      rcases hm2 with rfl | rfl <;> omega
    have e1 : U ⊓ W8 = U := eq_of_le_of_card_ge inf_le_left (by rw [h8', h8])
    have e2 : U ⊓ W8 = W8 := eq_of_le_of_card_ge inf_le_right (by rw [h8', hW8c, hl8])
    rw [← e1, e2]
    exact hW8d

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
