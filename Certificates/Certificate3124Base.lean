
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputs
public import Certificates.Kernel.MonsterB.Orb14Glue

@[expose] public section

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.Bfs CertificateChecks.Orb14

namespace CertificateChecks.Batch3124

theorem singGenArr_eq_0 : ∀ (k : Fin 17) (i : Fin 693),
    (singGenArr[(k : ℕ)]!)[(i : ℕ)]! = (singGen k i : ℕ) := fun k i => singGenArr_get k.2 i.2

theorem singT_eq : singT = transArr singGenArr 693 := rfl

theorem singI_eq : singI = (transArr singGenArr 693).map invPermArr := rfl

theorem natT_eq : natT = transArr n6PermsArr 891 := rfl

theorem natI_eq : natI = (transArr n6PermsArr 891).map invPermArr := rfl

theorem natTree_ok_2 : treeOK n6PermsArr natT natI 891 = true := by
  rw [natI_eq, natT_eq]
  exact treeOK_of_perm pgN treeShape

theorem singSchreier_ok_3 : schreierOK singGenArr singT singI singPart 693 = true := schS

theorem natSchreier_ok_4 : schreierOK n6PermsArr natT natI natPart 891 = true := schN

theorem singBfs (c : ℕ) (hc : (o14PtOrb[c]!)[0]! < 693) :
    natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size (fun x => decide (x < 693))
      (o14PtOrb[c]!)[0]! (singCert c) = true ∧ ∀ y, (singCert c).pts.contains y = true ↔
      Reach (selAct singGenArr singT singI o14PtSel) o14PtSel.size (o14PtOrb[c]!)[0]! y := by
  have e : singCert c =
      natBfs (selAct singGenArr singT singI o14PtSel) o14PtSel.size (o14PtOrb[c]!)[0]! 800 := rfl
  rw [e, singI_eq, singT_eq]
  exact natBfs_range hc (selAct_lt pgS sel_ok) (by decide)

theorem natBfs' (c : ℕ) (hc : natOf (o14PlOrb[c]!)[0]! < 891) :
    natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size (fun x => decide (x < 891))
      (natOf (o14PlOrb[c]!)[0]!) (natCert c) = true ∧ ∀ y, (natCert c).pts.contains y = true ↔
      Reach (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size (natOf (o14PlOrb[c]!)[0]!) y := by
  have e : natCert c =
      natBfs (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size (natOf (o14PlOrb[c]!)[0]!) 1000 :=
    rfl
  rw [e, natI_eq, natT_eq]
  exact natBfs_range hc (selAct_lt pgN selN_ok) (by decide)

theorem singCert_ok0_5 :
    natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size
    (fun x => decide (x < 693)) (o14PtOrb[0]!)[0]! (singCert 0) = true :=
  (singBfs 0 (by rw [kRoots.1]; decide)).1

theorem singCert_ok1_6 :
    natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size
    (fun x => decide (x < 693)) (o14PtOrb[1]!)[0]! (singCert 1) = true :=
  (singBfs 1 (by rw [kRoots.2.1]; decide)).1

theorem natCert_ok0_7 :
    natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size
    (fun x => decide (x < 891)) (natOf (o14PlOrb[0]!)[0]!) (natCert 0) = true :=
  (natBfs' 0 (by rw [kRoots.2.2.1]; decide)).1

theorem natCert_ok1_8 :
    natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size
    (fun x => decide (x < 891)) (natOf (o14PlOrb[1]!)[0]!) (natCert 1) = true :=
  (natBfs' 1 (by rw [kRoots.2.2.2]; decide)).1

theorem sel_size : o14PtSel.size = 7 ∧ o14PlSel.size = 7 := by
  rw [kSel.1, kSel.2]
  exact ⟨rfl, rfl⟩

theorem singCov_9 :
    ∀ y < 693, (singPart[y]! = 0 ∧ (singCert 0).pts.contains y = true) ∨
    (singPart[y]! = 1 ∧ (singCert 1).pts.contains y = true) := by
  intro y hy
  cases h : MO0.testBit y with
  | true =>
    refine Or.inl ⟨(singPart_zero hy).2 h, ?_⟩
    rw [(singBfs 0 (by rw [kRoots.1]; decide)).2, sel_size.1, kRoots.1]
    exact reachS 0 10 (pw2 0) rfl (by decide) y (by rw [beq_true_iff.1 kCovS0]; exact h)
  | false =>
    refine Or.inr ⟨(singPart_one hy).2 h, ?_⟩
    rw [(singBfs 1 (by rw [kRoots.2.1]; decide)).2, sel_size.1, kRoots.2.1]
    refine reachS 2 12 (pw2 2) rfl (by decide) y ?_
    rw [beq_true_iff.1 kCovS1, mo_split hy, h]
    rfl

theorem natCov_10 :
    ∀ y < 891, (natPart[y]! = 0 ∧ (natCert 0).pts.contains y = true) ∨
    (natPart[y]! = 1 ∧ (natCert 1).pts.contains y = true) := by
  intro y hy
  cases h : MN0.testBit y with
  | true =>
    refine Or.inl ⟨(natPart_zero hy).2 h, ?_⟩
    rw [(natBfs' 0 (by rw [kRoots.2.2.1]; decide)).2, sel_size.2, kRoots.2.2.1]
    exact reachN 167 6 (pw2 167) rfl (by decide) y (by rw [beq_true_iff.1 kCovN0]; exact h)
  | false =>
    refine Or.inr ⟨(natPart_one hy).2 h, ?_⟩
    rw [(natBfs' 1 (by rw [kRoots.2.2.2]; decide)).2, sel_size.2, kRoots.2.2.2]
    refine reachN 0 13 (pw2 0) rfl (by decide) y ?_
    rw [beq_true_iff.1 kCovN1, testBit_nxor, testBit_maskN, decide_eq_true hy, h]
    rfl

theorem singPart_spec_11 :
    ∀ i < 693, (i ∈ o14PtOrb[0]! ↔ singPart[i]! = 0) ∧
    (i ∈ o14PtOrb[1]! ↔ singPart[i]! = 1) := by
  intro i hi
  rw [mem_orb kO0, mem_orb kO1, singPart_zero hi, singPart_one hi, mo_split hi]
  cases MO0.testBit i <;> simp

theorem iso_lt (j : Fin 891) : (b6Iso j : ℕ) = fget ISO j 10 := by
  change b6IsoArr[(j : ℕ)]! % 891 = _
  rw [Nat.mod_eq_of_lt (iso_spec.2 j j.2).1, (iso_spec.2 j j.2).2]

theorem natPart_spec_12 :
    ∀ j : Fin 891, ((b6Iso j : ℕ) ∈ o14PlOrb[0]! ↔ natPart[(j : ℕ)]! = 0) ∧
    ((b6Iso j : ℕ) ∈ o14PlOrb[1]! ↔ natPart[(j : ℕ)]! = 1) := by
  intro j
  have hl : fget ISO j 10 < 891 := by rw [← iso_lt]; exact (b6Iso j).2
  rw [mem_orb kP0, mem_orb kP1, natPart_zero j.2, natPart_one j.2, mn0_spec, iso_lt,
    decide_eq_true j.2, Bool.true_and, mp_split hl]
  cases MP0.testBit (fget ISO j 10) <;> simp

theorem card_split (N X : ℕ) :
    (Finset.univ.filter fun y : Fin N => ¬ X.testBit y = true).card = N - popc N X := by
  have e := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun y : Fin N => X.testBit y = true)
  rw [Finset.card_univ, Fintype.card_fin, card_eq_popc] at e
  omega

theorem card_singPart_13 :
    (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 0).card = 126 ∧
    (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 1).card = 567 := by
  have e0 : (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 0) =
      Finset.univ.filter fun y : Fin 693 => MO0.testBit y = true :=
    Finset.filter_congr fun y _ => singPart_zero y.2
  have e1 : (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 1) =
      Finset.univ.filter fun y : Fin 693 => ¬ MO0.testBit y = true :=
    Finset.filter_congr fun y _ => (singPart_one y.2).trans (Iff.of_eq (Bool.not_eq_true _).symm)
  have hp := beq_true_iff.1 (andB_eq_true.1 kCard).1
  rw [e0, e1, card_eq_popc, card_split, hp]
  exact ⟨rfl, rfl⟩

theorem card_natPart_14 :
    (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 0).card = 324 ∧
    (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 1).card = 567 := by
  have e0 : (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 0) =
      Finset.univ.filter fun y : Fin 891 => MN0.testBit y = true :=
    Finset.filter_congr fun y _ => natPart_zero y.2
  have e1 : (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 1) =
      Finset.univ.filter fun y : Fin 891 => ¬ MN0.testBit y = true :=
    Finset.filter_congr fun y _ => (natPart_one y.2).trans (Iff.of_eq (Bool.not_eq_true _).symm)
  have hp := beq_true_iff.1 (andB_eq_true.1 kCard).2
  rw [e0, e1, card_eq_popc, card_split, hp]
  exact ⟨rfl, rfl⟩

theorem expand_eq {p : ℕ} (hp : p < 891) (v : V6) :
    expand ⟨p, hp⟩ v = fun t : Fin 6 =>
      ∑ b ∈ Finset.range 3, v (piv (vec6 (rowP PLP p b))) * vec6 (rowP PLP p b) t := by
  funext t
  unfold expand
  rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range
    (fun b => v (piv (vec6 (rowP PLP p b))) * vec6 (rowP PLP p b) t) 3]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : planeRow ⟨p, hp⟩ b = vec6 (rowP PLP p b) := by
    unfold planeRow rowP
    rw [(pl_spec.2 p hp b b.2).2]
  rw [Pi.smul_apply, smul_eq_mul, e]

theorem incid_mem {p : ℕ} (hp : p < 891) {A : ℕ}
    (hD : Nat.xor (maskN 693) (planeD XP (rowP PLP p)) = maskF A 21 10) (i : Fin 693) :
    expand ⟨p, hp⟩ (singVec i) = singVec i ↔
      (i : ℕ) ∈ (Finset.range 21).image fun t => fget A t 10 := by
  have e : ((i : ℕ) ∈ (Finset.range 21).image fun t => fget A t 10) ↔ ∃ t < 21, fget A t 10 = i := by
    simp only [Finset.mem_image, Finset.mem_range]
  rw [e, ← testBit_maskF, ← hD, testBit_nxor, testBit_maskN, decide_eq_true i.2, Bool.true_xor,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, planeD_bit (planes_sing i i.2), expand_eq hp]
  simp

theorem card_list {N m w A : ℕ} (hinc : incOK A m w N = true) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i : Fin N =>
        P i ∧ (i : ℕ) ∈ (Finset.range m).image fun t => fget A t w).card =
      ((Finset.range m).filter fun t => P (fget A t w)).card := by
  obtain ⟨hlt, hmono⟩ := incOK_spec hinc
  symm
  refine Finset.card_bij (fun t ht => (⟨fget A t w, hlt t (by
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      exact ht.1)⟩ : Fin N)) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    exact ⟨ht.2, t, ht.1, rfl⟩
  · intro a ha b hb e
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have e' : fget A a w = fget A b w := congrArg Fin.val e
    rcases lt_trichotomy a b with h | h | h
    · exact absurd e' (ne_of_lt (hmono a ha.1 b hb.1 h))
    · exact h
    · exact absurd e' (ne_of_gt (hmono b hb.1 a ha.1 h))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range] at hi
    obtain ⟨hP, t, ht, e⟩ := hi
    refine ⟨t, ?_, Fin.ext e⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ht, e ▸ hP⟩

theorem incid_spec {X PL PU MO MP o n : ℕ} (h : incidOK X PL PU MO MP o n = true) :
    ∀ l < n, incOK (fget PU (o + l) 210) 21 10 693 = true ∧
      Nat.xor (maskN 693) (planeD X (rowP PL (o + l))) = maskF (fget PU (o + l) 210) 21 10 ∧
      sumN 21 (fun t => nIf(bit MO (fget (fget PU (o + l) 210) t 10), 1, 0)) =
        nIf(bit MP (o + l), 0, 6) := by
  intro l hl
  rw [incidOK, allN_iff] at h
  obtain ⟨h1, h2⟩ := andB_eq_true.1 (h l hl)
  obtain ⟨h2, h3⟩ := andB_eq_true.1 h2
  exact ⟨h1, beq_true_iff.1 h2, beq_true_iff.1 h3⟩

theorem sumN_count (m : ℕ) (c : ℕ → Bool) :
    sumN m (fun t => nIf(c t, 1, 0)) = ((Finset.range m).filter fun t => c t = true).card := by
  rw [sumN_eq', Finset.card_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases c t <;> rfl

theorem incid_one {p : ℕ} (hp : p < 891) {A : ℕ} (hinc : incOK A 21 10 693 = true)
    (hD : Nat.xor (maskN 693) (planeD XP (rowP PLP p)) = maskF A 21 10)
    (hc : sumN 21 (fun t => nIf(bit MO0 (fget A t 10), 1, 0)) = nIf(bit MP0 p, 0, 6)) :
    ((Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 0 ∧ expand ⟨p, hp⟩ (singVec i) = singVec i).card,
      (Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 1 ∧ expand ⟨p, hp⟩ (singVec i) = singVec i).card) =
      if p ∈ o14PlOrb[0]! then (0, 21) else (6, 15) := by
  have hA := (incOK_spec hinc).1
  have e0 : (Finset.univ.filter fun i : Fin 693 =>
      singPart[(i : ℕ)]! = 0 ∧ expand ⟨p, hp⟩ (singVec i) = singVec i) =
      Finset.univ.filter fun i : Fin 693 =>
        MO0.testBit i = true ∧ (i : ℕ) ∈ (Finset.range 21).image fun t => fget A t 10 :=
    Finset.filter_congr fun i _ => by rw [singPart_zero i.2, incid_mem hp hD i]
  have e1 : (Finset.univ.filter fun i : Fin 693 =>
      singPart[(i : ℕ)]! = 1 ∧ expand ⟨p, hp⟩ (singVec i) = singVec i) =
      Finset.univ.filter fun i : Fin 693 =>
        MO0.testBit i = false ∧ (i : ℕ) ∈ (Finset.range 21).image fun t => fget A t 10 :=
    Finset.filter_congr fun i _ => by rw [singPart_one i.2, incid_mem hp hD i]
  rw [e0, e1, card_list (N := 693) hinc (fun i => MO0.testBit i = true),
    card_list (N := 693) hinc (fun i => MO0.testBit i = false)]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range 21)
    (fun t => MO0.testBit (fget A t 10) = true)
  rw [Finset.card_range] at hsplit
  have hneg : ((Finset.range 21).filter fun t => ¬ MO0.testBit (fget A t 10) = true) =
      (Finset.range 21).filter fun t => MO0.testBit (fget A t 10) = false :=
    Finset.filter_congr fun t _ => Iff.of_eq (Bool.not_eq_true _)
  rw [hneg] at hsplit
  have hc' := hc
  rw [sumN_count 21 (fun t => bit MO0 (fget A t 10))] at hc'
  simp only [bit_eq] at hc'
  by_cases hm : p ∈ o14PlOrb[0]!
  · rw [ite_eq_left hm]
    have hb : MP0.testBit p = true := (mem_orb kP0 p).1 hm
    rw [hb] at hc'
    change _ = 0 at hc'
    rw [hc'] at hsplit ⊢
    simp only [Prod.mk.injEq, true_and]
    omega
  · rw [ite_eq_right hm]
    have hb : MP0.testBit p = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hm ((mem_orb kP0 p).2 h)
    rw [hb] at hc'
    change _ = 6 at hc'
    rw [hc'] at hsplit ⊢
    simp only [Prod.mk.injEq, true_and]
    omega

theorem incid_check_15 :
    ∀ p : Fin 891,
    ((Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 0 ∧ expand p (singVec i) = singVec i).card,
      (Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 1 ∧ expand p (singVec i) = singVec i).card) =
      if (p : ℕ) ∈ o14PlOrb[0]! then (0, 21) else (6, 15) := by
  intro ⟨p, hp⟩
  have key : ∀ o, incidOK XP PLP PU MO0 MP0 o 297 = true → o ≤ p → p < o + 297 →
      ((Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 0 ∧ expand ⟨p, hp⟩ (singVec i) = singVec i).card,
      (Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 1 ∧ expand ⟨p, hp⟩ (singVec i) = singVec i).card) =
      if p ∈ o14PlOrb[0]! then (0, 21) else (6, 15) := by
    intro o ho h1 h2
    obtain ⟨a, b, c⟩ := incid_spec ho (p - o) (by omega)
    rw [Nat.add_sub_cancel' h1] at a b c
    exact incid_one hp a b c
  rcases (by omega : p < 297 ∨ (297 ≤ p ∧ p < 594) ∨ 594 ≤ p) with h | h | h
  · exact key 0 kInc0 (by omega) (by omega)
  · exact key 297 kInc1 h.1 (by omega)
  · exact key 594 kInc2 h (by omega)

theorem plList_spec_16 : ∀ p < 891, ¬ (p ∈ o14PlOrb[0]! ∧ p ∈ o14PlOrb[1]!) := by
  intro p hp
  rw [mem_orb kP0, mem_orb kP1, mp_split hp]
  cases MP0.testBit p <;> simp

end CertificateChecks.Batch3124

namespace Certificates

end Certificates
