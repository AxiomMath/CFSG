module

public import CFSG.LocalAnalysis.StandardType.GGTWLowCheckAux

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWLOutSound (p N allow : ℕ)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) : Prop :=
  (∀ (news : List GGDepANPair) (w : GGTWLE6), (∀ q ∈ news, GGTWNValid p N q) → allow = 6 →
      ggTWLFrameOK p N = true → ggTWLE6Test p N news w = true →
        Out (ggTWGens p N (ggTWNNews p N news))) ∧
    ∀ (news : List GGDepANPair) (w : GGTWLE8), (∀ q ∈ news, GGTWNValid p N q) → allow = 8 →
      ggTWLE8Test p N news w = true → Out (ggTWGens p N (ggTWNNews p N news))

private lemma l05nLC_pat1_wit {N : ℕ} {pos : GGTWPos} {c0 : ℕ} {m n : ℤ}
    (h : GGTWPat1 N pos c0 m n) :
    ∃ mi ni : ℕ, (mi = 1 ∨ mi = 2) ∧ (ni = 1 ∨ ni = 2) ∧
      m = -(mi : ℤ) ∧ n = -(ni : ℤ) := by
  obtain ⟨hm, hn⟩ := ggTWPat1_mn h
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨1, 2, Or.inl rfl, Or.inr rfl, rfl, rfl⟩
  · exact ⟨2, 1, Or.inr rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨2, 2, Or.inr rfl, Or.inr rfl, rfl, rfl⟩

private theorem l05nLC_surv1_false {p N allow : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) (hOutS : GGTWLOutSound p N allow Out)
    (d : GGTWLData) (h : ggTWLCheck p N allow d = true)
    (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true)
    (hFrame : (allow != 6 || ggTWLFrameOK p N) = true)
    (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ) (ha αa : GGTWE p N) (lam mu : ZMod p)
    (hpat : GGTWPat1 N pos c0.val m n) (hpair : GGTWPairs1 p N pos c0 m n ha αa)
    (hdot : ggTWdot αa ha = 2) (hx : ggTWdot αa (ggTWx p N) ≠ 0)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ggTWdot αa (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (hkf : ¬ GGTWKill .frame p N pos {(ha, αa)}
      (lam • ggTWx p N + mu • ggTWz p N pos))
    (hko : ¬ GGTWKill .other p N pos {(ha, αa)}
      (lam • ggTWx p N + mu • ggTWz p N pos))
    (hpz : ∀ c : ZMod p, c ≠ 0 → ¬ GGTWPZBad p N pos (ggTWGens p N {(ha, αa)})
      (ggTWx p N + c • (lam • ggTWx p N + mu • ggTWz p N pos)))
    (hOut : ¬ Out (ggTWGens p N {(ha, αa)})) : False := by
  obtain ⟨mi, ni, hmi, hni, hm, hn⟩ := l05nLC_pat1_wit hpat
  have hpatB : ggTWNPat1B N (ggTWPosNat pos) c0.val mi ni = true :=
    (ggTWNPat1B_iff pos c0.val mi ni hmi hni).mpr (by rw [← hm, ← hn]; exact hpat)
  have hpos : ggTWPosNat pos ∈ [0, 1] := by cases pos <;> simp [ggTWPosNat]
  have hc0 : c0.val ∈ List.range (N - 1) := List.mem_range.mpr c0.isLt
  obtain ⟨wits, _hlook, hwv, hcases⟩ :=
    l05nLC_check_one d h (ggTWPosNat pos) c0.val mi ni hpatB hpos hc0 hmi hni
  have hpair' : GGTWPairs1 p N pos c0 (-(mi : ℤ)) (-(ni : ℤ)) ha αa := by
    rw [← hm, ← hn]; exact hpair
  obtain ⟨lh, la, hlh, hla, hd, hz, hvalid_pair, hnews_eq⟩ :=
    ggTWLEnc1 hp hN pos c0 mi ni hmi hni ha αa hpair' hdot hx
  have hvalid : ∀ q ∈ [(lh, la)], GGTWNValid p N q := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hvalid_pair
  have hla_eq : ggTWNToZ p N la = αa := by
    have hmem : (ggTWNToZ p N lh, ggTWNToZ p N la) ∈ ggTWNNews p N [(lh, la)] :=
      ⟨(lh, la), by simp, rfl⟩
    rw [hnews_eq] at hmem
    rw [Set.mem_singleton_iff] at hmem
    exact congrArg Prod.snd hmem
  have hfix' : ∀ q ∈ [(lh, la)],
      ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [hla_eq]
    exact hfix
  have hx' : ∃ q ∈ [(lh, la)], ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0 :=
    ⟨(lh, la), by simp, by rw [hla_eq]; exact hx⟩
  obtain hwit | hexc := l05nLC_cases1_extract (p := p) (N := N) (allow := allow)
    (ggTWPosNat pos) c0.val mi ni (ggTWNRoots p N) wits
    ((d.excOne.lookup (ggTWPosNat pos, c0.val, mi, ni)).getD []) hcases hlh hla hd hz
  · obtain ⟨w, hwmem, hwtest⟩ := hwit
    have hv : ggTWNKillValid N (N - 1 + [(lh, la)].length) w = true := by
      have hlen : N - 1 + [(lh, la)].length = N := by
        simp only [List.length_cons, List.length_nil]; omega
      rw [hlen]; exact hwv w hwmem
    have hkill := ggTWNKillTest_sound hp hN hvalid hR w hv hwtest pos
      (lam • ggTWx p N + mu • ggTWz p N pos)
    rw [hnews_eq] at hkill
    exact hkf hkill
  · obtain ⟨e, _hemem, _hp1, _hp2, hrt⟩ := hexc
    obtain ⟨e1, r⟩ := e
    cases r with
    | hk w =>
        obtain ⟨hY0len, t, ht, heq⟩ := ggTWLY0_line hp hN pos hvalid lam mu hlm hfix' hx'
        have htest : ggTWLHKTest p N (ggTWPosNat pos) [(lh, la)]
            (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)]) w = true := hrt
        have hkill0 := ggTWLHKTest_sound hp hN pos hvalid
          (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)]) hY0len w htest
        rw [hnews_eq] at hkill0
        have hs := (ggTWKill_other_smul (p := p) (N := N) pos {(ha, αa)}
          (ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)])) t ht).mpr hkill0
        rw [← heq] at hs
        exact hko hs
    | pz w =>
        obtain ⟨hY0len, t, ht, heq⟩ := ggTWLY0_line hp hN pos hvalid lam mu hlm hfix' hx'
        have htest : ggTWLPZTest p N (ggTWPosNat pos) [(lh, la)]
            (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)]) w = true := hrt
        obtain ⟨hc0z, hpz0⟩ := ggTWLPZTest_sound hp hN pos hvalid
          (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)]) hY0len w htest
        rw [hnews_eq] at hpz0
        have hcne : (w.c0 : ZMod p) * t⁻¹ ≠ 0 := mul_ne_zero hc0z (inv_ne_zero ht)
        have harg : ggTWx p N + (w.c0 : ZMod p) •
              ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)]) =
            ggTWx p N + ((w.c0 : ZMod p) * t⁻¹) •
              (lam • ggTWx p N + mu • ggTWz p N pos) := by
          have htoz : ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) [(lh, la)]) =
              t⁻¹ • (lam • ggTWx p N + mu • ggTWz p N pos) := by
            rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul]
          rw [htoz, smul_smul]
        rw [harg] at hpz0
        exact hpz ((w.c0 : ZMod p) * t⁻¹) hcne hpz0
    | out6 w =>
        change (allow == 6 && ggTWLE6Test p N [(lh, la)] w) = true at hrt
        rw [Bool.and_eq_true] at hrt
        obtain ⟨hall6, htest⟩ := hrt
        have hallow6 : allow = 6 := beq_iff_eq.mp hall6
        have hframe : ggTWLFrameOK p N = true := by
          have hh := hFrame
          rw [hallow6] at hh
          simpa using hh
        have hOut6 := hOutS.1 [(lh, la)] w hvalid hallow6 hframe htest
        rw [hnews_eq] at hOut6
        exact hOut hOut6
    | out8 w =>
        change (allow == 8 && ggTWLE8Test p N [(lh, la)] w) = true at hrt
        rw [Bool.and_eq_true] at hrt
        obtain ⟨hall8, htest⟩ := hrt
        have hallow8 : allow = 8 := beq_iff_eq.mp hall8
        have hOut8 := hOutS.2 [(lh, la)] w hvalid hallow8 htest
        rw [hnews_eq] at hOut8
        exact hOut hOut8

private theorem l05nLC_surv2_false {p N allow : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) (hOutS : GGTWLOutSound p N allow Out)
    (d : GGTWLData) (h : ggTWLCheck p N allow d = true)
    (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true)
    (hFrame : (allow != 6 || ggTWLFrameOK p N) = true)
    (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1)))
    (ha1 αa1 ha2 αa2 : GGTWE p N) (lam mu : ZMod p)
    (hpat : GGTWPat2 N pos c.val (c₂.map Fin.val))
    (hpair : GGTWPairs2 p N pos c c₂ ha1 αa1 ha2 αa2)
    (hx : ggTWdot αa1 (ggTWx p N) ≠ 0 ∨ ggTWdot αa2 (ggTWx p N) ≠ 0)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (h1 : ggTWdot αa1 (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (h2 : ggTWdot αa2 (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (hkf : ¬ GGTWKill .frame p N pos {(ha1, αa1), (ha2, αa2)}
      (lam • ggTWx p N + mu • ggTWz p N pos))
    (hko : ¬ GGTWKill .other p N pos {(ha1, αa1), (ha2, αa2)}
      (lam • ggTWx p N + mu • ggTWz p N pos))
    (hpz : ∀ c' : ZMod p, c' ≠ 0 → ¬ GGTWPZBad p N pos
      (ggTWGens p N {(ha1, αa1), (ha2, αa2)})
      (ggTWx p N + c' • (lam • ggTWx p N + mu • ggTWz p N pos)))
    (hOut : ¬ Out (ggTWGens p N {(ha1, αa1), (ha2, αa2)})) : False := by
  have hpatB : ggTWNPat2B N (ggTWPosNat pos) c.val (c₂.map Fin.val) = true :=
    (ggTWNPat2B_iff pos c.val (c₂.map Fin.val)).mpr hpat
  have hpos : ggTWPosNat pos ∈ [0, 1] := by cases pos <;> simp [ggTWPosNat]
  have hcm : c.val ∈ List.range (N - 1) := List.mem_range.mpr c.isLt
  have hc2m : c₂.map Fin.val ∈ none :: (List.range (N - 1)).map some := by
    cases c₂ with
    | none => simp
    | some c' =>
        exact List.mem_cons_of_mem none
          (List.mem_map.mpr ⟨c'.val, List.mem_range.mpr c'.isLt, rfl⟩)
  obtain ⟨wits, _hlook, hwv, hcases⟩ :=
    l05nLC_check_two d h (ggTWPosNat pos) c.val (c₂.map Fin.val) hpatB hpos hcm hc2m
  obtain ⟨lh1, la1, lh2, la2, hlh1, hla1, hlh2, hla2, hd1, hd2, hd3, hd4, hx_list, hdet,
    hvalid_pair1, hvalid_pair2, hnews_eq⟩ :=
    ggTWLEnc2 hp hN pos c c₂ ha1 αa1 ha2 αa2 hpair hx lam mu hlm h1 h2
  have hvalid : ∀ q ∈ [(lh1, la1), (lh2, la2)], GGTWNValid p N q := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact hvalid_pair1
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq; exact hvalid_pair2
      · simp at hq
  have hla1mem : (ggTWNToZ p N lh1, ggTWNToZ p N la1) ∈
      ggTWNNews p N [(lh1, la1), (lh2, la2)] :=
    ⟨(lh1, la1), by simp, rfl⟩
  rw [hnews_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hla1mem
  have hla2mem : (ggTWNToZ p N lh2, ggTWNToZ p N la2) ∈
      ggTWNNews p N [(lh1, la1), (lh2, la2)] :=
    ⟨(lh2, la2), by simp, rfl⟩
  rw [hnews_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hla2mem
  have hfix' : ∀ q ∈ [(lh1, la1), (lh2, la2)],
      ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      change ggTWdot (ggTWNToZ p N la1) (lam • ggTWx p N + mu • ggTWz p N pos) = 0
      rcases hla1mem with he | he
      · have hla : ggTWNToZ p N la1 = αa1 := by
          simpa using congrArg Prod.snd he
        rw [hla]; exact h1
      · have hla : ggTWNToZ p N la1 = αa2 := by
          simpa using congrArg Prod.snd he
        rw [hla]; exact h2
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq
        change ggTWdot (ggTWNToZ p N la2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0
        rcases hla2mem with he | he
        · have hla : ggTWNToZ p N la2 = αa1 := by
            simpa using congrArg Prod.snd he
          rw [hla]; exact h1
        · have hla : ggTWNToZ p N la2 = αa2 := by
            simpa using congrArg Prod.snd he
          rw [hla]; exact h2
      · simp at hq
  have hx' : ∃ q ∈ [(lh1, la1), (lh2, la2)],
      ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0 := by
    rcases hx with hx1 | hx2
    · have hmem : (ha1, αa1) ∈ ggTWNNews p N [(lh1, la1), (lh2, la2)] := by
        rw [hnews_eq]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      rcases hmem with ⟨q, hq, hqeq⟩
      have hla : ggTWNToZ p N q.2 = αa1 := by
        simpa using (congrArg Prod.snd hqeq).symm
      exact ⟨q, hq, by rw [hla]; exact hx1⟩
    · have hmem : (ha2, αa2) ∈ ggTWNNews p N [(lh1, la1), (lh2, la2)] := by
        rw [hnews_eq]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      rcases hmem with ⟨q, hq, hqeq⟩
      have hla : ggTWNToZ p N q.2 = αa2 := by
        simpa using (congrArg Prod.snd hqeq).symm
      exact ⟨q, hq, by rw [hla]; exact hx2⟩
  obtain hwit | hexc := l05nLC_cases2_extract (p := p) (N := N) (allow := allow)
    (ggTWPosNat pos) c.val (c₂.map Fin.val) (ggTWNRoots p N) wits
    ((d.excTwo.lookup (ggTWPosNat pos, c.val, ggTWNCode (c₂.map Fin.val))).getD [])
    hcases hlh1 hla1 hlh2 hla2 hd1 hd2 hd3 hd4 hx_list hdet
  · obtain ⟨w, hwmem, hwtest⟩ := hwit
    have hv : ggTWNKillValid N (N - 1 + [(lh1, la1), (lh2, la2)].length) w = true := by
      have hlen : N - 1 + [(lh1, la1), (lh2, la2)].length = N + 1 := by
        simp only [List.length_cons, List.length_nil]; omega
      rw [hlen]; exact hwv w hwmem
    have hkill := ggTWNKillTest_sound hp hN hvalid hR w hv hwtest pos
      (lam • ggTWx p N + mu • ggTWz p N pos)
    rw [hnews_eq] at hkill
    exact hkf hkill
  · obtain ⟨e, _hemem, _hp1, _hp2, _hp3, _hp4, hrt⟩ := hexc
    obtain ⟨e1, r⟩ := e
    cases r with
    | hk w =>
        obtain ⟨hY0len, t, ht, heq⟩ := ggTWLY0_line hp hN pos hvalid lam mu hlm hfix' hx'
        have htest : ggTWLHKTest p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]
            (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]) w = true := hrt
        have hkill0 := ggTWLHKTest_sound hp hN pos hvalid
          (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]) hY0len w htest
        rw [hnews_eq] at hkill0
        have hs := (ggTWKill_other_smul (p := p) (N := N) pos {(ha1, αa1), (ha2, αa2)}
          (ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)])) t ht).mpr hkill0
        rw [← heq] at hs
        exact hko hs
    | pz w =>
        obtain ⟨hY0len, t, ht, heq⟩ := ggTWLY0_line hp hN pos hvalid lam mu hlm hfix' hx'
        have htest : ggTWLPZTest p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]
            (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]) w = true := hrt
        obtain ⟨hc0z, hpz0⟩ := ggTWLPZTest_sound hp hN pos hvalid
          (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]) hY0len w htest
        rw [hnews_eq] at hpz0
        have hcne : (w.c0 : ZMod p) * t⁻¹ ≠ 0 := mul_ne_zero hc0z (inv_ne_zero ht)
        have harg : ggTWx p N + (w.c0 : ZMod p) •
              ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]) =
            ggTWx p N + ((w.c0 : ZMod p) * t⁻¹) •
              (lam • ggTWx p N + mu • ggTWz p N pos) := by
          have htoz : ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) [(lh1, la1), (lh2, la2)]) =
              t⁻¹ • (lam • ggTWx p N + mu • ggTWz p N pos) := by
            rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul]
          rw [htoz, smul_smul]
        rw [harg] at hpz0
        exact hpz ((w.c0 : ZMod p) * t⁻¹) hcne hpz0
    | out6 w =>
        change (allow == 6 && ggTWLE6Test p N [(lh1, la1), (lh2, la2)] w) = true at hrt
        rw [Bool.and_eq_true] at hrt
        obtain ⟨hall6, htest⟩ := hrt
        have hallow6 : allow = 6 := beq_iff_eq.mp hall6
        have hframe : ggTWLFrameOK p N = true := by
          have hh := hFrame
          rw [hallow6] at hh
          simpa using hh
        have hOut6 := hOutS.1 [(lh1, la1), (lh2, la2)] w hvalid hallow6 hframe htest
        rw [hnews_eq] at hOut6
        exact hOut hOut6
    | out8 w =>
        change (allow == 8 && ggTWLE8Test p N [(lh1, la1), (lh2, la2)] w) = true at hrt
        rw [Bool.and_eq_true] at hrt
        obtain ⟨hall8, htest⟩ := hrt
        have hallow8 : allow = 8 := beq_iff_eq.mp hall8
        have hOut8 := hOutS.2 [(lh1, la1), (lh2, la2)] w hvalid hallow8 htest
        rw [hnews_eq] at hOut8
        exact hOut hOut8

theorem ggTWLCheck_sound {p N allow : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    (hallow : allow = 0 ∨ allow = 6 ∨ allow = 8)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) (hOut : GGTWLOutSound p N allow Out)
    (d : GGTWLData) (h : ggTWLCheck p N allow d = true) : GGTWLowCells p N Out := by
  have hh := h
  rw [ggTWLCheck] at hh
  have h1 := Bool.and_eq_true_iff.mp hh
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have h4 := Bool.and_eq_true_iff.mp h3.1
  have hR : ggTWNRootsOK p N (ggTWNRoots p N) = true := h4.1
  have hFrame : (allow != 6 || ggTWLFrameOK p N) = true := h4.2
  constructor
  · rintro ⟨pos, c0, m, n, ha, αa, lam, mu, hpat, hpair, hdot, hx, hlm, hfix, hkf, hko,
      hpz, hOut'⟩
    exact l05nLC_surv1_false hp hN Out hOut d h hR hFrame pos c0 m n ha αa lam mu
      hpat hpair hdot hx hlm hfix hkf hko hpz hOut'
  · rintro ⟨pos, c, c₂, ha1, αa1, ha2, αa2, lam, mu, hpat, hpair, hx, hlm, h1, h2, hkf, hko,
      hpz, hOut'⟩
    exact l05nLC_surv2_false hp hN Out hOut d h hR hFrame pos c c₂ ha1 αa1 ha2 αa2 lam mu
      hpat hpair hx hlm h1 h2 hkf hko hpz hOut'

theorem ggTWLCells55 (d : GGTWLData) (h : ggTWLCheck 5 5 0 d = true) :
    GGTWLowCells 5 5 (fun _ => False) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ggTWLCheck_sound (p := 5) (N := 5) (allow := 0) (by norm_num) (by norm_num)
    (Or.inl rfl) (fun _ => False) ?_ d h
  refine ⟨?_, ?_⟩
  · intro news w hnews h6 hf ht
    exact absurd h6 (by norm_num)
  · intro news w hnews h8 ht
    exact absurd h8 (by norm_num)

theorem ggTWLCells36 (d : GGTWLData) (h : ggTWLCheck 3 6 6 d = true) :
    GGTWLowCells 3 6 GGTWLowE6Outcome := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ggTWLCheck_sound (p := 3) (N := 6) (allow := 6) (by norm_num) (by norm_num)
    (Or.inr (Or.inl rfl)) GGTWLowE6Outcome ?_ d h
  refine ⟨?_, ?_⟩
  · intro news w hnews h6 hf ht
    exact ggTWLE6_sound hnews w hf ht
  · intro news w hnews h8 ht
    exact absurd h8 (by norm_num)

theorem ggTWLCells39 (d : GGTWLData) (h : ggTWLCheck 3 9 8 d = true) :
    GGTWLowCells 3 9 GGTWLowE8Outcome := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ggTWLCheck_sound (p := 3) (N := 9) (allow := 8) (by norm_num) (by norm_num)
    (Or.inr (Or.inr rfl)) GGTWLowE8Outcome ?_ d h
  refine ⟨?_, ?_⟩
  · intro news w hnews h6 hf ht
    exact absurd h6 (by norm_num)
  · intro news w hnews h8 ht
    exact ggTWLE8_sound hnews w ht

end CFSG.StandardType

end
