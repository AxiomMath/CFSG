module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat
public import Certificates.Data.DepED4Low

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev ggDepELToZ (l : List ℕ) : GGDepAE 3 6 := ggDepANToZ 3 6 l

@[expose] def GGDepELNValid (q : GGDepANPair) : Prop :=
  q.1.length = 6 ∧ q.2.length = 6 ∧ ggDepANDot 3 q.2 q.1 = 2

noncomputable abbrev ggDepELNRflOf (q : GGDepANPair) :
    Module.End (ZMod 3) (GGDepAE 3 6) :=
  ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2)

@[expose] def ggDepELNNews (news : List GGDepANPair) : Set (GGDepAE 3 6 × GGDepAE 3 6) :=
  {t | ∃ q ∈ news, t = (ggDepELToZ q.1, ggDepELToZ q.2)}

private lemma l05nTT_toZ_add {p N : ℕ} [Fact p.Prime] {a b : List ℕ}
    (ha : a.length = N) (hb : b.length = N) :
    ggDepANToZ p N (ggTWNAdd p a b) = ggDepANToZ p N a + ggDepANToZ p N b := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + y) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggDepANToZ, ggTWNAdd, Pi.add_apply]
  rw [List.getD_eq_getElem (l := a.zipWith (fun x y => (x + y) % p) b) (d := 0)
      (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb,
    List.getElem_zipWith, ZMod.natCast_mod, Nat.cast_add]

private lemma l05nTT_toZ_refl {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N) (hq2 : q.2.length = N) (hv : v.length = N) :
    ggDepANToZ p N (ggTWNRefl p q v) =
      ggDepARefl (ggDepANToZ p N q.1) (ggDepANToZ p N q.2) (ggDepANToZ p N v) := by
  unfold ggTWNRefl
  rw [l05nNC_toZ_sub hv (l05nNC_smul_length hq1), l05nNC_toZ_smul hq1,
    ggDepANDot_cast q.2 v hq2 hv]
  rw [l05nNC_refl_apply]

private lemma l05nTT_valid_of_dot {q : GGDepANPair} (hq1 : q.1.length = 6)
    (hq2 : q.2.length = 6) (h : ggDepAdot (ggDepELToZ q.2) (ggDepELToZ q.1) = 2) :
    GGDepELNValid q := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨hq1, hq2, ?_⟩
  have hcast := ggDepANDot_cast (p := 3) (N := 6) q.2 q.1 hq2 hq1
  rw [h] at hcast
  have h2 : ((ggDepANDot 3 q.2 q.1 : ℕ) : ZMod 3) = ((2 % 3 : ℕ) : ZMod 3) := by
    rw [ZMod.natCast_mod]; exact hcast
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  simpa [ggDepANDot, Nat.mod_mod] using h2

private lemma l05nTT_rfl_conj {p N : ℕ} [Fact p.Prime] {q g : GGDepANPair}
    (hq1 : q.1.length = N) (hq2 : q.2.length = N) (hg1 : g.1.length = N)
    (hg2 : g.2.length = N) (hdg : ggDepAdot (ggDepANToZ p N g.2) (ggDepANToZ p N g.1) = 2) :
    ggDepARefl (ggDepANToZ p N (ggDepANConj p q g).1) (ggDepANToZ p N (ggDepANConj p q g).2) =
      ggDepARefl (ggDepANToZ p N g.1) (ggDepANToZ p N g.2) *
        ggDepARefl (ggDepANToZ p N q.1) (ggDepANToZ p N q.2) *
        ggDepARefl (ggDepANToZ p N g.1) (ggDepANToZ p N g.2) := by
  have hc := l05nNC_toZ_conj (p := p) (N := N) (q := q) (g := g) hq1 hq2 hg1 hg2
  rw [hc.1, hc.2]
  exact (l05nNC_refl_conj (ggDepANToZ p N q.1) (ggDepANToZ p N q.2)
    (ggDepANToZ p N g.1) (ggDepANToZ p N g.2) hdg).symm

theorem ggDepELSub_length {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    (ggDepANSub 3 a b).length = 6 := by
  exact l05nNC_sub_length (p := 3) (N := 6) ha hb

theorem ggDepELSmul_length (k : ℕ) {a : List ℕ} (ha : a.length = 6) :
    (ggDepANSmul 3 k a).length = 6 := by
  exact l05nNC_smul_length (p := 3) (N := 6) ha

theorem ggDepELAdd_length {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    (ggTWNAdd 3 a b).length = 6 := by
  simp only [ggTWNAdd, List.length_zipWith, ha, hb, min_self]

theorem ggDepELRefl_length {q : GGDepANPair} {v : List ℕ} (hq : q.1.length = 6)
    (hv : v.length = 6) : (ggTWNRefl 3 q v).length = 6 := by
  unfold ggTWNRefl
  exact l05nNC_sub_length hv (l05nNC_smul_length (p := 3) (N := 6) hq)

theorem ggDepELConj_length {q g : GGDepANPair} (hq1 : q.1.length = 6) (hq2 : q.2.length = 6)
    (hg1 : g.1.length = 6) (hg2 : g.2.length = 6) :
    (ggDepANConj 3 q g).1.length = 6 ∧ (ggDepANConj 3 q g).2.length = 6 := by
  exact l05nNC_conj_length (p := 3) (N := 6) hq1 hq2 hg1 hg2

theorem ggDepELToZ_sub {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    ggDepELToZ (ggDepANSub 3 a b) = ggDepELToZ a - ggDepELToZ b := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact l05nNC_toZ_sub (p := 3) (N := 6) ha hb

theorem ggDepELToZ_smul {a : List ℕ} (ha : a.length = 6) (k : ℕ) :
    ggDepELToZ (ggDepANSmul 3 k a) = (k : ZMod 3) • ggDepELToZ a := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact l05nNC_toZ_smul (p := 3) (N := 6) ha k

theorem ggDepELToZ_add {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    ggDepELToZ (ggTWNAdd 3 a b) = ggDepELToZ a + ggDepELToZ b := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact l05nTT_toZ_add (p := 3) (N := 6) ha hb

theorem ggDepELDot_cast {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    ((ggDepANDot 3 a b : ℕ) : ZMod 3) = ggDepAdot (ggDepELToZ a) (ggDepELToZ b) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact ggDepANDot_cast (p := 3) (N := 6) a b ha hb

theorem ggDepELToZ_refl {q : GGDepANPair} {v : List ℕ} (hq1 : q.1.length = 6)
    (hq2 : q.2.length = 6) (hv : v.length = 6) :
    ggDepELToZ (ggTWNRefl 3 q v) =
      ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2) (ggDepELToZ v) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact l05nTT_toZ_refl (p := 3) (N := 6) hq1 hq2 hv

theorem ggDepELNValid_dot {q : GGDepANPair} (hq : GGDepELNValid q) :
    ggDepAdot (ggDepELToZ q.2) (ggDepELToZ q.1) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcast := ggDepANDot_cast (p := 3) (N := 6) q.2 q.1 hq.2.1 hq.1
  rw [hq.2.2] at hcast
  simpa using hcast.symm

theorem ggDepELNConj_rfl {q g : GGDepANPair} (hq : GGDepELNValid q) (hg : GGDepELNValid g) :
    GGDepELNValid (ggDepANConj 3 q g) ∧
      ggDepELNRflOf (ggDepANConj 3 q g) =
        ggDepELNRflOf g * ggDepELNRflOf q * ggDepELNRflOf g := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hdq : ggDepAdot (ggDepELToZ q.2) (ggDepELToZ q.1) = 2 := ggDepELNValid_dot hq
  have hdg : ggDepAdot (ggDepELToZ g.2) (ggDepELToZ g.1) = 2 := ggDepELNValid_dot hg
  have hlen := l05nNC_conj_length (p := 3) (N := 6) hq.1 hq.2.1 hg.1 hg.2.1
  have hc := l05nNC_toZ_conj (p := 3) (N := 6) (q := q) (g := g) hq.1 hq.2.1 hg.1 hg.2.1
  have hdotconj : ggDepAdot (ggDepELToZ (ggDepANConj 3 q g).2)
      (ggDepELToZ (ggDepANConj 3 q g).1) = 2 := by
    change ggDepAdot (ggDepANToZ 3 6 (ggDepANConj 3 q g).2)
      (ggDepANToZ 3 6 (ggDepANConj 3 q g).1) = 2
    rw [hc.1, hc.2]
    exact l05nNC_conj_dot (ggDepELToZ q.1) (ggDepELToZ q.2) (ggDepELToZ g.1)
      (ggDepELToZ g.2) hdq hdg
  constructor
  · exact l05nTT_valid_of_dot hlen.1 hlen.2 hdotconj
  · show ggDepARefl (ggDepELToZ (ggDepANConj 3 q g).1) (ggDepELToZ (ggDepANConj 3 q g).2) =
      ggDepARefl (ggDepELToZ g.1) (ggDepELToZ g.2) * ggDepARefl (ggDepELToZ q.1)
        (ggDepELToZ q.2) * ggDepARefl (ggDepELToZ g.1) (ggDepELToZ g.2)
    exact l05nTT_rfl_conj hq.1 hq.2.1 hg.1 hg.2.1 hdg

end CFSG.StandardType

end
