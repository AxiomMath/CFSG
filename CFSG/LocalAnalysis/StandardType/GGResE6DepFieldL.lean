module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGResE6DepZsig
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrders

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4m_eq_of_ggLabel_eq {a b : LargeEvenLabel} (h : GGLabelIso a b)
    (hb : GGE6DepLabel b) : a = b := by
  obtain ⟨ta, la, na⟩ := a
  obtain ⟨tb, lb, nb⟩ := b
  simp only [GGE6DepLabel, LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or] at hb h
  rcases hb with hb | hb <;> rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem l05nL4m_eq_of_ggLabel_A5 {a b : LargeEvenLabel} (h : GGLabelIso a b)
    (hb : GGA5Label b) : a = b := by
  obtain ⟨ta, la, na⟩ := a
  obtain ⟨tb, lb, nb⟩ := b
  simp only [GGA5Label, LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or] at hb h
  obtain ⟨hlb, hb | hb⟩ := hb
  all_goals rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem l05nL4m_not_three_dvd (n : ℕ) : ¬ 3 ∣ 2 ^ (2 * n) + 1 := by
  have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have h1 : 4 ^ n ≡ 1 [MOD 3] := by simpa using h4.pow n
  have hp : 2 ^ (2 * n) % 3 = 1 := by
    have h : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [h]
    exact h1
  intro h
  have hmod : (2 ^ (2 * n) + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod, hp] at hmod
  norm_num at hmod

private theorem l05nL4m_facts {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    commutator ↥L = ⊤ ∧ commutator ↥J = ⊤ ∧
      Nontrivial (↥L ⧸ Subgroup.center ↥L) ∧ Nontrivial (↥J ⧸ Subgroup.center ↥J) ∧
      J ≤ L := by
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hcomp.2.2
  have hJperf : commutator ↥J = ⊤ := hJq.1
  have hJnt : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJq.2.toNontrivial
  have hMark : GGInnerDiagOnLab (fun _ _ => True) p B L :=
    ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hH.1.1
  have hLq : CFSG.Assembly.IsQuasisimple ↥L := isQuasisimple_of_largeEvenMarking hMark
  have hLperf : commutator ↥L = ⊤ := hLq.1
  have hLnt : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hLq.2.toNontrivial
  exact ⟨hLperf, hJperf, hLnt, hJnt, hJL⟩

private theorem l05nL4m_dvd {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    {labL labJ : LargeEvenLabel}
    (hL2 : LargeEvenInLambda2 labL) (hJ2 : LargeEvenInLambda2 labJ)
    (hL : GGE6DepLabel labL) (hJ : GGA5Label labJ)
    (hlL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (hlJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : labL.n ∣ labJ.n := by
  obtain ⟨lab, labJ', hlab, hsplit, hhasL, hlabJ', hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj hTCJ hH.1 hH.2.2.2.2.1
  have hiso1 : GGLabelIso lab labL :=
    hRig lab labL (↥L ⧸ Subgroup.center ↥L) hlab hL2 hhasL hlL
  have heq1 : lab = labL := l05nL4m_eq_of_ggLabel_eq hiso1 hL
  have hiso2 : GGLabelIso labJ' labJ :=
    hRig labJ' labJ (↥J ⧸ Subgroup.center ↥J) hlabJ' hJ2 hhasJ hlJ
  have heq2 : labJ' = labJ := l05nL4m_eq_of_ggLabel_A5 hiso2 hJ
  rw [heq1, heq2] at hdvd
  exact hdvd

private theorem l05nL4m_bound
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hT3 : GGSchurDvdInput) (hH : GGResHyp p B Bs x L D J y K)
    {labL labJ : LargeEvenLabel} (hL2 : LargeEvenInLambda2 labL) (hJ2 : LargeEvenInLambda2 labJ)
    (hL : GGE6DepLabel labL) (hJ : GGA5Label labJ)
    (hlL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (hlJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    {m : ℕ} (hm : labJ.n = labL.n * m) : m ≤ 2 := by
  obtain ⟨hLperf, hJperf, hLnt, hJnt, hJL⟩ := l05nL4m_facts hH
  have h2J : 15 * labJ.n ≤ (Nat.card ↥J).factorization 2 :=
    ggResE6Dep_two_part_ge_A5 hJperf hJnt hJ2 hJ hlJ
  have h2L : (Nat.card ↥L).factorization 2 ≤ 36 * labL.n + 2 :=
    ggResE6Dep_two_part_le_E6 hT3 hLperf hLnt hL2 hL hlL
  have hcard : Nat.card ↥J ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hJL
  have hfac : (Nat.card ↥J).factorization 2 ≤ (Nat.card ↥L).factorization 2 :=
    (Nat.factorization_le_iff_dvd (Nat.card_ne_zero.mpr ⟨⟨(1 : ↥J)⟩, inferInstance⟩)
      (Nat.card_ne_zero.mpr ⟨⟨(1 : ↥L)⟩, inferInstance⟩)).mpr hcard 2
  have hle : 15 * (labL.n * m) ≤ 36 * labL.n + 2 := by
    have h := h2J.trans (hfac.trans h2L)
    rwa [hm] at h
  have hn1 : 1 ≤ labL.n := hL2.1
  by_contra hlt
  push Not at hlt
  have hm3 : 3 ≤ m := by omega
  nlinarith [Nat.mul_le_mul_left (15 * labL.n) hm3, hn1, hle]

private theorem l05nL4m_ne_two
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hT3 : GGSchurDvdInput) (hH : GGResHyp p B Bs x L D J y K)
    {labL labJ : LargeEvenLabel} (hL2 : LargeEvenInLambda2 labL)
    (hJ2 : LargeEvenInLambda2 labJ)
    (hL : GGE6DepLabel labL) (hJ : GGA5Label labJ)
    (hlL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (hlJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hm : labJ.n = 2 * labL.n) : False := by
  obtain ⟨hLperf, hJperf, hLnt, hJnt, hJL⟩ := l05nL4m_facts hH
  have hn1 : 1 ≤ labL.n := hL2.1
  have hcard : Nat.card ↥J ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hJL
  rcases hJ.2 with ⟨htagA, h3dvdA⟩ | ⟨htagTwA, h3dvdTwA⟩
  · have hL0 : GGE6DepLabel labL := hL
    rcases hL with ⟨htagE6, -⟩ | ⟨htagTwE6, -⟩
    · obtain ⟨r, hr, h11, hr10, hnrE6⟩ := (ggResE6Dep_zsigmondy labL.n hn1).1
      have hrdvdL : r ∣ Nat.card ↥L :=
        dvd_trans (ggResE6Dep_prime_dvd_A5 hJperf hJnt hJ2 hJ hlJ hm hr h11 hr10) hcard
      have hZ : (labL.tag = .E6 → ¬ r ∣ CFSG.Open.ordE6 (2 ^ labL.n)) ∧
          (labL.tag = .twE6 → ¬ r ∣ CFSG.Open.ordTwistedE6 (2 ^ labL.n)) := by
        refine ⟨fun _ => hnrE6, ?_⟩
        intro htw
        rw [htagE6] at htw
        exact nomatch htw
      exact (ggResE6Dep_not_prime_dvd_E6 hT3 hLperf hLnt hL2 hL0 hlL hr h11 hZ) hrdvdL
    · obtain ⟨r, hr, h11, hr5, hnrtwE6⟩ := (ggResE6Dep_zsigmondy labL.n hn1).2
      have hpoweq : (2 ^ (5 * labL.n)) ^ 2 = 2 ^ (10 * labL.n) := by
        rw [← pow_mul]; congr 1; ring
      have hdvd10 : r ∣ 2 ^ (10 * labL.n) - 1 := by
        have h' : 2 ^ (5 * labL.n) - 1 ∣ (2 ^ (5 * labL.n)) ^ 2 - 1 :=
          Nat.sub_one_dvd_pow_sub_one _ 2
        rw [hpoweq] at h'
        exact hr5.trans h'
      have hrdvdL : r ∣ Nat.card ↥L :=
        dvd_trans (ggResE6Dep_prime_dvd_A5 hJperf hJnt hJ2 hJ hlJ hm hr h11 hdvd10) hcard
      have hZ : (labL.tag = .E6 → ¬ r ∣ CFSG.Open.ordE6 (2 ^ labL.n)) ∧
          (labL.tag = .twE6 → ¬ r ∣ CFSG.Open.ordTwistedE6 (2 ^ labL.n)) := by
        refine ⟨?_, fun _ => hnrtwE6⟩
        intro hE6
        rw [htagTwE6] at hE6
        exact nomatch hE6
      exact (ggResE6Dep_not_prime_dvd_E6 hT3 hLperf hLnt hL2 hL0 hlL hr h11 hZ) hrdvdL
  · have h3 : 3 ∣ 2 ^ (2 * labL.n) + 1 := by rw [hm] at h3dvdTwA; exact h3dvdTwA
    exact absurd h3 (l05nL4m_not_three_dvd labL.n)

theorem ggResE6Dep_L_field
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hT3 : GGSchurDvdInput)
    (hH : GGResHyp p B Bs x L D J y K) {labL labJ : LargeEvenLabel}
    (hL2 : LargeEvenInLambda2 labL) (hJ2 : LargeEvenInLambda2 labJ)
    (hL : GGE6DepLabel labL) (hJ : GGA5Label labJ)
    (hlL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (hlJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : labL.n = labJ.n := by
  obtain ⟨m, hm⟩ := l05nL4m_dvd hTCJ hRig hH hL2 hJ2 hL hJ hlL hlJ
  have hmle : m ≤ 2 := l05nL4m_bound hT3 hH hL2 hJ2 hL hJ hlL hlJ hm
  have hmne0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hm
    have := hJ2.1
    omega
  have hmne2 : m ≠ 2 := by
    intro h2
    exact l05nL4m_ne_two hT3 hH hL2 hJ2 hL hJ hlL hlJ (by rw [hm, h2, Nat.mul_comm])
  have hm1 : m = 1 := by omega
  subst hm1
  simpa using hm.symm

end CFSG.StandardType
