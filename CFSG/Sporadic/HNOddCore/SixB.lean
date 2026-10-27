module

public import CFSG.Sporadic.HNOddCore.SixA
public import CFSG.Sporadic.Th.GroupTheory
public import CFSG.GroupActions.PrimitiveCoprimeSimplicity
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2092
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native Equiv

theorem prep_ppowN {n : ℕ} {t : Array ℕ} {g : Perm (Fin n)} (h : PRep n t g) :
    ∀ e, PRep n (ppow n t e) (g ^ e)
  | 0 => by simpa [ppow] using (prep_pid (n := n))
  | e + 1 => by
    rw [pow_succ]
    exact prep_pcomp (prep_ppowN h e) h

theorem mem_arrGen_iff_sift {n : ℕ} (hn : 1 ≤ n) {O : Array (Array ℕ)} {W : Array (List ℤ)}
    {base : List (Fin n)} {sizes : List ℕ} (hb : base.Nodup)
    (h : chainCheck n O W base sizes = true) {t : Array ℕ} {g : Perm (Fin n)} (ht : PRep n t g) :
    siftA n (rawLevels n (strongArrs n O W) (base.map Fin.val).toArray)
      (base.map Fin.val).toArray 0 t = true ↔ g ∈ arrGen n O := by
  unfold chainCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hOS, h2⟩, h3⟩, -⟩ := h
  have hSO : ∀ i < O.size, (strongArrs n O W)[i]! = O[i]! := fun i hi => by
    simpa using allBelowN_spec h2 hi
  have hF := chainCheckFacts h3
  have hA := chainArrays_ofArrays (hn := hn) (k := O.size) (hk := hOS) (hb := hb) (W := W)
    hF.strong_inv
  have hQ : (RawSchreierDatum.ofArrays n hn (strongArrs n O W) O.size hOS base hb
      W).originalSubgroup = arrGen n O := by
    unfold RawSchreierDatum.originalSubgroup arrGen
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
  rw [← hQ]
  exact siftA_iff_mem_originalSubgroup hA (by norm_num) h3 (fun x => ht x)

theorem reach_of_orbitCert {n : ℕ} {gens : Array (Array ℕ)} {gs : ℕ → Perm (Fin n)}
    (hg : ∀ s < gens.size, PRep n gens[s]! (gs s)) {L pos par lab : Array ℕ}
    (h : orbitCertOK n gens L pos par lab = true) :
    ∀ k (hk : k < L.size), ∃ g ∈ Subgroup.closure (Set.range fun s : Fin gens.size => gs s),
      g ⟨L[0]!, ((pointsOK_spec (orbitCertOK_spec h).2.1).2 0 (orbitCertOK_spec h).1).1⟩ =
        ⟨L[k]!, ((pointsOK_spec (orbitCertOK_spec h).2.1).2 k hk).1⟩ := by
  obtain ⟨h0, hpts, htree, -⟩ := orbitCertOK_spec h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      exact ⟨1, Subgroup.one_mem _, rfl⟩
    · obtain ⟨hpar, hlab, hstep⟩ := htree k hk (Nat.pos_of_ne_zero hk0)
      obtain ⟨g, hgK, hge⟩ := ih _ hpar (lt_trans hpar hk)
      refine ⟨gs lab[k]! * g, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨_, hlab⟩, rfl⟩) hgK, ?_⟩
      rw [Perm.mul_apply, hge]
      apply Fin.ext
      rw [← hg _ hlab]
      exact hstep

theorem idPts (n : ℕ) : PtList n (Array.range n) where
  lt k hk := by
    rw [Array.size_range] at hk
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_range]
    exact hk
  inj k hk l hl he := by
    rw [Array.size_range] at hk hl
    rwa [getElem!_pos _ k (by simpa using hk), getElem!_pos _ l (by simpa using hl),
      Array.getElem_range, Array.getElem_range] at he

theorem isSolvable_of_card_two {G : Type*} [Group G] (h : Nat.card G = 2) : Group.IsSolvable G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 G := IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have := hp.isNilpotent
  infer_instance

@[expose] def om0Perm
    (s : ℕ) : Perm (Fin 1100) := if h : s < 12 then phi6 (g6C ⟨s, h⟩) else 1

theorem prep_om0
    {s : ℕ} (hs : s < 12) : PRep 1100 om0Gens[s]! (om0Perm s) := by
  rw [om0Perm, dite_eq_left hs]
  exact prep_phi6 ⟨s, hs⟩

theorem om0Perm_mem
    {s : ℕ} (hs : s < 12) : om0Perm s ∈ phi6.range := by
  rw [om0Perm, dite_eq_left hs]
  exact ⟨_, rfl⟩

@[irreducible] def aArr : Array ℕ := dA om0Gens

theorem aArr_eq : aArr = dA om0Gens := by unfold aArr; rfl

@[irreducible] def bArr : Array ℕ := dB om0Gens

theorem bArr_eq : bArr = dB om0Gens := by unfold bArr; rfl

@[irreducible] def hArr : Array (Array ℕ) := dStab aArr bArr

theorem hArr_eq : hArr = dStab aArr bArr := by unfold hArr; rfl

@[irreducible] def lsArr : Array (Array ℕ) := subOrbits hArr

theorem lsArr_eq : lsArr = subOrbits hArr := by unfold lsArr; rfl

@[irreducible] def labArr : Array ℕ := subLabels lsArr

theorem labArr_eq : labArr = subLabels lsArr := by unfold labArr; rfl

@[irreducible] def lvArr : Array Level := dLevels aArr bArr

theorem lvArr_eq : lvArr = dLevels aArr bArr := by unfold lvArr; rfl

theorem six_parts :
    om0Gens.size = 12 ∧ (∀ g < 12, pisInv 1100 om0Gens[g]! (pinvCand 1100 om0Gens[g]!) = true) ∧
    plettersOK 12 SixData.wa = true ∧ plettersOK 12 SixData.wb = true ∧
    peq 1100 (pcomp 1100 aArr aArr) (pid 1100) = true ∧ peq 1100 aArr (pid 1100) = false ∧
    peq 1100 (ppow 1100 bArr 5) (pid 1100) = true ∧ peq 1100 bArr (pid 1100) = false ∧
    peq 1100 (ppow 1100 (pcomp 1100 aArr bArr) 11) (pid 1100) = true ∧
    peq 1100 (pcomp 1100 aArr bArr) (pid 1100) = false ∧
    peq 1100 (pcomp 1100 aArr bArr) (pcomp 1100 bArr aArr) = false ∧
    chainCheck 1100 #[aArr, bArr] SixData.dWords SixData.dBase SixData.dSizes = true ∧
    orbitOK 1100 #[aArr, bArr] (bfsList 1100 #[aArr, bArr] 0) = true ∧
    (bfsList 1100 #[aArr, bArr] 0).size = 1100 ∧
    (∀ i < hArr.size, (hArr[i]!)[0]! = 0 ∧ pisInv 1100 hArr[i]! (pinvCand 1100 hArr[i]!) = true ∧
      siftA 1100 lvArr dBaseArr 0 hArr[i]! = true) ∧
    lsArr.size = 5 ∧ lsArr.map Array.size = #[1, 336, 105, 630, 28] ∧ (lsArr[0]!)[0]! = 0 ∧
    (∀ i < 5, orbitOK 1100 hArr lsArr[i]! = true) ∧ labArr.size = 1100 ∧
    (∀ i < 5, ∀ k < (lsArr[i]!).size, labArr[(lsArr[i]!)[k]!]! = i) ∧
    (∀ p < 1100, labArr[p]! < 5 ∧ (lsArr[labArr[p]!]!).contains p = true) ∧
    (∀ g < 12, siftA 1100 lvArr dBaseArr 0
        (pcomp 1100 om0Gens[g]! (pcomp 1100 aArr (pinvCand 1100 om0Gens[g]!))) = true ∧
      siftA 1100 lvArr dBaseArr 0
        (pcomp 1100 om0Gens[g]! (pcomp 1100 bArr (pinvCand 1100 om0Gens[g]!))) = true) ∧
    siftA 1100 lvArr dBaseArr 0 om0Gens[5]! = false := by
  have h := six_cert
  unfold sixChecks sixChecksA sixChecksD at h
  rw [← aArr_eq, ← bArr_eq, ← hArr_eq, ← lvArr_eq, ← lsArr_eq, ← labArr_eq] at h
  unfold sixChecksH at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩ := h
  refine ⟨h1, fun g hg => allBelowN_spec h2 hg, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, fun i hi => ?_, h16, h17, h18, fun i hi => allBelowN_spec h19 hi, h20,
    fun i hi k hk => ?_, fun p hp => ?_, fun g hg => ?_, h24⟩
  · have := allBelowN_spec h15 hi
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allBelowN_spec (allBelowN_spec h21 hi) hk
    simpa only [beq_iff_eq] using this
  · have := allBelowN_spec h22 hp
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  · have := allBelowN_spec h23 hg
    simpa only [Bool.and_eq_true] using this

end CFSG.Sporadic.HNOddCore
