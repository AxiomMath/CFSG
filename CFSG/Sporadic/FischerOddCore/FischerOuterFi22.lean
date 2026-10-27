module

public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Check
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Monster.B.Fischer.Fi22Model

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

section Chain

variable {n : ℕ}

@[expose] def fo22Datum (n : ℕ) (hn : 1 ≤ n) (S : Array (Array ℕ)) (k : ℕ)
    (base : List (Fin n)) (hb : base.Nodup) (W : Array (List ℤ)) : RawSchreierDatum n :=
  RawSchreierDatum.ofArrays n hn S (min k S.size) (Nat.min_le_right _ _) base hb W

structure ChainFacts (n : ℕ) (Q : RawSchreierDatum n) (S : Array (Array ℕ)) (baseArr : Array ℕ)
    (k size ord : ℕ) : Prop where
  card : Nat.card Q.originalSubgroup = ord
  eq_closure : Q.originalSubgroup = Subgroup.closure {g | ∃ i < k, permOfArr n S[i]! = g}
  inv : ∀ j < size, isInvA n S[j]! (invCand n S[j]!) = true
  sift : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G →
    siftA n (rawLevels n S baseArr) baseArr 0 g = true → G ∈ Q.originalSubgroup
  strong_mem : ∀ j < size, permOfArr n S[j]! ∈ Q.originalSubgroup
  size_eq : S.size = size

theorem chainFacts_of_ok {hn : 1 ≤ n} {S : Array (Array ℕ)} {k size ord : ℕ}
    {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)} {baseArr : Array ℕ}
    (hbase : (base.map Fin.val).toArray = baseArr) (hk : k ≤ size)
    (hok : fo22ChainOK n S baseArr W k size ord = true) :
    ChainFacts n (fo22Datum n hn S k base hb W) S baseArr k size ord := by
  unfold fo22ChainOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hsz, hraw⟩, hprod⟩ := hok
  have hmin : min k S.size = k := by rw [hsz]; exact Nat.min_eq_left hk
  have hraw' : rawChainOK n (S.extract 0 (min k S.size)) S baseArr W 4 = true := by
    rw [hmin]; exact hraw
  have hA : ChainArrays (fo22Datum n hn S k base hb W) (S.extract 0 (min k S.size)) S
      baseArr W := by
    have h := chainArrays_ofArrays (n := n) (hn := hn) (k := min k S.size)
      (hk := Nat.min_le_right _ _) (base := base) (hb := hb) (W := W)
      (chainCheckFacts hraw').strong_inv
    rw [hbase] at h
    exact h
  have hV := (validSchreier_of_chainOK hA (by norm_num) hraw').1
  refine ⟨?_, ?_, ?_, ?_, ?_, hsz⟩
  · rw [card_originalSubgroup_of_chainOK hA (by norm_num) hraw', hprod]
  · rw [RawSchreierDatum.originalSubgroup]
    congr 1
    ext g
    change g ∈ (fo22Datum n hn S k base hb W).original.toList ↔ _
    rw [fo22Datum, RawSchreierDatum.mem_ofArrays_original, hmin]
    rfl
  · intro j hj
    have hj' : j < S.size := hsz ▸ hj
    have h := (chainCheckFacts hraw').strong_inv j hj'
    rwa [rawInvs, map_getElem! hj'] at h
  · intro g G hG h
    exact (siftA_iff_mem_originalSubgroup hA (by norm_num) hraw' hG).1 h
  · intro j hj
    have hj' : j < (fo22Datum n hn S k base hb W).strongCount := by
      show j < S.size
      rw [hsz]
      exact hj
    have h := RawSchreierDatum.strong_get_mem_originalSubgroup _ hV ⟨j, hj'⟩
    have e : (fo22Datum n hn S k base hb W).strong.get ⟨j, hj'⟩ = permOfArr n S[j]! :=
      RawSchreierDatum.ofArrays_strong_get (n := n) ⟨j, hj'⟩
    rwa [e] at h

theorem ChainFacts.eq_closure_two {Q : RawSchreierDatum n} {S : Array (Array ℕ)}
    {baseArr : Array ℕ} {size ord : ℕ} (h : ChainFacts n Q S baseArr 2 size ord) :
    Q.originalSubgroup = Subgroup.closure {permOfArr n S[0]!, permOfArr n S[1]!} := by
  rw [h.eq_closure]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

end Chain

section Simple

variable {m : ℕ}

theorem trans_of_treeOK {Q : RawSchreierDatum m} {S : Array (Array ℕ)} {baseArr : Array ℕ}
    {size ord' : ℕ} (hc : ChainFacts m Q S baseArr 2 size ord') (h2 : 2 ≤ size)
    {ord par gen : Array ℕ} (h : fo22TreeOK m S ord par gen = true) (hm : 0 < m) :
    ∀ p : Fin m, ∃ g ∈ Q.originalSubgroup, g ⟨0, hm⟩ = p := by
  unfold fo22TreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hos, hps⟩, hgs⟩, hinv⟩, ho0⟩, hall⟩ := h
  have hrep : ∀ i < 2, Rep m S[i]! (permOfArr m S[i]!) := fun i hi =>
    (rep_permOfArr (hc.inv i (by omega))).1
  have hmem : ∀ i < 2, permOfArr m S[i]! ∈ Q.originalSubgroup := fun i hi =>
    hc.strong_mem i (by omega)
  have hpt : ∀ i < m, ∃ g ∈ Q.originalSubgroup, ((g ⟨0, hm⟩ : Fin m) : ℕ) = ord[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hi' := allLt_spec hall hi
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hi'
      rcases hi' with h0 | ⟨⟨hpi, hgi⟩, hstep⟩
      · subst h0
        exact ⟨1, Q.originalSubgroup.one_mem, by rw [ho0]; rfl⟩
      · obtain ⟨g, hg, hgv⟩ := ih (par[i]!) hpi (by omega)
        refine ⟨permOfArr m S[gen[i]!]! * g, Q.originalSubgroup.mul_mem (hmem _ hgi) hg, ?_⟩
        rw [Equiv.Perm.mul_apply, ← (hrep _ hgi) (g ⟨0, hm⟩), hgv]
        exact hstep
  intro p
  have hord := rep_permOfArr hinv
  set σ := permOfArr m ord
  obtain ⟨g, hg, hgv⟩ := hpt (σ⁻¹ p) (σ⁻¹ p).2
  refine ⟨g, hg, Fin.ext ?_⟩
  rw [hgv, hord.1.apply (σ⁻¹ p).2]
  simp [σ]

theorem sub_facts {S : Array (Array ℕ)} {lab ord tpar tgen start : Array ℕ} {k : ℕ}
    (h : fo22SubOK m S lab ord tpar tgen start k = true) :
    lab.size = m ∧ (∀ p < m, lab[p]! < k) ∧ isInvA m ord (invCand m ord) = true ∧
      start[0]! = 0 ∧ start[k]! = m ∧ (∀ c < k, start[c]! < start[c + 1]!) ∧
      lab[0]! = 0 ∧ ord[0]! = 0 ∧
      (∀ c < k, ∀ d < start[c + 1]! - start[c]!,
        lab[ord[start[c]! + d]!]! = c ∧ (d = 0 ∨
          (start[c]! ≤ tpar[start[c]! + d]! ∧ tpar[start[c]! + d]! < start[c]! + d ∧
            tgen[start[c]! + d]! < S.size ∧ (S[tgen[start[c]! + d]!]!)[0]! = 0 ∧
            (S[tgen[start[c]! + d]!]!)[ord[tpar[start[c]! + d]!]!]! = ord[start[c]! + d]!))) ∧
      (∀ g < S.size, (S[g]!)[0]! ≠ 0 ∨ ∀ p < m, lab[(S[g]!)[p]!]! = lab[p]!) := by
  unfold fo22SubOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, fun p hp => of_decide_eq_true (allLt_spec h2 hp), h3, h4, h5,
    fun c hc => of_decide_eq_true (allLt_spec h6 hc), h7, h8, fun c hc d hd => ?_,
    fun g hg => ?_⟩
  · have := allLt_spec (allLt_spec h9 hc) hd
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, this.2.imp id fun h => ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩⟩
  · have := allLt_spec h10 hg
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr fun p hp => by
        have := allLt_spec h hp
        simpa only [beq_iff_eq] using this

theorem rep_fo22powA {t : Array ℕ} {g : Equiv.Perm (Fin m)} (ht : Rep m t g) :
    ∀ e, Rep m (powA m t e) (g ^ e)
  | 0 => by rw [pow_zero]; exact rep_idA
  | e + 1 => by
    rw [pow_succ']
    exact rep_compA ht (rep_fo22powA ht e)

theorem exists_class {start : Array ℕ} {k : ℕ} (h0 : start[0]! = 0) (hk : start[k]! = m)
    {i : ℕ} (hi : i < m) : ∃ c < k, start[c]! ≤ i ∧ i < start[c + 1]! := by
  classical
  have hex : ∃ c, i < start[c + 1]! ∧ c + 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [h0] at hk
      omega
    · exact ⟨k - 1, by rw [show k - 1 + 1 = k by omega, hk]; exact hi, by omega⟩
  let c₀ := Nat.find hex
  have hc₀ : i < start[c₀ + 1]! ∧ c₀ + 1 ≤ k := Nat.find_spec hex
  refine ⟨c₀, by omega, ?_, hc₀.1⟩
  rcases Nat.eq_zero_or_pos c₀ with h | h
  · rw [h, h0]
    exact Nat.zero_le _
  · have hmin := Nat.find_min hex (show c₀ - 1 < c₀ by omega)
    rw [show c₀ - 1 + 1 = c₀ by omega] at hmin
    by_contra hlt
    exact hmin ⟨by omega, by omega⟩

theorem start_le_of_inc {start : Array ℕ} {k : ℕ} (hsinc : ∀ c < k, start[c]! < start[c + 1]!) :
    ∀ c ≤ k, start[c]! ≤ start[k]! := by
  intro c hc
  induction k with
  | zero => rw [Nat.le_zero.1 hc]
  | succ k ih =>
    rcases Nat.lt_or_ge c (k + 1) with h | h
    · exact (ih (fun c' hc' => hsinc c' (by omega)) (by omega)).trans
        (le_of_lt (hsinc k (by omega)))
    · rw [show c = k + 1 by omega]

theorem card_filter_Ico_fin {a b : ℕ} (hb : b ≤ m) :
    (Finset.univ.filter fun i : Fin m => a ≤ i.1 ∧ i.1 < b).card = b - a := by
  have e : (Finset.univ.filter fun i : Fin m => a ≤ i.1 ∧ i.1 < b) =
      (Finset.Ico a b).attachFin (fun x hx => by rw [Finset.mem_Ico] at hx; omega) := by
    ext i
    simp [Finset.mem_attachFin, Finset.mem_Ico]
  rw [e, Finset.card_attachFin, Nat.card_Ico]

theorem isSimpleGroup_of_checks (hm : 2 ≤ m) {hn : 1 ≤ m} {S : Array (Array ℕ)}
    {size ord : ℕ} {base : List (Fin m)} {hb : base.Nodup} {W : Array (List ℤ)}
    {baseArr : Array ℕ} (hc : ChainFacts m (fo22Datum m hn S 2 base hb W) S baseArr 2 size ord)
    (h2 : 2 ≤ size) {tord tpar tgen : Array ℕ} (htree : fo22TreeOK m S tord tpar tgen = true)
    {lab ordl spar sgen start : Array ℕ} {k : ℕ} (hk0 : 0 < k)
    (hsub : fo22SubOK m S lab ordl spar sgen start k = true)
    (hdiv : ∀ T : Finset (Fin k), ⟨0, hk0⟩ ∈ T →
      (∑ c ∈ T, (start[c.1 + 1]! - start[c.1]!)) ∣ m → T = {⟨0, hk0⟩} ∨ T = Finset.univ)
    {oa pb e oab : ℕ} (hord : fo22OrderOK m S oa pb e oab = true) (hoa : oa.Prime)
    (hpb : pb.Prime) (hoab : oab.Prime) (hab : oa.Coprime (pb ^ (e + 1)))
    (hprod : oab.Coprime (ord / m)) :
    IsSimpleGroup (fo22Datum m hn S 2 base hb W).originalSubgroup := by
  classical
  set P := (fo22Datum m hn S 2 base hb W).originalSubgroup
  have hm0 : 0 < m := by omega
  obtain ⟨-, hlab, hordinv, hs0, hsk, hsinc, hl0, ho0, hcls, hinvar⟩ := sub_facts hsub
  let lab' : Fin m → Fin k := fun p => ⟨lab[p.1]!, hlab p.1 p.2⟩
  set Hs : Set (Equiv.Perm (Fin m)) :=
    {h | ∃ g < S.size, (S[g]!)[0]! = 0 ∧ permOfArr m S[g]! = h} with hHsdef
  have hsize : S.size = size := hc.size_eq
  have hrepS : ∀ g < S.size, Rep m S[g]! (permOfArr m S[g]!) := fun g hg =>
    (rep_permOfArr (hc.inv g (hsize ▸ hg))).1
  have hHs : ∀ h ∈ Hs, h ∈ P ∧ h ⟨0, hm0⟩ = ⟨0, hm0⟩ := by
    rintro _ ⟨g, hg, hg0, rfl⟩
    refine ⟨hc.strong_mem g (hsize ▸ hg), Fin.ext ?_⟩
    rw [← (hrepS g hg) ⟨0, hm0⟩]
    exact hg0
  have hlabinv : ∀ h ∈ Hs, ∀ p, lab' (h p) = lab' p := by
    rintro _ ⟨g, hg, hg0, rfl⟩ p
    apply Fin.ext
    show lab[((permOfArr m S[g]!) p : ℕ)]! = lab[p.1]!
    rw [← (hrepS g hg) p]
    rcases hinvar g hg with h | h
    · exact absurd hg0 h
    · exact h p.1 p.2
  have hordrep := (rep_permOfArr hordinv).1
  set σ := permOfArr m ordl
  have hσ : ∀ i (hi : i < m), ((σ ⟨i, hi⟩ : Fin m) : ℕ) = ordl[i]! := fun i hi =>
    (hordrep ⟨i, hi⟩).symm
  have hstart_le : ∀ c ≤ k, start[c]! ≤ m := fun c hc => hsk ▸ start_le_of_inc hsinc c hc
  have hroot : ∀ c < k, start[c]! < m := fun c hc => by
    have := hstart_le (c + 1) hc
    have := hsinc c hc
    omega
  have htreec : ∀ c (hc : c < k) d (hd : start[c]! + d < start[c + 1]!),
      ∃ h ∈ Subgroup.closure Hs,
        ((h (σ ⟨start[c]!, hroot c hc⟩) : Fin m) : ℕ) = ordl[start[c]! + d]! := by
    intro c hc d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hd
      rcases (hcls c hc d (by omega)).2 with h0 | ⟨hp1, hp2, hg1, hg2, hg3⟩
      · subst h0
        exact ⟨1, Subgroup.one_mem _, by rw [Equiv.Perm.one_apply, hσ, Nat.add_zero]⟩
      · obtain ⟨h', hh', hh'v⟩ := ih (spar[start[c]! + d]! - start[c]!) (by omega) (by omega)
        rw [show start[c]! + (spar[start[c]! + d]! - start[c]!) = spar[start[c]! + d]! by
          omega] at hh'v
        have hgen : permOfArr m S[sgen[start[c]! + d]!]! ∈ Hs := ⟨_, hg1, hg2, rfl⟩
        refine ⟨permOfArr m S[sgen[start[c]! + d]!]! * h',
          Subgroup.mul_mem _ (Subgroup.subset_closure hgen) hh', ?_⟩
        rw [Equiv.Perm.mul_apply, ← (hrepS _ hg1) _, hh'v]
        exact hg3
  have hclass : ∀ p : Fin m, ∃ c < k, ∃ d, start[c]! + d < start[c + 1]! ∧
      ordl[start[c]! + d]! = p.1 ∧ lab[p.1]! = c := by
    intro p
    set i := ((σ⁻¹ p : Fin m) : ℕ)
    have hi : i < m := (σ⁻¹ p).2
    have hpi : ordl[i]! = p.1 := by
      rw [← hσ i hi]
      simp [i]
    obtain ⟨c, hc, hci, hic⟩ := exists_class hs0 hsk hi
    refine ⟨c, hc, i - start[c]!, by omega, by rw [Nat.add_sub_cancel' hci, hpi], ?_⟩
    have := (hcls c hc (i - start[c]!) (by omega)).1
    rw [Nat.add_sub_cancel' hci, hpi] at this
    exact this
  have horb : ∀ p q : Fin m, lab' p = lab' q → ∃ h ∈ Subgroup.closure Hs, h p = q := by
    intro p q hpq
    obtain ⟨c, hc, d, hd, hpd, hlp⟩ := hclass p
    obtain ⟨c', hc', d', hd', hqd, hlq⟩ := hclass q
    have hcc : c = c' := by
      have := congrArg Fin.val hpq
      simp only [lab'] at this
      omega
    subst hcc
    obtain ⟨hp, hpm, hpv⟩ := htreec c hc d hd
    obtain ⟨hq, hqm, hqv⟩ := htreec c hc d' hd'
    refine ⟨hq * hp⁻¹, Subgroup.mul_mem _ hqm (Subgroup.inv_mem _ hpm), ?_⟩
    have hp' : hp (σ ⟨start[c]!, hroot c hc⟩) = p := Fin.ext (hpv.trans hpd)
    have hq' : hq (σ ⟨start[c]!, hroot c hc⟩) = q := Fin.ext (hqv.trans hqd)
    rw [Equiv.Perm.mul_apply, ← hp', Equiv.Perm.inv_eq_iff_eq.2 rfl, hq']
  have hcard : ∀ c : Fin k, (Finset.univ.filter fun p : Fin m => lab' p = c).card =
      start[c.1 + 1]! - start[c.1]! := by
    intro c
    have e : (Finset.univ.filter fun p : Fin m => lab' p = c) =
        (Finset.univ.filter fun i : Fin m => start[c.1]! ≤ i.1 ∧ i.1 < start[c.1 + 1]!).map
          σ.toEmbedding := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.toEmbedding_apply]
      constructor
      · intro hp
        obtain ⟨c', hc', d, hd, hpd, hlp⟩ := hclass p
        have hcc : c'= c.1 := by
          have := congrArg Fin.val hp
          simp only [lab'] at this
          omega
        subst hcc
        refine ⟨⟨start[c.1]! + d, by have := hstart_le (c.1 + 1) hc'; omega⟩, ⟨by simp, hd⟩, ?_⟩
        apply Fin.ext
        rw [hσ, hpd]
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        apply Fin.ext
        show lab[((σ i : Fin m) : ℕ)]! = c.1
        rw [hσ i.1 i.2]
        have := (hcls c.1 c.2 (i.1 - start[c.1]!) (by omega)).1
        rwa [Nat.add_sub_cancel' hi1] at this
    rw [e, Finset.card_map, card_filter_Ico_fin (hstart_le (c.1 + 1) c.2)]
  unfold fo22OrderOK at hord
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hord
  obtain ⟨⟨⟨⟨⟨ho1, ho2⟩, ho3⟩, ho4⟩, ho5⟩, ho6⟩ := hord
  have hS0 : 0 < S.size := by omega
  have hS1 : 1 < S.size := by omega
  have hra := hrepS 0 hS0
  have hrb := hrepS 1 hS1
  set a := permOfArr m S[0]!
  set b := permOfArr m S[1]!
  have hne : ∀ {t : Array ℕ} {g : Equiv.Perm (Fin m)}, Rep m t g → eqA m t (idA m) = false →
      g ≠ 1 := fun ht hf hg => by
    rw [hg] at ht
    rw [(eqA_iff ht rep_idA).2 rfl] at hf
    exact Bool.noConfusion hf
  have haord : orderOf a = oa := by
    have : Fact oa.Prime := ⟨hoa⟩
    exact orderOf_eq_prime (eq_of_eqA (rep_fo22powA hra oa) rep_idA ho1) (hne hra ho2)
  have hbord : orderOf b = pb ^ (e + 1) := by
    have : Fact pb.Prime := ⟨hpb⟩
    exact orderOf_eq_prime_pow (hne (rep_fo22powA hrb (pb ^ e)) ho4)
      (eq_of_eqA (rep_fo22powA hrb (pb ^ (e + 1))) rep_idA ho3)
  have habord : orderOf (a * b) = oab := by
    have : Fact oab.Prime := ⟨hoab⟩
    exact orderOf_eq_prime (eq_of_eqA (rep_fo22powA (rep_compA hra hrb) oab) rep_idA ho5)
      (hne (rep_compA hra hrb) ho6)
  refine isSimpleGroup_of_permCert hm hc.eq_closure_two ⟨0, hm0⟩
    (trans_of_treeOK hc h2 htree hm0) (Hs := Hs) hHs lab' hlabinv horb ?_ ?_ ?_
  · intro T hT hd
    have hl0' : lab' ⟨0, hm0⟩ = ⟨0, hk0⟩ := Fin.ext hl0
    rw [hl0'] at hT ⊢
    refine hdiv T hT ?_
    rwa [Finset.sum_congr rfl fun c _ => (hcard c).symm]
  · rw [haord, hbord]
    exact hab
  · rw [habord, hc.card]
    exact hprod

end Simple

section Data

theorem extract_getElem! {a : Array (Array ℕ)} {j k : ℕ} (hj : j < k) (hk : k ≤ a.size) :
    (a.extract 0 k)[j]! = a[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos a j (by omega), Array.getElem_extract]
  simp

theorem fi22CentStrong_size {c : ℕ} (_hc : c < 5) :
    (fi22CentStrong c).size = fi22CentStrongCount.getD c 0 := by
  rw [fi22CentStrong, Array.size_ofFn]

theorem fo22_hgens {c : ℕ} (hc : c < 5) {j : ℕ} (hj : j < fi22CentGenCount.getD c 0) :
    ((fi22CentStrong c).extract 0 (fi22CentGenCount.getD c 0))[j]! =
      fi22CentArr (fi22CentStrongStart.getD c 0 + j) := by
  have hgs : fi22CentGenCount.getD c 0 ≤ fi22CentStrongCount.getD c 0 := by
    interval_cases c <;> decide
  have hle : fi22CentGenCount.getD c 0 ≤ (fi22CentStrong c).size := by
    rw [fi22CentStrong_size hc]
    exact hgs
  rw [extract_getElem! hj hle, fi22CentStrong_get hc (by omega)]

theorem rep_conj_fi22CentArr
    {L : ℕ} (hL : L < 306) {x : Array ℕ} {X : Equiv.Perm (Fin 3510)}
    (hx : Rep 3510 x X) :
    Rep 3510 (conjA 3510 (fi22CentArr L) x) (fi22CentPerm L * X * (fi22CentPerm L)⁻¹) :=
  rep_conjA (rep_fi22CentPerm hL) (fi22Cent_check.2.1 L hL) hx

theorem conj_mem_of_closure_two {G : Type*} [Group G] {N : Subgroup G} {a b t : G}
    (hN : N = Subgroup.closure {a, b}) (ha : t * a * t⁻¹ ∈ N) (hb : t * b * t⁻¹ ∈ N) :
    ∀ x ∈ N, t * x * t⁻¹ ∈ N := by
  have hle : N ≤ N.comap (MulAut.conj t).toMonoidHom := by
    conv_lhs => rw [hN]
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  exact fun x hx => hle hx

end Data

section N3

@[expose] def fo22N3Datum : RawSchreierDatum 3510 :=
  fo22Datum 3510 (by decide) fo22N3Strong 2 (fi22FinList 3510 (by decide) [9, 0, 1, 2])
    (by decide) fo22N3Words

@[expose] def fo22N3 : Subgroup (Equiv.Perm (Fin 3510)) := fo22N3Datum.originalSubgroup

theorem fo22N3_facts :
    ChainFacts 3510 fo22N3Datum fo22N3Strong #[9, 0, 1, 2] 2 7 174182400 :=
  chainFacts_of_ok rfl (by norm_num) fo22N3Chain_ok

@[expose] def fo22P3Datum : RawSchreierDatum 1575 :=
  fo22Datum 1575 (by decide) fo22P3Strong 2 (fi22FinList 1575 (by decide) [0, 1, 2, 4, 3])
    (by decide) fo22P3Words

theorem fo22P3_facts :
    ChainFacts 1575 fo22P3Datum fo22P3Strong #[0, 1, 2, 4, 3] 2 11 174182400 :=
  chainFacts_of_ok rfl (by norm_num) fo22P3Chain_ok

theorem fo22Sizes3 : ∀ T : Finset (Fin 7), (⟨0, by norm_num⟩ : Fin 7) ∈ T →
    (∑ c ∈ T, (fo22Start3[c.1 + 1]! - fo22Start3[c.1]!)) ∣ 1575 →
      T = {⟨0, by norm_num⟩} ∨ T = Finset.univ := by
  decide +kernel

theorem isSimpleGroup_fo22P3 :
    IsSimpleGroup fo22P3Datum.originalSubgroup :=
  isSimpleGroup_of_checks (by norm_num) fo22P3_facts (by norm_num) fo22Tree3_ok (by norm_num)
    fo22Sub3_ok fo22Sizes3 fo22Order3_ok Nat.prime_three Nat.prime_five (by norm_num)
    (by norm_num) (by norm_num)

@[expose] def fo22T3 : Array (Array ℕ) :=
  treeConjN 3510 2 #[fo22N3Strong[0]!, fo22N3Strong[1]!] fo22S03 fo22Tree3

theorem fo22T3_facts : fo22T3.size = 1575 ∧
    (∀ j < 1575, isInvA 3510 fo22T3[j]! (invCand 3510 fo22T3[j]!) = true ∧
      eqA 3510 (conjA 3510 fo22N3Strong[0]! fo22T3[j]!) fo22T3[(fo22P3Strong[0]!)[j]!]! = true ∧
      eqA 3510 (conjA 3510 fo22N3Strong[1]! fo22T3[j]!) fo22T3[(fo22P3Strong[1]!)[j]!]! = true) ∧
    (∀ j < 1575, ∀ k < j, eqA 3510 fo22T3[j]! fo22T3[k]! = false) := by
  have h := fo22Class3_ok
  unfold fo22ClassOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun j hj => ?_, fun j hj k hk => ?_⟩
  · have := allLt_spec h2 hj
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec h3 hj) hk
    simp only [Bool.not_eq_true'] at this
    exact this

@[expose] def fo22T3j (j : Fin 1575) : Equiv.Perm (Fin 3510) := permOfArr 3510 fo22T3[j.1]!

theorem rep_fo22T3j
    (j : Fin 1575) : Rep 3510 fo22T3[j.1]! (fo22T3j j) :=
  (rep_permOfArr (fo22T3_facts.2.1 j j.2).1).1

theorem fo22T3j_injective : Function.Injective fo22T3j := by
  intro j k h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with hlt | hlt
  · have := fo22T3_facts.2.2 k k.2 j hlt
    rw [(eqA_iff (rep_fo22T3j k) (rep_fo22T3j j)).2 h.symm] at this
    exact Bool.noConfusion this
  · have := fo22T3_facts.2.2 j j.2 k hlt
    rw [(eqA_iff (rep_fo22T3j j) (rep_fo22T3j k)).2 h] at this
    exact Bool.noConfusion this

theorem fo22T3j_conj (i : ℕ) (hi : i < 2) (j : Fin 1575) :
    fo22T3j (permOfArr 1575 fo22P3Strong[i]! j) = conjPerm (permOfArr 3510 fo22N3Strong[i]!)
      (fo22T3j j) := by
  have hrN := (rep_permOfArr (fo22N3_facts.inv i (by omega))).1
  have hrP := (rep_permOfArr (fo22P3_facts.inv i (by omega))).1
  have h1 := rep_conjA hrN (fo22N3_facts.inv i (by omega)) (rep_fo22T3j j)
  have e : fo22T3[(fo22P3Strong[i]!)[j.1]!]! = fo22T3[(permOfArr 1575 fo22P3Strong[i]! j).1]! := by
    rw [hrP.apply j.2]
  have h2 := rep_fo22T3j (permOfArr 1575 fo22P3Strong[i]! j)
  rw [← e] at h2
  have heq : eqA 3510 (conjA 3510 fo22N3Strong[i]! fo22T3[j.1]!)
      fo22T3[(fo22P3Strong[i]!)[j.1]!]! = true := by
    interval_cases i
    · exact (fo22T3_facts.2.1 j j.2).2.1
    · exact (fo22T3_facts.2.1 j j.2).2.2
  rw [conjPerm_apply]
  exact (eq_of_eqA h1 h2 heq).symm

theorem isSimpleGroup_fo22N3 : IsSimpleGroup fo22N3 := by
  have : IsSimpleGroup fo22P3Datum.originalSubgroup := isSimpleGroup_fo22P3
  exact isSimpleGroup_of_famHom conjPerm fo22T3j_injective (fo22T3j_conj 0 (by norm_num))
    (fo22T3j_conj 1 (by norm_num)) fo22N3_facts.eq_closure_two fo22P3_facts.eq_closure_two
    (by rw [fo22N3, fo22N3_facts.card, fo22P3_facts.card]) this

theorem card_fo22N3 :
    Nat.card fo22N3 = 174182400 := fo22N3_facts.card

theorem fo22N3_facts_normal :
    siftA 3510 (rawLevels 3510 (fi22CentStrong 3) fo22HBase) fo22HBase 0 fo22N3Strong[0]! = true ∧
    siftA 3510 (rawLevels 3510 (fi22CentStrong 3) fo22HBase) fo22HBase 0 fo22N3Strong[1]! = true ∧
    ∀ j < 9, siftA 3510 (rawLevels 3510 fo22N3Strong #[9, 0, 1, 2]) #[9, 0, 1, 2] 0
        (conjA 3510 ((fi22CentStrong 3).extract 0 9)[j]! fo22N3Strong[0]!) = true ∧
      siftA 3510 (rawLevels 3510 fo22N3Strong #[9, 0, 1, 2]) #[9, 0, 1, 2] 0
        (conjA 3510 ((fi22CentStrong 3).extract 0 9)[j]! fo22N3Strong[1]!) = true := by
  have h := fo22N3InNormal_ok
  unfold fo22InNormalOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun j hj => ?_⟩
  have hsz : ((fi22CentStrong 3).extract 0 9).size = 9 := by
    rw [Array.size_extract, fi22CentStrong_size (by norm_num)]
    rfl
  have := allLt_spec h3 (by rw [hsz]; exact hj)
  simpa only [Bool.and_eq_true] using this

theorem fo22N3_le :
    fo22N3 ≤ fi22H 3 := by
  rw [fo22N3, fo22N3_facts.eq_closure_two, Subgroup.closure_le]
  obtain ⟨h1, h2, -⟩ := fo22N3_facts_normal
  rintro _ (rfl | rfl)
  · exact (siftA_iff_mem_fi22H (by norm_num)
      (rep_permOfArr (fo22N3_facts.inv 0 (by norm_num))).1).1 h1
  · exact (siftA_iff_mem_fi22H (by norm_num)
      (rep_permOfArr (fo22N3_facts.inv 1 (by norm_num))).1).1 h2

theorem fo22N3_normal :
    (fo22N3.subgroupOf (fi22H 3)).Normal := by
  refine normal_subgroupOf_of_conj (fi22H_eq_closure (c := 3) (by norm_num)) fo22N3_le ?_
  rintro _ ⟨j, hj, rfl⟩
  have hj9 : j < 9 := hj
  have hL : fi22CentStrongStart.getD 3 0 + j < 306 := by
    show 44 + j < 306
    omega
  obtain ⟨-, -, h3⟩ := fo22N3_facts_normal
  obtain ⟨ha, hb⟩ := h3 j hj9
  have hg := fo22_hgens (c := 3) (by norm_num) hj
  have hg' : ((fi22CentStrong 3).extract 0 9)[j]! =
      fi22CentArr (fi22CentStrongStart.getD 3 0 + j) := hg
  rw [hg'] at ha hb
  refine conj_mem_of_closure_two (fo22N3_facts.eq_closure_two) ?_ ?_
  · exact fo22N3_facts.sift (rep_conj_fi22CentArr hL
      (rep_permOfArr (fo22N3_facts.inv 0 (by norm_num))).1) ha
  · exact fo22N3_facts.sift (rep_conj_fi22CentArr hL
      (rep_permOfArr (fo22N3_facts.inv 1 (by norm_num))).1) hb

end N3

section N4

@[expose] def fo22N4Datum : RawSchreierDatum 3510 :=
  fo22Datum 3510 (by decide) fo22N4Strong 2 (fi22FinList 3510 (by decide) [0, 1, 2]) (by decide)
    fo22N4Words

@[expose] def fo22N4 : Subgroup (Equiv.Perm (Fin 3510)) := fo22N4Datum.originalSubgroup

theorem fo22N4_facts :
    ChainFacts 3510 fo22N4Datum fo22N4Strong #[0, 1, 2] 2 7 1451520 :=
  chainFacts_of_ok rfl (by norm_num) fo22N4Chain_ok

@[expose] def fo22P4Datum : RawSchreierDatum 63 :=
  fo22Datum 63 (by decide) fo22P4Strong 2 (fi22FinList 63 (by decide) [0, 1, 2, 4, 3, 5])
    (by decide) fo22P4Words

theorem fo22P4_facts :
    ChainFacts 63 fo22P4Datum fo22P4Strong #[0, 1, 2, 4, 3, 5] 2 11 1451520 :=
  chainFacts_of_ok rfl (by norm_num) fo22P4Chain_ok

theorem fo22Sizes4 : ∀ T : Finset (Fin 3), (⟨0, by norm_num⟩ : Fin 3) ∈ T →
    (∑ c ∈ T, (fo22Start4[c.1 + 1]! - fo22Start4[c.1]!)) ∣ 63 →
      T = {⟨0, by norm_num⟩} ∨ T = Finset.univ := by
  decide +kernel

theorem isSimpleGroup_fo22P4 :
    IsSimpleGroup fo22P4Datum.originalSubgroup :=
  isSimpleGroup_of_checks (by norm_num) fo22P4_facts (by norm_num) fo22Tree4_ok (by norm_num)
    fo22Sub4_ok fo22Sizes4 fo22Order4_ok Nat.prime_three Nat.prime_two (by norm_num)
    (by norm_num) (by norm_num)

theorem fo22O63_facts : fo22O63.size = 63 ∧ fo22O63[62]! < 3510 ∧
    (∀ j < 62, fo22O63[j]! < fo22O63[j + 1]!) ∧
    (∀ j < 63, (fo22P4Strong[0]!)[j]! < 63 ∧ (fo22P4Strong[1]!)[j]! < 63 ∧
      (fo22N4Strong[0]!)[fo22O63[j]!]! = fo22O63[(fo22P4Strong[0]!)[j]!]! ∧
      (fo22N4Strong[1]!)[fo22O63[j]!]! = fo22O63[(fo22P4Strong[1]!)[j]!]!) := by
  have h := fo22Orbit4_ok
  unfold fo22OrbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun j hj => of_decide_eq_true (allLt_spec h3 hj), fun j hj => ?_⟩
  have := allLt_spec h4 hj
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem fo22O63_mono
    {i j : ℕ} (hij : i < j) (hj : j < 63) : fo22O63[i]! < fo22O63[j]! := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih h (by omega)).trans (fo22O63_facts.2.2.1 j (by omega))
    · subst h
      exact fo22O63_facts.2.2.1 i (by omega)

theorem fo22O63_lt {j : ℕ} (hj : j < 63) : fo22O63[j]! < 3510 := by
  rcases Nat.lt_or_ge j 62 with h | h
  · exact (fo22O63_mono h (by norm_num)).trans fo22O63_facts.2.1
  · rw [show j = 62 by omega]
    exact fo22O63_facts.2.1

@[expose] def fo22O63j
    (j : Fin 63) : Fin 3510 := ⟨fo22O63[j.1]!, fo22O63_lt j.2⟩

theorem fo22O63j_injective :
    Function.Injective fo22O63j := fun i j h => by
  have h' : fo22O63[i.1]! = fo22O63[j.1]! := congrArg Fin.val h
  rcases lt_trichotomy i.1 j.1 with hl | he | hg
  · exact absurd h' (fo22O63_mono hl j.2).ne
  · exact Fin.ext he
  · exact absurd h' (fo22O63_mono hg i.2).ne'

theorem fo22O63j_val
    (j : Fin 63) : (fo22O63j j : ℕ) = fo22O63[j.1]! := rfl

theorem toPermHom_apply_perm {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n) :
    MulAction.toPermHom (Equiv.Perm (Fin n)) (Fin n) g x = g x := rfl

theorem fo22O63j_act (i : ℕ) (hi : i < 2) (j : Fin 63) :
    fo22O63j (permOfArr 63 fo22P4Strong[i]! j) =
      MulAction.toPermHom (Equiv.Perm (Fin 3510)) (Fin 3510) (permOfArr 3510 fo22N4Strong[i]!)
        (fo22O63j j) := by
  have hrN := (rep_permOfArr (fo22N4_facts.inv i (by omega))).1
  have hrP := (rep_permOfArr (fo22P4_facts.inv i (by omega))).1
  rw [toPermHom_apply_perm]
  apply Fin.ext
  rw [fo22O63j_val, ← hrN (fo22O63j j), ← hrP j, fo22O63j_val]
  obtain ⟨-, -, h1, h2⟩ := fo22O63_facts.2.2.2 j j.2
  interval_cases i
  · exact h1.symm
  · exact h2.symm

theorem isSimpleGroup_fo22N4 : IsSimpleGroup fo22N4 := by
  have : IsSimpleGroup fo22P4Datum.originalSubgroup := isSimpleGroup_fo22P4
  exact isSimpleGroup_of_famHom (MulAction.toPermHom (Equiv.Perm (Fin 3510)) (Fin 3510))
    fo22O63j_injective (fo22O63j_act 0 (by norm_num)) (fo22O63j_act 1 (by norm_num))
    fo22N4_facts.eq_closure_two fo22P4_facts.eq_closure_two
    (by rw [fo22N4, fo22N4_facts.card, fo22P4_facts.card]) this

theorem fo22N4_facts_normal :
    siftA 3510 (rawLevels 3510 (fi22CentStrong 4) fo22HBase) fo22HBase 0 fo22N4Strong[0]! = true ∧
    siftA 3510 (rawLevels 3510 (fi22CentStrong 4) fo22HBase) fo22HBase 0 fo22N4Strong[1]! = true ∧
    ∀ j < 9, siftA 3510 (rawLevels 3510 fo22N4Strong #[0, 1, 2]) #[0, 1, 2] 0
        (conjA 3510 ((fi22CentStrong 4).extract 0 9)[j]! fo22N4Strong[0]!) = true ∧
      siftA 3510 (rawLevels 3510 fo22N4Strong #[0, 1, 2]) #[0, 1, 2] 0
        (conjA 3510 ((fi22CentStrong 4).extract 0 9)[j]! fo22N4Strong[1]!) = true := by
  have h := fo22N4InNormal_ok
  unfold fo22InNormalOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun j hj => ?_⟩
  have hsz : ((fi22CentStrong 4).extract 0 9).size = 9 := by
    rw [Array.size_extract, fi22CentStrong_size (by norm_num)]
    rfl
  have := allLt_spec h3 (by rw [hsz]; exact hj)
  simpa only [Bool.and_eq_true] using this

theorem fo22N4_le :
    fo22N4 ≤ fi22H 4 := by
  rw [fo22N4, fo22N4_facts.eq_closure_two, Subgroup.closure_le]
  obtain ⟨h1, h2, -⟩ := fo22N4_facts_normal
  rintro _ (rfl | rfl)
  · exact (siftA_iff_mem_fi22H (by norm_num)
      (rep_permOfArr (fo22N4_facts.inv 0 (by norm_num))).1).1 h1
  · exact (siftA_iff_mem_fi22H (by norm_num)
      (rep_permOfArr (fo22N4_facts.inv 1 (by norm_num))).1).1 h2

theorem fo22N4_normal :
    (fo22N4.subgroupOf (fi22H 4)).Normal := by
  refine normal_subgroupOf_of_conj (fi22H_eq_closure (c := 4) (by norm_num)) fo22N4_le ?_
  rintro _ ⟨j, hj, rfl⟩
  have hj9 : j < 9 := hj
  have hL : fi22CentStrongStart.getD 4 0 + j < 306 := by
    show 63 + j < 306
    omega
  obtain ⟨-, -, h3⟩ := fo22N4_facts_normal
  obtain ⟨ha, hb⟩ := h3 j hj9
  have hg := fo22_hgens (c := 4) (by norm_num) hj
  have hg' : ((fi22CentStrong 4).extract 0 9)[j]! =
      fi22CentArr (fi22CentStrongStart.getD 4 0 + j) := hg
  rw [hg'] at ha hb
  refine conj_mem_of_closure_two (fo22N4_facts.eq_closure_two) ?_ ?_
  · exact fo22N4_facts.sift (rep_conj_fi22CentArr hL
      (rep_permOfArr (fo22N4_facts.inv 0 (by norm_num))).1) ha
  · exact fo22N4_facts.sift (rep_conj_fi22CentArr hL
      (rep_permOfArr (fo22N4_facts.inv 1 (by norm_num))).1) hb

end N4

section H2

@[expose] def fo22P2Datum : RawSchreierDatum 27 :=
  fo22Datum 27 (by decide) fo22P2Strong 3 (fi22FinList 27 (by decide) [0, 1, 2, 3, 5, 7])
    (by decide) fo22P2Words

theorem fo22P2_facts :
    ChainFacts 27 fo22P2Datum fo22P2Strong #[0, 1, 2, 3, 5, 7] 3 11 51840 :=
  chainFacts_of_ok rfl (by norm_num) fo22P2Chain_ok

@[expose] def fo22T2 : Array (Array ℕ) :=
  treeConjN 3510 3 ((fi22CentStrong 2).extract 0 3) fo22S02 fo22Tree2

theorem fo22T2_facts : fo22T2.size = 27 ∧
    (∀ j < 27, isInvA 3510 fo22T2[j]! (invCand 3510 fo22T2[j]!) = true ∧
      siftA 3510 (rawLevels 3510 (fi22CentStrong 2) fo22HBase) fo22HBase 0 fo22T2[j]! = true ∧
      ∀ i < 3, (fo22P2Strong[i]!)[j]! < 27 ∧
        eqA 3510 (conjA 3510 ((fi22CentStrong 2).extract 0 3)[i]! fo22T2[j]!)
          fo22T2[(fo22P2Strong[i]!)[j]!]! = true) ∧
    (∀ j < 27, ∀ k < 27, j = k ∨ eqA 3510 fo22T2[j]! fo22T2[k]! = false) ∧
    (∀ j < 27, ∀ k < 27,
      eqA 3510 (compA 3510 fo22T2[j]! fo22T2[k]!) (compA 3510 fo22T2[k]! fo22T2[j]!) = true) := by
  have h := fo22H2_ok
  unfold fo22H2OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun j hj => ?_, fun j hj k hk => ?_,
    fun j hj k hk => allLt_spec (allLt_spec h4 hj) hk⟩
  · have := allLt_spec h2 hj
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1.1, this.1.2, fun i hi => ?_⟩
    have := allLt_spec this.2 hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩
  · have := allLt_spec (allLt_spec h3 hj) hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    exact this

@[expose] def fo22T2j (j : Fin 27) : Equiv.Perm (Fin 3510) := permOfArr 3510 fo22T2[j.1]!

theorem rep_fo22T2j
    (j : Fin 27) : Rep 3510 fo22T2[j.1]! (fo22T2j j) :=
  (rep_permOfArr (fo22T2_facts.2.1 j j.2).1).1

@[expose] def fo22H2gen (i : Fin 3) : Equiv.Perm (Fin 3510) := fi22CentPerm (35 + i.1)

theorem fi22H_two_eq :
    fi22H 2 = Subgroup.closure (Set.range fo22H2gen) := by
  rw [fi22H_eq_closure (c := 2) (by norm_num)]
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩

theorem fo22H2_selfCentralizing :
    ∃ N : Subgroup (fi22H 2), N.Normal ∧ Nat.card N = 64 ∧
    Subgroup.centralizer (N : Set (fi22H 2)) ≤ N := by
  have hinj : Function.Injective fo22T2j := by
    intro j k h
    rcases fo22T2_facts.2.2.1 j j.2 k k.2 with h' | h'
    · exact Fin.ext h'
    · rw [(eqA_iff (rep_fo22T2j j) (rep_fo22T2j k)).2 h] at h'
      exact Bool.noConfusion h'
  have hmem : ∀ j, fo22T2j j ∈ fi22H 2 := fun j =>
    (siftA_iff_mem_fi22H (by norm_num) (rep_fo22T2j j)).1 (fo22T2_facts.2.1 j j.2).2.1
  have hcomm : ∀ j k, fo22T2j j * fo22T2j k = fo22T2j k * fo22T2j j := fun j k =>
    eq_of_eqA (rep_compA (rep_fo22T2j j) (rep_fo22T2j k))
      (rep_compA (rep_fo22T2j k) (rep_fo22T2j j)) (fo22T2_facts.2.2.2 j j.2 k k.2)
  have hπ : ∀ i j, fo22H2gen i * fo22T2j j * (fo22H2gen i)⁻¹ =
      fo22T2j (permOfArr 27 fo22P2Strong[i.1]! j) := by
    intro i j
    have hrP := (rep_permOfArr (fo22P2_facts.inv i.1 (by omega))).1
    have hL : fi22CentStrongStart.getD 2 0 + i.1 < 306 := by
      show 35 + i.1 < 306
      omega
    obtain ⟨-, hc⟩ := (fo22T2_facts.2.1 j j.2).2.2 i.1 i.2
    have hg := fo22_hgens (c := 2) (by norm_num) (j := i.1) i.2
    have hg' : ((fi22CentStrong 2).extract 0 3)[i.1]! =
        fi22CentArr (fi22CentStrongStart.getD 2 0 + i.1) := hg
    rw [hg'] at hc
    have h1 := rep_conj_fi22CentArr hL (rep_fo22T2j j)
    have e : fo22T2[(fo22P2Strong[i.1]!)[j.1]!]! =
        fo22T2[(permOfArr 27 fo22P2Strong[i.1]! j).1]! := by
      rw [hrP j]
    have h2 := rep_fo22T2j (permOfArr 27 fo22P2Strong[i.1]! j)
    rw [← e] at h2
    exact eq_of_eqA h1 h2 hc
  have hP : fo22P2Datum.originalSubgroup =
      Subgroup.closure (Set.range fun i : Fin 3 => permOfArr 27 fo22P2Strong[i.1]!) := by
    rw [fo22P2_facts.eq_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
  obtain ⟨N, hN, hcard, hc⟩ := exists_selfCentralizing_of_conjCert fi22H_two_eq hinj hmem hcomm
    (fun i => permOfArr 27 fo22P2Strong[i.1]!) hπ hP
  refine ⟨N, hN, ?_, hc⟩
  rw [fo22P2_facts.card, card_fi22H (c := 2) (by norm_num)] at hcard
  have hc' : Nat.card N * 51840 = 3317760 := hcard
  omega

theorem fo22H2_no_component
    (B : Subgroup (fi22H 2)) : ¬ IsComponent B := by
  obtain ⟨N, hN, hcard, hc⟩ := fo22H2_selfCentralizing
  exact no_component_of_selfCentralizing hN
    (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hc B

end H2

section Components

theorem isSolvable_of_card_six {G : Type*} [Group G] [Finite G] (h : Nat.card G = 6) :
    Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  decide

theorem isSolvable_of_card_two {G : Type*} [Group G] [Finite G] (h : Nat.card G = 2) :
    Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, Nat.Prime.primeFactors Nat.prime_two]
  decide

theorem fo22H3_component
    {B : Subgroup (fi22H 3)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 174182400 := by
  have := fo22N3_normal
  have hs : IsSimpleGroup fo22N3 := isSimpleGroup_fo22N3
  have e := Subgroup.subgroupOfEquivOfLe fo22N3_le
  have hs' : IsSimpleGroup (fo22N3.subgroupOf (fi22H 3)) := e.isSimpleGroup
  have hcardN : Nat.card (fo22N3.subgroupOf (fi22H 3)) = 174182400 := by
    rw [Nat.card_congr e.toEquiv, card_fo22N3]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (fo22N3.subgroupOf (fi22H 3))
  rw [card_fi22H (c := 3) (by norm_num), hcardN] at hq
  have hq6 : Nat.card ((fi22H 3) ⧸ fo22N3.subgroupOf (fi22H 3)) = 6 := by
    have hq' : 1045094400 = Nat.card ((fi22H 3) ⧸ fo22N3.subgroupOf (fi22H 3)) * 174182400 :=
      hq
    omega
  have hnc := exists_noncomm_of_isSimpleGroup hs' (by rw [hcardN]; norm_num)
  rw [card_quotient_center_of_component_of_normal_simple (isSolvable_of_card_six hq6) hs' hnc hB,
    hcardN]

theorem fo22H4_component
    {B : Subgroup (fi22H 4)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 1451520 := by
  have := fo22N4_normal
  have hs : IsSimpleGroup fo22N4 := isSimpleGroup_fo22N4
  have e := Subgroup.subgroupOfEquivOfLe fo22N4_le
  have hs' : IsSimpleGroup (fo22N4.subgroupOf (fi22H 4)) := e.isSimpleGroup
  have hcardN : Nat.card (fo22N4.subgroupOf (fi22H 4)) = 1451520 := by
    rw [Nat.card_congr e.toEquiv, fo22N4, fo22N4_facts.card]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (fo22N4.subgroupOf (fi22H 4))
  rw [card_fi22H (c := 4) (by norm_num), hcardN] at hq
  have hq2 : Nat.card ((fi22H 4) ⧸ fo22N4.subgroupOf (fi22H 4)) = 2 := by
    have hq' : 2903040 = Nat.card ((fi22H 4) ⧸ fo22N4.subgroupOf (fi22H 4)) * 1451520 := hq
    omega
  have hnc := exists_noncomm_of_isSimpleGroup hs' (by rw [hcardN]; norm_num)
  rw [card_quotient_center_of_component_of_normal_simple (isSolvable_of_card_two hq2) hs' hnc hB,
    hcardN]

end Components

section Outer

@[expose] def fixSubRAutEquiv
    (r : fi22R) :
    fixSub (fi22RAut r) ≃* ↥(fi22P ⊓ Subgroup.centralizer {(r : Equiv.Perm (Fin 3510))}) where
  toFun g := ⟨((g : fi22P) : Equiv.Perm (Fin 3510)), (g : fi22P).2, by
    show _ ∈ Subgroup.centralizer {(r : Equiv.Perm (Fin 3510))}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : ((fi22ConjHom r (g : fi22P) : fi22P) : Equiv.Perm (Fin 3510)) = g :=
      congrArg Subtype.val g.2
    rw [fi22ConjHom_apply] at h2
    calc ((g : fi22P) : Equiv.Perm (Fin 3510)) * r =
        (r : Equiv.Perm (Fin 3510)) * g * (r : Equiv.Perm (Fin 3510))⁻¹ * r := by rw [h2]
      _ = r * g := by group⟩
  invFun x := ⟨⟨x, x.2.1⟩, by
    show fi22RAut r ⟨x, x.2.1⟩ = ⟨x, x.2.1⟩
    apply Subtype.ext
    rw [fi22RAut_apply, fi22ConjHom_apply]
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    show (r : Equiv.Perm (Fin 3510)) * x * (r : Equiv.Perm (Fin 3510))⁻¹ = x
    rw [← hx]
    group⟩
  left_inv g := rfl
  right_inv x := rfl
  map_mul' x y := rfl

theorem fi22P_outer_components
    (r : fi22R) (hr2 : r * r = 1)
    (hrP : (r : Equiv.Perm (Fin 3510)) ∉ fi22P)
    {B : Subgroup ↥(fi22P ⊓ Subgroup.centralizer {(r : Equiv.Perm (Fin 3510))})}
    (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 174182400 ∨ Nat.card (B ⧸ Subgroup.center B) = 1451520 := by
  set τ := (r : Equiv.Perm (Fin 3510))
  have hτ1 : τ ≠ 1 := fun h => hrP (h ▸ fi22P.one_mem)
  have hτ2 : τ * τ = 1 := congrArg Subtype.val hr2
  have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  obtain ⟨k, hk, c, hc, hck⟩ := fi22R_involution_conj r.2 hτo
  have hcn := fi22R_le_normalizer hc
  have hk3 : 3 ≤ k := by
    by_contra h
    apply hrP
    have hkP : fi22ExtRep k ∈ fi22P := CTUC_Fi22_all_extension_involutions_covered.1 k (by omega)
    rw [← hck] at hkP
    exact (Subgroup.mem_normalizer_iff.1 hcn τ).2 hkP
  have e1 := (fi22CP_conj_equiv hcn τ).trans (MulEquiv.subgroupCongr (by rw [hck]))
  obtain ⟨hB1, hc1⟩ := component_quotient_mulEquiv e1 hB
  rw [hc1]
  obtain ⟨-, -, h3, h4, h5, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · exfalso
    obtain ⟨hB2, -⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h3) hB1
    exact fo22H2_no_component _ hB2
  · left
    obtain ⟨hB2, hc2⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h4) hB1
    rw [hc2]
    exact fo22H3_component hB2
  · right
    obtain ⟨hB2, hc2⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h5) hB1
    rw [hc2]
    exact fo22H4_component hB2

end Outer

theorem fi22P_mulAut_outer_components
    (β : MulAut fi22P) (hβ2 : β * β = 1)
    (hβn : β ∉ inner fi22P) {B : Subgroup (fixSub β)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 174182400 ∨ Nat.card (B ⧸ Subgroup.center B) = 1451520 := by
  obtain ⟨r, rfl⟩ := fi22RAut.surjective β
  have hr2 : r * r = 1 := fi22RAut.injective (by rw [map_mul, hβ2, map_one])
  have hrP : (r : Equiv.Perm (Fin 3510)) ∉ fi22P := by
    intro h
    apply hβn
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, ← fi22RAut_inn]
    exact ⟨r, Subgroup.mem_subgroupOf.2 h, rfl⟩
  obtain ⟨hB2, hc2⟩ := component_quotient_mulEquiv (fixSubRAutEquiv r) hB
  rw [hc2]
  exact fi22P_outer_components r hr2 hrP hB2

open CFSG.ComponentClassification.RestrictedStd.Spor in
theorem fi22OuterComponentsInput_holds :
    Fi22OuterComponentsInput := by
  intro G _ ⟨e⟩ α hα2 hαn B hB
  set θ : G ≃* fi22P := e.trans fi22PermEquiv
  obtain ⟨hB1, hc1⟩ := component_quotient_mulEquiv (fixSubCongr θ α) hB
  rw [hc1]
  exact fi22P_mulAut_outer_components _ (congr_mul_self θ α hα2)
    (fun h => hαn ((congr_mem_inner_iff θ α).1 h)) hB1

end CFSG.Sporadic.FischerOddCore
