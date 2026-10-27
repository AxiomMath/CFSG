module

public import CFSG.RankThree.Native.FiveKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {n : ℕ}

@[expose] def powPA (p n : ℕ) (x : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := p) fun e => powArr n x e

theorem rep_powPA {p : ℕ} {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) :
    ∀ e < (powPA p n x).size, Rep n (powPA p n x)[e]! (X ^ e) := by
  intro e he
  rw [getElem!_pos _ e he]
  simp only [powPA, Array.getElem_ofFn]
  exact rep_powArr hx e

@[expose] def relsOKP (p n : ℕ) (base x : Array ℕ) (rels : List (ℕ × ℕ × ℕ)) : Bool :=
  rels.all fun r => decide (r.2.2 < p) && decide (r.1 < base.size) &&
    decide (r.2.1 < base.size) && (powArr n x r.2.2)[base[r.1]!]! == base[r.2.1]!

theorem relsOKP_spec {p : ℕ} {base x : Array ℕ} {rels : List (ℕ × ℕ × ℕ)}
    (h : relsOKP p n base x rels = true) :
    ∀ r ∈ rels, r.2.2 < (powPA p n x).size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      ((powPA p n x)[r.2.2]!)[base[r.1]!]! = base[r.2.1]! := by
  intro r hr
  have h' := List.all_eq_true.1 h r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  refine ⟨by simpa [powPA] using h1, h2, h3, ?_⟩
  rw [getElem!_pos (powPA p n x) r.2.2 (by simpa [powPA] using h1)]
  simpa [powPA] using h4

@[expose] def caseChainOK3 (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ))
    (a b u : Array ℕ) : Bool :=
  rawChainOK n (S.extract 0 3) S base W 1 && eqA n S[0]! a && eqA n S[1]! b && eqA n S[2]! u

@[expose] def caseChainOK2P (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ))
    (a b : Array ℕ) : Bool :=
  rawChainOK n (S.extract 0 2) S base W 1 && eqA n S[0]! a && eqA n S[1]! b

theorem caseChainOK3_parts {S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    {a b u : Array ℕ} (h : caseChainOK3 n S base W a b u = true) :
    rawChainOK n (S.extract 0 3) S base W 1 = true ∧ eqA n S[0]! a = true ∧
      eqA n S[1]! b = true ∧ eqA n S[2]! u = true := by
  simp only [caseChainOK3, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem caseChainOK2P_parts {S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    {a b : Array ℕ} (h : caseChainOK2P n S base W a b = true) :
    rawChainOK n (S.extract 0 2) S base W 1 = true ∧ eqA n S[0]! a = true ∧
      eqA n S[1]! b = true := by
  simp only [caseChainOK2P, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem originalSubgroup_ofArrays_twoP {S : Array (Array ℕ)} {hn : 1 ≤ n} {hk : 2 ≤ S.size}
    {bs : List (Fin n)} {hb : bs.Nodup} {W' : Array (List ℤ)}
    (hc : rawChainOK n (S.extract 0 2) S (bs.map Fin.val).toArray W' 1 = true)
    {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (e0 : eqA n S[0]! a = true) (e1 : eqA n S[1]! b = true) :
    (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W').originalSubgroup =
      Subgroup.closure {A, B} := by
  have hinv := (chainCheckFacts hc).strong_inv
  have hrep : ∀ j < S.size, Rep n S[j]! (permOfArr n S[j]!) := fun j hj =>
    (rep_permOfArr (hinv j hj)).1
  have g0 : permOfArr n S[0]! = A := eq_of_eqA (hrep 0 (by omega)) ha e0
  have g1 : permOfArr n S[1]! = B := eq_of_eqA (hrep 1 (by omega)) hb' e1
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl g0
    · exact Or.inr g1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, g0⟩
    · exact ⟨1, by norm_num, g1⟩

theorem mem_closure_two_of_siftG {S : Array (Array ℕ)} {bs : List (Fin n)}
    {W : Array (List ℤ)} {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (hn : 1 ≤ n)
    (hk : 2 ≤ S.size) (hb : bs.Nodup) (ha : Rep n a A) (hb' : Rep n b B)
    (hchain : caseChainOK2P n S (bs.map Fin.val).toArray W a b = true) {g : Array ℕ}
    {G : Equiv.Perm (Fin n)} (hG : Rep n g G)
    (hs : siftA n (rawLevels n S (bs.map Fin.val).toArray) (bs.map Fin.val).toArray 0 g = true) :
    G ∈ Subgroup.closure {A, B} := by
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  rw [← originalSubgroup_ofArrays_twoP (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1]
  exact mem_of_siftA hA hc hG hs

theorem mem_closure_three_of_siftG {S : Array (Array ℕ)} {bs : List (Fin n)}
    {W : Array (List ℤ)} {a b u : Array ℕ} {A B U : Equiv.Perm (Fin n)} (hn : 1 ≤ n)
    (hk : 3 ≤ S.size) (hb : bs.Nodup) (ha : Rep n a A) (hb' : Rep n b B) (hu : Rep n u U)
    (hchain : caseChainOK3 n S (bs.map Fin.val).toArray W a b u = true) {g : Array ℕ}
    {G : Equiv.Perm (Fin n)} (hG : Rep n g G)
    (hs : siftA n (rawLevels n S (bs.map Fin.val).toArray) (bs.map Fin.val).toArray 0 g = true) :
    G ∈ Subgroup.closure {A, B, U} := by
  obtain ⟨hc, e0, e1, e2⟩ := caseChainOK3_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 3 hk bs hb W) (S.extract 0 3) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  rw [← originalSubgroup_ofArrays_three (hn := hn) (hk := hk) (hb := hb) hc ha hb' hu e0 e1 e2]
  exact mem_of_siftA hA hc hG hs

theorem card_closure_two_of_chainOK {S : Array (Array ℕ)} {bs : List (Fin n)}
    {W : Array (List ℤ)} {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (hn : 1 ≤ n)
    (hk : 2 ≤ S.size) (hb : bs.Nodup) (ha : Rep n a A) (hb' : Rep n b B)
    (hchain : caseChainOK2P n S (bs.map Fin.val).toArray W a b = true) :
    Nat.card (Subgroup.closure {A, B}) = (rawOrbitSizes n S (bs.map Fin.val).toArray).prod := by
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  rw [← originalSubgroup_ofArrays_twoP (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1]
  exact card_originalSubgroup_of_chainOK hA (by norm_num) hc

theorem card_closure_three_of_chainOK {S : Array (Array ℕ)} {bs : List (Fin n)}
    {W : Array (List ℤ)} {a b u : Array ℕ} {A B U : Equiv.Perm (Fin n)} (hn : 1 ≤ n)
    (hk : 3 ≤ S.size) (hb : bs.Nodup) (ha : Rep n a A) (hb' : Rep n b B) (hu : Rep n u U)
    (hchain : caseChainOK3 n S (bs.map Fin.val).toArray W a b u = true) :
    Nat.card (Subgroup.closure {A, B, U}) =
      (rawOrbitSizes n S (bs.map Fin.val).toArray).prod := by
  obtain ⟨hc, e0, e1, e2⟩ := caseChainOK3_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 3 hk bs hb W) (S.extract 0 3) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  rw [← originalSubgroup_ofArrays_three (hn := hn) (hk := hk) (hb := hb) hc ha hb' hu e0 e1 e2]
  exact card_originalSubgroup_of_chainOK hA (by norm_num) hc

theorem closure_le_of_siftG {gs : Array (Array ℕ)} {PL : Array Level} {Pb : Array ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))} (hval : ∀ l < gs.size, validA n gs[l]! = true)
    (hsift : allLt gs.size (fun l => siftA n PL Pb 0 gs[l]!) = true)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P) :
    Subgroup.closure (permsA n gs) ≤ P := by
  rw [closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact hmemP (rep_of_validA (hval l hl)) (allLt_spec hsift hl)

theorem centralizer_eq_of_ptailOKP {p : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W 1 = true) {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)} (hrels : relsOKP p n base x rels = true)
    {gs : Array (Array ℕ)} {ps : List ℕ} {cC : ArrCert} (hps : ∀ q ∈ ps, q < n)
    (hC : enumOK n gs ps cC = true) (hcomm : allLt gs.size (fun k => commA n gs[k]! x) = true)
    (hsift : allLt gs.size (fun k => siftA n (rawLevels n S base) base 0 gs[k]!) = true)
    (htail : ptailOK n (rawLevels n S base) base x (powPA p n x) rels cC.pts.toList base.size 0
      (idA n) = true) :
    Subgroup.closure (permsA n gs) = Subgroup.centralizer {X} ⊓ Q.originalSubgroup := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hC hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 (allLt_spec hcomm hk)
    · exact mem_of_siftA hA hc hrep (allLt_spec hsift hk)
  · intro g hg
    have htail' : ptailOK n (rawLevels n S base) base x (powPA p n x) rels cC.pts.toList
        Q.baseCount 0 (idA n) = true := by
      rw [← hA.base_size]
      exact htail
    obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK hA (chainCheckFacts hc)
      (validSchreier_of_chainOK hA (by norm_num) hc).1 hx (rep_powPA hx) (relsOKP_spec hrels)
      htail' hg
    exact enumOK_mem_of_mem hps hC hre he

@[expose] def centOKP (p n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) (N : ℕ) : Bool :=
  relsOKP p n base x rels && enumOK n gs ps c && c.pts.size == N &&
    allLt gs.size (fun k => commA n gs[k]! x) &&
    allLt gs.size (fun k => siftA n (rawLevels n S base) base 0 gs[k]!) &&
    ptailOK n (rawLevels n S base) base x (powPA p n x) rels c.pts.toList base.size 0 (idA n)

theorem centOKP_enum {p N : ℕ} {S : Array (Array ℕ)} {base x : Array ℕ}
    {rels : List (ℕ × ℕ × ℕ)} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (h : centOKP p n S base x rels gs ps c N = true) : enumOK n gs ps c = true := by
  simp only [centOKP, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem case_centralizerP {p : ℕ} {S : Array (Array ℕ)} (hn : 1 ≤ n) (hk : 3 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)} {a b u : Array ℕ}
    {A B U : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B) (hu : Rep n u U)
    (hchain : caseChainOK3 n S (bs.map Fin.val).toArray W a b u = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N : ℕ} (hps : ∀ q ∈ ps, q < n)
    (hcent : centOKP p n S (bs.map Fin.val).toArray x rels gs ps c N = true) :
    closure (permsA n gs) = centralizer {X} ⊓ closure {A, B, U} ∧
      Nat.card (closure (permsA n gs)) = N := by
  obtain ⟨hc, e0, e1, e2⟩ := caseChainOK3_parts hchain
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 3 hk bs hb W) (S.extract 0 3) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have horig := originalSubgroup_ofArrays_three (hn := hn) (hk := hk) (hb := hb) hc ha hb' hu e0
    e1 e2
  refine ⟨?_, (enumOK_spec hps hC).2.1.trans hsize⟩
  rw [← horig]
  exact centralizer_eq_of_ptailOKP hA hc hx hrels hps hC hcomm hsift htail

theorem case_centralizer2P {p : ℕ} {S : Array (Array ℕ)} (hn : 1 ≤ n) (hk : 2 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)} {a b : Array ℕ}
    {A B : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (hchain : caseChainOK2P n S (bs.map Fin.val).toArray W a b = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N : ℕ} (hps : ∀ q ∈ ps, q < n)
    (hcent : centOKP p n S (bs.map Fin.val).toArray x rels gs ps c N = true) :
    closure (permsA n gs) = centralizer {X} ⊓ closure {A, B} ∧
      Nat.card (closure (permsA n gs)) = N := by
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hchain
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have horig := originalSubgroup_ofArrays_twoP (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1
  refine ⟨?_, (enumOK_spec hps hC).2.1.trans hsize⟩
  rw [← horig]
  exact centralizer_eq_of_ptailOKP hA hc hx hrels hps hC hcomm hsift htail

section Normal

variable {p N : ℕ} {gC gA : Array (Array ℕ)} {ps : List ℕ} {cC cA : ArrCert}

@[expose] def normalOKP (p n : ℕ) (gC gA : Array (Array ℕ)) (ps : List ℕ) (cC cA : ArrCert)
    (N : ℕ) (PL : Array Level) (Pb : Array ℕ) : Bool :=
  enumOK n gA ps cA && cA.pts.size == N &&
    allLt cA.pts.size (fun k => eqA n (powArr n cA.pts[k]! p) (idA n)) &&
    allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) &&
    allLt gC.size (fun k => allLt gA.size fun l =>
      cA.pts.toList.any (eqA n (conjA n gC[k]! gA[l]!))) &&
    allLt gA.size (fun l => siftA n PL Pb 0 gA[l]!)

@[expose] def selfCentOKG (n : ℕ) (gA : Array (Array ℕ)) (cC cA : ArrCert) : Bool :=
  allLt gA.size (fun l => allLt gA.size fun l' => commA n gA[l]! gA[l']!) &&
    allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      cA.pts.toList.any (eqA n cC.pts[k]!))

@[expose] def zCentOKP (p n : ℕ) (gA : Array (Array ℕ)) (cC cA : ArrCert) (x : Array ℕ) :
    Bool :=
  cA.pts.toList.any (eqA n x) &&
    allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      (List.range p).any fun e => eqA n cC.pts[k]! (powArr n x e))

theorem normalOKP_parts {PL : Array Level} {Pb : Array ℕ}
    (h : normalOKP p n gC gA ps cC cA N PL Pb = true) :
    enumOK n gA ps cA = true ∧ cA.pts.size = N ∧
    allLt cA.pts.size (fun k => eqA n (powArr n cA.pts[k]! p) (idA n)) = true ∧
    allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) = true ∧
    allLt gC.size (fun k => allLt gA.size fun l =>
      cA.pts.toList.any (eqA n (conjA n gC[k]! gA[l]!))) = true ∧
    allLt gA.size (fun l => siftA n PL Pb 0 gA[l]!) = true := by
  simp only [normalOKP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hAe, hsize⟩, hpow⟩, hmem⟩, hnorm⟩, hsift⟩ := h
  exact ⟨hAe, hsize, hpow, hmem, hnorm, hsift⟩

theorem pow_p_of_enum (hps : ∀ q ∈ ps, q < n) (hAe : enumOK n gA ps cA = true)
    (hpow : allLt cA.pts.size (fun k => eqA n (powArr n cA.pts[k]! p) (idA n)) = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.closure (permsA n gA)) : g ^ p = 1 := by
  obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hAe hg
  exact (eqA_iff (rep_powArr hkg p) rep_idA).1 (allLt_spec hpow hk)

theorem mem_of_gen_zeroG {gs : Array (Array ℕ)} {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) (h0 : 0 < gs.size) (hv : validA n gs[0]! = true)
    (he : eqA n gs[0]! x = true) : X ∈ closure (permsA n gs) := by
  rw [← eq_of_eqA (rep_of_validA hv) hx he]
  exact subset_closure (mem_permsA h0)

theorem normal_p (hp : p.Prime) {PL : Array Level} {Pb : Array ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))} (hps : ∀ q ∈ ps, q < n)
    (hC : enumOK n gC ps cC = true) (h : normalOKP p n gC gA ps cC cA N PL Pb = true)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P) (hN : 1 < N) :
    enumOK n gA ps cA = true ∧
    allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) = true ∧
    closure (permsA n gA) ≤ closure (permsA n gC) ∧
      ((closure (permsA n gA)).subgroupOf (closure (permsA n gC))).Normal ∧
      closure (permsA n gA) ≤ P ∧ Nat.card (closure (permsA n gA)) = N ∧
      Monoid.exponent (closure (permsA n gA)) = p := by
  obtain ⟨hAe, hsize, hpow, hmem, hnorm, hsift⟩ := normalOKP_parts h
  have hcard : Nat.card (closure (permsA n gA)) = N := (enumOK_spec hps hAe).2.1.trans hsize
  refine ⟨hAe, hmem, le_of_gens_mem hps hC hAe hmem, normal_kit hps hC hAe hmem hnorm,
    closure_le_of_siftG (fun l hl => enumOK_gens_valid hAe hl) hsift hmemP, hcard, ?_⟩
  have hdvd : Monoid.exponent (closure (permsA n gA)) ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      Subtype.ext (pow_p_of_enum hps hAe hpow g.2)
  rcases (Nat.dvd_prime hp).1 hdvd with he | he
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 he
    have : Nat.card (closure (permsA n gA)) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hs
    omega
  · exact he

theorem centralizer_eq_zpowers_kitP (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hAe : enumOK n gA ps cA = true) {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    (hXC : X ∈ Subgroup.closure (permsA n gC))
    (hXA : X ∈ Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))))
    (hcent : allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      (List.range p).any fun e => eqA n cC.pts[k]! (powArr n x e)) = true) :
    Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓
      Subgroup.closure (permsA n gC) = Subgroup.zpowers X := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hC hgC
    have hc : (allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) = true := by
      refine allLt_iff.2 fun l hl => ?_
      exact (commA_iff hkg (rep_of_validA (enumOK_gens_valid hAe hl))).2
        ((mem_centralizer_closure_iff.1 hgA l hl).symm)
    have h := allLt_spec hcent hk
    rw [hc] at h
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range] at h
    obtain ⟨e, -, he⟩ := h
    rw [(eqA_iff hkg (rep_powArr hx e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hXA, hXC⟩

end Normal

section Derived

variable {p M : ℕ} {gC gD : Array (Array ℕ)} {ps : List ℕ} {cC cD : ArrCert}

@[expose] def derivedOKP (p M n : ℕ) (gC gD : Array (Array ℕ)) (ps : List ℕ) (cC cD : ArrCert)
    (c d x : Array ℕ) (PL : Array Level) (Pb : Array ℕ) : Bool :=
  enumOK n gD ps cD && cD.pts.size == M && validA n c && validA n d &&
    cC.pts.toList.any (eqA n c) && cC.pts.toList.any (eqA n d) &&
    eqA n gC[2]! (commutatorA n c d) &&
    allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) &&
    allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!))) &&
    !(commA n gD[0]! gD[1]!) && conjSimpleOK n ps cD &&
    allLt cC.pts.size (fun k => !(allLt gD.size fun l => commA n cC.pts[k]! gD[l]!) ||
      (List.range p).any fun e => eqA n cC.pts[k]! (powArr n x e)) &&
    allLt gD.size (fun l => siftA n PL Pb 0 gD[l]!)

theorem derivedOKP_parts {c d x : Array ℕ} {PL : Array Level} {Pb : Array ℕ}
    (h : derivedOKP p M n gC gD ps cC cD c d x PL Pb = true) :
    enumOK n gD ps cD = true ∧ cD.pts.size = M ∧ validA n c = true ∧ validA n d = true ∧
    cC.pts.toList.any (eqA n c) = true ∧ cC.pts.toList.any (eqA n d) = true ∧
    eqA n gC[2]! (commutatorA n c d) = true ∧
    allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) = true ∧
    allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!))) = true ∧
    commA n gD[0]! gD[1]! = false ∧ conjSimpleOK n ps cD = true ∧
    allLt cC.pts.size (fun k => !(allLt gD.size fun l => commA n cC.pts[k]! gD[l]!) ||
      (List.range p).any fun e => eqA n cC.pts[k]! (powArr n x e)) = true ∧
    allLt gD.size (fun l => siftA n PL Pb 0 gD[l]!) = true := by
  simp only [derivedOKP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDe, hDs⟩, hcv⟩, hdv⟩, hcm⟩, hdm⟩, hb⟩, hnorm⟩, hcomm⟩, hnab⟩,
    hsimple⟩, hcent⟩, hsift⟩ := h
  exact ⟨hDe, hDs, hcv, hdv, hcm, hdm, hb, hnorm, hcomm, hnab, hsimple, hcent, hsift⟩

theorem recordD_eq_commutator {c d x : Array ℕ} {PL : Array Level} {Pb : Array ℕ}
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hD : derivedOKP p M n gC gD ps cC cD c d x PL Pb = true)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) (h3 : 3 ≤ gC.size) :
    ⁅closure (permsA n gC), closure (permsA n gC)⁆ = closure (permsA n gD) := by
  obtain ⟨hDe, -, hcv, hdv, hcm, hdm, hb, hnorm, hcomm, -⟩ := derivedOKP_parts hD
  exact derived_kit hps hC hDe h3 hgD hcv hdv hcm hdm hb hnorm hcomm

end Derived

@[expose] def transOKG (r n : ℕ) (H L : Array (Array ℕ)) (rec : List ℕ) (RL : Array Level)
    (Rb : Array ℕ) : Bool :=
  allLt r fun j => validA n H[j]! && siftA n RL Rb 0 H[j]! &&
    eqA n (conjA n H[j]! L[rec.getD j 0 % r]!) L[j]!

theorem trans_spec {r : ℕ} {H L : Array (Array ℕ)} {rec : List ℕ} {RL : Array Level}
    {Rb : Array ℕ} {R' : Subgroup (Equiv.Perm (Fin n))}
    (hmemR : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n RL Rb 0 g = true →
      G ∈ R')
    (hL : ∀ i < r, validA n L[i]! = true) (h : transOKG r n H L rec RL Rb = true) {j : ℕ}
    (hj : j < r) :
    permOfArr n H[j]! ∈ R' ∧
      permOfArr n H[j]! * permOfArr n L[rec.getD j 0 % r]! * (permOfArr n H[j]!)⁻¹ =
        permOfArr n L[j]! := by
  have h' := allLt_spec h hj
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨hv, hs⟩, he⟩ := h'
  have hlt : rec.getD j 0 % r < r := Nat.mod_lt _ (by omega)
  exact ⟨hmemR (rep_of_validA hv) hs,
    eq_of_eqA (rep_conjA hv (rep_of_validA (hL _ hlt))) (rep_of_validA (hL j hj)) he⟩

theorem rec_mod_memG {r : ℕ} {rec cs : List ℕ}
    (h : allLt r (fun j => cs.any fun i => rec.getD j 0 == i) = true)
    (hcs : ∀ i ∈ cs, i < r) {j : ℕ} (hj : j < r) : rec.getD j 0 % r ∈ cs := by
  have h' := allLt_spec h hj
  simp only [List.any_eq_true, beq_iff_eq] at h'
  obtain ⟨i, hi, hji⟩ := h'
  rw [hji, Nat.mod_eq_of_lt (hcs i hi)]
  exact hi

section Spec

variable {p N M : ℕ} {PL : Array Level} {Pb : Array ℕ} {P R' : Subgroup (Equiv.Perm (Fin n))}
  {gC gA gD : Array (Array ℕ)} {ps : List ℕ} {cC cA cD : ArrCert}

theorem recordA_spec_zcent (hp : p.Prime) {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hCx : closure (permsA n gC) = centralizer {X} ⊓ R')
    (hN : normalOKP p n gC gA ps cC cA N PL Pb = true)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P)
    (hN1 : 1 < N) (hx : Rep n x X) (h0 : 0 < gC.size) (hxz : eqA n gC[0]! x = true)
    (hz : zCentOKP p n gA cC cA x = true) (hord : orderOf X = p) :
    closure (permsA n gA) ≤ closure (permsA n gC) ∧
      ((closure (permsA n gA)).subgroupOf (closure (permsA n gC))).Normal ∧
      closure (permsA n gA) ≤ P ∧ Nat.card (closure (permsA n gA)) = N ∧
      Monoid.exponent (closure (permsA n gA)) = p ∧
      Nat.card (centralizer (closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓
        closure (permsA n gC) : Subgroup (Equiv.Perm (Fin n))) = p ∧
      centralizer (closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) ≤
        closure (permsA n gA) := by
  obtain ⟨hAe, -, hle, hnorm, hP, hcard, hexp⟩ := normal_p hp hps hC hN hmemP hN1
  have hz' := hz
  simp only [zCentOKP, Bool.and_eq_true] at hz'
  have hxC : X ∈ closure (permsA n gC) := mem_of_gen_zeroG hx h0 (enumOK_gens_valid hC h0) hxz
  have hxA : X ∈ closure (permsA n gA) := enumOK_mem_of_any hps hAe hx hz'.1
  have hxcent : X ∈ centralizer (closure (permsA n gA) : Set (Equiv.Perm (Fin n))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have : a ∈ centralizer {X} ⊓ R' := hCx ▸ hle ha
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcent : centralizer (closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓
      closure (permsA n gC) = zpowers X :=
    centralizer_eq_zpowers_kitP hps hC hAe hx hxC hxcent hz'.2
  refine ⟨hle, hnorm, hP, hcard, hexp, ?_, ?_⟩
  · rw [hcent, Nat.card_zpowers]
    exact hord
  · rw [hcent, zpowers_le]
    exact hxA

theorem recordA_self_centralizer (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hN : normalOKP p n gC gA ps cC cA N PL Pb = true) (hS : selfCentOKG n gA cC cA = true) :
    centralizer (closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) =
      closure (permsA n gA) := by
  obtain ⟨hAe, -, -, hmem, -⟩ := normalOKP_parts hN
  simp only [selfCentOKG, Bool.and_eq_true] at hS
  exact centralizer_eq_self_kit hps hC hAe hmem hS.1 hS.2

theorem recordA_spec_self (hp : p.Prime) (hps : ∀ q ∈ ps, q < n)
    (hC : enumOK n gC ps cC = true) (hN : normalOKP p n gC gA ps cC cA N PL Pb = true)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P)
    (hN1 : 1 < N) (hS : selfCentOKG n gA cC cA = true) :
    closure (permsA n gA) ≤ closure (permsA n gC) ∧
      ((closure (permsA n gA)).subgroupOf (closure (permsA n gC))).Normal ∧
      closure (permsA n gA) ≤ P ∧ Nat.card (closure (permsA n gA)) = N ∧
      Monoid.exponent (closure (permsA n gA)) = p ∧
      centralizer (closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) ≤
        closure (permsA n gA) := by
  obtain ⟨-, -, hle, hnorm, hP, hcard, hexp⟩ := normal_p hp hps hC hN hmemP hN1
  exact ⟨hle, hnorm, hP, hcard, hexp, (recordA_self_centralizer hps hC hN hS).le⟩

theorem recordD_spec {c d x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hCx : closure (permsA n gC) = centralizer {X} ⊓ R')
    (hD : derivedOKP p M n gC gD ps cC cD c d x PL Pb = true)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) (h3 : 3 ≤ gC.size) (hM : 1 < M)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P)
    (hx : Rep n x X) (hxz : eqA n gC[0]! x = true) (hord : orderOf X = p) :
    IsSimpleGroup (closure (permsA n gD)) ∧
      (∃ g ∈ closure (permsA n gD), ∃ h ∈ closure (permsA n gD), g * h ≠ h * g) ∧
      Nat.card (closure (permsA n gD)) = M ∧ closure (permsA n gD) ≤ P ∧
      centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) =
        zpowers X ∧
      Nat.card (centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) ⊓
        closure (permsA n gC) : Subgroup (Equiv.Perm (Fin n))) = p := by
  obtain ⟨hDe, hDs, -, -, -, -, -, -, -, hnab, hsimple, hcent, hsift⟩ := derivedOKP_parts hD
  have hDeq := recordD_eq_commutator hps hC hD hgD h3
  have hDsize : gD.size = 2 := by simp [hgD]
  have hrepD : ∀ l < gD.size, Rep n gD[l]! (permOfArr n gD[l]!) := fun l hl =>
    rep_of_validA (enumOK_gens_valid hDe hl)
  have hcard : Nat.card (closure (permsA n gD)) = M := (enumOK_spec hps hDe).2.1.trans hDs
  have h0 : 0 < gC.size := by omega
  have hxC : X ∈ closure (permsA n gC) := mem_of_gen_zeroG hx h0 (enumOK_gens_valid hC h0) hxz
  have hDC : closure (permsA n gD) ≤ closure (permsA n gC) := by
    rw [← hDeq, commutator_le]
    intro a ha b hb'
    rw [commutatorElement_def]
    exact (closure (permsA n gC)).mul_mem ((closure (permsA n gC)).mul_mem
      ((closure (permsA n gC)).mul_mem ha hb') ((closure (permsA n gC)).inv_mem ha))
      ((closure (permsA n gC)).inv_mem hb')
  have hxcent : X ∈ centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have : a ∈ centralizer {X} ⊓ R' := hCx ▸ hDC ha
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcentD : centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) ⊓
      closure (permsA n gC) = zpowers X :=
    centralizer_eq_zpowers_kitP hps hC hDe hx hxC hxcent hcent
  refine ⟨?_, ?_, hcard, ?_, hcentD, ?_⟩
  · exact isSimpleGroup_of_conjSimpleOK hps hDe (by rw [hDs]; exact hM) hsimple
  · refine ⟨_, subset_closure (mem_permsA (k := 0) (by rw [hDsize]; norm_num)), _,
      subset_closure (mem_permsA (k := 1) (by rw [hDsize]; norm_num)), fun e => ?_⟩
    have := (commA_iff (hrepD 0 (by rw [hDsize]; norm_num))
      (hrepD 1 (by rw [hDsize]; norm_num))).2 e
    rw [hnab] at this
    exact Bool.false_ne_true this
  · exact closure_le_of_siftG (fun l hl => enumOK_gens_valid hDe hl) hsift hmemP
  · rw [hcentD, Nat.card_zpowers]
    exact hord

theorem recordD_spec_comm {c d x : Array ℕ} {X : Equiv.Perm (Fin n)}
    {D : Subgroup (Equiv.Perm (Fin n))}
    (hDc : D = ⁅closure (permsA n gC), closure (permsA n gC)⁆)
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hCx : closure (permsA n gC) = centralizer {X} ⊓ R')
    (hD : derivedOKP p M n gC gD ps cC cD c d x PL Pb = true)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) (h3 : 3 ≤ gC.size) (hM : 1 < M)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P)
    (hx : Rep n x X) (hxz : eqA n gC[0]! x = true) (hord : orderOf X = p) :
    IsSimpleGroup D ∧ (∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) ∧ Nat.card D = M ∧ D ≤ P ∧
      centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) = zpowers X ∧
      Nat.card (centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) :
        Subgroup (Equiv.Perm (Fin n))) = p := by
  rw [hDc, recordD_eq_commutator hps hC hD hgD h3]
  exact recordD_spec hps hC hCx hD hgD h3 hM hmemP hx hxz hord

end Spec

end CFSG.RankThree.PartOne
