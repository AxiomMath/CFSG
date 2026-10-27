module

public import CFSG.Sporadic.Schreier.PairClasses

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

@[expose] def closureKeys (n : Nat) (L : Array Level) (bs : List Nat)
    (cls : List (Array (Array Nat))) : List Nat :=
  cls.flatMap fun c => c.toList.map fun nf => imgKey n (baseImgs bs (nfWord L nf))

@[expose] def coverTest (n : Nat) (bs : List Nat) (t0 : Array Nat) (keys : List Nat)
    (w : List (Array Nat)) : Bool :=
  fixB bs w 2 && !(fixB bs w 1) && !(baseImgs bs w == baseImgs bs [t0]) &&
    !(keys.contains (imgKey n (baseImgs bs w)))

@[expose] def coverClosures (n : Nat) (L : Array Level) (bs : List Nat)
    (gens gensInv : Array (Array Nat)) (reps : List (Array Nat)) (cap : Nat) :
    List (Array (Array Nat) × Array Nat × Array Nat) :=
  reps.map fun r => conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs [r]).toArray) cap

@[expose] def coverOK (n : Nat) (L : Array Level) (bs : List Nat)
    (gens gensInv : Array (Array Nat)) (t0 : Array Nat) (reps : List (Array Nat)) (cap : Nat)
    (blocks : List (Array (Array Nat))) : Bool :=
  let cls := coverClosures n L bs gens gensInv reps cap
  ((reps.zip cls).all fun p => closureOK L bs gens gensInv [p.1] p.2.1 p.2.2.1 p.2.2.2) &&
    countW (coverTest n bs t0 (closureKeys n L bs (cls.map (·.1)))) blocks [] == 0

end CFSG.Quasithin.KGC31.Native

namespace CFSG.Quasithin.KGC31

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
  CFSG.Quasithin.KGC31.Native

variable {n : ℕ}

section Facts

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ} (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem closureOK_spec_le (hQ : ValidSchreier Q) {bs : List ℕ}
    (hH : BaseFaithful Q.originalSubgroup bs) (hbs : ∀ b ∈ bs, b < n)
    {K : Subgroup (Equiv.Perm (Fin n))} {gens gensInv : Array (Array ℕ)}
    {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧
      gg l ∈ Q.originalSubgroup ∧ gg l ∈ K)
    {rep : List (Array ℕ)} {x₀ : Equiv.Perm (Fin n)} (hrep : RepW n rep x₀)
    (hx₀ : x₀ ∈ Q.originalSubgroup) {elts : Array (Array ℕ)} {par lab : Array ℕ}
    (h : closureOK (rawLevels n S base) bs gens gensInv rep elts par lab = true) :
    ∀ k < elts.size, nfOK (rawLevels n S base) elts[k]! = true ∧
      ∃ c ∈ K, nfElt n S base elts[k]! = c * x₀ * c⁻¹ := by
  simp only [closureOK, allFrom, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨_, hnf⟩, h0⟩, hk⟩ := h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk'
    refine ⟨hnf k hk', ?_⟩
    have hW := repW_nfWord hA hF (hnf k hk')
    have hM := nfElt_mem hA hF hQ (hnf k hk')
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, K.one_mem, by
        rw [one_mul, inv_one, mul_one]
        exact eq_of_baseImgs_eq hH hbs hW hrep hM hx₀ h0⟩
    · obtain ⟨⟨hpar, hlab⟩, heq⟩ := (hk k hk').resolve_left (by omega)
      obtain ⟨-, c, hc, hcx⟩ := ih _ hpar (hpar.trans hk')
      obtain ⟨hgl, hgil, hgH, hgK⟩ := hg _ hlab
      have hWp := repW_nfWord hA hF (hnf _ (hpar.trans hk'))
      have hMp := nfElt_mem hA hF hQ (hnf _ (hpar.trans hk'))
      refine ⟨gg lab[k]! * c, K.mul_mem hgK hc, ?_⟩
      rw [conjImgs_eq] at heq
      have := eq_of_baseImgs_eq hH hbs hW (repW_conj hgl hgil hWp) hM
        (Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem hgH hMp)
          (Q.originalSubgroup.inv_mem hgH)) heq
      rw [this, hcx]
      group

end Facts

theorem contains_iff_mem {l : List ℕ} {a : ℕ} : l.contains a = true ↔ a ∈ l := by
  simp

theorem exists_conj_of_coverOK {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hc : 0 < chunks) (hQc : rawChainOK n O S base W chunks = true) {bs : List ℕ}
    (hH : BaseFaithful Q.originalSubgroup bs) (hbs : ∀ b ∈ bs, b < n)
    {Q₁ : RawSchreierDatum n} {O₁ S₁ : Array (Array ℕ)} {base₁ : Array ℕ} {W₁ : Array (List ℤ)}
    {chunks₁ : ℕ} (hA₁ : ChainArrays Q₁ O₁ S₁ base₁ W₁) (hc₁ : 0 < chunks₁)
    (hQc₁ : rawChainOK n O₁ S₁ base₁ W₁ chunks₁ = true)
    (hK : Q₁.originalSubgroup ≤ Q.originalSubgroup) {groups : List (List ℕ)}
    (hg : groups.flatten = List.range Q₁.baseCount) {gens gensInv : Array (Array ℕ)}
    {gg : ℕ → Equiv.Perm (Fin n)}
    (hgens : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧
      gg l ∈ Q₁.originalSubgroup)
    {t0 : Array ℕ} {t₀ : Equiv.Perm (Fin n)} (ht : Rep n t0 t₀) (ht₀ : t₀ ∈ Q.originalSubgroup)
    {reps : List (Array ℕ)} {repsG : List (Equiv.Perm (Fin n))}
    (hreps : List.Forall₂ (Rep n) reps repsG) (hrepsH : ∀ r ∈ repsG, r ∈ Q.originalSubgroup)
    {cap : ℕ}
    (h : coverOK n (rawLevels n S base) bs gens gensInv t0 reps cap
      (blocksOf n (rawLevels n S₁ base₁) groups) = true) :
    ∀ x ∈ Q₁.originalSubgroup, x ^ 2 = 1 → x ≠ 1 → x ≠ t₀ →
      ∃ r ∈ repsG, ∃ c ∈ Q₁.originalSubgroup, c * x * c⁻¹ = r := by
  have hF := chainCheckFacts hQc
  have hQ := (validSchreier_of_chainOK hA hc hQc).1
  rw [coverOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hcl, hcnt⟩ := h
  have hlen : (coverClosures n (rawLevels n S base) bs gens gensInv reps cap).length =
      reps.length := by
    rw [coverClosures, List.length_map]
  have hfP : ∀ w g, RepW n w g → g ∈ Q₁.originalSubgroup →
      (coverTest n bs t0 (closureKeys n (rawLevels n S base) bs
        ((coverClosures n (rawLevels n S base) bs gens gensInv reps cap).map (·.1))) w = true ↔
        g ^ 2 = 1 ∧ g ≠ 1 ∧ g ≠ t₀ ∧ keyElt n bs g ∉ closureKeys n (rawLevels n S base) bs
          ((coverClosures n (rawLevels n S base) bs gens gensInv reps cap).map (·.1))) := by
    intro w g hw hg
    have hgQ := hK hg
    rw [coverTest, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      Bool.not_eq_true', Bool.not_eq_true', fixB_iff_eq_one hH hbs hw hgQ,
      ← Bool.not_eq_true, fixB_iff_eq_one hH hbs hw hgQ, pow_one, ← Bool.not_eq_true,
      beq_iff_eq, ← Bool.not_eq_true, contains_iff_mem, imgKey_baseImgs hbs hw]
    constructor
    · rintro ⟨⟨⟨h2, h1⟩, ht'⟩, hk⟩
      exact ⟨h2, h1, fun e => ht' ((baseImgs_eq_iff hbs hw (RepW.single ht)).2 fun _ _ => by
        rw [e]), hk⟩
    · rintro ⟨h2, h1, ht', hk⟩
      exact ⟨⟨⟨h2, h1⟩, fun e => ht' (eq_of_baseImgs_eq hH hbs hw (RepW.single ht) hgQ ht₀ e)⟩,
        hk⟩
  have hcard := card_eq_countW hA₁ hc₁ hQc₁ hg hfP
  rw [hcnt] at hcard
  have hempty := Finite.card_eq_zero_iff.mp hcard
  intro x hx hx2 hx1 hxt
  have hkey : keyElt n bs x ∈ closureKeys n (rawLevels n S base) bs
      ((coverClosures n (rawLevels n S base) bs gens gensInv reps cap).map (·.1)) := by
    by_contra hk
    exact hempty.false ⟨⟨x, hx⟩, hx2, hx1, hxt, hk⟩
  rw [closureKeys, List.mem_flatMap] at hkey
  obtain ⟨elts, helts, hk⟩ := hkey
  obtain ⟨nf, hnf, hnfk⟩ := List.mem_map.1 hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 helts
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  have hi' : i < reps.length := by rw [← hlen]; exact hi
  have hiG : i < repsG.length := by rw [← hreps.length_eq]; exact hi'
  have hrep : Rep n reps[i] repsG[i] := (List.forall₂_iff_get.1 hreps).2 i hi' hiG
  have hmem : (reps[i], p) ∈ reps.zip (coverClosures n (rawLevels n S base) bs gens gensInv
      reps cap) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, by rw [List.length_zip, hlen]; omega, ?_⟩
    rw [List.getElem_zip, hpi]
  have hclose := List.all_eq_true.1 hcl _ hmem
  obtain ⟨k, hk', hkk⟩ := List.getElem_of_mem hnf
  rw [Array.length_toList] at hk'
  obtain ⟨hnfok, c, hcK, hcx⟩ := closureOK_spec_le hA hF hQ hH hbs (K := Q₁.originalSubgroup)
    (fun l hl => ⟨(hgens l hl).1, (hgens l hl).2.1, hK (hgens l hl).2.2, (hgens l hl).2.2⟩)
    (RepW.single hrep) (hrepsH _ (List.getElem_mem _)) hclose k hk'
  have e : (reps[i], p).2.1[k]! = nf := by
    rw [← hkk, Array.getElem_toList]
    exact getElem!_pos _ k hk'
  rw [e] at hnfok hcx
  have hW := repW_nfWord hA hF hnfok
  have hM := nfElt_mem hA hF hQ hnfok
  rw [imgKey_baseImgs hbs hW] at hnfk
  have hxe := keyElt_inj hH hbs hM (hK hx) hnfk
  refine ⟨repsG[i], List.getElem_mem _, c⁻¹, Q₁.originalSubgroup.inv_mem hcK, ?_⟩
  rw [← hxe, hcx]
  group

end CFSG.Quasithin.KGC31

end
