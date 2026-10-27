module

public import CFSG.Sporadic.Schreier.PairChain

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

variable {n : ℕ}

theorem baseImgs_eq_iff {bs : List ℕ} (hbs : ∀ b ∈ bs, b < n) {w₁ w₂ : List (Array ℕ)}
    {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : RepW n w₁ g₁) (h₂ : RepW n w₂ g₂) :
    baseImgs bs w₁ = baseImgs bs w₂ ↔ ∀ x : Fin n, (x : ℕ) ∈ bs → g₁ x = g₂ x := by
  rw [baseImgs, baseImgs, List.map_inj_left]
  constructor
  · intro h x hx
    have := h x hx
    rw [h₁ x, h₂ x] at this
    exact Fin.ext this
  · intro h b hb
    have h1 := h₁ ⟨b, hbs b hb⟩
    have h2 := h₂ ⟨b, hbs b hb⟩
    change evR w₁ b = _ at h1
    change evR w₂ b = _ at h2
    rw [h1, h2, h ⟨b, hbs b hb⟩ hb]

theorem eq_of_baseImgs_eq {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}
    (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {w₁ w₂ : List (Array ℕ)}
    {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : RepW n w₁ g₁) (h₂ : RepW n w₂ g₂) (hg₁ : g₁ ∈ H)
    (hg₂ : g₂ ∈ H) (he : baseImgs bs w₁ = baseImgs bs w₂) : g₁ = g₂ := by
  have hfix := (baseImgs_eq_iff hbs h₁ h₂).1 he
  have h1 := hH (g₂⁻¹ * g₁) (H.mul_mem (H.inv_mem hg₂) hg₁) fun x hx => by
    rw [Equiv.Perm.mul_apply, hfix x hx]
    exact Equiv.Perm.inv_eq_iff_eq.2 rfl
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem conjImgs_eq (bs : List ℕ) (g gi : Array ℕ) (w : List (Array ℕ)) :
    conjImgs bs g gi w = baseImgs bs (gi :: (w ++ [g])) := by
  rw [conjImgs, baseImgs]
  refine List.map_congr_left fun b _ => ?_
  rw [evR_cons, evR_append]
  rfl

theorem repW_conj {g gi : Array ℕ} {w : List (Array ℕ)} {cg h : Equiv.Perm (Fin n)}
    (hg : Rep n g cg) (hgi : Rep n gi cg⁻¹) (hw : RepW n w h) :
    RepW n (gi :: (w ++ [g])) (cg * h * cg⁻¹) :=
  (hw.append (RepW.single hg)).cons hgi

theorem repW_reverse {ts : List (Array ℕ)} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) ts gs) : RepW n ts.reverse gs.prod := by
  induction h with
  | nil => exact repW_nil
  | cons hT _ ih =>
    rw [List.reverse_cons, List.prod_cons]
    exact ih.append (RepW.single hT)

theorem imgKey_inj {l₁ l₂ : List ℕ} (hl : l₁.length = l₂.length) (h₁ : ∀ x ∈ l₁, x < n)
    (h₂ : ∀ x ∈ l₂, x < n) (he : imgKey n l₁ = imgKey n l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at hl
    | cons b l₂ =>
      simp only [imgKey, List.foldr_cons] at he
      have ha := h₁ a List.mem_cons_self
      have hb := h₂ b List.mem_cons_self
      have hab : a = b := by
        have h1 := congrArg (· % n) he
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
        exact h1
      subst hab
      have hpos : 0 < n := by omega
      have h2 : List.foldr (fun x acc => x + n * acc) 0 l₁ =
          List.foldr (fun x acc => x + n * acc) 0 l₂ := by
        have := Nat.add_left_cancel he
        exact Nat.eq_of_mul_eq_mul_left hpos this
      rw [ih (by simpa using hl) (fun x hx => h₁ x (List.mem_cons_of_mem a hx))
        (fun x hx => h₂ x (List.mem_cons_of_mem a hx)) h2]

@[expose] def keyElt (n : ℕ) (bs : List ℕ) (g : Equiv.Perm (Fin n)) : ℕ :=
  imgKey n (bs.map fun b => if hb : b < n then (g ⟨b, hb⟩ : ℕ) else 0)

theorem imgKey_baseImgs {bs : List ℕ} (hbs : ∀ b ∈ bs, b < n) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (hw : RepW n w g) :
    imgKey n (baseImgs bs w) = keyElt n bs g := by
  rw [keyElt, baseImgs]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  rw [dite_eq_left (hbs b hb)]
  exact hw ⟨b, hbs b hb⟩

theorem keyElt_inj {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hH : BaseFaithful H bs)
    (hbs : ∀ b ∈ bs, b < n) {g₁ g₂ : Equiv.Perm (Fin n)} (hg₁ : g₁ ∈ H) (hg₂ : g₂ ∈ H)
    (he : keyElt n bs g₁ = keyElt n bs g₂) : g₁ = g₂ := by
  have hl := imgKey_inj (n := n) (by simp) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      rw [dite_eq_left (hbs b hb)]
      exact Fin.isLt _) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      rw [dite_eq_left (hbs b hb)]
      exact Fin.isLt _) he
  have h1 := hH (g₂⁻¹ * g₁) (H.mul_mem (H.inv_mem hg₂) hg₁) fun x hx => by
    have := congrArg (fun l => l.getD (bs.idxOf (x : ℕ)) 0) hl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_idxOf hx,
      Option.map_some, Option.getD_some, dite_eq_left x.2, Fin.eta] at this
    rw [Equiv.Perm.mul_apply, show g₁ x = g₂ x from Fin.ext this]
    exact Equiv.Perm.inv_eq_iff_eq.2 rfl
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem pairwise_of_strictInc : ∀ {l : List ℕ}, strictInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have hbl := pairwise_of_strictInc h.2
    refine List.Pairwise.cons (fun c hc => ?_) hbl
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons hbl hc)

@[expose] def nfElt (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (nf : Array ℕ) :
    Equiv.Perm (Fin n) :=
  ((List.range nf.size).map fun i => levT n S base i nf[i]!).prod

section Facts

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ} (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

omit hF in
theorem size_rawLevels : (rawLevels n S base).size = Q.baseCount := by
  rw [rawLevels, Array.size_ofFn, hA.base_size]

omit hF in
theorem nfOK_spec {nf : Array ℕ} (h : nfOK (rawLevels n S base) nf = true) :
    nf.size = Q.baseCount ∧ ∀ i < nf.size, nf[i]! < (lev n S base i).pts.size := by
  simp only [nfOK, Bool.and_eq_true, beq_iff_eq, allLt_iff, decide_eq_true_eq] at h
  exact ⟨h.1.trans (size_rawLevels hA), h.2⟩

theorem repW_nfWord {nf : Array ℕ} (h : nfOK (rawLevels n S base) nf = true) :
    RepW n (nfWord (rawLevels n S base) nf) (nfElt n S base nf) := by
  obtain ⟨hsz, hlt⟩ := nfOK_spec hA h
  have e : nfWord (rawLevels n S base) nf =
      ((List.range nf.size).map fun i => (rawLevels n S base)[i]!.tr[nf[i]!]!).reverse := by
    rw [nfWord, List.map_reverse]
  rw [e, nfElt]
  refine repW_reverse ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  exact hA.rep_levT hF (by omega) (hlt i hi')

theorem nfElt_mem (hQ : ValidSchreier Q) {nf : Array ℕ}
    (h : nfOK (rawLevels n S base) nf = true) : nfElt n S base nf ∈ Q.originalSubgroup := by
  obtain ⟨hsz, hlt⟩ := nfOK_spec hA h
  refine Q.originalSubgroup.list_prod_mem fun z hz => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
  have hi' := List.mem_range.1 hi
  exact levT_mem_original hA hF hQ (by omega) (hlt i hi')

theorem closureOK_spec (hQ : ValidSchreier Q) {bs : List ℕ}
    (hH : BaseFaithful Q.originalSubgroup bs) (hbs : ∀ b ∈ bs, b < n)
    {gens gensInv : Array (Array ℕ)} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    {rep : List (Array ℕ)} {x₀ : Equiv.Perm (Fin n)} (hrep : RepW n rep x₀)
    (hx₀ : x₀ ∈ Q.originalSubgroup) {elts : Array (Array ℕ)} {par lab : Array ℕ}
    (h : closureOK (rawLevels n S base) bs gens gensInv rep elts par lab = true) :
    ∀ k < elts.size, nfOK (rawLevels n S base) elts[k]! = true ∧
      ∃ c ∈ Q.originalSubgroup, nfElt n S base elts[k]! = c * x₀ * c⁻¹ := by
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
    · exact ⟨1, Q.originalSubgroup.one_mem, by
        rw [one_mul, inv_one, mul_one]
        exact eq_of_baseImgs_eq hH hbs hW hrep hM hx₀ h0⟩
    · obtain ⟨⟨hpar, hlab⟩, heq⟩ := (hk k hk').resolve_left (by omega)
      obtain ⟨-, c, hc, hcx⟩ := ih _ hpar (hpar.trans hk')
      obtain ⟨hgl, hgil, hgH⟩ := hg _ hlab
      have hWp := repW_nfWord hA hF (hnf _ (hpar.trans hk'))
      have hMp := nfElt_mem hA hF hQ (hnf _ (hpar.trans hk'))
      refine ⟨gg lab[k]! * c, Q.originalSubgroup.mul_mem hgH hc, ?_⟩
      rw [conjImgs_eq] at heq
      have := eq_of_baseImgs_eq hH hbs hW (repW_conj hgl hgil hWp) hM
        (Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem hgH hMp)
          (Q.originalSubgroup.inv_mem hgH)) heq
      rw [this, hcx]
      group

end Facts

theorem sum_flatMap_nat {α β : Type*} (f : α → List β) (g : β → ℕ) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap_nat f g l, List.map_cons,
      List.sum_cons]

theorem sum_eq_classSumNF {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) {bs : List ℕ}
    (hH : BaseFaithful Q.originalSubgroup bs) (hbs : ∀ b ∈ bs, b < n)
    {gens gensInv : Array (Array ℕ)} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (p : Equiv.Perm (Fin n) → ℕ) (hp : ∀ c ∈ Q.originalSubgroup, ∀ x, p (c * x * c⁻¹) = p x)
    (XG : List (Equiv.Perm (Fin n)))
    (hclosed : ∀ c ∈ Q.originalSubgroup, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG)
    (pRep : List (Array ℕ) → ℕ) (hpRep : ∀ w x, RepW n w x → x ∈ XG → pRep w = p x)
    (cl : List (List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ))
    (h1 : ∀ c ∈ cl, ∃ x ∈ XG, RepW n c.1 x ∧ x ∈ Q.originalSubgroup)
    (h2 : ∀ c ∈ cl,
      closureOK (rawLevels n S base) bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true)
    (h3 : keysDistinctNF n (rawLevels n S base) bs (cl.map fun c => c.2.1) = true)
    (h4 : (cl.map fun c => c.2.1.size).sum = XG.length) :
    (XG.map p).sum = (cl.map fun c => c.2.1.size * pRep c.1).sum := by
  set U := cl.flatMap fun c => c.2.1.toList
  have hentry : ∀ c ∈ cl, ∃ x ∈ XG, RepW n c.1 x ∧ x ∈ Q.originalSubgroup ∧
      ∀ nf ∈ c.2.1.toList, nfOK (rawLevels n S base) nf = true ∧
        ∃ d ∈ Q.originalSubgroup, nfElt n S base nf = d * x * d⁻¹ := by
    intro c hc
    obtain ⟨x, hx, hrep, hxH⟩ := h1 c hc
    refine ⟨x, hx, hrep, hxH, fun nf hnf => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hnf
    rw [Array.length_toList] at hk
    have := closureOK_spec hA hF hQ hH hbs hg hrep hxH (h2 c hc) k hk
    rw [getElem!_pos c.2.1 k hk] at this
    simpa [Array.getElem_toList] using this
  have hU : ∀ nf ∈ U, nfOK (rawLevels n S base) nf = true ∧ nfElt n S base nf ∈ XG := by
    intro nf hnf
    obtain ⟨c, hc, hnf⟩ := List.mem_flatMap.1 hnf
    obtain ⟨x, hx, -, -, hall⟩ := hentry c hc
    obtain ⟨hok, d, hd, he⟩ := hall nf hnf
    exact ⟨hok, he ▸ hclosed d hd x hx⟩
  have hkeys : (U.map fun nf => keyElt n bs (nfElt n S base nf)).Nodup := by
    have hsorted := (pairwise_of_strictInc h3).imp (fun hab => Nat.ne_of_lt hab)
    have hk := (List.mergeSort_perm _ _).nodup_iff.1 hsorted
    rw [List.flatMap_map] at hk
    have e : (cl.flatMap fun c => c.2.1.toList.map fun nf =>
        imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))) =
        U.map fun nf => keyElt n bs (nfElt n S base nf) := by
      rw [List.map_flatMap]
      refine List.flatMap_congr fun c hc => List.map_congr_left fun nf hnf => ?_
      exact imgKey_baseImgs hbs (repW_nfWord hA hF (hU nf (List.mem_flatMap.2 ⟨c, hc, hnf⟩)).1)
    rwa [e] at hk
  have hnodup : (U.map (nfElt n S base)).Nodup := by
    have h' : ((U.map (nfElt n S base)).map (keyElt n bs)).Nodup := by
      rw [List.map_map]
      exact hkeys
    exact h'.of_map _
  have hsub : U.map (nfElt n S base) ⊆ XG := by
    intro y hy
    obtain ⟨nf, hnf, rfl⟩ := List.mem_map.1 hy
    exact (hU nf hnf).2
  have hlen : XG.length ≤ (U.map (nfElt n S base)).length := by
    rw [List.length_map, List.length_flatMap, ← h4]
    simp
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  rw [← (hperm.map p).sum_eq, List.map_map, sum_flatMap_nat]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨x, hx, hrep, -, hall⟩ := hentry c hc
  have hconst : ∀ nf ∈ c.2.1.toList, (p ∘ nfElt n S base) nf = p x := by
    intro nf hnf
    obtain ⟨-, d, hd, he⟩ := hall nf hnf
    rw [Function.comp_apply, he, hp d hd x]
  rw [List.map_congr_left hconst, List.map_const', List.sum_replicate, smul_eq_mul,
    Array.length_toList, hpRep _ _ hrep hx]

theorem patProd_conj {G : Type*} [Group G] (c x y : G) (pat : List Bool) :
    (pat.map fun b => if b then c * y * c⁻¹ else c * x * c⁻¹).prod =
      c * (pat.map fun b => if b then y else x).prod * c⁻¹ := by
  have h : (pat.map fun b => if b then c * y * c⁻¹ else c * x * c⁻¹) =
      (pat.map fun b => if b then y else x).map (MulAut.conj c) := by
    rw [List.map_map]
    refine List.map_congr_left fun b _ => ?_
    cases b <;> rfl
  rw [h, ← map_list_prod]
  rfl

@[expose] def PatRel (conds : List (List Bool × ℕ)) {G : Type*} [Group G] (x y : G) : Prop :=
  ∀ c ∈ conds, orderOf (c.1.map fun b => if b then y else x).prod = c.2

noncomputable instance (conds : List (List Bool × ℕ)) {G : Type*} [Group G] (x : G) :
    DecidablePred (PatRel conds x) := fun _ => Classical.propDecidable _

theorem patRel_conj (conds : List (List Bool × ℕ)) {G : Type*} [Group G] (c x y : G) :
    PatRel conds (c * x * c⁻¹) (c * y * c⁻¹) ↔ PatRel conds x y := by
  refine forall_congr' fun d => forall_congr' fun _ => ?_
  rw [patProd_conj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem card_pairs_eq_classTotalNF {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hc : 0 < chunks) (h : rawChainOK n O S base W chunks = true) {bs : List ℕ}
    (hbs : bs = Q.base.toList.map Fin.val) {groups : List (List ℕ)}
    (hgr : groups.flatten = List.range Q.baseCount) {mx my : ℕ} (hmx : 0 < mx) (hmy : 0 < my)
    {conds : List (List Bool × ℕ)} (hconds : ∀ c ∈ conds, 0 < c.2)
    {gens gensInv : Array (Array ℕ)} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (cl : List (List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ))
    (h1 : ∀ c ∈ cl, ∃ x ∈ Q.originalSubgroup, RepW n c.1 x)
    (h1' : ∀ c ∈ cl, ordB bs c.1 mx = true)
    (h2 : ∀ c ∈ cl,
      closureOK (rawLevels n S base) bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true)
    (h3 : keysDistinctNF n (rawLevels n S base) bs (cl.map fun c => c.2.1) = true)
    (h4 : (cl.map fun c => c.2.1.size).sum =
      countW (fun w => ordB bs w mx) (blocksOf n (rawLevels n S base) groups) []) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ PatRel conds p.1 p.2} =
      (cl.map fun c => c.2.1.size * countW (fun y => ordB bs y my && condsOK bs c.1 y conds)
        (blocksOf n (rawLevels n S base) groups) []).sum := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  set P := Q.originalSubgroup
  set L := enumeration Q
  have hL : L.Nodup := enumeration_nodup Q hQ
  have hmem : ∀ g, g ∈ L ↔ g ∈ P := mem_enumeration_iff Q hQ
  have hH : BaseFaithful P bs := hbs ▸ baseFaithful_of_valid hQ
  have hbsn : ∀ b ∈ bs, b < n := fun b hb => by
    rw [hbs] at hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    exact x.2
  have hcoe : ∀ p : P × P, (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ PatRel conds p.1 p.2) ↔
      (orderOf (p.1 : Equiv.Perm (Fin n)) = mx ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = my ∧
        PatRel conds (p.1 : Equiv.Perm (Fin n)) p.2) := fun p => by
    simp only [PatRel, ← Subgroup.orderOf_coe, Subgroup.val_list_prod, List.map_map]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun c => forall_congr' fun _ => ?_))
    have e : (Subtype.val ∘ fun b : Bool => if b then p.2 else p.1) =
        fun b => if b then (p.2 : Equiv.Perm (Fin n)) else p.1 := by
      funext b; cases b <;> rfl
    rw [e]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum P L hL hmem (fun h => orderOf h = mx) (fun h => orderOf h = my)
      (PatRel conds)]
  set XG := L.filter fun h => decide (orderOf h = mx)
  set pf : Equiv.Perm (Fin n) → ℕ := fun x =>
    (L.filter fun h => decide (orderOf h = my)).countP fun y => decide (PatRel conds x y)
  have hpf : ∀ x, pf x = Nat.card {y : P // orderOf (y : Equiv.Perm (Fin n)) = my ∧
      PatRel conds x y} := by
    intro x
    simp only [pf]
    rw [List.countP_filter,
      card_subtype_eq_countP P L hL hmem (fun y => orderOf y = my ∧ PatRel conds x y)]
    congr 1
    funext y
    rw [Bool.decide_and, Bool.and_comm]
  have hpconj : ∀ c ∈ P, ∀ x, pf (c * x * c⁻¹) = pf x := by
    intro c hc x
    rw [hpf, hpf]
    let e : P ≃ P := (MulAut.conj (⟨c, hc⟩ : P)).toEquiv
    refine (Nat.card_congr (e.subtypeEquiv fun y => ?_)).symm
    have he : ((e y : P) : Equiv.Perm (Fin n)) = c * y * c⁻¹ := rfl
    rw [he, patRel_conj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hXGmem : ∀ x ∈ XG, x ∈ P ∧ orderOf x = mx := fun x hx => by
    rw [List.mem_filter, decide_eq_true_eq] at hx
    exact ⟨(hmem x).1 hx.1, hx.2⟩
  have hclosed : ∀ c ∈ P, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG := by
    intro c hc x hx
    obtain ⟨hxP, hxo⟩ := hXGmem x hx
    rw [List.mem_filter, decide_eq_true_eq, hmem]
    exact ⟨P.mul_mem (P.mul_mem hc hxP) (P.inv_mem hc),
      (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hxo⟩
  have hpRep : ∀ w x, RepW n w x → x ∈ XG →
      countW (fun y => ordB bs y my && condsOK bs w y conds)
        (blocksOf n (rawLevels n S base) groups) [] = pf x := by
    intro w x hw hx
    obtain ⟨hxP, -⟩ := hXGmem x hx
    rw [hpf, ← card_eq_countW hA hc h hgr (Pr := fun y => orderOf y = my ∧ PatRel conds x y)]
    intro y yg hy hyP
    rw [Bool.and_eq_true, ordB_iff hH hbsn hy hyP hmy, condsOK_iff hH hbsn hw hy hxP hyP hconds]
    rfl
  have hXGlen : XG.length = countW (fun w => ordB bs w mx)
      (blocksOf n (rawLevels n S base) groups) [] := by
    have h1 := card_subtype_eq_countP P L hL hmem (fun y => orderOf y = mx)
    rw [List.countP_eq_length_filter] at h1
    rw [← card_eq_countW hA hc h hgr (Pr := fun y => orderOf y = mx)
      (fun w g hw hgP => ordB_iff hH hbsn hw hgP hmx)]
    exact h1.symm
  refine sum_eq_classSumNF hA hF hQ hH hbsn hg pf hpconj XG hclosed _ hpRep cl
    (fun c hc => ?_) h2 h3 (h4.trans hXGlen.symm)
  obtain ⟨x, hxP, hx⟩ := h1 c hc
  refine ⟨x, ?_, hx, hxP⟩
  rw [List.mem_filter, decide_eq_true_eq, hmem]
  exact ⟨hxP, (ordB_iff hH hbsn hx hxP hmx).1 (h1' c hc)⟩

theorem exists_repW_of_forall {H : Subgroup (Equiv.Perm (Fin n))} :
    ∀ {w : List (Array ℕ)}, (∀ t ∈ w, ∃ h ∈ H, Rep n t h) → ∃ g ∈ H, RepW n w g
  | [], _ => ⟨1, H.one_mem, repW_nil⟩
  | t :: w, hw => by
    obtain ⟨h, hh, ht⟩ := hw t List.mem_cons_self
    obtain ⟨g, hg, hwg⟩ := exists_repW_of_forall fun t' ht' => hw t' (List.mem_cons_of_mem t ht')
    exact ⟨g * h, H.mul_mem hg hh, hwg.cons ht⟩

theorem mem_patW {x y : List (Array ℕ)} {pat : List Bool} {t : Array ℕ} (ht : t ∈ patW x y pat) :
    t ∈ x ∨ t ∈ y := by
  simp only [patW, List.mem_flatten, List.mem_map, List.mem_reverse] at ht
  obtain ⟨l, ⟨b, -, rfl⟩, ht⟩ := ht
  cases b
  · exact Or.inl ht
  · exact Or.inr ht

theorem patRel_comm_iff {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) {m : ℕ}
    (hy : orderOf y = m) (hm : 0 < m) (r s : ℕ) :
    PatRel [([false, true], r), ([false, true, false] ++ List.replicate (m - 1) true, s)] x y ↔
      orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s := by
  have hxi : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  have hyi : y⁻¹ = y ^ (m - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hm, ← hy, pow_orderOf_eq_one]
  have e1 : (([false, true] : List Bool).map fun b => if b then y else x).prod = x * y := by
    simp
  have e2 : ((([false, true, false] : List Bool) ++ List.replicate (m - 1) true).map
      fun b => if b then y else x).prod = x * y * x⁻¹ * y⁻¹ := by
    rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, hxi, hyi]
    simp [mul_assoc]
  simp only [PatRel, List.mem_cons, forall_eq_or_imp, List.not_mem_nil, e1, e2]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, fun _ h => h.elim⟩

end CFSG.Sporadic.Schreier
