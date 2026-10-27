module

public import CFSG.RankThree.Native.F2Chain

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS

structure Sys (d : ℕ) (V : Array ℕ) (VG LK : ℕ → ℕ) : Prop where
  hd : 0 < d
  nodup : V.toList.Nodup
  lt : ∀ v ∈ V, v < 2 ^ d
  vg : ∀ i < V.size, V[i]! = VG i
  lk : ∀ i < V.size, LK (VG i) = i

structure LevFacts (d : ℕ) (V : Array ℕ) (L : Array Level) (nb : ℕ) (m : ℕ → ℕ)
    (PT PO TM TIM : ℕ → ℕ → ℕ) : Prop where
  size : L.size = nb
  pts_size : ∀ l < nb, (L[l]!).pts.size = m l
  pts : ∀ l < nb, ∀ k < m l, (L[l]!).pts[k]! = PT l k
  pts_lt : ∀ l < nb, ∀ k < m l, PT l k < V.size
  pos_pts : ∀ l < nb, ∀ k < m l, PO l (PT l k) = k
  pos : ∀ l < nb, ∀ x < V.size, (L[l]!).pos[x]! = PO l x
  tr : ∀ l < nb, ∀ k < m l, (L[l]!).tr[k]! = permOfMat d V (TM l k)
  trInv : ∀ l < nb, ∀ k < m l, (L[l]!).trInv[k]! = permOfMat d V (TIM l k)
  inv : ∀ l < nb, ∀ k < m l, Inv d V (TM l k) (TIM l k)

theorem levFacts_lvlOf {d : ℕ} {V : Array ℕ} {nb : ℕ} {m : ℕ → ℕ}
    {PT PO PA LB TM TIM : ℕ → ℕ → ℕ} (hlt : ∀ l < nb, ∀ k < m l, PT l k < V.size)
    (hpp : ∀ l < nb, ∀ k < m l, PO l (PT l k) = k)
    (hinv : ∀ l < nb, ∀ k < m l, Inv d V (TM l k) (TIM l k)) :
    LevFacts d V (Array.ofFn (n := nb) fun i =>
      lvlOf d V (m i) (PT i) (PO i) (PA i) (LB i) (TM i) (TIM i)) nb m PT PO TM TIM := by
  have hg : ∀ l (hl : l < nb), (Array.ofFn (n := nb) fun i : Fin nb =>
      lvlOf d V (m i) (PT i) (PO i) (PA i) (LB i) (TM i) (TIM i))[l]! =
        lvlOf d V (m l) (PT l) (PO l) (PA l) (LB l) (TM l) (TIM l) := by
    intro l hl
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  refine ⟨by simp, fun l hl => ?_, fun l hl k hk => ?_, hlt, hpp, fun l hl x hx => ?_,
    fun l hl k hk => ?_, fun l hl k hk => ?_, hinv⟩
  · rw [hg l hl]
    simp [lvlOf]
  · rw [hg l hl, lvlOf, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  · rw [hg l hl, lvlOf, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  · rw [hg l hl, lvlOf, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  · rw [hg l hl, lvlOf, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem allN_of_chunks {f : ℕ → Bool} {c n : ℕ}
    (h : ∀ j < n, allN c (fun t => f (Nat.add (Nat.mul c j) t)) = true) : ∀ i < c * n, f i = true := by
  intro i hi
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · simp [h0] at hi
    · exact h0
  have hj : i / c < n := (Nat.div_lt_iff_lt_mul hc).2 (by rwa [Nat.mul_comm] at hi)
  have := allN_spec (h (i / c) hj) (i % c) (Nat.mod_lt i hc)
  have e : Nat.add (Nat.mul c (i / c)) (i % c) = i := Nat.div_add_mod i c
  rwa [e] at this

section Facts

variable {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ}

theorem Sys.vidx_eq (hs : Sys d V VG LK) {q : ℕ} (hq : q < V.size) : vidx V (VG q) = q := by
  rw [← hs.vg q hq]
  exact vidx_get hs.nodup hq

theorem Sys.mem (hs : Sys d V VG LK) {q : ℕ} (hq : q < V.size) : VG q ∈ V := by
  rw [← hs.vg q hq]
  exact mem_of_lt hq

theorem Sys.perm_get (hs : Sys d V VG LK) {G q : ℕ} (hq : q < V.size) :
    (permOfMat d V G)[q]! = vidx V (vmul d (VG q) G) := by
  rw [permOfMat_get hq, hs.vg q hq]

theorem vidx_beq {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) :
    (vidx V a == vidx V b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  constructor
  · intro h
    rw [← (getElem_vidx ha).2, h, (getElem_vidx hb).2]
  · rintro rfl
    rfl

end Facts

@[expose] noncomputable def siftM (vm mm : ℕ → ℕ → ℕ) (I n : ℕ) (VG BS LK m : ℕ → ℕ)
    (PO TIM : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, G => Nat.beq G I
  | fuel + 1, l, G => strictB (vm (VG (BS l)) G) fun w => strictB (LK w) fun q =>
    Nat.blt q n && Nat.beq (VG q) w && Nat.blt (PO l q) (m l) &&
      siftM vm mm I n VG BS LK m PO TIM fuel (l + 1) (mm G (TIM l (PO l q)))

theorem siftA_of_siftM {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm mm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    {I : ℕ} (hI : I = idM d) {L : Array Level} {nb : ℕ} {m : ℕ → ℕ} {PT PO TM TIM : ℕ → ℕ → ℕ}
    (hL : LevFacts d V L nb m PT PO TM TIM) {base : Array ℕ} {BS : ℕ → ℕ}
    (hBS : ∀ i < nb, base[i]! = BS i) (hb : ∀ i < nb, BS i < V.size) :
    ∀ fuel l G, l + fuel = nb → (∀ v ∈ V, vmul d v G ∈ V) →
      siftM vm mm I V.size VG BS LK m PO TIM fuel l G = true →
      siftA V.size L base l (permOfMat d V G) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro l G hl _ h
    rw [siftA, dite_eq_right (by rw [hL.size]; omega)]
    rw [siftM, Nat.beq_eq, hI] at h
    subst h
    rw [permOfMat_idM hs.hd hs.nodup hs.lt, eqA, allLt_iff]
    intro i _
    exact beq_self_eq_true _
  | succ fuel ih =>
    intro l G hl hG h
    have hlt : l < nb := by omega
    rw [siftM, strictB_eq', strictB_eq'] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨hq, hw⟩, hpo⟩, hrec⟩ := h
    rw [siftA, dite_eq_left (by rw [hL.size]; exact hlt)]
    simp only
    rw [← getElem!_pos L l (by rw [hL.size]; exact hlt), hBS l hlt, hs.perm_get (hb l hlt),
      ← hvm, ← hw, hs.vidx_eq hq, hL.pos l hlt _ hq, hL.pts_size l hlt, decide_eq_true hpo,
      Bool.true_and, hL.trInv l hlt _ hpo, compA_permOfMat hG]
    apply ih (l + 1) _ (by omega) (maps_mmul hG (hL.inv l hlt _ hpo).2.1)
    rwa [← hmm]

theorem fixLevCount_eq {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {L : Array Level} {nb : ℕ} {m : ℕ → ℕ} {PT PO TM TIM : ℕ → ℕ → ℕ}
    (hL : LevFacts d V L nb m PT PO TM TIM) {Z : ℕ} (hZ : ∀ v ∈ V, vmul d v Z ∈ V)
    {F : List ℕ} (hF : F.Pairwise (· < ·)) (hFf : ∀ q ∈ F, q < V.size ∧ vmul d (VG q) Z = VG q)
    (hFa : ∀ q < V.size, vmul d (VG q) Z = VG q → q ∈ F) {i : ℕ} (hi : i < nb) :
    fixLevCount V.size L (permOfMat d V Z) i = (F.filter fun q => Nat.blt (PO i q) (m i)).length := by
  have hfix : ∀ q < V.size, ((permOfMat d V Z)[q]! == q) = Nat.beq (vmul d (VG q) Z) (VG q) := by
    intro q hq
    rw [hs.perm_get hq]
    nth_rewrite 2 [← hs.vidx_eq hq]
    rw [vidx_beq (hZ _ (hs.mem hq)) (hs.mem hq)]
  have hR : (List.range V.size).filter (fun q => Nat.beq (vmul d (VG q) Z) (VG q)) = F := by
    apply List.SortedLT.eq_of_mem_iff ((List.pairwise_lt_range).filter _).sortedLT hF.sortedLT
    intro q
    rw [List.mem_filter, List.mem_range, Nat.beq_eq]
    exact ⟨fun h => hFa q h.1 h.2, fun h => hFf q h⟩
  have hfin : (List.finRange V.size).map Fin.val = List.range V.size :=
    List.ext_getElem (by simp) fun i _ _ => by simp
  unfold fixLevCount fixLevList
  rw [← List.length_map (f := Fin.val), ← hR, List.filter_filter, ← hfin, List.filter_map]
  congr 2
  apply List.filter_congr
  intro q _
  simp only [Function.comp, hfix q q.2, hL.pos i hi q q.2, hL.pts_size i hi]
  cases Nat.beq (vmul d (VG q) Z) (VG q) <;> simp [blt_eq_decide]

@[expose] noncomputable def tailM (mm : ℕ → ℕ → ℕ) (X : ℕ) (EM : ℕ → Bool) (m : ℕ → ℕ)
    (TM : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, A => !(Nat.beq (mm X A) (mm A X)) || EM A
  | fuel + 1, i, A => allN (m i) fun k => tailM mm X EM m TM fuel (i + 1) (mm (TM i k) A)

theorem leaf_of {d : ℕ} {V : Array ℕ} {l : ℕ → List ℕ} (hsp : Spans d V l)
    {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {X A : ℕ}
    (hX : ∀ v ∈ V, vmul d v X ∈ V) (hA : ∀ v ∈ V, vmul d v A ∈ V) {E : List (Array ℕ)}
    {EM : ℕ → Bool} (hEM : ∀ A, (∀ v ∈ V, vmul d v A ∈ V) → EM A = true →
      E.any (eqA V.size (permOfMat d V A)) = true)
    (h : (!(Nat.beq (mm X A) (mm A X)) || EM A) = true) :
    (!(commA V.size (permOfMat d V A) (permOfMat d V X)) ||
      E.any (eqA V.size (permOfMat d V A))) = true := by
  rw [commA_permOfMat hsp hA hX, ← hmm, ← hmm]
  rw [Bool.or_eq_true] at h ⊢
  exact h.imp id (hEM A hA)

theorem tailOK_of_tailM {d : ℕ} {V : Array ℕ} {l : ℕ → List ℕ} (hsp : Spans d V l)
    {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {L : Array Level} {nb : ℕ}
    {m : ℕ → ℕ} {PT PO TM TIM : ℕ → ℕ → ℕ} (hL : LevFacts d V L nb m PT PO TM TIM) {X : ℕ}
    (hX : ∀ v ∈ V, vmul d v X ∈ V) {E : List (Array ℕ)} {EM : ℕ → Bool}
    (hEM : ∀ A, (∀ v ∈ V, vmul d v A ∈ V) → EM A = true →
      E.any (eqA V.size (permOfMat d V A)) = true) :
    ∀ fuel i A, i + fuel = nb → (∀ v ∈ V, vmul d v A ∈ V) → tailM mm X EM m TM fuel i A = true →
      tailOK V.size L (permOfMat d V X) E fuel i (permOfMat d V A) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i A _ hA h
    exact leaf_of hsp hmm hX hA hEM h
  | succ fuel ih =>
    intro i A hi hA h
    have hlt : i < nb := by omega
    rw [tailOK, allLt_iff, hL.pts_size i hlt]
    intro k hk
    rw [hL.tr i hlt k hk, compA_permOfMat (hL.inv i hlt k hk).1]
    refine ih (i + 1) _ (by omega) (maps_mmul (hL.inv i hlt k hk).1 hA) ?_
    rw [← hmm]
    exact allN_spec h k hk

@[expose] noncomputable def relVecM (vm : ℕ → ℕ → ℕ) (VG BS : ℕ → ℕ) (i A q m' : ℕ) : ℕ :=
  nIf(Nat.blt m' i, vm (VG (BS m')) A, vm (VG q) A)

@[expose] noncomputable def relM (vm : ℕ → ℕ → ℕ) (VG BS XP : ℕ → ℕ) (rels : List (ℕ × ℕ × ℕ))
    (i A q : ℕ) : Bool :=
  rels.all fun r => !(decide (max r.1 r.2.1 = i)) ||
    Nat.beq (relVecM vm VG BS i A q r.2.1) (vm (relVecM vm VG BS i A q r.1) (XP r.2.2))

theorem relVecM_eq {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) {nb : ℕ} {base : Array ℕ}
    {BS : ℕ → ℕ} (hBS : ∀ i < nb, base[i]! = BS i) (hb : ∀ i < nb, BS i < V.size) {i A q m' : ℕ}
    (hq : q < V.size) (hm : m' < nb) :
    relImg base i (permOfMat d V A) q m' = vidx V (relVecM vm VG BS i A q m') := by
  unfold relImg relVecM
  simp only [hvm, blt_eq_decide]
  by_cases h : m' < i
  · simp only [h, ↓reduceIte, decide_true]
    rw [hBS m' hm, hs.perm_get (hb m' hm)]
  · simp only [h, ↓reduceIte, decide_false]
    rw [hs.perm_get hq]

theorem relVecM_mem {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) {nb : ℕ} {BS : ℕ → ℕ}
    (hb : ∀ i < nb, BS i < V.size) {i A q m' : ℕ} (hA : ∀ v ∈ V, vmul d v A ∈ V)
    (hq : q < V.size) (hm : m' < nb) : relVecM vm VG BS i A q m' ∈ V := by
  unfold relVecM
  simp only [hvm, blt_eq_decide]
  by_cases h : m' < i
  · simp only [h, decide_true]
    exact hA _ (hs.mem (hb m' hm))
  · simp only [h, decide_false]
    exact hA _ (hs.mem hq)

theorem relOK_eq {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) {nb : ℕ} {base : Array ℕ}
    {BS : ℕ → ℕ} (hBS : ∀ i < nb, base[i]! = BS i) (hb : ∀ i < nb, BS i < V.size)
    {xs : Array (Array ℕ)} {XP : ℕ → ℕ} (hxs : ∀ e < xs.size, xs[e]! = permOfMat d V (XP e))
    (hXP : ∀ e < xs.size, ∀ v ∈ V, vmul d v (XP e) ∈ V) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < nb ∧ r.2.1 < nb) {i A q : ℕ}
    (hA : ∀ v ∈ V, vmul d v A ∈ V) (hq : q < V.size) :
    relOK base xs rels i (permOfMat d V A) q = relM vm VG BS XP rels i A q := by
  unfold relOK relM
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun r => imp_congr_right fun hr => ?_
  obtain ⟨he, h1, h2⟩ := hrels r hr
  have m1 := relVecM_mem hs hvm hb (i := i) hA hq h1
  rw [relVecM_eq hs hvm hBS hb hq h1, relVecM_eq hs hvm hBS hb hq h2, hxs _ he,
    permOfMat_get (getElem_vidx m1).1, (getElem_vidx m1).2,
    vidx_beq (relVecM_mem hs hvm hb hA hq h2) (hXP _ he _ m1), hvm]

@[expose] noncomputable def ptailM (vm mm : ℕ → ℕ → ℕ) (n : ℕ) (VG BS LK XP : ℕ → ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (X : ℕ) (EM PVf : ℕ → Bool) (PVl PVe m : ℕ → ℕ)
    (PT PO TM TIM : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, A, _ => !(Nat.beq (mm X A) (mm A X)) || EM A
  | fuel + 1, i, A, AI =>
    bif PVf i then
      strictB (vm (vm (vm (VG (BS (PVl i))) A) (XP (PVe i))) AI) fun w => strictB (LK w) fun q =>
        !(Nat.blt q n && Nat.beq (VG q) w && Nat.blt (PO i q) (m i)) ||
          (!(relM vm VG BS XP rels i A q) ||
            ptailM vm mm n VG BS LK XP rels X EM PVf PVl PVe m PT PO TM TIM fuel (i + 1)
              (mm (TM i (PO i q)) A) (mm AI (TIM i (PO i q))))
    else allN (m i) fun k => !(relM vm VG BS XP rels i A (PT i k)) ||
      ptailM vm mm n VG BS LK XP rels X EM PVf PVl PVe m PT PO TM TIM fuel (i + 1)
        (mm (TM i k) A) (mm AI (TIM i k))

theorem ptailM_succ {vm mm : ℕ → ℕ → ℕ} {n : ℕ} {VG BS LK XP : ℕ → ℕ}
    {rels : List (ℕ × ℕ × ℕ)} {X : ℕ} {EM PVf : ℕ → Bool} {PVl PVe m : ℕ → ℕ}
    {PT PO TM TIM : ℕ → ℕ → ℕ} {fuel i A AI : ℕ} :
    ptailM vm mm n VG BS LK XP rels X EM PVf PVl PVe m PT PO TM TIM (fuel + 1) i A AI =
      bif PVf i then
        strictB (vm (vm (vm (VG (BS (PVl i))) A) (XP (PVe i))) AI) fun w => strictB (LK w) fun q =>
          !(Nat.blt q n && Nat.beq (VG q) w && Nat.blt (PO i q) (m i)) ||
            (!(relM vm VG BS XP rels i A q) ||
              ptailM vm mm n VG BS LK XP rels X EM PVf PVl PVe m PT PO TM TIM fuel (i + 1)
                (mm (TM i (PO i q)) A) (mm AI (TIM i (PO i q))))
      else allN (m i) fun k => !(relM vm VG BS XP rels i A (PT i k)) ||
        ptailM vm mm n VG BS LK XP rels X EM PVf PVl PVe m PT PO TM TIM fuel (i + 1)
          (mm (TM i k) A) (mm AI (TIM i k)) :=
  rfl

theorem ptailOK_of_ptailM {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm mm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    {l : ℕ → List ℕ} (hsp : Spans d V l) {L : Array Level} {nb : ℕ} {m : ℕ → ℕ}
    {PT PO TM TIM : ℕ → ℕ → ℕ} (hL : LevFacts d V L nb m PT PO TM TIM) {base : Array ℕ}
    {BS : ℕ → ℕ} (hBS : ∀ i < nb, base[i]! = BS i) (hb : ∀ i < nb, BS i < V.size) {X : ℕ}
    (hX : ∀ v ∈ V, vmul d v X ∈ V) {xs : Array (Array ℕ)} {XP : ℕ → ℕ}
    (hxs : ∀ e < xs.size, xs[e]! = permOfMat d V (XP e))
    (hXP : ∀ e < xs.size, ∀ v ∈ V, vmul d v (XP e) ∈ V) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < nb ∧ r.2.1 < nb) {E : List (Array ℕ)}
    {EM : ℕ → Bool} (hEM : ∀ A, (∀ v ∈ V, vmul d v A ∈ V) → EM A = true →
      E.any (eqA V.size (permOfMat d V A)) = true)
    {PVf : ℕ → Bool} {PVl PVe : ℕ → ℕ}
    (hpv : ∀ i < nb, PVf i = true → (PVl i, i, PVe i) ∈ rels ∧ PVl i < i) :
    ∀ fuel i A AI, i + fuel = nb → (∀ v ∈ V, vmul d v A ∈ V) → mmul d A AI = idM d →
      ptailM vm mm V.size VG BS LK XP rels X EM PVf PVl PVe m PT PO TM TIM fuel i A AI = true →
      ptailOK V.size L base (permOfMat d V X) xs rels E fuel i (permOfMat d V A) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i A AI _ hA _ h
    exact leaf_of hsp hmm hX hA hEM h
  | succ fuel ih =>
    intro i A AI hi hA hAI h
    have hlt : i < nb := by omega
    rw [ptailOK, allLt_iff, hL.pts_size i hlt]
    intro k hk
    have hp := hL.pts_lt i hlt k hk
    rw [hL.pts i hlt k hk, hL.tr i hlt k hk, compA_permOfMat (hL.inv i hlt k hk).1,
      relOK_eq hs hvm hBS hb hxs hXP hrels hA hp, Bool.or_eq_true, Bool.not_eq_true']
    by_cases hr : relM vm VG BS XP rels i A (PT i k) = false
    · exact Or.inl hr
    right
    rw [Bool.not_eq_false] at hr
    have hinv : mmul d (mmul d (TM i k) A) (mmul d AI (TIM i k)) = idM d :=
      mmul_inv_cancel hs.hd (hL.inv i hlt k hk).2.2.1 hAI
    have hA' := maps_mmul (hL.inv i hlt k hk).1 hA
    rw [ptailM] at h
    cases hf : PVf i with
    | false =>
      rw [hf, Bool.cond_false] at h
      have hk' := allN_spec h k hk
      rw [hr, Bool.not_true, Bool.false_or, hmm, hmm] at hk'
      exact ih _ _ _ (by omega) hA' hinv hk'
    | true =>
      rw [hf, Bool.cond_true, strictB_eq', strictB_eq'] at h
      obtain ⟨hmem, hli⟩ := hpv i hlt hf
      have hrel := List.all_eq_true.1 hr _ hmem
      have hmax : max (PVl i) i = i := max_eq_right hli.le
      simp only [hmax, decide_true, Bool.not_true, Bool.false_or, Nat.beq_eq] at hrel
      unfold relVecM at hrel
      rw [blt_eq_decide, blt_eq_decide, decide_eq_false (lt_irrefl i), decide_eq_true hli] at hrel
      change vm (VG (PT i k)) A = vm (vm (VG (BS (PVl i))) A) (XP (PVe i)) at hrel
      have hw : vm (vm (vm (VG (BS (PVl i))) A) (XP (PVe i))) AI = VG (PT i k) := by
        rw [← hrel, hvm, hvm, ← vmul_mmul, hAI,
          vmul_idM hs.hd (hs.lt _ (hs.mem hp))]
      rw [hw, hs.lk _ hp, hL.pos_pts i hlt k hk] at h
      rw [blt_eq_decide, blt_eq_decide, decide_eq_true hp, decide_eq_true hk, Nat.beq_refl, hr,
        hmm, hmm] at h
      simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h
      exact ih _ _ _ (by omega) hA' hinv h

end CFSG.RankThree.Native.F2

end
