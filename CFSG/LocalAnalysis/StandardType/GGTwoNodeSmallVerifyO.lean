module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallWord
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallChain

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pwo_foldr_congr {α : Type*} {l : List α} {f g : α → ℕ → ℕ} {init : ℕ}
    (h : ∀ x ∈ l, f x = g x) : l.foldr f init = l.foldr g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private lemma pwo_ent_of_vec_eq (P : Pt) [Fact P.p.Prime] {a b : Vec} (h : P.vec a = P.vec b)
    (j : ℕ) (hj : j < P.D) : P.ent a j = P.ent b j := by
  have hc : (P.ent a j : ZMod P.p) = (P.ent b j : ZMod P.p) := by
    have hv := congrFun h ⟨j, hj⟩
    calc (P.ent a j : ZMod P.p) = P.vec a ⟨j, hj⟩ := by
          rw [Pt.vec]; exact (CharP.cast_eq_mod (ZMod P.p) P.p (a.getD j 0)).symm
      _ = P.vec b ⟨j, hj⟩ := hv
      _ = (P.ent b j : ZMod P.p) := by
          rw [Pt.vec]; exact CharP.cast_eq_mod (ZMod P.p) P.p (b.getD j 0)
  have hmod : P.ent a j % P.p = P.ent b j % P.p := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
  simpa [Pt.ent, Nat.mod_mod] using hmod

private lemma pwo_code_eq_of_vec_eq (P : Pt) [Fact P.p.Prime] {a b : Vec} (h : P.vec a = P.vec b) :
    P.code a = P.code b := by
  unfold Pt.code
  apply pwo_foldr_congr
  intro j hj
  rw [List.mem_range] at hj
  funext acc
  rw [pwo_ent_of_vec_eq P h j hj]

private lemma pwo_vec_of_vecEq (P : Pt) [Fact P.p.Prime] {a b : Vec} (h : P.vecEq a b = true) :
    P.vec a = P.vec b := by
  funext i
  have hp := (List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt)
  have he : P.ent a i.val = P.ent b i.val := by simpa using hp
  calc P.vec a i = (P.ent a i.val : ZMod P.p) := by
        rw [Pt.vec]; exact CharP.cast_eq_mod (ZMod P.p) P.p (a.getD i.val 0)
    _ = (P.ent b i.val : ZMod P.p) := by rw [he]
    _ = P.vec b i := by
        rw [Pt.vec]; exact (CharP.cast_eq_mod (ZMod P.p) P.p (b.getD i.val 0)).symm

private lemma pwo_eraseDups_sublist {α : Type*} [BEq α] (l : List α) : l.eraseDups.Sublist l := by
  suffices H : ∀ n, ∀ (l : List α), l.length = n → l.eraseDups.Sublist l from H l.length l rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro m ih l hl
  cases l with
  | nil => exact List.Sublist.slnil
  | cons a l =>
      rw [List.eraseDups_cons]
      refine List.Sublist.cons₂ a ?_
      have hrec : (l.filter (fun b => !b == a)).eraseDups.Sublist (l.filter (fun b => !b == a)) :=
        ih (l.filter (fun b => !b == a)).length (by
          have h1 : (l.filter (fun b => !b == a)).length ≤ l.length := List.length_filter_le _ _
          have h2 : l.length < (a :: l).length := by rw [List.length_cons]; omega
          omega) (l.filter (fun b => !b == a)) rfl
      exact List.Sublist.trans hrec List.filter_sublist

private lemma pwo_nodup_of_eraseDups_length {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.length = l.length → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
      intro h
      have hp : (l.filter (fun b => !b == a)).eraseDups.length = l.length := by
        have h' := h
        rw [List.eraseDups_cons, List.length_cons, List.length_cons,
          Nat.add_right_cancel_iff] at h'
        exact h'
      have hflen : (l.filter (fun b => !b == a)).length = l.length := by
        apply le_antisymm (List.length_filter_le _ _)
        calc l.length = (l.filter (fun b => !b == a)).eraseDups.length := hp.symm
          _ ≤ (l.filter (fun b => !b == a)).length :=
              (pwo_eraseDups_sublist (l.filter (fun b => !b == a))).length_le
      have hfeq : l.filter (fun b => !b == a) = l :=
        List.filter_sublist.eq_of_length hflen
      have hl : l.eraseDups.length = l.length := by
        rw [← hfeq, hflen]; exact hp
      have hlnod : l.Nodup := ih hl
      have hane : a ∉ l := by
        intro ham
        have hmem : a ∈ l.filter (fun b => !b == a) := by rw [hfeq]; exact ham
        have hc : (!(a == a) : Bool) = true := (List.mem_filter.mp hmem).2
        simpa using hc
      exact List.nodup_cons.mpr ⟨hane, hlnod⟩

private lemma pwo_mem_zipIdx_get {α : Type*} (l : List α) (i : Fin l.length) :
    (l.get i, i.val) ∈ l.zipIdx := by
  have hlen : i.val < (l.zipIdx 0).length := by rw [List.length_zipIdx]; exact i.isLt
  have hmem := List.getElem_mem hlen
  rw [List.getElem_zipIdx] at hmem
  simpa [List.get_eq_getElem, Nat.zero_add] using hmem

private structure pwo_Good (P : Pt) (E : List Vec) (L : Level) : Prop where
  wordOK : ∀ s ∈ L.strong, P.wordOK s = true
  fix : ∀ s ∈ L.strong, ∀ b ∈ E, P.vecEq (P.applyWord s b) b = true
  ne_nil : L.tree ≠ []
  head : ∀ e0 rest, L.tree = e0 :: rest → P.vecEq e0.1 L.base = true
  edge : ∀ e idx, (e, idx) ∈ L.tree.zipIdx → idx ≠ 0 →
    e.2.1 < idx ∧ e.2.2 < L.strong.length ∧
      P.vecEq e.1 (P.applyWord (L.strong.getD e.2.2 []) ((L.tree.getD e.2.1 ([], 0, 0)).1)) = true
  code : (L.tree.map fun e => P.code e.1).eraseDups.length = L.tree.length

private lemma pwo_levelOK_good (P : Pt) (E : List Vec) (L : Level)
    (h : P.levelOK E L = true) : pwo_Good P E L := by
  have hne : L.tree ≠ [] := by
    intro hnil
    have h'' : False := by simpa [Pt.levelOK, hnil] using h
    exact h''
  obtain ⟨e0, rest, htree⟩ := List.exists_cons_of_ne_nil hne
  have h1 := h
  simp only [Pt.levelOK, htree] at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h1
  refine ⟨?_, ?_, hne, ?_, ?_, ?_⟩
  · exact List.all_eq_true.mp hA
  · intro s hs
    exact List.all_eq_true.mp (List.all_eq_true.mp hB s hs)
  · intro e0' rest' hh
    have hinj := List.cons.inj (hh.symm.trans htree)
    rw [hinj.1]
    exact hC
  · intro e idx hmem hne0
    have hmem' : (e, idx) ∈ (e0 :: rest).zipIdx := by rw [← htree]; exact hmem
    have hcond := List.all_eq_true.mp hD (e, idx) hmem'
    dsimp only at hcond
    rw [Bool.or_eq_true] at hcond
    rcases hcond with h0 | hrest
    · exact absurd (by simpa using h0) hne0
    · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hrest
      exact ⟨hrest.1.1, hrest.1.2, by simpa [← htree] using hrest.2⟩
  · have hcodeeq : ((e0 :: rest).map fun e => P.code e.1).eraseDups.length = (e0 :: rest).length := by
      simpa using hE
    simpa [← htree] using hcodeeq

private def pwo_S (P : Pt) (L : Level) : Set (P.V ≃ₗ[ZMod P.p] P.V) :=
  {γ | γ ∈ P.group ∧ ∃ s ∈ L.strong, ∀ v : Vec, γ (P.vec v) = P.vec (P.applyWord s v)}

private def pwo_O (P : Pt) (L : Level) : Finset P.V :=
  (L.tree.map fun e => P.vec e.1).toFinset

private lemma pwo_smul_mem_orbit {G α : Type*} [Group G] [MulAction G α]
    (H : Subgroup G) {a x : α} (hx : x ∈ MulAction.orbit H a) (g : H) :
    g • x ∈ MulAction.orbit H a := by
  obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.mp hx
  exact MulAction.mem_orbit_iff.mpr ⟨g * δ, by rw [mul_smul, hδ]⟩

private lemma pwo_tree_orbit (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (L : Level) {E : List Vec}
    (h : pwo_Good P E L) :
    ∀ v ∈ pwo_O P L, v ∈ MulAction.orbit (Subgroup.closure (pwo_S P L)) (P.vec L.base) := by
  intro v hv
  rw [pwo_O, List.mem_toFinset, List.mem_map] at hv
  obtain ⟨e, he, rfl⟩ := hv
  rw [List.mem_iff_get] at he
  obtain ⟨i, hi⟩ := he
  subst hi
  have key : ∀ (n : ℕ) (hn : n < L.tree.length),
      P.vec (L.tree.get ⟨n, hn⟩).1 ∈
        MulAction.orbit (Subgroup.closure (pwo_S P L)) (P.vec L.base) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro m ih hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      obtain ⟨e0, rest, htree⟩ := List.exists_cons_of_ne_nil h.ne_nil
      have hv0 : P.vec e0.1 = P.vec L.base := pwo_vec_of_vecEq P (h.head e0 rest htree)
      have hget0 : L.tree.get ⟨0, hm⟩ = e0 := by
        rw [List.get_eq_getElem]
        have h1 := List.getElem?_eq_getElem hm
        have h2 : L.tree[0]? = some e0 := by rw [htree]; rfl
        rw [h1] at h2
        exact Option.some.inj h2
      rw [hget0, hv0]
      exact MulAction.mem_orbit_self _
    · have hmne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
      let e := L.tree.get ⟨m, hm⟩
      change P.vec e.1 ∈ MulAction.orbit (Subgroup.closure (pwo_S P L)) (P.vec L.base)
      have hmem : (e, m) ∈ L.tree.zipIdx := by
        change (L.tree.get ⟨m, hm⟩, m) ∈ L.tree.zipIdx
        exact pwo_mem_zipIdx_get L.tree ⟨m, hm⟩
      obtain ⟨hpar, hgen, hveq⟩ := h.edge e m hmem hmne
      have hi_lt : e.2.1 < L.tree.length := lt_trans hpar hm
      have hparent : L.tree.getD e.2.1 ([], 0, 0) = L.tree.get ⟨e.2.1, hi_lt⟩ := by
        rw [List.getD_eq_getElem _ _ hi_lt, List.get_eq_getElem]
      have hgen' : L.strong.getD e.2.2 [] = L.strong.get ⟨e.2.2, hgen⟩ := by
        rw [List.getD_eq_getElem _ _ hgen, List.get_eq_getElem]
      have hvec : P.vec e.1 =
          P.vec (P.applyWord (L.strong.get ⟨e.2.2, hgen⟩) (L.tree.get ⟨e.2.1, hi_lt⟩).1) := by
        have hp := pwo_vec_of_vecEq P hveq
        rwa [hparent, hgen'] at hp
      have hmemgen : L.strong.get ⟨e.2.2, hgen⟩ ∈ L.strong := by
        rw [List.get_eq_getElem]; exact List.getElem_mem (l := L.strong) hgen
      have hwordOK : P.wordOK (L.strong.get ⟨e.2.2, hgen⟩) = true := h.wordOK _ hmemgen
      obtain ⟨γ, hγmem, hγspec⟩ :=
        Pt.applyWord_spec P hwf (L.strong.get ⟨e.2.2, hgen⟩) hwordOK
      have hγS : γ ∈ pwo_S P L := ⟨hγmem, _, hmemgen, hγspec⟩
      have hpar_orbit : P.vec (L.tree.get ⟨e.2.1, hi_lt⟩).1 ∈
          MulAction.orbit (Subgroup.closure (pwo_S P L)) (P.vec L.base) := ih e.2.1 hpar hi_lt
      have hgoal : P.vec e.1 = γ (P.vec (L.tree.get ⟨e.2.1, hi_lt⟩).1) :=
        hvec.trans (hγspec _).symm
      let γH : Subgroup.closure (pwo_S P L) := ⟨γ, Subgroup.subset_closure hγS⟩
      have hgx : γH • (P.vec (L.tree.get ⟨e.2.1, hi_lt⟩).1) =
          γ (P.vec (L.tree.get ⟨e.2.1, hi_lt⟩).1) := by
        rw [Subgroup.smul_def]; rfl
      rw [hgoal, ← hgx]
      exact pwo_smul_mem_orbit _ hpar_orbit γH
  exact key i i.isLt

private lemma pwo_O_card (P : Pt) [Fact P.p.Prime] (L : Level) {E : List Vec}
    (h : pwo_Good P E L) : (pwo_O P L).card = L.tree.length := by
  have hcodes : (L.tree.map fun e => P.code e.1).Nodup := by
    apply pwo_nodup_of_eraseDups_length
    rw [List.length_map]
    exact h.code
  have htree_nodup : L.tree.Nodup := List.Nodup.of_map _ hcodes
  have hinjCode : ∀ a ∈ L.tree, ∀ b ∈ L.tree, P.code a.1 = P.code b.1 → a = b :=
    (List.nodup_map_iff_inj_on htree_nodup).mp hcodes
  have hinjVec : ∀ a ∈ L.tree, ∀ b ∈ L.tree, P.vec a.1 = P.vec b.1 → a = b :=
    fun a ha b hb hv => hinjCode a ha b hb (pwo_code_eq_of_vec_eq P hv)
  have hnodup : (L.tree.map fun e => P.vec e.1).Nodup :=
    (List.nodup_map_iff_inj_on htree_nodup).mpr hinjVec
  rw [pwo_O, List.toFinset_card_of_nodup hnodup, List.length_map]

private lemma pwo_fin_prod_get {α : Type*} (l : List α) (f : α → ℕ) :
    (∏ i : Fin l.length, f (l.get i)) = (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons]
      change (∏ i : Fin (l.length + 1), f ((a :: l).get i)) = f a * (l.map f).prod
      rw [Fin.prod_univ_succ, List.get_cons_zero]
      have hstep : (∏ i : Fin l.length, f ((a :: l).get i.succ)) =
          ∏ i : Fin l.length, f (l.get i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
      rw [hstep, ih]

private lemma pwo_chainProd_spec (P : Pt) :
    ∀ (Ls : List Level) (E : List Vec) (acc n : ℕ),
      P.chainProd E Ls acc = some n →
      n = acc * (Ls.map (fun L => L.tree.length)).prod ∧
      ∀ i : Fin Ls.length,
        P.levelOK (E ++ (Ls.take i.val).map (fun L => L.base)) (Ls.get i) = true := by
  intro Ls
  induction Ls with
  | nil =>
      intro E acc n h
      simp only [Pt.chainProd] at h
      injection h with hn
      refine ⟨?_, ?_⟩
      · rw [← hn]; simp
      · intro i; exact Fin.elim0 i
  | cons L Ls ih =>
      intro E acc n h
      simp only [Pt.chainProd] at h
      by_cases hL : P.levelOK E L = true
      · rw [if_pos hL] at h
        obtain ⟨hn, hgood⟩ := ih (E ++ [L.base]) (acc * L.tree.length) n h
        refine ⟨?_, ?_⟩
        · rw [hn]
          simp only [List.map_cons, List.prod_cons]
          ring
        · intro i
          rcases i with ⟨v, hv⟩
          cases v with
          | zero => simpa using hL
          | succ k =>
              have hk : k < Ls.length := by
                simp only [List.length_cons] at hv; omega
              have := hgood ⟨k, hk⟩
              simpa [List.take_succ_cons, List.map_cons, List.get_cons_succ, List.append_assoc]
                using this
      · rw [if_neg hL] at h
        simp at h

theorem verifyO_sound {P : Pt} [Fact P.p.Prime] (hwf : P.WF) {o : OWit} {b : ℕ}
    (h : verifyO P o b = true) : b < Nat.card P.group := by
  haveI : NeZero P.p := ⟨(Fact.out : P.p.Prime).ne_zero⟩
  unfold verifyO at h
  cases hc : P.chainProd [] o.levels 1 with
  | none =>
      rw [hc] at h
      exact absurd h (by simp)
  | some n =>
      rw [hc] at h
      simp only [decide_eq_true_eq] at h
      obtain ⟨hn, hgood⟩ := pwo_chainProd_spec P o.levels [] 1 n hc
      have hgoodG : ∀ k : Fin o.levels.length,
          pwo_Good P ((o.levels.take k.val).map fun L => L.base) (o.levels.get k) :=
        fun k => pwo_levelOK_good P _ _ (by simpa using hgood k)
      have hnp : (o.levels.map fun L => L.tree.length).prod = n := by
        rw [hn]; simp
      let bvec : Fin o.levels.length → P.V := fun k => P.vec (o.levels.get k).base
      let S : Fin o.levels.length → Set (P.V ≃ₗ[ZMod P.p] P.V) :=
        fun k => pwo_S P (o.levels.get k)
      let O : Fin o.levels.length → Finset P.V := fun k => pwo_O P (o.levels.get k)
      have hS : ∀ k, S k ⊆ P.group := by
        intro k γ hγ
        exact (by simpa [S, pwo_S] using hγ.1)
      have hfix : ∀ k, ∀ s ∈ S k, ∀ j : Fin o.levels.length, j < k → s (bvec j) = bvec j := by
        intro k s hs j hjk
        have hs' : s ∈ pwo_S P (o.levels.get k) := by simpa [S] using hs
        obtain ⟨_, w, hw, hspec⟩ := hs'
        have hbj : (o.levels.get j).base ∈ (o.levels.take k.val).map (fun L => L.base) := by
          apply List.mem_map.mpr
          refine ⟨o.levels.get j, ?_, rfl⟩
          rw [List.get_eq_getElem]
          have hjlen : j.val < (o.levels.take k.val).length := by
            rw [List.length_take]; exact lt_min hjk j.isLt
          have hmem := List.getElem_mem (l := o.levels.take k.val) hjlen
          rw [List.getElem_take] at hmem
          exact hmem
        have hvec := pwo_vec_of_vecEq P ((hgoodG k).fix w hw (o.levels.get j).base hbj)
        show s (P.vec (o.levels.get j).base) = P.vec (o.levels.get j).base
        rw [hspec (o.levels.get j).base, hvec]
      have hO : ∀ k, ∀ v ∈ O k, v ∈ MulAction.orbit (Subgroup.closure (S k)) (bvec k) := by
        intro k v hv
        have hv' : v ∈ pwo_O P (o.levels.get k) := by simpa [O] using hv
        have := pwo_tree_orbit P hwf (o.levels.get k) (hgoodG k) v hv'
        simpa [S, bvec] using this
      have hbound : (∏ k, (O k).card) ≤ Nat.card P.group :=
        card_ge_of_orbit_chain (p := P.p) (V := P.V) (R := P.group) (m := o.levels.length)
          bvec S O hS hfix hO
      have hprodcard : ∀ k : Fin o.levels.length, (O k).card = (o.levels.get k).tree.length :=
        fun k => pwo_O_card P (o.levels.get k) (hgoodG k)
      have hprod : (∏ k : Fin o.levels.length, (O k).card) = n := by
        calc (∏ k : Fin o.levels.length, (O k).card)
            = ∏ k : Fin o.levels.length, (o.levels.get k).tree.length := by
              apply Finset.prod_congr rfl
              intro k _
              exact hprodcard k
          _ = (o.levels.map fun L => L.tree.length).prod :=
              pwo_fin_prod_get o.levels (fun L => L.tree.length)
          _ = n := hnp
      have : n ≤ Nat.card P.group := by
        rw [← hprod]
        exact hbound
      exact lt_of_lt_of_le h this

end CFSG.TwoNodeSmall
