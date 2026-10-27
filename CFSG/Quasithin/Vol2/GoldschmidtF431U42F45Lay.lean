module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Act
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers
public import Certificates.Certificate4162

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F45Ru

@[expose] def layFun (lp ll : List ℕ) : Vtx → ℕ
  | Sum.inl p => lp.getD p 0
  | Sum.inr k => ll.getD k 0

theorem mem_ptLines {p k : ℕ} : k ∈ ptLines p ↔ k < 27 ∧ p ∈ lnTab.getD k [] := by
  simp [ptLines, List.mem_filter, List.mem_range]

structure LayProps (isPt : Bool) (lp ll : List ℕ) : Prop where
  root : (if isPt then lp.getD 0 0 else ll.getD 0 0) = 0
  leP : ∀ p < 45, lp.getD p 0 ≤ 4
  leL : ∀ k < 27, ll.getD k 0 ≤ 4
  parP : ∀ p < 45, (isPt = true ∧ p = 0) ∨ ∃ k ∈ ptLines p, ll.getD k 0 + 1 = lp.getD p 0
  parL : ∀ k < 27, (isPt = false ∧ k = 0) ∨
    ∃ p ∈ lnTab.getD k [], lp.getD p 0 + 1 = ll.getD k 0
  lip : ∀ k < 27, ∀ p ∈ lnTab.getD k [],
    ll.getD k 0 ≤ lp.getD p 0 + 1 ∧ lp.getD p 0 ≤ ll.getD k 0 + 1
  uniqP : ∀ p < 45, ∀ k ∈ ptLines p, ∀ k' ∈ ptLines p, 1 ≤ lp.getD p 0 → lp.getD p 0 < 4 →
    ll.getD k 0 + 1 = lp.getD p 0 → ll.getD k' 0 + 1 = lp.getD p 0 → k = k'
  uniqL : ∀ k < 27, ∀ p ∈ lnTab.getD k [], ∀ p' ∈ lnTab.getD k [], 1 ≤ ll.getD k 0 →
    ll.getD k 0 < 4 → lp.getD p 0 + 1 = ll.getD k 0 → lp.getD p' 0 + 1 = ll.getD k 0 → p = p'

theorem layOK_spec {isPt : Bool} {lp ll : List ℕ} (h : layOK isPt lp ll = true) :
    LayProps isPt lp ll := by
  simp only [layOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨?_, fun p hp => ?_, fun k hk => ?_, fun p hp => ?_, fun k hk => ?_,
    fun k hk p hpk => ?_, fun p hp k hk k' hk' a b c d => ?_,
    fun k hk p hpk p' hpk' a b c d => ?_⟩
  · cases isPt <;> simpa using h1
  · simpa using List.all_eq_true.1 h2 p (List.mem_range.2 hp)
  · simpa using List.all_eq_true.1 h3 k (List.mem_range.2 hk)
  · have := List.all_eq_true.1 h4 p (List.mem_range.2 hp)
    simpa [List.any_eq_true] using this
  · have := List.all_eq_true.1 h5 k (List.mem_range.2 hk)
    simpa [List.any_eq_true] using this
  · have := List.all_eq_true.1 (List.all_eq_true.1 h6 k (List.mem_range.2 hk)) p hpk
    simpa using this
  · have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h7 p
      (List.mem_range.2 hp)) k hk) k' hk'
    rcases Bool.or_eq_true_iff.1 this with h | h
    · exfalso
      rw [decide_eq_true a, decide_eq_true b, beq_iff_eq.2 c, beq_iff_eq.2 d] at h
      exact absurd h (by decide)
    · exact beq_iff_eq.1 h
  · have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h8 k
      (List.mem_range.2 hk)) p hpk) p' hpk'
    rcases Bool.or_eq_true_iff.1 this with h | h
    · exfalso
      rw [decide_eq_true a, decide_eq_true b, beq_iff_eq.2 c, beq_iff_eq.2 d] at h
      exact absurd h (by decide)
    · exact beq_iff_eq.1 h

theorem layers_of_layProps {isPt : Bool} {lp ll : List ℕ}
    (h : LayProps isPt lp ll) {b : Vtx} (hb : b = if isPt then Sum.inl 0 else Sum.inr 0) :
    Layers incGraph 4 b (layFun lp ll) where
  root := by
    subst hb
    cases isPt
    · simpa [layFun] using h.root
    · simpa [layFun] using h.root
  le x := by
    rcases x with p | k
    · exact h.leP p p.2
    · exact h.leL k k.2
  parent x hx := by
    rcases x with p | k
    · rcases h.parP p p.2 with ⟨hpt, hp0⟩ | ⟨k, hk, hlay⟩
      · have hp : p = 0 := Fin.ext hp0
        exact absurd (by subst hb; simp [hpt, hp]) hx
      · obtain ⟨hk27, hpk⟩ := mem_ptLines.1 hk
        exact ⟨Sum.inr ⟨k, hk27⟩, hpk, hlay⟩
    · rcases h.parL k k.2 with ⟨hpt, hk0⟩ | ⟨p, hp, hlay⟩
      · have hk' : k = 0 := Fin.ext hk0
        exact absurd (by subst hb; simp [hpt, hk']) hx
      · exact ⟨Sum.inl ⟨p, lnTab_lt k.2 p hp⟩, hp, hlay⟩
  lip x y hxy := by
    rcases x with p | k <;> rcases y with q | l
    · exact absurd hxy (not_adj_inl_inl p q)
    · exact (h.lip l.val l.2 p.val hxy).1
    · exact (h.lip k.val k.2 q.val hxy).2
    · exact absurd hxy (not_adj_inr_inr k l)
  uniq x y z h1 h2 hxy hxz hy hz := by
    rcases x with p | k <;> rcases y with q | l <;> rcases z with q' | l'
    · exact absurd hxy (not_adj_inl_inl p q)
    · exact absurd hxy (not_adj_inl_inl p q)
    · exact absurd hxz (not_adj_inl_inl p q')
    · have hk : l.val ∈ ptLines p := mem_ptLines.2 ⟨l.2, hxy⟩
      have hk' : l'.val ∈ ptLines p := mem_ptLines.2 ⟨l'.2, hxz⟩
      exact congrArg Sum.inr (Fin.ext (h.uniqP p p.2 l hk l' hk' h1 h2 hy hz))
    · exact congrArg Sum.inl (Fin.ext (h.uniqL k k.2 q hxy q' hxz h1 h2 hy hz))
    · exact absurd hxz (not_adj_inr_inr k l')
    · exact absurd hxy (not_adj_inr_inr k l)
    · exact absurd hxy (not_adj_inr_inr k l)

theorem layers_of_layOK {isPt : Bool} {lp ll : List ℕ}
    (h : layOK isPt lp ll = true) {b : Vtx} (hb : b = if isPt then Sum.inl 0 else Sum.inr 0) :
    Layers incGraph 4 b (layFun lp ll) :=
  layers_of_layProps (layOK_spec h) hb

theorem layers_pt :
    Layers incGraph 4 (Sum.inl 0) (layFun layPt0 layLn0) :=
  layers_of_layOK (isPt := true) (by
    have h := Certificates.certificate4162.1
    simp only [chkF45Lay, Bool.and_eq_true] at h
    exact h.1.1) rfl

theorem layers_ln :
    Layers incGraph 4 (Sum.inr 0) (layFun layPt1 layLn1) :=
  layers_of_layOK (isPt := false) (by
    have h := Certificates.certificate4162.1
    simp only [chkF45Lay, Bool.and_eq_true] at h
    exact h.1.2) rfl

end CFSG.Quasithin.H13.F431.U42
