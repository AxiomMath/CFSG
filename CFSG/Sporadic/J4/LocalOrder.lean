module

public import CFSG.Sporadic.J4.GlobalSpec
public import CFSG.Perm.ChainSpec
import Certificates.Data.CFSGNative.J4.Tables
import Certificates.Data.CFSGNative.J4.Chain
import Certificates.Data.CFSGNative.J4.Cert
import Certificates.Data.CFSGNative.Perm.Chain
import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

theorem smul_mem_of_inv_gens {G Y : Type*} [Group G] [Finite G] [MulAction G Y] {s : Set G}
    {S : Set Y} (hs : ∀ g ∈ s, ∀ v ∈ S, g⁻¹ • v ∈ S) :
    ∀ g ∈ Subgroup.closure s, ∀ v ∈ S, g • v ∈ S := by
  intro g hg
  rw [← Subgroup.closure_inv] at hg
  have hg' : g ∈ Submonoid.closure s⁻¹ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    intro v hv
    have := hs x⁻¹ hx v hv
    rwa [inv_inv] at this
  | one => intro v hv; rwa [one_smul]
  | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy v hv)

@[expose] noncomputable def vecO (p : ℕ) : Row := toRow (O0.pts[p]!).toVec

noncomputable abbrev posImg (g p : ℕ) : ℕ :=
  vfind O0.pts O0.slots O0.bits (frApply tx0[g]! O0.pts[p]!) - 1

structure O0Facts : Prop where
  ok : vorbOK tx0 (rdV2 bs0.keys 24) O0 15180 = true
  mat : MatFacts

section O0

variable (hO : O0Facts)
include hO

theorem tx0_size : tx0.size = 3 := by rw [tx0, Array.size_map]; exact hO.mat.locSize

theorem o0_size : O0.pts.size = 15180 := by
  have h := hO.ok
  unfold vorbOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

theorem o0_at {q : ℕ} (hq : q < 15180) : vorbAt tx0 O0 q = true := by
  have h := hO.ok
  unfold vorbOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 q (List.mem_range.2 hq)

theorem o0_wf {q : ℕ} (hq : q < 15180) : (O0.pts[q]!).wf = true := by
  have h := o0_at hO hq
  unfold vorbAt at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem o0_find {q : ℕ} (hq : q < 15180) : vfind O0.pts O0.slots O0.bits O0.pts[q]! = q + 1 := by
  have h := o0_at hO hq
  unfold vorbAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem posImg_spec {g p : ℕ} (hg : g < 3) (hp : p < 15180) :
    posImg g p < 15180 ∧ O0.pts[posImg g p]! = frApply tx0[g]! O0.pts[p]! := by
  have h := o0_at hO hp
  unfold vorbAt at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2 g (by rw [tx0_size hO]; exact hg)
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, V2.beq_iff] at this
  obtain ⟨⟨h0, hle⟩, heq⟩ := this
  rw [o0_size hO] at hle
  refine ⟨?_, heq⟩
  show vfind O0.pts O0.slots O0.bits (frApply tx0[g]! O0.pts[p]!) - 1 < 15180
  omega

theorem tx0_get {g : ℕ} (hg : g < 3) : tx0[g]! = frTable ((locMats ())[g]?.getD idRows) := by
  have hs := hO.mat.locSize
  rw [tx0, getElem!_pos _ g (by rw [Array.size_map, hs]; exact hg), Array.getElem_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hg), Option.getD_some]

theorem xJ_inv_smul_vecO {g p : ℕ} (hg : g < 3) (hp : p < 15180) :
    (xJ g)⁻¹ • vecO p = vecO (posImg g p) := by
  rw [← ofRow_inj, xJ_inv_smul hO.mat]
  show (O0.pts[p]!).toVec ᵥ* _ = (O0.pts[posImg g p]!).toVec
  rw [(posImg_spec hO hg hp).2, tx0_get hO hg, frApply_toVec_eq_vecMul]

theorem vecO_injective {p q : ℕ} (hp : p < 15180) (hq : q < 15180) (h : vecO p = vecO q) :
    p = q := by
  have e : O0.pts[p]! = O0.pts[q]! := V2.eq_of_toVec_eq (o0_wf hO hp) (o0_wf hO hq) h
  have := o0_find hO hp
  rw [e, o0_find hO hq] at this
  omega

noncomputable abbrev o0Set : Set Row := vecO '' Set.Iio 15180

theorem smul_mem_o0Set : ∀ g ∈ Hj, ∀ v ∈ o0Set, g • v ∈ o0Set := by
  refine smul_mem_of_inv_gens fun g hg v hv => ?_
  obtain ⟨p, hp, rfl⟩ := hv
  have hk : ∃ k < 3, g = xJ k := by
    rcases hg with h | h | h
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨k, hk, rfl⟩ := hk
  exact ⟨_, (posImg_spec hO hk hp).1, (xJ_inv_smul_vecO hO hk hp).symm⟩

end O0

@[expose] noncomputable def o0Sub (hO : O0Facts) : SubMulAction Hj Row where
  carrier := o0Set
  smul_mem' g _ hv := smul_mem_o0Set hO g.1 g.2 _ hv

@[expose] noncomputable def o0Equiv (hO : O0Facts) : Fin 15180 ≃ o0Sub hO :=
  Equiv.ofBijective (fun p => ⟨vecO p, ⟨p, p.isLt, rfl⟩⟩)
    ⟨fun p q h => Fin.ext (vecO_injective hO p.isLt q.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨p, hp, rfl⟩⟩
      exact ⟨⟨p, hp⟩, rfl⟩⟩

noncomputable instance o0Action : MulAction Hj (Fin 15180) where
  smul g p := by
    classical
    exact if h : O0Facts then (o0Equiv h).symm (g • o0Equiv h p) else p
  one_smul p := by
    classical
    show (if h : O0Facts then (o0Equiv h).symm ((1 : Hj) • o0Equiv h p) else p) = p
    split
    · rw [one_smul, Equiv.symm_apply_apply]
    · rfl
  mul_smul g h p := by
    classical
    show (if hF : O0Facts then (o0Equiv hF).symm ((g * h) • o0Equiv hF p) else p) =
      (if hF : O0Facts then (o0Equiv hF).symm (g • o0Equiv hF
        (if hF : O0Facts then (o0Equiv hF).symm (h • o0Equiv hF p) else p)) else
        (if hF : O0Facts then (o0Equiv hF).symm (h • o0Equiv hF p) else p))
    split
    · rw [Equiv.apply_symm_apply, mul_smul]
    · rfl

section Act

variable (hO : O0Facts)
include hO

theorem vecO_smul (g : Hj) (p : Fin 15180) : vecO (g • p : Fin 15180) = (g : J) • vecO p := by
  have : (g • p : Fin 15180) = (o0Equiv hO).symm (g • o0Equiv hO p) := by
    classical
    show (if h : O0Facts then (o0Equiv h).symm (g • o0Equiv h p) else p) = _
    rw [dite_eq_left hO]
  have e := congrArg Subtype.val (congrArg (o0Equiv hO) this)
  rw [Equiv.apply_symm_apply] at e
  exact e

theorem idxO_eq_iff {g : Hj} {p q : ℕ} (hp : p < 15180) (hq : q < 15180) :
    idx 15180 g p = q ↔ (g : J) • vecO p = vecO q := by
  rw [idx, dite_eq_left hp]
  constructor
  · intro h
    have := vecO_smul hO g ⟨p, hp⟩
    rw [h] at this
    exact this.symm
  · intro h
    have e := vecO_smul hO g ⟨p, hp⟩
    rw [h] at e
    exact vecO_injective hO (g • (⟨p, hp⟩ : Fin 15180)).isLt hq e

noncomputable abbrev gq (k : ℕ) : Hj := if hk : k < 3 then ⟨(xJ k)⁻¹, Hj.inv_mem (xJ_mem hk)⟩ else 1

theorem rep_posTable {k : ℕ} (hk : k < 3) : Rep 15180 (posTable O0 tx0[k]!) (gq k) := by
  intro p hp
  have hps : p < O0.pts.size := by rw [o0_size hO]; exact hp
  obtain ⟨hlt, -⟩ := posImg_spec hO hk hp
  unfold posTable ap
  rw [getElem!_pos _ p (by rw [Array.size_map]; exact hps), Array.getElem_map,
    ← getElem!_pos O0.pts p hps, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (by norm_num))]
  symm
  rw [idxO_eq_iff hO hp hlt]
  simp only [gq, dite_eq_left hk]
  exact xJ_inv_smul_vecO hO hk hp

end Act

noncomputable abbrev gens0 : Array Table := tx0.map (posTable O0)

noncomputable abbrev invs0 : Array Table := gens0.map (invT 15180)

noncomputable abbrev gensT (l : ℤ) : Table :=
  if 0 < l then gens0[l.toNat - 1]?.getD (idT 15180) else invs0[(-l).toNat - 1]?.getD (idT 15180)

noncomputable abbrev strong0 : Array Table := strongTables 15180 gens0 chainWords

noncomputable abbrev gensG (l : ℤ) : Hj :=
  if 0 < l then gq (l.toNat - 1) else (gq ((-l).toNat - 1))⁻¹

noncomputable abbrev gs0 (j : ℕ) : Hj :=
  if j < 3 then gq j else wordG gensG (chainWords[j - 3]?.getD [])

theorem letters0_eq : letters0 = chainLetters 15180 strong0 := rfl

theorem gens0_size (hM : MatFacts) : gens0.size = 3 := by
  rw [gens0, Array.size_map, tx0, Array.size_map]; exact hM.locSize

theorem strong0_size (hM : MatFacts) : strong0.size = 3 + chainWords.length := by
  rw [strong0, strongTables, Array.size_append, gens0_size hM, List.size_toArray, List.length_map]

theorem letters0_size : letters0.size = 2 * strong0.size := by
  rw [letters0_eq, chainLetters, Array.size_ofFn]

theorem letters0_even {j : ℕ} (hj : j < strong0.size) : letters0[2 * j]! = strong0[j]! := by
  rw [letters0_eq, chainLetters, getElem!_pos _ _ (by rw [Array.size_ofFn]; omega),
    Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 1
  omega

theorem letters0_odd {j : ℕ} (hj : j < strong0.size) :
    letters0[2 * j + 1]! = invT 15180 strong0[j]! := by
  rw [letters0_eq, chainLetters, getElem!_pos _ _ (by rw [Array.size_ofFn]; omega),
    Array.getElem_ofFn]
  simp only
  rw [ite_eq_right (by omega)]
  congr 2
  omega

theorem strong0_lt (hM : MatFacts) {j : ℕ} (hj : j < 3) : strong0[j]! = gens0[j]! := by
  rw [strong0, strongTables, getElem!_pos _ _ (by rw [Array.size_append, gens0_size hM]; omega),
    Array.getElem_append_left (by rw [gens0_size hM]; exact hj),
    getElem!_pos _ _ (by rw [gens0_size hM]; exact hj)]

theorem strong0_ge (hM : MatFacts) {j : ℕ} (hj : 3 ≤ j) (hj' : j < strong0.size) :
    strong0[j]! = wordT 15180 gensT (chainWords[j - 3]?.getD []) := by
  have hs := strong0_size hM
  have hw : j - 3 < chainWords.length := by omega
  rw [strong0, strongTables, getElem!_pos _ _ (by
      rw [Array.size_append, gens0_size hM, List.size_toArray, List.length_map]; omega),
    Array.getElem_append_right (by rw [gens0_size hM]; exact hj)]
  simp only [gens0_size hM, List.getElem_toArray, List.getElem_map,
    List.getElem?_eq_getElem hw, Option.getD_some]

section Chain

variable (hF : J4NativeFacts)
include hF

theorem J4NativeFacts.o0Facts : O0Facts := ⟨hF.o0, hF.mat⟩

theorem chain_inv {j : ℕ} (hj : j < strong0.size) :
    invOK 15180 letters0[2 * j]! letters0[2 * j + 1]! = true :=
  (chainOK_parts hF.chain).2.1 j (by rw [letters0_size]; omega)

theorem rep_gens0 {k : ℕ} (hk : k < 3) : Rep 15180 gens0[k]! (gq k) := by
  rw [gens0, getElem!_pos _ _ (by rw [Array.size_map, tx0_size hF.o0Facts]; exact hk),
    Array.getElem_map, ← getElem!_pos tx0 k (by rw [tx0_size hF.o0Facts]; exact hk)]
  exact rep_posTable hF.o0Facts hk

theorem rep_invs0 {k : ℕ} (hk : k < 3) : Rep 15180 invs0[k]! (gq k)⁻¹ := by
  have hs := strong0_size hF.mat
  have h := chain_inv hF (j := k) (by omega)
  rw [letters0_even (by omega), letters0_odd (by omega), strong0_lt hF.mat hk] at h
  have e : invs0[k]! = invT 15180 gens0[k]! := by
    rw [invs0, getElem!_pos _ _ (by rw [Array.size_map, gens0_size hF.mat]; exact hk),
      Array.getElem_map, ← getElem!_pos gens0 k (by rw [gens0_size hF.mat]; exact hk)]
  rw [e]
  exact Rep.inv_of_invOK (rep_gens0 hF hk) h

theorem rep_gensT (l : ℤ) : Rep 15180 (gensT l) (gensG l) := by
  have hg := gens0_size hF.mat
  have hi : invs0.size = 3 := by rw [invs0, Array.size_map, hg]
  unfold gensT gensG
  split_ifs with hl
  · by_cases hk : l.toNat - 1 < 3
    · rw [Array.getElem?_eq_getElem (by omega), Option.getD_some,
        ← getElem!_pos gens0 _ (by omega)]
      exact rep_gens0 hF hk
    · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
      simp only [gq, dite_eq_right hk]
      exact Rep.idT (by norm_num)
  · by_cases hk : (-l).toNat - 1 < 3
    · rw [Array.getElem?_eq_getElem (by omega), Option.getD_some,
        ← getElem!_pos invs0 _ (by omega)]
      exact rep_invs0 hF hk
    · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
      simp only [gq, dite_eq_right hk, inv_one]
      exact Rep.idT (by norm_num)

theorem rep_strong0 : ∀ j < letters0.size / 2, Rep 15180 letters0[2 * j]! (gs0 j) := by
  intro j hj
  rw [letters0_size] at hj
  have hj' : j < strong0.size := by omega
  rw [letters0_even hj']
  by_cases h3 : j < 3
  · rw [strong0_lt hF.mat h3]
    simp only [gs0, ite_eq_left h3]
    exact rep_gens0 hF h3
  · rw [strong0_ge hF.mat (by omega) hj']
    simp only [gs0, ite_eq_right h3]
    exact Rep.wordT (by norm_num) _ fun l _ => rep_gensT hF l

theorem eq_one_of_fix_qIdx0 {g : J} (hg0 : idx nPts g 0 = 0)
    (hgq : ∀ t < qIdx0.size, idx nPts g qIdx0[t]! = qIdx0[t]!) : g = 1 := by
  refine eq_one_of_fix_tuple hF.orbitFacts (qIdx0_lt hF) hF.sig ?_ hF.basis hg0 hgq
  intro t ht
  have h := hF.blt
  rw [Array.all_eq_true] at h
  rw [getElem!_pos basisIdx t ht]
  exact of_decide_eq_true (h t ht)

theorem vecAt_qIdx0 {t : ℕ} (ht : t < qLen) : vecAt qIdx0[t]! = vecO t := by
  have h := hF.q
  rw [List.all_eq_true] at h
  have := h t (List.mem_range.2 ht)
  rw [Bool.and_eq_true, V2.beq_iff] at this
  unfold vecAt vecO
  rw [this.2]

theorem hsep0 : ∀ g : Hj, (∀ t < (Array.range qLen).size,
    idx 15180 g (Array.range qLen)[t]! = (Array.range qLen)[t]!) → g = 1 := by
  intro g hg
  have hq := hF.qsize
  apply Subtype.ext
  apply eq_one_of_fix_qIdx0 hF (idx_Hj hF g.2)
  intro t ht
  have ht' : t < qLen := by rw [← hq]; exact ht
  have hfix := hg t (by rw [Array.size_range]; exact ht')
  rw [getElem!_pos _ t (by rw [Array.size_range]; exact ht'), Array.getElem_range] at hfix
  have hO := hF.o0Facts
  have h25 : t < 15180 := by unfold qLen at ht'; omega
  rw [idxO_eq_iff hO h25 h25] at hfix
  have hlt := qIdx0_lt hF t ht
  rw [idx_eq_iff hF.orbitFacts hlt hlt, vecAt_qIdx0 hF ht']
  exact hfix

theorem level0_top : levelGroup letters0 chainBase (pairG gs0) 0 = ⊤ := by
  rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := ({xJ 0, xJ 1, xJ 2} : Set J)),
    Subgroup.closure_le]
  intro x hx
  have hk : ∃ k < 3, (x : J) = xJ k := by
    rcases hx with h | h | h
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨k, hk, hxk⟩ := hk
  have e : x = (gq k)⁻¹ := Subtype.ext (by simp [gq, dite_eq_left hk, hxk])
  rw [e]
  apply Subgroup.inv_mem
  have hs := strong0_size hF.mat
  have hl : 2 * k ∈ levelLetters letters0 chainBase 0 := by
    rw [levelLetters, Array.mem_range, letters0_size]
    omega
  have := lG_mem (lG := pairG gs0) hl
  have e2 : pairG gs0 (2 * k) = gq k := by
    simp only [pairG, gs0]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    congr 1
    omega
  rw [e2] at this
  exact this

theorem trees0_size_at : ∀ l < 6, trees0[l]!.pts.size = chainSizes[l]! := by
  have hs := hF.sizes
  have hlen : trees0.size = 6 := by
    have := congrArg List.length hs
    simpa [orbitSizes, chainSizes] using this
  intro l hl
  rw [← hs, orbitSizes,
    getElem!_pos (trees0.toList.map fun T => T.pts.size) l (by simp [hlen]; exact hl),
    List.getElem_map, Array.getElem_toList, ← getElem!_pos trees0 l (by rw [hlen]; exact hl)]

theorem card_Hj_N : Nat.card Hj = 501397585920 := by
  have h := (chain_facts (G := Hj) (n := 15180) (gs := gs0) (rep_strong0 hF) (hsep0 hF)
    hF.chain).2.2 0 (Nat.zero_le _)
  rw [level0_top hF, Subgroup.card_top] at h
  rw [h, show chainBase.size = 6 from rfl, ← Finset.range_eq_Ico,
    Finset.prod_congr rfl fun l hl => trees0_size_at hF l (Finset.mem_range.1 hl)]
  decide

end Chain

theorem card_Hj (hF : J4Facts) : Nat.card Hj = 501397585920 := hF.cardHj

end CFSG.Sporadic.J4
