module

public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.J4.TreeSpec
public import CFSG.Sporadic.Th.GroupTheory
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Tables
import Certificates.Data.CFSGNative.J4.Global
import Certificates.Data.CFSGNative.J4.Local
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th

theorem J4NativeFacts.orbitFacts (hF : J4NativeFacts) : OrbitFacts := ⟨hF.count, hF.orbit, hF.mat⟩

theorem mem_Hj_iff {g : J} : g ∈ Hj ↔ (g : GL (Fin 112) (ZMod 2)) ∈ Hgl := by
  have hmap : Hj.map J.subtype = Hgl := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem J.subtype_injective).symm

@[expose] noncomputable def sJ (k : ℕ) : J := ⟨stabGL k, Hgl_le_J (stabGL_mem_Hgl k)⟩

theorem sJ_mem (k : ℕ) : sJ k ∈ Hj := mem_Hj_iff.2 (stabGL_mem_Hgl k)

theorem sJ_inv_smul (hM : MatFacts) (k : ℕ) (w : Row) :
    ofRow ((sJ k)⁻¹ • w) = ofRow w ᵥ* rowsMatrix ((stabMats ())[k]?.getD idRows) := by
  rw [inv_smul_row, stabMats_spec hM]; rfl

noncomputable abbrev treeL : ℕ → J := letterG (a⁻¹ : J) b⁻¹ b

noncomputable abbrev trans (j : ℕ) : J := treeElt t20.1 (a⁻¹ : J) b⁻¹ b 64 j

theorem trans_zero : trans 0 = 1 := by
  rw [trans, treeElt, ite_eq_left rfl]

theorem treeL_inv (l : ℕ) : (treeL l)⁻¹ = letterG (a : J) b b⁻¹ l := by
  show (letterG (a⁻¹ : J) b⁻¹ b l)⁻¹ = _
  unfold letterG
  split_ifs <;> simp

section Facts

variable (hF : J4NativeFacts)
include hF

theorem nPts_pos : 0 < nPts := (orbit_parts hF.orbitFacts).1

theorem rep_ta : RepT nPts bs0.alpha (a⁻¹ : J) := rep_alpha hF.orbitFacts

theorem rep_tb : RepT nPts bs0.beta (b⁻¹ : J) := rep_beta hF.orbitFacts

theorem rep_tbi : RepT nPts tbi0 (b : J) := by
  intro j hj
  have hb := rep_tb hF
  set i := idx nPts (b : J) j with hi
  have hin : i < nPts := idx_lt _ hj
  have := parAllS_eq_true hF.inv i hin
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  rw [← this.2, hb i hin, hi, idx_inv_idx]

theorem a_mul_self : (a : J) * a = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, a_coe, gA_val hF.mat, ← pow_two, matA_sq hF.mat]
  rfl

theorem a_inv_eq : (a⁻¹ : J) = a := inv_eq_of_mul_eq_one_right (a_mul_self hF)

theorem rep_ta_a : RepT nPts bs0.alpha (a : J) := by
  have := rep_ta hF
  rwa [a_inv_eq hF] at this


theorem treeFacts0 : TreeFacts nPts bs0.alpha bs0.beta tbi0 t20.1 t20.2 :=
  treeFacts_of (nPts_pos hF) hF.tree

theorem idx_trans {j : ℕ} (hj : j < nPts) : idx nPts (trans j) 0 = j :=
  idx_treeElt (treeFacts0 hF) (rep_ta hF) (rep_tb hF) (rep_tbi hF) _ j hj rfl 64
    ((treeFacts0 hF).dep_lt j hj)


theorem txi0_get {k : ℕ} (hk : k < 3) : txi0[k]! = frTable ((locInvs ())[k]?.getD idRows) := by
  have hs : (locInvs ()).size = 3 := by rw [locInvs, Array.size_map]; exact hF.mat.locSize
  rw [txi0, getElem!_pos _ k (by rw [Array.size_map, hs]; exact hk), Array.getElem_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hk), Option.getD_some]

theorem rep_z {k : ℕ} (hk : k < 3) : RepT nPts (zT k) (xJ k) := by
  have hm : matTabOK bs0.keys nPts txi0[k]! (zT k) 3 = true := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    exacts [hF.z0, hF.z1, hF.z2]
  show RepB (zT k) (xJ k)
  refine repB_of_vec hF.orbitFacts fun i hi => ?_
  have h := parAllS_eq_true hm i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, V2.beq_iff] at h
  refine ⟨h.1, ?_⟩
  rw [← ofRow_inj, xJ_smul hF.mat]
  show (rdV2 bs0.keys i).toVec ᵥ* _ = (rdV2 bs0.keys (rdU32 (zT k) i)).toVec
  rw [h.2, txi0_get hF hk, frApply_toVec_eq_vecMul]


theorem rep_invLetter (l : ℕ) :
    RepT nPts (invLetter bs0.alpha bs0.beta tbi0 l) (treeL l)⁻¹ := by
  rw [treeL_inv]
  exact RepT.letter3 (rep_ta_a hF) (rep_tbi hF) (rep_tb hF) l

theorem rep_pairs {k : ℕ} (hk : k < 6) : RepT nPts (pairs0[k]?.getD .empty)
    ((treeL pairLetters[k]!.2)⁻¹ * (treeL pairLetters[k]!.1)⁻¹) := by
  have h := hF.pairs
  unfold pairsOK at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  have hc := h.2 k (List.mem_range.2 hk)
  rw [Array.getElem?_eq_getElem (by rw [h.1]; exact hk), Option.getD_some,
    ← getElem!_pos pairs0 k (by rw [h.1]; exact hk)]
  exact RepT.comp (rep_invLetter hF _) (rep_invLetter hF _) hc

theorem qIdx0_lt : ∀ t < qIdx0.size, qIdx0[t]! < nPts := by
  intro t ht
  have h := hF.q
  rw [List.all_eq_true] at h
  have := h t (List.mem_range.2 (by rw [← hF.qsize]; exact ht))
  rw [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem q00_size : q00.size = qLen + 1 := by rw [q00, Array.size_push, hF.qsize]

omit hF in
theorem q00_get {t : ℕ} (ht : t < qIdx0.size) : q00[t]! = qIdx0[t]! := by
  rw [q00, getElem!_pos _ t (by rw [Array.size_push]; omega), Array.getElem_push_lt ht,
    getElem!_pos qIdx0 t ht]

theorem q00_lt : ∀ t < q00.size, q00[t]! < nPts := by
  intro t ht
  by_cases hlt : t < qIdx0.size
  · rw [q00_get hlt]; exact qIdx0_lt hF t hlt
  · rw [q00, getElem!_pos _ t ht, Array.getElem_push, dif_neg hlt]
    exact (by decide : stripBase < nPts)

theorem idx_Hj {g : J} (hg : g ∈ Hj) : idx nPts g 0 = 0 := by
  have hO := hF.orbitFacts
  rw [idx_eq_iff hO (nPts_pos hF) (nPts_pos hF), vecAt_zero hO]
  exact Hj_fix_root hF.mat g hg

theorem eq_one_of_fix_q00 {g : J} (hg0 : idx nPts g 0 = 0)
    (hgq : ∀ t < q00.size, idx nPts g q00[t]! = q00[t]!) : g = 1 := by
  refine eq_one_of_fix_tuple hF.orbitFacts (qIdx0_lt hF) hF.sig ?_ hF.basis hg0 fun t ht => ?_
  · intro t ht
    have h := hF.blt
    rw [Array.all_eq_true] at h
    rw [getElem!_pos basisIdx t ht]
    exact of_decide_eq_true (h t ht)
  · have := hgq t (by rw [q00, Array.size_push]; omega)
    rwa [q00_get ht] at this

theorem mem_Hj_of_tupRep {u c h : J} {z : Array ℕ} (hu0 : idx nPts u 0 = 0) (hc : c ∈ Hj)
    (hh : h ∈ Hj) (h1 : TupRep nPts q00 z (c * u)) (h2 : TupRep nPts q00 z h) : u ∈ Hj := by
  have e : h⁻¹ * (c * u) = 1 := by
    apply eq_one_of_fix_q00 hF
    · rw [idx_mul, idx_mul, hu0, idx_Hj hF hc, idx_Hj hF (Hj.inv_mem hh)]
    · intro t ht
      rw [idx_mul, ← h1.2 t ht, h2.2 t ht, idx_inv_idx]
  have e' : c * u = h := by
    calc c * u = h * (h⁻¹ * (c * u)) := (mul_inv_cancel_left h _).symm
      _ = h := by rw [e, mul_one]
  have : u = c⁻¹ * h := by rw [← e', inv_mul_cancel_left]
  rw [this]
  exact Hj.mul_mem (Hj.inv_mem hc) hh

theorem ts50_get {l : ℕ} (hl : l < 6) : ts50[l]! = frTable ((stabMats ())[l]?.getD idRows) := by
  have hs := hF.mat.stabSize
  rw [ts50, getElem!_pos _ l (by rw [Array.size_map, hs]; exact hl), Array.getElem_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hl), Option.getD_some]

theorem tup_rep : ∀ e < tg0.1.size, ∃ h ∈ Hj, TupRep nPts q00 tg0.1[e]! h := by
  have h := hF.tg
  unfold tupleGroupOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, h0⟩, hall⟩ := h
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    by_cases he0 : e = 0
    · subst he0
      exact ⟨1, Hj.one_mem, by rw [h0]; exact TupRep.one⟩
    · have hk := hall e he
      unfold tupleAt at hk
      simp only [Bool.or_eq_true, beq_iff_eq, he0, false_or, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true, List.mem_range, V2.beq_iff] at hk
      obtain ⟨⟨⟨hp, hl⟩, hsz⟩, hpts⟩ := hk
      rw [ts50, Array.size_map, hF.mat.stabSize] at hl
      obtain ⟨h1, hh1, hrep⟩ := ih _ hp (by omega)
      refine ⟨(sJ tg0.2.2.1[e]!)⁻¹ * h1, Hj.mul_mem (Hj.inv_mem (sJ_mem _)) hh1, hsz,
        fun t ht => ?_⟩
      obtain ⟨hlt, heq⟩ := hpts t ht
      rw [idx_mul, ← hrep.2 t ht]
      have hpt : (tg0.1[tg0.2.1[e]!]!)[t]! < nPts := by
        rw [hrep.2 t ht]; exact idx_lt _ (q00_lt hF t ht)
      symm
      rw [idx_eq_iff hF.orbitFacts hpt hlt, ← ofRow_inj, sJ_inv_smul hF.mat]
      show (rdV2 bs0.keys _).toVec ᵥ* _ = (rdV2 bs0.keys _).toVec
      rw [heq, ts50_get hF hl, frApply_toVec_eq_vecMul]

omit hF in
private theorem GD0_eq : GD0 = ⟨nPts, bs0.alpha, bs0.beta, tbi0, t20.1, t20.2, q00, lev0, qLen,
    tg0.1, tg0.2.2.2, cacheDepth, NatMap.ofKeys cpts0 21,
    mkCache t20.1 bs0.alpha bs0.beta tbi0 q00 cpts0, pairs0⟩ := GD0_def

omit hF in
private theorem gdata_fields {G : GData} {n slot cd : ℕ} {ta tb tbi par dep : ByteArray}
    {q0 : Array ℕ} {lev : Level} {last c : Array (Array ℕ)} {lastMap : Std.HashMap (Array ℕ) ℕ}
    {cm : NatMap} {pairs : Array ByteArray}
    (h : G = ⟨n, ta, tb, tbi, par, dep, q0, lev, slot, last, lastMap, cd, cm, c, pairs⟩) :
    G.n = n ∧ G.ta = ta ∧ G.tb = tb ∧ G.tbi = tbi ∧ G.par = par ∧ G.dep = dep ∧ G.q0 = q0 ∧
      G.lev = lev ∧ G.last = last ∧ G.cacheDepth = cd ∧ G.cacheMap = cm ∧ G.cache = c ∧
      G.pairs = pairs := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit hF in
private theorem natMap_keys {k : Array ℕ} {b : ℕ} : (NatMap.ofKeys k b).keys = k := rfl

omit hF in
theorem GD0_fields : GD0.n = nPts ∧ GD0.ta = bs0.alpha ∧ GD0.tb = bs0.beta ∧ GD0.tbi = tbi0 ∧
    GD0.par = t20.1 ∧ GD0.dep = t20.2 ∧ GD0.q0 = q00 ∧ GD0.lev = lev0 ∧ GD0.last = tg0.1 ∧
    GD0.cacheDepth = cacheDepth ∧ GD0.cacheMap.keys = cpts0 ∧
    GD0.cache = mkCache t20.1 bs0.alpha bs0.beta tbi0 q00 cpts0 ∧ GD0.pairs = pairs0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := gdata_fields GD0_eq
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, (congrArg NatMap.keys h11).trans natMap_keys,
    h12, h13⟩

omit hF in
theorem cache_get {s : ℕ} (hs : s < cpts0.size) :
    (mkCache t20.1 bs0.alpha bs0.beta tbi0 q00 cpts0)[s]! =
      fwd t20.1 bs0.alpha bs0.beta tbi0 64 cpts0[s]! q00 := by
  unfold mkCache
  rw [getElem!_pos _ s (by rw [Array.size_map]; exact hs), Array.getElem_map,
    getElem!_pos cpts0 s hs]

theorem fwdC_spec : ∀ f j, j < nPts → depOf t20.2 j < f → TupRep nPts q00 (fwdC GD0 f j) (trans j) := by
  have hT := treeFacts0 hF
  have hl := RepT.letter3 (rep_ta hF) (rep_tb hF) (rep_tbi hF)
  intro f
  induction f with
  | zero => intro j _ h; omega
  | succ f ih =>
    intro j hj hd
    obtain ⟨-, hta, htb, htbi, hpar, hdep, hq0, -, -, hcd, hck, hc, -⟩ := GD0_fields
    rw [fwdC, hta, htb, htbi, hpar, hdep, hq0, hcd, hck, hc]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [beq_self_eq_true, ite_true]
      rw [trans_zero]
      exact TupRep.one
    · have hfwd : TupRep nPts q00 (fwd t20.1 bs0.alpha bs0.beta tbi0 64 j q00) (trans j) := by
        have := fwd_spec (par := t20.1) (rep_ta hF) (rep_tb hF) (rep_tbi hF) (q00_lt hF) 64 j
          (TupRep.one (n := nPts))
        rwa [mul_one] at this
      simp only [beq_iff_eq, hj0, ite_false]
      split_ifs with hc hk
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
        obtain ⟨⟨hs, hkey⟩, -⟩ := hk
        rw [cache_get hs, hkey]
        exact hfwd
      · exact hfwd
      · obtain ⟨hp, -, -, -, hdp⟩ := hT.step j hj hj0
        have hdj := hT.dep_lt j hj
        have e : trans j = treeL (labOf t20.1 j) * trans (parOf t20.1 j) := by
          rw [trans, treeElt_succ_of_ne 63 hj0,
            treeElt_fuel hT _ _ hp rfl 63 64 (by omega) (by omega)]
        rw [e]
        exact (ih _ hp (by omega)).apTab (q00_lt hF) (hl _)

private abbrev MulConv (G : Type*) [Group G] (f : G → G → G) : Prop := ∀ a b : G, a * b = f a b

omit hF in
private theorem J_mulConv : MulConv J (fun a b => a * b) := fun _ _ => rfl

omit hF in
private theorem tupRep_mul_conv {G : Type*} [Group G] {m : ℕ} [MulAction G (Fin m)]
    {q0 z : Array ℕ} {f : G → G → G} (hf : MulConv G f) {c x y w : G}
    (h : TupRep m q0 z (c * (x * (y * w)))) : TupRep m q0 z (f c (f x (f y w))) := by
  rwa [hf y w, hf x, hf c] at h

noncomputable abbrev sGen (s : ℕ) : J := if s = 1 then a⁻¹ else b⁻¹

omit hF in
theorem climbElt_mem (L : Level) : ∀ f k, climbElt L (fun s => xJ s) f k ∈ Hj
  | 0, _ => Hj.one_mem
  | f + 1, k => by
    rw [climbElt]
    split_ifs
    · exact Hj.one_mem
    · exact Hj.mul_mem (climbElt_mem L f _) (xJ_mem (by omega))

theorem globalTest_spec {s i : ℕ} (hi : i < nPts) (h : globalTest GD0 (fwdC GD0 64 i) s i = true) :
    (trans (idx nPts (sGen s) i))⁻¹ * sGen s * trans i ∈ Hj := by
  have hT := treeFacts0 hF
  have hx := fwdC_spec hF 64 i hi (hT.dep_lt i hi)
  have hj : idx nPts (sGen s) i < nPts := idx_lt _ hi
  obtain ⟨-, hta, htb, htbi, hpar, -, -, hlev, hlast, -, -, -, hpairs⟩ := GD0_fields
  unfold globalTest at h
  generalize GD0.lastMap = M at h
  generalize GD0.slot = sl at h
  rw [hta, htb, htbi, hpar, hlev, hlast, hpairs] at h
  generalize lev0.map = Mp at h
  simp -proj only at h
  generalize hstd : (if s = 1 then bs0.alpha else bs0.beta) = st at h
  have hst : RepT nPts st (sGen s) := by
    rw [← hstd]
    unfold sGen
    split_ifs
    exacts [rep_ta hF, rep_tb hF]
  have hz := bwd2_spec (par := t20.1) (L1 := (a⁻¹ : J)) (L2 := b⁻¹) (L3 := b)
    (by rw [inv_inv]; exact rep_ta_a hF) (by rw [inv_inv]; exact rep_tbi hF) (rep_tb hF)
    (fun k hk => rep_pairs hF hk) (q00_lt hF) 64 (rdU32 st i) (hx.apTab (q00_lt hF) hst)
  have e1 : bwd2Elt t20.1 (a⁻¹ : J) b⁻¹ b 64 (rdU32 st i) = (trans (idx nPts (sGen s) i))⁻¹ := by
    rw [hst i hi]
    exact bwd2Elt_eq hT _ _ hj rfl 64 (hT.dep_lt _ hj)
  rw [e1] at hz
  have hY : ∀ s ≤ 2, RepT nPts (lev0.tabs[s]?.getD .empty) (xJ s) := by
    intro s hs
    have e : lev0.tabs[s]?.getD .empty = zT s := by interval_cases s <;> rfl
    rw [e]
    exact rep_z hF (by omega)
  have hc := fun k => climb_spec (L := lev0) (Y := fun s => xJ s) hY (q00_lt hF) 64 k hz
  split_ifs at h with hk
  split at h
  · rename_i e _
    rw [beq_iff_eq] at h
    have hsz : (tg0.1[e]?.getD #[]).size = q00.size := by
      rw [h]
      exact (hc _).1
    have he : e < tg0.1.size := by
      by_contra hne
      rw [Array.getElem?_eq_none (by omega), Option.getD_none, q00_size hF] at hsz
      simp at hsz
    rw [Array.getElem?_eq_getElem he, Option.getD_some, ← getElem!_pos tg0.1 e he] at h
    obtain ⟨g, hg, hrep⟩ := tup_rep hF e he
    rw [h] at hrep
    rw [mul_assoc]
    refine mem_Hj_of_tupRep hF ?_ (climbElt_mem _ _ _) hg (tupRep_mul_conv J_mulConv (hc _)) hrep
    rw [idx_mul, idx_mul, idx_trans hF hi]
    have e := idx_inv_idx (n := nPts) (trans (idx nPts (sGen s) i)) 0
    rwa [idx_trans hF hj] at e
  · exact absurd h (by simp)

end Facts

end CFSG.Sporadic.J4
