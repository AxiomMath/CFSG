module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosModelled
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGCartanATypeArith

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pmb_natCast_pred (p : ℕ) (hp : 0 < p) : ((p - 1 : ℕ) : ZMod p) = -1 := by
  have h : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
    have h1 : ((p - 1 : ℕ) : ZMod p) + ((1 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    rw [Nat.cast_one, ZMod.natCast_self] at h1
    exact h1
  exact eq_neg_of_add_eq_zero_right (by rwa [add_comm] at h)

private lemma pmb_getD_append_left (l₁ l₂ : List ℕ) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_append]; omega), List.getElem?_eq_getElem h]
  congr 1
  rw [List.getElem_append_left h]

private lemma pmb_getD_append_right (l₁ l₂ : List ℕ) (i : ℕ) (h : l₁.length ≤ i)
    (hi : i < (l₁ ++ l₂).length) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by rw [List.length_append] at hi; omega)]
  congr 1
  rw [List.getElem_append_right h]

private lemma pmb_allVecsP_mem {p : ℕ} :
    ∀ (n : ℕ) (l : Vec), l.length = n → (∀ x ∈ l, x < p) → l ∈ allVecsP p n
  | 0, l, hlen, _ => by
      cases l with
      | nil => simp [allVecsP]
      | cons a t => simp at hlen
  | n + 1, l, hlen, hlt => by
      cases l with
      | nil => simp at hlen
      | cons a t =>
          simp only [allVecsP]
          refine List.mem_flatMap.mpr
            ⟨t, pmb_allVecsP_mem n t (by simpa using hlen)
              (fun x hx => hlt x (by simp [hx])), ?_⟩
          simp only [List.mem_map]
          exact ⟨a, List.mem_range.mpr (hlt a (by simp)), rfl⟩

private lemma pmb_cartanRowP_getD_cast {p N : ℕ} (hp : 0 < p) (i j : Fin (N - 1)) :
    (((cartanRowP p N (i : ℕ)).getD (j : ℕ) 0 : ℕ) : ZMod p) =
      ((CartanMatrix.A (N - 1) i j : ℤ) : ZMod p) := by
  have hfold : ((CartanMatrix.A (N - 1) i j : ℤ) : ZMod p) =
      CFSG.StandardType.ggCartanAMod (N - 1) p i j := rfl
  rw [hfold, CFSG.StandardType.ggCartanAMod_apply]
  rw [cartanRowP, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt]
  simp only [Option.map_some, Option.getD_some]
  by_cases h1 : i = j
  · have hv : (i : ℕ) = (j : ℕ) := congrArg Fin.val h1
    rw [if_pos h1, if_pos hv]
    norm_num
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => h1 (Fin.ext h)
    rw [if_neg h1, if_neg hv]
    by_cases h2 : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)
    · rw [if_pos h2, if_pos h2, pmb_natCast_pred p hp]
    · rw [if_neg h2, if_neg h2]
      simp

private lemma pmb_vec_unitP (p D k : ℕ) (hk : k < D) :
    (fun j : Fin D => (((unitP D k).getD (j : ℕ) 0 : ℕ) : ZMod p)) =
      (Pi.single (⟨k, hk⟩ : Fin D) 1 : Fin D → ZMod p) := by
  funext j
  simp only [unitP, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt]
  by_cases h : (j : ℕ) = k
  · have hj : j = (⟨k, hk⟩ : Fin D) := Fin.ext h
    subst hj
    simp [Pi.single_eq_same]
  · have hj : j ≠ (⟨k, hk⟩ : Fin D) := fun hh => h (congrArg Fin.val hh)
    simp [Pi.single_eq_of_ne hj, h]

private lemma pmb_vec_x (p n : ℕ) :
    (fun j : Fin (n + 1) =>
        ((((List.range n).map (fun k => k + 1) ++ [0]).getD (j : ℕ) 0 : ℕ) : ZMod p)) =
      fun j : Fin (n + 1) => if (j : ℕ) < n then (((j : ℕ) + 1 : ℕ) : ZMod p) else 0 := by
  funext j
  by_cases hj : (j : ℕ) < n
  · rw [if_pos hj]
    rw [pmb_getD_append_left (l₁ := (List.range n).map (fun k => k + 1)) (l₂ := [0])
      (i := (j : ℕ)) (by simp [hj])]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  · rw [if_neg hj]
    have hj' : (j : ℕ) = n := by omega
    rw [pmb_getD_append_right (l₁ := (List.range n).map (fun k => k + 1)) (l₂ := [0])
      (i := (j : ℕ)) (by simp only [List.length_map, List.length_range]; omega)
      (by simp [j.isLt])]
    simp [hj']

private lemma pmb_outs_length (n s : ℕ) (hn : n = 4 ∨ n = 5 ∨ n = 6) (hs : s ≤ 2) :
    ((List.range n).filter (fun k => !(s ≤ k && k < s + (n + 1 - 3)))).length = 2 := by
  rcases hn with rfl | rfl | rfl <;> interval_cases s <;> decide


theorem posb_model (p N : ℕ) [Fact p.Prime] (hc : CFSG.StandardType.lr6SmallCellA p N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (hV : Module.finrank (ZMod p) V = N)
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hF : CFSG.StandardType.GGIndepAFrame p N h α x) (hha : αa ha = 2)
    (hsp : ha ∉ Submodule.span (ZMod p) (Set.range h)) (s : ℕ) (hs : s ≤ 2)
    (o : ℕ × ℕ × ℕ) (ho : o ∈ posOpts p N)
    (hH : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p))
    (hA : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p)) :
    ModelledIn (posBCell p N) s p h α x ha αa := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hN5 : 5 ≤ N := by rcases hc with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : n = 4 ∨ n = 5 ∨ n = 6 := by
    rcases hc with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl | rfl <;> omega
  have hli : LinearIndependent (ZMod p) (Fin.snoc h ha : Fin (n + 1) → V) := by
    rw [linearIndependent_fin_snoc]
    exact ⟨hF.indep, hsp⟩
  let b : Module.Basis (Fin (n + 1)) (ZMod p) V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb_coe : ⇑b = (Fin.snoc h ha : Fin (n + 1) → V) :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb_castSucc : ∀ i : Fin n, b (Fin.castSucc i) = h i := by
    intro i
    have := congrFun hb_coe (Fin.castSucc i)
    simpa [Fin.snoc_castSucc] using this
  have hb_last : b (Fin.last n) = ha := by
    have := congrFun hb_coe (Fin.last n)
    simpa [Fin.snoc_last] using this
  let e : V ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) := b.equivFun
  have he_b : ∀ k : Fin (n + 1), e (b k) = (Pi.single k 1 : Fin (n + 1) → ZMod p) := by
    intro k
    dsimp only [e]
    funext j
    rw [Module.Basis.equivFun_self]
    by_cases h : k = j
    · rw [if_pos h, ← h, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
  have he_h : ∀ i : Fin n, e (h i) = (Pi.single (Fin.castSucc i) 1 : Fin (n + 1) → ZMod p) := by
    intro i
    rw [← hb_castSucc i]
    exact he_b (Fin.castSucc i)
  have he_ha : e ha = (Pi.single (Fin.last n) 1 : Fin (n + 1) → ZMod p) := by
    rw [← hb_last]
    exact he_b (Fin.last n)
  let U : ℕ → ℕ := fun k => if h : k < n then (α ⟨k, h⟩ ha).val else 0
  let Vv : ℕ → ℕ := fun k => if hk : k < n then (αa (h ⟨k, hk⟩)).val else 0
  have hU_lt : ∀ k, U k < p := by
    intro k
    dsimp only [U]
    split
    · exact ZMod.val_lt _
    · exact hp0
  have hV_lt : ∀ k, Vv k < p := by
    intro k
    dsimp only [Vv]
    split
    · exact ZMod.val_lt _
    · exact hp0
  have ho1 : o.2.1 < p := by
    have ho' := ho
    simp only [posOpts, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at ho'
    rcases ho' with ⟨c, _, rfl⟩ | ⟨c, _, h⟩
    · show p - 1 < p; omega
    · rcases h with rfl | rfl
      · show p - 1 < p; omega
      · show p - 2 < p; omega
  have ho2 : o.2.2 < p := by
    have ho' := ho
    simp only [posOpts, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at ho'
    rcases ho' with ⟨c, _, rfl⟩ | ⟨c, _, h⟩
    · show p - 1 < p; omega
    · rcases h with rfl | rfl
      · show p - 2 < p; omega
      · show p - 1 < p; omega
  let inJ : ℕ → Bool := fun k => s ≤ k && k < s + (n + 1 - 3)
  let outs : List ℕ := (List.range n).filter fun k => !(inJ k)
  have houts_len : outs.length = 2 := by
    simpa only [outs, inJ] using pmb_outs_length n s hn hs
  obtain ⟨b0, b1, houts_eq0⟩ := List.length_eq_two.mp houts_len
  let bmin : ℕ := outs.getD 0 0
  let bmax : ℕ := outs.getD 1 0
  have hbmin : bmin = b0 := by simp [bmin, houts_eq0]
  have hbmax : bmax = b1 := by simp [bmax, houts_eq0]
  have houts_eq : outs = [bmin, bmax] := by
    rw [houts_eq0]
    simp [hbmin, hbmax]
  have hout_cases : ∀ k, k < n → (!(inJ k)) = true → k = bmin ∨ k = bmax := by
    intro k hk hout
    have hkmem : k ∈ outs := by
      simp only [outs, List.mem_filter, List.mem_range]
      exact ⟨hk, hout⟩
    rw [houts_eq] at hkmem
    simpa using hkmem
  have hbmin_mem : bmin ∈ outs := by rw [houts_eq]; simp
  have hbmax_mem : bmax ∈ outs := by rw [houts_eq]; simp
  have hbmin_out : (!(inJ bmin)) = true := (List.mem_filter.mp hbmin_mem).2
  have hbmax_out : (!(inJ bmax)) = true := (List.mem_filter.mp hbmax_mem).2
  have hbmin_ne : bmin ≠ bmax := by
    have hnodup : outs.Nodup := by
      dsimp only [outs]
      exact (List.nodup_range).filter _
    rw [houts_eq] at hnodup
    simpa using hnodup
  let fr : Vec := [U bmin, Vv bmin, U bmax, Vv bmax]
  let uv : ℕ → ℕ × ℕ := fun k =>
    if inJ k then (if k - s = o.1 then (o.2.1, o.2.2) else (0, 0))
    else if outs.head? = some k then (fr.getD 0 0, fr.getD 1 0)
    else (fr.getD 2 0, fr.getD 3 0)
  have hhead : outs.head? = some bmin := by rw [houts_eq]; rfl
  have huv : ∀ k, k < n → uv k = (U k, Vv k) := by
    intro k hk
    by_cases hin : inJ k
    · have hin' : (decide (s ≤ k) && decide (k < s + (n + 1 - 3))) = true := by
        simpa [inJ] using hin
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin'
      have h1 : s ≤ k := hin'.1
      have h2 : k < s + (n + 1 - 3) := hin'.2
      have hHk := hH ⟨k, hk⟩ h1 (by simpa using h2)
      have hAk := hA ⟨k, hk⟩ h1 (by simpa using h2)
      have hlt1 : (if k - s = o.1 then o.2.1 else 0) < p := by
        by_cases h : k - s = o.1 <;> simp [h, ho1, hp0]
      have hlt2 : (if k - s = o.1 then o.2.2 else 0) < p := by
        by_cases h : k - s = o.1 <;> simp [h, ho2, hp0]
      have hUval : U k = (if k - s = o.1 then o.2.1 else 0) := by
        dsimp only [U]
        rw [dif_pos hk]
        rw [hHk, ZMod.val_cast_of_lt hlt1]
      have hVval : Vv k = (if k - s = o.1 then o.2.2 else 0) := by
        dsimp only [Vv]
        rw [dif_pos hk]
        rw [hAk, ZMod.val_cast_of_lt hlt2]
      have hif : (if k - s = o.1 then (o.2.1, o.2.2) else (0, 0)) = (U k, Vv k) := by
        by_cases h : k - s = o.1 <;> simp [h, hUval, hVval]
      simpa [uv, hin] using hif
    · have hout : (!(inJ k)) = true := by simpa using hin
      rcases hout_cases k hk hout with rfl | rfl
      · have hbmin_false : inJ bmin = false := by
          have := hbmin_out
          simpa using this
        ext <;> simp [uv, hbmin_false, hhead, fr]
      · have hbmax_false : inJ bmax = false := by
          have := hbmax_out
          simpa using this
        have hhead_ne : outs.head? ≠ some bmax := by
          rw [hhead]
          simp [hbmin_ne]
        ext <;> simp [uv, hbmax_false, hhead_ne, fr]
  let gens : List Refl :=
    (List.range n).map (fun k =>
      (⟨cartanRowP p (n + 1) k ++ [(uv k).1], unitP (n + 1) k⟩ : Refl)) ++
      [⟨(List.range n).map (fun k => (uv k).2) ++ [2], unitP (n + 1) n⟩]
  let xv : Vec := (List.range n).map (fun k => k + 1) ++ [0]
  let P : Pt := ⟨p, n + 1, n, gens, xv, posBound p (n + 1)⟩
  have hgen_i : ∀ i : Fin n,
      gens.getD i.val ⟨[], []⟩ =
        (⟨cartanRowP p (n + 1) i.val ++ [(uv i.val).1], unitP (n + 1) i.val⟩ : Refl) := by
    intro i
    dsimp only [gens]
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp)]
    simp [List.getElem?_map, List.getElem?_range i.isLt]
  have hgen_last :
      gens.getD n ⟨[], []⟩ =
        (⟨(List.range n).map (fun k => (uv k).2) ++ [2], unitP (n + 1) n⟩ : Refl) := by
    dsimp only [gens]
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp
  let y : V := ∑ i : Fin n, (((i : ℕ) + 1 : ℕ) : ZMod p) • h i
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hF.x_mem
  have hmul : m = m ⟨0, by omega⟩ • (CFSG.StandardType.ggCartanARad n p) :=
    CFSG.StandardType.ggCartanAMod_ker n p (by omega) m (by
      intro i
      have h := hF.x_ker i
      rw [← hm, map_sum] at h
      simp only [map_smul, smul_eq_mul] at h
      rw [Finset.sum_congr rfl (fun j _ => by
        rw [hF.pair, ← CFSG.StandardType.ggCartanAMod, mul_comm])] at h
      exact h)
  have hxy : x = m ⟨0, by omega⟩ • y := by
    rw [← hm, hmul]
    simp only [y, CFSG.StandardType.ggCartanARad, Finset.smul_sum, Pi.smul_apply,
      smul_eq_mul, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have hm0ne : m ⟨0, by omega⟩ ≠ 0 := by
    intro h0
    apply hF.x_ne
    rw [hxy, h0, zero_smul]
  let c : ZMod p := (m ⟨0, by omega⟩)⁻¹
  have hcne : c ≠ 0 := inv_ne_zero hm0ne
  have hcx : c • x = y := by
    rw [hxy, smul_smul, inv_mul_cancel₀ hm0ne, one_smul]
  have he_y : e y = (fun j : Fin (n + 1) =>
      if (j : ℕ) < n then (((j : ℕ) + 1 : ℕ) : ZMod p) else 0) := by
    dsimp only [y]
    ext j
    simp only [map_sum, Finset.sum_apply, map_smul, he_h, Pi.smul_apply, smul_eq_mul]
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj]
      let i : Fin n := ⟨j, hj⟩
      have hji : j = Fin.castSucc i := Fin.ext rfl
      rw [hji]
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
        simp
      · intro k _ hk
        have hne : k.castSucc ≠ i.castSucc := fun h => hk (Fin.castSucc_injective n h)
        rw [Pi.single_eq_of_ne (Ne.symm hne)]
        simp
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg hj]
      have hj' : (j : ℕ) = n := by omega
      have hjl : j = Fin.last n := Fin.ext hj'
      rw [hjl]
      rw [Finset.sum_eq_zero]
      · intro k _
        have hne : k.castSucc ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        rw [Pi.single_eq_of_ne (Ne.symm hne)]
        simp
  have hPvecx : P.vec P.x = (fun j : Fin (n + 1) =>
      if (j : ℕ) < n then (((j : ℕ) + 1 : ℕ) : ZMod p) else 0) := by
    dsimp only [P, xv]
    exact pmb_vec_x p n
  have hrepr : ∀ w : V, (∑ j : Fin (n + 1), e w j • b j) = w := by
    intro w
    dsimp only [e]
    rw [← Module.Basis.equivFun_symm_apply, b.equivFun.symm_apply_apply]
  have hαdot : ∀ (i : Fin n) (w : V),
      α i w = P.dot (P.vec (P.gens.getD i.val ⟨[], []⟩).f) (e w) := by
    intro i w
    have hlen : (cartanRowP p (n + 1) i.val).length = n := by simp [cartanRowP]
    rw [hgen_i i, Pt.dot, Fin.sum_univ_castSucc]
    conv_lhs => rw [← hrepr w]
    rw [map_sum, Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have hpvj : P.vec (cartanRowP p (n + 1) i.val ++ [(uv i.val).1]) (Fin.castSucc j) =
          (((cartanRowP p (n + 1) i.val).getD (j : ℕ) 0 : ℕ) : ZMod p) := by
        dsimp only [P, Pt.vec]
        rw [show ((Fin.castSucc j : Fin (n + 1)) : ℕ) = (j : ℕ) from rfl]
        rw [pmb_getD_append_left (l₁ := cartanRowP p (n + 1) i.val)
          (l₂ := [(uv i.val).1]) (i := (j : ℕ)) (by rw [hlen]; exact j.isLt)]
      rw [map_smul, smul_eq_mul, hb_castSucc j, hF.pair, hpvj,
        pmb_cartanRowP_getD_cast (p := p) (N := n + 1) hp0 i j]
      ring
    · have hpvl : P.vec (cartanRowP p (n + 1) i.val ++ [(uv i.val).1]) (Fin.last n) =
          ((uv i.val).1 : ZMod p) := by
        dsimp only [P, Pt.vec]
        rw [show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl]
        rw [pmb_getD_append_right (l₁ := cartanRowP p (n + 1) i.val)
          (l₂ := [(uv i.val).1]) (i := n) (by simp [hlen])
          (by simp [List.length_append, hlen])]
        simp [hlen]
      have huv1 : (uv i.val).1 = (α i ha).val := by
        have h : (uv i.val).1 = U i.val := by
          simpa using congrArg Prod.fst (huv i.val i.isLt)
        rw [h]
        dsimp only [U]
        rw [dif_pos i.isLt]
        rfl
      rw [map_smul, smul_eq_mul, hb_last, hpvl, huv1, ZMod.natCast_zmod_val]
      ring
  have hαadot : ∀ w : V,
      αa w = P.dot (P.vec (P.gens.getD n ⟨[], []⟩).f) (e w) := by
    intro w
    rw [hgen_last, Pt.dot, Fin.sum_univ_castSucc]
    conv_lhs => rw [← hrepr w]
    rw [map_sum, Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have hpvj : P.vec ((List.range n).map (fun k => (uv k).2) ++ [2]) (Fin.castSucc j) =
          ((uv j.val).2 : ZMod p) := by
        dsimp only [P, Pt.vec]
        rw [show ((Fin.castSucc j : Fin (n + 1)) : ℕ) = (j : ℕ) from rfl]
        rw [pmb_getD_append_left (l₁ := (List.range n).map (fun k => (uv k).2))
          (l₂ := [2]) (i := (j : ℕ)) (by simp [j.isLt])]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt]
        rfl
      have huv2 : (uv j.val).2 = (αa (h j)).val := by
        have h : (uv j.val).2 = Vv j.val := by
          simpa using congrArg Prod.snd (huv j.val j.isLt)
        rw [h]
        dsimp only [Vv]
        rw [dif_pos j.isLt]
        rfl
      rw [map_smul, smul_eq_mul, hb_castSucc j, hpvj, huv2, ZMod.natCast_zmod_val]
      ring
    · have hpvl : P.vec ((List.range n).map (fun k => (uv k).2) ++ [2]) (Fin.last n) =
          (2 : ZMod p) := by
        dsimp only [P, Pt.vec]
        rw [show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl]
        rw [pmb_getD_append_right (l₁ := (List.range n).map (fun k => (uv k).2))
          (l₂ := [2]) (i := n) (by simp) (by simp [List.length_append, List.length_range])]
        simp
      rw [map_smul, smul_eq_mul, hb_last, hpvl, hha]
      ring
  have hfr : fr ∈ allVecsP p 4 := by
    apply pmb_allVecsP_mem 4 fr (by simp [fr])
    intro z hz
    simp only [fr, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hU_lt bmin
    · exact hV_lt bmin
    · exact hU_lt bmax
    · exact hV_lt bmax
  have hmem : (⟨P, s⟩ : SPt) ∈ posBCell p (n + 1) := by
    dsimp only [posBCell, P, gens, xv, uv, outs, inJ, fr]
    refine List.mem_flatMap.mpr ⟨s, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · refine List.mem_flatMap.mpr ⟨o, ho, ?_⟩
      refine List.mem_map.mpr ⟨fr, hfr, ?_⟩
      rfl
  have hmodels : P.Models e h α (c • x) ha αa := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [P, gens, List.length_map, List.length_append, List.length_range]
    · rw [hcx, he_y, hPvecx]
    · intro i
      refine ⟨?_, ?_⟩
      · rw [hgen_i i]
        have hvec := pmb_vec_unitP p (n + 1) i.val (by omega)
        rw [show P.vec (unitP (n + 1) i.val) =
            (fun j : Fin (n + 1) => (((unitP (n + 1) i.val).getD (j : ℕ) 0 : ℕ) : ZMod p))
            from rfl]
        exact (he_h i).trans hvec.symm
      · exact hαdot i
    · change e ha = P.vec (P.gens.getD n ⟨[], []⟩).h
      rw [hgen_last]
      have hvec := pmb_vec_unitP p (n + 1) n (by omega)
      rw [show P.vec (unitP (n + 1) n) =
          (fun j : Fin (n + 1) => (((unitP (n + 1) n).getD (j : ℕ) 0 : ℕ) : ZMod p))
          from rfl]
      exact he_ha.trans hvec.symm
    · exact hαadot
  exact ⟨n + 1, n, gens, xv, posBound p (n + 1), hmem, c, hcne, e, hmodels⟩

end CFSG.TwoNodeSmall
