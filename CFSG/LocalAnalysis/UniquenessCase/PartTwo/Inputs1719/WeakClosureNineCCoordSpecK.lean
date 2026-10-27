module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

theorem kdata_spec {G T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {D : KData} (hD : D.check TL = true)
    (hgens : ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c) :
    ∃ K : Subgroup P10, K ≤ G ∧ Desc K D.K.lit ∧
      (∃ N : Subgroup P10, Desc N D.N2.lit ∧ N ≤ pCoreOf 2 K) ∧
      ∀ y : P10, code y = D.y → TwoPTwo K (K ⊓ T₀) (zpowers y) D.p ∧
        Nat.card (zpowers y) = D.p := by
  obtain ⟨K, hKG, hK, hKnd, ⟨Z, h2, hZ⟩, N, hN, hNK⟩ := KData.spec hT hT2 hD hgens
  simp only [KData.check, sylB, Bool.and_eq_true, and_assoc, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.or_eq_true] at hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hyc, hyp, hy1, hp35, -, -, -, -, hpodd⟩ := hD
  have hpr : D.p.Prime := by rcases hp35 with h | h <;> rw [h] <;> norm_num
  have : Fact D.p.Prime := ⟨hpr⟩
  have hKc : Nat.card K = D.K.lit.length := hK.card hKnd
  refine ⟨K, hKG, hK, ⟨N, hN, hNK⟩, fun y hy => ?_⟩
  have hyK : y ∈ K := (hK.mem y).mpr (by rw [hy]; exact List.contains_iff_mem.mp hyc)
  have hypow : y ^ D.p = 1 := by
    have h1 : Core.cpow (code y) D.p = Core.cid := by rw [hy, hyp]
    rwa [cpow_eq_code, code_eq_cid_iff] at h1
  have hyne : y ≠ 1 := by
    rintro rfl
    exact hy1 (by rw [← hy, code_one])
  have hoy : orderOf y = D.p := orderOf_eq_prime hypow hyne
  have hZy : Nat.card (zpowers y) = D.p := by rw [Nat.card_zpowers, hoy]
  refine ⟨{ h2 with sylowP := ?_ }, hZy⟩
  refine ⟨zpowers_le.mpr hyK, IsPGroup.of_card (n := 1) (by rw [hZy, pow_one]), ?_⟩
  rw [relIndex_of_card (zpowers_le.mpr hyK) hZy hKc hpr.ne_zero]
  exact hpodd ∘ Nat.mod_eq_zero_of_dvd

private theorem cmul_getD {x a : List ℕ} {k : ℕ} (hk : k < a.length) :
    (cmul x a).getD k 0 = x.getD (a.getD k 0) 0 := by
  rw [cmul, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map,
    List.getD_eq_getElem _ _ hk]

private theorem getD_cid {k : ℕ} (hk : k < 10) : cid.getD k 0 = k := by
  rw [cid_eq]
  change (code (1 : P10)).getD (⟨k, hk⟩ : Fin 10) 0 = k
  rw [code_getD]
  rfl

private theorem cpow_three_getD {P : List ℕ} (hlen : P.length = 10)
    (hbound : ∀ k : Fin 10, P.getD k 0 < 10) (f : Fin 10 → Fin 10)
    (hf : ∀ k : Fin 10, (f k : ℕ) = P.getD k 0) (k : Fin 10) :
    (Core.cpow P 3).getD (k : ℕ) 0 = (f (f (f k)) : ℕ) := by
  have hk : (k : ℕ) < P.length := by rw [hlen]; exact k.2
  have h1 : P.getD (k : ℕ) 0 < P.length := by rw [hlen]; exact hbound k
  have h2 : P.getD (P.getD (k : ℕ) 0) 0 < P.length := by
    rw [hlen]; exact hbound ⟨_, hbound k⟩
  have h3 : P.getD (P.getD (P.getD (k : ℕ) 0) 0) 0 < 10 :=
    hbound ⟨_, hbound ⟨_, hbound k⟩⟩
  rw [Core.cpow.eq_2, Core.cpow.eq_2, Core.cpow.eq_2, Core.cpow.eq_1, hlen]
  rw [cmul_getD hk, cmul_getD h1, cmul_getD h2]
  change cid.getD (P.getD (P.getD (P.getD (k : ℕ) 0) 0) 0) 0 = (f (f (f k)) : ℕ)
  rw [getD_cid h3, ← hf k, ← hf (f k), ← hf (f (f k))]

private theorem eq_code_of_cpow_three {P : List ℕ} {σ : P10} (hlen : P.length = 10)
    (h : ∀ k : Fin 10, P.getD k 0 = (σ k : ℕ) ∨ P.getD k 0 = 0)
    (hpow : Core.cpow P 3 = Core.cid) : P = code σ := by
  have hbound : ∀ k : Fin 10, P.getD k 0 < 10 := by
    intro k
    rcases h k with hk | hk
    · rw [hk]; exact (σ k).2
    · rw [hk]; norm_num
  let f : Fin 10 → Fin 10 := fun k => ⟨P.getD k 0, hbound k⟩
  have hf : ∀ k : Fin 10, (f k : ℕ) = P.getD k 0 := fun _ => rfl
  have hf3 : ∀ k : Fin 10, f (f (f k)) = k := by
    intro k
    have h1 := cpow_three_getD hlen hbound f hf k
    rw [hpow, getD_cid k.2] at h1
    exact Fin.ext h1.symm
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : f (f (f x)) = f (f (f y)) := by rw [hxy]
    rwa [hf3 x, hf3 y] at h1
  have hfσ : f = σ := by
    funext k
    rcases h k with hk | hk
    · exact Fin.ext hk
    · have hfk : f k = ⟨0, by norm_num⟩ := Fin.ext hk
      by_cases hσk : σ k = ⟨0, by norm_num⟩
      · rw [hfk, hσk]
      · obtain ⟨y, hy⟩ := σ.surjective ⟨0, by norm_num⟩
        have hfy : f y = ⟨0, by norm_num⟩ := by
          rcases h y with hy' | hy'
          · rw [show f y = σ y from Fin.ext hy', hy]
          · exact Fin.ext hy'
        have hyk : y = k := hfinj (by rw [hfy, hfk])
        exfalso
        exact hσk (by rw [← hyk]; exact hy)
  apply List.ext_getElem?
  intro n
  by_cases hn : n < 10
  · rw [List.getElem?_eq_getElem (by rw [hlen]; exact hn),
      List.getElem?_eq_getElem (by rw [code_length]; exact hn)]
    have hcalc : P[n] = (code σ)[n] := by
      calc P[n] = P.getD n 0 := (List.getD_eq_getElem _ _ (by rw [hlen]; exact hn)).symm
        _ = (f ⟨n, hn⟩ : ℕ) := rfl
        _ = (σ ⟨n, hn⟩ : ℕ) := by rw [hfσ]
        _ = (code σ).getD (⟨n, hn⟩ : Fin 10) 0 := (code_getD σ ⟨n, hn⟩).symm
        _ = (code σ)[n] := List.getD_eq_getElem _ _ (by rw [code_length]; exact hn)
    rw [hcalc]
    rfl
  · rw [List.getElem?_eq_none (by rw [hlen]; omega),
      List.getElem?_eq_none (by rw [code_length]; omega)]

private theorem foldl_cmul_agree :
    ∀ (as : List (List ℕ)) (cs : List P10),
      List.Forall₂ (fun a c => (∀ k : Fin 10, a.getD k 0 = (c k : ℕ)) ∧ 9 ≤ a.length) as cs →
      ∀ (b : List ℕ) (τ : P10),
        (∀ k : Fin 10, b.getD k 0 = (τ k : ℕ) ∨ b.getD k 0 = 0) →
        ∀ k : Fin 10,
          (as.foldl cmul b).getD k 0 = ((cs.foldl (· * ·) τ) k : ℕ) ∨
            (as.foldl cmul b).getD k 0 = 0 := by
  intro as
  induction as with
  | nil =>
    intro cs h b τ hb k
    cases h
    rw [List.foldl_nil, List.foldl_nil]
    exact hb k
  | cons a as ih =>
    intro cs h b τ hb k
    cases cs with
    | nil => cases h
    | cons c cs =>
      cases h with
      | cons ha htail =>
        rw [List.foldl_cons, List.foldl_cons]
        refine ih cs htail (cmul b a) (τ * c) ?_ k
        intro j
        by_cases hj : (j : ℕ) < a.length
        · rw [cmul_getD hj, ha.1 j, Equiv.Perm.mul_apply]
          rcases hb (c j) with h | h
          · exact Or.inl h
          · exact Or.inr h
        · right
          have hlen : (cmul b a).length ≤ (j : ℕ) := by
            rw [cmul, List.length_map]
            omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
          rfl

private theorem nine_le_length_of_agree {l : List ℕ} {c : P10}
    (h : ∀ m : Fin 10, l.getD m 0 = (c m : ℕ)) : 9 ≤ l.length := by
  by_contra hlt
  have hlt' : l.length < 9 := by omega
  have hm0 : l.getD l.length 0 = 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_refl _)]
    rfl
  have hm1 : l.getD (l.length + 1) 0 = 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have h0 : (c ⟨l.length, by omega⟩ : ℕ) = 0 := by
    rw [← h ⟨l.length, by omega⟩]; exact hm0
  have h1 : (c ⟨l.length + 1, by omega⟩ : ℕ) = 0 := by
    rw [← h ⟨l.length + 1, by omega⟩]; exact hm1
  have hc0 : c ⟨l.length, by omega⟩ = c ⟨l.length + 1, by omega⟩ := by
    apply Fin.ext
    rw [h0, h1]
  have hval := congrArg Fin.val (c.injective hc0)
  simp at hval

private theorem three_letter {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    {y : P10} {t : List ℕ × ℕ × List ℕ} (ht1 : TL.contains t.1 = true)
    (heq : cmul t.1 (cpow (code y) t.2.1) = cmul t.2.2 t.1) :
    ∃ c : P10, c ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ zpowers y, z = d * x * d⁻¹} ∧
      (∀ k : Fin 10, t.2.2.getD k 0 = (c k : ℕ)) ∧ 9 ≤ t.2.2.length := by
  obtain ⟨d, hdT, hdcode⟩ := hT.surj t.1 (List.contains_iff_mem.mp ht1)
  let c : P10 := d * y ^ t.2.1 * d⁻¹
  have hcS : c ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ zpowers y, z = d * x * d⁻¹} :=
    Subgroup.subset_closure ⟨d, hdT, y ^ t.2.1, pow_mem (Subgroup.mem_zpowers y) _, rfl⟩
  have heq' : code (d * y ^ t.2.1) = cmul t.2.2 (code d) := by
    have h := heq
    rw [← hdcode, cpow_eq_code, ← code_mul] at h
    exact h
  have hpref : ∀ k : Fin 10, t.2.2.getD (d k : ℕ) 0 = ((d * y ^ t.2.1) k : ℕ) := by
    intro k
    have hk := congrArg (fun l : List ℕ => l.getD (k : ℕ) 0) heq'
    rw [code_getD (d * y ^ t.2.1) k] at hk
    rw [cmul_getD (x := t.2.2) (a := code d) (k := (k : ℕ))
      (by rw [code_length]; exact k.2)] at hk
    rw [code_getD d k] at hk
    exact hk.symm
  have hpref' : ∀ m : Fin 10, t.2.2.getD m 0 = (c m : ℕ) := by
    intro m
    have hdm : d (d⁻¹ m) = m := d.apply_symm_apply m
    have hk : t.2.2.getD m 0 = ((d * y ^ t.2.1) (d⁻¹ m) : ℕ) := by
      simpa only [hdm] using hpref (d⁻¹ m)
    rw [hk]
    rfl
  exact ⟨c, hcS, hpref', nine_le_length_of_agree hpref'⟩

private theorem foldl_mul_mem {H : Subgroup P10} :
    ∀ (l : List P10) (a : P10), a ∈ H → (∀ c ∈ l, c ∈ H) → l.foldl (· * ·) a ∈ H := by
  intro l
  induction l with
  | nil => intro a ha _; exact ha
  | cons c l ih =>
    intro a ha hl
    rw [List.foldl_cons]
    exact ih (a * c) (mul_mem ha (hl c (List.mem_cons_self)))
      fun d hd => hl d (List.mem_cons_of_mem _ hd)

theorem three_spec {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL) {y : P10}
    {p : ℕ} {w : List (List ℕ × ℕ × List ℕ)} (h : threeB TL (code y) p w = true) :
    p = 3 ∨ ∃ z ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ zpowers y, z = d * x * d⁻¹}, orderOf z = 3 := by
  simp only [threeB, Bool.or_eq_true, Bool.and_eq_true, and_assoc, beq_iff_eq, bne_iff_ne,
    ne_eq] at h
  rcases h with hp | ⟨hall, hpow, hne⟩
  · exact Or.inl hp
  · right
    let S : Set P10 := {z | ∃ d ∈ T₀, ∃ x ∈ zpowers y, z = d * x * d⁻¹}
    have hchoice : ∀ t ∈ w, ∃ c : P10, c ∈ closure S ∧
        (∀ k : Fin 10, t.2.2.getD k 0 = (c k : ℕ)) ∧ 9 ≤ t.2.2.length := by
      intro t ht
      have hcheck := List.all_eq_true.mp hall t ht
      rw [Bool.and_eq_true, beq_iff_eq] at hcheck
      exact three_letter hT hcheck.1 hcheck.2
    let cs : List P10 := w.pmap (fun t ht => Classical.choose (hchoice t ht)) (fun _ ht => ht)
    have hcs_mem : ∀ c ∈ cs, c ∈ closure S := by
      intro c hc
      rw [List.mem_pmap] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      exact (Classical.choose_spec (hchoice t ht)).1
    have hfa : List.Forall₂
        (fun a c => (∀ k : Fin 10, a.getD k 0 = (c k : ℕ)) ∧ 9 ≤ a.length)
        (w.map fun t => t.2.2) cs := by
      rw [List.forall₂_iff_get]
      refine ⟨by simp [cs], fun i hi hj => ?_⟩
      have hiw : i < w.length := by simpa using hi
      have hjw : i < w.length := by simpa [cs] using hj
      rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map, List.getElem_pmap]
      exact (Classical.choose_spec (hchoice _ (List.getElem_mem hiw))).2
    have hfold := foldl_cmul_agree (w.map fun t => t.2.2) cs hfa cid 1
      (fun k => Or.inl (getD_cid k.2))
    have hPlen : ((w.map fun t => t.2.2).foldl cmul cid).length = 10 := by
      have h1 : (Core.cpow ((w.map fun t => t.2.2).foldl cmul cid) 3).length =
          ((w.map fun t => t.2.2).foldl cmul cid).length := by
        simp [Core.cpow, Core.cmul]
      rw [hpow, cid_eq, code_length] at h1
      exact h1.symm
    have hPcode : (w.map fun t => t.2.2).foldl cmul cid = code (cs.foldl (· * ·) 1) :=
      eq_code_of_cpow_three hPlen hfold hpow
    have hσ1 : cs.foldl (· * ·) 1 ≠ 1 := by
      intro h1
      exact hne (by rw [hPcode, h1, code_one])
    have hσ3 : (cs.foldl (· * ·) 1) ^ 3 = 1 := by
      have h1 : Core.cpow (code (cs.foldl (· * ·) 1)) 3 = Core.cid := by
        rw [← hPcode]; exact hpow
      rwa [cpow_eq_code, code_eq_cid_iff] at h1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨cs.foldl (· * ·) 1, foldl_mul_mem cs 1 (one_mem _) hcs_mem,
      orderOf_eq_prime hσ3 hσ1⟩

end CFSG.LocalAnalysis.WeakClosure81.CoordA6
