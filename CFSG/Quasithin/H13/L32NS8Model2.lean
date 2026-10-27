module

public import CFSG.Quasithin.H13.L32NS8Model
public import CFSG.Quasithin.H13.L32NS7Model2

public section

namespace CFSG.Quasithin.H13.S8Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert

@[expose] def Z8 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub z8G

theorem zB_spec :
    (elemsOf z8G).length = 16 ∧ subB z8G (elemsOf z8G) = true ∧ (∀ g ∈ z8G, g ∈ s8E) ∧
      (∀ n ∈ stE, mul8 (invSt n) n = one8) ∧
      ∀ x ∈ stE, mul8 x x = one8 →
        (∀ n ∈ stE, mul8 x (mul8 (mul8 n x) (invSt n)) = mul8 (mul8 (mul8 n x) (invSt n)) x) →
        x ∈ elemsOf z8G := by
  have h := s8Check_parts.2.2.2.1
  simp only [zB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx hsq hcomm => ?_⟩
  have := bimp (h5 x hx) (by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨hsq, hcomm⟩)
  simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using this

theorem Z8_le_s8 : Z8 ≤ s8 := genSub_le_s8 zB_spec.2.2.1

theorem mem_Z8_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ Z8 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf z8G :=
  mem_genSub_iff_of zB_spec.2.1 (unit_of_s8E zB_spec.2.2.1) u

theorem card_Z8 : Nat.card Z8 = 16 := by
  rw [Z8, card_genSub_of zB_spec.2.1 (unit_of_s8E zB_spec.2.2.1), zB_spec.1]

theorem colsOf_inv_st {n : GL (Fin 8) (ZMod 2)}
    (hn : colsOf (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ stE) :
    colsOf ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      invSt (colsOf (n : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  refine colsOf_inv_of ?_ (zB_spec.2.2.2.1 _ hn)
  unfold invSt
  cases hf : stE.find? (fun m => mul8 m (colsOf (n : Matrix (Fin 8) (Fin 8) (ZMod 2))) == one8)
    with
  | none => exact valid8_one8
  | some m =>
    exact (subB_spec s8Basic_spec.1).1 _ (List.mem_filter.mp (List.mem_of_find?_eq_some hf)).1

theorem colsOf_mem_stE {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ s8)
    (hyf : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR) :
    colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ stE := by
  have hvR : vR < 256 := by decide
  refine List.mem_filter.mpr ⟨colsOf_mem_s8E hy, ?_⟩
  rw [mulVec_vec8] at hyf
  exact beq_iff_eq.mpr (vec8_inj (mv8_lt (valid8_colsOf _) _) hvR hyf)

theorem exists_of_stE {c : List ℕ} (hc : c ∈ stE) :
    ∃ y ∈ s8, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR ∧
      colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c := by
  obtain ⟨hcs, hcf⟩ := List.mem_filter.mp hc
  obtain ⟨y, hy, hyc⟩ := exists_mem_s8 hcs
  have hval : Valid8 c := (subB_spec s8Basic_spec.1).1 _ hcs
  have hyc' : colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c := by rw [hyc, colsOf_dec8 hval]
  refine ⟨y, hy, ?_, hyc'⟩
  rw [mulVec_vec8, hyc', beq_iff_eq.mp hcf]

theorem mem_Z8_of {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ s8)
    (hfix : (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR)
    (hsq : x * x = 1)
    (hcomm : ∀ n ∈ s8, (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR →
      x * (n * x * n⁻¹) = (n * x * n⁻¹) * x) : x ∈ Z8 := by
  rw [mem_Z8_iff]
  refine zB_spec.2.2.2.2 _ (colsOf_mem_stE hx hfix) ?_ ?_
  · rw [← colsOf_mul, ← Units.val_mul, hsq, Units.val_one, colsOf_one]
  · intro n' hn'
    obtain ⟨n, hn, hnfix, hnn⟩ := exists_of_stE hn'
    have hinv := colsOf_inv_st (n := n) (by rw [hnn]; exact hn')
    rw [hnn] at hinv
    have := congrArg (fun y : GL (Fin 8) (ZMod 2) => colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)))
      (hcomm n hn hnfix)
    simp only [Units.val_mul, colsOf_mul, hnn, hinv] at this
    exact this

@[expose] def N8 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub n8G

theorem nB_spec :
    (elemsOf n8G).length = 8 ∧ subB n8G (elemsOf n8G) = true ∧ (∀ g ∈ n8G, g ∈ elemsOf z8G) ∧
      (∀ n ∈ stE, ∀ x ∈ elemsOf n8G, mul8 (mul8 n x) (invSt n) ∈ elemsOf n8G) ∧
      ∀ x ∈ elemsOf z8G, x ∈ elemsOf n8G ∨
        ((elemsOf (stE.map fun n => mul8 (mul8 n x) (invSt n))).length = 16 ∧
          nodupB (elemsOf (stE.map fun n => mul8 (mul8 n x) (invSt n))) = true) := by
  have h := s8Check_parts.2.2.2.2.1
  simp only [nB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem N8_gens_mem : ∀ g ∈ n8G, g ∈ s8E := by
  intro g hg
  obtain ⟨u, hu, hu'⟩ : ∃ u ∈ Z8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
    obtain ⟨w, hw⟩ := mem_elemsOf (nB_spec.2.2.1 g hg)
    rw [hw]
    exact exists_evalW z8G (subB_spec zB_spec.2.1).2.2.2.2 (unit_of_s8E zB_spec.2.2.1) w
  have hval : Valid8 g := (subB_spec nB_spec.2.1).2.2.2.2 g hg
  rw [← colsOf_dec8 hval, ← hu']
  exact colsOf_mem_s8E (Z8_le_s8 hu)

theorem mem_N8_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ N8 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf n8G :=
  mem_genSub_iff_of nB_spec.2.1 (unit_of_s8E N8_gens_mem) u

theorem card_N8 : Nat.card N8 = 8 := by
  rw [N8, card_genSub_of nB_spec.2.1 (unit_of_s8E N8_gens_mem), nB_spec.1]

theorem N8_le_Z8 : N8 ≤ Z8 :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_Z8_iff u).mpr (nB_spec.2.2.1 _ hu)

theorem eq_Z8_of {K : Subgroup (GL (Fin 8) (ZMod 2))} (hKZ : K ≤ Z8)
    (hKn : ∀ n ∈ s8, (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR →
      ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    {x : GL (Fin 8) (ZMod 2)} (hxK : x ∈ K) (hxN : x ∉ N8) : K = Z8 := by
  have hxZ := (mem_Z8_iff x).mp (hKZ hxK)
  rcases nB_spec.2.2.2.2 _ hxZ with h | ⟨h16, hnd⟩
  · exact absurd ((mem_N8_iff x).mpr h) hxN
  refine Subgroup.eq_of_le_of_card_ge hKZ ?_
  rw [card_Z8, ← h16]
  set gens := stE.map fun n => mul8 (mul8 n (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))))
    (invSt n) with hgens
  have hgK : ∀ c ∈ gens, ∃ u ∈ K, colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c := by
    intro c hc
    obtain ⟨n', hn', rfl⟩ := List.mem_map.mp hc
    obtain ⟨n, hn, hnfix, hnn⟩ := exists_of_stE hn'
    have hinv := colsOf_inv_st (n := n) (by rw [hnn]; exact hn')
    refine ⟨n * x * n⁻¹, hKn n hn hnfix x hxK, ?_⟩
    rw [Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul, hinv, hnn]
  have hgval : ∀ c ∈ gens, Valid8 c := fun c hc => by
    obtain ⟨u, -, hu⟩ := hgK c hc
    rw [← hu]
    exact valid8_colsOf _
  have hgunit : ∀ c ∈ gens, ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := fun c hc => by
    obtain ⟨u, -, hu⟩ := hgK c hc
    exact ⟨u, by rw [← hu, dec8_colsOf]⟩
  have hle : genSub gens ≤ K := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    obtain ⟨u', hu'K, hu'c⟩ := hgK _ hu
    have : u = u' := eq_of_colsOf_eq hu'c.symm
    rw [this]
    exact hu'K
  refine le_card_of_list (nodup_of_nodupB hnd) (fun b hb => ?_) (fun b hb => ?_)
  · obtain ⟨w, rfl⟩ := mem_elemsOf hb
    obtain ⟨u, hu, hu'⟩ := exists_evalW gens hgval hgunit w
    exact ⟨u, hle hu, hu'⟩
  · obtain ⟨w, rfl⟩ := mem_elemsOf hb
    exact valid8_evalW gens hgval w

theorem wB_spec :
    (∀ p ∈ eW8, p.1 ∈ elemsOf n8G ∧ b4N p.2 vR = false) ∧ eSpan8.length = 16 ∧
      eSpan8.Nodup := by
  have h := s8Check_parts.2.2.2.2.2.1
  simp only [wB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  simp only [nodupN, decide_eq_true_eq] at h3
  have h4 : (eSpan8.mergeSort).Nodup :=
    (List.isChain_iff_pairwise.mp h3).imp (fun hab => ne_of_lt hab)
  exact (List.mergeSort_perm _ _).nodup_iff.mp h4

theorem eSpan8_mem (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ p ∈ eW8, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) : ∀ c ∈ eSpan8, vec8 c ∈ W := by
  refine spanN_mem _ W ?_
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact hW p hp

theorem eSpan8_lt : ∀ c ∈ eSpan8, c < 256 := by decide

theorem card_le_of_eSpan8 (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ p ∈ eW8, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) : 16 ≤ Nat.card W := by
  classical
  have hmem := eSpan8_mem W hW
  let f : {c // c ∈ eSpan8} → W := fun c => ⟨vec8 c.1, hmem c.1 c.2⟩
  have hf : Function.Injective f := fun c c' h => Subtype.ext (vec8_inj (eSpan8_lt _ c.2)
    (eSpan8_lt _ c'.2) (congrArg Subtype.val h))
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (List.mem_toFinset (l := eSpan8) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup wB_spec.2.2,
    wB_spec.2.1] at h

theorem dotN_spec (c w : ℕ) : b2z (dotN c w) = vec8 c ⬝ᵥ vec8 w := by
  simp only [dotN, b2z_xor, b2z_and, dotProduct, Fin.sum_univ_eight, vec8, bt]
  rfl

theorem fB_spec :
    dotN cF vR = false ∧ ∀ x ∈ elemsOf n8G, ∃ w ∈ eSpan8,
      mv8 x w ≠ (w ^^^ (if dotN cF w then vR else 0)) := by
  have h := s8Check_parts.2.2.2.2.2.2
  simp only [fB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
    bne_iff_ne, ne_eq] at h
  exact h

theorem not_transv {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ N8)
    (h : ∀ c ∈ eSpan8, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 c) =
      vec8 c + (vec8 cF ⬝ᵥ vec8 c) • vec8 vR) : False := by
  obtain ⟨w, hw, hne⟩ := fB_spec.2 _ ((mem_N8_iff x).mp hx)
  apply hne
  have h1 := h w hw
  rw [mulVec_vec8, ← dotN_spec] at h1
  have h2 : vec8 (w ^^^ (if dotN cF w then vR else 0)) = vec8 w + b2z (dotN cF w) • vec8 vR := by
    rw [vec8_xor, vec8_ite]
  have hw256 := eSpan8_lt w hw
  have hlt : (w ^^^ (if dotN cF w then vR else 0)) < 256 := by
    have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
    have hite : (if dotN cF w then vR else 0) < 256 := by
      split
      · decide
      · norm_num
    rw [h256] at hw256 hite ⊢
    exact Nat.xor_lt_two_pow hw256 hite
  exact vec8_inj (mv8_lt (valid8_colsOf _) _) hlt (h1.trans h2.symm)

end CFSG.Quasithin.H13.S8Cert
