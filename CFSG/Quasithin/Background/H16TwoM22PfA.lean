module

public import CFSG.Quasithin.Background.H16TwoM22Check
public import CFSG.Quasithin.Background.HMathieuM21

public section

namespace CFSG.Quasithin.H.Mathieu.H16Pf

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

theorem eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

theorem comp_eq_of_fix {g : Equiv.Perm (Fin 24)} (hg : g ∈ AutPerm) {c : Fin 24 → ZMod 2}
    (hc : c ∈ C) (hw : hammingNorm c = 8)
    (h5 : 5 ≤ (Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 9 ∧ c i ≠ 0).card)
    (hfix : ∀ i : Fin 24, (i : ℕ) < 9 → g i = i) : c ∘ g = c := by
  set T := Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 9 ∧ c i ≠ 0
  set A := Finset.univ.filter fun i : Fin 24 => c i ≠ 0
  set A' := Finset.univ.filter fun i : Fin 24 => c (g i) ≠ 0
  have hA : A.card = 8 := hw
  have hA' : A'.card = 8 := by
    have : A' = A.map g.symm.toEmbedding := by
      ext i
      simp only [A, A', Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.toEmbedding_apply]
      exact ⟨fun h => ⟨g i, h, g.symm_apply_apply i⟩, fun ⟨a, ha, he⟩ => by
        rw [← he, Equiv.apply_symm_apply]; exact ha⟩
    rw [this, Finset.card_map, hA]
  have hTA : T ⊆ A ∩ A' := by
    intro i hi
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [A, A', Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      hfix i hi.1]
    exact ⟨hi.2, hi.2⟩
  by_contra hne
  have hd : c ∘ g + c ∈ C := C.add_mem (comp_mem_of_mem_AutPerm hg hc) hc
  have hd0 : c ∘ g + c ≠ 0 := fun h => hne (funext fun i =>
    eq_of_add_eq_zero _ _ (by simpa using congrFun h i))
  have h8 := eight_le_wt hd hd0
  have hsub : (Finset.univ.filter fun i => (c ∘ g + c) i ≠ 0) ⊆ (A ∪ A') \ T := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
      Function.comp_apply] at hi
    refine Finset.mem_sdiff.2 ⟨?_, fun hiT => ?_⟩
    · by_contra hn
      simp only [A, A', Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
        not_not] at hn
      rw [hn.1, hn.2, add_zero] at hi
      exact hi rfl
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hiT
      rw [hfix i hiT.1] at hi
      exact hi (CharTwo.add_self_eq_zero _)
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_union_add_card_inter A A'
  have hc3 := Finset.card_le_card hTA
  have hc4 := Finset.card_sdiff_add_card_inter (A ∪ A') T
  have hc5 : (A ∪ A') ∩ T = T := Finset.inter_eq_right.2 (hTA.trans Finset.inter_subset_union)
  rw [hc5] at hc4
  have hw' : hammingNorm (c ∘ g + c) =
      (Finset.univ.filter fun i => (c ∘ g + c) i ≠ 0).card := rfl
  omega

@[expose] def dArrs : List (Array ℕ) :=
  [#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    #[0, 1, 3, 4, 5, 2, 7, 6, 21, 19, 10, 12, 11, 13, 20, 18, 22, 16, 9, 15, 8, 14, 23, 17],
    #[0, 1, 4, 5, 2, 3, 6, 7, 14, 15, 10, 11, 12, 13, 8, 9, 23, 22, 19, 18, 21, 20, 17, 16],
    #[0, 1, 5, 2, 3, 4, 7, 6, 20, 18, 10, 12, 11, 13, 21, 19, 17, 23, 15, 9, 14, 8, 16, 22],
    #[0, 1, 3, 2, 5, 4, 6, 7, 14, 15, 13, 12, 11, 10, 8, 9, 17, 16, 18, 19, 20, 21, 23, 22],
    #[0, 1, 2, 5, 4, 3, 7, 6, 21, 19, 13, 11, 12, 10, 20, 18, 23, 17, 15, 9, 14, 8, 22, 16],
    #[0, 1, 5, 4, 3, 2, 6, 7, 8, 9, 13, 12, 11, 10, 14, 15, 22, 23, 19, 18, 21, 20, 16, 17],
    #[0, 1, 4, 3, 2, 5, 7, 6, 20, 18, 13, 11, 12, 10, 21, 19, 16, 22, 9, 15, 8, 14, 17, 23]]

@[expose] def dInvs : List (Array ℕ) :=
  [#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    #[0, 1, 5, 2, 3, 4, 7, 6, 20, 18, 10, 12, 11, 13, 21, 19, 17, 23, 15, 9, 14, 8, 16, 22],
    #[0, 1, 4, 5, 2, 3, 6, 7, 14, 15, 10, 11, 12, 13, 8, 9, 23, 22, 19, 18, 21, 20, 17, 16],
    #[0, 1, 3, 4, 5, 2, 7, 6, 21, 19, 10, 12, 11, 13, 20, 18, 22, 16, 9, 15, 8, 14, 23, 17],
    #[0, 1, 3, 2, 5, 4, 6, 7, 14, 15, 13, 12, 11, 10, 8, 9, 17, 16, 18, 19, 20, 21, 23, 22],
    #[0, 1, 2, 5, 4, 3, 7, 6, 21, 19, 13, 11, 12, 10, 20, 18, 23, 17, 15, 9, 14, 8, 22, 16],
    #[0, 1, 5, 4, 3, 2, 6, 7, 8, 9, 13, 12, 11, 10, 14, 15, 22, 23, 19, 18, 21, 20, 16, 17],
    #[0, 1, 4, 3, 2, 5, 7, 6, 20, 18, 13, 11, 12, 10, 21, 19, 16, 22, 9, 15, 8, 14, 17, 23]]

@[expose] def ctTab : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [0, 6, 15, 9, 14, 8, 1, 7, 3, 5, 12, 10, 13, 11, 2, 4],
    [0, 1, 4, 5, 2, 3, 6, 7, 9, 8, 13, 12, 11, 10, 15, 14],
    [0, 6, 14, 8, 15, 9, 1, 7, 5, 3, 11, 13, 10, 12, 4, 2],
    [0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8],
    [0, 6, 8, 14, 9, 15, 1, 7, 2, 4, 10, 12, 11, 13, 3, 5],
    [0, 1, 5, 4, 3, 2, 6, 7, 14, 15, 11, 10, 13, 12, 8, 9],
    [0, 6, 9, 15, 8, 14, 1, 7, 4, 2, 13, 11, 12, 10, 5, 3]]

@[expose] def mtTab : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
    [1, 2, 3, 0, 7, 4, 5, 6],
    [2, 3, 0, 1, 6, 7, 4, 5],
    [3, 0, 1, 2, 5, 6, 7, 4],
    [4, 5, 6, 7, 0, 1, 2, 3],
    [5, 6, 7, 4, 3, 0, 1, 2],
    [6, 7, 4, 5, 2, 3, 0, 1],
    [7, 4, 5, 6, 1, 2, 3, 0]]

@[expose] def c3A : List ℕ :=
  [0xc33c, 0xa0536, 0x900935, 0x11111e, 0x48211d, 0x82411b, 0x248117, 0x414127, 0x82411b,
    0x248117, 0x48211d, 0x18812b, 0x248117, 0x48211d, 0x82411b]

@[expose] def c3B : List ℕ :=
  [0xc00356, 0x50539, 0x60093a, 0x22112d, 0x84212e, 0x414127, 0x18812b, 0x81814d, 0x122147,
    0x84212e, 0x18812b, 0x122147, 0x28414e, 0x414127, 0x84212e]


theorem c3_check : ∀ p : Fin 24, 9 ≤ (p : ℕ) →
    syndM (c3A.getD (p - 9) 0) = 0 ∧ syndM (c3B.getD (p - 9) 0) = 0 ∧
    popc 24 (c3A.getD (p - 9) 0) = 8 ∧ popc 24 (c3B.getD (p - 9) 0) = 8 ∧
    5 ≤ (Finset.univ.filter fun i : Fin 24 =>
      (i : ℕ) < 9 ∧ bvec 24 (c3A.getD (p - 9) 0) i ≠ 0).card ∧
    5 ≤ (Finset.univ.filter fun i : Fin 24 =>
      (i : ℕ) < 9 ∧ bvec 24 (c3B.getD (p - 9) 0) i ≠ 0).card ∧
    bvec 24 (c3A.getD (p - 9) 0) p ≠ 0 ∧ bvec 24 (c3B.getD (p - 9) 0) p ≠ 0 ∧
    ∀ j : Fin 24, 9 ≤ (j : ℕ) → bvec 24 (c3A.getD (p - 9) 0) j ≠ 0 →
      bvec 24 (c3B.getD (p - 9) 0) j ≠ 0 → j = p := by
  decide +kernel

theorem eq_one_of_fix_nine {g : Equiv.Perm (Fin 24)} (hg : g ∈ AutPerm)
    (hfix : ∀ i : Fin 24, (i : ℕ) < 9 → g i = i) : g = 1 := by
  refine Equiv.ext fun p => ?_
  rw [Equiv.Perm.one_apply]
  by_cases hp : (p : ℕ) < 9
  · exact hfix p hp
  obtain ⟨hs1, hs2, hp1, hp2, h51, h52, hpA, hpB, huniq⟩ := c3_check p (by omega)
  have e1 := comp_eq_of_fix hg ((bvec_mem_C_iff _).2 hs1)
    ((hammingNorm_bvec 24 _).trans hp1) h51 hfix
  have e2 := comp_eq_of_fix hg ((bvec_mem_C_iff _).2 hs2)
    ((hammingNorm_bvec 24 _).trans hp2) h52 hfix
  have hgp : 9 ≤ ((g p : Fin 24) : ℕ) := by
    by_contra h
    have h' := g.injective (hfix (g p) (by omega))
    rw [h'] at h
    exact hp (by omega)
  refine huniq (g p) hgp ?_ ?_
  · have := congrFun e1 p
    simp only [Function.comp_apply] at this
    rw [this]
    exact hpA
  · have := congrFun e2 p
    simp only [Function.comp_apply] at this
    rw [this]
    exact hpB

@[expose] def fixO : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {g | g ∈ AutPerm ∧ ∀ i : Fin 24, (i : ℕ) < 8 → g i = i}
  mul_mem' := fun ha hb => ⟨AutPerm.mul_mem ha.1 hb.1, fun i hi => by
    rw [Equiv.Perm.mul_apply, hb.2 i hi, ha.2 i hi]⟩
  one_mem' := ⟨AutPerm.one_mem, fun _ _ => rfl⟩
  inv_mem' := fun {g} ha => ⟨AutPerm.inv_mem ha.1, fun i hi => by
    rw [Equiv.Perm.inv_eq_iff_eq, ha.2 i hi]⟩

theorem koPerm_val : ∀ t j : Fin 16,
    ((koPerm t ⟨8 + j, by omega⟩ : Fin 24) : ℕ) = 8 + ((j : ℕ) ^^^ t) := by
  decide +kernel

theorem koPerm_mul_self : ∀ t : Fin 16, koPerm t * koPerm t = 1 := by
  decide +kernel

theorem mem_fixO_iff (g : Equiv.Perm (Fin 24)) : g ∈ fixO ↔ ∃ t, g = koPerm t := by
  constructor
  · rintro ⟨hg, hfix⟩
    have h8 : 8 ≤ ((g 8 : Fin 24) : ℕ) := by
      by_contra h
      have h' := g.injective (hfix (g 8) (by omega))
      rw [h'] at h
      exact h (by decide)
    set s := ((g 8 : Fin 24) : ℕ) - 8 with hs
    have hs16 : s < 16 := by omega
    refine ⟨⟨s, hs16⟩, ?_⟩
    have hk : koPerm ⟨s, hs16⟩ * g = 1 := by
      refine eq_one_of_fix_nine (AutPerm.mul_mem
        (koArr_ok ⟨s, hs16⟩ |>.2.1 |> mem_AutPerm_of_arr (koArr_ok _).1) hg) fun i hi => ?_
      rw [Equiv.Perm.mul_apply]
      by_cases hi8 : (i : ℕ) < 8
      · rw [hfix i hi8, koPerm_apply_of_lt _ _ hi8]
      have hi' : i = ⟨8 + (0 : Fin 16), by omega⟩ := Fin.ext (by simp; omega)
      have hg8 : g i = ⟨8 + (⟨s, hs16⟩ : Fin 16), by omega⟩ := by
        rw [hi']; exact Fin.ext (by simp; omega)
      rw [hg8]
      apply Fin.ext
      rw [koPerm_val, Nat.xor_self, hi']
      simp
    rw [eq_inv_of_mul_eq_one_right hk, inv_eq_of_mul_eq_one_right (koPerm_mul_self _)]
  · rintro ⟨t, rfl⟩
    exact ⟨mem_AutPerm_of_arr (koArr_ok t).1 (koArr_ok t).2.1, fun i hi =>
      koPerm_apply_of_lt t i hi⟩

theorem fixO_le_mog22 : fixO ≤ mog22 := by
  intro g hg
  obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
  exact koPerm_mem_mog22 t

theorem isPGroup_fixO : IsPGroup 2 fixO := by
  intro ⟨g, hg⟩
  obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
  exact ⟨1, Subtype.ext (by simpa [pow_two] using koPerm_mul_self t)⟩

theorem mem_normalizer_fixO {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    (hO : ∀ i : Fin 24, ((σ i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8) :
    σ ∈ Subgroup.normalizer (fixO : Set (Equiv.Perm (Fin 24))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have e1 : ∀ x, σ (σ⁻¹ x) = x := fun x => σ.apply_symm_apply x
  have e2 : ∀ x, σ⁻¹ (σ x) = x := fun x => σ.symm_apply_apply x
  have hO' : ∀ i : Fin 24, (i : ℕ) < 8 → ((σ⁻¹ i : Fin 24) : ℕ) < 8 := fun i hi =>
    (hO (σ⁻¹ i)).1 (by rwa [e1])
  constructor
  · intro hg
    refine ⟨AutPerm.mul_mem (AutPerm.mul_mem hσ hg.1) (AutPerm.inv_mem hσ), fun i hi => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg.2 _ (hO' i hi), e1]
  · intro hg
    have hg' : g = σ⁻¹ * (σ * g * σ⁻¹) * σ := by group
    refine ⟨hg' ▸ AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hσ) hg.1) hσ,
      fun i hi => σ.injective ?_⟩
    have := hg.2 (σ i) ((hO i).2 hi)
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e2] at this

theorem dArrs_ok : ∀ j : Fin 8, InvPairOK 24 (dArrs.getD j #[]) (dInvs.getD j #[]) = true ∧
    autArrOK (dArrs.getD j #[]) (dInvs.getD j #[]) = true ∧
    (dArrs.getD j #[])[0]! = 0 ∧ (dArrs.getD j #[])[1]! = 1 := by
  decide +kernel

@[expose] def dPerm (j : Fin 8) : Equiv.Perm (Fin 24) :=
  permOfArr 24 (dArrs.getD j #[]) (dInvs.getD j #[]) (dArrs_ok j).1

theorem dPerm_mem_mog22 (j : Fin 8) : dPerm j ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr (dArrs_ok j).1 (dArrs_ok j).2.1)
    (hasArr_permOfArr (dArrs_ok j).1) (dArrs_ok j).2.2.1 (dArrs_ok j).2.2.2

@[expose] def xorF (s t : Fin 16) : Fin 16 := ⟨((s : ℕ) ^^^ t) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def ctF (j : Fin 8) (t : Fin 16) : Fin 16 :=
  ⟨((ctTab.getD j []).getD t 0) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def mtF (j k : Fin 8) : Fin 8 :=
  ⟨((mtTab.getD j []).getD k 0) % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def ivF (j : Fin 8) : Fin 8 := ⟨([0, 3, 2, 1, 4, 5, 6, 7].getD j 0) % 8,
  Nat.mod_lt _ (by norm_num)⟩

theorem koPerm_mul : ∀ s t : Fin 16, koPerm s * koPerm t = koPerm (xorF s t) := by
  decide +kernel

theorem dPerm_mul_koPerm : ∀ (j : Fin 8) (t : Fin 16),
    dPerm j * koPerm t = koPerm (ctF j t) * dPerm j := by
  decide +kernel

theorem dPerm_mul : ∀ j k : Fin 8, dPerm j * dPerm k = dPerm (mtF j k) := by
  decide +kernel

theorem dPerm_mul_ivF : ∀ j : Fin 8, dPerm j * dPerm (ivF j) = 1 := by
  decide +kernel

theorem koPerm_zero : koPerm 0 = 1 := by decide +kernel

theorem dPerm_zero : dPerm 0 = 1 := by decide +kernel

theorem dPerm_hexad : ∀ j j' : Fin 8, (∀ i : Fin 24, 2 ≤ (i : ℕ) → (i : ℕ) < 8 →
    dPerm j i = dPerm j' i) → j = j' := by
  decide +kernel

theorem dPerm_lt : ∀ (j : Fin 8) (i : Fin 24), (i : ℕ) < 8 → ((dPerm j i : Fin 24) : ℕ) < 8 := by
  decide +kernel

theorem koPerm_eight : ∀ t : Fin 16, ((koPerm t 8 : Fin 24) : ℕ) = 8 + t := by
  decide +kernel

@[expose] def PO : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {g | ∃ t j, g = koPerm t * dPerm j}
  mul_mem' := by
    rintro _ _ ⟨t, j, rfl⟩ ⟨t', j', rfl⟩
    refine ⟨xorF t (ctF j t'), mtF j j', ?_⟩
    rw [← koPerm_mul, ← dPerm_mul, mul_assoc, ← mul_assoc (dPerm j), dPerm_mul_koPerm]
    group
  one_mem' := ⟨0, 0, by rw [koPerm_zero, dPerm_zero, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨t, j, rfl⟩
    refine ⟨ctF (ivF j) t, ivF j, ?_⟩
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (dPerm_mul_ivF j),
      inv_eq_of_mul_eq_one_right (koPerm_mul_self t), dPerm_mul_koPerm]

theorem koPerm_mem_PO (t : Fin 16) : koPerm t ∈ PO := ⟨t, 0, by rw [dPerm_zero, mul_one]⟩

theorem dPerm_mem_PO (j : Fin 8) : dPerm j ∈ PO := ⟨0, j, by rw [koPerm_zero, one_mul]⟩

theorem PO_le_mog22 : PO ≤ mog22 := by
  rintro _ ⟨t, j, rfl⟩
  exact mog22.mul_mem (koPerm_mem_mog22 t) (dPerm_mem_mog22 j)

theorem card_PO : Nat.card PO = 128 := by
  have hinj : Function.Injective fun x : Fin 16 × Fin 8 =>
      (⟨koPerm x.1 * dPerm x.2, x.1, x.2, rfl⟩ : PO) := by
    rintro ⟨t, j⟩ ⟨t', j'⟩ h
    have h' : koPerm t * dPerm j = koPerm t' * dPerm j' := congrArg Subtype.val h
    have hj : j = j' := dPerm_hexad j j' fun i _ hi8 => by
      have := congrArg (fun g => g i) h'
      simp only [Equiv.Perm.mul_apply] at this
      rwa [koPerm_apply_of_lt _ _ (dPerm_lt j i hi8),
        koPerm_apply_of_lt _ _ (dPerm_lt j' i hi8)] at this
    subst hj
    have e := koPerm_eight t
    rw [mul_right_cancel h', koPerm_eight t'] at e
    exact Prod.ext (Fin.ext (by dsimp only; omega)) rfl
  have hsurj : Function.Surjective fun x : Fin 16 × Fin 8 =>
      (⟨koPerm x.1 * dPerm x.2, x.1, x.2, rfl⟩ : PO) := by
    rintro ⟨_, t, j, rfl⟩
    exact ⟨(t, j), rfl⟩
  rw [← Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card]
  rfl

theorem exists_conj_PO
    {N : Subgroup (Equiv.Perm (Fin 24))} (hN : N ≤ mog22) (hcard : Nat.card N = 5760) :
    ∃ g ∈ mog22, ∀ x ∈ PO, g * x * g⁻¹ ∈ N := by
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(N.subgroupOf mog22)) 2
    (n := 7) (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv, hcard]; norm_num)
  set S := H.map (N.subgroupOf mog22).subtype
  have hS : Nat.card S = 2 ^ 7 := by
    rw [← hH]
    exact Nat.card_congr (H.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm
  have hG : Nat.card mog22 = 443520 := card_mog22
  have hidx : ∀ X : Subgroup ↥mog22, Nat.card X = 2 ^ 7 → ¬ 2 ∣ X.index := by
    intro X hX
    have := X.card_mul_index
    rw [hX, Nat.card_congr (Equiv.refl _), hG] at this
    have h3 : X.index = 3465 := by omega
    rw [h3]
    decide
  have hP : Nat.card (PO.subgroupOf mog22) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe PO_le_mog22).toEquiv, card_PO]
    norm_num
  let S1 := (IsPGroup.of_card hS).toSylow (hidx S hS)
  let S2 := (IsPGroup.of_card hP).toSylow (hidx _ hP)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥mog22 S2 S1
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hx' : (⟨x, PO_le_mog22 hx⟩ : ↥mog22) ∈ (S2 : Subgroup ↥mog22) := hx
  have h1 : g * ⟨x, PO_le_mog22 hx⟩ * g⁻¹ ∈ (S1 : Subgroup ↥mog22) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨_, hx', rfl⟩
  obtain ⟨y, -, hy⟩ := h1
  have hy' := congrArg Subtype.val hy
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hy'
  exact hy' ▸ Subgroup.mem_subgroupOf.1 y.2

end CFSG.Quasithin.H.Mathieu.H16Pf
