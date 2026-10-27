module

public import CFSG.Permutation.BurnsideSchur.SchurRing

public section

namespace CFSG

open scoped Pointwise

namespace BurnsideSchur

variable {C : Type*} [AddCommGroup C]

section Counting

variable {E : AddSubgroup C} {A B : Set C}

private theorem vadd_subset (hA : A ⊆ E) (hEB : (E : Set C) + B ⊆ B) {z : C} (hz : z ∈ B) :
    z +ᵥ A ⊆ B := by
  rintro _ ⟨a, ha, rfl⟩
  simpa [add_comm] using hEB (Set.add_mem_add (hA ha) hz)

private theorem vadd_eq (hEB : (E : Set C) + B ⊆ B) {e : C} (he : e ∈ E) : e +ᵥ B = B := by
  have key {e : C} (he : e ∈ E) : e +ᵥ B ⊆ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact hEB (Set.add_mem_add he hb)
  refine (key he).antisymm fun b hb => ⟨-e + b, key (neg_mem he) ⟨b, hb, rfl⟩, ?_⟩
  simp

private theorem exists_coe_eq_union (hEB : (E : Set C) + B ⊆ B) (hnegB : -B = B)
    (hBB : ∀ b ∈ B, b +ᵥ B ⊆ B ∪ E) : ∃ U : AddSubgroup C, (U : Set C) = (E : Set C) ∪ B := by
  let U : AddSubgroup C :=
    { carrier := E ∪ B
      zero_mem' := Or.inl E.zero_mem
      add_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (add_mem ha hb)
        · exact Or.inr (hEB (Set.add_mem_add ha hb))
        · exact Or.inr (by simpa [add_comm] using hEB (Set.add_mem_add hb ha))
        · exact (hBB a ha ⟨b, hb, rfl⟩).symm
      neg_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (neg_mem ha)
        · exact Or.inr (hnegB ▸ Set.neg_mem_neg.2 ha) }
  exact ⟨U, rfl⟩

private theorem exists_coe_eq_diff (h0 : (0 : C) ∉ A) (hnegA : -A = A)
    (hAA : ∀ t ∈ A, (E : Set C) ⊆ A ∪ (t +ᵥ A)) :
    ∃ L : AddSubgroup C, (L : Set C) = (E : Set C) \ A := by
  have hneg {a : C} : -a ∈ A ↔ a ∈ A := by rw [← Set.mem_neg, hnegA]
  let L : AddSubgroup C :=
    { carrier := (E : Set C) \ A
      zero_mem' := ⟨E.zero_mem, h0⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun hab => ?_⟩
        obtain ha'' | ⟨c, hc, hca⟩ := hAA _ hab ha
        · exact ha' ha''
        · obtain rfl : c = -b :=
            eq_neg_of_add_eq_zero_right (by simpa [vadd_eq_add, add_assoc] using hca)
          exact hb' (hneg.1 hc)
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨neg_mem ha, fun h => ha' (hneg.1 h)⟩ }
  exact ⟨L, rfl⟩

private theorem neg_mem_of_mem (hA : A ⊆ E) (hB : Disjoint (E : Set C) B)
    (hneg : -(A ∪ B) = A ∪ B) {z : C} (hz : z ∈ B) : -z ∈ B := by
  have : -z ∈ A ∪ B := by
    rw [← Set.mem_neg, hneg]
    exact Or.inr hz
  exact this.resolve_left fun h => Set.disjoint_left.1 hB (by simpa using neg_mem (hA h)) hz

private theorem inter_vadd_eq (hA : A ⊆ E) (hB : Disjoint (E : Set C) B)
    (hEB : (E : Set C) + B ⊆ B) (hneg : -(A ∪ B) = A ∪ B) {z : C} (hz : z ∈ B) :
    A ∩ (z +ᵥ B) = A := by
  refine Set.inter_eq_left.2 fun a ha => Set.mem_vadd_set_iff_neg_vadd_mem.2 ?_
  simpa [add_comm] using hEB (Set.add_mem_add (hA ha) (neg_mem_of_mem hA hB hneg hz))

variable [Finite C]

private theorem ncard_inter_vadd_of_mem (hA : A ⊆ E) (hB : Disjoint (E : Set C) B)
    (hEB : (E : Set C) + B ⊆ B) {t : C} (ht : t ∈ E) :
    ((A ∪ B) ∩ (t +ᵥ (A ∪ B))).ncard = (A ∩ (t +ᵥ A)).ncard + B.ncard := by
  rw [Set.vadd_set_union, vadd_eq hEB ht, ← Set.inter_union_distrib_right,
    Set.ncard_union_eq ((hB.mono_left hA).mono_left Set.inter_subset_left)]

private theorem ncard_inter_vadd_of_mem_compl (hA : A ⊆ E) (hB : Disjoint (E : Set C) B)
    (hEB : (E : Set C) + B ⊆ B) {z : C} (hz : z ∈ B) :
    ((A ∪ B) ∩ (z +ᵥ (A ∪ B))).ncard =
      A.ncard + (A ∩ (z +ᵥ B)).ncard + (B ∩ (z +ᵥ B)).ncard := by
  have hzA := vadd_subset hA hEB hz
  have hAB : Disjoint A B := hB.mono_left hA
  have hzAB : Disjoint (z +ᵥ A) (z +ᵥ B) := Set.disjoint_vadd_set.2 hAB
  have hsplit :
      (A ∪ B) ∩ (z +ᵥ (A ∪ B)) = ((z +ᵥ A) ∪ A ∩ (z +ᵥ B)) ∪ B ∩ (z +ᵥ B) := by
    ext y
    simp only [Set.vadd_set_union, Set.mem_inter_iff, Set.mem_union]
    constructor
    · rintro ⟨hy | hy, hy' | hy'⟩
      · exact absurd (hzA hy') (Set.disjoint_left.1 hAB hy)
      · exact Or.inl (Or.inr ⟨hy, hy'⟩)
      · exact Or.inl (Or.inl hy')
      · exact Or.inr ⟨hy, hy'⟩
    · rintro ((hy | ⟨hy, hy'⟩) | ⟨hy, hy'⟩)
      · exact ⟨Or.inr (hzA hy), Or.inl hy⟩
      · exact ⟨Or.inl hy, Or.inr hy'⟩
      · exact ⟨Or.inr hy, Or.inr hy'⟩
  rw [hsplit, Set.ncard_union_eq, Set.ncard_union_eq, Set.ncard_vadd_set]
  · exact Set.disjoint_of_subset_right Set.inter_subset_left (Set.disjoint_of_subset_left hzA
      hAB.symm)
  · rw [Set.disjoint_union_left]
    exact ⟨hzAB.mono_right Set.inter_subset_right, hAB.mono Set.inter_subset_left
      Set.inter_subset_left⟩

private theorem two_mul_ncard_le (hA : A ⊆ E) {t : C} (ht : t ∈ E) :
    2 * A.ncard ≤ (A ∩ (t +ᵥ A)).ncard + (E : Set C).ncard := by
  have hunion : A ∪ (t +ᵥ A) ⊆ E := by
    refine Set.union_subset hA ?_
    rintro _ ⟨a, ha, rfl⟩
    exact add_mem ht (hA ha)
  have := Set.ncard_inter_add_ncard_union A (t +ᵥ A)
  have := Set.ncard_le_ncard hunion
  rw [Set.ncard_vadd_set] at *
  omega

private theorem ncard_add_ncard_le (hB : Disjoint (E : Set C) B) (hEB : (E : Set C) + B ⊆ B)
    {z : C} (hz : z ∈ B) : (B ∩ (z +ᵥ B)).ncard + (E : Set C).ncard ≤ B.ncard := by
  have hdisj : Disjoint (B ∩ (z +ᵥ B)) (z +ᵥ (E : Set C)) :=
    (Set.disjoint_vadd_set.2 hB).symm.mono_left Set.inter_subset_right
  have := Set.ncard_le_ncard (s := B ∩ (z +ᵥ B) ∪ (z +ᵥ (E : Set C)))
    (Set.union_subset Set.inter_subset_left (vadd_subset subset_rfl hEB hz))
  rwa [Set.ncard_union_eq hdisj, Set.ncard_vadd_set] at this

section Constant

variable (hA : A ⊆ E) (hB : Disjoint (E : Set C) B) (hEB : (E : Set C) + B ⊆ B) {c : ℕ}
  (hc : ∀ y ∈ A ∪ B, ((A ∪ B) ∩ (y +ᵥ (A ∪ B))).ncard = c)
include hA hB hEB hc

private theorem neg_union_eq (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hsymm : A ∪ B ⊆ -(A ∪ B) ∨ Disjoint (A ∪ B) (-(A ∪ B))) : -(A ∪ B) = A ∪ B := by
  rcases hsymm with h | h
  · exact (Set.neg_subset.2 h).antisymm h
  obtain ⟨t, ht⟩ := hAne
  obtain ⟨z, hz⟩ := hBne
  have hempty : A ∩ (z +ᵥ B) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ⟨ha, b, hb, hab⟩ => ?_
    have hb' : -b ∈ B := by simpa [← hab] using hEB (Set.add_mem_add (neg_mem (hA ha)) hz)
    exact Set.disjoint_left.1 h (Or.inr hb) (Set.mem_neg.2 (Or.inr hb'))
  have h₁ := ncard_inter_vadd_of_mem hA hB hEB (hA ht)
  have h₂ := ncard_inter_vadd_of_mem_compl hA hB hEB hz
  rw [hc _ (Or.inl ht)] at h₁
  rw [hc _ (Or.inr hz), hempty, Set.ncard_empty] at h₂
  have := two_mul_ncard_le hA (hA ht)
  have := ncard_add_ncard_le hB hEB hz
  have := (Set.ncard_pos).2 ⟨t, ht⟩
  omega

variable (hneg : -(A ∪ B) = A ∪ B)
include hneg

private theorem ncard_inter_vadd_add_ncard_eq_left (hBne : B.Nonempty) {t : C} (ht : t ∈ A) :
    (A ∩ (t +ᵥ A)).ncard + (E : Set C).ncard = 2 * A.ncard := by
  obtain ⟨z, hz⟩ := hBne
  have h₁ := ncard_inter_vadd_of_mem hA hB hEB (hA ht)
  have h₂ := ncard_inter_vadd_of_mem_compl hA hB hEB hz
  rw [hc _ (Or.inl ht)] at h₁
  rw [hc _ (Or.inr hz), inter_vadd_eq hA hB hEB hneg hz] at h₂
  have := two_mul_ncard_le hA (hA ht)
  have := ncard_add_ncard_le hB hEB hz
  omega

private theorem ncard_inter_vadd_add_ncard_eq_right (hAne : A.Nonempty) {z : C} (hz : z ∈ B) :
    (B ∩ (z +ᵥ B)).ncard + (E : Set C).ncard = B.ncard := by
  obtain ⟨t, ht⟩ := hAne
  have h₁ := ncard_inter_vadd_of_mem hA hB hEB (hA ht)
  have h₂ := ncard_inter_vadd_of_mem_compl hA hB hEB hz
  rw [hc _ (Or.inl ht)] at h₁
  rw [hc _ (Or.inr hz), inter_vadd_eq hA hB hEB hneg hz] at h₂
  have := two_mul_ncard_le hA (hA ht)
  have := ncard_add_ncard_le hB hEB hz
  omega

private theorem subset_union_vadd (hBne : B.Nonempty) {t : C} (ht : t ∈ A) :
    (E : Set C) ⊆ A ∪ (t +ᵥ A) := by
  have hsub : A ∪ (t +ᵥ A) ⊆ E := by
    refine Set.union_subset hA ?_
    rintro _ ⟨a, ha, rfl⟩
    exact add_mem (hA ht) (hA ha)
  refine (Set.eq_of_subset_of_ncard_le hsub ?_).ge
  have := Set.ncard_inter_add_ncard_union A (t +ᵥ A)
  have := ncard_inter_vadd_add_ncard_eq_left hA hB hEB hc hneg hBne ht
  rw [Set.ncard_vadd_set] at *
  omega

private theorem vadd_subset_union (hAne : A.Nonempty) {b : C} (hb : b ∈ B) :
    b +ᵥ B ⊆ B ∪ E := by
  have hsub : B ∪ E ⊆ B ∪ (b +ᵥ B) := by
    refine Set.union_subset_union_right _ fun e he => Set.mem_vadd_set_iff_neg_vadd_mem.2 ?_
    simpa [add_comm] using hEB (Set.add_mem_add he (neg_mem_of_mem hA hB hneg hb))
  have heq := Set.eq_of_subset_of_ncard_le hsub ?_
  · exact heq ▸ Set.subset_union_right
  have := Set.ncard_inter_add_ncard_union B (b +ᵥ B)
  have := ncard_inter_vadd_add_ncard_eq_right hA hB hEB hc hneg hAne hb
  rw [Set.ncard_vadd_set, Set.ncard_union_eq hB.symm] at *
  omega

end Constant

end Counting

open MulAction

variable [Finite C] {G : Subgroup (Equiv.Perm C)} (hG : ∀ c : C, Equiv.addRight c ∈ G)
include hG

private theorem ncard_inter_vadd_eq {x y : C} (hy : y ∈ suborbit G x) :
    (suborbit G x ∩ (y +ᵥ suborbit G x)).ncard = (suborbit G x ∩ (x +ᵥ suborbit G x)).ncard := by
  have := Fintype.ofFinite C
  have hT := isStable_suborbit (G := G) x
  have hmem := mul_mem (ofSet_mem_schurRing hG (R := ℤ) hT) (ofSet_mem_schurRing hG (hT.neg hG))
  simpa [coeff_ofSet_mul_ofSet] using coeff_eq_of_mem_suborbit hG hmem hy

theorem suborbit_eq_compl_zero_of_separating [IsPreprimitive G C] {x : C} (hx : x ≠ 0)
    {E : AddSubgroup C} (hin : (suborbit G x ∩ E).Nonempty) (hout : (suborbit G x \ E).Nonempty)
    (hEB : (E : Set C) + (suborbit G x \ E) ⊆ suborbit G x \ E) : suborbit G x = {0}ᶜ := by
  set T := suborbit G x
  set A := T ∩ E
  set B := T \ E
  have hTS : IsStable G T := isStable_suborbit x
  have hA : A ⊆ E := Set.inter_subset_right
  have hB : Disjoint (E : Set C) B := Set.disjoint_sdiff_right
  have hAB : A ∪ B = T := Set.inter_union_sdiff T E
  have h0 : (0 : C) ∉ T := zero_notMem_suborbit hx
  have hc (y : C) (hy : y ∈ A ∪ B) :
      ((A ∪ B) ∩ (y +ᵥ (A ∪ B))).ncard = (T ∩ (x +ᵥ T)).ncard := by
    rw [hAB] at hy ⊢
    exact ncard_inter_vadd_eq hG hy
  have hneg : -(A ∪ B) = A ∪ B :=
    neg_union_eq hA hB hEB hc hin hout (hAB ▸ suborbit_subset_or_disjoint (hTS.neg hG) x)
  have hnegT {y : C} : -y ∈ T ↔ y ∈ T := by rw [← Set.mem_neg, ← hAB, hneg]
  obtain ⟨U, hU⟩ := exists_coe_eq_union hEB (by ext y; simp [B, hnegT])
    fun b hb => vadd_subset_union hA hB hEB hc hneg hin hb
  obtain ⟨L, hL⟩ := exists_coe_eq_diff (fun h => h0 h.1) (by ext y; simp [A, hnegT])
    fun t ht => subset_union_vadd hA hB hEB hc hneg hout ht
  have hU_top : U = ⊤ := by
    rcases (hTS.closure hG).eq_bot_or_eq_top hG with h | h
    · have hx' : x ∈ AddSubgroup.closure T := AddSubgroup.subset_closure (mem_suborbit_self x)
      exact absurd (h ▸ hx' : x ∈ (⊥ : AddSubgroup C)) hx
    · rw [eq_top_iff, ← h, AddSubgroup.closure_le, hU, ← hAB]
      exact Set.union_subset_union_left _ hA
  have hL_bot : L = ⊥ := by
    have hst : AddAction.stabilizer C T = ⊥ := by
      refine ((hTS.stabilizer hG).eq_bot_or_eq_top hG).resolve_right fun h => h0 ?_
      have hx' : -x +ᵥ T = T := by
        rw [← AddAction.mem_stabilizer_iff, h]
        exact AddSubgroup.mem_top _
      exact hx' ▸ ⟨x, mem_suborbit_self x, neg_add_cancel x⟩
    rw [eq_bot_iff, ← hst]
    intro s hs
    rw [← SetLike.mem_coe, hL] at hs
    rw [AddAction.mem_stabilizer_iff]
    refine Set.eq_of_subset_of_ncard_le ?_ (Set.ncard_vadd_set s T).ge
    rintro _ ⟨y, hy, rfl⟩
    rw [← hAB] at hy ⊢
    rcases hy with hy | hy
    · refine Or.inl (by_contra fun hsy => ?_)
      have h₁ : s + y ∈ (L : Set C) := hL ▸ ⟨add_mem hs.1 (hA hy), hsy⟩
      have h₂ : -s ∈ (L : Set C) := hL ▸ ⟨neg_mem hs.1, fun h => hs.2 ⟨hnegT.1 h.1, by
        simpa using neg_mem h.2⟩⟩
      have h₃ : y ∈ (L : Set C) := by simpa using L.add_mem h₂ h₁
      exact (hL ▸ h₃ : y ∈ (E : Set C) \ A).2 hy
    · exact Or.inr (hEB (Set.add_mem_add hs.1 hy))
  refine Set.Subset.antisymm (fun y hy hy0 => h0 (hy0 ▸ hy)) fun y hy => ?_
  have hyU : y ∈ (U : Set C) := by simp [hU_top]
  rw [hU] at hyU
  refine hyU.elim (fun hyE => by_contra fun hyT => ?_) fun hyB => hyB.1
  have hyL : y ∈ (L : Set C) := hL ▸ ⟨hyE, fun h => hyT h.1⟩
  rw [hL_bot] at hyL
  exact hy hyL

end BurnsideSchur

end CFSG
