module

public import CFSG.RankThree.PartOne.CTP.AltGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Alt36

open Equiv Equiv.Perm

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def C3 (N : Subgroup (Perm Ω)) (x y z : Ω) : Prop :=
  swap x y * swap y z ∈ N

variable {N : Subgroup (Perm Ω)} {x y z p q r s u : Ω}

theorem C3.rot (h : C3 N x y z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : C3 N y z x := by
  unfold C3 at *
  rwa [CFSG.RankThree.PartOne.CTP.Alt.swap_mul_swap_rot hxy hyz hxz] at h

theorem C3.flip (h : C3 N x y z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : C3 N x z y := by
  have := N.inv_mem h
  unfold C3
  rwa [CFSG.RankThree.PartOne.CTP.Alt.swap_mul_swap_inv hxy hyz hxz] at this

theorem C3.comm (h1 : C3 N p q r) (h2 : C3 N r s u)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s)
    (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) : C3 N p s r := by
  have := N.mul_mem (N.mul_mem (N.mul_mem h1 h2) (N.inv_mem h1)) (N.inv_mem h2)
  unfold C3
  rwa [CFSG.RankThree.PartOne.CTP.Alt.swap_commutator hpq hpr hps hpu hqr hqs hqu hrs hru hsu] at this

section Union

variable {A B : Finset Ω}

theorem C3.mixed_outside
    (hNA : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ A → y ∈ A → z ∈ A → C3 N x y z)
    (hNB : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ B → y ∈ B → z ∈ B → C3 N x y z)
    (hA : 3 ≤ (A \ B).card) (hB : 3 ≤ (B \ A).card) {w₁ w₂ r : Ω} (hw₁ : w₁ ∈ A \ B)
    (hw₂ : w₂ ∈ B \ A) (hrA : r ∈ A) (hrB : r ∈ B) : C3 N w₁ w₂ r := by
  obtain ⟨s, hs, hsw⟩ := Finset.exists_mem_ne (by omega : 1 < (A \ B).card) w₁
  obtain ⟨t, ht, htw⟩ := Finset.exists_mem_ne (by omega : 1 < (B \ A).card) w₂
  rw [Finset.mem_sdiff] at hw₁ hw₂ hs ht
  have e1 : C3 N w₁ s r :=
    hNA _ _ _ hsw.symm (by rintro rfl; exact hs.2 hrB) (by rintro rfl; exact hw₁.2 hrB) hw₁.1 hs.1 hrA
  have e2 : C3 N r w₂ t :=
    hNB _ _ _ (by rintro rfl; exact hw₂.2 hrA) htw.symm (by rintro rfl; exact ht.2 hrA) hrB hw₂.1 ht.1
  exact e1.comm e2 hsw.symm (by rintro rfl; exact hw₁.2 hrB) (by rintro rfl; exact hw₁.2 hw₂.1)
    (by rintro rfl; exact hw₁.2 ht.1) (by rintro rfl; exact hs.2 hrB)
    (by rintro rfl; exact hs.2 hw₂.1) (by rintro rfl; exact hs.2 ht.1)
    (by rintro rfl; exact hw₂.2 hrA) (by rintro rfl; exact ht.2 hrA) htw.symm

theorem C3.mixed_second
    (hNA : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ A → y ∈ A → z ∈ A → C3 N x y z)
    (hNB : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ B → y ∈ B → z ∈ B → C3 N x y z)
    (hA : 3 ≤ (A \ B).card) (hB : 3 ≤ (B \ A).card) {r : Ω} (hrA : r ∈ A) (hrB : r ∈ B)
    {w₁ w₂ w₂' : Ω} (hw₁ : w₁ ∈ A \ B) (hw₂ : w₂ ∈ B \ A) (hw₂' : w₂' ∈ B \ A) (hne : w₂ ≠ w₂') :
    C3 N w₁ w₂ w₂' := by
  obtain ⟨e, he, hee⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {w₂, w₂'}) (t := B \ A) (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hee
  have e1 : C3 N w₁ r w₂' := by
    have h := C3.mixed_outside hNA hNB hA hB hw₁ hw₂' hrA hrB
    rw [Finset.mem_sdiff] at hw₁ hw₂'
    exact h.flip (by rintro rfl; exact hw₁.2 hw₂'.1) (by rintro rfl; exact hw₂'.2 hrA)
      (by rintro rfl; exact hw₁.2 hrB)
  rw [Finset.mem_sdiff] at hw₁ hw₂ hw₂' he
  have e2 : C3 N w₂' w₂ e :=
    hNB _ _ _ hne.symm (Ne.symm hee.1) (Ne.symm hee.2) hw₂'.1 hw₂.1 he.1
  exact e1.comm e2 (by rintro rfl; exact hw₁.2 hrB) (by rintro rfl; exact hw₁.2 hw₂'.1)
    (by rintro rfl; exact hw₁.2 hw₂.1) (by rintro rfl; exact hw₁.2 he.1)
    (by rintro rfl; exact hw₂'.2 hrA) (by rintro rfl; exact hw₂.2 hrA) (by rintro rfl; exact he.2 hrA)
    hne.symm (Ne.symm hee.2) (Ne.symm hee.1)

theorem contains3_union {r : Ω} (hrA : r ∈ A) (hrB : r ∈ B)
    (hA : 3 ≤ (A \ B).card) (hB : 3 ≤ (B \ A).card)
    (hNA : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ A → y ∈ A → z ∈ A → C3 N x y z)
    (hNB : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ B → y ∈ B → z ∈ B → C3 N x y z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hx : x ∈ A ∪ B) (hy : y ∈ A ∪ B)
    (hz : z ∈ A ∪ B) : C3 N x y z := by
  have hmix : ∀ {w₁ w₂ t : Ω}, w₁ ∈ A \ B → w₂ ∈ B \ A → t ∈ A ∪ B → t ≠ w₁ → t ≠ w₂ → C3 N w₁ w₂ t := by
    intro w₁ w₂ t hw₁ hw₂ ht ht₁ ht₂
    have hw : w₁ ≠ w₂ := fun h => (Finset.mem_sdiff.1 hw₁).2 (h ▸ (Finset.mem_sdiff.1 hw₂).1)
    by_cases htA : t ∈ A
    · by_cases htB : t ∈ B
      · exact C3.mixed_outside hNA hNB hA hB hw₁ hw₂ htA htB
      · have ht' : t ∈ A \ B := Finset.mem_sdiff.2 ⟨htA, htB⟩
        exact ((C3.mixed_second hNB hNA hB hA hrB hrA hw₂ hw₁ ht' ht₁.symm).rot hw.symm ht₁.symm
          ht₂.symm).flip ht₁.symm ht₂ hw
    · have htB : t ∈ B := (Finset.mem_union.1 ht).resolve_left htA
      exact C3.mixed_second hNA hNB hA hB hrA hrB hw₁ hw₂ (Finset.mem_sdiff.2 ⟨htB, htA⟩) ht₂.symm
  by_cases hAB : (x ∈ A \ B ∨ y ∈ A \ B ∨ z ∈ A \ B) ∧ (x ∈ B \ A ∨ y ∈ B \ A ∨ z ∈ B \ A)
  · obtain ⟨hP, hQ⟩ := hAB
    have hn : ∀ a, a ∈ A \ B → a ∉ B \ A := fun a ha hb =>
      (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 hb).1
    rcases hP with hxP | hyP | hzP <;> rcases hQ with hxQ | hyQ | hzQ
    · exact absurd hxQ (hn _ hxP)
    · exact hmix hxP hyQ hz hxz.symm hyz.symm
    · exact (hmix hxP hzQ hy hxy.symm hyz).flip hxz hyz.symm hxy
    · exact (((hmix hyP hxQ hz hyz.symm hxz.symm).flip hxy.symm hxz hyz).rot hyz hxz.symm
        hxy.symm).rot hxz.symm hxy hyz.symm
    · exact absurd hyQ (hn _ hyP)
    · exact ((hmix hyP hzQ hx hxy hxz).rot hyz hxz.symm hxy.symm).rot hxz.symm hxy hyz.symm
    · exact (hmix hzP hxQ hy hyz hxy.symm).rot hxz.symm hxy hyz.symm
    · exact ((hmix hzP hyQ hx hxz hxy).flip hyz.symm hxy.symm hxz.symm).rot hxz.symm hxy hyz.symm
    · exact absurd hzQ (hn _ hzP)
  · rw [not_and_or] at hAB
    rcases hAB with h | h
    · simp only [not_or, Finset.mem_sdiff, not_and, not_not] at h
      have hB' : ∀ a, a ∈ A ∪ B → (a ∈ A → a ∈ B) → a ∈ B := fun a ha hab =>
        (Finset.mem_union.1 ha).elim hab id
      exact hNB _ _ _ hxy hyz hxz (hB' x hx h.1) (hB' y hy h.2.1) (hB' z hz h.2.2)
    · simp only [not_or, Finset.mem_sdiff, not_and, not_not] at h
      have hA' : ∀ a, a ∈ A ∪ B → (a ∈ B → a ∈ A) → a ∈ A := fun a ha hab =>
        (Finset.mem_union.1 ha).elim id hab
      exact hNA _ _ _ hxy hyz hxz (hA' x hx h.1) (hA' y hy h.2.1) (hA' z hz h.2.2)

end Union

theorem contains3_biUnion (𝒳 : Finset (Finset Ω)) {r : Ω} (hr : ∀ A ∈ 𝒳, r ∈ A)
    (hpriv : ∀ A ∈ 𝒳, 3 ≤ (A \ (𝒳.erase A).biUnion id).card)
    (hN : ∀ A ∈ 𝒳, ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ A → y ∈ A → z ∈ A → C3 N x y z) :
    ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ 𝒳.biUnion id → y ∈ 𝒳.biUnion id → z ∈ 𝒳.biUnion id →
      C3 N x y z := by
  classical
  induction 𝒳 using Finset.induction_on with
  | empty =>
    intro x y z _ _ _ hx
    simp at hx
  | insert A 𝒳' hA ih =>
    rcases 𝒳'.eq_empty_or_nonempty with h0 | ⟨B, hB⟩
    · subst h0
      intro x y z hxy hyz hxz hx hy hz
      simp only [insert_empty_eq, Finset.singleton_biUnion, id] at hx hy hz
      exact hN A (Finset.mem_insert_self A ∅) x y z hxy hyz hxz hx hy hz
    · have hr' : ∀ C ∈ 𝒳', r ∈ C := fun C hC => hr C (Finset.mem_insert_of_mem hC)
      have hpriv' : ∀ C ∈ 𝒳', 3 ≤ (C \ (𝒳'.erase C).biUnion id).card := by
        intro C hC
        refine (hpriv C (Finset.mem_insert_of_mem hC)).trans (Finset.card_le_card ?_)
        refine Finset.sdiff_subset_sdiff le_rfl (Finset.biUnion_subset_biUnion_of_subset_left _ ?_)
        exact Finset.erase_subset_erase C (Finset.subset_insert A 𝒳')
      have hN' : ∀ C ∈ 𝒳', ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ C → y ∈ C → z ∈ C →
          C3 N x y z := fun C hC => hN C (Finset.mem_insert_of_mem hC)
      have hY := ih hr' hpriv' hN'
      have hAY : 3 ≤ (A \ 𝒳'.biUnion id).card := by
        have h := hpriv A (Finset.mem_insert_self A 𝒳')
        rwa [Finset.erase_insert hA] at h
      have hYA : 3 ≤ (𝒳'.biUnion id \ A).card := by
        refine (hpriv B (Finset.mem_insert_of_mem hB)).trans (Finset.card_le_card ?_)
        intro a ha
        rw [Finset.mem_sdiff] at ha ⊢
        refine ⟨Finset.mem_biUnion.2 ⟨B, hB, ha.1⟩, fun haA => ha.2 ?_⟩
        refine Finset.mem_biUnion.2 ⟨A, Finset.mem_erase.2 ⟨?_, Finset.mem_insert_self A 𝒳'⟩, haA⟩
        rintro rfl
        exact hA hB
      have hrY : r ∈ 𝒳'.biUnion id := Finset.mem_biUnion.2 ⟨B, hB, hr' B hB⟩
      intro x y z hxy hyz hxz hx hy hz
      rw [Finset.biUnion_insert] at hx hy hz
      exact contains3_union (hr A (Finset.mem_insert_self A 𝒳')) hrY hAY hYA
        (hN A (Finset.mem_insert_self A 𝒳')) hY hxy hyz hxz hx hy hz

theorem alternatingGroup_le_of_family [Fintype Ω] (𝒳 : Finset (Finset Ω)) {r : Ω}
    (hr : ∀ A ∈ 𝒳, r ∈ A) (hcov : ∀ x, ∃ A ∈ 𝒳, x ∈ A)
    (hpriv : ∀ A ∈ 𝒳, 3 ≤ (A \ (𝒳.erase A).biUnion id).card)
    (hN : ∀ A ∈ 𝒳, ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ A → y ∈ A → z ∈ A → C3 N x y z) :
    alternatingGroup Ω ≤ N := by
  have hU : ∀ x, x ∈ 𝒳.biUnion id := fun x => by
    obtain ⟨A, hA, hxA⟩ := hcov x
    exact Finset.mem_biUnion.2 ⟨A, hA, hxA⟩
  have hall := contains3_biUnion 𝒳 hr hpriv hN
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  obtain ⟨c, hc⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ3.card_support]
    norm_num
  have h1 := (hσ3.eq_swap_mul_swap_iff_mem_support (a := c)).mpr hc
  obtain ⟨hc1, hc2⟩ := List.nodup_cons.mp (hσ3.nodup_iff_mem_support.mpr hc)
  obtain ⟨hc3, -⟩ := List.nodup_cons.mp hc2
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hc1 hc3
  have h3 := hall _ _ _ hc1.1 hc3 hc1.2 (hU _) (hU _) (hU _)
  unfold C3 at h3
  rw [← h1] at h3
  exact h3

end CFSG.LocalAnalysis.UniquenessCase.UCK.Alt36
