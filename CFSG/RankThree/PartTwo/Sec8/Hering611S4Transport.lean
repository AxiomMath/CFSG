module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3J3
public import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Subgroup CFSG CFSG.RankThree.PartTwo.Sec18

section Transport

variable {J J' : Type} [Group J] [Group J'] (φ : J ≃* J')

theorem card_comap_equiv (K : Subgroup J') : Nat.card (K.comap φ.toMonoidHom) = Nat.card K := by
  rw [comap_equiv_eq_map_symm', card_map_of_injective φ.symm.injective]

theorem isElemAbelian_comap_equiv {K : Subgroup J'} {p : ℕ} (h : CFSG.Open.IsElemAbelian p K) :
    CFSG.Open.IsElemAbelian p (K.comap φ.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h2 : φ (a : J) * φ (b : J) = φ (b : J) * φ (a : J) :=
      congrArg Subtype.val (h.1.is_comm.comm (⟨φ a, a.2⟩ : K) ⟨φ b, b.2⟩)
    apply Subtype.ext
    apply φ.injective
    show φ ((a : J) * b) = φ ((b : J) * a)
    rw [map_mul, map_mul]
    exact h2
  · have hx' : φ x ∈ K := hx
    have := h.2 (φ x) hx'
    apply φ.injective
    simpa [← map_pow] using this

theorem normalizer_comap_equiv (K : Subgroup J') :
    normalizer ((K.comap φ.toMonoidHom : Subgroup J) : Set J) =
      (normalizer (K : Set J')).comap φ.toMonoidHom := by
  ext x
  simp only [mem_normalizer_iff, mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  constructor
  · intro h n'
    simpa using h (φ.symm n')
  · intro h n
    exact h (φ n)

theorem inSubgroup_perfectResidual_comap_equiv (K : Subgroup J') :
    inSubgroup perfectResidual (K.comap φ.toMonoidHom) =
      (inSubgroup perfectResidual K).comap φ.toMonoidHom := by
  rw [comap_equiv_eq_map_symm', comap_equiv_eq_map_symm',
    inSubgroup_perfectResidual_map φ.symm.toMonoidHom φ.symm.injective K]

theorem closure_preimage_equiv (S : Set J') :
    closure (φ ⁻¹' S) = (closure S).comap φ.toMonoidHom := by
  rw [comap_equiv_eq_map_symm', MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨φ x, hx, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    simpa using hs

theorem centralizer_singleton_comap_equiv (y : J) :
    centralizer ({y} : Set J) = (centralizer ({φ y} : Set J')).comap φ.toMonoidHom := by
  ext x
  simp only [mem_centralizer_singleton_iff, mem_comap, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply φ.injective
    simpa using h

theorem J3VPair.comap_equiv {kb ab : J} {V' : Fin 2 → Subgroup J'}
    (h : J3VPair J' (φ kb) (φ ab) V') :
    J3VPair J kb ab (fun i => (V' i).comap φ.toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨isElemAbelian_comap_equiv φ (h.elem i).1, by rw [card_comap_equiv]; exact (h.elem i).2⟩
  · intro i
    simp only [normalizer_comap_equiv, mem_comap, MulEquiv.coe_toMonoidHom]
    exact h.inv i
  · rw [comap_sup_eq φ.toMonoidHom _ _ φ.surjective, card_comap_equiv]
    exact h.card
  · intro i j
    simp only [normalizer_comap_equiv]
    exact comap_mono (h.norm i j)
  · intro i j
    simp only [normalizer_comap_equiv, inSubgroup_perfectResidual_comap_equiv]
    exact comap_mono (h.le_res i j)
  · intro i
    simp only [normalizer_comap_equiv, inSubgroup_perfectResidual_comap_equiv, mem_comap,
      MulEquiv.coe_toMonoidHom]
    exact h.ab_mem i
  · intro i
    simp only [normalizer_comap_equiv, inSubgroup_perfectResidual_comap_equiv]
    have hN := h.closure i
    have hset : {z : J | ∃ x ∈ (inSubgroup perfectResidual (normalizer (V' i : Set J'))).comap
        φ.toMonoidHom, z = x * ab * x⁻¹} =
        φ ⁻¹' {z' : J' | ∃ x' ∈ inSubgroup perfectResidual (normalizer (V' i : Set J')),
          z' = x' * φ ab * x'⁻¹} := by
      ext z
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨φ x, hx, by simp⟩
      · rintro ⟨x', hx', hz⟩
        refine ⟨φ.symm x', by simpa using hx', φ.injective ?_⟩
        simpa using hz
    rw [hset, closure_preimage_equiv, hN]
  · simp only [normalizer_comap_equiv, inSubgroup_perfectResidual_comap_equiv]
    rw [comap_sup_eq φ.toMonoidHom _ _ φ.surjective, h.gen, comap_top]
  · intro i σ hσ
    set σ' : MulAut J' := φ.symm.trans (σ.trans φ) with hσ'
    have hfix : ∀ v ∈ V' i, σ' v = v := by
      intro v hv
      have := hσ (φ.symm v) (by simpa [mem_comap] using hv)
      simp [hσ', this]
    obtain ⟨v', hv', hv'σ⟩ := h.aut i σ' hfix
    refine ⟨φ.symm v', by simpa [mem_comap] using hv', ?_⟩
    ext x
    have := congrArg (fun τ : MulAut J' => τ (φ x)) hv'σ
    simp only [hσ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
    apply φ.injective
    simpa using this
  · intro m hm
    obtain ⟨h1, w', hw', hne⟩ := h.four m hm
    have hL : (V' 0).comap φ.toMonoidHom ⊔ (V' 1).comap φ.toMonoidHom =
        (V' 0 ⊔ V' 1).comap φ.toMonoidHom := comap_sup_eq φ.toMonoidHom _ _ φ.surjective
    have hC : centralizer ({kb * ab ^ m} : Set J) ⊓ ((V' 0).comap φ.toMonoidHom ⊔
        (V' 1).comap φ.toMonoidHom) =
        (centralizer ({φ kb * φ ab ^ m} : Set J') ⊓ (V' 0 ⊔ V' 1)).comap φ.toMonoidHom := by
      rw [hL, comap_inf, centralizer_singleton_comap_equiv φ (kb * ab ^ m)]
      simp
    rw [hC, card_comap_equiv]
    refine ⟨h1, φ.symm w', ?_, fun hw => hne ?_⟩
    · simpa [mem_comap] using hw'
    · have := congrArg φ hw
      simpa using this

theorem J3TwoLocalFacts.of_mulEquiv {kb ab : J} (h : J3TwoLocalFacts J' (φ kb) (φ ab)) :
    J3TwoLocalFacts J kb ab := by
  have hC : centralizer ((closure ({kb, ab} : Set J) : Subgroup J) : Set J) =
      (centralizer ((closure ({φ kb, φ ab} : Set J') : Subgroup J') : Set J')).comap
        φ.toMonoidHom := by
    rw [centralizer_closure, centralizer_closure]
    ext x
    simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, mem_comap,
      MulEquiv.coe_toMonoidHom, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← map_mul, ← map_mul, h1], by rw [← map_mul, ← map_mul, h2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨φ.injective (by simpa using h1), φ.injective (by simpa using h2)⟩
  refine ⟨?_, ?_, ⟨fun i => (h.pair.choose i).comap φ.toMonoidHom,
    J3VPair.comap_equiv φ h.pair.choose_spec⟩⟩
  · rw [hC]
    exact ⟨isElemAbelian_comap_equiv φ h.B0.1, by rw [card_comap_equiv]; exact h.B0.2⟩
  · intro m hm
    obtain ⟨g', hg', hgm⟩ := h.fuse m hm
    refine ⟨φ.symm g', ?_, φ.injective ?_⟩
    · rw [hC, normalizer_comap_equiv, mem_comap]
      simpa using hg'
    · simpa using hgm

theorem J3TwoLocalFacts.inv_left {kb ab : J} (hcomm : kb * ab = ab * kb) (ha : ab ^ 3 = 1)
    (h : J3TwoLocalFacts J kb⁻¹ ab) : J3TwoLocalFacts J kb ab := by
  have hcl : closure ({kb⁻¹, ab} : Set J) = closure ({kb, ab} : Set J) := by
    apply le_antisymm
    · rw [closure_le]
      rintro x (rfl | rfl)
      · exact inv_mem (subset_closure (Or.inl rfl))
      · exact subset_closure (Or.inr rfl)
    · rw [closure_le]
      rintro x (rfl | rfl)
      · have h1 : x⁻¹ ∈ closure ({x⁻¹, ab} : Set J) := subset_closure (Or.inl rfl)
        simpa using inv_mem h1
      · exact subset_closure (Or.inr rfl)
  have hab : Commute kb ab := hcomm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcl]
    exact h.B0
  · intro m hm
    obtain ⟨g, hg, hgk⟩ := h.fuse (3 - m) (by omega)
    refine ⟨g, by rw [← hcl]; exact hg, ?_⟩
    have h1 := congrArg (fun z => z⁻¹) hgk
    simp only [mul_inv_rev, inv_inv] at h1
    have h2 : (ab ^ (3 - m))⁻¹ = ab ^ m := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show 3 - m + m = 3 by omega, ha]
    rw [mul_assoc, h1, h2]
    exact (hab.symm.pow_left m).eq
  · obtain ⟨V, hV⟩ := h.pair
    refine ⟨V, ?_⟩
    refine ⟨hV.elem, ?_, hV.card, hV.norm, hV.le_res, hV.ab_mem, hV.closure, hV.gen, hV.aut,
      ?_⟩
    · intro i
      exact ⟨by simpa using (hV.inv i).1, (hV.inv i).2⟩
    · intro m hm
      have key : ∀ m' : ℕ, (kb⁻¹ * ab ^ m')⁻¹ = kb * ab ^ m →
          centralizer ({kb * ab ^ m} : Set J) = centralizer ({kb⁻¹ * ab ^ m'} : Set J) := by
        intro m' he
        rw [← he]
        ext x
        simp only [mem_centralizer_singleton_iff]
        exact Commute.inv_right_iff
      have hab2 : (ab ^ 2)⁻¹ = ab :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact ha)
      have hab1 : ab⁻¹ = ab ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha)
      have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm3 with rfl | rfl | rfl
      · rw [key 0 (by simp [ha])]
        exact hV.four 0 hm
      · rw [key 2 (by rw [mul_inv_rev, inv_inv, hab2, pow_one]; exact hab.symm.eq)]
        exact hV.four 2 (by norm_num)
      · rw [key 1 (by rw [mul_inv_rev, inv_inv, pow_one, hab1]; exact (hab.symm.pow_left 2).eq)]
        exact hV.four 1 (by norm_num)

end Transport

end CFSG.RankThree.PartTwo.Sec8.Hering611
