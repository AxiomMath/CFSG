module

public import CFSG.RankThree.GF2n.Tim79aIdentConnected

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_conj_eq_of_opposite [Finite G] {A B : Subgroup G}
    (hsq : ∀ a ∈ A, a * a = 1) (hAB : Opposite A B) {e a : G} (he : e ∈ A) (he1 : e ≠ 1)
    (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ x ∈ Subgroup.normalizer (A : Set G), x * e * x⁻¹ = a := by
  obtain ⟨n, -, -, φ, hφA, -⟩ :=
    ElemAbRankOne.exists_mulEquiv_SL2' (hAB.isElemAbRankOne_of_mul_self hsq)
  set F := GaloisField 2 n
  have hmem : ∀ y : ↥(A ⊔ B), (y : G) ∈ A ↔ φ y ∈ upperUnipotent F := by
    intro y
    rw [← hφA, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  set e' : ↥(A ⊔ B) := ⟨e, Subgroup.mem_sup_left he⟩
  set a' : ↥(A ⊔ B) := ⟨a, Subgroup.mem_sup_left ha⟩
  obtain ⟨s, hs⟩ := (mem_upperUnipotent_iff F).1 ((hmem e').1 he)
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff F).1 ((hmem a').1 ha)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [upperElt_zero, MulEquiv.map_eq_one_iff] at hs
    exact he1 (congrArg Subtype.val hs)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [upperElt_zero, MulEquiv.map_eq_one_iff] at ht
    exact ha1 (congrArg Subtype.val ht)
  obtain ⟨l, hl⟩ := isSquare_of_charTwo' (t * s⁻¹)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero, mul_eq_zero] at hl
    exact hl.elim ht0 (inv_ne_zero hs0)
  set c : Fˣ := Units.mk0 l hl0
  set d : Matrix.SpecialLinearGroup (Fin 2) F := NaturalModule.diagElt c
  have hd : ∀ u : F, d * upperElt F u * d⁻¹ = upperElt F (l ^ 2 * u) := fun u => by
    rw [mul_inv_eq_iff_eq_mul, NaturalModule.diagElt_mul_upperElt, Units.val_mk0]
  set y : ↥(A ⊔ B) := φ.symm d
  have hφ : ∀ z : ↥(A ⊔ B), φ (y * z * y⁻¹) = d * φ z * d⁻¹ := fun z => by
    simp [y, map_mul, map_inv]
  refine ⟨(y : G), ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (y : G)).injective])
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu⟩ := (mem_upperUnipotent_iff F).1 ((hmem ⟨z, Subgroup.mem_sup_left hz⟩).1 hz)
    have hyz := (hmem (y * ⟨z, Subgroup.mem_sup_left hz⟩ * y⁻¹)).2 (by
      rw [hφ, hu, hd]
      exact (mem_upperUnipotent_iff F).2 ⟨_, rfl⟩)
    simpa using hyz
  · have h1 : φ (y * e' * y⁻¹) = φ a' := by
      rw [hφ, hs, hd, ht, pow_two, ← hl, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact congrArg Subtype.val (φ.injective h1)

theorem transvectionTorusStatement_holds :
    TransvectionTorusStatement := by
  intro K _ Δ hΔ _ A hA E hEA hE
  have := hΔ.finite
  obtain ⟨B, -, hAB⟩ := hΔ.cls.noIsolated hΔ.points hΔ.rank A hA
  obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  refine le_antisymm (iSup₂_le fun x hx => ?_) fun a ha => ?_
  · exact (Subgroup.map_mono hEA).trans_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp hx)
  · by_cases ha1 : a = 1
    · rw [ha1]
      exact Subgroup.one_mem _
    obtain ⟨x, hx, hxe⟩ := exists_mem_normalizer_conj_eq_of_opposite
      (hΔ.cls.root.mul_self A hA) hAB (hEA heE) he1' ha ha1
    refine Subgroup.mem_iSup_of_mem x (Subgroup.mem_iSup_of_mem hx ?_)
    rw [← hxe]
    exact conj_mem_conjSub x heE

end CFSG.RankThree.GF2n.Tim79a
