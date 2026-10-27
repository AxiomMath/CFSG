module

public import CFSG.LargeExtraspecial.O62Sylow
public import CFSG.LargeExtraspecial.O62Span

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

theorem s16c1c_checkSylow : checkSylow true = true := by
  decide +kernel

theorem s16c1c_spec :
    (∀ w ∈ sylowWords true, ∀ n ∈ w, qB true n = true) ∧ [] ∈ sylowWords true ∧
    (∀ a ∈ sylowWords true, ∀ b ∈ sylowWords true,
      ∃ c ∈ sylowWords true, wordC c = mul (wordC a) (wordC b)) ∧
    (∀ a ∈ sylowWords true, ∃ c ∈ sylowWords true, wordC c = wordC a.reverse) ∧
    ((sylowWords true).map wordC).Nodup ∧ (sylowWords true).length = 128 ∧
    ((sylowWords true).filter fun w => w.length % 2 == 0).length = 64 := by
  have h := s16c1c_checkSylow
  simp only [checkSylow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem, List.mem_map] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, fun a ha b hb => ?_, fun a ha => h4 a ha, h5, h6, h7⟩
  exact h3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩

noncomputable def s16c1c_T : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) where
  carrier := {g | ∃ w ∈ sylowWords true, wordProd w = g}
  one_mem' := ⟨[], s16c1c_spec.2.1, wordProd_nil⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hcode⟩ := s16c1c_spec.2.2.1 a ha b hb
    refine ⟨c, hc, ?_⟩
    have h1 := hasCode_wordProd c
    rw [hcode] at h1
    exact h1.eq_of_equiv ((hasCode_wordProd a).mul (hasCode_wordProd b))
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc, hcode⟩ := s16c1c_spec.2.2.2.1 a ha
    refine ⟨c, hc, ?_⟩
    rw [wordProd_inv]
    exact (wordProd_eq_iff _ _).mpr hcode

theorem s16c1c_mem_T {g : V₀ ≃ₗ[ZMod 2] V₀} :
    g ∈ s16c1c_T ↔ ∃ w ∈ sylowWords true, wordProd w = g :=
  Iff.rfl

theorem s16c1c_T_le_O : s16c1c_T ≤ O₀ true := by
  rintro _ ⟨w, hw, rfl⟩
  exact wordProd_mem_orthogonalGroup (s16c1c_spec.1 w hw)

theorem s16c1c_injOn_wordProd : Set.InjOn wordProd {w | w ∈ sylowWords true} := by
  intro a ha b hb hab
  exact List.inj_on_of_nodup_map s16c1c_spec.2.2.2.2.1 ha hb ((wordProd_eq_iff a b).mp hab)

theorem s16c1c_card_T : Nat.card s16c1c_T = 128 := by
  classical
  have hset : ((s16c1c_T : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Set (V₀ ≃ₗ[ZMod 2] V₀)) =
      wordProd '' {w | w ∈ sylowWords true} := by
    ext g
    simp only [SetLike.mem_coe, s16c1c_mem_T, Set.mem_image, Set.mem_ofPred_eq]
  have hnd : (sylowWords true).Nodup := s16c1c_spec.2.2.2.2.1.of_map _
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, s16c1c_injOn_wordProd.ncard_image,
    ← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    s16c1c_spec.2.2.2.2.2.1]

theorem s16c1c_mem_T_inf_omega {g : V₀ ≃ₗ[ZMod 2] V₀} :
    g ∈ s16c1c_T ⊓ Ω₀ true ↔
      ∃ w ∈ (sylowWords true).filter (fun w => w.length % 2 == 0), wordProd w = g := by
  simp only [Subgroup.mem_inf, s16c1c_mem_T, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hΩ⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    rw [wordProd_mem_omegaGroup_iff (s16c1c_spec.1 w hw)] at hΩ
    exact Nat.even_iff.mp hΩ
  · rintro ⟨w, ⟨hw, hev⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, (wordProd_mem_omegaGroup_iff (s16c1c_spec.1 w hw)).mpr
      (Nat.even_iff.mpr hev)⟩

theorem s16c1c_card_T_inf_omega :
    Nat.card (s16c1c_T ⊓ Ω₀ true : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) = 64 := by
  classical
  set l := (sylowWords true).filter (fun w => w.length % 2 == 0) with hl
  have hset : ((s16c1c_T ⊓ Ω₀ true : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) :
      Set (V₀ ≃ₗ[ZMod 2] V₀)) = wordProd '' {w | w ∈ l} := by
    ext g
    simp only [SetLike.mem_coe, s16c1c_mem_T_inf_omega, Set.mem_image, Set.mem_ofPred_eq, hl]
  have hnd : (sylowWords true).Nodup := s16c1c_spec.2.2.2.2.1.of_map _
  have hinj : Set.InjOn wordProd {w | w ∈ l} := s16c1c_injOn_wordProd.mono fun w hw =>
    (List.mem_filter.mp hw).1
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, hinj.ncard_image,
    ← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter _),
    s16c1c_spec.2.2.2.2.2.2]

theorem s16c1c_exists_conj_mem_T {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (hP : P ≤ O₀ true)
    (h2 : IsPGroup 2 P) : ∃ g ∈ O₀ true, ∀ x ∈ P, g⁻¹ * x * g ∈ s16c1c_T := by
  have := finite_linearEquiv (V := V₀)
  refine exists_conj_mem_of_isPGroup s16c1c_T_le_O hP
    (IsPGroup.of_card (n := 7) s16c1c_card_T) h2 fun B hB hB2 => ?_
  rw [s16c1c_card_T]
  exact card_le_of_isPGroup finrank_V₀ (qModel_nondegenerate true) hB hB2

theorem s16c1c_exists_conj_mem_T_omega {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (hP : P ≤ Ω₀ true)
    (h2 : IsPGroup 2 P) :
    ∃ g ∈ Ω₀ true, ∀ x ∈ P, g⁻¹ * x * g ∈ s16c1c_T ⊓ Ω₀ true := by
  have := finite_linearEquiv (V := V₀)
  refine exists_conj_mem_of_isPGroup inf_le_right hP
    (IsPGroup.of_card (n := 6) s16c1c_card_T_inf_omega) h2 fun B hB hB2 => ?_
  rw [s16c1c_card_T_inf_omega]
  exact card_le_of_isPGroup_omega finrank_V₀ (qModel_nondegenerate true) hB hB2

theorem s16c1c_exists_coded_of_mem_T {x : V₀ ≃ₗ[ZMod 2] V₀} (hx : x ∈ s16c1c_T) :
    ∃ c ∈ (sylowWords true).map wordC, Coded x c := by
  obtain ⟨w, hw, rfl⟩ := s16c1c_mem_T.mp hx
  exact ⟨wordC w, List.mem_map_of_mem hw, coded_wordProd w⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
