module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.BruhatUnique

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.F4ExplicitPos.BruhatNo117

open CFSG.StandardType.F4ExplicitPos.PositiveNo117 CFSG.StandardType.F4ExplicitPos.UnipotentNo117

open scoped Pointwise

variable {K : Type} [Field K]

theorem f4_bruhatCell_injective :
    Function.Injective (bruhatCell Tag.F4 K) := by
  have key : ∀ (m : ℕ) (w : WeylGroup Tag.F4), (coxeterSystem Tag.F4).length w = m →
      ∀ v, bruhatCell Tag.F4 K w = bruhatCell Tag.F4 K v → w = v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro w hm v h
      by_cases hw : w = 1
      · subst hw
        exact (eq_one_of_bruhatCell_one_eq (τ := Tag.F4) h).symm
      obtain ⟨i, hi⟩ := exists_length_simple_mul_eq_sub_one (τ := Tag.F4) hw
      have hlen : (coxeterSystem Tag.F4).length (simple Tag.F4 i * w) < m := by
        have := (coxeterSystem Tag.F4).length_eq_zero_iff.not.2 hw
        omega
      have hmem : canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) ∈
          bruhatCell Tag.F4 K (simple Tag.F4 i) * bruhatCell Tag.F4 K v := by
        rw [← h, f4_bruhatCell_simple_mul_of_length_eq_sub_one hi]
        exact Or.inl (canonicalRep_mem_bruhatCell _)
      rcases f4_bruhatCell_simple_mul_subset i v hmem with h' | h'
      · exact mul_left_cancel (ih _ hlen _ rfl _
          (bruhatCell_eq_of_mem (canonicalRep_mem_bruhatCell _) h'))
      · have hsw := ih _ hlen _ rfl _ (bruhatCell_eq_of_mem (canonicalRep_mem_bruhatCell _)
          (h ▸ h'))
        have h1 : (coxeterSystem Tag.F4).simple i = 1 := mul_eq_right.1 hsw
        have := (coxeterSystem Tag.F4).length_simple i
        rw [h1, (coxeterSystem Tag.F4).length_one] at this
        exact absurd this zero_ne_one
  exact fun w v h => key _ w rfl v h

theorem f4_disjoint_bruhatCell
    {w w' : WeylGroup Tag.F4} (h : w ≠ w') :
    Disjoint (bruhatCell Tag.F4 K w) (bruhatCell Tag.F4 K w') :=
  Set.disjoint_left.2 fun _ hx hx' => h (f4_bruhatCell_injective (bruhatCell_eq_of_mem hx hx'))

theorem f4_bruhat_factor_unique
    {w w' : WeylGroup Tag.F4}
    {h h' u u' v v' : ModGL Tag.F4 K}
    (hh : h ∈ torusGroup Tag.F4 K) (hh' : h' ∈ torusGroup Tag.F4 K)
    (hu : u ∈ posUnipotent Tag.F4 K) (hu' : u' ∈ posUnipotent Tag.F4 K)
    (hv : v ∈ rootSpan Tag.F4 K (inversionSet w))
    (hv' : v' ∈ rootSpan Tag.F4 K (inversionSet w'))
    (heq : h * u * canonicalRep (coxeterSystem Tag.F4) K w * v =
           h' * u' * canonicalRep (coxeterSystem Tag.F4) K w' * v') :
    w = w' ∧ h = h' ∧ u = u' ∧ v = v' := by
  have hb : h * u ∈ borelGroup Tag.F4 K :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)
  have hb' : h' * u' ∈ borelGroup Tag.F4 K :=
    mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right hu')
  have hvB : v ∈ borelGroup Tag.F4 K :=
    ((rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα)).trans le_sup_right) hv
  have hvB' : v' ∈ borelGroup Tag.F4 K :=
    ((rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα)).trans le_sup_right) hv'
  have hcell : h * u * canonicalRep (coxeterSystem Tag.F4) K w * v ∈
      bruhatCell Tag.F4 K w :=
    mem_bruhatCell.2 ⟨h * u, hb, v, hvB, rfl⟩
  have hcell' : h' * u' * canonicalRep (coxeterSystem Tag.F4) K w' * v' ∈
      bruhatCell Tag.F4 K w' :=
    mem_bruhatCell.2 ⟨h' * u', hb', v', hvB', rfl⟩
  have hww : w = w' := by
    by_contra hne
    exact Set.disjoint_left.1 (f4_disjoint_bruhatCell hne) (heq ▸ hcell) hcell'
  subst hww
  obtain ⟨h1, h2, h3⟩ := f4_sameW_bruhat_unique hh hh' hu hu' hv hv' heq
  exact ⟨rfl, h1, h2, h3⟩

theorem f4_bijOn_bruhatCell
    (w : WeylGroup Tag.F4) :
    Set.BijOn (fun p : ModGL Tag.F4 K × ModGL Tag.F4 K =>
        p.1 * canonicalRep (coxeterSystem Tag.F4) K w * p.2)
      ((borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ×ˢ
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K)))
      (bruhatCell Tag.F4 K w) := by
  set n := canonicalRep (coxeterSystem Tag.F4) K w
  have hIB : rootSpan Tag.F4 K (inversionSet w) ≤ borelGroup Tag.F4 K :=
    (rootSpan_le_posUnipotent fun α h => inversionSet_pos (w := w) h).trans le_sup_right
  refine ⟨fun p hp => mem_bruhatCell.2 ⟨p.1, hp.1, p.2, hIB hp.2, rfl⟩, ?_, fun x hx => ?_⟩
  · rintro ⟨b, u⟩ ⟨hb, hu⟩ ⟨b', u'⟩ ⟨hb', hu'⟩ h
    simp only at h hb hu hb' hu'
    have hmem : b'⁻¹ * b = n * (u' * u⁻¹) * n⁻¹ :=
      calc b'⁻¹ * b = b'⁻¹ * (b * n * u) * u⁻¹ * n⁻¹ := by group
        _ = b'⁻¹ * (b' * n * u') * u⁻¹ * n⁻¹ := by rw [h]
        _ = n * (u' * u⁻¹) * n⁻¹ := by group
    have hneg : b'⁻¹ * b ∈ negUnipotent Tag.F4 K := by
      rw [hmem]
      exact canonicalRep_conj_mem_negUnipotent (mul_mem hu' (inv_mem hu))
    have h1 : b'⁻¹ * b ∈ borelGroup Tag.F4 K ⊓ negUnipotent Tag.F4 K :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hb') hb, hneg⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    rw [mul_left_cancel h]
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    obtain ⟨-, -, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} Tag.F4 K
    have hb'' : b' ∈ (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
        (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [← hHU]
      exact hb'
    obtain ⟨h, hh, v, hv, rfl⟩ := hb''
    rw [f4_posUnipotent_eq_mul_rootSpan w] at hv
    obtain ⟨uJ, huJ, uI, huI, rfl⟩ := hv
    have hnh : n * h * n⁻¹ ∈ torusGroup Tag.F4 K :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) h).1 hh
    refine ⟨(b * (n * h * n⁻¹) * (n * uJ * n⁻¹), uI), ⟨mul_mem (mul_mem hb
      (torusGroup_le_borelGroup hnh))
      (Subgroup.mem_sup_right (canonicalRep_conj_mem_posUnipotent huJ)), huI⟩, ?_⟩
    show b * (n * h * n⁻¹) * (n * uJ * n⁻¹) * n * uI = b * n * (h * (uJ * uI))
    group

theorem f4_card_rootSpan
    {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.F4 (a • α + b • β) →
      a • α + b • β ∈ S) :
    Nat.card (rootSpan Tag.F4 K S) = Nat.card K ^ S.ncard := by
  obtain ⟨α, hα, hrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos (τ := Tag.F4) hS)
  calc Nat.card (rootSpan Tag.F4 K S) = Nat.card (Set.univ : Set (Fin S.ncard → K)) :=
        Nat.card_congr (f4_bijOn_prod_pinnedX K hS hclosed α hα hrange).equiv.symm
    _ = Nat.card K ^ S.ncard := by rw [Nat.card_univ, Nat.card_fun, Nat.card_fin]

theorem f4_card_rootSpan_inversionSet
    (w : WeylGroup Tag.F4) :
    Nat.card (rootSpan Tag.F4 K (inversionSet w)) =
      Nat.card K ^ (coxeterSystem Tag.F4).length w := by
  rw [f4_card_rootSpan (fun _ h => inversionSet_pos (w := w) h) (inversionSet_closed w),
    ← (weyl_inversion_length Tag.F4).1 w]

theorem f4_card_posUnipotent :
    Nat.card (posUnipotent Tag.F4 K) =
      Nat.card K ^ {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard :=
  f4_card_rootSpan (fun _ h => h) fun α hα β hβ a b ha hb hr => ⟨hr, by
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    rw [f4_height_nsmul_add_nsmul]
    nlinarith [hα.2, hβ.2]⟩

theorem f4_card_borelGroup :
    Nat.card (borelGroup Tag.F4 K) =
      Nat.card (torusGroup Tag.F4 K) * Nat.card (posUnipotent Tag.F4 K) := by
  obtain ⟨-, -, -, -, hHU, -, huniq, -⟩ := triangular_borel_structure.{0, 0} Tag.F4 K
  have hbij : Set.BijOn (fun p : ModGL Tag.F4 K × ModGL Tag.F4 K => p.1 * p.2)
      ((torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ×ˢ
        (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)))
      (borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) := by
    refine ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun x hx => ?_⟩
    · rw [hHU]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · obtain ⟨h1, h2⟩ := huniq p.1 hp.1 q.1 hq.1 p.2 hp.2 q.2 hq.2 h
      exact Prod.ext h1 h2
    · rw [hHU] at hx
      obtain ⟨h, hh, u, hu, rfl⟩ := hx
      exact ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  calc Nat.card (borelGroup Tag.F4 K) = Nat.card ((torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ×ˢ
        (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K))) := Nat.card_congr hbij.equiv.symm
    _ = Nat.card (torusGroup Tag.F4 K) * Nat.card (posUnipotent Tag.F4 K) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl

theorem f4_card_bruhatCell
    (w : WeylGroup Tag.F4) :
    Nat.card (bruhatCell Tag.F4 K w) = Nat.card (torusGroup Tag.F4 K) *
      Nat.card K ^ ({α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard +
        (coxeterSystem Tag.F4).length w) := by
  calc Nat.card (bruhatCell Tag.F4 K w) = Nat.card ((borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ×ˢ
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K))) :=
        Nat.card_congr (f4_bijOn_bruhatCell (K := K) w).equiv.symm
    _ = Nat.card (borelGroup Tag.F4 K) * Nat.card (rootSpan Tag.F4 K (inversionSet w)) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl
    _ = _ := by
      rw [f4_card_borelGroup, f4_card_posUnipotent, f4_card_rootSpan_inversionSet, pow_add,
        mul_assoc]

theorem f4_card_adjointGroup
    [Finite K] :
    Nat.card (adjointGroup Tag.F4 K) = Nat.card (torusGroup Tag.F4 K) *
      Nat.card K ^ {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard *
        ∑ᶠ w : WeylGroup Tag.F4, Nat.card K ^ (coxeterSystem Tag.F4).length w := by
  classical
  have : Fintype (WeylGroup Tag.F4) := Fintype.ofFinite _
  have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
  have e : (adjointGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ≃
      Σ w : WeylGroup Tag.F4, bruhatCell Tag.F4 K w := by
    rw [f4_adjointGroup_eq_iUnion_bruhatCell]
    exact Set.unionEqSigmaOfDisjoint fun w w' h => f4_disjoint_bruhatCell h
  calc Nat.card (adjointGroup Tag.F4 K) = Nat.card (Σ w : WeylGroup Tag.F4,
      bruhatCell Tag.F4 K w) :=
        Nat.card_congr e
    _ = ∑ w : WeylGroup Tag.F4, Nat.card (bruhatCell Tag.F4 K w) := Nat.card_sigma
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [f4_card_bruhatCell, pow_add, mul_assoc]

end CFSG.StandardType.F4ExplicitPos.BruhatUnique

end

end
