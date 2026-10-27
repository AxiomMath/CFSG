module

public import CFSG.Timmesfeld.Bridge.RootClosureLocal
public import CFSG.Timmesfeld.Bridge.RootSetsQuot
public import CFSG.Timmesfeld.Exceptional.CaseIThm31

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

theorem closure_insert_centralizer_eq_top (h : Hyp G D) (hC : Moufang.ExcCollConnected D)
    {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) :
    Subgroup.closure (insert x {f | f ∈ D ∧ Commute d f}) = ⊤ := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  have hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy => conj_mem_of_isClass hclass g hy
  have hOD := oppositeDetermines_of_hyp h
  set R := Subgroup.closure (insert x {f | f ∈ D ∧ Commute d f}) with hR
  have hCR : ∀ f ∈ D, Commute d f → f ∈ R := fun f hf hdf =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨hf, hdf⟩)
  have hxR : x ∈ R := Subgroup.subset_closure (Set.mem_insert _ _)
  have hdR : d ∈ R := hCR d hd (Commute.refl d)
  set S := classIn R d with hS
  have hSD : S ⊆ D := classIn_subset_of_normal hN R hd
  have hdS : d ∈ S := mem_classIn_self R d
  have hopp : ∀ v ∈ S, ∀ y ∈ D, y ∈ R → Odd (orderOf (v * y)) → y ∈ S := by
    intro v hv y hy hyR hvy
    rw [hS, ← classIn_eq_of_mem hv]
    exact mem_classIn_of_odd hD (hSD hv) hy (classIn_subset R hdR hv) hyR hvy
  have hxS : x ∈ S := hopp d hdS x hx hxR hodd
  have hcol : ∀ a ∈ D, Commute d a → d * a ∈ D → a ∈ S := by
    intro a haD hda hdaD
    have haR := hCR a haD hda
    have hdaR := hCR (d * a) hdaD ((Commute.refl d).mul_right hda)
    have hnc := not_commute_of_opposite_of_line hD hd haD hda hdaD hx hdx hodd
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hx haD with hc | h4 | ⟨ho, -⟩
    · exact absurd hc.symm hnc.1
    ·
      obtain ⟨-, hoda⟩ := opposite_of_opposite_of_special_of_line hclass hD hd haD hda hdaD hx
        hdx hodd h4
      have hdaS : d * a ∈ S := hopp x hxS (d * a) hdaD hdaR (by rwa [orderOf_mul_comm_eq])
      have haT : a ∉ rootSet D d := by
        intro haT
        have hoa := (odd_orderOf_mul_iff_of_mem_rootSet hD hd haT hx hdx).2 hodd
        rw [orderOf_mul_comm_eq, h4] at hoa
        exact absurd hoa (by decide)
      obtain ⟨y, hyD, ⟨hay, hoay⟩, hnyd⟩ := exists_opposite_not_opposite hclass hOD hd haD haT
      have had : Commute a d := hda.symm
      have hadD : a * d ∈ D := by rwa [← hda.eq]
      have hyd4 : orderOf (y * d) = 4 := by
        have hndy := (not_commute_of_opposite_of_line hD haD hd had hadD hyD hay hoay).1
        rcases commute_or_orderOf_mul_eq_four_or_odd hD hyD hd with hc | h4' | ⟨ho, hnc'⟩
        · exact absurd hc.symm hndy
        · exact h4'
        · exact absurd ⟨fun hc => hnc' hc.symm, by rwa [orderOf_mul_comm_eq]⟩ hnyd
      obtain ⟨c, hcD, hcQ, -, -, hca⟩ := exists_conj_eq_mul_of_odd_special hD hN haD hyD hd hay
        hoay hyd4 had hadD
      have hcd : Commute c d := qdCore_commute hD hN haD hyD hd hay hoay hyd4 had c hcQ d
        self_mem_qdCore
      have hcR := hCR c hcD hcd.symm
      have hc2 := hD.mul_self_eq_one hcD
      have hcinv : c⁻¹ = c := hD.inv_eq hcD
      have hac : a = c * (d * a) * c⁻¹ := by
        rw [hcinv, hda.eq, ← hca, show c * (c * a * c) * c = (c * c) * a * (c * c) by group,
          hc2, one_mul, mul_one]
      rw [hac]
      exact conj_mem_classIn hdaS hcR
    · exact hopp x hxS a haD haR ho
  have hclosed : ∀ f ∈ S, ∀ y ∈ D, Commute f y → f * y ∈ D → y ∈ S := by
    rintro f ⟨r, hr, rfl⟩ y hy hfy hfyD
    set y' := r⁻¹ * y * r with hy'
    have hy'D : y' ∈ D := by simpa using hN r⁻¹ y hy
    have hdy' : Commute d y' := by
      have := (Commute.conj_iff r⁻¹).2 hfy
      simpa [hy', mul_assoc] using this
    have hdy'D : d * y' ∈ D := by
      have := hN r⁻¹ _ hfyD
      simpa [hy', mul_assoc] using this
    have hy'S := hcol y' hy'D hdy' hdy'D
    have hyeq : y = r * y' * r⁻¹ := by rw [hy']; group
    rw [hyeq]
    exact conj_mem_classIn hy'S hr
  have hall : D ⊆ S := hC S hSD ⟨d, hdS⟩ hclosed
  rw [eq_top_iff, ← h.gen, Subgroup.closure_le]
  exact fun y hy => classIn_subset R hdR (hall hy)

theorem noCommonCentral_of_collConnected (h : Hyp G D) (hC : Moufang.ExcCollConnected D) :
    Closure.NoCommonCentral D :=
  Closure.noCommonCentral_of_gen h fun _ hd _ hc hdc hodd =>
    closure_insert_centralizer_eq_top h hC hd hc hdc hodd

theorem noCommonCentral_of_tim75 (hT : Moufang.Tim75Thm31) {G : Type} [Group G] {D : Set G}
    (h : Hyp G D) : Closure.NoCommonCentral D :=
  noCommonCentral_of_collConnected h (Moufang.collConnected_of_hyp hT h)

end CFSG.Timmesfeld.Bridge.RootClosure
