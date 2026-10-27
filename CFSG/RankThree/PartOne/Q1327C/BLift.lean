module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.N143.SectionGroup

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne

theorem exists_lift_elementary {M N : Type} [Group M] [Group N] [Finite M] [Finite N] {p : ℕ}
    (hp : p.Prime) (π : M →* N) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    {P' : Subgroup N} (hP' : IsElementaryAbelian p P') :
    ∃ P : Subgroup M, IsElementaryAbelian p P ∧ P.map π = P' ∧ Disjoint P π.ker := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hP'
  have hP'p : IsPGroup p P' := IsElementaryAbelian.isPGroup p P'
  let Pt : Subgroup M := P'.comap π
  obtain ⟨Q⟩ : Nonempty (Sylow p Pt) := inferInstance
  let Q' : Subgroup M := (Q : Subgroup ↥Pt).map Pt.subtype
  have hQ'Pt : Q' ≤ Pt := Subgroup.map_subtype_le _
  have hQ'p : IsPGroup p Q' := Q.isPGroup'.map Pt.subtype
  have hdis : Disjoint Q' π.ker := N143.disjoint_ker_of_isPGroup π hp hQ'p hker
  have hker_le : π.ker ≤ Pt := fun x hx => by
    show π x ∈ P'
    rw [MonoidHom.mem_ker.1 hx]
    exact P'.one_mem
  have hcardPt : Nat.card Pt = Nat.card π.ker * Nat.card P' := by
    have h1 := Subgroup.card_ker_mul_card_range (π.comp Pt.subtype)
    have hrange : (π.comp Pt.subtype).range = P' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective hπ P'
    have hker' : (π.comp Pt.subtype).ker = π.ker.subgroupOf Pt := by
      ext x
      simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [hrange, hker'] at h1
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv]
  have hcardQ : Nat.card Q' = Nat.card P' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
    have h1 : Nat.card Q' = Nat.card (Q : Subgroup ↥Pt) :=
      Nat.card_congr ((Q : Subgroup ↥Pt).equivMapOfInjective Pt.subtype
        Pt.subtype_injective).symm.toEquiv
    have h2 : (Nat.card π.ker).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hker
    rw [h1, Q.card_eq_multiplicity, hcardPt, hn,
      Nat.factorization_mul (Nat.card_pos.ne') (pow_ne_zero n hp.ne_zero), Finsupp.add_apply, h2,
      hp.factorization_pow, Finsupp.single_eq_same, zero_add]
  have hQ'le : Q'.map π ≤ P' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hQ'Pt hx
  have hQ'eq : Q'.map π = P' := by
    refine Subgroup.eq_of_le_of_card_ge hQ'le ?_
    rw [N143.card_map_of_disjoint_ker π hdis]
    exact hcardQ.ge
  have hinj' : ∀ x ∈ Q', ∀ y ∈ Q', π x = π y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ Q' ⊓ π.ker :=
      Subgroup.mem_inf.2 ⟨Q'.mul_mem (Q'.inv_mem hx) hy,
        MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    have h1 : x⁻¹ * y = 1 := Subgroup.disjoint_def.1 hdis (Subgroup.mem_inf.1 hmem).1
      (Subgroup.mem_inf.1 hmem).2
    exact inv_mul_eq_one.1 h1
  have hQ'el : IsElementaryAbelian p Q' := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply hinj' _ (Q'.mul_mem a.2 b.2) _ (Q'.mul_mem b.2 a.2)
      have ha : π (a : M) ∈ P' := hQ'le ⟨a, a.2, rfl⟩
      have hb : π (b : M) ∈ P' := hQ'le ⟨b, b.2, rfl⟩
      have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := P')).comm
        ⟨π (a : M), ha⟩ ⟨π (b : M), hb⟩)
      simpa using this
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      apply Subtype.ext
      apply hinj' _ (Q'.pow_mem x.2 p) 1 Q'.one_mem
      have hx : π (x : M) ∈ P' := hQ'le ⟨x, x.2, rfl⟩
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (A := P') _ hx
  exact ⟨Q', hQ'el, hQ'eq, hdis⟩

end CFSG.RankThree.PartOne.Q1327C
