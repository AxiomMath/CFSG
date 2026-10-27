module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem hasType424_of_central_kernel {C D : Type} [Group C] [Finite C] [Group D]
    (f : C →* D) (hker : f.ker ≤ Subgroup.center C) (hnorm : f.range.Normal)
    (h : Sec11.KS11Lie2Proof.HasType424 C) : Sec11.KS11Lie2Proof.HasType424 D := by
  obtain ⟨L, ⟨hLp, hLsn, hLq⟩, hT⟩ := h
  set L' := L.map f with hL'
  let g : L →* L' := f.subgroupMap L
  have hg : Function.Surjective g := f.subgroupMap_surjective L
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hZT : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    Sec11.FieldCentRigid82.center_eq_bot_of_isType424 hT
  have hkθ : g.ker ≤ aschbacherSolvableCore 3 L := by
    intro l hl
    have hlZ : (l : C) ∈ Subgroup.center C := by
      apply hker
      rw [MonoidHom.mem_ker]
      have h1 := congrArg Subtype.val hl
      exact h1
    rw [← QuotientGroup.eq_one_iff]
    have hc : (l : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      have hm : m * l = l * m := Subtype.ext (Subgroup.mem_center_iff.mp hlZ (m : C))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hm]
    rw [hZT, Subgroup.mem_bot] at hc
    exact hc
  have hks : Group.IsSolvable g.ker :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hkθ)
      (Subgroup.inclusion_injective hkθ)
  have hk3 : ¬ 3 ∣ Nat.card g.ker := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_dvd_of_le hkθ))
  obtain ⟨eθ⟩ := Sec4.Item426.nonempty_quotTheta_equiv_of_surjective g hg hks hk3
  refine ⟨L', ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Group.IsPerfect.map (f := f)
  ·
    set R := f.range with hR
    have hLR : L' ≤ R := Subgroup.map_le_range f L
    have hsub : (L'.subgroupOf R).IsSubnormal := by
      have hmap : L'.subgroupOf R = L.map f.rangeRestrict := by
        ext ⟨d, hd⟩
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, hL']
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c, hc, Subtype.ext rfl⟩
        · rintro ⟨c, hc, hcd⟩
          exact ⟨c, hc, congrArg Subtype.val hcd⟩
      rw [hmap]
      exact hLsn.map f.rangeRestrict_surjective
    exact Subgroup.IsSubnormal.trans hLR hsub hnorm.isSubnormal
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eθ hLq
  · exact Sec11.isType424_of_mulEquiv eθ.symm hT

@[expose] def fixSubConjHom {X S : Type} [Group X] [Group S] (ρ : X →* S) (y : X) :
    Sec4.Item426.fixSub (MulAut.conj y) →* Sec4.Item426.fixSub (MulAut.conj (ρ y)) :=
  (ρ.comp (Sec4.Item426.fixSub (MulAut.conj y)).subtype).codRestrict _ fun c => by
    rw [Sec4.Item426.mem_fixSub, MulAut.conj_apply]
    have hc : y * (c : X) * y⁻¹ = c := c.2
    change ρ y * ρ c * (ρ y)⁻¹ = ρ c
    rw [← map_inv, ← map_mul, ← map_mul, hc]

theorem fixSubConjHom_range_normal {X S : Type} [Group X] [Group S] (ρ : X →* S)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center X) (y : X) :
    (fixSubConjHom ρ y).range.Normal := by
  constructor
  rintro _ ⟨c, rfl⟩ ⟨d, hd⟩
  obtain ⟨x, rfl⟩ := hρ d
  have hd' : ρ y * ρ x * (ρ y)⁻¹ = ρ x := hd
  have hz : x⁻¹ * (y * x * y⁻¹) ∈ Subgroup.center X := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hd', inv_mul_cancel]
  have hc : y * (c : X) * y⁻¹ = c := c.2
  have hmem : x * (c : X) * x⁻¹ ∈ Sec4.Item426.fixSub (MulAut.conj y) := by
    rw [Sec4.Item426.mem_fixSub, MulAut.conj_apply]
    set z := x⁻¹ * (y * x * y⁻¹) with hzdef
    have hyx : y * x * y⁻¹ = x * z := by rw [hzdef]; group
    have hzc : ∀ g : X, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
    calc y * (x * (c : X) * x⁻¹) * y⁻¹
        = (y * x * y⁻¹) * (y * (c : X) * y⁻¹) * (y * x * y⁻¹)⁻¹ := by group
      _ = x * z * (c : X) * (x * z)⁻¹ := by rw [hyx, hc]
      _ = x * (z * (c : X)) * z⁻¹ * x⁻¹ := by group
      _ = x * ((c : X) * z) * z⁻¹ * x⁻¹ := by rw [hzc]
      _ = x * (c : X) * x⁻¹ := by group
  refine ⟨⟨x * (c : X) * x⁻¹, hmem⟩, ?_⟩
  apply Subtype.ext
  change ρ (x * (c : X) * x⁻¹) = ρ x * ρ c * (ρ x)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem fixSubConjHom_ker_le_center {X S : Type} [Group X] [Group S] (ρ : X →* S)
    (hker : ρ.ker ≤ Subgroup.center X) (y : X) :
    (fixSubConjHom ρ y).ker ≤ Subgroup.center (Sec4.Item426.fixSub (MulAut.conj y)) := by
  intro c hc
  have hcZ : (c : X) ∈ Subgroup.center X := by
    apply hker
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hc
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hcZ (g : X))

theorem hasType424_fixSub_conj_of_surjective {X S : Type} [Group X] [Finite X] [Group S]
    (ρ : X →* S) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center X) (y : X)
    (h : Sec11.KS11Lie2Proof.HasType424 (Sec4.Item426.fixSub (MulAut.conj y))) :
    Sec11.KS11Lie2Proof.HasType424 (Sec4.Item426.fixSub (MulAut.conj (ρ y))) :=
  hasType424_of_central_kernel (fixSubConjHom ρ y) (fixSubConjHom_ker_le_center ρ hker y)
    (fixSubConjHom_range_normal ρ hρ hker y) h

theorem false_of_noType424At3 {X S : Type} [Group X] [Finite X] [Group S]
    (e : X ⧸ Subgroup.center X ≃* S) (hS : NoType424At3 S) {y : X}
    (hy : y ∉ Subgroup.center X) (hy3 : y ^ 3 ∈ Subgroup.center X) {P : Subgroup X}
    (hP : P ∈ thetaComponentsIn (Sec4.Item426.fixSub (MulAut.conj y)))
    (hT : Sec11.IsType424 (P ⧸ aschbacherSolvableCore 3 P)) : False := by
  set ρ : X →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hρdef
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have hs1 : ρ y ≠ 1 := by
    rw [hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ne_eq,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy
  have hs3 : ρ y ^ 3 = 1 := by
    rw [← map_pow, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy3
  have hso : orderOf (ρ y) = 3 := orderOf_eq_prime hs3 hs1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hS (ρ y) hso (hasType424_fixSub_conj_of_surjective ρ hρ hker y
    (Sec11.KS11Lie2Proof.hasType424_of_mem hP hT))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent
