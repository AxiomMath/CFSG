module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentStruct

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

theorem le_ncard_xSet
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) {v u : CVert}
    (hvu : u ∈ sphereDistThree v) : 38072 ≤ (xSet v u).ncard := by
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  obtain ⟨w, hw⟩ := (hP.2.2 v u hvu).1
  have hwu : cgraph.Adj u w := (cgraph.mem_neighborSet u w).1 hw.1
  have hA := ncard_inter_neighborSet_of_adj hwu.symm
  have hB := hP.2.1 v w hw.2
  have hvu' : cgraph.dist v u = 3 := mem_sphereDistThree.1 hvu
  have hvw : cgraph.dist v w = 2 := hw.2.1
  have hsub : cgraph.neighborSet w ∩ cgraph.neighborSet u ⊆
      (xSet v u \ {w}) ∪ ((cgraph.neighborSet w ∩ sphereDistThree v) \ {u}) := by
    rintro z ⟨hzw, hzu⟩
    have hwz : cgraph.Adj w z := (cgraph.mem_neighborSet w z).1 hzw
    have huz : cgraph.Adj u z := (cgraph.mem_neighborSet u z).1 hzu
    have hz1 : cgraph.dist v z ≤ 3 := by
      have h := dist_le_add_one_of_adj (v := v) hwz
      omega
    have hz2 : 3 ≤ cgraph.dist v z + 1 := by
      have h := dist_le_add_one_of_adj (v := v) huz.symm
      omega
    by_cases h3 : cgraph.dist v z = 3
    · refine Or.inr ⟨⟨hzw, h3⟩, fun e => ?_⟩
      rw [Set.mem_singleton_iff] at e
      exact cgraph.ne_of_adj huz e.symm
    · have h2 : cgraph.dist v z = 2 := by omega
      have hz34 : z ∈ sphereThree v ∪ sphereFour v := by
        rw [← setOf_dist_eq_two_eq_union exists_rootModel v]
        exact h2
      rcases hz34 with h3' | h4'
      · exact absurd hvu (hT v z u h3' huz.symm)
      · refine Or.inl ⟨⟨hzu, h4'⟩, fun e => ?_⟩
        rw [Set.mem_singleton_iff] at e
        exact cgraph.ne_of_adj hwz e.symm
  have huB : u ∈ cgraph.neighborSet w ∩ sphereDistThree v :=
    ⟨(cgraph.mem_neighborSet w u).2 hwu.symm, hvu⟩
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_union_le (xSet v u \ {w})
    ((cgraph.neighborSet w ∩ sphereDistThree v) \ {u})
  rw [Set.ncard_sdiff_singleton_of_mem hw, Set.ncard_sdiff_singleton_of_mem huB, hB] at h2
  have hX : 0 < (xSet v u).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨w, hw⟩
  omega

theorem natCard_pairStab
    (hP : DistThreePathInput) {v u : CVert} (hvu : u ∈ sphereDistThree v) :
    Nat.card (vStab v ⊓ vStab u : Subgroup Shat) = (xSet v u).ncard * 3397386240 := by
  obtain ⟨⟨w, hw⟩, htr, hst⟩ := hP.2.2 v u hvu
  have h := natCard_subgroup_eq_mul (vStab v ⊓ vStab u) w
  have horb : {x | ∃ s ∈ vStab v ⊓ vStab u, cvMul w s = x} = xSet v u := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨cvMul_mem_neighborSet hg.2 hw.1, mem_sphereFour_of_cvMul (mem_vStab.1 hg.1) hw.2⟩
    · intro hx
      obtain ⟨g, hgv, hgu, hgw⟩ := htr w hw x hx
      exact ⟨g, ⟨hgv, hgu⟩, hgw⟩
  rw [horb, hst w hw] at h
  exact h

theorem le_natCard_pairStab
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) {v u : CVert}
    (hvu : u ∈ sphereDistThree v) :
    129345288929280 ≤ Nat.card (vStab v ⊓ vStab u : Subgroup Shat) := by
  rw [natCard_pairStab hP hvu]
  have := le_ncard_xSet hP hT hvu
  omega

theorem natCard_subgroupOf_vStab
    (v u : CVert) :
    Nat.card ((vStab u).subgroupOf (vStab v)) = Nat.card (vStab v ⊓ vStab u : Subgroup Shat) := by
  rw [← Subgroup.inf_subgroupOf_left]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem subgroupOf_le_centralizer
    {v u : CVert} (s : vStab v) (hs : (s : Shat) = clabelS u) :
    (vStab u).subgroupOf (vStab v) ≤ Subgroup.centralizer {s} := by
  intro g hg
  have h := commute_clabelS_of_mem_vStab (Subgroup.mem_subgroupOf.1 hg)
  rw [← hs] at h
  exact Subgroup.mem_centralizer_singleton_iff.2
    (Commute.of_map (f := (vStab v).subtype) Subtype.val_injective h)

theorem finite_GStar :
    Finite GStar :=
  Nat.finite_of_card_ne_zero (by rw [card_GStar]; norm_num)

theorem natCard_centralizer_le
    {v : CVert} {ρ : vStab v →* GStar}
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (s : vStab v) :
    Nat.card (Subgroup.centralizer {s}) ≤ 2 * Nat.card (Subgroup.centralizer {ρ s}) := by
  have := finite_GStar
  set f := ρ.comp (Subgroup.centralizer {s}).subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.ker ≤ 2 := by
    have hinj : Nat.card f.ker ≤ Nat.card ρ.ker := by
      refine Nat.card_le_card_of_injective (fun x => ⟨(x : Subgroup.centralizer {s}), x.2⟩) ?_
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ρ.ker => ((z : vStab v))) hxy))
    have hk : Nat.card ρ.ker = 2 :=
      (congrArg (fun H : Subgroup (vStab v) => Nat.card H) hker).trans (natCard_zpowers_cStab v)
    omega
  have h3 : Nat.card f.range ≤ Nat.card (Subgroup.centralizer {ρ s}) := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨x, rfl⟩
    have hx : Commute (x : vStab v) s := Subgroup.mem_centralizer_singleton_iff.1 x.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (hx.map ρ)
  rw [← h1]
  calc Nat.card f.ker * Nat.card f.range ≤ 2 * Nat.card f.range := Nat.mul_le_mul_right _ h2
    _ ≤ 2 * Nat.card (Subgroup.centralizer {ρ s}) := Nat.mul_le_mul_left _ h3

theorem eq_conj_of_conj_eq {G : Type*} [Group G] {a x y : G} (h : a * x * a⁻¹ = y) :
    x = a⁻¹ * y * a⁻¹⁻¹ := by
  rw [← h]
  group

theorem eq_inl_mul_beta
    {γ : GStar} (h : γ.right ≠ 1) :
    γ = SemidirectProduct.inl γ.left * betaStarElt := by
  have hb : γ.right = ⟨betaG, Subgroup.mem_zpowers _⟩ := by
    rcases mem_betaGroup_iff.1 γ.right.2 with e | e
    · exact absurd (Subtype.ext e) h
    · exact Subtype.ext e
  calc γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
        (SemidirectProduct.inl_left_mul_inr_right γ).symm
    _ = SemidirectProduct.inl γ.left * betaStarElt := by rw [hb]

theorem exists_compat_beta
    (hO : DistThreeOuterInput) (hP : DistThreePathInput)
    (hT : TypeThreeBoundInput) {v u : CVert} (hvu : cgraph.dist v u = 3) (s : vStab v)
    (hs : (s : Shat) = clabelS u) :
    ∃ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass),
      IsCompatLocal v ρ iv ∧ ρ s = betaStarElt := by
  obtain ⟨ρ, iv, hc⟩ := exists_isCompatLocal v
  have hform := eq_inl_mul_beta (hO v u hvu ρ iv hc s hs)
  have hs2 : s * s = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hs, Subgroup.coe_one]
    exact clabelS_mul_clabelS u
  have hsq : (SemidirectProduct.inl (ρ s).left * betaStarElt) ^ 2 = 1 := by
    rw [← hform, sq, ← map_mul ρ s s, hs2, map_one]
  rcases CFSG.Monster.B.E6.FieldInvF4.xor_conj_of_sq_eq_one hsq with ⟨⟨g, hg⟩, -⟩ | ⟨⟨g, hg⟩, -⟩
  · refine ⟨conjRho g⁻¹ ρ, iv.trans (rootClassConj g⁻¹), hc.conj g⁻¹, ?_⟩
    rw [conjRho_apply, map_inv, inv_inv, hform]
    exact hg
  · exfalso
    have : Finite (vStab v) := Finite.of_injective _ Subtype.val_injective
    have hcs := natCard_centralizer_le (ker_eq_zpowers_cStab hc.2.1) s
    have hρs : ρ s = (SemidirectProduct.inl g)⁻¹ * CFSG.Monster.B.E6.FieldInvF4.tStar *
        (SemidirectProduct.inl g)⁻¹⁻¹ := by
      rw [hform]
      exact eq_conj_of_conj_eq hg
    rw [hρs, CFSG.Monster.B.E6.FieldInvF4.card_centralizer_conj,
      CFSG.Monster.B.E6.FieldInvF4.card_centralizer_tStar] at hcs
    have hR := le_natCard_pairStab hP hT (u := u) hvu
    have hRC : Nat.card (vStab v ⊓ vStab u : Subgroup Shat) ≤
        Nat.card (Subgroup.centralizer {s}) :=
      (natCard_subgroupOf_vStab v u).symm.le.trans
        (Subgroup.card_le_of_le (subgroupOf_le_centralizer s hs))
    omega

theorem orderOf_sLabel
    {v u : CVert} (s : vStab v) (hs : (s : Shat) = clabelS u) :
    orderOf s = 2 := by
  rw [← Subgroup.orderOf_coe, hs, orderOf_clabelS]

theorem relIndex_le_102
    {v u : CVert} (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    (hvu : u ∈ sphereDistThree v) (s : vStab v) (hs : (s : Shat) = clabelS u)
    (hC : Nat.card (Subgroup.centralizer {s}) = 13244506413465600) :
    ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) ≤ 102 := by
  have hle := subgroupOf_le_centralizer s hs
  have h1 := Subgroup.relIndex_mul_card ((vStab u).subgroupOf (vStab v))
    (Subgroup.centralizer {s})
  have h2 := congrArg (fun H : Subgroup (vStab v) => Nat.card H) (inf_eq_left.2 hle)
  rw [h2, natCard_subgroupOf_vStab, hC] at h1
  have hR := le_natCard_pairStab hP hT hvu
  by_contra hcon
  have h3 : 103 * 129345288929280 ≤
      ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) *
        Nat.card (vStab v ⊓ vStab u : Subgroup Shat) :=
    Nat.mul_le_mul (by omega) hR
  omega

theorem native_distance_three_canonical_F4_centralizer_image
    (hL : DistThreeLabelsInput)
    (hO : DistThreeOuterInput) (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    ∃ s c : vStab v, (s : Shat) = clabelS u ∧ (c : Shat) = clabelS v ∧
      (∃ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass),
        IsCompatLocal v ρ iv ∧ ρ s = betaStarElt) ∧
      (∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ρ s = betaStarElt →
          (∀ n ∈ jStar.comap ρ, Commute n s) ∧
          jStar.comap ρ ⊓ Subgroup.zpowers s = ⊥ ∧
          jStar.comap ρ ⊔ Subgroup.zpowers s = Subgroup.centralizer {s} ∧
          (∃ e : (jStar.comap ρ) × Subgroup.zpowers s ≃* Subgroup.centralizer {s},
            ∀ x, (e x : vStab v) = (x.1 : vStab v) * x.2) ∧
          ρ.ker = Subgroup.zpowers c ∧ Subgroup.zpowers c ≤ Subgroup.center (vStab v) ∧
          (∃ φ : jStar.comap ρ →* groupJ, Function.Surjective φ ∧
            φ.ker = (Subgroup.zpowers c).subgroupOf (jStar.comap ρ)) ∧
          Nat.card (jStar.comap ρ) = 6622253206732800) ∧
      Nonempty (groupJ ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card (Subgroup.centralizer {s}) = 13244506413465600 ∧
      (vStab u).subgroupOf (vStab v) ≤ Subgroup.centralizer {s} ∧
      ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) ≤ 102 ∧
      clabelS v ∈ vStab v ⊓ vStab u ∧ clabelS u ∈ vStab v ⊓ vStab u ∧
      clabelS u ≠ clabelS v ∧ Commute (clabelS u) (clabelS v) := by
  have hLvu := hL v u hvu
  have hsv : clabelS u ∈ vStab v := hLvu.1
  have hcu : clabelS v ∈ vStab u := hLvu.2.1
  have hex : ∃ s : vStab v, (s : Shat) = clabelS u := ⟨⟨clabelS u, hsv⟩, rfl⟩
  refine hex.elim (fun s hs => ?_)
  have hs2 := orderOf_sLabel s hs
  refine (exists_compat_beta hO hP hT hvu s hs).elim (fun ρ₀ h₀ => h₀.elim (fun iv₀ h₁ => ?_))
  have hC := natCard_centralizer_s h₁.1.1 (ker_eq_zpowers_cStab h₁.1.2.1) h₁.2 hs2
  refine ⟨s, cStab v, hs, rfl, ⟨ρ₀, iv₀, h₁⟩, fun ρ hsurj hker hρs => ?_,
    nonempty_groupJ_mulEquiv_F4, hC, subgroupOf_le_centralizer s hs,
    relIndex_le_102 hP hT hvu s hs hC, ⟨clabelS_mem_vStab_self v, hcu⟩,
    ⟨hsv, clabelS_mem_vStab_self u⟩, hLvu.2.2.1, hLvu.2.2.2⟩
  have hk := ker_eq_zpowers_cStab hker
  exact ⟨fun n hn => commute_of_mem hsurj hk hρs hn, comap_inf_zpowers hρs hs2,
    comap_sup_zpowers hsurj hk hρs hs2,
    ⟨prodCentralizer hsurj hk hρs hs2, coe_prodCentralizer hsurj hk hρs hs2⟩, hk,
    zpowers_cStab_le_center v, ⟨jHom ρ, jHom_surjective ρ hsurj, ker_jHom hk⟩,
    natCard_comap_jStar hsurj hk⟩

end CFSG.Monster.B.TwoA.Amalgam
