module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MSU

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.SubgroupLists Matrix

section PSU

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem card_map_unitaryProj_of_card_eight {T : Subgroup (unitarySU 2 3 K 3)}
    (hT : Nat.card T = 8) : Nat.card (T.map (unitaryProj h 3)) = 8 := by
  have hinj : Function.Injective ((unitaryProj h 3).comp T.subtype) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzS : (z : unitarySU 2 3 K 3) ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj]
      exact hz
    have h3 := pow_three_eq_one_of_mem_unitaryScalars h hzS
    have h8 : (z : unitarySU 2 3 K 3) ^ 8 = 1 := by
      have := pow_card_eq_one' (G := T) (x := z)
      rw [hT] at this
      have h1 := congrArg Subtype.val this
      simpa using h1
    have hz1 : (z : unitarySU 2 3 K 3) = 1 := by
      calc (z : unitarySU 2 3 K 3) =
          ((z : unitarySU 2 3 K 3) ^ 3) ^ 3 * ((z : unitarySU 2 3 K 3) ^ 8)⁻¹ := by group
        _ = 1 := by rw [h3, h8]; group
    exact Subtype.ext hz1
  have hrange : ((unitaryProj h 3).comp T.subtype).range = T.map (unitaryProj h 3) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← hT]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem unitaryProj_suField (σ : K ≃+* K) (g : unitarySU 2 3 K 3) :
    unitaryProj h 3 (suField h σ g) = psuField h σ (unitaryProj h 3 g) := rfl

theorem unitaryProj_suConj (A : unitaryIsom3 h) (g : unitarySU 2 3 K 3) :
    unitaryProj h 3 (suConj h A g) = psuConj h A (unitaryProj h 3 g) := rfl

theorem psu_syl_model {σ : K ≃+* K} {ι : F →+* K} {l m : F} {D : unitaryIsom3 h}
    (hισ : ∀ a, σ (ι a) = ι a) (hD : RefData h ι l m D) :
    ∃ T : Subgroup (unitaryPSU h 3), T ≤ u38Fix (psuField h σ) ∧ Nat.card T = 8 ∧
      (∀ x ∈ T, psuConj h D x ∈ T) ∧ T ≤ u38Comm T (psuConj h D) := by
  obtain ⟨T, hTf, hT8, hTβ, hTc⟩ := core_syl h ι ι.injective hισ hD
  refine ⟨T.map (unitaryProj h 3), ?_, card_map_unitaryProj_of_card_eight h hT8, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [mem_u38Fix, ← unitaryProj_suField]
    exact congrArg _ (mem_u38Fix.mp (hTf ht))
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨suConj h D t, hTβ t ht, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h1 : t ∈ u38Comm T (suConj h D) := hTc ht
    have h2 : (u38Comm T (suConj h D)).map (unitaryProj h 3) ≤
        u38Comm (T.map (unitaryProj h 3)) (psuConj h D) := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨w, hw, rfl⟩
      show unitaryProj h 3 (w * (suConj h D w)⁻¹) ∈ u38Comm (T.map (unitaryProj h 3)) (psuConj h D)
      rw [map_mul, map_inv, unitaryProj_suConj]
      exact Subgroup.subset_closure ⟨unitaryProj h 3 w, ⟨w, hw, rfl⟩, rfl⟩
    exact h2 ⟨t, h1, rfl⟩

include h in
theorem psu_syl {α β : MulAut (unitaryPSU h 3)} (hyps : U38Hyps (unitaryPSU h 3) α β) :
    ∃ T : Subgroup (unitaryPSU h 3), T ≤ u38Fix α ∧ Nat.card T = 8 ∧ (∀ x ∈ T, β x ∈ T) ∧
      T ≤ u38Comm T β := by
  obtain ⟨hα3, hβ3, hαβ, hαout, hu4, hβ1, h7⟩ := hyps
  obtain ⟨G, D, σ, ι, l, m, hσ, hισ, hιs, hD, hα, hβ⟩ := nf_psu h hα3 hβ3 hαβ hαout
    (by obtain ⟨u, hu, h4, h2⟩ := hu4; exact ⟨u, mem_u38Fix.mp hu, h4, h2⟩) hβ1 h7
  set ψ : MulAut (unitaryPSU h 3) := psuConj h G with hψ
  have e1 : MulAut.congr (ψ⁻¹ : MulAut (unitaryPSU h 3)) α = psuField h σ := by
    rw [congr_eq_mul, hα]
    group
  have e2 : MulAut.congr (ψ⁻¹ : MulAut (unitaryPSU h 3)) β = psuConj h D := by
    rw [congr_eq_mul, hβ]
    group
  apply syl_conclusion_congr (ψ⁻¹ : MulAut (unitaryPSU h 3))
  rw [e1, e2]
  exact psu_syl_model h hισ hD

variable {σ : K ≃+* K}

theorem map_u38Two_le : (u38Two (suField h σ)).map (unitaryProj h 3) ≤ u38Two (psuField h σ) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hy, k, hk⟩
  show unitaryProj h 3 y ∈ u38Two (psuField h σ)
  refine Subgroup.subset_closure ⟨?_, k, ?_⟩
  · rw [mem_u38Fix, ← unitaryProj_suField, mem_u38Fix.mp hy]
  · rw [← map_pow, hk, map_one]

theorem u38Two_psuField_le :
    u38Two (psuField h σ) ≤ (u38Two (suField h σ)).map (unitaryProj h 3) := by
  have := h.finite
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hy, k, hk⟩
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 y
  obtain ⟨g', ⟨e, hge⟩, hπg', -⟩ := exists_two_element_lift (unitaryProj h 3) hk
  have hπ : unitaryProj h 3 (suField h σ g') = unitaryProj h 3 g' := by
    rw [unitaryProj_suField, hπg']
    exact mem_u38Fix.mp hy
  have hz : g'⁻¹ * suField h σ g' ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
  set z := g'⁻¹ * suField h σ g' with hzdef
  have hzc : z ∈ Subgroup.center (unitarySU 2 3 K 3) := unitaryScalars_le_center h 3 hz
  have hz3 := pow_three_eq_one_of_mem_unitaryScalars h hz
  have hσg : suField h σ g' = g' * z := by rw [hzdef]; group
  have hcomm : Commute g' z := Subgroup.mem_center_iff.mp hzc g'
  have hz2e : z ^ 2 ^ e = 1 := by
    have h1 : (suField h σ g') ^ 2 ^ e = 1 := by rw [← map_pow, hge, map_one]
    rw [hσg, hcomm.mul_pow, hge, one_mul] at h1
    exact h1
  have hz1 : z = 1 := by
    have hg : Nat.gcd 3 (2 ^ e) = 1 := Nat.Coprime.pow_right e (by norm_num)
    have h1 := pow_gcd_eq_one.mpr ⟨hz3, hz2e⟩
    rwa [hg, pow_one] at h1
  have hfix : suField h σ g' = g' := by rw [hσg, hz1, mul_one]
  exact ⟨g', Subgroup.subset_closure ⟨mem_u38Fix.mpr hfix, e, hge⟩, hπg'⟩

theorem mat_levi_22 {g : unitarySU 2 3 K 3} (hg : g ∈ leviSU3 (K := K) (2 ^ 3)) :
    mat g 2 2 = 1 := by
  obtain ⟨A, -, hA⟩ := hg
  have hA' : (g : GL (Fin 3) K) = blockGL3 A := hA.symm
  show ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1
  rw [hA']
  rfl

theorem psu_p3_model {ι : F →+* K} {l m : F} {D : unitaryIsom3 h}
    (hισ : ∀ a, σ (ι a) = ι a) (hιs : ∀ y : K, σ y = y → ∃ a, ι a = y) (hσ : orderOf σ = 3)
    (hD : RefData h ι l m D) {x : unitaryPSU h 3} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hαx : psuField h σ x = x)
    (hxK : x ∈ (perfectResidual (u38Fix (psuConj h D))).map (u38Fix (psuConj h D)).subtype) :
    x ∈ u38Two (psuField h σ) ∧ ∀ z ∈ u38Two (psuField h σ), (∃ j : ℕ, z ^ 3 ^ j = 1) →
      z ∈ Subgroup.closure {y | ∃ g ∈ u38Two (psuField h σ), y = g * x * g⁻¹} := by
  have hfin := h.finite
  have hq : 4 ≤ 2 ^ 3 := by norm_num
  have hlm' : ι l ≠ ι m := fun e => hD.hlm (ι.injective e)
  have ht : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ι l, ι l, ι m] := by
    rw [hD.hD]
    exact toMat_diag ι l l m
  have hfixeq : u38Fix (psuConj h D) =
      (suCentralizer (2 ^ 3) (D : GL (Fin 3) K)).map (unitaryProj h 3) := by
    ext z
    rw [mem_u38Fix]
    exact (mem_map_suCentralizer_iff h ht z).symm
  have hlevi : inSubgroup perfectResidual (u38Fix (psuConj h D)) =
      (leviSU3 (K := K) (2 ^ 3)).map (unitaryProj h 3) := by
    rw [hfixeq, ← map_inSubgroup_perfectResidual_hom,
      inSubgroup_perfectResidual_suCentralizer_eq h hq hlm' ht]
  obtain ⟨g, hgL, rfl⟩ : x ∈ (leviSU3 (K := K) (2 ^ 3)).map (unitaryProj h 3) := by
    rw [← hlevi]
    exact hxK
  have hg1 : g ≠ 1 := by
    intro e
    exact hx1 (by rw [e, map_one])
  have hg3 : g ^ 3 = 1 := by
    have hm : g ^ 3 ∈ leviSU3 (K := K) (2 ^ 3) := Subgroup.pow_mem _ hgL 3
    have hinj := unitaryProj_comp_leviSU3_injective h (K := K)
    have := @hinj ⟨g ^ 3, hm⟩ ⟨1, Subgroup.one_mem _⟩ (by
      show unitaryProj h 3 (g ^ 3) = unitaryProj h 3 1
      rw [map_pow, hx3, map_one])
    exact congrArg Subtype.val this
  have hgσ : suField h σ g = g := by
    have hπ : unitaryProj h 3 (suField h σ g) = unitaryProj h 3 g := by
      rw [unitaryProj_suField]
      exact hαx
    have hz : g⁻¹ * suField h σ g ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
    obtain ⟨c, -, -, hc⟩ := hz
    have hGL : (suField h σ g : GL (Fin 3) K) =
        (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
      have h1 := hc
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← h1, mul_inv_cancel_left]
    have h22 := mat_levi_22 hgL
    have hm22 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 2 2) hGL
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal] at hm22
    have hm22' : σ (mat g 2 2) = mat g 2 2 * (c : K) := hm22
    rw [h22, map_one, one_mul] at hm22'
    have hc1 : c = 1 := Units.ext (by rw [Units.val_one]; exact hm22'.symm)
    apply Subtype.ext
    rw [hGL, hc1, map_one, mul_one]
  have hgK : g ∈ (perfectResidual (u38Fix (suConj h D))).map (u38Fix (suConj h D)).subtype := by
    show g ∈ inSubgroup perfectResidual (u38Fix (suConj h D))
    rw [u38Fix_suConj_eq, inSubgroup_perfectResidual_suCentralizer_eq h hq hlm' ht]
    exact hgL
  obtain ⟨hgI, hgz⟩ := core_p3 h ι ι.injective hισ hιs hσ hD hg1 hg3 hgσ hgK
  refine ⟨map_u38Two_le h ⟨g, hgI, rfl⟩, fun z hz ⟨j, hj⟩ => ?_⟩
  obtain ⟨zs, hzs, rfl⟩ := u38Two_psuField_le h hz
  have hzs3 : zs ^ 3 ^ (j + 1) = 1 := by
    have h1 : unitaryProj h 3 (zs ^ 3 ^ j) = 1 := by rw [map_pow]; exact hj
    have h2 : zs ^ 3 ^ j ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj]
      exact h1
    have h3 := pow_three_eq_one_of_mem_unitaryScalars h h2
    rwa [← pow_mul, ← pow_succ] at h3
  have h4 := hgz zs hzs ⟨j + 1, hzs3⟩
  have hmap : (Subgroup.closure {y | ∃ g' ∈ u38Two (suField h σ), y = g' * g * g'⁻¹}).map
      (unitaryProj h 3) ≤ Subgroup.closure {y | ∃ g' ∈ u38Two (psuField h σ),
        y = g' * unitaryProj h 3 g * g'⁻¹} := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨g', hg', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.subset_closure ⟨unitaryProj h 3 g', map_u38Two_le h ⟨g', hg', rfl⟩, rfl⟩
  exact hmap ⟨zs, h4, rfl⟩

include h in
theorem psu_p3 {α β : MulAut (unitaryPSU h 3)} (hyps : U38Hyps (unitaryPSU h 3) α β)
    {x : unitaryPSU h 3} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hαx : α x = x)
    (hxK : x ∈ (perfectResidual (u38Fix β)).map (u38Fix β).subtype) :
    x ∈ u38Two α ∧ ∀ z ∈ u38Two α, (∃ j : ℕ, z ^ 3 ^ j = 1) →
      z ∈ Subgroup.closure {y | ∃ g ∈ u38Two α, y = g * x * g⁻¹} := by
  have hfin := h.finite
  obtain ⟨hα3, hβ3, hαβ, hαout, hu4, hβ1, h7⟩ := hyps
  obtain ⟨G, D, σ, ι, l, m, hσ, hισ, hιs, hD, hα, hβ⟩ := nf_psu h hα3 hβ3 hαβ hαout
    (by obtain ⟨u, hu, h4, h2⟩ := hu4; exact ⟨u, mem_u38Fix.mp hu, h4, h2⟩) hβ1 h7
  set ψ : MulAut (unitaryPSU h 3) := psuConj h G with hψ
  have e1 : MulAut.congr (ψ⁻¹ : MulAut (unitaryPSU h 3)) α = psuField h σ := by
    rw [congr_eq_mul, hα]
    group
  have e2 : MulAut.congr (ψ⁻¹ : MulAut (unitaryPSU h 3)) β = psuConj h D := by
    rw [congr_eq_mul, hβ]
    group
  have hαx' : psuField h σ ((ψ⁻¹ : MulAut (unitaryPSU h 3)) x) =
      (ψ⁻¹ : MulAut (unitaryPSU h 3)) x := by
    have h1 := congr_apply_e (ψ⁻¹ : MulAut (unitaryPSU h 3)) α x
    rw [e1, hαx] at h1
    exact h1
  have hxK' := (mem_perfectResidual_congr (ψ⁻¹ : MulAut (unitaryPSU h 3)) β x).mpr hxK
  rw [e2] at hxK'
  have hx1' : (ψ⁻¹ : MulAut (unitaryPSU h 3)) x ≠ 1 := by
    intro h1
    exact hx1 ((ψ⁻¹ : MulAut (unitaryPSU h 3)).injective (h1.trans (map_one _).symm))
  have hx3' : ((ψ⁻¹ : MulAut (unitaryPSU h 3)) x) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  apply p3_conclusion_congr (ψ⁻¹ : MulAut (unitaryPSU h 3))
  rw [e1]
  exact psu_p3_model h hισ hιs hσ hD hx1' hx3' hαx' hxK'

end PSU

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
