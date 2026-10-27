module

public import CFSG.RankThree.PartOne.CTP.SeitzFine
public import CFSG.RankThree.PartOne.SEITZ2.SUnPair

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical

theorem two_le_div_five_of_dvd {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) (hf : 5 ∣ f) : 2 ≤ f / 5 := by
  obtain ⟨f0, rfl⟩ := hf
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  by_contra hlt
  have : f0 = 0 ∨ f0 = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h5

theorem exists_ker_ne_one_of_cyclic {G Γ : Type*} [Group G] [Group Γ] [IsCyclic Γ]
    (Φ : G →* Γ) (A : Subgroup G) (hA5 : ∀ a ∈ A, a ^ 5 = 1) (hAcard : Nat.card A = 25) :
    ∃ α0 ∈ A, Φ α0 = 1 ∧ α0 ≠ 1 := by
  classical
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let φ : A →* Γ := Φ.comp A.subtype
  have : IsCyclic φ.range := Subgroup.isCyclic _
  have hexp : Monoid.exponent φ.range ∣ 5 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    change (φ a) ^ 5 = 1
    rw [← map_pow]
    have : a ^ 5 = 1 := Subtype.ext (hA5 a a.2)
    rw [this, map_one]
  have hcard : Nat.card φ.range ∣ 5 := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  have hmul : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hle : Nat.card φ.range ≤ 5 := Nat.le_of_dvd (by norm_num) hcard
  have hker : φ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, mul_one] at hmul
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker
  refine ⟨(x : A), (x : A).2, x.2, ?_⟩
  intro h1
  apply hx1
  apply Subtype.ext
  apply Subtype.ext
  exact h1

section Plane

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_outer_inner (A : Subgroup (MulAut (primeFormP h (idGram K 5))))
    [IsElementaryAbelian 5 A] (hAcard : Nat.card A = 5 ^ 2)
    (hAD : ¬ A ≤ primeFormD h (idGram K 5)) :
    ∃ β ∈ A, β ∉ primeFormD h (idGram K 5) ∧
      ∃ α0 ∈ A, α0 ∈ primeFormD h (idGram K 5) ∧ α0 ≠ 1 := by
  have hf1 : 1 ≤ f := h.one_le
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hn3 : 3 ≤ 5 := by norm_num
  have hne : ¬(5 = 3 ∧ 2 ^ f = 2) := by omega
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card Nat.prime_two (by omega) h.card
  obtain ⟨β, hβA, hβ⟩ := Set.not_subset.1 hAD
  obtain ⟨α0, hα0A, hΦ, hα01⟩ := exists_ker_ne_one_of_cyclic
    (primeFormFieldFactor h hC hn3 hne) A
    (fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha) (by simpa using hAcard)
  refine ⟨β, hβA, hβ, α0, hα0A, ?_, hα01⟩
  rw [← ker_primeFormFieldFactor h hC hn3 hne]
  exact hΦ

theorem closure_fixSet_of_outer_plane (h5 : 5 ∣ 2 ^ f + 1)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAel : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 2) (hAD : ¬ A ≤ primeFormD h (idGram K 5)) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hn3 : 3 ≤ 5 := by norm_num
  have hne : ¬(5 = 3 ∧ 2 ^ f = 2) := by omega
  have := hAel
  obtain ⟨β, hβA, hβD, α0, hα0A, hα0D, hα01⟩ := exists_outer_inner h A hAcard hAD
  have hβ1 : β ≠ 1 := fun h1 => hβD (h1 ▸ one_mem _)
  have hβ5 : orderOf β = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian β hβA) hβ1
  set Φ := primeFormFieldFactor h hC hn3 hne with hΦ
  set σ := Φ β with hσdef
  have hker := ker_primeFormFieldFactor h hC hn3 hne
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hβD
    rw [← hker]
    exact h1
  have hσ5' : σ ^ 5 = 1 := by
    rw [hσdef, ← map_pow, elemPow_eq_one_of_isElementaryAbelian β hβA, map_one]
  have hσ5 : orderOf σ = 5 := orderOf_eq_prime hσ5' hσ1
  obtain ⟨hpf, -, -, -, -, M0, hM0⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne
      Nat.prime_five (by norm_num) (by norm_num) β hβ5 σ rfl hσ5
  have hγA : β * α0 ∈ A := A.mul_mem hβA hα0A
  have hγD : β * α0 ∉ primeFormD h (idGram K 5) := by
    intro hmem
    apply hβD
    have := (primeFormD h (idGram K 5)).mul_mem hmem ((primeFormD h (idGram K 5)).inv_mem hα0D)
    simpa using this
  have hγ1 : β * α0 ≠ 1 := fun h1 => hγD (h1 ▸ one_mem _)
  have hγ5 : orderOf (β * α0) = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ hγA) hγ1
  have hΦγ : Φ (β * α0) = σ := by
    rw [map_mul, hσdef]
    have : Φ α0 = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hα0D
    rw [this, mul_one]
  obtain ⟨-, -, -, -, -, M1, hM1⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne
      Nat.prime_five (by norm_num) (by norm_num) (β * α0) hγ5 σ hΦγ hσ5
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_five (by norm_num) hσ5 with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_five (by norm_num) hσ5
  set R := (subfieldPSU h h₀ hbar 5).range with hR
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hfixσ : ∀ x ∈ R, fσ x = x := fun x hx =>
    primeFormFieldHom_apply_of_mem_range h 5 h₀ hbar
      (fun c hc => (CFSG.LieType.Chevalley.mem_fixSubfield σ).1 hc) hx
  set cM0 := primeFormConjHom h (idGram K 5) M0 with hcM0
  set cM1 := primeFormConjHom h (idGram K 5) M1 with hcM1
  have hβeq : β = cM0 * fσ * cM0⁻¹ := by rw [← hM0]; group
  have hγeq : β * α0 = cM1 * fσ * cM1⁻¹ := by rw [← hM1]; group
  have hfixβ : ∀ x ∈ R, β (cM0 x) = cM0 x := by
    intro x hx
    rw [hβeq]
    simp [hfixσ x hx]
  have hfixγ : ∀ x ∈ R, (β * α0) (cM1 x) = cM1 x := by
    intro x hx
    rw [hγeq]
    simp [hfixσ x hx]
  have hΦf : Φ fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn3 hne 1 σ
    simpa using this
  have hne01 : R.map cM0.toMonoidHom ≠ R.map cM1.toMonoidHom := by
    intro heq
    have hα0fix : ∀ x ∈ R, α0 (cM0 x) = cM0 x := by
      intro x hx
      have hx1 : cM0 x ∈ R.map cM1.toMonoidHom := heq ▸ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx1
      have h1 : (β * α0) (cM0 x) = cM0 x := by
        have := hfixγ y hy
        have hyx' : cM1 y = cM0 x := hyx
        rwa [hyx'] at this
      have h2 : β (cM0 x) = cM0 x := hfixβ x hx
      have h3 : β (α0 (cM0 x)) = β (cM0 x) := by rw [h2]; exact h1
      exact β.injective h3
    have hα0' : (cM0⁻¹ * α0 * cM0) ∈
        fixingSubgroup (MulAut (primeFormP h (idGram K 5)))
          (R : Set (primeFormP h (idGram K 5))) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      simp [hα0fix y hy]
    obtain ⟨hfs1, hfs2, -⟩ := fixingSubgroup_range_subfieldPSU h 5 h₀ hbar hn3 hne
      (by omega)
    rw [hfs1, hfs2] at hα0'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hα0'
    have hΦα0 : Φ α0 = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hα0D
    have hΦj : σ ^ j = 1 := by
      have e1 : Φ (fσ ^ j) = σ ^ j := by rw [map_zpow, hΦf]
      rw [← e1, hj]
      simp [map_mul, map_inv, hΦα0]
    have h5j : (5 : ℤ) ∣ j := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hΦj
      rw [hσ5] at this
      exact_mod_cast this
    have hf1 : fσ ^ j = 1 := by
      refine orderOf_dvd_iff_zpow_eq_one.1 ?_
      have hof : orderOf fσ ∣ orderOf σ := orderOf_map_dvd (primeFormFieldHom h hC) σ
      rw [hσ5] at hof
      exact (Int.natCast_dvd_natCast.2 hof).trans h5j
    rw [hf1] at hj
    apply hα01
    have : α0 = cM0 * (cM0⁻¹ * α0 * cM0) * cM0⁻¹ := by group
    rw [this, ← hj]
    group
  have hp5f : 5 ∣ f := hpf
  have hge : 2 ≤ f / 5 := two_le_div_five_of_dvd h5 hp5f
  set Nh := primeFormConjHom h (idGram K 5) (M0⁻¹ * M1) with hNh
  have hNeq : Nh = cM0⁻¹ * cM1 := by rw [hNh, hcM0, hcM1]; simp [map_mul, map_inv]
  have e1 : R.map cM1.toMonoidHom = (R.map Nh.toMonoidHom).map cM0.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [hNeq]
  have hne2 : R ≠ R.map Nh.toMonoidHom := by
    intro heq
    apply hne01
    rw [e1, ← heq]
  have hne3 : (suSub h h₀ hbar 5).map (primeFormConjSU h _ (M0⁻¹ * M1)).toMonoidHom ≠
      suSub h h₀ hbar 5 := by
    intro hh
    apply hne2
    rw [hR, range_subfieldPSU_eq_map]
    rw [map_primeFormConjHom_map_mk h h₀ hbar 5 (M0⁻¹ * M1), hh]
  have hgen := CFSG.RankThree.PartOne.SEITZ2.subfieldPairSUBig (n := 5) hn3 f (f / 5) K h
    (CFSG.LieType.Chevalley.fixSubfield σ) h₀ hbar 5 Nat.prime_five le_rfl
    (Nat.mul_div_cancel' hp5f).symm hge
    (M0⁻¹ * M1) hne3
  have h4 := congrArg (Subgroup.map (QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) 5))) hgen
  rw [map_closure_union, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    at h4
  rw [← map_primeFormConjHom_map_mk h h₀ hbar 5 (M0⁻¹ * M1), ← range_subfieldPSU_eq_map] at h4
  have hcl : Subgroup.closure ((R.map cM0.toMonoidHom : Set (primeFormP h (idGram K 5))) ∪
      (R.map cM1.toMonoidHom : Set (primeFormP h (idGram K 5)))) = ⊤ := by
    have h6 := congrArg (Subgroup.map cM0.toMonoidHom) h4
    rw [map_closure_union, Subgroup.map_top_of_surjective cM0.toMonoidHom cM0.surjective,
      ← e1] at h6
    exact h6
  have hstab : ∀ (γ : MulAut (primeFormP h (idGram K 5))) (x : primeFormP h (idGram K 5)),
      γ x = x → ∀ φ ∈ Subgroup.zpowers γ, φ x = x := by
    intro γ x hγ φ hφ
    have hmem : γ ∈ MulAction.stabilizer (MulAut (primeFormP h (idGram K 5))) x := by
      rw [MulAction.mem_stabilizer_iff]
      exact hγ
    have := Subgroup.zpowers_le.2 hmem hφ
    rwa [MulAction.mem_stabilizer_iff] at this
  refine eq_top_iff.2 ?_
  rw [← hcl]
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  refine Subgroup.subset_closure ?_
  rcases hx with hx | hx
  · obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.zpowers β, Subgroup.zpowers_le.2 hβA, ?_, hstab β _ (hfixβ y hy)⟩
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hβ1
  · obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.zpowers (β * α0), Subgroup.zpowers_le.2 hγA, ?_,
      hstab _ _ (hfixγ y hy)⟩
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hγ1

end Plane


theorem psu5FieldPlane_holds : PSU5FieldPlane := by
  intro f K _ h h5 A hAel hAcard hAD
  exact closure_fixSet_of_outer_plane h h5 A hAel hAcard hAD

theorem seitzUnitaryFiveFine_of_diag49 (h : PSU5DiagPlane49) :
    SeitzUnitaryFiveFine :=
  ⟨h, psu5FieldPlane_holds⟩

end CFSG.RankThree.PartOne.SEITZ10
