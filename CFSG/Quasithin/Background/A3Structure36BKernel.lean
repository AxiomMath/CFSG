
module

public import CFSG.Quasithin.Background.A3Structure36BSL2
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Quasithin.Background.A3Structure36BAux
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrimeBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement

variable {X : Type} [Group X]

theorem five_le_of_isSL2 (h : A36BHyp X) {K : Subgroup X} [K.Normal] (hKtop : K ≠ ⊤) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hs : IsSL2 p (X ⧸ K)) : 5 ≤ p := by
  have hfin : Finite X := h.finite
  have hperf : Group.IsPerfect X := isPerfect_of_hyp h
  by_contra hlt
  have hp3 : p = 3 := by
    have := hp.two_le
    interval_cases p <;> first | rfl | omega | exact absurd hp (by norm_num)
  subst hp3
  obtain ⟨e⟩ := hs
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) < 60 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula (ZMod 3), Nat.card_zmod]
    norm_num
  have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable hcard
  have hsolv' : Group.IsSolvable (X ⧸ K) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnt : Nontrivial (X ⧸ K) :=
    Finite.one_lt_card_iff_nontrivial.1 (Subgroup.one_lt_index_of_ne_top hKtop)
  exact Group.IsPerfect.not_isSolvable (X ⧸ K) hsolv'

theorem PrimeData.exists_sl2 (h : A36BHyp X) {q : ℕ} (hq : q.Prime) (hπ : IsPi X q)
    (D : PrimeData X q) : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ IsSL2 r (X ⧸ D.K) := by
  have hq2 : q ≠ 2 := IsPi.ne_two h hπ
  rcases D.sl2 with hs | ⟨-, hs⟩
  · exact ⟨q, hq, five_le_of_isSL2 h D.ne_top hq hq2 hs, hs⟩
  · exact ⟨5, by norm_num, le_rfl, hs⟩

theorem exists_hom_of_isSL2 {K : Subgroup X} [K.Normal] {r : ℕ} (hK : IsSL2 r (X ⧸ K)) :
    ∃ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r), Function.Surjective φ ∧ φ.ker = K := by
  obtain ⟨e⟩ := hK
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K),
    e.surjective.comp (QuotientGroup.mk'_surjective K), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

theorem center_sl2_ne_top {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) ≠ ⊤ := by
  intro htop
  have hQ := isQuasisimple_sl2 hr h5
  have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) (ZMod r) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have := hQ.2.1.toNontrivial
  exact (not_nontrivial_iff_subsingleton.2 hsub) this

theorem radical_eq_comap_center (h : A36BHyp X) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) (hφ : Function.Surjective φ) :
    CFSG.solvableRadical X =
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))).comap φ := by
  have hfin : Finite X := h.finite
  have hQ := isQuasisimple_sl2 hr h5
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hperfSL := isPerfect_sl2 hr h5
  apply le_antisymm
  · intro t ht
    have hN : ((CFSG.solvableRadical X).map φ).Normal :=
      Subgroup.Normal.map inferInstance φ hφ
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with htop | hle
    · exfalso
      have hsolvO : Group.IsSolvable (CFSG.solvableRadical X) := A3.solvableRadical_isSolvable
      have hsolv : Group.IsSolvable ((CFSG.solvableRadical X).map φ) :=
        Group.isSolvable_of_surjective (φ.subgroupMap_surjective (CFSG.solvableRadical X))
      rw [htop] at hsolv
      have hsolv' : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
        Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
          ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))) ≃* _).toMonoidHom)
          Subgroup.topEquiv.surjective
      exact Group.IsPerfect.not_isSolvable _ hsolv'
    · exact hle (Subgroup.mem_map_of_mem φ ht)
  · apply normal_le_radical h
    intro htop
    apply center_sl2_ne_top hr h5
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hφ y
    have hx : x ∈ (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))).comap φ :=
      htop ▸ Subgroup.mem_top x
    exact hx

structure IsKernelData (X : Type) [Group X] (K : Subgroup X) : Prop where
  normal : K.Normal
  le_radical : K ≤ CFSG.solvableRadical X
  comm : ∀ t ∈ CFSG.solvableRadical X, ∀ g : X, ⁅t, g⁆ ∈ K
  sq : ∀ t ∈ CFSG.solvableRadical X, t ^ 2 ∈ K
  relIndex : K.relIndex (CFSG.solvableRadical X) = 2

theorem isKernelData_of_sl2 (h : A36BHyp X) {K : Subgroup X} [hKn : K.Normal] {r : ℕ}
    (hr : r.Prime) (h5 : 5 ≤ r) (hK : IsSL2 r (X ⧸ K)) :
    IsKernelData X K ∧ IsPSL 2 r 1 (X ⧸ CFSG.solvableRadical X) := by
  have hr2 : r ≠ 2 := by omega
  obtain ⟨e⟩ := hK
  let φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) :=
    e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : φ.ker = K := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  have hrad := radical_eq_comap_center h hr h5 φ hφ
  refine ⟨⟨hKn, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    rw [hrad]
    show φ x ∈ Subgroup.center _
    rw [(MonoidHom.mem_ker.1 (hker ▸ hx))]
    exact Subgroup.one_mem _
  · intro t ht g
    rw [hrad] at ht
    have hzt : φ t ∈ Subgroup.center _ := ht
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hzt (φ g)).symm
  · intro t ht
    rw [hrad] at ht
    have hzt : φ t ∈ Subgroup.center _ := ht
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact sq_eq_one_of_mem_center_sl2 hr hr2 hzt
  · rw [← hker, Subgroup.relIndex_ker, hrad, Subgroup.map_comap_eq_self_of_surjective hφ]
    exact card_center_sl2 hr hr2
  · let f : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r) :=
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)))).comp φ
    have hfsurj : Function.Surjective f :=
      (QuotientGroup.mk'_surjective _).comp hφ
    have hfker : f.ker = CFSG.solvableRadical X := by
      rw [hrad, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact isPSL_two_of_mulEquiv hr h5
      ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfsurj))

theorem relIndex_le_two (hL2 : L2MultiplierFact) (h : A36BHyp X) {r : ℕ} (hr : r.Prime)
    (h5 : 5 ≤ r) (hPSL : IsPSL 2 r 1 (X ⧸ CFSG.solvableRadical X)) {D : Subgroup X}
    [hDn : D.Normal] (hDO : D ≤ CFSG.solvableRadical X)
    (hcomm : ∀ t ∈ CFSG.solvableRadical X, ∀ g : X, ⁅t, g⁆ ∈ D) :
    D.relIndex (CFSG.solvableRadical X) ≤ 2 := by
  have hfin : Finite X := h.finite
  have hperf : Group.IsPerfect X := isPerfect_of_hyp h
  have hZn : ((CFSG.solvableRadical X).map (QuotientGroup.mk' D)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective D)
  have hZc : (CFSG.solvableRadical X).map (QuotientGroup.mk' D) ≤ Subgroup.center (X ⧸ D) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : QuotientGroup.mk' D ⁅t, g⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcomm t ht g)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hPSL' : IsPSL 2 r 1 ((X ⧸ D) ⧸ (CFSG.solvableRadical X).map (QuotientGroup.mk' D)) :=
    isPSL_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient D _ hDO) hPSL
  have hcard := hL2 r hr h5 (X ⧸ D) inferInstance _ hZc hPSL'
  rw [relIndex_eq_card_map]
  exact hcard

theorem kernel_eq (hL2 : L2MultiplierFact) (h : A36BHyp X) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hPSL : IsPSL 2 r 1 (X ⧸ CFSG.solvableRadical X)) {K₁ K₂ : Subgroup X}
    (h₁ : IsKernelData X K₁) (h₂ : IsKernelData X K₂) : K₁ = K₂ := by
  have hfin : Finite X := h.finite
  have key : ∀ {A B : Subgroup X}, IsKernelData X A → IsKernelData X B → A ≤ B := by
    intro A B hA hB
    have hAn := hA.normal
    have hBn := hB.normal
    have hABn : (A ⊓ B).Normal := inferInstance
    have hD := relIndex_le_two hL2 h hr h5 hPSL (D := A ⊓ B)
      (inf_le_left.trans hA.le_radical) (fun t ht g => ⟨hA.comm t ht g, hB.comm t ht g⟩)
    have h1 := Subgroup.relIndex_mul_relIndex (A ⊓ B) A (CFSG.solvableRadical X) inf_le_left
      hA.le_radical
    rw [hA.relIndex] at h1
    have hne : (A ⊓ B).relIndex A ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_dvd_card (A ⊓ B) A
      rw [h0, zero_dvd_iff] at this
      exact (Nat.card_pos (α := A)).ne' this
    have h2 : (A ⊓ B).relIndex A = 1 := by omega
    exact (Subgroup.relIndex_eq_one.1 h2).trans inf_le_right
  exact le_antisymm (key h₁ h₂) (key h₂ h₁)

theorem eq_of_commutator_le (hL2 : L2MultiplierFact) (h : A36BHyp X) {r : ℕ} (hr : r.Prime)
    (h5 : 5 ≤ r) (hPSL : IsPSL 2 r 1 (X ⧸ CFSG.solvableRadical X)) {K N : Subgroup X}
    [hNn : N.Normal] (hK : IsKernelData X K) (hNK : N ≤ K)
    (hKN : ∀ k ∈ K, ∀ g : X, ⁅k, g⁆ ∈ N) (hodd : Odd (Nat.card K)) : N = K := by
  have hfin : Finite X := h.finite
  have hOcomm : ∀ t ∈ CFSG.solvableRadical X, ∀ g : X, ⁅t, g⁆ ∈ N := fun t ht g =>
    commutator_mem_of_odd_central N K (CFSG.solvableRadical X) hKN hK.comm hK.sq hodd ht g
  have hD := relIndex_le_two hL2 h hr h5 hPSL (D := N) (hNK.trans hK.le_radical) hOcomm
  have h1 := Subgroup.relIndex_mul_relIndex N K (CFSG.solvableRadical X) hNK hK.le_radical
  rw [hK.relIndex] at h1
  have hodd' : Odd (N.relIndex K) := by
    have hdvd : N.relIndex K ∣ Nat.card K := Subgroup.relIndex_dvd_card N K
    exact Odd.of_dvd_nat hodd hdvd
  have h2 : N.relIndex K = 1 := by
    have h3 := hodd'.pos
    omega
  exact le_antisymm hNK (Subgroup.relIndex_eq_one.1 h2)

end CFSG.Quasithin.A36B
