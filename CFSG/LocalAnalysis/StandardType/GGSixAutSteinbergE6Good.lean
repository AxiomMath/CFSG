module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Root
public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public section

namespace CFSG.StandardType

namespace AutSt

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

open scoped commutatorElement

section Abstract

variable {S : Type*} [Group S]

theorem eq_one_or_eq_of_mem_zpowers {η x : MulAut S} (hord : orderOf η = 2)
    (hx : x ∈ Subgroup.zpowers η) : x = 1 ∨ x = η := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hord]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_bot_of_derived_fixed (hZ : Subgroup.center S = ⊥) {η : MulAut S}
    (hord : orderOf η = 2) (hηI : ∀ g : S, MulAut.conj g ≠ η) {J : Subgroup S}
    (hJ : ⁅fixSub η, fixSub η⁆ = J) (hJs : IsSimpleGroup J)
    (hcent : Subgroup.centralizer {η} ⊓ Subgroup.centralizer
      ((J.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) =
        Subgroup.zpowers η)
    {a : S} (haJ : a ∈ J) (ha1 : a ≠ 1) (hao : Odd (orderOf a)) (Q : Subgroup S)
    (hfix : ∀ q ∈ Q, η q = q) (hQ : IsPGroup 2 Q)
    (hnorm : ∀ y : S, η y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) : Q = ⊥ := by
  have hJF : J ≤ fixSub η := hJ ▸ Subgroup.commutator_le_self _
  have hQJ : ∀ x ∈ Q, x ∈ J → x = 1 := by
    have hN : ((Q ⊓ J).subgroupOf J).Normal := by
      refine ⟨fun x hx y => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hnorm y (hJF y.2) x hx.1, J.mul_mem (J.mul_mem y.2 hx.2) (J.inv_mem y.2)⟩
    rcases hN.eq_bot_or_eq_top with h | h
    · intro x hxQ hxJ
      have hx : (⟨x, hxJ⟩ : J) ∈ (Q ⊓ J).subgroupOf J := ⟨hxQ, hxJ⟩
      rw [h, Subgroup.mem_bot] at hx
      exact congrArg Subtype.val hx
    · exfalso
      have ha : (⟨a, haJ⟩ : J) ∈ (Q ⊓ J).subgroupOf J := by
        rw [h]
        exact Subgroup.mem_top _
      exact ha1 (eq_one_of_odd_of_mem hQ (Subgroup.mem_subgroupOf.1 ha).1 hao)
  have hcomm : ∀ q ∈ Q, ∀ j ∈ J, j * q = q * j := by
    intro q hq j hj
    have h1 : ⁅q, j⁆ ∈ Q := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine Q.mul_mem hq ?_
      rw [← mul_assoc]
      exact hnorm j (hJF hj) q⁻¹ (Q.inv_mem hq)
    have h2 : ⁅q, j⁆ ∈ J := hJ ▸ Subgroup.commutator_mem_commutator (hfix q hq) (hJF hj)
    exact (commutatorElement_eq_one_iff_mul_comm.1 (hQJ _ h1 h2)).symm
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  have hmem : MulAut.conj q ∈ Subgroup.centralizer {η} ⊓ Subgroup.centralizer
      ((J.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, Subgroup.mem_centralizer_iff.2 ?_⟩
    · have h := mulAut_mul_conj_mul_inv η q
      rw [hfix q hq] at h
      calc MulAut.conj q * η = η * MulAut.conj q * η⁻¹ * η := by rw [h]
        _ = η * MulAut.conj q := by group
    · rintro _ ⟨j, hj, rfl⟩
      rw [← map_mul, ← map_mul, hcomm q hq j hj]
  rw [hcent] at hmem
  rcases eq_one_or_eq_of_mem_zpowers hord hmem with h | h
  · have hc : q ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut S => φ x) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * q = q * x * q⁻¹ * q := by rw [hx]
        _ = q * x := by group
    rw [hZ] at hc
    exact hc
  · exact absurd h (hηI q)

theorem goodAut_of_derived_fixed (hZ : Subgroup.center S = ⊥) {η : MulAut S}
    (hord : orderOf η = 2) (hηI : ∀ g : S, MulAut.conj g ≠ η) {J : Subgroup S}
    (hJ : ⁅fixSub η, fixSub η⁆ = J) (hJs : IsSimpleGroup J)
    (hcent : Subgroup.centralizer {η} ⊓ Subgroup.centralizer
      ((J.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) =
        Subgroup.zpowers η)
    {r : S} (g : S) (hg : η (g * r * g⁻¹) = g * r * g⁻¹) {a : S} (haJ : a ∈ J)
    (har : a * (g * r * g⁻¹) = g * r * g⁻¹ * a) (ha1 : a ≠ 1) (hao : Odd (orderOf a)) :
    GGGoodAut r η := by
  have hJF : J ≤ fixSub η := hJ ▸ Subgroup.commutator_le_self _
  exact ⟨fun Q hfix hQ hnorm => eq_bot_of_derived_fixed hZ hord hηI hJ hJs hcent haJ ha1 hao Q
    hfix hQ hnorm, g, hg, a, hJF haJ, har, ha1, hao⟩

theorem isSimpleGroup_subgroupOf {G : Type*} [Group G] {J C : Subgroup G} (hJC : J ≤ C)
    (hJs : IsSimpleGroup J) : IsSimpleGroup (J.subgroupOf C) := by
  let e := Subgroup.subgroupOfEquivOfLe hJC
  have : Nontrivial (J.subgroupOf C) := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

end Abstract

section Normal


variable {K : Type} [Field K]

theorem exactNormalAut_one_one_zero {τ : Tag} : exactNormalAut τ K 1 1 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_exactNormalAut, rootDiagUnit_one, exactQ_zero]
    simp only [one_mul, mul_one, inv_one, MulAut.one_apply]
    exact Units.ext (entrywise_id _))

theorem exactNormalAut_one_zero_eq (σ : K ≃+* K) :
    exactNormalAut TwistTag.E6.tag K 1 σ 0 =
      diagramConjAut TwistTag.E6 K ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ := by
  rw [pow_zero, one_mul]
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_exactNormalAut, coe_entrywiseAdjointAut, rootDiagUnit_one, exactQ_zero]
  simp only [one_mul, mul_one, inv_one]

theorem exactNormalAut_one_one_eq (σ : K ≃+* K) :
    exactNormalAut TwistTag.E6.tag K 1 σ 1 =
      diagramConjAut TwistTag.E6 K ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ := by
  rw [pow_one]
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_exactNormalAut, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut,
    rootDiagUnit_one]
  simp only [one_mul, mul_one, inv_one]
  rw [show exactQ TwistTag.E6.tag K 1 = diagramMap TwistTag.E6 K from pow_one _]

theorem exactNormalAut_one_ne_conj [Finite K] {σ : K ≃+* K} {ε : ℕ} (hε : ε < 2)
    (h : σ ≠ 1 ∨ ε ≠ 0) (g : adjointGroup .E6 K) :
    MulAut.conj g ≠ exactNormalAut .E6 K 1 σ ε := by
  intro hg
  have e : MulAut.conj g * exactNormalAut .E6 K 1 1
        ((⟨0, by decide⟩ : Fin (exactE .E6)) : ℕ) =
      MulAut.conj 1 * exactNormalAut .E6 K 1 σ ((⟨ε, hε⟩ : Fin (exactE .E6)) : ℕ) := by
    rw [exactNormalAut_one_one_zero, mul_one, map_one, one_mul]
    exact hg
  obtain ⟨h1, h2⟩ := params_eq_of_conj_mul_exactNormalAut_eq (Or.inl rfl) e
  rcases h with h | h
  · exact h h1.symm
  · exact h (congrArg Fin.val h2).symm

end Normal

section Involutions


variable {K : Type} [Field K]

theorem goodAut_e6One_of_derived [Finite K] [CharP K 2] {σ : K ≃+* K} {ε : ℕ}
    {J : Subgroup (ModGL .E6 K)}
    (hD : DerivedFixedSubgroupData (adjointGroup .E6 K) J (exactNormalAut .E6 K 1 σ ε))
    (hcent : Subgroup.centralizer {exactNormalAut .E6 K 1 σ ε} ⊓ Subgroup.centralizer
      (((J.subgroupOf (adjointGroup .E6 K)).map MulAut.conj :
        Subgroup (MulAut (adjointGroup .E6 K))) : Set (MulAut (adjointGroup .E6 K))) =
          Subgroup.zpowers (exactNormalAut .E6 K 1 σ ε))
    (hηI : ∀ g, MulAut.conj g ≠ exactNormalAut .E6 K 1 σ ε) :
    GGGoodAut (xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K))
      (exactNormalAut .E6 K 1 σ ε) := by
  obtain ⟨hord, hJC, hJ, -, hJs, -, -, -, -⟩ := hD
  have ha3 := orderOf_e6A (F := rootOperatorFamily .E6) (K := K)
  have haJ : ⁅xPar (rootOperatorFamily .E6) (Pi.single (e6Node 0) 1) (1 : K) *
        xPar (rootOperatorFamily .E6) (Pi.single (e6Node 5) 1) (1 : K),
      xPar (rootOperatorFamily .E6) (-Pi.single (e6Node 0) 1) (1 : K) *
        xPar (rootOperatorFamily .E6) (-Pi.single (e6Node 5) 1) (1 : K)⁆ ∈
      J.subgroupOf (adjointGroup .E6 K) := by
    rw [← hJ]
    exact Subgroup.commutator_mem_commutator (exactNormalAut_one_e6U σ ε)
      (exactNormalAut_one_e6V σ ε)
  refine goodAut_of_derived_fixed center_adjointGroup_eq_bot hord hηI hJ
    (isSimpleGroup_subgroupOf hJC hJs) hcent 1 ?_ haJ ?_ ?_ ?_
  · rw [one_mul, inv_one, mul_one]
    exact exactNormalAut_one_e6One σ ε
  · rw [one_mul, inv_one, mul_one]
    exact commute_e6A.eq
  · intro h
    rw [h, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  · rw [ha3]
    decide

theorem isSimpleGroup_fixSub_e6Graph [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h2 : (2 : K) = 0) : IsSimpleGroup (fixSub (exactNormalAut TwistTag.E6.tag K 1 1 1)) := by
  obtain ⟨η, hη, -, hJC, hfixJ, hJs, -, -, -, -⟩ :=
    canonicalGraphFixedSubgroup_adjointGroup K hf hK h2
  have hηN : η = exactNormalAut TwistTag.E6.tag K 1 1 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [hη, coe_exactNormalAut, rootDiagUnit_one,
      show exactQ TwistTag.E6.tag K 1 = diagramMap TwistTag.E6 K from pow_one _]
    simp only [one_mul, mul_one, inv_one]
    rw [show Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (g : ModGL TwistTag.E6.tag K) = g
      from Units.ext (entrywise_id _)]
  have hfix : fixSub (exactNormalAut TwistTag.E6.tag K 1 1 1) =
      ((twistedFixedGroup TwistTag.E6 K (RingHom.id K)).map
        (baseChangeGL (RingHom.id K))).subgroupOf (adjointGroup TwistTag.E6.tag K) := by
    ext g
    rw [mem_fixSub, Subgroup.mem_subgroupOf, ← hfixJ g, hηN]
  rw [hfix]
  exact isSimpleGroup_subgroupOf hJC hJs

theorem goodAut_e6One_graph [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    GGGoodAut (xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K))
      (exactNormalAut .E6 K 1 1 1) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have ha3 := orderOf_e6A (F := rootOperatorFamily .E6) (K := K)
  refine goodAut_of_fixed_simple (isSimpleGroup_fixSub_e6Graph hf hK h2) 1 ?_ _
    (exactNormalAut_one_e6A (F := rootOperatorFamily .E6) 1 1) ?_ ?_ ?_
  · rw [one_mul, inv_one, mul_one]
    exact exactNormalAut_one_e6One 1 1
  · rw [one_mul, inv_one, mul_one]
    exact commute_e6A.eq
  · intro h
    rw [h, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  · rw [ha3]
    decide

theorem goodAut_e6One [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} {ε : ℕ} (hε : ε < 2) (hσ2 : σ ^ 2 = 1) (hne : ¬(σ = 1 ∧ ε = 0)) :
    GGGoodAut (xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K))
      (exactNormalAut .E6 K 1 σ ε) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  by_cases hσ : σ = 1
  · subst hσ
    obtain rfl : ε = 1 := by
      have : ε ≠ 0 := fun h => hne ⟨rfl, h⟩
      omega
    exact goodAut_e6One_graph hf hK
  · obtain ⟨-, -, -, -, -, hfield⟩ :=
      ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
    obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
    obtain ⟨hD0, hD1⟩ :=
      even_E6_canonical_field_graph_field_derived_fixed_subgroups he1 K hK' σ hσ'
    obtain ⟨hc0, hc1⟩ :=
      even_E6_canonical_field_graph_field_pointwise_centralizers he1 K hK' σ hσ'
    have hηI := exactNormalAut_one_ne_conj (K := K) hε (Or.inl hσ)
    interval_cases ε
    · rw [← exactNormalAut_one_zero_eq] at hD0 hc0
      exact goodAut_e6One_of_derived hD0 hc0 hηI
    · rw [← exactNormalAut_one_one_eq] at hD1 hc1
      exact goodAut_e6One_of_derived hD1 hc1 hηI

end Involutions

end AutSt

end CFSG.StandardType
