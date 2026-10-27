module

public import CFSG.RankThree.PartOne.CTP.SeitzD4Generation
public import CFSG.RankThree.PartOne.CTP.SeitzLift
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.RankThree.PartOne.CTP.D4Two

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly.LowTwoRank

theorem card_K2 : Nat.card K2 = 2 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_orthogonalGroup_Qf :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qf) = 348364800 := by
  have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K2) 3).2
  rw [card_K2] at h
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qf) : ℤ) = 348364800 := by
    rw [show (348364800 : ℤ) = 2 * (2 : ℤ) ^ (3 * (3 + 1)) * ((2 : ℤ) ^ (3 + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 3, ((2 : ℤ) ^ (2 * i) - 1) by decide]
    exact_mod_cast h
  exact_mod_cast h2

theorem prime_eq_five_of_sq_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 348364800) : p = 5 := by
  have hpd : p ∣ 348364800 := (dvd_pow_self p two_ne_zero).trans h
  have hN : (348364800 : ℕ) = 2 ^ 13 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num
  rw [hN] at hpd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h2)
  · have h7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h1
    subst h7
    exact absurd h (by norm_num)

theorem finite_linearEquiv_K2 : Finite (Vec ≃ₗ[K2] Vec) :=
  Finite.of_injective (fun g : Vec ≃ₗ[K2] Vec => (g : Vec → Vec)) DFunLike.coe_injective

theorem closure_centralizers_plane_Ω {E : Subgroup (orthDerived Qf)} (hcard : Nat.card E = 25) :
    Subgroup.closure {h : orthDerived Qf | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := finite_linearEquiv_K2
  have hdvdΩ : Nat.card (orthDerived Qf) ∣ 348364800 :=
    card_orthogonalGroup_Qf ▸ Subgroup.card_dvd_of_le
      (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Qf)
  have h25 : 5 ^ 2 ∣ Nat.card (orthDerived Qf) := by
    have := Subgroup.card_subgroup_dvd_card E
    rwa [hcard] at this
  have hfac : (Nat.card (orthDerived Qf)).factorization 5 = 2 := by
    have hge : 2 ≤ (Nat.card (orthDerived Qf)).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').1 h25
    have hle : (Nat.card (orthDerived Qf)).factorization 5 ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have h125 : 5 ^ 3 ∣ Nat.card (orthDerived Qf) :=
        (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').2 hlt
      have := h125.trans hdvdΩ
      norm_num at this
    omega
  let P₀ : Sylow 5 (orthDerived Qf) := Sylow.ofCard E₀Ω (by rw [card_E₀Ω, hfac]; norm_num)
  let P : Sylow 5 (orthDerived Qf) := Sylow.ofCard E (by rw [hcard, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (orthDerived Qf) P P₀
  have hmap : E.map (MulAut.conj g).toMonoidHom = E₀Ω := by
    have h := congrArg (fun Q : Sylow 5 (orthDerived Qf) => (Q : Subgroup (orthDerived Qf))) hg
    have h' : E.map (MulDistribMulAction.toMonoidHom (orthDerived Qf) (MulAut.conj g)) = E₀Ω := by
      simpa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, P, P₀] using h
    exact h'
  refine closure_centralizers_transfer (MulAut.conj g) E ?_
  rw [hmap]
  exact closure_centralizers_E₀Ω

theorem closure_centralizers_statedProj_quadPlus_four_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K2))))
    [CFSG.IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus 4 K2)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQ : ⇑Qf = StatedQuadPlus 4 K2 := coe_quadPlus 4 K2
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆ =
      elementaryGroup Qf := commutator_orthogonalGroup_quadPlus (K := K2) (n := 4) (by norm_num)
  have hnd := nondegenerate_polarBilin_quadPlus 4 K2
  have : Nontrivial Vec := inferInstance
  have := finite_linearEquiv_K2
  let ψ : StatedOmega (StatedQuadPlus 4 K2) ≃* orthDerived Qf :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega (StatedQuadPlus 4 K2),
      ((ψ y : orthDerived Qf) : Vec ≃ₗ[K2] Vec) = toLinEquiv Idx K2 (y : GL Idx K2) :=
    fun y => rfl
  let π : orthDerived Qf →* StatedProj (StatedOmega (StatedQuadPlus 4 K2)) :=
    (QuotientGroup.mk' ((StatedScalars _ K2).subgroupOf
      (StatedOmega (StatedQuadPlus 4 K2)))).comp ψ.symm.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.symm.surjective
  have hker : π.ker = (scalars K2 Vec).subgroupOf (orthDerived Qf) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  refine closure_centralizers_of_lift π hπ hker' E hcomm hexp fun E' hc he hcd _ => ?_
  have hE'card : Nat.card E' = p ^ 2 := hcd.trans hcard
  have hdvd : p ^ 2 ∣ 348364800 := by
    rw [← hE'card, ← card_orthogonalGroup_Qf]
    exact (Subgroup.card_subgroup_dvd_card E').trans
      (Subgroup.card_dvd_of_le (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Qf))
  have hp5' := prime_eq_five_of_sq_dvd hp hp5 hdvd
  subst hp5'
  exact closure_centralizers_plane_Ω hE'card

theorem extSeitzAtInner_D_four_two {q : TauCeti.PrimePower} (hq : q.p = 2) (he : q.exponent = 1) :
    ExtSeitzAtInner (.D 4 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hF : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 := by
    have h : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) =
        q.p ^ q.exponent := by
      rw [TauCeti.ValidLieTypeIndex.card_fixedField]
      simp [TauCeti.ValidLieTypeIndex.fieldOrder]
    rw [h, hq, he]
    norm_num
  have e1 := e0.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj 4 q hv
    hq)
  have : Fintype ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) := Fintype.ofFinite _
  have hcardF : Fintype.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) =
      Fintype.card K2 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_K2]
  let φ : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) ≃+* K2 :=
    FiniteField.ringEquivOfCardEq hcardF
  let e2 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.statedQuadPlus_comp φ 4))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (e1.trans e2) (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_quadPlus_four_two hp hp5 E₁ hcard₁

end CFSG.RankThree.PartOne.CTP.D4Two
