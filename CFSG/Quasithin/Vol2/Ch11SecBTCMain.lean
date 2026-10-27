module

public import CFSG.Quasithin.Vol2.Ch11SecBTCSteps2
public import CFSG.Quasithin.Vol2.Ch11SecBDerived35
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement Pointwise

theorem derivedTwoComponents_of (hSL2 : ∀ (k : ℕ) (F : Type) [Field F] [Finite F],
    Nat.card F = 2 ^ k → 2 ≤ k →
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ ∧
      ∀ S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), IsSylowTwoOf S ⊤ →
        (2 ^ k - 1) ∣
          Nat.card ↥(Subgroup.normalizer (S : Set (Matrix.SpecialLinearGroup (Fin 2) F)))) :
    DerivedTwoComponents := by
  intro G _ _ T L I n H K D k p hyp hH hKc hHK hcases hTK hk2 hnk hiso hD _ hTD hp hp2 hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set X := H ⊓ M with hXdef
  have hTH : T ≤ H := hH.1.1
  have hTM : T ≤ M := hyp.normal
  have hXH : X ≤ H := inf_le_left
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hU : IsUniqueMaxOver H T X := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hTM)
    rwa [hP] at this
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hns : ¬ Group.IsSolvable ↥H := fun hsol => not_isSolvable_of_mem_cComp hKc
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
      (Subgroup.inclusion_injective hKH))
  dsimp only [E2.E22Cases] at hcases
  rcases hcases with ⟨hJ, -, -, -, -, h1⟩ | ⟨hTK', -⟩
  swap
  · exact absurd hTK' hTK
  obtain ⟨-, -, -, hBor, -⟩ := h1.resolve_right fun ⟨_, _, _, _, _, _, hn⟩ => by
    rw [hnk] at hn
    have : k = 1 := by exact_mod_cast hn
    omega
  have hJ2 : IsPGroup 2 ↥(kerIn X H) := hJ ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hJs : Group.IsSolvable ↥(kerIn X H) := by
    have := hJ2.isNilpotent
    infer_instance
  have hRJ : solvRad H ≤ kerIn X H := solvRad_le_kerIn hU hT2 hns
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hiso
  have hOK : pCoreOf 2 K ≤ kerIn X H := hJ ▸
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hKc)
  have hKJ : K ⊓ kerIn X H ≤ pCoreOf 2 K := hJ ▸ inf_pCoreOf_le_pCoreOf hKH
  obtain ⟨ε⟩ := nonempty_mulEquiv_star hKH hOK hKJ e
  obtain ⟨hZ0, hdvd0⟩ := hSL2 k F hFc hk2
  have hZ := center_eq_bot_of_mulEquiv ε hZ0
  obtain ⟨S, hS, hMK⟩ := hBor
  have hS' : IsSylowTwoOf (S.subgroupOf (E2.star X H K)) ⊤ := by
    refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
    show ¬ 2 ∣ (S.subgroupOf (E2.star X H K)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hS.2.2
  have hdvd := dvd_card_normalizer_of_mulEquiv ε hdvd0 _ hS'
  rw [card_normalizer_subgroupOf hS.1, ← hMK] at hdvd
  obtain ⟨y, hyX, hyK, hyo⟩ : ∃ y ∈ X, y ∈ K ∧ orderOf y = p := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(E2.star X H (X ⊓ K))) p
      (hpk.trans hdvd)
    obtain ⟨y₀, hy₀, hy₀z⟩ := z.2
    have hz' : orderOf (QuotientGroup.mk' ((kerIn X H).subgroupOf H) y₀) = p := by
      rw [hy₀z, Subgroup.orderOf_coe]
      exact hz
    have hpd : p ∣ orderOf y₀ := hz' ▸ orderOf_map_dvd _ y₀
    have hy1 := orderOf_pow_orderOf_div (orderOf_pos y₀).ne' hpd
    refine ⟨((y₀ ^ (orderOf y₀ / p) : ↥H) : G), ?_, ?_, ?_⟩
    · rw [Subgroup.coe_pow]
      exact X.pow_mem (Subgroup.mem_subgroupOf.mp hy₀).1 _
    · rw [Subgroup.coe_pow]
      exact K.pow_mem (Subgroup.mem_subgroupOf.mp hy₀).2 _
    · rw [Subgroup.orderOf_coe, hy1]
  have hO := pCoreOf_le_normalizer_of_star hXH hJ2 hRJ hKc hZ hyX hyK hp hp2 hyo
  obtain ⟨t, htT, htD, htK⟩ : ∃ t ∈ T, t ∈ Subgroup.normalizer (D : Set G) ∧
      t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hTK (hTD.trans (sup_le hO fun t ht => hcon t ht.1 ht.2))
  obtain ⟨d, hdD, hdKJ, hdo⟩ :=
    exists_mem_hall_order hXH hTH hT2 hHK hJs hRJ hKc hD hyX hyK hp2 hyo
  refine ⟨t, htT, htD, d, hdD, hdo ▸ pow_orderOf_eq_one d, fun hmem => ?_⟩
  have hdH : d ∈ H := hXH (hD.1 hdD)
  have htH : t ∈ H := hTH htT
  have hK'c : cjSub t K ∈ cComp H := by
    have := cComp_map_mulEquiv (MulAut.conj t) hKc
    rwa [map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer htH)] at this
  have hne : E2.star X H (cjSub t K) ≠ E2.star X H K := fun h =>
    htK (mem_normalizer_of_map_conj_eq (eq_of_star_eq hXH hJs hK'c hKc h))
  have hcomm : ⁅E2.star X H (cjSub t K), E2.star X H K⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute (isComponent_star hXH hJs hRJ hK'c)
      (isComponent_star hXH hJs hRJ hKc)).resolve_left hne
  set π := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hπ
  have hdtH : t * d * t⁻¹ ∈ H := H.mul_mem (H.mul_mem htH hdH) (H.inv_mem htH)
  have hdt1 : π ⟨t * d * t⁻¹, hdtH⟩ ∈ E2.star X H (cjSub t K) := by
    refine mem_star_of_mem_sup hXH (le_of_mem_cComp hK'c) ?_ hdtH
    have : t * d * t⁻¹ ∈ (K ⊔ kerIn X H).map (MulAut.conj t).toMonoidHom := ⟨d, hdKJ, rfl⟩
    rwa [Subgroup.map_sup,
      map_conj_eq_self_of_mem_normalizer (le_normalizer_kerIn X H htH)] at this
  have hdt2 : π ⟨t * d * t⁻¹, hdtH⟩ ∈ E2.star X H K :=
    mem_star_of_mem_sup hXH hKH (Subgroup.zpowers_le.mpr hdKJ hmem) hdtH
  have h1 := eq_one_of_mem_of_commutator_eq_bot hZ hcomm hdt2 hdt1
  have hd1 : π ⟨d, hdH⟩ = 1 := by
    have e1 : π ⟨t * d * t⁻¹, hdtH⟩ = π ⟨t, htH⟩ * π ⟨d, hdH⟩ * (π ⟨t, htH⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1] at h1
    have := congrArg (fun z => (π ⟨t, htH⟩)⁻¹ * z * π ⟨t, htH⟩) h1
    simpa [mul_assoc] using this
  have hdJ : d ∈ kerIn X H := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hd1
    exact hd1
  obtain ⟨b, hb⟩ := hJ2 ⟨d, hdJ⟩
  have hb' : d ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hd1' : d = 1 :=
    eq_one_of_pow_two_pow_of_pow_prime hp hp2 hb' (hdo ▸ pow_orderOf_eq_one d)
  rw [hd1', orderOf_one] at hdo
  exact hp.one_lt.ne hdo

end CFSG.Quasithin.Vol2.Ch11.SecB
