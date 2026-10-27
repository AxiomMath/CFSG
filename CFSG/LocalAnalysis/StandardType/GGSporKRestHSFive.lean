module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestComp
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTransport
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOvergroups
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveU35
public import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.AGLEmbeddingD2 CFSG.RankThree.Native

private theorem sporKRest_sylow_normalizer_le_of_controls {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {E Y : Subgroup K} (hEp : IsPGroup p E) (hE1 : E ≠ ⊥)
    (S : Sylow p K) (hSY : (S : Subgroup K) ≤ Y) (hctl : SporKRestControls E Y) :
    ∃ S₁ : Sylow p K, E ≤ S₁ ∧ (S₁ : Subgroup K) ≤ Y ∧
      Subgroup.normalizer ((S₁ : Subgroup K) : Set K) ≤ Y := by
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S
  obtain ⟨⟨e₀, he₀⟩, he₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  replace he₀1 : e₀ ≠ 1 := fun h => he₀1 (Subtype.ext h)
  have hconj : ∀ x ∈ (P : Subgroup K), g * x * g⁻¹ ∈ Y := by
    intro x hx
    have h := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup K) hx
    rw [← Sylow.coe_subgroup_smul, hg, MulAut.smul_def, MulAut.conj_apply] at h
    exact hSY h
  have hgY : g⁻¹ ∈ Y := hctl e₀ he₀ he₀1 g⁻¹ (by simpa using hconj e₀ (hEP he₀))
  have hPY : (P : Subgroup K) ≤ Y := fun x hx => by
    have := Y.mul_mem (Y.mul_mem hgY (hconj x hx)) (Y.inv_mem hgY)
    simpa [mul_assoc] using this
  refine ⟨P, hEP, hPY, fun n hn => ?_⟩
  have hn' := (Subgroup.mem_normalizer_iff''.1 hn e₀).1 (hEP he₀)
  exact hctl e₀ he₀ he₀1 n (hPY hn')

private theorem sporKRest_center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ¬ (Nat.card T).Prime) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with hc | hc
  · exact hc
  · exfalso
    have : IsMulCommutative T := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center T := hc ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    exact h (Group.is_simple_iff_prime_card.mp inferInstance)

private theorem sporKRest_unmarked_of_simple_index_two
    (hmk : ∀ {L : Type} [Group L], Nat.card (L ⧸ Subgroup.center L) = 126000 →
      ¬ LargeEvenMarking L (fun _ _ _ _ _ _ => True))
    {G : Type} [Group G] [Finite G] {U Y : Subgroup G} (hUY : U ≤ Y) (hs : IsSimpleGroup ↥U)
    (hU : Nat.card ↥U = 126000) (hY : Nat.card ↥Y = 252000) : SporKRestUnmarked ↥Y := by
  intro C hC hmark
  have hidx : (U.subgroupOf Y).index = 2 := by
    have h1 : Nat.card ↥(U.subgroupOf Y) = 126000 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, hU]
    have h2 := Subgroup.card_mul_index (U.subgroupOf Y)
    rw [h1, hY] at h2
    omega
  have hN : (U.subgroupOf Y).Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨C', hC', ⟨e⟩⟩ := ggSporKRest_component_transfer hUY hN hidx.le C hC
  have hcore : CFSG.pCore 2 ↥U = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥U) with h | h
    · exact h
    · exfalso
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥U))
      rw [h, Subgroup.card_top, hU] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 126000)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  let φ : (↥U ⧸ CFSG.pCore 2 ↥U) ≃* ↥U :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (↥U ⧸ CFSG.pCore 2 ↥U) := φ.isSimpleGroup
  have hCtop : C' = ⊤ := by
    rcases CFSG.Assembly.IsSubnormal.eq_bot_or_top hC'.2.1 with h | h
    · exfalso
      haveI : Subsingleton ↥C' := by rw [h]; infer_instance
      haveI : Subsingleton (↥C' ⧸ Subgroup.center ↥C') := inferInstance
      haveI : Nontrivial (↥C' ⧸ Subgroup.center ↥C') := hC'.2.2.2.toNontrivial
      exact (not_subsingleton (↥C' ⧸ Subgroup.center ↥C')) inferInstance
    · exact h
  let e2 : ↥C ≃* ↥U :=
    e.trans (((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).trans φ)
  haveI : IsSimpleGroup ↥C := e2.isSimpleGroup
  have hZ : Subgroup.center ↥C = ⊥ :=
    sporKRest_center_eq_bot_of_simple (by rw [Nat.card_congr e2.toEquiv, hU]; norm_num)
  have hq : Nat.card (↥C ⧸ Subgroup.center ↥C) = 126000 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr e2.toEquiv, hU]
  exact hmk hq hmark

private theorem sporKRest_hsOR0_le_hs100P :
    hsOR0 ≤ hs100P :=
  hsOR0_le_UA.trans (hsOUA_le_UA2.trans hsOUA2_le)

private theorem sporKRest_unmarked_of_hs_overgroup
    (hmk : ∀ {L : Type} [Group L], Nat.card (L ⧸ Subgroup.center L) = 126000 →
      ¬ LargeEvenMarking L (fun _ _ _ _ _ _ => True))
    (R : Sylow 5 ↥hs100P) (hR : (R : Subgroup ↥hs100P) = hsOR0.subgroupOf hs100P)
    (Y : Subgroup ↥hs100P) (hYtop : Y ≠ ⊤)
    (hNY : Subgroup.normalizer ((R : Subgroup ↥hs100P) : Set ↥hs100P) ≤ Y) :
    SporKRestUnmarked ↥Y := by
  have hNR : Subgroup.normalizer ((R : Subgroup ↥hs100P) : Set ↥hs100P) =
      (Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100)))).subgroupOf hs100P := by
    rw [hR]
    exact (Subgroup.subgroupOf_normalizer_eq sporKRest_hsOR0_le_hs100P).symm
  set Y₂ : Subgroup (Equiv.Perm (Fin 100)) := Y.map hs100P.subtype with hY₂
  have hY₂P : Y₂ ≤ hs100P := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hY₂N : hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y₂ := by
    rintro g ⟨hgP, hgN⟩
    refine ⟨⟨g, hgP⟩, hNY ?_, rfl⟩
    rw [hNR]
    exact hgN
  let eY : ↥Y ≃* ↥Y₂ := Subgroup.equivMapOfInjective Y hs100P.subtype hs100P.subtype_injective
  have hUA : SporKRestUnmarked ↥hsOUA2 :=
    sporKRest_unmarked_of_simple_index_two hmk hsOUA_le_UA2 hsOUA_isSimpleGroup card_hsOUA
      card_hsOUA2
  rcases hs100P_normalizer_overgroups Y₂ hY₂N hY₂P with h | h | h | h
  ·
    have hYle : Y ≤ Subgroup.normalizer ((R : Subgroup ↥hs100P) : Set ↥hs100P) := by
      intro y hy
      rw [hNR]
      have hy₂ : (y : Equiv.Perm (Fin 100)) ∈ Y₂ := ⟨y, hy, rfl⟩
      rw [h] at hy₂
      exact hy₂.2
    have hsolv := (heisLocalEq_hsP (MulEquiv.refl ↥hs100P) R).2.2.2.2.2.1
    rw [le_antisymm hYle hNY]
    exact ggSporKRest_unmarked_of_solvable hsolv
  ·
    exact SporKRestUnmarked.of_mulEquiv ((MulEquiv.subgroupCongr h.symm).trans eY.symm) hUA
  ·
    let eB : ↥hsOUA2 ≃* ↥hsOUB2 :=
      (Subgroup.equivMapOfInjective hsOUA2 (MulAut.conj hsOW0).toMonoidHom
        (MulAut.conj hsOW0).injective).trans (MulEquiv.subgroupCongr hsOUB2_eq_map.symm)
    exact SporKRestUnmarked.of_mulEquiv
      (eB.trans ((MulEquiv.subgroupCongr h.symm).trans eY.symm)) hUA
  ·
    exfalso
    apply hYtop
    rw [eq_top_iff]
    intro y _
    have hy : (y : Equiv.Perm (Fin 100)) ∈ Y₂ := by rw [h]; exact y.2
    obtain ⟨y', hy', hyy⟩ := hy
    exact (Subtype.ext hyy) ▸ hy'

private theorem sporKRest_coverOrUnmarked_hs100P
    (hmk : ∀ {L : Type} [Group L], Nat.card (L ⧸ Subgroup.center L) = 126000 →
      ¬ LargeEvenMarking L (fun _ _ _ _ _ _ => True)) :
    SporKRestCoverOrUnmarked 5 ↥hs100P := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hR0card : Nat.card (hsOR0.subgroupOf hs100P) =
      5 ^ (Nat.card ↥hs100P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sporKRest_hsOR0_le_hs100P).toEquiv,
      card_hsOR0, factorization_card_hs100P_five]
    norm_num
  let R : Sylow 5 ↥hs100P := Sylow.ofCard (hsOR0.subgroupOf hs100P) hR0card
  have hR : (R : Subgroup ↥hs100P) = hsOR0.subgroupOf hs100P := rfl
  intro E hE hcard
  refine Or.inr fun Y hY ⟨S, hSY⟩ hctl => ?_
  have hEp : IsPGroup 5 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨S₁, -, -, hN⟩ := sporKRest_sylow_normalizer_le_of_controls hEp hE1 S hSY hctl
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥hs100P R S₁
  have hNk : ∀ n ∈ Subgroup.normalizer ((R : Subgroup ↥hs100P) : Set ↥hs100P),
      k * n * k⁻¹ ∈ Subgroup.normalizer ((S₁ : Subgroup ↥hs100P) : Set ↥hs100P) := by
    intro n hn
    have h1 : n • R = R := Sylow.smul_eq_iff_mem_normalizer.2 hn
    refine Sylow.smul_eq_iff_mem_normalizer.1 ?_
    calc (k * n * k⁻¹) • S₁ = (k * n * k⁻¹) • (k • R) := by rw [hk]
      _ = ((k * n * k⁻¹) * k) • R := (mul_smul _ _ _).symm
      _ = (k * n) • R := by rw [show k * n * k⁻¹ * k = k * n by group]
      _ = k • (n • R) := mul_smul _ _ _
      _ = k • R := by rw [h1]
      _ = S₁ := hk
  let Y' : Subgroup ↥hs100P := Y.map (MulAut.conj k⁻¹).toMonoidHom
  have hNY' : Subgroup.normalizer ((R : Subgroup ↥hs100P) : Set ↥hs100P) ≤ Y' := by
    intro n hn
    refine ⟨k * n * k⁻¹, hN (hNk n hn), ?_⟩
    show k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n
    group
  have hYtop' : Y' ≠ ⊤ := by
    intro htop
    apply hY
    rw [eq_top_iff]
    intro y _
    have hy : k⁻¹ * y * k ∈ Y' := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := by
      have h2 : k⁻¹ * z * k = k⁻¹ * y * k := by simpa using hzy
      exact mul_left_cancel (mul_right_cancel h2)
    exact hzy' ▸ hz
  exact SporKRestUnmarked.of_mulEquiv (MulEquiv.subgroupMap (MulAut.conj k⁻¹) Y).symm
    (sporKRest_unmarked_of_hs_overgroup hmk R hR Y' hYtop' hNY')

theorem sporKRest_coverOrUnmarked_HS_5 :
    SporKRestCoverOrUnmarked 5 (TauCeti.CFSGIndex.sporadic .HS).Group := by
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  exact @SporKRestCoverOrUnmarked.of_mulEquiv ↥hs100P (TauCeti.CFSGIndex.sporadic .HS).Group
    inferInstance inferInstance (hs100Equiv.symm.trans eC) 5
    (sporKRest_coverOrUnmarked_hs100P fun h => largeEvenMarking_not_card_126000 h)

end CFSG.StandardType.SporadicShape
