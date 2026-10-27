module

public import CFSG.LocalAnalysis.StandardType.GGRCSShadowSeitzComp
public import CFSG.LocalAnalysis.StandardType.SpTwoThreeFixedPoints
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Rigid

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggAllInner_of_lieModel_PSp {K : Type} [Group K] {m : ℕ} (hm : 3 ≤ m)
    (hK : LieModel K .PSp m 2 1) : ∀ α : MulAut K, ∃ k : K, α = MulAut.conj k := by
  intro α
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK.statedClassicalModel (by decide)
  have hF' : Nat.card F = 2 := by simpa using hF
  obtain ⟨g, hg⟩ := SpTwoThree.all_inner_statedProj hF' hm (MulAut.congr e α)
  obtain ⟨k, hk⟩ := (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e α).mp ⟨g, hg.symm⟩
  exact ⟨k, hk.symm⟩

private theorem ggShR_E_le_generalizedFitting
    (hin : ∀ α : MulAut ↥(CFSG.generalizedFitting W), ∃ k, α = MulAut.conj k)
    (hyp : GGHypThreeSixteenFlat p H E) :
    E ≤ CFSG.generalizedFitting W := by
  obtain ⟨⟨-, -, -, -, -⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  haveI : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  intro e he
  obtain ⟨k, hk⟩ := hin (MulAut.conjNormal (H := CFSG.generalizedFitting W) e)
  have hcomm : ∀ x ∈ CFSG.generalizedFitting W,
      ((k : W)⁻¹ * e) * x = x * ((k : W)⁻¹ * e) := by
    intro x hx
    have h1 : e * x * e⁻¹ = (k : W) * x * (k : W)⁻¹ := by
      have h := congrArg Subtype.val (DFunLike.congr_fun hk ⟨x, hx⟩)
      rw [MulAut.conjNormal_apply] at h
      simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
    calc ((k : W)⁻¹ * e) * x = (k : W)⁻¹ * (e * x * e⁻¹) * e := by group
      _ = (k : W)⁻¹ * ((k : W) * x * (k : W)⁻¹) * e := by rw [h1]
      _ = x * ((k : W)⁻¹ * e) := by group
  have hw : (k : W)⁻¹ * e = 1 :=
    ggEq_one_of_commute_generalizedFitting hsimple hnab hcomm
  have hek : e = (k : W) := by
    calc e = (k : W) * ((k : W)⁻¹ * e) := by group
      _ = (k : W) * 1 := by rw [hw]
      _ = (k : W) := mul_one _
  rw [hek]
  exact k.2

private theorem ggShR_E_le_commutator
    (hyp : GGHypThreeSixteenFlat p H E)
    (hEK : E ≤ CFSG.generalizedFitting W)
    (hidx : ¬ p ∣ ((⁅H ⊓ CFSG.generalizedFitting W, H ⊓ CFSG.generalizedFitting W⁆ :
      Subgroup W).subgroupOf (CFSG.generalizedFitting W)).index) :
    E ≤ ⁅H ⊓ CFSG.generalizedFitting W, H ⊓ CFSG.generalizedFitting W⁆ := by
  obtain ⟨⟨hp, -, hEel, -, hfus⟩, -⟩ := hyp
  haveI : Fact p.Prime := ⟨hp⟩
  set K := CFSG.generalizedFitting W with hKdef
  set M : Subgroup W := ⁅H ⊓ K, H ⊓ K⁆ with hMdef
  have hEH : E ≤ H := hfus.1
  have hEHK : E ≤ H ⊓ K := le_inf hEH hEK
  have hMle : M ≤ H ⊓ K := Subgroup.commutator_le_self (H ⊓ K)
  have hNcomm : M.subgroupOf (H ⊓ K) = commutator ↥(H ⊓ K) := by
    apply Subgroup.map_injective (H ⊓ K).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hMle, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top, Subgroup.range_subtype]
  have hNnormal : (M.subgroupOf (H ⊓ K)).Normal := by
    rw [hNcomm]
    infer_instance
  have hNindex : ¬ p ∣ (M.subgroupOf (H ⊓ K)).index := by
    intro hdvd
    have hrel : M.relIndex (H ⊓ K) * (H ⊓ K).relIndex K = M.relIndex K :=
      Subgroup.relIndex_mul_relIndex M (H ⊓ K) K hMle inf_le_right
    have h1 : M.relIndex (H ⊓ K) = (M.subgroupOf (H ⊓ K)).index := by
      change M.relIndex (H ⊓ K) = (M.comap (H ⊓ K).subtype).index
      rw [Subgroup.index_comap, Subgroup.range_subtype]
    have h2 : M.relIndex K = (M.subgroupOf K).index := by
      change M.relIndex K = (M.comap K.subtype).index
      rw [Subgroup.index_comap, Subgroup.range_subtype]
    have h3 : (H ⊓ K).relIndex K = (H.subgroupOf K).index := by
      rw [← Subgroup.inf_subgroupOf_right]
      change (H ⊓ K).relIndex K = ((H ⊓ K).comap K.subtype).index
      rw [Subgroup.index_comap, Subgroup.range_subtype]
    rw [h1, h3, h2] at hrel
    refine hidx ?_
    rw [← hrel]
    exact dvd_mul_of_dvd_left hdvd _
  have hEp : IsPGroup p ↥E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 g.1 g.2)⟩
  have hPp : IsPGroup p (E.subgroupOf (H ⊓ K)) :=
    IsPGroup.comap_of_injective hEp (H ⊓ K).subtype (H ⊓ K).subtype_injective
  haveI := hNnormal
  have hle : E.subgroupOf (H ⊓ K) ≤ M.subgroupOf (H ⊓ K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1810_le_of_not_dvd_index hPp hNindex
  intro e he
  have he' : (⟨e, hEHK he⟩ : ↥(H ⊓ K)) ∈ E.subgroupOf (H ⊓ K) := by
    rw [Subgroup.mem_subgroupOf]; exact he
  exact Subgroup.mem_subgroupOf.mp (hle he')

private theorem ggShR_mem_commutator_of_pElement
    (hp : p.Prime)
    (hidx : ¬ p ∣ ((⁅H ⊓ CFSG.generalizedFitting W, H ⊓ CFSG.generalizedFitting W⁆ :
      Subgroup W).subgroupOf (CFSG.generalizedFitting W)).index)
    {k : W} (hkK : k ∈ CFSG.generalizedFitting W)
    (hkp : IsPGroup p (Subgroup.zpowers (⟨k, hkK⟩ : ↥(CFSG.generalizedFitting W))))
    (hkc : ∀ m ∈ (⁅H ⊓ CFSG.generalizedFitting W,
      H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W), k * m = m * k) :
    k ∈ (⁅H ⊓ CFSG.generalizedFitting W,
      H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K := CFSG.generalizedFitting W with hKdef
  set M : Subgroup W := ⁅H ⊓ K, H ⊓ K⁆ with hMdef
  set N : Subgroup K := M.subgroupOf K with hNdef
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥N)
  have hPindex : ¬ p ∣ (S.toSubgroup.map N.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact Sylow.not_dvd_index S h
    · exact hidx (hNdef ▸ h)
  have hPp : IsPGroup p (S.toSubgroup.map N.subtype) := (Sylow.isPGroup' S).map N.subtype
  let S' : Sylow p K := hPp.toSylow hPindex
  have hS' : (S' : Subgroup K) = S.toSubgroup.map N.subtype := IsPGroup.toSylow_coe hPp hPindex
  let kK : K := ⟨k, hkK⟩
  have hPle : S.toSubgroup.map N.subtype ≤ N := Subgroup.map_subtype_le _
  have hcommP : ∀ x ∈ S.toSubgroup.map N.subtype, kK * x = x * kK := by
    intro x hx
    have hxM : ((x : K) : W) ∈ M := hPle hx
    apply Subtype.ext
    exact hkc (x : K) hxM
  have hcent : kK ∈ Subgroup.centralizer ((S.toSubgroup.map N.subtype : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcommP x hx).symm
  have hnorm : Subgroup.zpowers kK ≤ Subgroup.normalizer (S.toSubgroup.map N.subtype) :=
    (Subgroup.zpowers_le.mpr hcent).trans (Subgroup.centralizer_le_normalizer _)
  have hQp : IsPGroup p ↥((S.toSubgroup.map N.subtype) ⊔ Subgroup.zpowers kK) :=
    IsPGroup.to_sup_of_normal_left' hPp hkp hnorm
  have hkP : kK ∈ S.toSubgroup.map N.subtype := by
    have hmax : (S.toSubgroup.map N.subtype) ⊔ Subgroup.zpowers kK = (S' : Subgroup K) := by
      refine Sylow.is_maximal' S' hQp ?_
      rw [hS']
      exact le_sup_left
    have hmem : kK ∈ (S.toSubgroup.map N.subtype) ⊔ Subgroup.zpowers kK :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers kK)
    rw [hmax, hS'] at hmem
    exact hmem
  exact Subgroup.mem_subgroupOf.mp (hPle hkP)

theorem ggShadow_rigid (hyp : GGHypThreeSixteenFlat p H E)
    (hCE : IsPGroup p ↥(CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W)))
    (hin : ∀ α : MulAut ↥(CFSG.generalizedFitting W), ∃ k, α = MulAut.conj k)
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))))
    (hns : ¬ Group.IsSolvable ↥(H.subgroupOf (CFSG.generalizedFitting W)))
    (hidx : ¬ p ∣ ((⁅H ⊓ CFSG.generalizedFitting W, H ⊓ CFSG.generalizedFitting W⁆ :
      Subgroup W).subgroupOf (CFSG.generalizedFitting W)).index) :
    ∀ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ →
      ∀ α : MulAut ↥(CFSG.generalizedFitting W),
        (∀ c ∈ C, α ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ = ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩) →
          α = 1 := by
  intro C hC α hα
  have hEK : E ≤ CFSG.generalizedFitting W := ggShR_E_le_generalizedFitting hin hyp
  have hEM : E ≤ ⁅H ⊓ CFSG.generalizedFitting W,
      H ⊓ CFSG.generalizedFitting W⁆ := ggShR_E_le_commutator hyp hEK hidx
  obtain ⟨k, hk⟩ := hin α
  have hkc : ∀ m ∈ (⁅H ⊓ CFSG.generalizedFitting W,
      H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W), (k : W) * m = m * (k : W) := by
    intro m hm
    have hCmap := ggShadow_component_map_eq (H := H) hs hC
    have hm' : m ∈ C.map (H ⊓ CFSG.generalizedFitting W).subtype := by
      rw [hCmap]; exact hm
    obtain ⟨c, hc, hcm⟩ := Subgroup.mem_map.mp hm'
    have h1 := hα c hc
    rw [hk] at h1
    have h2 : (k : W) * c.1 * (k : W)⁻¹ = c.1 := by
      have h := congrArg Subtype.val h1
      simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
    have h3 : (k : W) * c.1 = c.1 * (k : W) := mul_inv_eq_iff_eq_mul.mp h2
    have hcm' : (c : W) = m := hcm
    rw [hcm'] at h3
    exact h3
  have hkK : (k : W) ∈ CFSG.generalizedFitting W := k.2
  have hkC : (k : W) ∈ Subgroup.centralizer (E : Set W) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hkc e (hEM he)).symm
  have hkL : (k : W) ∈ CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W) :=
    Subgroup.mem_inf.mpr ⟨hkK, hkC⟩
  have hkpW : IsPGroup p (Subgroup.zpowers (k : W)) :=
    IsPGroup.to_le hCE (Subgroup.zpowers_le.mpr hkL)
  have hkpK : IsPGroup p (Subgroup.zpowers (⟨(k : W), hkK⟩ : ↥(CFSG.generalizedFitting W))) :=
    IsPGroup.to_le
      (IsPGroup.comap_of_injective hkpW (CFSG.generalizedFitting W).subtype
        (Subgroup.subtype_injective _))
      (Subgroup.zpowers_le.mpr (by
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_zpowers (k : W)))
  have hkM : (k : W) ∈ ⁅H ⊓ CFSG.generalizedFitting W,
      H ⊓ CFSG.generalizedFitting W⁆ :=
    ggShR_mem_commutator_of_pElement hyp.1.1 hidx hkK hkpK hkc
  have hk1 : k = 1 := by
    let eM := ggInfCommutatorEquiv H (CFSG.generalizedFitting W)
    have hX'ns : ¬ Group.IsSolvable
        ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
      fun h => hns (ggIsSolvable_of_commutator h)
    haveI : IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) := hs
    have hZ : Subgroup.center ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) = ⊥ :=
      ggCenter_eq_bot_of_not_isSolvable hX'ns
    have hkcenter : (⟨(k : W), hkM⟩ : ↥(⁅H ⊓ CFSG.generalizedFitting W,
        H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W)) ∈
        Subgroup.center ↥(⁅H ⊓ CFSG.generalizedFitting W,
          H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact (hkc x.1 x.2).symm
    have hmem : eM ⟨(k : W), hkM⟩ ∈ Subgroup.center
        ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) := by
      rw [← Subgroup.map_center_eq eM]
      exact Subgroup.mem_map_of_mem eM.toMonoidHom hkcenter
    rw [hZ, Subgroup.mem_bot] at hmem
    have h1 : (⟨(k : W), hkM⟩ : ↥(⁅H ⊓ CFSG.generalizedFitting W,
        H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W)) = 1 :=
      eM.injective (by simpa using hmem)
    exact Subtype.ext (congrArg (fun x : ↥(⁅H ⊓ CFSG.generalizedFitting W,
      H ⊓ CFSG.generalizedFitting W⁆ : Subgroup W) => (x : W)) h1)
  rw [hk, hk1]
  simp

theorem ggShadow_rigid_spEight (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .PSp 4 2 1)
    (hCE : IsPGroup p ↥(CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W))) :
    ∀ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ →
      ∀ α : MulAut ↥(CFSG.generalizedFitting W),
        (∀ c ∈ C, α ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ = ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩) →
          α = 1 := by
  refine ggShadow_rigid hyp hCE (ggAllInner_of_lieModel_PSp (by norm_num) hK) ?_ ?_ ?_
  · exact (ggShadow_spEight_component hyp hL hperf hKH hp hK).1
  · exact ggShadow_not_isSolvable hperf hL
  · intro hdvd
    have hX'card : Nat.card ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) =
        174182400 := (ggShadow_spEight_component hyp hL hperf hKH hp hK).2.1
    set M : Subgroup W := ⁅H ⊓ CFSG.generalizedFitting W,
        H ⊓ CFSG.generalizedFitting W⁆ with hMdef
    have hMcard : Nat.card ↥M = 174182400 := by
      rw [hMdef]
      exact (Nat.card_congr (ggInfCommutatorEquiv H
        (CFSG.generalizedFitting W)).toEquiv).trans hX'card
    set N : Subgroup ↥(CFSG.generalizedFitting W) :=
      M.subgroupOf (CFSG.generalizedFitting W) with hNdef
    have hNcard : Nat.card ↥N = 174182400 := by
      rw [hNdef]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show M ≤ CFSG.generalizedFitting W from
          (Subgroup.commutator_le_self (H ⊓ CFSG.generalizedFitting W)).trans
            inf_le_right)).toEquiv]
      exact hMcard
    have hKcard : Nat.card ↥(CFSG.generalizedFitting W) = 47377612800 := by
      rw [(CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSp hK).2]
      decide
    have hcardmul := Subgroup.card_mul_index N
    rw [hNcard, hKcard] at hcardmul
    have hmul : 174182400 * N.index = 174182400 * 272 := by
      rw [hcardmul]
    have hindex : N.index = 272 := Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
    rw [hindex, hp] at hdvd
    norm_num at hdvd

theorem ggShadow_rigid_spSix
    (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .PSp 3 2 1)
    (hCE : IsPGroup p ↥(CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W))) :
    ∀ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ →
      ∀ α : MulAut ↥(CFSG.generalizedFitting W),
        (∀ c ∈ C, α ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ = ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩) →
          α = 1 := by
  refine ggShadow_rigid hyp hCE (ggAllInner_of_lieModel_PSp (by norm_num) hK) ?_ ?_ ?_
  · exact (ggShadow_spSix_component hyp hL hperf hKH hp hK).1
  · exact ggShadow_not_isSolvable hperf hL
  · intro hdvd
    have hX'card : Nat.card ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) =
        25920 := (ggShadow_spSix_component hyp hL hperf hKH hp hK).2.1
    set M : Subgroup W := ⁅H ⊓ CFSG.generalizedFitting W,
        H ⊓ CFSG.generalizedFitting W⁆ with hMdef
    have hMcard : Nat.card ↥M = 25920 := by
      rw [hMdef]
      exact (Nat.card_congr (ggInfCommutatorEquiv H
        (CFSG.generalizedFitting W)).toEquiv).trans hX'card
    set N : Subgroup ↥(CFSG.generalizedFitting W) :=
      M.subgroupOf (CFSG.generalizedFitting W) with hNdef
    have hNcard : Nat.card ↥N = 25920 := by
      rw [hNdef]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show M ≤ CFSG.generalizedFitting W from
          (Subgroup.commutator_le_self (H ⊓ CFSG.generalizedFitting W)).trans
            inf_le_right)).toEquiv]
      exact hMcard
    have hKcard : Nat.card ↥(CFSG.generalizedFitting W) = 1451520 := by
      rw [(CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSp hK).2]
      decide
    have hcardmul := Subgroup.card_mul_index N
    rw [hNcard, hKcard] at hcardmul
    have hmul : 25920 * N.index = 25920 * 56 := by
      rw [hcardmul]
    have hindex : N.index = 56 := Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
    rw [hindex, hp] at hdvd
    norm_num at hdvd

end Rigid

end CFSG.StandardType
