module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc
import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFIn2
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

theorem ggTorusSelfCent_map_descAut {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hZ : ψ.ker = Subgroup.center L')
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center L')) {A : Subgroup (MulAut L')}
    (hA : GGTorusSelfCent 3 A) : GGTorusSelfCent 3 (A.map (BstarDesc.descAut hψ hZ)) := by
  have hcop : ∀ z ∈ Subgroup.center L', Nat.Coprime 3 (orderOf z) := fun z hz =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hZ3 (h3.trans (Subgroup.orderOf_dvd_natCard _ hz))
  intro r hr hr3
  obtain ⟨l, rfl⟩ := hψ r
  have hl3 : l ^ 3 ∈ Subgroup.center L' := by
    rw [← hZ, MonoidHom.mem_ker, map_pow, hr3]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (hcop _ hl3)
  have hwZ : (l ^ 3) ^ m ∈ Subgroup.center L' := Subgroup.pow_mem _ hl3 m
  let w : L' := (l ^ 3) ^ m
  have hw3 : w ^ 3 = l ^ 3 := by
    change ((l ^ 3) ^ m) ^ 3 = l ^ 3
    rw [← pow_mul, mul_comm, pow_mul, hm]
  let l₃ : L' := l * w⁻¹
  have hwker : w ∈ ψ.ker := by rw [hZ]; exact hwZ
  have hψl₃ : ψ l₃ = ψ l := by
    change ψ (l * w⁻¹) = ψ l
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hwker, inv_one, mul_one]
  have hwc : Commute l w⁻¹ := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hwZ) l
  have hl₃3 : l₃ ^ 3 = 1 := by
    change (l * w⁻¹) ^ 3 = 1
    rw [hwc.mul_pow, inv_pow, hw3, mul_inv_cancel]
  have hfix : ∀ a ∈ A, a l₃ = l₃ := by
    intro a ha
    have h1 : ψ (a l₃) = ψ l₃ := by
      rw [← BstarDesc.descAut_apply hψ hZ a l₃, hψl₃]
      exact hr _ ⟨a, ha, rfl⟩
    let u : L' := a l₃ * l₃⁻¹
    have huZ : u ∈ Subgroup.center L' := by
      rw [← hZ, MonoidHom.mem_ker]
      change ψ (a l₃ * l₃⁻¹) = 1
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hau : a l₃ = u * l₃ := by
      change a l₃ = a l₃ * l₃⁻¹ * l₃
      group
    have hu3 : u ^ 3 = 1 := by
      have ha3 : (a l₃) ^ 3 = 1 := by rw [← map_pow, hl₃3, map_one]
      have huc : Commute u l₃ := (Subgroup.mem_center_iff.mp huZ l₃).symm
      rw [hau, huc.mul_pow, hl₃3, mul_one] at ha3
      exact ha3
    have hu1 : u = 1 := by
      have hd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
      have h1 : orderOf u = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm (hcop u huZ)) hd
      exact orderOf_eq_one_iff.mp h1
    rw [hau, hu1, one_mul]
  refine ⟨MulAut.conj l₃, hA l₃ hfix hl₃3, ?_⟩
  refine MulEquiv.ext fun s => ?_
  obtain ⟨t, rfl⟩ := hψ s
  rw [BstarDesc.descAut_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    hψl₃]

private theorem twE6P_ker_rootMap_le_cent (m : Fin 6) (c : Finset (ExcRaw.Root m)) :
    LinearMap.ker (ExcRaw.rootMap m c) ≤ ExcRaw.cent m c := by
  intro v hv
  simp only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i hi
  have h := congrFun (LinearMap.mem_ker.mp hv) i
  simpa [ExcRaw.rootMap, hi] using h

private theorem twE6P_mem_of_pow_three_mem {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.centralizer (H : Set G)) (hg3 : g ^ 3 ∈ H)
    (hC : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) : g ∈ H := by
  have hcop : Nat.Coprime 3 (orderOf g) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hC (h3.trans (Subgroup.orderOf_dvd_natCard _ hg))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact H.pow_mem hg3 m

private theorem twE6P_frame
    (hMod : ExcTwE6ModelFrame) (hEq : ModelFrameOfEquivCover)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (hperf : commutator H = ⊤)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)) (h5 : 3 ^ 5 ≤ Nat.card E)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    (ψ : ↥H →* ↥(twistedE6RootGroup K σ)) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥H)
    (hφ : ∀ e : ↥E, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l : ↥H, φ (ψ l) = ψ (ggGamma H hEN e l)) :
    Nonempty (ModelFrame H E (excRaw 2)) ∨ Nonempty (ModelFrame H E (excRaw 3)) := by
  classical
  let δ : MulAut ↥H →* MulAut ↥(twistedE6RootGroup K σ) := BstarDesc.descAut hψ hker
  have hδ : ∀ a l, δ a (ψ l) = ψ (a l) := BstarDesc.descAut_apply hψ hker
  have hδinj : Function.Injective δ := BstarDesc.descAut_injective hψ hker hperf
  let γ : ↥E →* MulAut ↥H := ggGamma H hEN
  let ρ : ↥E →* MulAut ↥(twistedE6RootGroup K σ) := δ.comp γ
  let π : ↥H →* MulAut ↥(twistedE6RootGroup K σ) := MulAut.conj.comp ψ
  have hδconj : ∀ h : ↥H, δ (MulAut.conj h) = MulAut.conj (ψ h) := by
    intro h
    refine MulEquiv.ext fun s => ?_
    obtain ⟨t, rfl⟩ := hψ s
    rw [hδ, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hγH : ∀ (e : ↥E) (he : (e : G) ∈ H), γ e = MulAut.conj (⟨e, he⟩ : ↥H) := by
    intro e he
    refine MulEquiv.ext fun l => Subtype.ext ?_
    change ((ggGamma H hEN e l : ↥H) : G) = (e : G) * l * (e : G)⁻¹
    rw [ggGamma_coe]
  have hγinj : Function.Injective γ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hc : (e : G) ∈ Subgroup.centralizer (H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val (DFunLike.congr_fun he ⟨l, hl⟩)
      change ((ggGamma H hEN e ⟨l, hl⟩ : ↥H) : G) = l at h1
      rw [ggGamma_coe] at h1
      calc l * (e : G) = (e : G) * l * (e : G)⁻¹ * e := by rw [h1]
        _ = (e : G) * l := by group
    have hcop : Nat.Coprime 3 (orderOf (e : G)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
        hC3 (h3.trans (Subgroup.orderOf_dvd_natCard _ hc))
    have h3 : orderOf (e : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop.symm (orderOf_dvd_of_pow_eq_one (hEab.2 _ e.2))
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  have hρinj : Function.Injective ρ := hδinj.comp hγinj
  have hcompat : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩ := by
    intro e he
    change δ (γ e) = MulAut.conj (ψ ⟨e, he⟩)
    rw [hγH e he, hδconj]
  have hin : ∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H := by
    rintro e ⟨h, hh⟩
    have hγe : γ e = MulAut.conj h := hδinj (by rw [hδconj]; exact hh.symm)
    have hnorm : (h : G)⁻¹ * e ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer h.2)) (hEN e.2)
    have hcent : (h : G)⁻¹ * e ∈ Subgroup.centralizer (H : Set G) := by
      refine CFSG.mem_centralizer_of_commutator_mem_center ⟨hperf⟩ hnorm fun l hl => ?_
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hγe ⟨l, hl⟩)
      change ((ggGamma H hEN e ⟨l, hl⟩ : ↥H) : G) = (h : G) * l * (h : G)⁻¹ at h1
      rw [ggGamma_coe] at h1
      have h2 : (h : G)⁻¹ * e * l * ((h : G)⁻¹ * e)⁻¹ * l⁻¹ = 1 := by
        calc (h : G)⁻¹ * e * l * ((h : G)⁻¹ * e)⁻¹ * l⁻¹
            = (h : G)⁻¹ * ((e : G) * l * (e : G)⁻¹) * h * l⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [h2]
      exact Subgroup.one_mem _
    have hcomm : Commute (h : G) ((h : G)⁻¹ * e) := Subgroup.mem_centralizer_iff.mp hcent h h.2
    have hcube : ((h : G)⁻¹ * e) ^ 3 ∈ H := by
      have he3 : ((h : G) * ((h : G)⁻¹ * e)) ^ 3 = 1 := by
        rw [mul_inv_cancel_left]
        exact hEab.2 _ e.2
      rw [hcomm.mul_pow] at he3
      rw [eq_inv_of_mul_eq_one_right he3]
      exact H.inv_mem (H.pow_mem h.2 3)
    have hg : (h : G)⁻¹ * e ∈ H := twE6P_mem_of_pow_three_mem hcent hcube hC3
    have : (e : G) = h * ((h : G)⁻¹ * e) := by group
    rw [this]
    exact H.mul_mem h.2 hg
  have hAle : ρ.range ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨φ, hφr, hφl⟩ := hφ e
    have hρe : ρ e = φ := by
      refine MulEquiv.ext fun s => ?_
      obtain ⟨t, rfl⟩ := hψ s
      change δ (γ e) (ψ t) = φ (ψ t)
      rw [hδ, hφl]
    rw [hρe]
    exact hφr
  have hAsc : GGTorusSelfCent 3 ρ.range := by
    have h1 := ggTorusSelfCent_map_descAut hψ hker hZ3 (ggTorusSelfCent_ggGamma hEN hSC)
    rw [MonoidHom.range_comp]
    exact h1
  have hTinj : Function.Injective (RecipeExcLang.twConj K σ) :=
    NoOffTwE6Three.twConj_injective le_rfl (by rw [hK]; norm_num) σ fun c => by rw [hσ]; norm_num
  let eT : ↥(RecipeExcLang.twInndiagGroup K σ) ≃* (RecipeExcLang.twConj K σ).range :=
    MonoidHom.ofInjective hTinj
  let ρ₁ : ↥E →* (RecipeExcLang.twConj K σ).range := ρ.codRestrict _ fun e => hAle ⟨e, rfl⟩
  let ρ' : ↥E →* ModGL TwistTag.E6.tag K :=
    (RecipeExcLang.twInndiagGroup K σ).subtype.comp (eT.symm.toMonoidHom.comp ρ₁)
  let π' : ↥H →* ModGL TwistTag.E6.tag K := (twistedE6RootGroup K σ).subtype.comp ψ
  have hρ'T : ∀ e : ↥E, RecipeExcLang.twConj K σ (eT.symm (ρ₁ e)) = ρ e := fun e => by
    rw [← MonoidHom.ofInjective_apply hTinj]
    change ((eT (eT.symm (ρ₁ e)) : MulAut ↥(twistedE6RootGroup K σ))) = ρ e
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hbr : ∀ (e : ↥E) (c : ↥(twistedE6RootGroup K σ)), ρ' e * (c : ModGL TwistTag.E6.tag K) *
      (ρ' e)⁻¹ = ((ρ e c : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) := by
    intro e c
    rw [← hρ'T e, RecipeExcLang.coe_twConj]
    rfl
  have hconjT : ∀ (c : ↥(twistedE6RootGroup K σ)) (hc : (c : ModGL TwistTag.E6.tag K) ∈
      RecipeExcLang.twInndiagGroup K σ), RecipeExcLang.twConj K σ ⟨c, hc⟩ = MulAut.conj c := by
    intro c hc
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [RecipeExcLang.coe_twConj]
    rfl
  have hπr' : π'.range = twistedE6RootGroup K σ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hπ'ker : π'.ker = Subgroup.center ↥H := by
    rw [← hker]
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change ((ψ h : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) = 1 ↔ ψ h = 1
    exact OneMemClass.coe_eq_one
  have hk3 : ¬ 3 ∣ Nat.card π'.ker := by rw [hπ'ker]; exact hZ3
  have hρ'inj : Function.Injective ρ' := by
    intro a b hab
    apply hρinj
    have h1 : eT.symm (ρ₁ a) = eT.symm (ρ₁ b) := Subtype.ext hab
    have h2 := congrArg (RecipeExcLang.twConj K σ) h1
    rwa [hρ'T, hρ'T] at h2
  have hequiv' : ∀ (e : ↥E) (l : ↥H), π' (ggGamma H hEN e l) = ρ' e * π' l * (ρ' e)⁻¹ := by
    intro e l
    change (((ψ (γ e l)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      ρ' e * ((ψ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * (ρ' e)⁻¹
    rw [hbr]
    exact congrArg Subtype.val (hδ (γ e) l).symm
  have hcompat' : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ' e = π' ⟨e, he⟩ := by
    intro e he
    have hc : ((ψ ⟨e, he⟩ : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) ∈
        RecipeExcLang.twInndiagGroup K σ :=
      RecipeExcLang.graphFixedRootGroup_le_twInndiag σ (ψ ⟨e, he⟩).2
    have h1 : eT.symm (ρ₁ e) = ⟨_, hc⟩ := by
      apply hTinj
      rw [hρ'T, hcompat e he, hconjT]
      rfl
    exact congrArg Subtype.val h1
  have hin' : ∀ e : ↥E, ρ' e ∈ π'.range → (e : G) ∈ H := by
    intro e he
    rw [hπr'] at he
    apply hin e
    obtain ⟨h, hh⟩ := hψ ⟨_, he⟩
    refine ⟨h, ?_⟩
    have hc : ((ψ h : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) ∈
        RecipeExcLang.twInndiagGroup K σ :=
      RecipeExcLang.graphFixedRootGroup_le_twInndiag σ (ψ h).2
    have h1 : eT.symm (ρ₁ e) = ⟨_, hc⟩ := Subtype.ext (congrArg Subtype.val hh).symm
    exact ((hρ'T e).symm.trans ((congrArg (RecipeExcLang.twConj K σ) h1).trans
      (hconjT (ψ h) hc))).symm
  have hA'ab : IsElemAbelian 3 ρ'.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, e₁, rfl⟩ ⟨_, e₂, rfl⟩
      apply Subtype.ext
      change ρ' e₁ * ρ' e₂ = ρ' e₂ * ρ' e₁
      rw [← map_mul, ← map_mul, hEab.1.is_comm.comm e₁ e₂]
    · rintro _ ⟨e, rfl⟩
      have he3 : e ^ 3 = 1 := Subtype.ext (by simpa using hEab.2 _ e.2)
      rw [← map_pow, he3, map_one]
  have hA'le : ρ'.range ≤ RecipeExcLang.twInndiagGroup K σ := by
    rintro _ ⟨e, rfl⟩
    exact (eT.symm (ρ₁ e)).2
  have hA'card : 3 ^ 5 ≤ Nat.card ρ'.range := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρ'inj, Subgroup.card_top]
    exact h5
  have hA'sc : ∀ c ∈ twistedE6RootGroup K σ, (∀ a ∈ ρ'.range, a * c = c * a) → c ^ 3 = 1 →
      c ∈ ρ'.range := by
    intro c hc hca hc3
    have hfix : ∀ a ∈ ρ.range, a ⟨c, hc⟩ = ⟨c, hc⟩ := by
      rintro _ ⟨e, rfl⟩
      apply Subtype.ext
      rw [← hbr]
      calc ρ' e * c * (ρ' e)⁻¹ = c * ρ' e * (ρ' e)⁻¹ := by rw [hca (ρ' e) ⟨e, rfl⟩]
        _ = c := by group
    obtain ⟨e, he⟩ := hAsc ⟨c, hc⟩ hfix (Subtype.ext (by simpa using hc3))
    have hcT : c ∈ RecipeExcLang.twInndiagGroup K σ :=
      RecipeExcLang.graphFixedRootGroup_le_twInndiag σ hc
    have h1 : eT.symm (ρ₁ e) = ⟨c, hcT⟩ := by
      apply hTinj
      rw [hρ'T, he]
      exact (hconjT ⟨c, hc⟩ hcT).symm
    exact ⟨e, congrArg Subtype.val h1⟩
  rcases hMod hK hσ hA'ab hA'le hA'card hA'sc with hmf | hmf
  · rw [← hπr'] at hmf
    obtain ⟨mf, hmfN⟩ := hmf
    exact Or.inl (hEq hEN π' ρ' hπ'ker.le hk3 hperf hEab hρ'inj hequiv' hcompat' hin' mf hmfN)
  · rw [← hπr'] at hmf
    obtain ⟨mf, hmfN⟩ := hmf
    exact Or.inr (hEq hEN π' ρ' hπ'ker.le hk3 hperf hEab hρ'inj hequiv' hcompat' hin' mf hmfN)

theorem excTwE6Placement_of_pieces
    (hCov : ExcTwE6Cover) (hRank : ExcTwE6RankFive) (hMod : ExcTwE6ModelFrame)
    (hEq : ModelFrameOfEquivCover) : ExcTwE6Placement := by
  intro G _ _ B Bs x L D J hS hInn
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hEab, -, -, -⟩ := hcfg.tableB_facts
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  have hC3 := not_dvd_card_centralizer_ggG0_of_stdSub hp3 hThmI.2.2.2.2.2.2.1
    hThmI.2.2.2.2.2.2.2 hS.1.1.2.2
  obtain ⟨hEN, hperf, K, _, _, σ, hK, hσ, ψ, hψ, hker, hφ⟩ := hCov hInn
  rcases twE6P_frame hMod hEq hEN hperf hEab hcfg.2.1.2.2.2 hC3 (not_three_dvd_card_center_ggG0 hS)
      (hRank hS hInn) hK hσ ψ hψ hker hφ with hmf | hmf
  · obtain ⟨mf⟩ := hmf
    exact Or.inl ⟨Realization.ofModelFrame mf hInn fun c _ => twE6P_ker_rootMap_le_cent 2 c⟩
  · obtain ⟨mf⟩ := hmf
    exact Or.inr ⟨Realization.ofModelFrame mf hInn fun c _ => twE6P_ker_rootMap_le_cent 3 c⟩

end CFSG.StandardType.GGQ2Frame.ExcPlacement
