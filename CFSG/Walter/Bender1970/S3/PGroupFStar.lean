module

public import CFSG.Walter.Bender1970.S3.PCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedFittingSubgroupConjugate

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_generalizedFitting_of_le_qCoreOf {M U : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hUO : U ≤ qCoreOf M p) (hCM : Subgroup.centralizer (U : Set G) ≤ M)
    (hC : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G)))) :
    IsPGroup p (generalizedFittingSubgroupOf M) := by
  set C := Subgroup.centralizer (U : Set G) with hCdef
  have hCO : Subgroup.centralizer (qCoreOf M p : Set G) ≤ C := Subgroup.centralizer_le hUO
  refine isPGroup_generalizedFitting_of_qCoreOf_eq_bot (fun q hq hqp => ?_) ?_
  · by_contra hne
    have hOC : qCoreOf M q ≤ C := (qCoreOf_centralizer_of_ne M hp hq (Ne.symm hqp)).trans hCO
    have hOn : IsNormalIn (qCoreOf M q) C :=
      ⟨hOC, fun y hy x hx => (qCoreOf_normal_in M q).2 y (hCM hy) x hx⟩
    have : Fact q.Prime := ⟨hq⟩
    have hOF : qCoreOf M q ≤ generalizedFittingSubgroupOf C :=
      (le_fittingSubgroupOf_of_isNormalIn_nilpotent hOC hOn
        (qCoreOf_isPGroup M q).isNilpotent).trans le_sup_left
    exact hqp (eq_of_isPGroup_of_isPGroup hq hp (qCoreOf_isPGroup M q) (hC.to_le hOF) hne)
  · refine eq_bot_iff.mpr (sSup_le fun K hK => ?_)
    exfalso
    have hKC : K ≤ C := ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (component_centralizes_fittingSubgroupOf hK)).trans
        (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf M p hp))).trans hCO
    have hKc : IsComponentOf K C := ⟨hKC, isSubnormal_subgroupOf_of_le hKC hCM hK.2.1, hK.2.2⟩
    have hKF : K ≤ generalizedFittingSubgroupOf C :=
      (le_sSup (s := {E : Subgroup G | IsComponentOf E C}) hKc).trans le_sup_right
    have : Fact p.Prime := ⟨hp⟩
    exact not_isNilpotent_of_isQuasisimple K hK.2.2 (hC.to_le hKF).isNilpotent

theorem isPGroup_generalizedFitting_map_conj {M : Subgroup G} {p : ℕ} (g : G)
    (h : IsPGroup p (generalizedFittingSubgroupOf M)) :
    IsPGroup p (generalizedFittingSubgroupOf (M.map (MulAut.conj g).toMonoidHom)) := by
  have he := generalizedFittingSubgroupOf_conjugateSubgroup M g
  change IsPGroup p (generalizedFittingSubgroupOf (conjugateSubgroup M g))
  rw [he]
  exact h.map _

theorem exists_conj_mem_sylow (T : Sylow 2 G) {s : G} (hs : orderOf s = 2) :
    ∃ g : G, g * s * g⁻¹ ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q T
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
  exact ⟨s, hQ (Subgroup.mem_zpowers s), by simp⟩

theorem bender1970_3_6_of_exists
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H))
    (h35 : ∃ Pbar ≤ qCoreOf H p, Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer (Pbar : Set G) ∧ ⁅Subgroup.zpowers t, Pbar⁆ ≠ ⊥ ∧
        ∀ V ≤ Pbar, V ≠ ⊥ → t ∈ Subgroup.normalizer (V : Set G) → V ∈ benderABar H)
    {s : G} (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s) :
    IsPGroup p (generalizedFittingSubgroupOf M) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hG.isSimpleGroup
  obtain ⟨Pbar, hPbarP, hPbarC, hPbart, hPbarA⟩ := h35
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨T, htT⟩ : ∃ T : Sylow 2 G, t ∈ (T : Subgroup G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp' : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    obtain ⟨T, hT⟩ := hp'.exists_le_sylow
    exact ⟨T, hT (Subgroup.mem_zpowers t)⟩
  have hTab := hG.hasAbelianSylowTwo T
  have hTC := hG.sylow_le_centralizer T htT
  have hPbarodd : Odd (Nat.card Pbar) := by
    obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le hPbarP).exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hPbart' : ⁅Subgroup.zpowers t, Pbar⁆ ≠ ⊥ := hPbart
  obtain ⟨R, hRT, hRr, hRt⟩ := bender1970_3_4 T hTab htT ht (hTC.trans hPbarC) hPbarodd hPbart'
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set D := Pbar ⊓ Subgroup.centralizer (R : Set G) with hDdef
  set V := ⁅D, Subgroup.zpowers t⁆ with hVdef
  have htR : t ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hcommT r (hRT hr) t htT
  have htD : t ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_inf (hPbarC htC) (Subgroup.le_normalizer htR)
  have hVD : V ≤ D := commutator_zpowers_le_of_mem_normalizer htD
  have hV1 : V ≠ ⊥ := by
    rw [hVdef, Subgroup.commutator_comm]
    exact hRt
  have hVt : t ∈ Subgroup.normalizer (V : Set G) :=
    mem_normalizer_commutator htD (Subgroup.le_normalizer (Subgroup.mem_zpowers t))
  have hVA : V ∈ benderABar H := hPbarA V (hVD.trans inf_le_left) hV1 hVt
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card D) := by
    obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le (inf_le_left.trans hPbarP)).exists_card_eq
    rw [Nat.card_zpowers, ht, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hVtt : ⁅V, Subgroup.zpowers t⁆ = V :=
    le_antisymm (commutator_zpowers_le_of_mem_normalizer hVt)
      (commutator_le_commutator_commutator D _ (Subgroup.zpowers_le.mpr htD) hcop)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow T hs
  have hgs : orderOf (g * s * g⁻¹) = 2 := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
  obtain ⟨n, -, hnR⟩ := bender1970_1_3 hG.nonabelian T hTab hRT hRr hg hgs
  set x := n * g with hx
  have hxs : x * s * x⁻¹ = n * (g * s * g⁻¹) * n⁻¹ := by rw [hx]; group
  set s' := x * s * x⁻¹ with hs'def
  have hs'R : s' ∈ R := hxs ▸ hnR
  have hs' : orderOf s' = 2 := by rw [hs'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
  set M' := M.map (MulAut.conj x).toMonoidHom with hM'def
  have hM' : M' ∈ benderM s' := map_conj_mem_benderM x hM
  suffices hsuff : IsPGroup p (generalizedFittingSubgroupOf M') by
    have h := isPGroup_generalizedFitting_map_conj x⁻¹ hsuff
    rwa [hM'def, map_conj_map_conj_inv] at h
  have hM'co := isCoatom_of_mem_benderM hM'
  have hM'A : IsAStar M' := hG.isAStar_of_isCoatom hM'co
  have hVs : V ≤ Subgroup.centralizer ({s'} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hVD hv).2 s' hs'R).symm
  have hCM' := centralizer_le_of_mem_benderM hM'
  have hVM : V ≤ M' := hVs.trans hCM'
  have htM : t ∈ M' := hCM' (Subgroup.mem_centralizer_singleton_iff.mpr
    (hcommT t htT s' (hRT hs'R)))
  set P₀ := Pbar ⊓ M' with hP₀def
  have hP₀ : IsPGroup p P₀ := (qCoreOf_isPGroup H p).to_le (inf_le_left.trans hPbarP)
  have hCP₀ : M' ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    fun c hc => mem_normalizer_inf (hPbarC hc.2) (Subgroup.le_normalizer hc.1)
  have h24 := bender1970_2_4_pGroup_subgroup hM'A htM ht hp hp2 inf_le_right hP₀ hCP₀
  have hVO : V ≤ qCoreOf M' p :=
    hVtt ▸ (Subgroup.commutator_mono (le_inf (hVD.trans inf_le_left) hVM) le_rfl).trans h24
  set PM := qCoreOf M' p with hPMdef
  set U := PM ⊓ Subgroup.normalizer (V : Set G) with hUdef
  have hVU : V ≤ U := le_inf hVO Subgroup.le_normalizer
  have hUp : IsPGroup p U := (qCoreOf_isPGroup M' p).to_le inf_le_left
  have hH1 : H ≠ ⊥ := fun h => hG.bot_not_isCoatom (h ▸ isCoatom_of_mem_benderM hH)
  have hπ : Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) = 1 := by
    rw [primesOfOrder_generalizedFitting_eq_singleton hp hF hH1]
    simp
  have hCV : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (V : Set G))) := by
    have h := hVA.2.2.2 hπ
    rw [primesOfOrder_generalizedFitting_eq_singleton hp hF hH1] at h
    exact isPGroup_of_primesOfOrder_subset hp h.le
  have hCU := bender1970_1_9_centralizer_pGroup p hp hVU hUp (hUp.to_le hVU) hCV
  set Z := (Subgroup.center PM).map PM.subtype with hZdef
  have hZn : IsNormalIn Z M' :=
    map_characteristic_isNormalIn_of_isNormalIn _ inferInstance (qCoreOf_normal_in M' p)
  have hPM1 : PM ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVO))
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial PM := (Subgroup.nontrivial_iff_ne_bot PM).mpr hPM1
    have := (qCoreOf_isPGroup M' p).center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center PM)
    intro h
    have hzZ : ((z : PM) : G) ∈ Z := ⟨z, z.2, rfl⟩
    rw [h, Subgroup.mem_bot] at hzZ
    exact hz (Subtype.ext (Subtype.ext hzZ))
  have hZU : Z ≤ U := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.centralizer_le_normalizer _ ?_⟩
    show (z : G) ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨w, hVO hw⟩)
  have hNZ := hG.normalizer_eq_of_isNormalIn hM'co hZn hZ1
  have hCM : Subgroup.centralizer (U : Set G) ≤ M' :=
    (Subgroup.centralizer_le hZU).trans ((Subgroup.centralizer_le_normalizer _).trans hNZ.le)
  exact isPGroup_generalizedFitting_of_le_qCoreOf hp inf_le_left hCM hCU

theorem bender1970_3_6
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H)) {s : G} (hs : orderOf s = 2)
    {M : Subgroup G} (hM : M ∈ benderM s) : IsPGroup p (generalizedFittingSubgroupOf M) := by
  have : Fact p.Prime := ⟨hp⟩
  refine bender1970_3_6_of_exists hG ht hH hp hp2 hF (bender1970_3_5 hG ht hH hp ?_) hs hM
  intro h
  have htH : t ∈ H := mem_of_mem_benderM hH
  have hFH := generalizedFittingSubgroupOf_isNormalIn H
  have hFP : generalizedFittingSubgroupOf H ≤ qCoreOf H p :=
    le_qCoreOf_of_normal_isPGroup H _ p hFH.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hFH.1).mpr (le_normalizer_of_isNormalIn hFH))
      hF
  rw [commutator_zpowers_eq_bot_iff] at h
  have htC : t ∈ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h x (hFP hx)
  have htF : t ∈ generalizedFittingSubgroupOf H :=
    Bender35.inf_centralizer_le_generalizedFitting H ⟨htH, htC⟩
  have hto : Odd (orderOf t) := by
    obtain ⟨k, hk⟩ := hF.exists_card_eq
    have h1 := Subgroup.orderOf_dvd_natCard _ htF
    rw [hk] at h1
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2).pow h1
  rw [ht] at hto
  exact absurd hto (by decide)

end CFSG.Walter
