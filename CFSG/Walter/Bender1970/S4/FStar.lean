module

public import CFSG.Walter.Bender1970.S4.Tools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedFittingSubgroupConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
public import CFSG.Walter.Bender1970.S3.CoreExchangeRank
public import CFSG.Walter.Bender1970.S38.Basic
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.AmbientSylowZJNormalizer

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.Glauberman

variable {G : Type} [Group G] [Finite G]

namespace Bender41

theorem false_of_not_isPGroup
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpt : ⁅Subgroup.zpowers t, qCoreOf H p⁆ ≠ ⊥)
    (hF : ¬ IsPGroup p (generalizedFittingSubgroupOf H)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have := hG.isSimpleGroup
  obtain ⟨R, hRT, hRr, V, hVP, hV1, hVR, -, hVA, hVtt⟩ :=
    hG.exists_hyperplane_mem_benderABar ht hH T htT hp hp2 hpt
  set P := qCoreOf H p with hPdef
  have hHco := isCoatom_of_mem_benderM hH
  have hP1 : P ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVP))
  have hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) := by
    by_contra hlt
    push Not at hlt
    have hpπ := mem_primesOfOrder_of_qCoreOf_ne_bot hp hP1
    have hfin : (primesOfOrder (generalizedFittingSubgroupOf H)).Finite :=
      (Nat.card (generalizedFittingSubgroupOf H)).primeFactors.finite_toSet
    have hsub : primesOfOrder (generalizedFittingSubgroupOf H) ⊆ {p} := by
      intro r hr
      rw [Nat.card_coe_set_eq] at hlt
      exact Set.mem_singleton_iff.mpr ((Set.ncard_le_one hfin).mp (by omega) r hr p hpπ)
    exact hF (isPGroup_of_primesOfOrder_subset hp hsub)
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    (Subgroup.centralizer_le_normalizer _).trans (hVA.2.2.1 hπ)
  have habc : Bender39Conditions t H T V p := Or.inl ⟨hCV, hVtt⟩
  have key : ∀ s ∈ R, orderOf s = 2 → ∀ M ∈ benderM s, M ≠ H →
      rank P = 1 ∧ 1 < rank (qCoreOf M p) := by
    intro s hsR hs M hM hMH
    have hVs : V ≤ Subgroup.centralizer ({s} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp (hVR hv)) s hsR).symm
    exact (bender1970_3_9 hG ht hH T htT hp hp2 hVP hs (hRT hsR) hM hMH hπ
      (hVs.trans (centralizer_le_of_mem_benderM hM)) habc).2.2 hVs
  obtain ⟨s₀, hs₀R, hs₀, hs₀H⟩ := bender1970_3_3 hG ht hH T htT hRT hRr
  obtain ⟨M₀, hM₀, hM₀H⟩ := hG.exists_mem_benderM_ne hs₀ hs₀H
  have hrP : rank P = 1 := (key s₀ hs₀R hs₀ M₀ hM₀ hM₀H).1
  have hPcyc : IsCyclic P := isCyclic_of_rank_le_one hp hp2 (qCoreOf_isPGroup H p) hrP.le
  obtain ⟨n, -, hnR⟩ := bender1970_1_3 hG.nonabelian T (hG.hasAbelianSylowTwo T) hRT hRr htT ht
  set s := n * t * n⁻¹ with hsdef
  have hs : orderOf s = 2 := by rw [hsdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hM : H.map (MulAut.conj n).toMonoidHom ∈ benderM s := map_conj_mem_benderM n hH
  by_cases hMH : H.map (MulAut.conj n).toMonoidHom = H
  ·
    have hnH : n ∈ H := hG.mem_of_map_conj_eq hHco hMH
    set V' := V.map (MulAut.conj n⁻¹).toMonoidHom with hV'def
    have hV'P : V' ≤ P := by
      rintro _ ⟨v, hv, rfl⟩
      exact (qCoreOf_normal_in H p).2 _ (H.inv_mem hnH) _ (hVP hv)
    have hV'V : V' = V := by
      have hcard : Nat.card V' = Nat.card V :=
        Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective
      have h := (IsCyclic.subgroup_eq_iff_card_eq (H := V'.subgroupOf P)
        (K := V.subgroupOf P)).mpr
        (by rw [natCard_subgroupOf_of_le hV'P, natCard_subgroupOf_of_le hVP, hcard])
      have h' := congrArg (Subgroup.map P.subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hV'P, Subgroup.map_subgroupOf_eq_of_le hVP] at h'
    have htV : V ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [← hV'V]
      rintro _ ⟨v, hv, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hsv : s * v = v * s := (Subgroup.mem_centralizer_iff.mp (hVR hv)) s hnR
      change (MulAut.conj n⁻¹) v * t = t * (MulAut.conj n⁻¹) v
      rw [MulAut.conj_apply, inv_inv]
      calc n⁻¹ * v * n * t = n⁻¹ * (v * s) * n := by rw [hsdef]; group
        _ = n⁻¹ * (s * v) * n := by rw [hsv]
        _ = t * (n⁻¹ * v * n) := by rw [hsdef]; group
    apply hV1
    rw [← hVtt, Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq']
    exact htV
  ·
    have h := (key s hnR hs _ hM hMH).2
    have hQ : qCoreOf (H.map (MulAut.conj n).toMonoidHom) p = P.map (MulAut.conj n).toMonoidHom :=
      qCoreOf_conjugateSubgroup H n p
    rw [hQ, rank_map_conj, hrP] at h
    exact lt_irrefl _ h

theorem mem_normalizer_generalizedFittingSubgroupOf {C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer (generalizedFittingSubgroupOf C : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer] at hg ⊢
  rw [← generalizedFittingSubgroupOf_conjugateSubgroup]
  change generalizedFittingSubgroupOf (C.map (MulAut.conj g).toMonoidHom) = _
  rw [hg]

theorem false_of_isPGroup
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpt : ⁅Subgroup.zpowers t, qCoreOf H p⁆ ≠ ⊥)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hG.isSimpleGroup
  obtain ⟨R, hRT, hRr, V, hVP, hV1, hVR, -, hVA, -⟩ :=
    hG.exists_hyperplane_mem_benderABar ht hH T htT hp hp2 hpt
  have hHco := isCoatom_of_mem_benderM hH
  have hH1 : H ≠ ⊥ := fun h => hG.bot_not_isCoatom (h ▸ hHco)
  have hInv := qd_not_involved_of_hasAbelianSylowTwo hG.hasAbelianSylowTwo hp2
  have hFM : ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s,
      IsPGroup p (generalizedFittingSubgroupOf M) :=
    fun s hs M hM => bender1970_3_6 hG ht hH hp hp2 hF hs hM
  have hπ : Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) = 1 := by
    rw [primesOfOrder_generalizedFitting_eq_singleton hp hF hH1]
    simp
  have hCV : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (V : Set G))) := by
    have h := hVA.2.2.2 hπ
    rw [primesOfOrder_generalizedFitting_eq_singleton hp hF hH1] at h
    exact isPGroup_of_primesOfOrder_subset hp h.le
  have hVp : IsPGroup p V := (qCoreOf_isPGroup H p).to_le hVP
  have hVH : V ≤ H := hVP.trans (qCoreOf_normal_in H p).1
  obtain ⟨s₀, hs₀R, hs₀, hs₀H⟩ := bender1970_3_3 hG ht hH T htT hRT hRr
  obtain ⟨M₀, hM₀, hM₀H⟩ := hG.exists_mem_benderM_ne hs₀ hs₀H
  have hVM₀ : V ≤ M₀ := by
    refine le_trans ?_ (centralizer_le_of_mem_benderM hM₀)
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hVR hv)) s₀ hs₀R).symm
  set 𝒰 : Set (Subgroup G) := {U | V ≤ U ∧ U ≤ H ∧ IsPGroup p U ∧
    ∃ s : G, orderOf s = 2 ∧ ∃ X ∈ benderM s, X ≠ H ∧ U ≤ X} with h𝒰
  have hV𝒰 : V ∈ 𝒰 := ⟨le_rfl, hVH, hVp, s₀, hs₀, M₀, hM₀, hM₀H, hVM₀⟩
  obtain ⟨U, hU𝒰, hUmax⟩ :=
    Set.exists_max_image 𝒰 (fun U => Nat.card U) (Set.toFinite _) ⟨V, hV𝒰⟩
  obtain ⟨hVU, hUH, hUp, s₁, hs₁, X₀, hX₀, hX₀H, hUX₀⟩ := hU𝒰
  have hU1 : U ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVU))
  have hSyl : ∀ W ∈ 𝒰, p * Nat.card W ∣ Nat.card G := by
    rintro W ⟨hVW, hWH, hWp, s, hs, X, hX, hXH, hWX⟩
    by_contra hcon
    have hW1 : W ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVW))
    have hnd : ∀ Y : Subgroup G, ¬ p * Nat.card W ∣ Nat.card Y := fun Y h =>
      hcon (h.trans (Subgroup.card_subgroup_dvd_card Y))
    have h1 := (hG.normalizer_zj_eq hHco hp hp2 hF hWH hWp hW1 (hnd H)).2
    have h2 := (hG.normalizer_zj_eq (isCoatom_of_mem_benderM hX) hp hp2 (hFM s hs X hX) hWX hWp
      hW1 (hnd X)).2
    exact hXH (h2.symm.trans h1)
  have hNU : ¬ Subgroup.normalizer (U : Set G) ≤ H := by
    intro hNH
    have hdvd : p * Nat.card U ∣ Nat.card X₀ := by
      by_contra hcon
      exact (hG.normalizer_zj_eq (isCoatom_of_mem_benderM hX₀) hp hp2 (hFM s₁ hs₁ X₀ hX₀) hUX₀
        hUp hU1 hcon).1 (hSyl U ⟨hVU, hUH, hUp, s₁, hs₁, X₀, hX₀, hX₀H, hUX₀⟩)
    obtain ⟨U₁, hUU₁, hU₁X₀, hU₁N, hU₁p, hU₁card⟩ :=
      exists_le_normalizer_card_eq_mul hp hUX₀ hUp hdvd
    have h := hUmax U₁ ⟨hVU.trans hUU₁, hU₁N.trans hNH, hU₁p, s₁, hs₁, X₀, hX₀, hX₀H, hU₁X₀⟩
    rw [hU₁card] at h
    have hpos := Nat.card_pos (α := U)
    nlinarith [hp.two_le]
  obtain ⟨PB⟩ : Nonempty (Sylow p H) := inferInstance
  have hpH : p ∣ Nat.card H := by
    have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV1
    obtain ⟨k, hk, hcard⟩ := (IsPGroup.nontrivial_iff_card hVp).mp inferInstance
    exact (hcard ▸ dvd_pow_self p hk.ne').trans (Subgroup.card_dvd_of_le hVH)
  obtain ⟨PGH, hPGH, -⟩ := exists_ambient_sylow_with_zj_normalizer_eq_of_fstar_pgroup hp2
    hG.isSimpleGroup hInv H hHco hF PB (PB.ne_bot_of_dvd_card hpH)
  have hPGHH : (PGH : Subgroup G) ≤ H := by
    rw [hPGH]
    exact Subgroup.map_subtype_le _
  set 𝒮 : Set (Subgroup G) :=
    {S | U ≤ S ∧ S ≤ H ⊓ Subgroup.normalizer (U : Set G) ∧ IsPGroup p S} with h𝒮
  obtain ⟨S₀, ⟨hUS₀, hS₀HN, hS₀p⟩, hS₀max⟩ := Set.exists_max_image 𝒮 (fun S => Nat.card S)
    (Set.toFinite _) ⟨U, le_rfl, le_inf hUH Subgroup.le_normalizer, hUp⟩
  have hζ : ∀ Y : Subgroup G, S₀ ≤ Y → IsPGroup p Y → Y ≤ H := by
    intro Y hS₀Y hYp
    obtain ⟨PG, hYPG⟩ := hYp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PGH PG
    have hPG : (PG : Subgroup G) = (PGH : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, sylow_smul_subgroup_eq_map_conj]
    have hYHg : Y ≤ H.map (MulAut.conj g).toMonoidHom :=
      hYPG.trans (hPG ▸ Subgroup.map_mono hPGHH)
    by_cases hHg : H.map (MulAut.conj g).toMonoidHom = H
    · exact hHg ▸ hYHg
    exfalso
    have hgt : orderOf (g * t * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
    have hS₀𝒰 : S₀ ∈ 𝒰 := ⟨hVU.trans hUS₀, hS₀HN.trans inf_le_left, hS₀p, g * t * g⁻¹, hgt,
      _, map_conj_mem_benderM g hH, hHg, hS₀Y.trans hYHg⟩
    have hS₀U : U = S₀ := Subgroup.eq_of_le_of_card_ge hUS₀ (hUmax S₀ hS₀𝒰)
    have hndH : ¬ p * Nat.card U ∣ Nat.card H := by
      intro hdvd
      obtain ⟨U₁, hUU₁, hU₁H, hU₁N, hU₁p, hU₁card⟩ :=
        exists_le_normalizer_card_eq_mul hp hUH hUp hdvd
      have h := hS₀max U₁ ⟨hUU₁, le_inf hU₁H hU₁N, hU₁p⟩
      rw [hU₁card, ← hS₀U] at h
      have hpos := Nat.card_pos (α := U)
      nlinarith [hp.two_le]
    exact (hG.normalizer_zj_eq hHco hp hp2 hF hUH hUp hU1 hndH).1
      (hSyl U ⟨hVU, hUH, hUp, s₁, hs₁, X₀, hX₀, hX₀H, hUX₀⟩)
  set NU := Subgroup.normalizer (U : Set G) with hNUdef
  obtain ⟨x, hxN, hxH⟩ := Set.not_subset.mp hNU
  have hxN' : x ∈ NU := hxN
  set O := qCoreOf NU p with hOdef
  have hOp : IsPGroup p O := qCoreOf_isPGroup NU p
  have hOn := qCoreOf_normal_in NU p
  have hUO : U ≤ O :=
    le_qCoreOf_of_normal_isPGroup NU U p Subgroup.le_normalizer Subgroup.normal_in_normalizer hUp
  have hS₀O : S₀ ≤ Subgroup.normalizer (O : Set G) :=
    (hS₀HN.trans inf_le_right).trans (le_normalizer_of_isNormalIn hOn)
  have hOH : O ≤ H := le_sup_right.trans (hζ _ le_sup_left (hS₀p.to_sup_of_normal_right' hOp hS₀O))
  have hxt : orderOf (x * t * x⁻¹) = 2 := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hHx : H.map (MulAut.conj x).toMonoidHom ≠ H := fun h => hxH (hG.mem_of_map_conj_eq hHco h)
  have hOHx : O ≤ H.map (MulAut.conj x).toMonoidHom := by
    intro o ho
    refine ⟨x⁻¹ * o * x, ?_, ?_⟩
    · have := hOn.2 x⁻¹ (NU.inv_mem hxN') o ho
      rw [inv_inv] at this
      exact hOH this
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hOU : U = O := Subgroup.eq_of_le_of_card_ge hUO
    (hUmax O ⟨hVU.trans hUO, hOH, hOp, x * t * x⁻¹, hxt, _, map_conj_mem_benderM x hH, hHx, hOHx⟩)
  set C := Subgroup.centralizer (U : Set G) with hCdef
  have hFC : IsPGroup p (generalizedFittingSubgroupOf C) :=
    bender1970_1_9_centralizer_pGroup p hp hVU hUp hVp hCV
  have hFCC : generalizedFittingSubgroupOf C ≤ C := generalizedFittingSubgroupOf_le C
  have hCNU : C ≤ NU := Subgroup.centralizer_le_normalizer _
  have hFCN : NU ≤ Subgroup.normalizer (generalizedFittingSubgroupOf C : Set G) := fun g hg =>
    mem_normalizer_generalizedFittingSubgroupOf (Bender35.mem_normalizer_centralizer hg)
  have hFCU : generalizedFittingSubgroupOf C ≤ U := by
    rw [hOU]
    exact le_qCoreOf_of_normal_isPGroup NU _ p (hFCC.trans hCNU)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hFCC.trans hCNU)).mpr hFCN) hFC
  have hCU : C ≤ U := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer (generalizedFittingSubgroupOf C : Set G) :=
      Subgroup.centralizer_le hFCU hc
    exact hFCU (Bender35.inf_centralizer_le_generalizedFitting C ⟨hc, hc'⟩)
  obtain ⟨PG, hS₀PG⟩ := hS₀p.exists_le_sylow
  have hPGH : (PG : Subgroup G) ≤ H := hζ _ hS₀PG PG.isPGroup'
  have hPG1 : (PG : Subgroup G) ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUS₀.trans hS₀PG))
  have hndPG : ¬ p * Nat.card PG ∣ Nat.card H := by
    intro hdvd
    rw [PG.card_eq_multiplicity, ← pow_succ'] at hdvd
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp
      (hdvd.trans (Subgroup.card_subgroup_dvd_card H))
  have hNZ := (hG.normalizer_zj_eq hHco hp hp2 hF hPGH PG.isPGroup' hPG1 hndPG).2
  have hUPG : (U : Set G) ⊆ (PG : Subgroup G) := fun u hu => hS₀PG (hUS₀ hu)
  have hxU : conjSubset x (U : Set G) ⊆ (PG : Subgroup G) := by
    rintro _ ⟨u, hu, rfl⟩
    apply hUPG
    have := (Subgroup.mem_normalizer_iff.mp (NU.inv_mem hxN') u).mp hu
    rwa [inv_inv] at this
  obtain ⟨c, n, hcU, hnZ, hxcn⟩ :=
    Glauberman.theoremB hp2 PG hInv (U : Set G) ⟨1, U.one_mem⟩ hUPG x hxU
  have hcH : c ∈ H := hUH (hCU hcU)
  have hnH : n ∈ H := by rwa [hNZ] at hnZ
  exact hxH (hxcn ▸ H.mul_mem hcH hnH)

end Bender41

theorem BenderCounterexample.qCoreOf_le_centralizer_of_mem_benderM
    (hG : BenderCounterexample G)
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : qCoreOf H p ≤ Subgroup.centralizer ({t} : Set G) := by
  by_contra hcon
  have hpt : ⁅Subgroup.zpowers t, qCoreOf H p⁆ ≠ ⊥ := by
    intro h
    apply hcon
    rw [commutator_zpowers_eq_bot_iff] at h
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h x hx
  obtain ⟨T, htT⟩ := exists_sylow_two_mem ht
  by_cases hF : IsPGroup p (generalizedFittingSubgroupOf H)
  · exact Bender41.false_of_isPGroup hG ht hH T htT hp hp2 hpt hF
  · exact Bender41.false_of_not_isPGroup hG ht hH T htT hp hp2 hpt hF

theorem bender1970_4_1
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) : t ∈ generalizedFittingSubgroupOf H :=
  mem_generalizedFittingSubgroupOf_of_le_centralizer
    (hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hH)).1 (mem_of_mem_benderM hH) ht
    fun _ hp hp2 => hG.qCoreOf_le_centralizer_of_mem_benderM ht hH hp hp2

end CFSG.Walter
