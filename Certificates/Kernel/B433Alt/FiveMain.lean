module

public import Certificates.Kernel.B433Alt.FiveNode
public import Certificates.Kernel.B433Alt.FixMain
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentA2

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CertificateChecks.KernelY442 CFSG.KC.B433Alt CFSG.Certificates.TwDce CFSG.YGroups.SymGen
  CFSG.YGroups.DCE.B433 CFSG.HardMathSupport.Dickson.I271.TabBFiveCent CFSG.KD.B4AF
  CFSG.HardMathSupport.Dickson.I271.TabBFiveCentNative CFSG.YGroups.DCE

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem five_cover_data : (∀ k < 17, FJ.getD k 0 < 64 ∧ liveB (FJ.getD k 0) = true ∧
      CFSG.KD.B4AT.PA.getD (FJ.getD k 0) 0 = 0 ∧ FJ.getD k 0 ≠ 0 ∧
      ¬ 5 ^ (FA.getD k 0 + 1) ∣ CFSG.KD.B4AC.MJ (FJ.getD k 0)) ∧
    (∀ j < 64, liveB j = true → CFSG.KD.B4AT.PA.getD j 0 = 0 → j ≠ 0 → j ∉ FJ →
      CFSG.KD.B4AC.MJ j % 5 ≠ 0) ∧ FJ.Nodup := by
  decide +kernel

theorem five_sum : ∑ k ∈ Finset.range 17,
    CFSG.KD.B4AC.MJ (FJ.getD k 0) / FB.getD k 0 * (5 ^ FA.getD k 0 - 1) *
      (4089470473293004800 / CFSG.KD.B4AC.MJ (FJ.getD k 0)) ≤ 4089470473293004800 := by
  decide +kernel

theorem comm_iff_ker {A B : Type*} [Group A] [Group B] (f : A →* B) (a b : A) :
    f a * f b = f b * f a ↔ a * b * a⁻¹ * b⁻¹ ∈ f.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc f a * f b = f a * f b * (f a)⁻¹ * (f b)⁻¹ * (f b * f a) := by group
      _ = f b * f a := by rw [h, one_mul]

theorem ncard_five_eq_zero {K : Subgroup (Equiv.Perm (Fin 31671))} (hK : Nat.card K % 5 ≠ 0) :
    {σ : Equiv.Perm (Fin 31671) | σ ∈ K ∧ orderOf σ = 5}.ncard = 0 := by
  have h : {σ : Equiv.Perm (Fin 31671) | σ ∈ K ∧ orderOf σ = 5} = ∅ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hσ ho
    have hd : orderOf (⟨σ, hσ⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ho] at hd
    exact hK (Nat.mod_eq_zero_of_dvd hd)
  rw [h, Set.ncard_empty]

section

theorem card_centralizer_dFive
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    orderOf (psi dFive) = 5 ∧ 7 ∣ Nat.card (Subgroup.centralizer {psi dFive}) ∧
      Nat.card (Subgroup.centralizer {psi dFive}) ≤ 635065200 := by
  classical
  have hfinB : Finite B433 := (B433_finite_card_le).1
  have hfinG := finite_Ghat
  have hfinY := finite_y432
  obtain ⟨hC2, hs5, e7, he7, he7c⟩ := card_centralizer_rho_dFive_le
  obtain ⟨hex2, hHeq, hex3⟩ := exact hG
  have hker := ker_psi hG
  have hpsiF := card_psi_range hG
  have hinl : Function.Injective (inlB : B433 →* Ghat hsw) := inlB_injective
  have hkerG : (psiG hsw).ker = rho432F.ker := by
    rw [← hker]
    ext e
    simp only [MonoidHom.mem_ker, psiG, MonoidHom.comp_apply]
    exact ⟨fun h => hinl (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
  have hpre : ∀ i : Fin 46, i ∈ Ev → ∃ y : B433, (inlB : B433 →* Ghat hsw) y = (twist).x i :=
    fun i hi => (x_mem_inl_iff i).2 hi
  choose! yB hyB using hpre
  have hmemS : ∀ i ∈ Ev, ∀ e : YGroup 4 3 2,
      e ∈ CFSG.YGroups.DCE.B.stabSub setupB (yB i) ↔
        (twist).x i * psiG hsw e * ((twist).x i)⁻¹ ∈ Hh hsw := by
    intro i hi e
    rw [CFSG.YGroups.DCE.B.mem_stabSub, ← hyB i hi]
    change yB i * psi e * (yB i)⁻¹ ∈ psi.range ↔ inlB (yB i) * inlB (psi e) * (inlB (yB i))⁻¹ ∈ _
    rw [← map_inv, ← map_mul, ← map_mul]
    constructor
    · rintro ⟨e', he'⟩
      exact ⟨e', by rw [← he']; rfl⟩
    · rintro ⟨e', he'⟩
      exact ⟨e', hinl he'⟩
  have hkerS : ∀ i ∈ Ev, (psiG hsw).ker ≤ CFSG.YGroups.DCE.B.stabSub setupB (yB i) := by
    intro i hi e he
    rw [hmemS i hi, MonoidHom.mem_ker.1 he, mul_one, mul_inv_cancel]
    exact (Hh hsw).one_mem
  have hSeq : ∀ i ∈ Ev, (twist).S i = (CFSG.YGroups.DCE.B.stabSub setupB (yB i)).map (psiG hsw) ∧
      (CFSG.YGroups.DCE.B.stabSub setupB (yB i)).index = vN i := by
    intro i hi
    set P := CFSG.YGroups.DCE.B.stabSub setupB (yB i)
    have hle : (twist).S i ≤ P.map (psiG hsw) := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y, (hmemS i hi y).2 ((twist).S_conj i _ ⟨y, hy, rfl⟩), rfl⟩
    have hidx : (P.map (psiG hsw)).relIndex (Hh hsw) = P.index :=
      relIndex_map_eq_index (psiG hsw) P (hkerS i hi)
    have hDS : ((twist).S i).relIndex (Hh hsw) = vN i := relIndex_eq hG hi
    have hmono : (P.map (psiG hsw)).relIndex (Hh hsw) ≤ ((twist).S i).relIndex (Hh hsw) :=
      Subgroup.relIndex_le_of_le_left hle
        (Subgroup.index_ne_zero_of_finite (H := ((twist).S i).subgroupOf (Hh hsw)))
    have hconjP : ∀ s ∈ P.map (psiG hsw), (twist).x i * s * ((twist).x i)⁻¹ ∈ Hh hsw := by
      rintro _ ⟨e, he, rfl⟩
      exact (hmemS i hi e).1 he
    have hge := hex3 i hi _ hconjP
    have hrel : ((twist).S i).relIndex (Hh hsw) = (P.map (psiG hsw)).relIndex (Hh hsw) :=
      le_antisymm (hDS ▸ hge) hmono
    refine ⟨?_, by rw [← hidx, ← hrel, hDS]⟩
    have hc1 := Subgroup.relIndex_mul_card (H := (twist).S i) (K := Hh hsw)
    have hc2 := Subgroup.relIndex_mul_card (H := P.map (psiG hsw)) (K := Hh hsw)
    rw [inf_of_le_left ((twist).S_le i)] at hc1
    have hPH : P.map (psiG hsw) ≤ Hh hsw := Subgroup.map_le_range _ _
    rw [inf_of_le_left hPH] at hc2
    have hpos : 0 < ((twist).S i).relIndex (Hh hsw) := by rw [hDS]; exact Nat.div_pos (by
      have := (data_ok.2.1 _ ((liveL_spec _).1 (nodeAt_mem i)).1 ((liveL_spec _).1 (nodeAt_mem i)).2)
      exact Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero this.2)) (data_ok.2.1 _
        ((liveL_spec _).1 (nodeAt_mem i)).1 ((liveL_spec _).1 (nodeAt_mem i)).2).1
    refine Subgroup.eq_of_le_of_card_ge hle (Nat.le_of_mul_le_mul_left ?_ hpos)
    rw [hc1, hrel, hc2]
  have hρS : ∀ i ∈ Ev, ∀ e ∈ CFSG.YGroups.DCE.B.stabSub setupB (yB i),
      rho432F e ∈ Kof (nodeAt i) := by
    intro i hi e he
    have hmem : psiG hsw e ∈ (twist).S i := by
      rw [(hSeq i hi).1]
      exact ⟨e, he, rfl⟩
    obtain ⟨s, hs, hseq⟩ := hmem
    refine ⟨s, hs, ?_⟩
    have hk : s⁻¹ * e ∈ (psiG hsw).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hseq, inv_mul_cancel]
    rw [hkerG, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk
  have hcardK : ∀ i ∈ Ev, Nat.card (Kof (nodeAt i)) = CFSG.KD.B4AC.MJ (nodeAt i) := by
    intro i hi
    set P := CFSG.YGroups.DCE.B.stabSub setupB (yB i)
    have hkP : rho432F.ker ≤ P := hkerG ▸ hkerS i hi
    have heq : P.map rho432F = Kof (nodeAt i) := by
      refine le_antisymm (by rintro _ ⟨e, he, rfl⟩; exact hρS i hi e he) ?_
      rintro _ ⟨s, hs, rfl⟩
      have hsS : psiG hsw s ∈ (twist).S i := ⟨s, hs, rfl⟩
      rw [(hSeq i hi).1] at hsS
      obtain ⟨p, hp, hps⟩ := hsS
      have hk : p⁻¹ * s ∈ rho432F.ker := by
        rw [← hkerG, MonoidHom.mem_ker, map_mul, map_inv, hps, inv_mul_cancel]
      refine ⟨p, hp, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
      exact hk
    have h1 := index_mul_card_map_of_ker_le rho432F P hkP
    rw [card_range_rho432F, heq, (hSeq i hi).2] at h1
    obtain ⟨hj, hlv⟩ := (liveL_spec _).1 (nodeAt_mem i)
    obtain ⟨hpos, hdvd⟩ := data_ok.2.1 _ hj hlv
    have hd : CFSG.KD.B4AC.MJ (nodeAt i) * vN i = 4089470473293004800 :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdvd)
    have hv : 0 < vN i := Nat.div_pos (Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero hdvd)) hpos
    refine Nat.eq_of_mul_eq_mul_left hv ?_
    rw [h1, mul_comm, hd]
  let inst : MulAction (YGroup 4 3 2) (Equiv.Perm (Fin 31671)) :=
    MulAction.compHom _ ((ConjAct.toConjAct : Equiv.Perm (Fin 31671) ≃*
      ConjAct (Equiv.Perm (Fin 31671))).toMonoidHom.comp rho432F)
  have hsmul : ∀ (e : YGroup 4 3 2) (σ : Equiv.Perm (Fin 31671)),
      e • σ = rho432F e * σ * (rho432F e)⁻¹ := fun e σ => ConjAct.toConjAct_smul (rho432F e) σ
  set Stab : Subgroup (YGroup 4 3 2) :=
    (Subgroup.centralizer {rho432F dFive}).comap rho432F with hStab
  have hstabE : MulAction.stabilizer (YGroup 4 3 2) (rho432F dFive) = Stab := by
    ext e
    rw [MulAction.mem_stabilizer_iff, hsmul, hStab, Subgroup.mem_comap,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      calc rho432F e * rho432F dFive
          = rho432F e * rho432F dFive * (rho432F e)⁻¹ * rho432F e := by group
        _ = rho432F dFive * rho432F e := by rw [h1]
    · intro h1
      rw [h1, mul_inv_cancel_right]
  have ho : (MulAction.orbit (YGroup 4 3 2) (rho432F dFive)).ncard = Stab.index := by
    rw [← MulAction.index_stabilizer, hstabE]
  have hkerρ : rho432F.ker ≤ Stab := by
    intro e he
    rw [hStab, Subgroup.mem_comap, MonoidHom.mem_ker.1 he]
    exact Subgroup.one_mem _
  have hρ := index_mul_card_map_of_ker_le rho432F Stab hkerρ
  rw [card_range_rho432F, hStab, Subgroup.map_comap_eq, inf_comm] at hρ
  have hcomap : (Subgroup.centralizer {psi dFive}).comap psi = Stab := by
    ext e
    rw [hStab, Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, comm_iff_ker psi, comm_iff_ker rho432F, hker]
  have hψ := index_mul_card_map_of_ker_le psi Stab (by rw [hker]; exact hkerρ)
  rw [hpsiF, ← hcomap, Subgroup.map_comap_eq, inf_comm, hcomap] at hψ
  have hCH : Nat.card ((Subgroup.centralizer {psi dFive}).subgroupOf psi.range) =
      Nat.card ↥(Subgroup.centralizer {rho432F dFive} ⊓ rho432F.range) := by
    have e1 : Nat.card ((Subgroup.centralizer {psi dFive}).subgroupOf psi.range) =
        Nat.card (Subgroup.centralizer {psi dFive} ⊓ psi.range : Subgroup B433) := by
      rw [← Subgroup.card_map_of_injective psi.range.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
    rw [e1]
    have hpos : 0 < Stab.index := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hρ
      norm_num at hρ
    exact Nat.eq_of_mul_eq_mul_left hpos (hψ.trans hρ.symm)
  let xN : ℕ → B433 := fun n => if h : n < 46 then yB ⟨n, h⟩ else 1
  let I : Finset ℕ := Ev.map Fin.valEmbedding
  have hxN : ∀ i : Fin 46, xN i = yB i := fun i => dif_pos i.2
  let XcF : Fin 46 → Finset (Equiv.Perm (Fin 31671)) := fun i =>
    if i = idxOf 0 then (Set.toFinite (MulAction.orbit (YGroup 4 3 2) (rho432F dFive))).toFinset
    else (Set.toFinite {σ : Equiv.Perm (Fin 31671) | σ ∈ Kof (nodeAt i) ∧ orderOf σ = 5}).toFinset
  let XcN : ℕ → Finset (Equiv.Perm (Fin 31671)) := fun n => if h : n < 46 then XcF ⟨n, h⟩ else ∅
  let sN : ℕ → ℕ := fun n => if h : n < 46 then vN ⟨n, h⟩ else 0
  have hXcN : ∀ i : Fin 46, XcN i = XcF i := fun i => dif_pos i.2
  have hsN : ∀ i : Fin 46, sN i = vN i := fun i => dif_pos i.2
  have hcoverN : ∀ c : B433 ⧸ setupB.H, ∃ i ∈ I, ∃ e, c = setupB.cosetOf (xN i) e := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨ι, a, ha, b, hb, hg⟩ := (twist).exists_eq (u_mul_self hsw) (u_conj_Th hsw)
        (closure_Hh_u hsw) (inlB g⁻¹)
      obtain ⟨ea, rfl⟩ := ha
      obtain ⟨eb, rfl⟩ := hb
      have hιE : ι ∈ Ev := by
        rw [← x_mem_inl_iff]
        have e1 : (twist).x ι = (psiG hsw ea)⁻¹ * inlB g⁻¹ * (psiG hsw eb)⁻¹ := by
          rw [hg]
          group
        rw [e1]
        exact (inlB : B433 →* Ghat hsw).range.mul_mem ((inlB : B433 →* Ghat hsw).range.mul_mem
          ⟨(psi ea)⁻¹, by rw [map_inv]; rfl⟩ ⟨g⁻¹, rfl⟩) ⟨(psi eb)⁻¹, by rw [map_inv]; rfl⟩
      refine ⟨ι, Finset.mem_map_of_mem _ hιE, eb⁻¹, ?_⟩
      have hy : yB ι = psi ea⁻¹ * g⁻¹ * psi eb⁻¹ := by
        apply hinl
        rw [hyB ι hιE, map_mul, map_mul]
        change (twist).x ι = psiG hsw ea⁻¹ * inlB g⁻¹ * psiG hsw eb⁻¹
        rw [hg, map_inv, map_inv]
        group
      rw [Setup.cosetOf, hxN, QuotientGroup.eq, hy]
      refine ⟨ea, ?_⟩
      change psi ea = g⁻¹ * (psi eb⁻¹ * (psi ea⁻¹ * g⁻¹ * psi eb⁻¹)⁻¹)
      simp only [map_inv]
      group
  have hsI : ∀ i ∈ I, (CFSG.YGroups.DCE.B.stabSub setupB (xN i)).index ≤ sN i := by
    intro n hn
    obtain ⟨ι, hι, rfl⟩ := Finset.mem_map.1 hn
    simp only [Fin.valEmbedding_apply, hxN, hsN]
    exact (hSeq ι hι).2.le
  have hXN : ∀ i ∈ I, setupB.fixLabels (xN i) dFive (rho432F dFive) ⊆ XcN i := by
    intro n hn
    obtain ⟨ι, hι, rfl⟩ := Finset.mem_map.1 hn
    simp only [Fin.valEmbedding_apply, hxN, hXcN]
    intro ω hω
    obtain ⟨e, rfl, hed⟩ := hω
    by_cases h0 : ι = idxOf 0
    · simp only [XcF, h0, if_true, Finset.coe_sort_coe, Set.Finite.coe_toFinset]
      exact MulAction.mem_orbit _ _
    · simp only [XcF, h0, if_false, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      rw [hsmul]
      have e1 : rho432F e⁻¹ * rho432F dFive * (rho432F e⁻¹)⁻¹ = rho432F (e⁻¹ * dFive * e) := by
        simp only [map_mul, map_inv, inv_inv]
      rw [e1]
      refine ⟨hρS ι hι _ hed, ?_⟩
      rw [← e1, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hs5
  have hinj : Function.Injective nodeAt := by decide +kernel
  have hterm : ∀ i ∈ Ev, i ≠ idxOf 0 → (XcF i).card * vN i ≤
      ∑ k ∈ Finset.range 17, if FJ.getD k 0 = nodeAt i then
        CFSG.KD.B4AC.MJ (FJ.getD k 0) / FB.getD k 0 * (5 ^ FA.getD k 0 - 1) *
          (4089470473293004800 / CFSG.KD.B4AC.MJ (FJ.getD k 0)) else 0 := by
    intro i hi h0
    simp only [XcF, h0, if_false]
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    obtain ⟨hj, hlv⟩ := (liveL_spec _).1 (nodeAt_mem i)
    have hpa : CFSG.KD.B4AT.PA.getD (nodeAt i) 0 = 0 := by
      simp only [Ev, Finset.mem_filter] at hi
      exact hi.2
    have hne0 : nodeAt i ≠ 0 := by
      intro h
      apply h0
      apply hinj
      rw [h, nodeAt_idxOf ((liveL_spec 0).2 ⟨by norm_num, by decide⟩)]
    by_cases hF : nodeAt i ∈ FJ
    · obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem hF
      have hk17 : k < 17 := by rw [five_data.1] at hk; exact hk
      have hkj' : FJ.getD k 0 = nodeAt i := by rw [List.getD_eq_getElem _ _ hk, hkj]
      have hcount := ncard_five_le hk17 (c := CFSG.KD.B4AC.MJ (FJ.getD k 0))
        (by rw [hkj']; exact hcardK i hi) ((five_cover_data.1 k hk17).2.2.2.2)
      rw [hkj'] at hcount
      have huniq : ∀ k' ∈ Finset.range 17, k' ≠ k → FJ.getD k' 0 ≠ nodeAt i := by
        intro k' hk' hne he
        apply hne
        have h1 : FJ.getD k' 0 = FJ.getD k 0 := he.trans hkj'.symm
        have hl := five_data.1
        rw [List.getD_eq_getElem _ _ (by rw [hl]; exact Finset.mem_range.1 hk'),
          List.getD_eq_getElem _ _ (by rw [hl]; exact hk17)] at h1
        exact (List.Nodup.getElem_inj_iff five_cover_data.2.2).1 h1
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk17) (fun k' hk' hne => by
        rw [if_neg (huniq k' hk' hne)]), if_pos hkj']
      unfold vN
      rw [hkj']
      exact Nat.mul_le_mul_right _ hcount
    · have h5 := five_cover_data.2.1 _ hj hlv hpa hne0 hF
      rw [ncard_five_eq_zero (by rw [hcardK i hi]; exact h5), zero_mul]
      exact Nat.zero_le _
  have hsum : ∑ i ∈ I, (XcN i).card * sN i ≤ Stab.index + 4089470473293004800 := by
    rw [Finset.sum_map]
    simp only [Fin.valEmbedding_apply, hXcN, hsN]
    rw [← Finset.add_sum_erase _ _ idx0_mem]
    have h0 : (XcF (idxOf 0)).card * vN (idxOf 0) = Stab.index := by
      simp only [XcF, if_true, vN_idx0, mul_one]
      rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _), ho]
    rw [h0]
    refine Nat.add_le_add_left ?_ _
    refine (Finset.sum_le_sum fun i hi => hterm i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi)).trans ?_
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) five_sum
    have hk17 := Finset.mem_range.1 hk
    obtain ⟨hj, hlv, hpa, hne0, -⟩ := five_cover_data.1 k hk17
    have hmem : FJ.getD k 0 ∈ liveL := (liveL_spec _).2 ⟨hj, hlv⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_one.2 fun a ha b hb => ?_)) (by simp)
    simp only [Finset.mem_filter] at ha hb
    exact hinj (ha.2.symm.trans hb.2)
  have hmain := setupB.card_centralizer_le (d := dFive) (ω₀ := rho432F dFive) xN I hcoverN sN
    hsI XcN hXN
  change Nat.card (Subgroup.centralizer {psi dFive}) * _ ≤
    _ * Nat.card ((Subgroup.centralizer {psi dFive}).subgroupOf psi.range) at hmain
  rw [ho, hCH] at hmain
  set c := Nat.card ↥(Subgroup.centralizer {rho432F dFive} ⊓ rho432F.range) with hcdef
  set o := Stab.index with hodef
  set Z := Nat.card (Subgroup.centralizer {psi dFive}) with hZ
  have h1 : Z * o ≤ (o + 4089470473293004800) * c := hmain.trans (Nat.mul_le_mul_right _ hsum)
  have h2 : 4089470473293004800 * Z ≤ 4089470473293004800 * ((1 + c) * c) := by
    calc 4089470473293004800 * Z = Z * o * c := by rw [← hρ]; ring
      _ ≤ (o + 4089470473293004800) * c * c := Nat.mul_le_mul_right _ h1
      _ = (o * c + 4089470473293004800 * c) * c := by ring
      _ = 4089470473293004800 * ((1 + c) * c) := by rw [hρ]; ring
  have h3 : Z ≤ (1 + c) * c := Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hZle : Z ≤ 635065200 := h3.trans (Nat.mul_le_mul (Nat.add_le_add_left hC2 1) hC2)
  have horder : ∀ (x : YGroup 4 3 2) (p : ℕ), p.Prime → orderOf (rho432F x) = p →
      orderOf (psi x) = p := by
    intro x p hp hx
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ ?_
    · have hxp : x ^ p ∈ rho432F.ker := by
        rw [MonoidHom.mem_ker, map_pow, ← hx, pow_orderOf_eq_one]
      rw [← map_pow]
      exact MonoidHom.mem_ker.1 (ker_rho432F_le_ker_psi hxp)
    · intro h1
      have hx1 : x ∈ psi.ker := MonoidHom.mem_ker.2 h1
      rw [hker, MonoidHom.mem_ker] at hx1
      rw [hx1, orderOf_one] at hx
      exact hp.one_lt.ne hx
  have hψe7 : orderOf (psi e7) = 7 := horder e7 7 (by norm_num) he7
  have he7mem : psi e7 ∈ Subgroup.centralizer {psi dFive} := by
    rw [Subgroup.mem_centralizer_singleton_iff, comm_iff_ker]
    exact ker_rho432F_le_ker_psi ((comm_iff_ker rho432F e7 dFive).1 he7c)
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer {psi dFive}) := by
    have hd := orderOf_dvd_natCard (⟨psi e7, he7mem⟩ : Subgroup.centralizer {psi dFive})
    rwa [Subgroup.orderOf_mk, hψe7] at hd
  exact ⟨horder dFive 5 (by norm_num) hs5, h7, hZle⟩

end

end CertificateChecks.KernelB433

end
