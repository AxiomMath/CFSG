module

public import Certificates.Kernel.B433Alt.FixExcl
public import CFSG.YGroups.DCE.B433Fix
public import Certificates.Kernel.B433Alt.Y333B

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CertificateChecks.KernelY442 CFSG.KC.B433Alt CFSG.Certificates.TwDce CFSG.YGroups.SymGen
  CFSG.YGroups.DCE.B433

@[expose] noncomputable def setupB : SymGen.Setup B433 (YGroup 4 3 2) Unit where
  t := 1
  ψ := psi
  o := ()
  w := fun _ => 1
  t_mul_t := mul_one 1
  w_smul := fun _ => rfl
  stab_comm := fun c _ => by rw [mul_one, one_mul]

theorem setupB_H : setupB.H = psi.range := rfl

theorem relIndex_map_eq_index {E G' : Type*} [Group E] [Group G'] (φ : E →* G') (P : Subgroup E)
    (hker : φ.ker ≤ P) : (P.map φ).relIndex φ.range = P.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right, sup_of_le_left hker]

theorem ev_data : (Finset.range 22).image (fun k => idxOf (CFSG.KD.B4AX.NJ.getD k 0)) =
      Ev.erase (idxOf 0) ∧
    Set.InjOn (fun k => idxOf (CFSG.KD.B4AX.NJ.getD k 0)) (Finset.range 22 : Set ℕ) ∧
    ∀ k < 22, nodeAt (idxOf (CFSG.KD.B4AX.NJ.getD k 0)) = CFSG.KD.B4AX.NJ.getD k 0 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro a ha b hb h
  have key : ∀ a < 22, ∀ b < 22, idxOf (CFSG.KD.B4AX.NJ.getD a 0) = idxOf (CFSG.KD.B4AX.NJ.getD b 0) →
      a = b := by decide +kernel
  exact key a (by simpa using ha) b (by simpa using hb) h

theorem evalWord_replicate (L : List ℕ) :
    ∀ n, evalWord (yGen 4 3 2) (List.replicate n L).flatten = evalWord (yGen 4 3 2) L ^ n
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, CFSG.Certificates.CosetEnumeration.evalWord_append,
      evalWord_replicate L n, pow_succ']

theorem dY_eq : dY = dT := by
  unfold dY dT dWL
  rw [evalWord_replicate]
  rfl

section

theorem card_centralizer_dY_le (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    Nat.card (Subgroup.centralizer {psi dY}) ≤ 306129918735099415756800 := by
  classical
  have hfinB : Finite B433 := (B433_finite_card_le).1
  have hfinG := finite_Ghat
  have hfinY := finite_y432
  let inst : MulAction (YGroup 4 3 2) (Fin 31671) := MulAction.compHom (Fin 31671) rho432F
  have hsmul : ∀ (e : YGroup 4 3 2) (y : Fin 31671), e • y = rho432F e y := fun _ _ => rfl
  obtain ⟨hex2, hHeq, hex3⟩ := exact hG
  have hker := ker_psi hG
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
      (CFSG.YGroups.DCE.B.stabSub setupB (yB i)).index ≤ vN i := by
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
    refine ⟨?_, by rw [← hidx]; exact hmono.trans hDS.le⟩
    have hrel : ((twist).S i).relIndex (Hh hsw) = (P.map (psiG hsw)).relIndex (Hh hsw) :=
      le_antisymm (hDS ▸ hge) hmono
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
  let xN : ℕ → B433 := fun n => if h : n < 46 then yB ⟨n, h⟩ else 1
  let I : Finset ℕ := Ev.map Fin.valEmbedding
  have hxN : ∀ i : Fin 46, xN i = yB i := fun i => dif_pos i.2
  let kOf : Fin 46 → ℕ := fun i => CFSG.KD.B4AX.NJ.idxOf (nodeAt i)
  let XcF : Fin 46 → Finset (Fin 31671) := fun i =>
    if i = idxOf 0 then Finset.univ else Finset.univ.filter fun ω => (Xs (kOf i)).testBit ω = true
  let XcN : ℕ → Finset (Fin 31671) := fun n => if h : n < 46 then XcF ⟨n, h⟩ else ∅
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
    exact (hSeq ι hι).2
  have hXN : ∀ i ∈ I, setupB.fixLabels (xN i) dY (0 : Fin 31671) ⊆ XcN i := by
    intro n hn
    obtain ⟨ι, hι, rfl⟩ := Finset.mem_map.1 hn
    simp only [Fin.valEmbedding_apply, hxN, hXcN]
    intro ω hω
    by_cases h0 : ι = idxOf 0
    · simp [XcF, h0]
    · obtain ⟨e, he0, hed⟩ := hω
      have hmem : psiG hsw (e⁻¹ * dY * e) ∈ (twist).S ι := by
        rw [(hSeq ι hι).1]
        exact ⟨_, hed, rfl⟩
      obtain ⟨s, hs, hseq⟩ := hmem
      have hsρ : rho432F s = rho432F (e⁻¹ * dY * e) := by
        have hk : s⁻¹ * (e⁻¹ * dY * e) ∈ (psiG hsw).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hseq, inv_mul_cancel]
        rw [hkerG, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
        exact hk
      have hlab : lab ω = rho432F (e⁻¹ * dY * e) := by
        have he0' : rho432F e⁻¹ 0 = ω := he0
        rw [lab_eq jComm he0', dY_eq, map_mul, map_mul, map_inv, inv_inv, d0]
      have hmemL := nodeAt_mem ι
      obtain ⟨hj64, hjl⟩ := (liveL_spec _).1 hmemL
      have hpa : CFSG.KD.B4AT.PA.getD (nodeAt ι) 0 = 0 := by
        have := hι
        simp only [Ev, Finset.mem_filter] at this
        exact this.2
      have hne0 : nodeAt ι ≠ 0 := by
        intro h
        apply h0
        have hinj : Function.Injective nodeAt := by decide +kernel
        apply hinj
        rw [h, nodeAt_idxOf ((liveL_spec 0).2 ⟨by norm_num, by decide⟩)]
      have hjNJ : nodeAt ι ∈ CFSG.KD.B4AX.NJ := nj_all _ hj64 ⟨hjl, hpa, hne0⟩
      have hk22 : kOf ι < 22 := by
        have := List.idxOf_lt_length_of_mem hjNJ
        rw [nj_data.1] at this
        exact this
      have hNJk : CFSG.KD.B4AX.NJ.getD (kOf ι) 0 = nodeAt ι := by
        rw [List.getD_eq_getElem _ _ (by rw [nj_data.1]; exact hk22)]
        exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hjNJ)
      have hX := mem_X hk22 ω (by
        rw [hNJk, hlab, ← hsρ]
        exact ⟨s, hs, rfl⟩)
      rw [Finset.mem_coe]
      simp only [XcF, h0, if_false, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hX
  have hJidx : 31671 ≤ J432.index := by
    have hle : J432 ≤ MulAction.stabilizer (YGroup 4 3 2) (0 : Fin 31671) := by
      rw [J432, Subgroup.closure_le]
      rintro _ ⟨c, ⟨hc, hc4⟩, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, hsmul]
      exact tL_fix_zero c (by
        simp only [tL, List.mem_cons, List.not_mem_nil, or_false]
        omega)
    have horb : (MulAction.orbit (YGroup 4 3 2) (0 : Fin 31671)) = Set.univ := by
      ext p
      simp only [Set.mem_univ, iff_true]
      obtain ⟨y, hy⟩ := transitive_zero p
      exact ⟨y, hy⟩
    have h1 : (MulAction.stabilizer (YGroup 4 3 2) (0 : Fin 31671)).index = 31671 := by
      rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_fin]
    rw [← h1]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have hCH : Nat.card ((Subgroup.centralizer {psi dY}).subgroupOf psi.range) ≤
      129123503308800 := by
    have hle : Subgroup.centralizer {psi dY} ⊓ psi.range ≤ J432.map psi := by
      rintro z ⟨hz, ⟨e, rfl⟩⟩
      have hc : psi e * psi dY = psi dY * psi e := Subgroup.mem_centralizer_singleton_iff.1 hz
      have hk : e * dY * e⁻¹ * dY⁻¹ ∈ psi.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      rw [hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, dY_eq, ← d0] at hk
      have hcρ : rho432F e * d0 * (rho432F e)⁻¹ = d0 := mul_inv_eq_one.1 hk
      have he0 : rho432F e 0 = 0 := by
        apply lab_inj labFacts
        rw [lab_eq jComm rfl, hcρ, lab_zero jComm]
      have hJ : e ∈ J432 := by
        rw [← lsub_tL_eq]
        exact stab_zero he0
      exact ⟨e, hJ, rfl⟩
    have hJmap : Nat.card (J432.map psi) ≤ 129123503308800 := by
      have hkerJ : psi.ker ≤ J432 := by
        rw [hker]
        intro e he
        rw [← lsub_tL_eq]
        apply stab_zero
        rw [MonoidHom.mem_ker.1 he]
        rfl
      have h1 : J432.index * Nat.card (J432.map psi) = Nat.card psi.range := by
        have h2 := Subgroup.relIndex_mul_card (H := J432.map psi) (K := psi.range)
        rwa [inf_of_le_left (Subgroup.map_le_range psi J432),
          relIndex_map_eq_index psi J432 hkerJ] at h2
      rw [card_psi_range hG] at h1
      have h3 : 31671 * Nat.card (J432.map psi) ≤ 4089470473293004800 := by
        rw [← h1]
        exact Nat.mul_le_mul_right _ hJidx
      omega
    calc Nat.card ((Subgroup.centralizer {psi dY}).subgroupOf psi.range)
        = Nat.card (((Subgroup.centralizer {psi dY}).subgroupOf psi.range).map
            psi.range.subtype) :=
          (Subgroup.card_map_of_injective psi.range.subtype_injective).symm
      _ = Nat.card (Subgroup.centralizer {psi dY} ⊓ psi.range : Subgroup B433) := by
          rw [Subgroup.subgroupOf_map_subtype]
      _ ≤ Nat.card (J432.map psi) := Subgroup.card_le_of_le hle
      _ ≤ 129123503308800 := hJmap
  have hsum : ∑ i ∈ I, (XcN i).card * sN i ≤ 75086567571456 := by
    rw [Finset.sum_map]
    simp only [Fin.valEmbedding_apply, hXcN, hsN]
    rw [← Finset.add_sum_erase _ _ idx0_mem]
    have h0 : (XcF (idxOf 0)).card * vN (idxOf 0) = 31671 := by
      rw [show XcF (idxOf 0) = Finset.univ from if_pos rfl, Finset.card_univ, Fintype.card_fin,
        vN_idx0]
    rw [h0]
    obtain ⟨himg, hinj, hnode⟩ := ev_data
    rw [← himg, Finset.sum_image hinj]
    refine le_trans (Nat.add_le_add_left (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) _)
      sum_data
    have hk' := Finset.mem_range.1 hk
    have hne : idxOf (CFSG.KD.B4AX.NJ.getD k 0) ≠ idxOf 0 := by
      intro h
      have := congrArg nodeAt h
      rw [hnode k hk', nodeAt_idxOf ((liveL_spec 0).2 ⟨by norm_num, by decide⟩)] at this
      exact (nj_data.2.2 k hk').2.2.2 this
    have hkk : kOf (idxOf (CFSG.KD.B4AX.NJ.getD k 0)) = k := by
      change CFSG.KD.B4AX.NJ.idxOf (nodeAt _) = k
      rw [hnode k hk', idxOf_nj hk']
    simp only [XcF, hne, if_false, hkk]
    rw [card_X hk']
  have hmain := setupB.card_centralizer_le (d := dY) (ω₀ := (0 : Fin 31671)) xN I hcoverN sN
    hsI XcN hXN
  have horbE : (MulAction.orbit (YGroup 4 3 2) (0 : Fin 31671)).ncard = 31671 := by
    have : MulAction.orbit (YGroup 4 3 2) (0 : Fin 31671) = Set.univ := by
      ext p
      simp only [Set.mem_univ, iff_true]
      obtain ⟨y, hy⟩ := transitive_zero p
      exact ⟨y, hy⟩
    rw [this, Set.ncard_univ, Nat.card_fin]
  rw [horbE] at hmain
  have h3 := hmain.trans (Nat.mul_le_mul hsum hCH)
  rw [show (75086567571456 : ℕ) * 129123503308800 = 306129918735099415756800 * 31671 by
    norm_num] at h3
  exact Nat.le_of_mul_le_mul_right h3 (by norm_num)

end

end CertificateChecks.KernelB433

end
