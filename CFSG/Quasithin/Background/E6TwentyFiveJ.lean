module

public import CFSG.Quasithin.Background.E6TwentyFiveI
public import CFSG.Quasithin.Background.E6TwentyThreeC

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Tools

variable {G : Type} [Group G] [Finite G]

theorem not_isQuasisimple_of_isShort2 {L : Subgroup G} (hs : IsShort2 L) :
    ¬ CFSG.IsQuasisimple ↥L := by
  intro hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hLP : L ≤ pCoreOf 2 L := by
    intro x hx
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with h | h
    · exact ⟨⟨x, hx⟩, by rw [h]; exact Subgroup.mem_top _, rfl⟩
    · refine hs.2.1 ⟨hx, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      have h1 := Subgroup.mem_center_iff.1 (h hp) ⟨x, hx⟩
      exact congrArg Subtype.val h1.symm
  have h2 : IsPGroup 2 ↥L := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hLP
  have : Group.IsPerfect ↥L := hq.1
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsNilpotent ↥L := h2.isNilpotent
  have hsolv : Group.IsSolvable ↥L := inferInstance
  exact Group.IsPerfect.not_isSolvable _ hsolv

omit [Finite G] in
theorem sixty_dvd_card_range {L L₂ : Subgroup G} (hLL₂ : L ≤ L₂) (hL : IsLin2Type L 2)
    {H : Type*} [Group H] (α : ↥L₂ →* H) (hα : α.ker = CFSG.pCore 2 ↥L₂) :
    60 ∣ Nat.card (α.comp (Subgroup.inclusion hLL₂)).range := by
  set β := α.comp (Subgroup.inclusion hLL₂) with hβ
  have hk2 : IsPGroup 2 β.ker := by
    intro x
    have hx : Subgroup.inclusion hLL₂ (x : ↥L) ∈ CFSG.pCore 2 ↥L₂ := by
      rw [← hα, MonoidHom.mem_ker]
      exact x.2
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨_, hx⟩ : CFSG.pCore 2 ↥L₂)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h1 := congrArg (fun y : CFSG.pCore 2 ↥L₂ => ((y : ↥L₂) : G)) hk
    simpa using h1
  have hle : β.ker ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, hk2⟩
  have hidx := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker] at hidx
  obtain ⟨F, hF, hFin, hcard, αL, hαs, hαk, -⟩ := hL
  have h60 : (CFSG.pCore 2 ↥L).index = 60 := by
    rw [← hαk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hαs, Subgroup.card_top,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hcard]
    norm_num
  rwa [h60] at hidx

omit [Finite G] in
theorem not_isLin2Type_three {L L₂ : Subgroup G} (hLL₂ : L ≤ L₂) (hL : IsLin2Type L 2) :
    ¬ IsLin2Type L₂ 3 := by
  rintro ⟨F, hF, hFin, hcard, α, -, hαk, -⟩
  have h1 := sixty_dvd_card_range hLL₂ hL α hαk
  have h2 := Subgroup.card_subgroup_dvd_card (α.comp (Subgroup.inclusion hLL₂)).range
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card (α := F),
    hcard] at h2
  have h3 := dvd_trans h1 h2
  norm_num at h3

omit [Finite G] in
theorem exists_mul_mem_pCore_of_isLin2Type_two {L L₂ : Subgroup G} (hLL₂ : L ≤ L₂)
    (hL : IsLin2Type L 2) (hL₂ : IsLin2Type L₂ 2) (x : ↥L₂) :
    ∃ l : ↥L, (Subgroup.inclusion hLL₂ l)⁻¹ * x ∈ CFSG.pCore 2 ↥L₂ := by
  obtain ⟨F, hF, hFin, hcard, α, -, hαk, -⟩ := hL₂
  set β := α.comp (Subgroup.inclusion hLL₂) with hβ
  have h1 := sixty_dvd_card_range hLL₂ hL α hαk
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card,
      hcard]
    norm_num
  have h2 := Subgroup.card_subgroup_dvd_card β.range
  rw [hSL] at h2
  have h3 : Nat.card β.range = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [hSL]
    exact Nat.dvd_antisymm h2 h1
  have htop : β.range = ⊤ := Subgroup.eq_top_of_card_eq _ h3
  obtain ⟨l, hl⟩ := MonoidHom.range_eq_top.1 htop (α x)
  refine ⟨l, ?_⟩
  have hl' : α (Subgroup.inclusion hLL₂ l) = α x := hl
  rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hl', inv_mul_cancel]

theorem exists_notTwoCtx_at (h621 : E621Stmt) {T M V U L X : Subgroup G}
    {hV : CFSG.Open.IsElemAbelian 2 V} (hset : E625Setting T M V U hV) (hD : E611Data hV M U L X)
    {Y : Fin 2 → Subgroup (MulAut (IntMod V hV))} {Vs : Fin 2 → Subgroup (IntMod V hV)}
    (hB : E624Body hV M X 2 Y Vs) (hX3 : Nat.card (autI hV X) = 3) (hXY : ∀ i, autI hV X ≠ Y i)
    {i₀ j₀ : Fin 2} (hij : i₀ ≠ j₀) (hle : autI hV X ≤ Y i₀) :
    ∃ u : G, NotTwoCtx T M V U L X hV Y Vs i₀ j₀ u := by
  obtain ⟨i₁, j₁, u, hc⟩ := exists_notTwoCtx h621 hset hD hB hX3 hXY
  have hYind : iSupIndep Y := hB.1.2.1
  have hi : i₁ = i₀ := by
    by_contra hne
    have hdis : Disjoint (Y i₁) (Y i₀) := hYind.pairwiseDisjoint hne
    have hbot : autI hV X = ⊥ := le_bot_iff.1 (hdis hc.le_Y hle)
    rw [hbot, Subgroup.card_bot] at hX3
    omega
  subst hi
  have hj : j₁ = j₀ := by
    have h1 := hc.ne
    fin_cases i₁ <;> fin_cases j₁ <;> fin_cases j₀ <;> simp_all
  subst hj
  exact ⟨u, hc⟩

end Tools

theorem e625NotTwoBlockNQ_of (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h621 : E621Stmt)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) : E625NotTwoBlockNQ := by
  intro G _ _ T M V U L X hV hset hD hLb Y Vs hB hX3 hXY i₀ j₀ hij hle L₂ hL₂ hLL₂ hL₂q
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hc⟩ := exists_notTwoCtx_at h621 hset hD hB hX3 hXY hij hle
  have hset' := hset
  obtain ⟨h, -, hU, -, -, -⟩ := hset'
  have hD' := hD
  obtain ⟨hLU, hLn, hLM, hCL, -, -, hXcard, -, -, -, -, -, -, htype⟩ := hD'
  have := h.simple
  set V₂ := (Vs j₀).map (E3.valHom hV) with hV₂def
  set H₂ := Subgroup.centralizer (V₂ : Set G) with hH₂def
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hQ2 : IsPGroup 2 Q := h.isPGroup_Q
  have hQH₂ : IsSylowTwoOf Q H₂ := hc.sylow
  have hV₂V : V₂ ≤ V := E3.map_valHom_le hV _
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hpc₂ : pCoreOf 2 H₂ ≠ ⊥ := by
    have hV₂1 : V₂ ≠ ⊥ := hc.gamma.2.1
    intro h0
    apply hV₂1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_ (Subgroup.centralizer_le_normalizer _)
      (h.isPGroup_V.to_le hV₂V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hV₂V hw') _ (hV₂V hw)
  have hQM : Q ≤ M := inf_le_left.trans h.inM.2
  have hn2 : E3.mQuot V U = 2 := by
    rw [hXcard] at hX3
    have h4 : 2 ^ E3.mQuot V U = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) h4
  have hLlin : IsLin2Type L 2 := by
    rcases htype with ⟨⟨-, hLin⟩ | ⟨hLc, -⟩, -⟩ | ⟨hLc, -⟩
    · rwa [hn2] at hLin
    · exact absurd (BenderBranch.isQuasisimple_of_isComponentIn hLc)
        (not_isQuasisimple_of_isShort2 hLb.1)
    · exact absurd (BenderBranch.isQuasisimple_of_isComponentIn hLc)
        (not_isQuasisimple_of_isShort2 hLb.1)
  have h3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 :=
    L238.card_ne_three_of_isLin2Type (by omega) hLlin
  have hLcU : L ∈ cComp (Subgroup.centralizer (U : Set G)) := L238.mem_cComp_of_isBlock2 hLb h3
  have hQU : Q ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hLfam : L ∈ lFamily Q := cComp_subset_lFamily hQU hLcU
  have hNL : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLU).1 hLn
  have hL₂M : ¬ L₂ ≤ M := fun hle' => hLM (hLL₂.trans hle')
  set Yc := conjClosure L₂ Q with hYcdef
  set K := Yc ⊔ Q with hKdef
  have hL₂H₂ : L₂ ≤ H₂ := le_of_mem_cComp hL₂
  have hYcH₂ : Yc ≤ H₂ := conjClosure_le_of_le hL₂H₂ hQH₂.1
  have hKH₂ : K ≤ H₂ := sup_le hYcH₂ hQH₂.1
  have hH₂Yc : H₂ ≤ Subgroup.normalizer (Yc : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hq.1 h37 h38 hpc₂ hQH₂ hL₂
  have hQYc : Q ≤ Subgroup.normalizer (Yc : Set G) := hQH₂.1.trans hH₂Yc
  have hYcsn : IsSubnormal Yc H₂ :=
    A3.subnormal_of_normal hYcH₂ ((Subgroup.normal_subgroupOf_iff_le_normalizer hYcH₂).2 hH₂Yc)
  have hQK : IsSylowTwoOf Q K := A4.isSylowTwoOf_mono hQH₂ le_sup_right hKH₂
  have hK : CharTwo K := charTwo_conjClosure_sup hq.1 h37 h38 hpc₂ hQH₂ hc.oddCore hL₂ hL₂q
  have hKne : pCoreOf 2 K ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hK
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQK.1.trans h1)
  have hsq : IsSQTKIn K :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hKne,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hKne⟩
  have hcgs : cgsIn K Q ≤ K ⊓ M := by
    have h1 : cgsIn K Q ≤ cgsIn H₂ Q :=
      iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
        inf_le_inf_right _ hKH₂
    have h2 : cgsIn K Q ≤ K :=
      iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left
    exact le_inf h2 ((h1.trans (e6_5_two h hc.gamma).1).trans inf_le_right)
  obtain ⟨r, Lb, -, hLb', hprod⟩ := hC129 G K Q (K ⊓ M) hsq hK hQK hcgs inf_le_left
  by_cases hqt : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  swap
  ·
    push Not at hqt
    exfalso
    have hL₂K : L₂ ∈ cComp K :=
      cComp_mem_of_le hL₂ ((le_conjClosure L₂ Q).trans le_sup_left) hKH₂
    have hTC := threeCentral_conjClosure h.qtke h.simple h.nonabelian h36 hq.1 h37 hKne
      le_sup_right hL₂K
    have hOK : pCoreOf 2 K ≤ K ⊓ M :=
      le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
        ((B6.pCoreOf_two_le_of_isSylowTwoOf hQK).trans hQM)
    have hYcM := le_of_all_A3_of_threeCentral (L := Yc) le_sup_left
      (sup_le Subgroup.le_normalizer hQYc) (A3.conjClosure_perfect (perfect_of_mem_cComp hL₂))
      inf_le_left hOK hTC Lb (fun i => ⟨(hLb' i).1.1, hqt i⟩) hprod
    exact hL₂M ((le_conjClosure L₂ Q).trans (hYcM.trans inf_le_right))
  obtain ⟨i, hi⟩ := hqt
  set B := Lb i with hBdef
  have hBi : IsBlock2 K B := (hLb' i).1.1
  have hBc : B ∈ cComp K := L238.mem_cComp_of_isBlock2 hBi hi
  have hBYc : B ≤ Yc := C2Push.le_of_perfect_le_sup hQ2 hQYc (perfect_of_mem_cComp hBc) hBi.2.1
  have hBH₂ : B ∈ cComp H₂ :=
    cComp_mem_of_subnormal hYcsn (cComp_mem_of_le hBc hBYc le_sup_left)
  obtain ⟨q₀, hq₀, hBeq⟩ := exists_eq_map_conj_of_mem_cComp hq.1 h37 hpc₂ hQH₂.1 hL₂ hBH₂ hBYc
  have hLq : L.map (MulAut.conj q₀).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hNL (hQU hq₀))
  have hLB : L ≤ B := by
    rw [hBeq, ← hLq]
    exact Subgroup.map_mono hLL₂
  have hBL₂ : B = L₂ := Vol2Native.lemma_1_2_4_unique hq.1 h37 hpc₂ hLfam hBH₂ hL₂ hLB hLL₂
  have hVL₂ : V ⊓ Subgroup.centralizer (L₂ : Set G) ≤ U := by
    rw [← hCL]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hLL₂)
  have hV₂L₂ : V₂ ≤ V ⊓ Subgroup.centralizer (L₂ : Set G) :=
    le_inf hV₂V (Subgroup.le_centralizer_iff.1 hL₂H₂)
  have hm3 : E3.mQuot V V₂ = 3 := by
    have h1 := E3.card_eq_two_pow_mul h.isPGroup_V hV₂V
    rw [hc.card_V, hc.card_V₂] at h1
    have h2 : 2 ^ E3.mQuot V V₂ = 2 ^ 3 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  have hmlo : 2 ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (L₂ : Set G)) :=
    hn2 ▸ E3.mQuot_mono hVL₂
  have hmhi : E3.mQuot V (V ⊓ Subgroup.centralizer (L₂ : Set G)) ≤ 3 :=
    hm3 ▸ E3.mQuot_mono hV₂L₂
  have hidxW : (V ⊓ Subgroup.centralizer (L₂ : Set G)).relIndex V =
      2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L₂ : Set G)) :=
    E3.relIndex_eq_two_pow h.isPGroup_V _
  have hVB : ¬ V ≤ Subgroup.centralizer (L₂ : Set G) := by
    intro hle'
    rw [inf_eq_left.2 hle', E3.mQuot_self] at hmlo
    omega
  rw [hBL₂] at hBi
  have hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    (e6_5_three h hc.gamma).2 ⟨hKH₂ hg.1, hg.2⟩
  have htypeB := (hLb' i).1.2
  have hBor := (hLb' i).2.1
  rw [← hBdef, hBL₂] at htypeB hBor
  rcases htypeB with ⟨n, hn, hlin⟩ | h3' | h5
  ·
    obtain ⟨hidx, -⟩ := lin2_block_torus hV h.le hQK hQM hKN hK hBi hn hlin hBor hVB
    rw [hidxW] at hidx
    have hnW : E3.mQuot V (V ⊓ Subgroup.centralizer (L₂ : Set G)) = n :=
      Nat.pow_right_injective le_rfl hidx
    have hn23 : n = 2 ∨ n = 3 := by omega
    rcases hn23 with rfl | rfl
    ·
      have hO₂Q : pCoreOf 2 L₂ ≤ Q :=
        (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL₂)).trans
          (B6.pCoreOf_two_le_of_isSylowTwoOf hQH₂)
      have huV : u ∈ V := hU.1 hc.mem_U
      have hL₂u : L₂ ≤ Subgroup.centralizer ({u} : Set G) := by
        intro x hx
        obtain ⟨l, hl⟩ := exists_mul_mem_pCore_of_isLin2Type_two hLL₂ hLlin hlin ⟨x, hx⟩
        have hk : ((Subgroup.inclusion hLL₂ l)⁻¹ * ⟨x, hx⟩ : ↥L₂).1 ∈ Q :=
          hO₂Q ⟨_, by exact hl, rfl⟩
        have hxe : x = (l : G) * ((Subgroup.inclusion hLL₂ l)⁻¹ * ⟨x, hx⟩ : ↥L₂).1 := by
          simp
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hxe]
        have h1 : (l : G) * u = u * l :=
          (Subgroup.mem_centralizer_iff.1 (hLU l.2) u hc.mem_U).symm
        have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2 u huV
        rw [mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]
      have hL₂U : L₂ ≤ Subgroup.centralizer (U : Set G) := by
        rw [hc.centralizer_U]
        exact le_inf hL₂H₂ hL₂u
      by_contra hne
      have hsubL : IsSubnormal L L₂ :=
        A3.subnormal_of_normal hLL₂
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hLL₂).2 (hL₂U.trans hNL))
      have hsubG : IsSubnormal L H₂ := A3.subnormal_trans hsubL (subnormal_of_mem_cComp hL₂)
      have hLne : L ≠ ⊥ := fun h0 => hLM (h0 ▸ bot_le)
      exact not_subnormal_of_mem_cComp hL₂ (lt_of_le_of_ne hLL₂ (Ne.symm hne)) hLne
        (perfect_of_mem_cComp hLcU) hsubG
    ·
      exact absurd hlin (not_isLin2Type_three hLL₂ hLlin)
  ·
    exact absurd (C2Six.natCard_pCore_quotient_of_isAltType_three h3') (hBL₂ ▸ hi)
  ·
    have h1 := relIndex_le_two_of_alt5 hK hBi h5 hQK h.le_inf_centralizer inf_le_right
    rw [hidxW] at h1
    have h4 : 2 ^ 2 ≤ 2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L₂ : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) hmlo
    omega

end E6

end CFSG.Quasithin
