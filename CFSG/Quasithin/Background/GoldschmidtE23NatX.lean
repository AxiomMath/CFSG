module

public import CFSG.Quasithin.Background.GoldschmidtE23NatSyl
public import CFSG.Quasithin.Background.GoldschmidtE23Reg
public import CFSG.Quasithin.Background.GoldschmidtE23Mod
public import CFSG.Quasithin.Background.GoldschmidtE23Fam
public import CFSG.Quasithin.Background.GoldschmidtE23J

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace GE23

section Gen

theorem exists_fixed_elem {G : Type*} [Group G] [Finite G] {T P : Subgroup G} (hT : IsPGroup 2 T)
    {x : G} (hx : x ∈ T) (hPT : P ≤ T) (hPx : x ∈ Subgroup.normalizer (P : Set G))
    (hne : P ≠ ⊥) : ∃ a ∈ P, a ≠ 1 ∧ x * a = a * x := by
  classical
  let Q : Subgroup G := P ⊔ Subgroup.zpowers x
  have hQT : Q ≤ T := sup_le hPT (Subgroup.zpowers_le.2 hx)
  have hQp : IsPGroup 2 ↥Q := hT.to_le hQT
  have : Group.IsNilpotent ↥Q := hQp.isNilpotent
  have hPQ : P ≤ Q := le_sup_left
  have hxQ : x ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hnorm : Q ≤ Subgroup.normalizer (P : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hPx)
  have : (P.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPQ).2 hnorm
  have hne' : P.subgroupOf Q ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro p hp
    have h1 : (⟨p, hPQ hp⟩ : ↥Q) ∈ P.subgroupOf Q := Subgroup.mem_subgroupOf.2 hp
    rw [h] at h1
    have h2 := Subgroup.mem_bot.1 h1
    have h3 : p = 1 := congrArg Subtype.val h2
    rw [h3]
    exact Subgroup.one_mem _
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcen
  refine ⟨(a : G), Subgroup.mem_subgroupOf.1 ha.1, fun h => ha1 ?_, ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have := Subgroup.mem_center_iff.1 ha.2 ⟨x, hxQ⟩
    exact congrArg Subtype.val this

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {Ps : Set (Subgroup (MulAut V))}

theorem exists_min_in (hTX : T ≤ X) (hPs : IsStableFF T Ps) : ∃ B ∈ Ps, IsFFStarMin X B := by
  obtain ⟨B, hBPs, hBmin⟩ := exists_isFFStarMin_mem hPs
  have hBT : B ≤ T := hBmin.1.1
  refine ⟨B, hBPs, isFFStarOffender_mono hTX hBmin.1, fun B' hB'X hFF => ?_⟩
  have hB'B : B' ≤ B := hFF.2.2.1
  have hB'T : IsFFStarOffender T B' := ⟨hB'B.trans hBT, hB'X.2⟩
  exact hBmin.2 B' hB'T ⟨hB'T.isA2, hBmin.1.isA2, hB'B, hFF.2.2.2⟩

structure NatCtx (X T M : Subgroup (MulAut V)) : Prop where
  hB : B69.BlkCtx X T M
  hmp : MinParabolic X T M
  hFF : IsFFModule X
  hns : ¬ Group.IsSolvable ↥X
  hone : ¬ IsStrongFFModule X
  hk2 : ∀ {H : Subgroup (MulAut V)} {k : ℕ}, SymBlk X H k → k = 2
  hnat : ∀ L, CFSG.Open.IsComponentOf L X → NatComp X L

namespace NatCtx

variable (hC : NatCtx X T M)

include hC

theorem sc : B69.StructConcl X T M (B69.blkFamily X) :=
  B69.structConcl_of_blkCtx hC.hB hC.hmp hC.hFF

theorem blk_comp {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) :
    CFSG.Open.IsComponentOf H X ∧ NatComp X H := by
  obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hH
  have hN := hC.hnat L hL
  rw [hN.1]
  exact ⟨hL, hN⟩

theorem twoResidual_eq_ffJ : twoResidual X = ffJ X := by
  refine le_antisymm (hC.hmp.twoResidual_le_ffJ hC.hB.hO2 hC.hFF) ?_
  rw [(hC.sc).2.1]
  exact iSup₂_le fun H hH => component_le_twoResidual (hC.blk_comp hH).1

theorem exists_sylow (hPs : IsStableFF T Ps) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) : ∃ P ∈ Ps, IsSylowTwoOf P L ∧ P ≤ T := by
  obtain ⟨B, hBPs, hBmin⟩ := exists_min_in hC.hmp.isSylow.1 hPs
  obtain ⟨L₀, hL₀, hLB⟩ := B69.exists_component_of_nonsolvable hC.hB.hV hC.hB.hP4 hC.hmp
    hC.hB.hO2 hC.hns hBmin
  obtain ⟨-, e, -, -, hall⟩ := hC.hnat L₀ hL₀
  have hsyl : IsSylowTwoOf B L₀ := hall B hBmin hLB
  obtain ⟨t, ht, hconj⟩ := B69.exists_conj_component hC.hmp hL₀ hL
  have hPs' : B6.conjSub t B ∈ Ps := hPs.2.2.1 B hBPs t ht
  refine ⟨B6.conjSub t B, hPs', ?_, (hPs.2.1 _ hPs').1⟩
  have := B6.isSylowTwoOf_conjSub hsyl t
  rwa [hconj] at this

omit [Finite V] hC in
theorem ffJP_le_T : ffJP Ps T ≤ T :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun hAT => hAT

omit [Finite V] in
theorem ffJP_le_ffJ (hPs : IsStableFF T Ps) : ffJP Ps T ≤ ffJ X :=
  iSup_le fun A => iSup_le fun hA => iSup_le fun _ =>
    B19.le_ffJ (isFFStarOffender_mono hC.hmp.isSylow.1 (hPs.2.1 A hA))

omit [Finite V] hC in
theorem le_normalizer_ffJP (hPs : IsStableFF T Ps) :
    T ≤ Subgroup.normalizer (ffJP Ps T : Set (MulAut V)) := fun t ht =>
  B6.mem_normalizer_of_forall_mem (fun x hx => B1Red.ffJP_conj_mem hPs ht hx)
    (fun x hx => by
      have := B1Red.ffJP_conj_mem hPs (T.inv_mem ht) hx
      simpa using this)

theorem exists_fam (hPs : IsStableFF T Ps) :
    ∃ P : Subgroup (MulAut V) → Subgroup (MulAut V), ∀ H ∈ B69.blkFamily X,
      P H ∈ Ps ∧ IsSylowTwoOf (P H) H ∧ P H ≤ T := by
  classical
  have hex : ∀ H : Subgroup (MulAut V), ∃ P : Subgroup (MulAut V), H ∈ B69.blkFamily X →
      (P ∈ Ps ∧ IsSylowTwoOf P H ∧ P ≤ T) := by
    intro H
    by_cases hH : H ∈ B69.blkFamily X
    · obtain ⟨P, hP1, hP2, hP3⟩ := hC.exists_sylow hPs (hC.blk_comp hH).1
      exact ⟨P, fun _ => ⟨hP1, hP2, hP3⟩⟩
    · exact ⟨⊥, fun h => absurd h hH⟩
  choose P hP using hex
  exact ⟨P, hP⟩

theorem J_sylow (hPs : IsStableFF T Ps) :
    ∃ P : Subgroup (MulAut V) → Subgroup (MulAut V),
      (∀ H ∈ B69.blkFamily X, P H ∈ Ps ∧ IsSylowTwoOf (P H) H ∧ P H ≤ ffJP Ps T) ∧
      ffJP Ps T = ⨆ H ∈ B69.blkFamily X, P H ∧
      IsSylowTwoOf (ffJP Ps T) (ffJ X) ∧ ffJP Ps T = T ⊓ ffJ X := by
  classical
  obtain ⟨P, hP⟩ := hC.exists_fam hPs
  have hsc := hC.sc
  have hPJ : ∀ H ∈ B69.blkFamily X, P H ≤ ffJP Ps T := fun H hH =>
    B19.le_ffJP (hP H hH).1 (hP H hH).2.2
  have hJPJ : (⨆ H ∈ B69.blkFamily X, P H) ≤ ffJP Ps T := iSup₂_le fun H hH => hPJ H hH
  have hsylJP : IsSylowTwoOf (⨆ H ∈ B69.blkFamily X, P H) (ffJ X) := by
    rw [hsc.2.1]
    exact isSylowTwoOf_iSup (B69.blkFamily X) (fun H => H) P (fun H hH => (hP H hH).2.1)
      hsc.2.2.1 hsc.2.2.2.1
  have hT2 : IsPGroup 2 T := hC.hmp.isSylow.2.1
  have hJle : ffJP Ps T ≤ T := ffJP_le_T
  have hJeq : ffJP Ps T = ⨆ H ∈ B69.blkFamily X, P H :=
    eq_of_isSylowTwoOf_le hsylJP hJPJ (hC.ffJP_le_ffJ hPs) (hT2.to_le hJle)
  refine ⟨P, fun H hH => ⟨(hP H hH).1, (hP H hH).2.1, hPJ H hH⟩, hJeq, ?_, ?_⟩
  · rw [hJeq]
    exact hsylJP
  · have hW : T ⊓ ffJ X = ⨆ H ∈ B69.blkFamily X, P H :=
      eq_of_isSylowTwoOf_le hsylJP (le_inf (hJPJ.trans hJle) (hJPJ.trans (hC.ffJP_le_ffJ hPs)))
        inf_le_right (hT2.to_le inf_le_left)
    rw [hJeq, hW]

end NatCtx

omit [Finite V] in
theorem card_le_of_offender {X A : Subgroup (MulAut V)} (h : IsFFStarOffender X A) :
    Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  have := h.card_le (bot_le : ⊥ ≤ A)
  simpa [B1.fixV_bot, Subgroup.card_bot] using this

theorem block_facts {H P : Subgroup (MulAut V)} (hN : NatComp X H)
    (hP : IsSylowTwoOf P H) (hPoff : IsFFStarOffender X P) :
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card P = 2 ^ e ∧
      (∀ a ∈ P, a ≠ 1 → ∀ u ∈ commV H, a u = u → u ∈ fixV P) ∧
      (∀ a ∈ P, ∀ u ∈ commV H, a u * u⁻¹ ∈ fixV P) ∧
      (∃ u ∈ commV H, u ∈ fixV P ∧ u ∉ fixV (ffJ X)) ∧
      (∃ w ∈ H, H ≤ P ⊔ P.map (MulAut.conj w).toMonoidHom) ∧
      Nat.card ↥(commV H) = Nat.card ↥(commV H ⊓ fixV (ffJ X)) * 4 ^ e := by
  obtain ⟨-, e, -, hdata, -⟩ := hN
  have hS := exists_natSyl hdata hP
  have hPle : P ≤ ffJ X := B19.le_ffJ hPoff
  have hZP : commV H ⊓ fixV (ffJ X) ≤ fixV P := fun u hu => B1.fixV_le_fixV hPle hu.2
  obtain ⟨hA, hB, hC', hD, hE, he1, hF⟩ := hS.facts hZP (card_le_of_offender hPoff)
  refine ⟨e, he1, hE, hA, hB, ?_, hD, ?_⟩
  · obtain ⟨u, hu, hfix, hnZ⟩ := hC'
    exact ⟨u, hu, hfix, fun h => hnZ ⟨hu, h⟩⟩
  · rw [hF, inf_eq_left.2 inf_le_left]

theorem NatCtx.trivial_action {X T M : Subgroup (MulAut V)} {Ps : Set (Subgroup (MulAut V))}
    (hC : NatCtx X T M) (hPs : IsStableFF T Ps) :
    ∀ x ∈ T ⊓ centSub (fixV (ffJP Ps T)), ∀ v : V, x v * v⁻¹ ∈ fixV (ffJP Ps T) := by
  classical
  intro x hx
  obtain ⟨P, hP, hJeq, hJsyl, hJT⟩ := hC.J_sylow hPs
  have hsc := hC.sc
  have hT2 : IsPGroup 2 T := hC.hmp.isSylow.2.1
  set J := ffJP Ps T with hJdef
  set I := B69.blkFamily X with hI
  have hxT : x ∈ T := hx.1
  have hxX : x ∈ X := hC.hmp.isSylow.1 hxT
  have hxcent : ∀ z ∈ fixV J, x z = z := fun z hz => mem_centSub.1 hx.2 z hz
  have hJle : J ≤ T := NatCtx.ffJP_le_T
  have hPoff : ∀ H ∈ I, IsFFStarOffender X (P H) := fun H hH =>
    isFFStarOffender_mono hC.hmp.isSylow.1 (hPs.2.1 _ (hP H hH).1)
  have hPJ : ∀ H ∈ I, P H ≤ J := fun H hH => (hP H hH).2.2
  have hJH : ∀ H ∈ I, J ⊓ H = P H := fun H hH =>
    eq_of_isSylowTwoOf_le (hP H hH).2.1 (le_inf (hPJ H hH) (hP H hH).2.1.1) inf_le_right
      (hT2.to_le (inf_le_left.trans hJle))
  have hfixJ : ∀ z : V, (∀ H ∈ I, ∀ p ∈ P H, p z = z) → z ∈ fixV J := by
    intro z hz
    have : J ≤ MulAction.stabilizer (MulAut V) z := by
      rw [hJeq]
      exact iSup₂_le fun H hH p hp => hz H hH p hp
    exact fun y hy => this hy
  have hother : ∀ H ∈ I, ∀ H' ∈ I, H' ≠ H → ∀ y ∈ H', ∀ u ∈ commV H, y u = u := by
    intro H hH H' hH' hne y hy u hu
    exact commSub_eq_bot_iff.1 (hsc.2.2.2.2.2.2.1 H hH H' hH' (Ne.symm hne)) hu y hy
  have hsplit : ∀ H ∈ I, ∀ v : V, ∃ w ∈ commV H, ∃ c ∈ fixV H, v = w * c := by
    intro H hH v
    obtain ⟨w, hw, c, hc, hv⟩ := blocks_split hC.hB hC.hmp hC.hFF hC.hk2 {H}
      (fun H' hH' => by rw [Finset.mem_singleton.1 hH']; exact hH) v
    refine ⟨w, ?_, c, ?_, hv⟩
    · simpa using hw
    · simpa using hc
  have hblock : ∀ H ∈ I, ∃ a : MulAut V, x * a = a * x ∧ (∀ v : V, a v * v⁻¹ ∈ fixV J) ∧
      ∀ v : V, a v = v → ∀ p ∈ P H, p v = v := by
    intro H hH
    obtain ⟨hHcomp, hHnat⟩ := hC.blk_comp hH
    obtain ⟨e, he1, hcard, hA, hB, hC', -, -⟩ :=
      block_facts hHnat (hP H hH).2.1 (hPoff H hH)
    have hxH : B6.conjSub x H = H := by
      by_contra hne
      obtain ⟨z, hzU, hzP, hzZ⟩ := hC'
      have hzJ : z ∈ fixV J := by
        refine hfixJ z fun H' hH' p hp => ?_
        by_cases hHH : H' = H
        · subst hHH
          exact hzP p hp
        · exact hother H hH H' hH' hHH p ((hP H' hH').2.1.1 hp) z hzU
      have hxz : x z = z := hxcent z hzJ
      have hH'comp : CFSG.Open.IsComponentOf (B6.conjSub x H) X :=
        B113.isComponentOf_conj hHcomp hxX
      have hH'blk : B69.blk X (B6.conjSub x H) = B6.conjSub x H := by
        rw [← B69.conjSub_blk hxX, hHnat.1]
      have hH'I : B6.conjSub x H ∈ I := B69.mem_blkFamily.2 ⟨_, hH'comp, hH'blk.symm⟩
      have hcomm' : commV (B6.conjSub x H) = (commV H).map x.toMonoidHom :=
        B19.commV_map_conj x H
      have hzH' : z ∈ commV (B6.conjSub x H) := by
        rw [hcomm']
        exact ⟨z, hzU, hxz⟩
      have hind := inf_le_fixV_twoResidual hC.hB hC.hmp hC.hFF hC.hns hH
      have hz1 : z ∈ fixV (twoResidual X) := by
        refine hind ⟨hzU, ?_⟩
        exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun H'' (_ : H'' ∈ I) =>
          ⨆ (_ : H'' ≠ H), commV H'') (B6.conjSub x H) hH'I
          (le_iSup_of_le hne le_rfl) hzH')
      rw [hC.twoResidual_eq_ffJ] at hz1
      exact hzZ hz1
    have hxH2 : B6.conjSub x⁻¹ H ≤ H := by
      have : B6.conjSub x⁻¹ H = H := by
        calc B6.conjSub x⁻¹ H = B6.conjSub x⁻¹ (B6.conjSub x H) := by rw [hxH]
          _ = H := B69.conjSub_inv_conjSub x H
      exact this.le
    have hxH' : x ∈ Subgroup.normalizer (H : Set (MulAut V)) :=
      B6.mem_normalizer_of_conjSub_le hxH.le hxH2
    have hxPH : x ∈ Subgroup.normalizer (P H : Set (MulAut V)) := by
      rw [← hJH H hH]
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨NatCtx.le_normalizer_ffJP hPs hxT, hxH'⟩
    have hPne : P H ≠ ⊥ := by
      intro h
      have h1 : Nat.card (P H) = 1 := by rw [h]; simp
      rw [hcard] at h1
      have : e = 0 := Nat.pow_eq_one.1 h1 |>.resolve_left (by norm_num)
      omega
    obtain ⟨a, haP, ha1, hxa⟩ := exists_fixed_elem hT2 hxT ((hPJ H hH).trans hJle) hxPH hPne
    have haH : a ∈ H := (hP H hH).2.1.1 haP
    refine ⟨a, hxa, ?_, ?_⟩
    · intro v
      obtain ⟨w, hw, c, hc, rfl⟩ := hsplit H hH v
      have hac : a c = c := hc a haH
      have e1 : a (w * c) * (w * c)⁻¹ = a w * w⁻¹ := by
        rw [map_mul, hac, mul_inv_rev]
        calc a w * c * (c⁻¹ * w⁻¹) = a w * w⁻¹ * (c * c⁻¹) := by ac_rfl
          _ = a w * w⁻¹ := by rw [mul_inv_cancel, mul_one]
      rw [e1]
      refine hfixJ _ fun H' hH' p hp => ?_
      by_cases hHH : H' = H
      · subst hHH
        exact hB a haP w hw p hp
      · exact hother H hH H' hH' hHH p ((hP H' hH').2.1.1 hp) _
          (Subgroup.subset_closure ⟨a, haH, w, rfl⟩)
    · intro v hav p hp
      obtain ⟨w, hw, c, hc, rfl⟩ := hsplit H hH v
      have hac : a c = c := hc a haH
      have hpc : p c = c := hc p ((hP H hH).2.1.1 hp)
      rw [map_mul, hac] at hav
      have haw : a w = w := mul_right_cancel hav
      have := hA a haP ha1 w hw haw p hp
      rw [map_mul, this, hpc]
  choose! a ha using hblock
  exact fun v => trivial_of_commuting (Z := fixV J) hxcent (ι := ↥I) (fun h => a h.1)
    (fun h => (ha h.1 h.2).1) (fun h v => (ha h.1 h.2).2.1 v)
    (fun v hv => hfixJ v fun H hH p hp => (ha H hH).2.2 v (hv ⟨H, hH⟩) p hp) v

theorem card_iSup_blocks {X T M : Subgroup (MulAut V)}
    (hsc : B69.StructConcl X T M (B69.blkFamily X)) (P : Subgroup (MulAut V) → Subgroup (MulAut V))
    (hPH : ∀ H ∈ B69.blkFamily X, P H ≤ H) :
    Nat.card ↥(⨆ H ∈ B69.blkFamily X, P H) = ∏ H ∈ B69.blkFamily X, Nat.card ↥(P H) := by
  classical
  refine card_iSup_of_indep (B69.blkFamily X) P
    (fun i hi j hj hij a ha b hb => hsc.2.2.1 i hi j hj hij a (hPH i hi ha) b (hPH j hj hb))
    (fun i hi => le_bot_iff.1 ?_)
  calc P i ⊓ ⨆ j ∈ B69.blkFamily X, ⨆ (_ : j ≠ i), P j ≤
      i ⊓ ⨆ j ∈ B69.blkFamily X, ⨆ (_ : j ≠ i), j :=
      inf_le_inf (hPH i hi) (iSup₂_mono fun j hj => iSup_mono fun _ => hPH j hj)
    _ = ⊥ := hsc.2.2.2.1 i hi

theorem NatCtx.card_le_J {X T M : Subgroup (MulAut V)} {Ps : Set (Subgroup (MulAut V))}
    (hC : NatCtx X T M) (hPs : IsStableFF T Ps) :
    Nat.card V ≤ Nat.card (ffJP Ps T) * Nat.card (fixV (ffJP Ps T)) := by
  classical
  obtain ⟨P, hP, hJeq, -, -⟩ := hC.J_sylow hPs
  have hsc := hC.sc
  have hPH : ∀ H ∈ B69.blkFamily X, P H ≤ H := fun H hH => (hP H hH).2.1.1
  have hcard : Nat.card (ffJP Ps T) = ∏ H ∈ B69.blkFamily X, Nat.card (P H) := by
    rw [hJeq]
    exact card_iSup_blocks hsc P hPH
  have hfix : fixV (ffJP Ps T) = ⨅ H ∈ B69.blkFamily X, fixV (P H) := by
    ext z
    simp only [Subgroup.mem_iInf, mem_fixV]
    constructor
    · intro hz H hH p hp
      exact hz p (hP H hH |>.2.2 hp)
    · intro hz p hp
      have : ffJP Ps T ≤ MulAction.stabilizer (MulAut V) z := by
        rw [hJeq]
        exact iSup₂_le fun H hH q hq => hz H hH q hq
      exact this hp
  have hidx : ∀ s : Finset (Subgroup (MulAut V)), s ⊆ B69.blkFamily X →
      (⨅ H ∈ s, fixV (P H)).index ≤ ∏ H ∈ s, Nat.card (P H) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.iInf_insert, Finset.prod_insert ha]
      refine Subgroup.index_inf_le.trans ?_
      have h1 : (fixV (P a)).index ≤ Nat.card (P a) := by
        have hoff := card_le_of_offender (isFFStarOffender_mono hC.hmp.isSylow.1
          (hPs.2.1 _ (hP a (hs (Finset.mem_insert_self a s))).1))
        have hm := Subgroup.card_mul_index (fixV (P a))
        have hpos : 0 < Nat.card (fixV (P a)) := Nat.card_pos
        refine Nat.le_of_mul_le_mul_left ?_ hpos
        calc Nat.card (fixV (P a)) * (fixV (P a)).index = Nat.card V := hm
          _ ≤ Nat.card (P a) * Nat.card (fixV (P a)) := hoff
          _ = Nat.card (fixV (P a)) * Nat.card (P a) := mul_comm _ _
      exact Nat.mul_le_mul h1 (ih fun x hx => hs (Finset.mem_insert_of_mem hx))
  have hm := Subgroup.card_mul_index (fixV (ffJP Ps T))
  have hle := hidx (B69.blkFamily X) subset_rfl
  rw [← hfix] at hle
  rw [hcard]
  calc Nat.card V = Nat.card (fixV (ffJP Ps T)) * (fixV (ffJP Ps T)).index := hm.symm
    _ ≤ Nat.card (fixV (ffJP Ps T)) * ∏ H ∈ B69.blkFamily X, Nat.card (P H) :=
        Nat.mul_le_mul_left _ hle
    _ = (∏ H ∈ B69.blkFamily X, Nat.card (P H)) * Nat.card (fixV (ffJP Ps T)) := mul_comm _ _

theorem NatCtx.centSub_eq {X T M : Subgroup (MulAut V)} {Ps : Set (Subgroup (MulAut V))}
    (hC : NatCtx X T M) (hPs : IsStableFF T Ps) :
    T ⊓ centSub (fixV (ffJP Ps T)) = ffJP Ps T := by
  have hJle : ffJP Ps T ≤ T := NatCtx.ffJP_le_T
  have hJc : ffJP Ps T ≤ centSub (fixV (ffJP Ps T)) := fun j hj z hz => hz j hj
  have hne : ffJP Ps T ≠ ⊥ := by
    obtain ⟨B, hB⟩ := hPs.1
    intro h
    have : B ≤ ffJP Ps T := B19.le_ffJP hB (hPs.2.1 B hB).1
    rw [h] at this
    exact (hPs.2.1 B hB).2.1 (le_bot_iff.1 this)
  exact eq_of_trivial_action hC.hB.hV hC.hone (inf_le_left.trans hC.hmp.isSylow.1)
    (le_inf hJle hJc) hne (hC.card_le_J hPs) (fun x hx z hz => mem_centSub.1 hx.2 z hz)
    (hC.trivial_action hPs)

theorem NatCtx.generation {X T M : Subgroup (MulAut V)} {Ps : Set (Subgroup (MulAut V))}
    (hC : NatCtx X T M) (hPs : IsStableFF T Ps) :
    ∃ g ∈ ffJ X, ∀ H ∈ B69.blkFamily X,
      H ≤ ffJP Ps T ⊔ (ffJP Ps T).map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨P, hP, -, -, -⟩ := hC.J_sylow hPs
  have hsc := hC.sc
  have hgen : ∀ H ∈ B69.blkFamily X, ∃ w ∈ H, H ≤ P H ⊔ (P H).map (MulAut.conj w).toMonoidHom := by
    intro H hH
    obtain ⟨e, -, -, -, -, -, hD, -⟩ := block_facts (hC.blk_comp hH).2 (hP H hH).2.1
      (isFFStarOffender_mono hC.hmp.isSylow.1 (hPs.2.1 _ (hP H hH).1))
    exact hD
  obtain ⟨g, hg, hgP⟩ := exists_conj_gen (B69.blkFamily X) P hsc.2.2.1
    (fun H hH => (hP H hH).2.1.1) hgen
  refine ⟨g, by rw [hsc.2.1]; exact hg, fun H hH => (hgP H hH).trans ?_⟩
  exact sup_le_sup (hP H hH).2.2 (Subgroup.map_mono (hP H hH).2.2)

theorem NatCtx.two_mul_rkIdx_le {X T M : Subgroup (MulAut V)} {Ps : Set (Subgroup (MulAut V))}
    (hC : NatCtx X T M) (hPs : IsStableFF T Ps) :
    2 * rkIdx (fixV (ffJP Ps T)) ≤ rkIdx (fixV (ffJ X)) := by
  classical
  obtain ⟨P, hP, hJeq, -, -⟩ := hC.J_sylow hPs
  have hsc := hC.sc
  have hV := hC.hB.hV
  set I := B69.blkFamily X with hI
  have hPoff : ∀ H ∈ I, IsFFStarOffender X (P H) := fun H hH =>
    isFFStarOffender_mono hC.hmp.isSylow.1 (hPs.2.1 _ (hP H hH).1)
  have hfact : ∀ H ∈ I, ∃ e : ℕ, Nat.card ↥(P H) = 2 ^ e ∧
      Nat.card ↥(commV H) = Nat.card ↥(commV H ⊓ fixV (ffJ X)) * 4 ^ e := by
    intro H hH
    obtain ⟨e, -, h1, -, -, -, -, h2⟩ := block_facts (hC.blk_comp hH).2 (hP H hH).2.1 (hPoff H hH)
    exact ⟨e, h1, h2⟩
  choose! e he using hfact
  have hJcard : Nat.card (ffJP Ps T) = 2 ^ (∑ H ∈ I, e H) := by
    rw [hJeq, card_iSup_blocks hsc P (fun H hH => (hP H hH).2.1.1),
      Finset.prod_congr rfl fun H hH => (he H hH).1, Finset.prod_pow_eq_pow_sum]
  have hidx : rkIdx (fixV (ffJP Ps T)) ≤ ∑ H ∈ I, e H := by
    have h1 := hC.card_le_J hPs
    have hm := Subgroup.card_mul_index (fixV (ffJP Ps T))
    have hpos : 0 < Nat.card (fixV (ffJP Ps T)) := Nat.card_pos
    have h2 : (fixV (ffJP Ps T)).index ≤ Nat.card (ffJP Ps T) := by
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      calc Nat.card (fixV (ffJP Ps T)) * (fixV (ffJP Ps T)).index = Nat.card V := hm
        _ ≤ Nat.card (ffJP Ps T) * Nat.card (fixV (ffJP Ps T)) := h1
        _ = Nat.card (fixV (ffJP Ps T)) * Nat.card (ffJP Ps T) := mul_comm _ _
    rw [B1.index_eq_two_pow hV, hJcard] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hrk : ∀ s : Finset (Subgroup (MulAut V)), s ⊆ I →
      rk ↥(fixV (ffJ X) ⊔ ⨆ H ∈ s, commV H) = rk ↥(fixV (ffJ X)) + ∑ H ∈ s, 2 * e H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have h0 : (⨆ H ∈ (∅ : Finset (Subgroup (MulAut V))), commV H) = ⊥ := by simp
      rw [h0, sup_bot_eq, Finset.sum_empty, add_zero]
    | insert a s ha ih =>
      intro hs
      have haI : a ∈ I := hs (Finset.mem_insert_self a s)
      have hsI : s ⊆ I := fun x hx => hs (Finset.mem_insert_of_mem hx)
      have ih' := ih hsI
      set W := fixV (ffJ X) ⊔ ⨆ H ∈ s, commV H with hW
      have e1 := rk_sup_add_rk_inf W (commV a)
      have hinf : W ⊓ commV a = commV a ⊓ fixV (ffJ X) := by
        refine le_antisymm ?_ (le_inf (le_sup_left.trans' inf_le_right) inf_le_left)
        intro x hx
        refine ⟨hx.2, ?_⟩
        have hind := inf_le_fixV_twoResidual hC.hB hC.hmp hC.hFF hC.hns haI
        rw [hC.twoResidual_eq_ffJ] at hind
        refine hind ⟨hx.2, ?_⟩
        have hsub : (⨆ H ∈ s, commV H) ≤ ⨆ H' ∈ I, ⨆ (_ : H' ≠ a), commV H' := by
          refine iSup₂_le fun H hH => ?_
          exact le_iSup₂_of_le (f := fun H' (_ : H' ∈ I) => ⨆ (_ : H' ≠ a), commV H') H (hsI hH)
            (le_iSup_of_le (fun h => ha (h ▸ hH)) le_rfl)
        exact (sup_le_sup_left hsub (fixV (ffJ X))) hx.1
      have e2 : fixV (ffJ X) ⊔ ⨆ H ∈ insert a s, commV H = W ⊔ commV a := by
        rw [Finset.iSup_insert, hW]
        ac_rfl
      have hF := (he a haI).2
      have e3 : rk ↥(commV a) = rk ↥(commV a ⊓ fixV (ffJ X)) + 2 * e a := by
        unfold rk
        rw [hF, padicValNat.mul (Nat.card_pos).ne' (pow_pos (by norm_num) _).ne',
          show (4 : ℕ) ^ e a = 2 ^ (2 * e a) by rw [pow_mul]; norm_num, padicValNat.prime_pow]
      rw [e2, Finset.sum_insert ha]
      rw [hinf] at e1
      omega
  have htop : fixV (ffJ X) ⊔ ⨆ H ∈ I, commV H = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, c, hc, rfl⟩ := blocks_split hC.hB hC.hmp hC.hFF hC.hk2 I (fun _ h => h) v
    have hc' : c ∈ fixV (ffJ X) := by
      rw [← hsc.2.1] at hc
      exact hc
    rw [mul_comm]
    exact Subgroup.mul_mem_sup hc' hw
  have hfull := hrk I subset_rfl
  rw [htop, rk_top] at hfull
  have hadd := rk_add_rkIdx (fixV (ffJ X))
  have hsum : ∑ H ∈ I, 2 * e H = 2 * ∑ H ∈ I, e H := by rw [Finset.mul_sum]
  omega

end Gen

end GE23

end CFSG.Quasithin
