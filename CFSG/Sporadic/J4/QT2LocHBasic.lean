module

public import CFSG.Sporadic.J4.QT2LocBasicRep
public import CFSG.Sporadic.J4.QTRankInvBasic
public import CFSG.Sporadic.J4.QT2ARad
public import CFSG.Sporadic.J4.QT2LocCntMainBase
public import CFSG.Sporadic.J4.QT2LocRadMainBase

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem caseII_b
    (hF : J4Basic) {k : ℕ}
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) {V : Subgroup J}
    {d : J} (hc : HCfg V (fiveElt ^ k) d) (hVE : V ≤ Eg uJ 11) : HConcl V (fiveElt ^ k) d := by
  have hM := hF.mat
  have hξV := xi_conj_mem hM hk hc.hVx
  have hξfpf := xi_fpf hc.hfpf
  obtain ⟨td, hAd⟩ := acts_exists_of_mem_Hj hM d hc.hd
  have htd : td ∈ isetT := iset_complete_b hF hc.hd hc.hd2 hAd
  have hAx := acts_xiK hM k
  have hAxd : Acts (fiveElt ^ k * d) (compT (xiK k) td) := hAx.mul hAd
  have hcube : cubeT (compT (xiK k) td) = idT := by
    have h1 := acts_pow hAxd 3
    have h2 : Acts ((fiveElt ^ k * d) ^ 3) idT := Acts.of_mem_Eg hM (hVE hc.hxd)
    exact Acts.unique hM h1 h2
  have hAξ := acts_xi hM
  obtain ⟨Sset, hSset⟩ : ∃ S : Set ℕ, ∀ c, c ∈ S ↔ c < 2048 ∧ eta uJ 11 c ∈ V :=
    ⟨{c | c < 2048 ∧ eta uJ 11 c ∈ V}, fun c => Iff.rfl⟩
  have h0 : 0 ∈ Sset := (hSset 0).2 ⟨by norm_num, by rw [eta_zero]; exact V.one_mem⟩
  have hx : ∀ a ∈ Sset, ∀ b ∈ Sset, a ^^^ b ∈ Sset := by
    intro a ha b hb
    have ha' := (hSset a).1 ha
    have hb' := (hSset b).1 hb
    refine (hSset _).2 ⟨Nat.xor_lt_two_pow (n := 11) ha'.1 hb'.1, ?_⟩
    rw [eta_xor (elem_uJ hM) (m := 11) le_rfl a b]
    exact V.mul_mem ha'.2 hb'.2
  have hξ : ∀ c ∈ Sset, actT xiT c ∈ Sset := by
    intro c hcS
    have hcS' := (hSset c).1 hcS
    refine (hSset _).2 ⟨by simpa using actT_lt hAξ.1 c, ?_⟩
    have := hξV _ hcS'.2
    rwa [hAξ.2 c hcS'.1] at this
  have hdS : ∀ c ∈ Sset, actT td c ∈ Sset := by
    intro c hcS
    have hcS' := (hSset c).1 hcS
    refine (hSset _).2 ⟨by simpa using actT_lt hAd.1 c, ?_⟩
    have := hc.hVd _ hcS'.2
    rwa [hAd.2 c hcS'.1] at this
  have hfpf : ∀ c ∈ Sset, c ≠ 0 → actT xiT c ≠ c := by
    intro c hcS hc0 heq
    have hcS' := (hSset c).1 hcS
    have h1 := hAξ.2 c hcS'.1
    rw [heq] at h1
    have h2 : fiveElt * eta uJ 11 c = eta uJ 11 c * fiveElt := by
      calc fiveElt * eta uJ 11 c = (fiveElt * eta uJ 11 c * fiveElt⁻¹) * fiveElt := by group
        _ = eta uJ 11 c * fiveElt := by rw [h1]
    have h3 := hξfpf _ hcS'.2 h2
    rw [← eta_zero uJ 11] at h3
    exact hc0 (eta_inj hM c hcS'.1 0 (by norm_num) h3)
  have hlt : ∀ c ∈ Sset, c < 2048 := fun c hcS => ((hSset c).1 hcS).1
  have hcard : Sset.ncard = 16 := by
    have himg : (fun c => eta uJ 11 c) '' Sset = (V : Set J) := by
      ext v
      constructor
      · rintro ⟨c, hcS, rfl⟩
        exact ((hSset c).1 hcS).2
      · intro hv
        obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hVE hv)
        exact ⟨c, (hSset c).2 ⟨hcl, hv⟩, rfl⟩
    have hinj : Set.InjOn (fun c => eta uJ 11 c) Sset := fun a ha b hb e =>
      eta_inj hM a ((hSset a).1 ha).1 b ((hSset b).1 hb).1 e
    rw [← Set.InjOn.ncard_image hinj, himg]
    have := hc.hVcard
    rw [← this]
    exact (Nat.card_coe_set_eq (V : Set J)).symm
  obtain ⟨S, hS, hSeq⟩ := exists_line h0 hx hξ hfpf hlt hcard
  have hdur : ∀ s ∈ S, actT td s ∈ S := fun s hs => (hSeq _).2 (hdS s ((hSeq s).1 hs))
  rcases caseII_check hk htd hcube with ⟨c, hcd, hc1, hc2⟩ | hno
  · exact hconcl_of_duad hM hAx hAd hcd hc1 hc2 fun v hv =>
      ⟨idT, Acts.of_mem_Eg hM (hVE hv), actT_idT (duad_props c hcd).2⟩
  · exfalso
    obtain ⟨v, hv, hv1, hvf⟩ := hc.hfix
    obtain ⟨s0, hs0lt, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hVE hv)
    have hs0S : s0 ∈ S := (hSeq s0).2 ((hSset s0).2 ⟨hs0lt, hv⟩)
    have hs0ne : s0 ≠ 0 := by
      intro h
      apply hv1
      rw [h, eta_zero]
    have h1 := hno S hS hdur s0 hs0S
    rcases h1 with h2 | h3
    · exact hs0ne h2
    · apply h3
      have h4 := hAxd.2 s0 hs0lt
      have h5 : fiveElt ^ k * d * eta uJ 11 s0 * (fiveElt ^ k * d)⁻¹ = eta uJ 11 s0 := by
        calc fiveElt ^ k * d * eta uJ 11 s0 * (fiveElt ^ k * d)⁻¹ =
            ((fiveElt ^ k * d) * eta uJ 11 s0) * (fiveElt ^ k * d)⁻¹ := rfl
          _ = (eta uJ 11 s0 * (fiveElt ^ k * d)) * (fiveElt ^ k * d)⁻¹ := by rw [hvf]
          _ = eta uJ 11 s0 := by group
      rw [h5] at h4
      exact (eta_inj hM s0 hs0lt _ (actT_lt hAxd.1 s0) h4).symm

theorem caseI_b
    (hF : J4Basic) {k : ℕ}
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) {V : Subgroup J}
    {d : J} (hc : HCfg V (fiveElt ^ k) d) (hVE : V ⊓ Eg uJ 11 = ⊥) :
    HConcl V (fiveElt ^ k) d := by
  have hM := hF.mat
  have hξV := xi_conj_mem hM hk hc.hVx
  have hξfpf := xi_fpf hc.hfpf
  obtain ⟨td, hAd⟩ := acts_exists_of_mem_Hj hM d hc.hd
  have htd : td ∈ isetT := iset_complete_b hF hc.hd hc.hd2 hAd
  have hAx := acts_xiK hM k
  have hAxd : Acts (fiveElt ^ k * d) (compT (xiK k) td) := hAx.mul hAd
  obtain ⟨TV, hTV⟩ : ∃ T : Set (List ℕ), ∀ t, t ∈ T ↔ ∃ v ∈ V, Acts v t :=
    ⟨{t | ∃ v ∈ V, Acts v t}, fun t => Iff.rfl⟩
  have hTV1 : idT ∈ TV := (hTV _).2 ⟨1, V.one_mem, Acts.one⟩
  have hTVmul : ∀ t ∈ TV, ∀ t' ∈ TV, compT t t' ∈ TV := by
    intro t ht t' ht'
    obtain ⟨v, hv, hA⟩ := (hTV t).1 ht
    obtain ⟨v', hv', hA'⟩ := (hTV t').1 ht'
    exact (hTV _).2 ⟨v * v', V.mul_mem hv hv', hA.mul hA'⟩
  have hTVi : ∀ t ∈ TV, t ∈ isetT := by
    intro t ht
    obtain ⟨v, hv, hA⟩ := (hTV t).1 ht
    exact iset_complete_b hF (hc.hVH hv) (hc.hV2 v hv) hA
  obtain ⟨v0, hv0, hv0ne⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 fun v hv => by
      by_contra hne
      exact hcon ⟨v, hv, hne⟩
    have h16 := hc.hVcard
    rw [hbot] at h16
    simp at h16
  obtain ⟨y0, hAy0⟩ := acts_exists_of_mem_Hj hM v0 (hc.hVH hv0)
  have hy0TV : y0 ∈ TV := (hTV _).2 ⟨v0, hv0, hAy0⟩
  have hy0I : y0 ∈ isetT := hTVi _ hy0TV
  have hy0ne : y0 ≠ idT := by
    intro h
    rw [h] at hAy0
    have hmem : v0 ∈ Eg uJ 11 := by
      refine centralizer_Hj_b hF v0 (hc.hVH hv0) fun y hy => ?_
      obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hAy0.2 c hcl
      rw [actT_idT hcl] at this
      calc v0 * eta uJ 11 c = (v0 * eta uJ 11 c * v0⁻¹) * v0 := by group
        _ = eta uJ 11 c * v0 := by rw [this]
    have hmem' : v0 ∈ V ⊓ Eg uJ 11 := ⟨hv0, hmem⟩
    rw [hVE] at hmem'
    exact hv0ne ((Subgroup.mem_bot).1 hmem')
  obtain ⟨w, hw⟩ : ∃ w : ℕ → J, ∀ i, w i = fiveElt ^ i * v0 * (fiveElt ^ i)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hwV : ∀ i, w i ∈ V := fun i => by rw [hw]; exact pow_conj_mem hξV i v0 hv0
  have hwsucc : ∀ i, fiveElt * w i * fiveElt⁻¹ = w (i + 1) := fun i => by
    rw [hw, hw, conj_step]
  have hw0 : w 0 = v0 := by simp [hw]
  have hA0 : Acts (w 0) y0 := by rw [hw0]; exact hAy0
  have hA1 : Acts (w 1) (xiConj y0) := by
    have := acts_xiConj hM hA0
    rwa [hwsucc 0] at this
  have hA2 : Acts (w 2) (xiConj (xiConj y0)) := by
    have := acts_xiConj hM hA1
    rwa [hwsucc 1] at this
  have hA3 : Acts (w 3) (xiConj (xiConj (xiConj y0))) := by
    have := acts_xiConj hM hA2
    rwa [hwsucc 2] at this
  have hA4 : Acts (w 4) (xiConj (xiConj (xiConj (xiConj y0)))) := by
    have := acts_xiConj hM hA3
    rwa [hwsucc 3] at this
  have hN : w 0 * w 1 * w 2 * w 3 * w 4 = 1 :=
    norm_five_eq_one w hw (fiveElt_pow hM) hv0 hc.hVab hξV hξfpf
  have hcp : commProd y0 = true := by
    unfold commProd
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := tables_comm hc.hVab hM (hwV 0) (hwV 1) hA0 hA1
      simpa using this
    · simp only [xiConjs]
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]
        intro i hi
        rw [List.all_eq_true]
        intro j hj
        simp only [List.mem_range] at hi hj
        have hti : ∀ i < 5, ∃ a ∈ V, Acts a ([y0, xiConj y0, xiConj (xiConj y0),
            xiConj (xiConj (xiConj y0)), xiConj (xiConj (xiConj (xiConj y0)))].getD i idT) := by
          intro i hi
          interval_cases i
          · exact ⟨w 0, hwV 0, hA0⟩
          · exact ⟨w 1, hwV 1, hA1⟩
          · exact ⟨w 2, hwV 2, hA2⟩
          · exact ⟨w 3, hwV 3, hA3⟩
          · exact ⟨w 4, hwV 4, hA4⟩
        obtain ⟨a, ha, hAa⟩ := hti i hi
        obtain ⟨b, hb, hAb⟩ := hti j hj
        simpa using tables_comm hc.hVab hM ha hb hAa hAb
      · have h1 := hA0.mul (hA1.mul (hA2.mul (hA3.mul (hA4.mul Acts.one))))
        have e : w 0 * (w 1 * (w 2 * (w 3 * (w 4 * 1)))) = 1 := by
          calc w 0 * (w 1 * (w 2 * (w 3 * (w 4 * 1)))) = w 0 * w 1 * w 2 * w 3 * w 4 := by group
            _ = 1 := hN
        rw [e] at h1
        have := Acts.unique hM h1 Acts.one
        simpa using this
  obtain ⟨hGprops, hGcover⟩ := chkV_props
  obtain ⟨G, hG, hy0G⟩ := hGcover y0 hy0I hcp
  obtain ⟨hGlen, hGnd, hGspan⟩ := hGprops G hG
  have hspan : ∀ g ∈ G, g ∈ spanT y0 := (hGspan y0 hy0G).resolve_left hy0ne
  have hspanTV : ∀ t ∈ spanT y0, t ∈ TV := by
    intro t ht
    unfold spanT at ht
    rw [List.mem_eraseDups] at ht
    refine subsetProds_mem hTV1 hTVmul (xiConjs y0) ?_ t ht
    intro t' ht'
    simp only [xiConjs, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl | rfl | rfl
    · exact hy0TV
    · exact (hTV _).2 ⟨w 1, hwV 1, hA1⟩
    · exact (hTV _).2 ⟨w 2, hwV 2, hA2⟩
    · exact (hTV _).2 ⟨w 3, hwV 3, hA3⟩
    · exact (hTV _).2 ⟨w 4, hwV 4, hA4⟩
  have hGTV : ∀ g ∈ G, g ∈ TV := fun g hg => hspanTV g (hspan g hg)
  let f : V → List ℕ := fun v => Classical.choose (acts_exists_of_mem_Hj hM v.1 (hc.hVH v.2))
  have hf : ∀ v : V, Acts v.1 (f v) := fun v =>
    Classical.choose_spec (acts_exists_of_mem_Hj hM v.1 (hc.hVH v.2))
  have hTVsub : TV ⊆ Set.range f := by
    intro t ht
    obtain ⟨v, hv, hA⟩ := (hTV t).1 ht
    exact ⟨⟨v, hv⟩, Acts.unique hM (hf ⟨v, hv⟩) hA⟩
  have hTVfin : TV.Finite := (Set.finite_range f).subset hTVsub
  have hTVcard : TV.ncard ≤ 16 := by
    calc TV.ncard ≤ (Set.range f).ncard := Set.ncard_le_ncard hTVsub (Set.finite_range f)
      _ = (f '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set V).ncard := Set.ncard_image_le Set.finite_univ
      _ = Nat.card V := Set.ncard_univ V
      _ = 16 := hc.hVcard
  have hGcard : ({t | t ∈ G} : Set (List ℕ)).ncard = 16 := by
    have e : {t | t ∈ G} = ↑G.toFinset := by
      ext t
      simp
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hGnd, hGlen]
  have hTVeq : ({t | t ∈ G} : Set (List ℕ)) = TV :=
    Set.eq_of_subset_of_ncard_le (fun g hg => hGTV g hg) (by rw [hGcard]; exact hTVcard) hTVfin
  have hTVG : ∀ t ∈ TV, t ∈ G := fun t ht => by
    rw [← hTVeq] at ht
    exact ht
  have hnorm : ∀ g ∈ G, cjT td g ∈ G := by
    intro g hg
    obtain ⟨v, hv, hA⟩ := (hTV g).1 (hGTV g hg)
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hc.hd2
    have hAdi : Acts d⁻¹ td := by rw [hdinv]; exact hAd
    have h1 := hAd.mul (hA.mul hAdi)
    rw [← mul_assoc] at h1
    exact hTVG _ ((hTV _).2 ⟨d * v * d⁻¹, hc.hVd v hv, h1⟩)
  have hcubeG : cubeT (compT (xiK k) td) ∈ G :=
    hTVG _ ((hTV _).2 ⟨(fiveElt ^ k * d) ^ 3, hc.hxd, acts_pow hAxd 3⟩)
  obtain ⟨c, hcd, hc1, hc2, hc3⟩ := caseI_check hk hG htd hnorm hcubeG
  refine hconcl_of_duad hM hAx hAd hcd hc1 hc2 fun v hv => ?_
  have hvTV : f ⟨v, hv⟩ ∈ TV := (hTV _).2 ⟨v, hv, hf ⟨v, hv⟩⟩
  exact ⟨f ⟨v, hv⟩, hf ⟨v, hv⟩, hc3 _ (hTVG _ hvTV)⟩

theorem hpart_inner_b
    (hF : J4Basic) {k : ℕ}
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4)
    {V : Subgroup J} {d : J} (hc : HCfg V (fiveElt ^ k) d) : HConcl V (fiveElt ^ k) d := by
  have hM := hF.mat
  have hdich := eq_bot_or_eq_of_fpf (fiveElt ^ k) hc.hx5 V (V ⊓ Eg uJ 11) hc.hVcard inf_le_left
    (fun w hw => ⟨hc.hVx w hw.1, Hj_normalizes_Eg hM _ hc.hx w hw.2⟩)
    (fun w hw h => hc.hfpf w hw.1 h)
  rcases hdich with hbot | hall
  · exact caseI_b hF hk hc hbot
  · exact caseII_b hF hk hc (inf_eq_left.1 hall)

theorem hpart_core_b
    (hF : J4Basic) {V : Subgroup J}
    {x d : J} (hc : HCfg V x d) : HConcl V x d := by
  have hM := hF.mat
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h, k, hk⟩ := exists_conj_pow_of_card (G := ↥Hj) (p := 5)
    (card_Hj_factorization_five_b hF) (x := ⟨fiveElt, fiveElt_mem_Hj⟩) (y := ⟨x, hc.hx⟩)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_fiveElt hM)
    (by rw [Subgroup.orderOf_mk]; exact hc.hx5)
  have hk' : x = (h : J) * fiveElt ^ k * (h : J)⁻¹ := by
    have := congrArg Subtype.val hk
    simpa using this
  have hk5 : fiveElt ^ k = fiveElt ^ (k % 5) := by
    conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul, fiveElt_pow hM, one_pow, one_mul]
  have hkne : k % 5 ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk5
    have hx1 : x = 1 := by
      rw [hk', hk5]
      group
    have := hc.hx5
    rw [hx1, orderOf_one] at this
    omega
  have hkr : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  have hcj := hc.conj h.2
  have e : (h : J)⁻¹ * x * (h : J) = fiveElt ^ (k % 5) := by
    rw [hk', ← hk5]
    group
  rw [e] at hcj
  have h2 := hpart_inner_b hF hkr hcj
  rw [← e] at h2
  exact HConcl.of_conj h.2 hM h2

theorem lt_relIndex_Eg_of_order_five_b
    (hF : J4Basic) {g : J} (hg : g ∈ Hj) (h5 : orderOf g = 5) :
    16 < (Eg uJ 11 ⊓ Subgroup.centralizer ({g} : Set J)).relIndex (Eg uJ 11) := by
  have hM := hF.mat
  exact lt_relIndex_of_sylow Hj (Eg uJ 11) (Hj_normalizes_Eg hM) (card_Hj_factorization_five_b hF)
    fiveElt_mem_Hj (orderOf_fiveElt hM) (lt_relIndex_Eg_fiveElt hM) hg h5

theorem radical_eta_T_b
    (hF : J4Basic) {c : ℕ} (hc : c ∈ tMasks) :
    Radical (eta uJ 11 c) (Eg uJ 11) := by
  have hM := hF.mat
  refine radical_of_centralizer_le Hj (Eg uJ 11) (eta uJ 11 c) (isPGroup_Eg (elem_uJ hM)) ?_
    (eta_mem_Eg 11 le_rfl c) (Hj_normalizes_Eg hM) (centralizer_Hj_b hF) ?_ ?_
  · intro x hx e he
    obtain ⟨c₁, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
    obtain ⟨c₂, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 he
    exact eta_comm (elem_uJ hM) c₁ c₂
  · intro q hq
    have h := comm_of_mem_centralizer hq
    exact centralizer_le_Hj_of_T_b hF hc h
  · intro g hg h5
    exact lt_relIndex_Eg_of_order_five_b hF hg h5

theorem radical_eta_1131_b
    (hF : J4Basic) : ∃ N : Subgroup J, Radical (eta uJ 11 1131) N := by
  have hM := hF.mat
  have hC : Nat.card QT2A.Cz = 21799895040 :=
    card_centralizer_of_mem_Zl_b hF (mem_Zl.2 ⟨1131, mem_zMasks_1131, rfl⟩)
  obtain ⟨N, hQN, hNC, hnorm, hp, hself⟩ :=
    QT2A.exists_normal_two_group_selfcentralizing_ge hM hC
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hy5C, hy5⟩ := QT2A.y_prime_facts hM (QT2A.Mx_y5J hM) QT2A.chkYr5_true
  refine ⟨N, hp, hQN QT2A.zJ_mem_Qz, hNC, hnorm, hself, ?_⟩
  intro g hg hg5
  exact lt_relIndex_of_sylow QT2A.Cz N hnorm (card_Cz_factorization_five hC) hy5C hy5
    (lt_relIndex_inf_of_le hQN _ (QT2A.lt_relIndex_centralizer_y5J hM)) hg hg5

theorem j4_involution_radical_b
    (hF : J4Basic)
    (y : J) (hy : y * y = 1) (hne : y ≠ 1) :
    ∃ N : Subgroup J, IsPGroup 2 ↥N ∧ y ∈ N ∧ N ≤ Subgroup.centralizer ({y} : Set J) ∧
      (∀ q ∈ Subgroup.centralizer ({y} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      (∀ q ∈ Subgroup.centralizer ({y} : Set J), (∀ e ∈ N, q * e = e * q) → q ∈ N) ∧
      ∀ g ∈ Subgroup.centralizer ({y} : Set J), orderOf g = 5 →
        16 < (N ⊓ Subgroup.centralizer ({g} : Set J)).relIndex N := by
  rcases inv_conj_root_b hF hy hne with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hr := (radical_eta_T_b hF one_mem_tMasks).conj c
    rw [hc] at hr
    exact ⟨conjSub c (Eg uJ 11), hr⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨g, -, hg⟩ := exists_conj_eta_three hF.mat mem_zMasks_1131
    obtain ⟨N, hN⟩ := radical_eta_1131_b hF
    have hr := hN.conj (c * g⁻¹)
    have e : (c * g⁻¹) * eta uJ 11 1131 * (c * g⁻¹)⁻¹ = y := by
      rw [← hg, ← hc]
      group
    rw [e] at hr
    exact ⟨conjSub (c * g⁻¹) N, hr⟩

end CFSG.Sporadic.J4.QT2
