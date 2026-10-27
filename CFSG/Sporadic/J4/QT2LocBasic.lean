module

public import CFSG.Sporadic.J4.BasicFacts
public import CFSG.Sporadic.J4.QT2LocVLClassMain
public import CFSG.Sporadic.J4.QT2LocHMain
public import CFSG.Sporadic.J4.QT2LocVLMain

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A Matrix
open scoped Classical Pointwise

theorem centralizer_Hj_b (hF : J4Basic) :
    ∀ x ∈ Hj, (∀ y ∈ Eg uJ 11, x * y = y * x) → x ∈ Eg uJ 11 := by
  have hM := hF.mat
  refine centralizer_le_of_chain (elem_uJ hM) Hj Eg_le_Hj (card_Eg_uJ hM) bJ
    (fun i => eta_mem_Eg 11 le_rfl _) cntJ tJ 5 (fun j hj k hk => tJ_mem_Kc hM hj hk)
    (fun j hj k hk k' hk' h => tJ_distinct hM hj hk hk' h) ?_
  rw [hF.cardHj]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  unfold cntJ
  rw [chain_card]
  norm_num

theorem exists_eta_mul_Kel_b
    (hF : J4Basic) {g : J} (hg : g ∈ P0) :
    ∃ c < 2 ^ 11, ∃ e < 1024, g = eta uJ 11 c * Kel e := by
  have hM := hF.mat
  obtain ⟨t, ht, hgt⟩ := table_of_mem hM g hg
  obtain ⟨e, he, rfl⟩ : ∃ e < 1024, seqT (pcSeq e) = t := by
    unfold tabL at ht
    simpa [List.mem_map, List.mem_range] using ht
  have hK := Acts_Kel hM he
  have hmem : (Kel e)⁻¹ * g ∈ Hj := Hj.mul_mem (Hj.inv_mem (Kel_mem_Hj he)) (P0_le_Hj hg)
  have hcomm : ∀ y ∈ Eg uJ 11, (Kel e)⁻¹ * g * y = y * ((Kel e)⁻¹ * g) := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have hg1 := hgt.2 d hd
    have hK1 := hK.2 d hd
    calc (Kel e)⁻¹ * g * eta uJ 11 d
        = (Kel e)⁻¹ * (g * eta uJ 11 d * g⁻¹) * g := by group
      _ = (Kel e)⁻¹ * (Kel e * eta uJ 11 d * (Kel e)⁻¹) * g := by rw [hg1, hK1]
      _ = eta uJ 11 d * ((Kel e)⁻¹ * g) := by group
  obtain ⟨c0, hc0, hc0e⟩ := (mem_Eg_iff (elem_uJ hM)).1 (centralizer_Hj_b hF _ hmem hcomm)
  refine ⟨actT (seqT (pcSeq e)) c0, actT_lt hK.1 c0, e, he, ?_⟩
  have hg' : g = Kel e * eta uJ 11 c0 := by
    rw [← hc0e]; group
  rw [hg']
  calc Kel e * eta uJ 11 c0 = (Kel e * eta uJ 11 c0 * (Kel e)⁻¹) * Kel e := by group
    _ = eta uJ 11 (actT (seqT (pcSeq e)) c0) * Kel e := by rw [hK.2 c0 hc0]

theorem sylowFun_bijective_b
    (hF : J4Basic) : Function.Bijective sylowFun := by
  have hM := hF.mat
  constructor
  · intro p q h
    have h' := congrArg Subtype.val h
    simp only [sylowFun] at h'
    have := Kel_inj hM p.2.2 q.2.2 h' p.1.2 q.1.2
    exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)
  · rintro ⟨g, hg⟩
    obtain ⟨c, hc, e, he, rfl⟩ := exists_eta_mul_Kel_b hF hg
    exact ⟨(⟨c, hc⟩, ⟨e, he⟩), rfl⟩

theorem card_P0_b (hF : J4Basic) :
    Nat.card P0 = 2 ^ 21 := by
  rw [← Nat.card_congr (Equiv.ofBijective sylowFun (sylowFun_bijective_b hF)), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem card_Hj_factorization_two_b (hF : J4Basic) : (Nat.card Hj).factorization 2 = 21 := by
  rw [hF.cardHj]
  have h : (501397585920 : ℕ) = 2 ^ 21 * 239085 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_Hj_factorization_five_b (hF : J4Basic) : (Nat.card Hj).factorization 5 = 1 := by
  rw [hF.cardHj]
  have h : (501397585920 : ℕ) = 5 * 100279517184 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_into_P0_b
    (hF : J4Basic) {h : J} (hh : h ∈ Hj) (h2 : h * h = 1) :
    ∃ g ∈ Hj, g * h * g⁻¹ ∈ P0 :=
  exists_conj_into_of_involution Hj P0 P0_le_Hj
    (by rw [card_P0_b hF, card_Hj_factorization_two_b hF]) hh h2

theorem iset_complete_b
    (hF : J4Basic) {h : J} (hh : h ∈ Hj) (h2 : h * h = 1)
    {t : List ℕ} (ht : Acts h t) : t ∈ isetT := by
  have hM := hF.mat
  obtain ⟨g, hg, hgh⟩ := exists_conj_into_P0_b hF hh h2
  obtain ⟨t0, ht0, hA0⟩ := table_of_mem hM _ hgh
  have hsq : compT t0 t0 = idT := by
    have hA1 := hA0.mul hA0
    have e : (g * h * g⁻¹) * (g * h * g⁻¹) = 1 := by
      calc (g * h * g⁻¹) * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    rw [e] at hA1
    exact Acts.unique hM hA1 Acts.one
  have hseed : t0 ∈ invSeedsT := by
    unfold invSeedsT
    rw [List.mem_filter]
    exact ⟨ht0, by simp [hsq]⟩
  have h0 : ∃ t ∈ isetT, Acts (g * h * g⁻¹) t := ⟨t0, iset_props.1 t0 hseed, hA0⟩
  have h1 := piT_conj hM g⁻¹ (Hj.inv_mem hg) _ h0
  have e2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e2] at h1
  obtain ⟨t', ht', hA'⟩ := h1
  have := Acts.unique hM hA' ht
  rw [← this]
  exact ht'

theorem dichotomy_b
    (hF : J4Basic) {V : Subgroup J} (hV : XfV V) :
    V ⊓ Eg uJ 11 = ⊥ ∨ V ≤ Eg uJ 11 := by
  have hM := hF.mat
  rcases eq_bot_or_eq_of_fpf fiveElt (orderOf_fiveElt hM) V (V ⊓ Eg uJ 11) hV.hVcard inf_le_left
    (fun w hw => ⟨hV.hVx w hw.1, Hj_normalizes_Eg hM _ fiveElt_mem_Hj w hw.2⟩)
    (fun w hw h => hV.hfpf w hw.1 h) with hbot | hall
  · exact Or.inl hbot
  · exact Or.inr (inf_eq_left.1 hall)

theorem lineMasks_b
    (hF : J4Basic) {V : Subgroup J} (hV : XfV V) (hVE : V ≤ Eg uJ 11) :
    ∃ S ∈ lines17, ∀ c, c ∈ S ↔ c < 2048 ∧ eta uJ 11 c ∈ V := by
  have hM := hF.mat
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
    have := hV.hVx _ hcS'.2
    rwa [hAξ.2 c hcS'.1] at this
  have hfpf : ∀ c ∈ Sset, c ≠ 0 → actT xiT c ≠ c := by
    intro c hcS hc0 heq
    have hcS' := (hSset c).1 hcS
    have h1 := hAξ.2 c hcS'.1
    rw [heq] at h1
    have h2 : fiveElt * eta uJ 11 c = eta uJ 11 c * fiveElt := by
      calc fiveElt * eta uJ 11 c = (fiveElt * eta uJ 11 c * fiveElt⁻¹) * fiveElt := by group
        _ = eta uJ 11 c * fiveElt := by rw [h1]
    have h3 := hV.hfpf _ hcS'.2 h2
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
    have := hV.hVcard
    rw [← this]
    exact (Nat.card_coe_set_eq (V : Set J)).symm
  obtain ⟨S, hS, hSeq⟩ := exists_line h0 hx hξ hfpf hlt hcard
  exact ⟨S, hS, fun c => (hSeq c).trans (hSset c)⟩

theorem eq_eta_mul_lift_b
    (hF : J4Basic) {y : List ℕ} (hy : y ∈ vlTables) {v : J} (hvH : v ∈ Hj)
    (hAv : Acts v y) : ∃ e < 2048, v = eta uJ 11 e * el5 (vlLiftWord y) := by
  have hM := hF.mat
  obtain ⟨hAS, hSH⟩ := Acts_vlLift hM hy
  set S := el5 (vlLiftWord y) with hS
  have hnH : S⁻¹ * v ∈ Hj := Hj.mul_mem (Hj.inv_mem hSH) hvH
  have hnE : S⁻¹ * v ∈ Eg uJ 11 := by
    refine centralizer_Hj_b hF _ hnH fun y' hy' => ?_
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy'
    have h1 := hAS.2 c hc
    have h2 := hAv.2 c hc
    have h3 : v * eta uJ 11 c = eta uJ 11 (actT y c) * v := by
      calc v * eta uJ 11 c = (v * eta uJ 11 c * v⁻¹) * v := by group
        _ = eta uJ 11 (actT y c) * v := by rw [h2]
    have h4 : S⁻¹ * eta uJ 11 (actT y c) * S = eta uJ 11 c := by
      calc S⁻¹ * eta uJ 11 (actT y c) * S = S⁻¹ * (S * eta uJ 11 c * S⁻¹) * S := by rw [h1]
        _ = eta uJ 11 c := by group
    calc S⁻¹ * v * eta uJ 11 c = S⁻¹ * (v * eta uJ 11 c) := by group
      _ = S⁻¹ * (eta uJ 11 (actT y c) * v) := by rw [h3]
      _ = (S⁻¹ * eta uJ 11 (actT y c) * S) * (S⁻¹ * v) := by group
      _ = eta uJ 11 c * (S⁻¹ * v) := by rw [h4]
  obtain ⟨e, he, hen⟩ := (mem_Eg_iff (elem_uJ hM)).1 hnE
  refine ⟨actT y e, by simpa using actT_lt hAS.1 e, ?_⟩
  have h5 := hAS.2 e he
  have hv : v = S * eta uJ 11 e := by
    rw [← hen]
    group
  calc v = S * eta uJ 11 e := hv
    _ = (S * eta uJ 11 e * S⁻¹) * S := by group
    _ = eta uJ 11 (actT y e) * S := by rw [h5]

theorem commProd_of_xfV_b
    (hF : J4Basic) {V : Subgroup J} (hV : XfV V) {v0 : J} (hv0 : v0 ∈ V)
    {y0 : List ℕ} (hAy0 : Acts v0 y0) : commProd y0 = true := by
  have hM := hF.mat
  have hξV := hV.hVx
  obtain ⟨w, hw⟩ : ∃ w : ℕ → J, ∀ i, w i = fiveElt ^ i * v0 * (fiveElt ^ i)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hwV : ∀ i, w i ∈ V := fun i => by rw [hw]; exact pow_conj_mem_gen hξV i v0 hv0
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
    norm_five_eq_one w hw (fiveElt_pow hM) hv0 hV.hVab hξV hV.hfpf
  unfold commProd
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have := tables_comm hV.hVab hM (hwV 0) (hwV 1) hA0 hA1
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
      simpa using tables_comm hV.hVab hM ha hb hAa hAb
    · have h1 := hA0.mul (hA1.mul (hA2.mul (hA3.mul (hA4.mul Acts.one))))
      have e : w 0 * (w 1 * (w 2 * (w 3 * (w 4 * 1)))) = 1 := by
        calc w 0 * (w 1 * (w 2 * (w 3 * (w 4 * 1)))) = w 0 * w 1 * w 2 * w 3 * w 4 := by group
          _ = 1 := hN
      rw [e] at h1
      have := Acts.unique hM h1 Acts.one
      simpa using this

theorem classII_b
    (hF : J4Basic) {V : Subgroup J} (hV : XfV V) (hVE : V ⊓ Eg uJ 11 = ⊥) :
    ∃ G ∈ vlGroups, ∀ v ∈ V, ∃ M ∈ G, Mx v = rowsMatrix M := by
  have hM := hF.mat
  obtain ⟨v0, hv0, hv0ne⟩ := hV.exists_ne_one
  obtain ⟨y0, hAy0⟩ := acts_exists_of_mem_Hj hM v0 (hV.hVH hv0)
  have hy0I : y0 ∈ isetT := iset_complete_b hF (hV.hVH hv0) (hV.hV2 v0 hv0) hAy0
  have hy0ne : y0 ≠ idT := by
    intro h
    rw [h] at hAy0
    have hmem : v0 ∈ Eg uJ 11 := by
      refine centralizer_Hj_b hF v0 (hV.hVH hv0) fun y hy => ?_
      obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hAy0.2 c hcl
      rw [actT_idT hcl] at this
      calc v0 * eta uJ 11 c = (v0 * eta uJ 11 c * v0⁻¹) * v0 := by group
        _ = eta uJ 11 c * v0 := by rw [this]
    have hmem' : v0 ∈ V ⊓ Eg uJ 11 := ⟨hv0, hmem⟩
    rw [hVE] at hmem'
    exact hv0ne ((Subgroup.mem_bot).1 hmem')
  have hcp := commProd_of_xfV_b hF hV hv0 hAy0
  obtain ⟨-, hGcover⟩ := chkV_props
  obtain ⟨G0, hG0, hy0G⟩ := hGcover y0 hy0I hcp
  have hy0T : y0 ∈ vlTables := by
    unfold vlTables
    rw [List.mem_filter, List.mem_flatten]
    exact ⟨⟨G0, hG0, hy0G⟩, by simpa using hy0ne⟩
  obtain ⟨e, he, hv0e⟩ := eq_eta_mul_lift_b hF hy0T (hV.hVH hv0) hAy0
  have hv0p : v0 = vlElt (y0, e) := hv0e
  have hMv0 : Mx v0 = rowsMatrix (vlT (y0, e)) := by rw [hv0p]; exact Mx_vlElt hM hy0T he
  have hwf : wfRows (vlT (y0, e)) = true := wfRows_vlT hy0T he
  have hcjV : ∀ i, vlCj v0 i ∈ V := fun i => by
    rw [vlCj_eq]
    exact pow_conj_mem_gen hV.hVx i v0 hv0
  have hvalid : vlValid (vlT (y0, e)) = true := by
    refine vlValid_of_group hM hwf hMv0 (hV.hV2 v0 hv0) ?_ ?_ ?_
    · exact hV.hVab _ hv0 _ (hcjV 1)
    · exact hV.hVab _ hv0 _ (hcjV 2)
    · have hN := norm_five_eq_one (fun i => fiveElt ^ i * v0 * (fiveElt ^ i)⁻¹) (fun i => rfl)
        (fiveElt_pow hM) hv0 hV.hVab hV.hVx hV.hfpf
      simp only [← vlCj_eq] at hN
      exact hN
  have hpair : (y0, e) ∈ vlPairs := by
    unfold vlPairs
    rw [List.mem_flatMap]
    refine ⟨y0, hy0T, ?_⟩
    rw [List.mem_filterMap]
    have hv' : vlValid (mulRows vlEtaTab[e]! (vlLiftRows y0)) = true := hvalid
    exact ⟨e, List.mem_range.2 he, by simp [hv']⟩
  obtain ⟨hdist, G, hG, hGcov⟩ := vlGroups_cover hpair
  refine ⟨G, hG, ?_⟩
  have hTs : ∀ i < 4, Mx (vlCj v0 i) = rowsMatrix (vlConjs (vlT (y0, e)))[i]! := by
    obtain ⟨h0, h1, h2, h3⟩ := Mx_vlCj hM hMv0
    intro i hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hwfs := wfRows_vlConjs hwf
  have hgV : ∀ m, vlSubJ (vlCj v0) m ∈ V := fun m => vlSubJ_mem (fun i _ => hcjV i) m
  have hgM : ∀ m, Mx (vlSubJ (vlCj v0) m) =
      rowsMatrix (vlSubsetProd (vlConjs (vlT (y0, e))) m) := fun m => Mx_vlSubJ hTs m
  have hgwf : ∀ m, wfRows (vlSubsetProd (vlConjs (vlT (y0, e))) m) = true :=
    fun m => wfRows_vlSubsetProd hwfs m
  have hgetD : ∀ i < 16, (vlGroupOf (vlT (y0, e))).getD i #[] =
      vlSubsetProd (vlConjs (vlT (y0, e))) i := by
    intro i hi
    simp [vlGroupOf, List.getD_eq_getElem?_getD, hi]
  have hid : ∀ X : Array V2, eqRows X X = true := fun X => eqRows_iff.2 rfl
  have hginj : ∀ m < 16, ∀ m' < 16, vlSubJ (vlCj v0) m = vlSubJ (vlCj v0) m' → m = m' := by
    intro m hm m' hm' hmm
    by_contra hne
    have hrow : vlSubsetProd (vlConjs (vlT (y0, e))) m = vlSubsetProd (vlConjs (vlT (y0, e))) m' :=
      eq_of_rowsMatrix_eq (hgwf m) (hgwf m') (by rw [← hgM, ← hgM, hmm])
    unfold vlDistinct at hdist
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hdist
    obtain ⟨-, hd⟩ := hdist
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hd m' hm' m hlt
      rw [hgetD m' hm', hgetD m (hlt.trans hm'), ← hrow, hid] at this
      simp at this
    · have := hd m hm m' hlt
      rw [hgetD m hm, hgetD m' (hlt.trans hm), hrow, hid] at this
      simp at this
  let f : Fin 16 → V := fun m => ⟨vlSubJ (vlCj v0) m, hgV m⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg (fun x : V => (x : J)) hab
    exact Fin.ext (hginj a a.2 b b.2 this)
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [hV.hVcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  intro v hv
  obtain ⟨m, hm⟩ := hfbij.2 ⟨v, hv⟩
  have hvm : v = vlSubJ (vlCj v0) m := (congrArg (fun x : V => (x : J)) hm).symm
  have hmem : vlSubsetProd (vlConjs (vlT (y0, e))) m ∈ vlGroupOf (vlT (y0, e)) := by
    unfold vlGroupOf
    rw [List.mem_map]
    exact ⟨m, List.mem_range.2 m.2, rfl⟩
  obtain ⟨M', hM'G, hM'eq⟩ := hGcov _ hmem
  refine ⟨M', hM'G, ?_⟩
  rw [hvm, hgM, eqRows_iff.1 hM'eq]

theorem xfV_group_b
    (hF : J4Basic) {W : Subgroup J} (hW : XfV W) :
    ∃ g < 149, ∀ w ∈ W, ∃ M ∈ vlAll[g]!, Mx w = rowsMatrix M := by
  have hM := hF.mat
  rcases dichotomy_b hF hW with hbot | hle
  · obtain ⟨G, hG, hGW⟩ := classII_b hF hW hbot
    obtain ⟨g, hg, e⟩ := mem_vlAll_of_mem (mem_lift hG)
    refine ⟨g, hg, fun w hw => ?_⟩
    obtain ⟨M, hMG, hMw⟩ := hGW w hw
    exact ⟨M, by rw [e]; exact List.mem_toArray.2 hMG, hMw⟩
  · obtain ⟨S, hS, hSc⟩ := lineMasks_b hF hW hle
    obtain ⟨g, hg, e⟩ := mem_vlAll_of_mem (etaE_mem_line hS)
    refine ⟨g, hg, fun w hw => ?_⟩
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hle hw)
    have hcS : c ∈ S := (hSc c).2 ⟨hc, hw⟩
    refine ⟨etaE c, ?_, Mx_eta hM 11 le_rfl c⟩
    rw [e]
    exact List.mem_toArray.2 (List.mem_map.2 ⟨c, hcS, rfl⟩)

theorem xfV_conj_named_b
    (hF : J4Basic) {W : Subgroup J} (hW : XfV W) (target : List (Subgroup J))
    (hR : ∀ r ∈ vlRepIdx, ∃ R ∈ target, Nat.card R = 16 ∧
      ∀ u ∈ R, ∃ M ∈ vlAll[r]!, Mx u = rowsMatrix M) :
    ∃ R ∈ target, ∃ x : J, W = R.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨g, hg, hWg⟩ := xfV_group_b hF hW
  obtain ⟨r, hr, c, hc, hconj, hinv⟩ := vlClass_data hg
  obtain ⟨x, hx, hxi⟩ := vlCx_elt hF.mat hc hinv
  obtain ⟨R, hRt, hR16, hRs⟩ := hR r hr
  refine ⟨R, hRt, x, ?_⟩
  have hcj : ∀ M ∈ vlAll[r]!, ∃ M' ∈ vlAll[g]!, eqRows (mulRows (mulRows vlCx[c]! M)
      vlCxInv[c]!) M' = true := by
    intro M hM
    unfold vlConjEq at hconj
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Array.any_eq_true',
      Array.mem_map] at hconj
    obtain ⟨h1, -⟩ := hconj
    obtain ⟨M', hM', hk⟩ := h1 _ ⟨M, hM, rfl⟩
    exact ⟨M', hM', hk⟩
  exact eq_conj_of_matrices hW.hVcard hR16 (vlAll_size hg) hWg hRs hx hxi hcj

theorem RIn_rep_b (hM : MatFacts)
    (hstab : ∀ x : J, x • w₀ = w₀ → x ∈ Hj) {u : J} {r : Row} (hr : r = u⁻¹ • w₀) (x : J) :
    RIn r x ↔ u * x * u⁻¹ ∈ Eg uJ 11 := by
  constructor
  · rintro ⟨g, hg, hE⟩
    have h1 : (u * g) • w₀ = w₀ := by rw [mul_smul, hg, hr, smul_inv_smul]
    have hH : u * g ∈ Hj := hstab _ h1
    have e : u * x * u⁻¹ = (u * g) * (g⁻¹ * x * g) * (u * g)⁻¹ := by group
    rw [e]
    exact Hj_normalizes_Eg hM _ hH _ hE
  · intro h
    refine ⟨u⁻¹, hr.symm, ?_⟩
    rw [inv_inv]
    exact h

end CFSG.Sporadic.J4.QT2

end
