module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Pipe

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1

section Abstract

variable {P : Type} [Group P] [Finite P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem ordersOver_of_pipeline (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) {par gen Aa Ab repR : Array ℕ}
    {xs : Array (List ℕ)} (htv : treeValid N par gen) (hr : ∀ x, C.r x = treeR a b par gen x)
    (hA : ∀ i, C.Aa i = arrImg Aa i) (hB : ∀ i, C.Ab i = arrImg Ab i)
    (gsR : List (P × Array ℕ)) (ROm : List (Array ℕ)) (hROm : gsR.map Prod.snd = ROm)
    (hR : Subgroup.closure {g | g ∈ gsR.map Prod.fst} = R)
    (hgsR : ∀ p ∈ gsR, ActsOn C p.1 (arrImg p.2)) (hxs : xsOK N xs)
    (hbc : blocksClosed ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs))
    (hrep : repsOK ROm N repR (repList N repR) (repOrbs ROm N (repList N repR)))
    (hclo : closureOK ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs) (repList N repR)) :
    ∀ W : Subgroup P, R ≤ W → ∃ h < xs.size,
      Nat.card W = Nat.card R * blkSize N ((blocksOf ROm N Aa Ab par gen xs).getD h #[]) := by
  subst hROm
  set ROm := gsR.map Prod.snd with hROm
  set blocksArr := blocksOf ROm N Aa Ab par gen xs with hblocksArr
  set reps := repList N repR with hreps
  obtain ⟨hxs0, hxs1, hxs2⟩ := hxs
  have hom : ∀ x < N, ActsOn C (C.r x) (arrImg (omegaOf N Aa Ab par gen x x)) := fun x hx =>
    (omegaOf_actsOn C htv hr hA hB x x hx le_rfl).1
  let ox : ℕ → Array ℕ := fun x => omegaOf N Aa Ab par gen x x
  let gens' : ℕ → List (P × Array ℕ) := fun h => gsR ++ (xs.getD h []).map fun x => (C.r x, ox x)
  have hgs' : ∀ h < xs.size, ∀ p ∈ gens' h, ActsOn C p.1 (arrImg p.2) := by
    intro h hh p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hgsR p hp
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      exact hom x (hxs2 h hh x hx)
  have hsnd : ∀ h, (gens' h).map Prod.snd = gensOm ROm N Aa Ab par gen (xs.getD h []) := by
    intro h
    simp [gens', gensOm, ox, List.map_append, List.map_map, Function.comp_def, hROm]
  have hRV : ∀ h, R ≤ Subgroup.closure {g | g ∈ (gens' h).map Prod.fst} := by
    intro h
    rw [← hR]
    apply Subgroup.closure_mono
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
  have hsz : blocksArr.size = xs.size := hbc.1
  have hblk : ∀ h < xs.size, blocksArr.getD h #[] =
      bfsVis N ((gens' h).map Prod.snd) 0 ∧
      ClosedOK N ((gens' h).map Prod.snd) 0 (blocksArr.getD h #[]) := by
    intro h hh
    rw [hsnd h, hblocksArr, blocksOf_getD ROm N Aa Ab par gen xs hh]
    exact ⟨rfl, by rw [← blocksOf_getD ROm N Aa Ab par gen xs hh]; exact hbc.2 h hh⟩
  obtain ⟨hrlt, hrmem, hrcl, hrex⟩ := hrep
  have htab : ∀ t ∈ ROm, ∀ i < N, arrImg t i < N := tabs_lt_of_actsOn C hgsR
  have hrepR : ∀ i < N, repR.getD i 0 < N ∧ Reach ROm (repR.getD i 0) i := by
    intro i hi
    obtain ⟨p, hp, hp1, hp2⟩ := hrex i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
    have hcl := hrcl _ hp
    simp only at hp1 hp2 hcl
    refine ⟨hrlt i hi, ?_⟩
    rw [← hp1]
    exact (bfsVis_iff ROm x N hcl htab (by rw [hp1]; exact hrlt i hi) i).1 ⟨hi, hp2⟩
  have hcl' : ∀ h : Fin xs.size, ∀ x ∈ reps, x < N → ∃ k : Fin xs.size,
      bfsVis N (((gens' h) ++ [(C.r x, ox x)]).map Prod.snd) 0 = blocksArr.getD k #[] ∧
      ClosedOK N (((gens' h) ++ [(C.r x, ox x)]).map Prod.snd) 0 (blocksArr.getD k #[]) := by
    intro h x hx _
    obtain ⟨k, hk, hk1, hk2⟩ := hclo h.1 h.2 x hx
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · rw [List.map_append, hsnd]
      exact hk1
    · rw [List.map_append, hsnd]
      exact hk2
  have hinv := inventory_exhaustive C hgen gsR hR hgsR (m := xs.size) (fun h => gens' h.1)
    (fun h p hp => hgs' h.1 h.2 p hp) (fun h p hp => List.mem_append_left _ hp)
    ⟨⟨0, hxs0⟩, by show gens' 0 = gsR; simp only [gens', hxs1, List.map_nil, List.append_nil]⟩
    (fun h => blocksArr.getD h.1 #[])
    (fun h => hblk h.1 h.2) (fun i => repR.getD i 0) hrepR reps hrmem ox hom hcl'
  intro W hW
  obtain ⟨h, hh⟩ := hinv W hW
  refine ⟨h.1, h.2, ?_⟩
  rw [hh]
  exact card_eq_mul_blkSize C hgen (hRV h.1) _ fun i hi =>
    block_iff C hgen (gens' h.1) (hgs' h.1 h.2) (hRV h.1) _ (hblk h.1 h.2).1 (hblk h.1 h.2).2 hi

end Abstract

section Pipeline

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem pipeline_ordersOver (hn : 0 < n) (a b : Γ)
    (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    {N : ℕ} {ta tb tai tbi : Array ℕ} {prog qp : List (ℕ × ℕ)} {Aa Ab par gen repR : Array ℕ}
    {xs : Array (List ℕ)} (hta : ta = (tab n a).toArray) (htb : tb = (tab n b).toArray)
    {k m : ℕ} (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m) (hNm : N = m)
    (hinv : invValid n ta tb tai tbi) (hslp : slpValidAux prog 2 = true)
    (hqp : qpOK n (slpTabsA ta tb prog) qp) (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hE : BaseEnumOK n (List.range n) (qp.map fun p => (slpTabsA ta tb prog)[p.1]!)
      (qp.map fun p => (slpTabsA ta tb prog)[p.2]!) Ts rpar rcl)
    (hTs : Ts.size = 2 ^ k) (htv : treeValid N par gen)
    (hedge : edgeOK n N (ptsOf (List.range n) (qp.map fun p => (slpTabsA ta tb prog)[p.1]!)) Ts
      (keyMap n Ts) ta tb Aa Ab (treeTabs n N ta tb par gen)
      (treeInvTabs n N tai tbi par gen) = true)
    (hasz : aszOK N Aa Ab) (hxs : xsOK N xs) (ROm : List (Array ℕ))
    (hROm : qp.map (fun p => (slpTabsA Aa Ab prog)[p.1]!) = ROm)
    (hbc : blocksClosed ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs))
    (hrep : repsOK ROm N repR (repList N repR) (repOrbs ROm N (repList N repR)))
    (hclo : closureOK ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs) (repList N repR)) :
    ∃ R : Subgroup Γ, Nat.card R = 2 ^ k ∧ ∀ W : Subgroup Γ, R ≤ W → ∃ h < xs.size,
      Nat.card W = 2 ^ k * blkSize N ((blocksOf ROm N Aa Ab par gen xs).getD h #[]) := by
  obtain ⟨_, _, hs3, hs4, hinvq⟩ := hinv
  have hta' : tab n a = ta.toList := by rw [hta]
  have htb' : tab n b = tb.toList := by rw [htb]
  have htai' : tab n a⁻¹ = tai.toList :=
    tab_inv_of_inv a ta tai hta' hs3 (fun q hq => (hinvq q hq).1)
  have htbi' : tab n b⁻¹ = tbi.toList :=
    tab_inv_of_inv b tb tbi htb' hs4 (fun q hq => (hinvq q hq).2)
  have htai : tai = (tab n a⁻¹).toArray := by rw [htai']
  have htbi : tbi = (tab n b⁻¹).toArray := by rw [htbi']
  subst hta htb htai htbi
  set E := slpElts a b prog with hEdef
  set NT := slpTabsA (tab n a).toArray (tab n b).toArray prog with hNT
  have hsize : NT.size = prog.length + 2 := slpTabsA_size _ _ _
  have hspec := slp_tabs_spec (n := n) a b prog hslp
  let qs : List (Γ × Γ) := qp.map fun p => (E.getD p.1 1, E.getD p.2 1)
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3⟩ := hqp q hq
    refine eq_inv_of_img (n := n) _ _ (fun i hi => ?_)
    have := h3 i hi
    rw [← hspec q.1 h1, ← hspec q.2 h2] at this
    exact this
  have hG1 : qs.map (fun p => (tab n p.1).toArray) = qp.map fun p => NT[p.1]! := by
    simp only [qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hspec q.1 (hqp q hq).1
  have hG2 : qs.map (fun p => (tab n p.2).toArray) = qp.map fun p => NT[p.2]! := by
    simp only [qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hspec q.2 (hqp q hq).2.1
  have hE' : BaseEnumOK n (List.range n) (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl := by
    rw [hG1, hG2]; exact hE
  obtain ⟨hmemR, hcardR, _⟩ := benum_data qs Ts rpar rcl hqsinv hE'
  set R := Subgroup.closure {x | x ∈ qs.map Prod.fst} with hRdef
  have hGt : genTabs n (qs.map Prod.fst) = qp.map fun p => NT[p.1]! := by
    rw [← hG1]
    simp only [genTabs, List.map_map, Function.comp_def]
  have hmem : ∀ y : Γ, memR n (ptsOf (List.range n) (qp.map fun p => NT[p.1]!)) Ts
      (keyMap n Ts) (tab n y).toArray = true → y ∈ R := by
    intro y hy
    rw [← hGt] at hy
    exact mem_R_of_memR qs Ts hn hmemR y hy
  have hcardR' : Nat.card R = 2 ^ k := by rw [hcardR, hTs]
  have hindex : R.index = m := by
    have h1 := R.card_mul_index
    rw [hcardR', hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hN : Nat.card (Γ ⧸ R) = N := by
    rw [← Subgroup.index_eq_card, hindex, hNm]
  have hN0 : 0 < N := by rw [hNm]; exact hm.pos
  obtain ⟨C, hr, hA, hB⟩ := exists_cert a b R hN hN0 htv _ Ts hmem hedge
  let gsR : List (Γ × Array ℕ) := qp.map fun q => (E.getD q.1 1, (slpTabsA Aa Ab prog)[q.1]!)
  have hfst : gsR.map Prod.fst = qs.map Prod.fst := by
    simp only [gsR, qs, List.map_map, Function.comp_def]
  have hsnd : gsR.map Prod.snd = ROm := by
    rw [← hROm]
    simp only [gsR, List.map_map, Function.comp_def]
  have hRg : Subgroup.closure {g | g ∈ gsR.map Prod.fst} = R := by rw [hfst]
  have hgsR : ∀ p ∈ gsR, ActsOn C p.1 (arrImg p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hlt : q.1 < (slpTabsA Aa Ab prog).size := by
      rw [slpTabsA_size, ← hsize]
      exact (hqp q hq).1
    exact (slp_actsOn C hA hB hasz prog hslp q.1 hlt).1
  refine ⟨R, hcardR', fun W hW => ?_⟩
  obtain ⟨h, hh, hW'⟩ := ordersOver_of_pipeline C hgen htv hr hA hB gsR ROm hsnd hRg hgsR hxs hbc
    hrep hclo W hW
  exact ⟨h, hh, by rw [hW', hcardR']⟩

end Pipeline

end CFSG.Quasithin.H13.QTESylow
