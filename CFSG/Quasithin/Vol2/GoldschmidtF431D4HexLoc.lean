module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexLocSpec
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexPoly
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexPt
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexLn

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Quasithin CFSG.Quasithin.H13.F45Ru CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

universe u v

section Pairs

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

theorem two_of_pairs {a b₀ : V} {U : ℕ → V} {k : ℕ} (hU : ∀ u, Γ.Adj a u → ∃ i < k, u = U i)
    (hpairs : ∀ i < k, ∀ j < k, i ≠ j →
      ∃ σ : X, σ • a = a ∧ σ • b₀ = b₀ ∧ σ • U 0 = U i ∧ σ • U 1 = U j) :
    ∀ u₁ u₂ v₁ v₂, Γ.Adj a u₁ → Γ.Adj a u₂ → u₁ ≠ u₂ → Γ.Adj a v₁ → Γ.Adj a v₂ → v₁ ≠ v₂ →
      ∃ g : X, g • a = a ∧ g • b₀ = b₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂ := by
  intro u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne'
  obtain ⟨i₁, hi₁, rfl⟩ := hU u₁ hu₁
  obtain ⟨i₂, hi₂, rfl⟩ := hU u₂ hu₂
  obtain ⟨j₁, hj₁, rfl⟩ := hU v₁ hv₁
  obtain ⟨j₂, hj₂, rfl⟩ := hU v₂ hv₂
  obtain ⟨σ, hσa, hσb, hσ1, hσ2⟩ := hpairs i₁ hi₁ i₂ hi₂ (fun e => hne (by rw [e]))
  obtain ⟨τ, hτa, hτb, hτ1, hτ2⟩ := hpairs j₁ hj₁ j₂ hj₂ (fun e => hne' (by rw [e]))
  refine ⟨τ * σ⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.mpr hσa.symm, hτa]
  · rw [mul_smul, inv_smul_eq_iff.mpr hσb.symm, hτb]
  · rw [mul_smul, inv_smul_eq_iff.mpr hσ1.symm, hτ1]
  · rw [mul_smul, inv_smul_eq_iff.mpr hσ2.symm, hτ2]

end Pairs

section Words

variable {X : Type u} [Group X] [MulAction X HexVtx]

theorem actsAs_listElt {g : ℕ → X} {G : Array (Array ℕ)} (hg : ∀ j < G.size, ActsAs (g j) G[j]!)
    {ws : List String} (hw : hexWordsOK G.size ws = true) {i : ℕ} (hi : i < ws.length) :
    ActsAs (wordElt g (hexDecode ws[i]!)) (hexWordArrs G ws)[i]! := by
  have hm : ws[i]! ∈ ws := by
    have : ws[i]! = ws[i] := by simp [hi]
    rw [this]
    exact List.getElem_mem hi
  rw [hexWordArrs_get G ws hi]
  exact actsAs_wordElt hg _ (hexWordsOK_spec hw _ hm)

end Words

section Point

variable {X : Type u} [Group X] [MulAction X HexVtx] [GraphAction X hexGraph]

theorem hexPt_of_check {g : ℕ → X} {G : Array (Array ℕ)} (hg : ∀ j < G.size, ActsAs (g j) G[j]!)
    (hmeet : LineMeet) {ptL lay par : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) (hl : hexLayOK lineTab ptL 0 lay par = true) {b0 : ℕ}
    {hW pW : List String} (h : hexPtLocalOK lineTab ptL G lay b0 hW pW = true) :
    HexPt X hexGraph (Sum.inl 0) (hexOfCode b0) := by
  obtain ⟨hW1, hW2, hb0, hlay6, hnd, hHfix, hOrb, hPfix, hPpairs⟩ :=
    hexPtLocalOK_spec (H := hexWordArrs G hW) (P := hexWordArrs G pW) rfl rfl h
  have hL : Layers hexGraph 6 (Sum.inl 0) (fun x => lay[hexCode x]!) := by
    have := layers_of_hexLayOK hp hi hl
    rwa [hexOfCode_zero] at this
  have hptL : ∀ k < 9, ptL[k]! < 2457 := fun k hk => by
    have := ((hexIncOK_spec hi).1 0 (by norm_num) k hk).1
    simpa using this
  have hactsH : ∀ i < (hexWordArrs G hW).size,
      ActsAs (wordElt g (hexDecode hW[i]!)) (hexWordArrs G hW)[i]! := fun i hi' =>
    actsAs_listElt hg hW1 (by rwa [hexWordArrs_size] at hi')
  have hsurj : ∀ c < 3276, ∃ w : HexVtx, hexCode w = c := fun c hc =>
    ⟨hexOfCode c, hexCode_hexOfCode hc⟩
  have hfix0 : ∀ i < (hexWordArrs G hW).size,
      wordElt g (hexDecode hW[i]!) • (Sum.inl 0 : HexVtx) = Sum.inl 0 := by
    intro i hi'
    obtain ⟨q, hq, hxq⟩ := hactsH i hi' (0 : Fin 819)
    rw [hxq]
    exact congrArg Sum.inl (Fin.ext (by rw [← hq]; exact hHfix i hi'))
  have hact : ∀ j < (hexWordArrs G hW).size, ∀ v w : HexVtx,
      hexActOK lineTab (hexWordArrs G hW)[j]! (hexCode v) (hexCode w) = true →
        wordElt g (hexDecode hW[j]!) • v = w := by
    intro j hj v w hvw
    have := smul_hexOfCode_of_actOK hmeet hp (hactsH j hj) (hexCode_lt v) (hexCode_lt w) hvw
    rwa [hexOfCode_hexCode, hexOfCode_hexCode] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL.dist_eq (hexOfCode b0)]
    show lay[hexCode (hexOfCode b0)]! = 6
    rw [hexCode_hexOfCode (by omega)]
    exact hlay6
  · have hnd' : (hexNbr lineTab ptL (hexCode (Sum.inl 0 : HexVtx))).Nodup := by
      have e : hexNbr lineTab ptL (hexCode (Sum.inl 0 : HexVtx)) =
          ((List.range 9).map fun k => ptL[k]!).map (· + 819) := by
        simp [hexNbr, hexCode, List.map_map, Function.comp_def]
      rw [e]
      exact hnd.map (fun a b hab => by simpa using hab)
    rw [ncard_neighborSet_eq hp hi _ hnd']
    simp [hexNbr, hexCode]
  · intro b hb
    have hbl : (fun x => lay[x]! == 6) (hexCode b) = true := by
      have := hL.dist_eq b
      rw [hb] at this
      simpa using this.symm
    have hok : orbOKR 3276 (hexWordArrs G hW).size
        (fun j y x => hexActOK lineTab (hexWordArrs G hW)[j]! y x) (hexCode (hexOfCode b0)) 512
        (fun x => lay[x]! == 6)
        (orbBFS 3276 (hexWordArrs G hW).size
          (hexActS lineTab (hexLineKeyMap lineTab) (hexWordArrs G hW)) b0) = true := by
      rw [hexCode_hexOfCode (by omega)]
      exact hOrb
    obtain ⟨y, hy, e⟩ := orbOKR_cover hexCode (fun i => wordElt g (hexDecode hW[i]!))
      (fun j y x => hexActOK lineTab (hexWordArrs G hW)[j]! y x) hsurj hact hexCode_injective
      hexCode_lt hok hbl
    refine ⟨y, ?_, e⟩
    have : Subgroup.closure ((fun i => wordElt g (hexDecode hW[i]!)) ''
        Set.Iio (hexWordArrs G hW).size) ≤ MulAction.stabilizer X (Sum.inl 0 : HexVtx) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi', rfl⟩
      exact hfix0 i hi'
    exact this hy
  · refine two_of_pairs (U := fun a => hexOfCode (819 + ptL[a]!)) (k := 9) ?_ ?_
    · intro u hu
      obtain ⟨k, hk, hku⟩ := (mem_hexNbr_point (pts := lineTab) (ptL := ptL)
        (p := hexCode (Sum.inl 0 : HexVtx)) (by norm_num [hexCode])).1
          ((hexAdj_iff_nbr hp hi (Sum.inl 0) u).1 hu)
      have hku' : ptL[k]! + 819 = hexCode u := by simpa [hexCode] using hku
      refine ⟨k, hk, ?_⟩
      show u = hexOfCode (819 + ptL[k]!)
      rw [Nat.add_comm, hku', hexOfCode_hexCode]
    · intro i hi' j hj hij
      obtain ⟨idx, hidx, hA, hB⟩ := hPpairs i hi' j hj hij
      have hidx' : idx < pW.length := by rwa [hexWordArrs_size] at hidx
      have hx := actsAs_listElt hg hW2 hidx'
      refine ⟨wordElt g (hexDecode pW[idx]!), ?_, ?_, ?_, ?_⟩
      · obtain ⟨q, hq, hxq⟩ := hx (0 : Fin 819)
        rw [hxq]
        exact congrArg Sum.inl (Fin.ext (by rw [← hq]; exact (hPfix idx hidx).1))
      · obtain ⟨q, hq, hxq⟩ := hx ⟨b0, hb0⟩
        rw [hexOfCode_inl hb0, hxq]
        exact congrArg Sum.inl (Fin.ext (by rw [← hq]; exact (hPfix idx hidx).2))
      · exact smul_hexOfCode_of_actOK hmeet hp hx
          (by have := hptL 0 (by norm_num); omega) (by have := hptL i hi'; omega) hA
      · exact smul_hexOfCode_of_actOK hmeet hp hx
          (by have := hptL 1 (by norm_num); omega) (by have := hptL j hj; omega) hB

end Point

section Line

variable {X : Type u} [Group X] [MulAction X HexVtx] [GraphAction X hexGraph]

theorem hexLn_of_check {g : ℕ → X} {G : Array (Array ℕ)} (hg : ∀ j < G.size, ActsAs (g j) G[j]!)
    (hmeet : LineMeet) {ptL lay par : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) (hl : hexLayOK lineTab ptL 819 lay par = true)
    {y0 m0 : ℕ} {nW tW : List String} (h : hexLnLocalOK lineTab G lay y0 m0 nW tW = true) :
    HexLn X hexGraph (Sum.inr 0) (hexOfCode y0) (hexOfCode m0) := by
  obtain ⟨hN1, hT1, hy0, hlay5, hm0a, hm0b, hlay6, hNfix, hOrb5, hOrb6, hTfix, hTpairs⟩ :=
    hexLnLocalOK_spec (Nn := hexWordArrs G nW) (T := hexWordArrs G tW) rfl rfl h
  have hL : Layers hexGraph 6 (Sum.inr 0) (fun x => lay[hexCode x]!) := by
    have := layers_of_hexLayOK hp hi hl
    rwa [hexOfCode_819] at this
  have hactsN : ∀ i < (hexWordArrs G nW).size,
      ActsAs (wordElt g (hexDecode nW[i]!)) (hexWordArrs G nW)[i]! := fun i hi' =>
    actsAs_listElt hg hN1 (by rwa [hexWordArrs_size] at hi')
  have hsurj : ∀ c < 3276, ∃ w : HexVtx, hexCode w = c := fun c hc =>
    ⟨hexOfCode c, hexCode_hexOfCode hc⟩
  have hfixL : ∀ i < (hexWordArrs G nW).size,
      wordElt g (hexDecode nW[i]!) • (Sum.inr 0 : HexVtx) = Sum.inr 0 := by
    intro i hi'
    have := smul_hexOfCode_of_actOK hmeet hp (hactsN i hi') (by norm_num : 819 < 3276)
      (by norm_num : 819 < 3276) (hNfix i hi')
    rwa [hexOfCode_819] at this
  have hact : ∀ j < (hexWordArrs G nW).size, ∀ v w : HexVtx,
      hexActOK lineTab (hexWordArrs G nW)[j]! (hexCode v) (hexCode w) = true →
        wordElt g (hexDecode nW[j]!) • v = w := by
    intro j hj v w hvw
    have := smul_hexOfCode_of_actOK hmeet hp (hactsN j hj) (hexCode_lt v) (hexCode_lt w) hvw
    rwa [hexOfCode_hexCode, hexOfCode_hexCode] at this
  have key : ∀ (root t cnt : ℕ) (r : OrbRec), root < 3276 →
      orbOKR 3276 (hexWordArrs G nW).size
        (fun j y x => hexActOK lineTab (hexWordArrs G nW)[j]! y x) root cnt
        (fun x => lay[x]! == t) r = true →
      ∀ b : HexVtx, hexGraph.dist (Sum.inr 0) b = t →
        ∃ y : X, y • (Sum.inr 0 : HexVtx) = Sum.inr 0 ∧ y • hexOfCode root = b := by
    intro root t cnt r hroot hok b hb
    have hbl : (fun x => lay[x]! == t) (hexCode b) = true := by
      have := hL.dist_eq b
      rw [hb] at this
      simpa using this.symm
    have hok' : orbOKR 3276 (hexWordArrs G nW).size
        (fun j y x => hexActOK lineTab (hexWordArrs G nW)[j]! y x) (hexCode (hexOfCode root)) cnt
        (fun x => lay[x]! == t) r = true := by
      rw [hexCode_hexOfCode hroot]
      exact hok
    obtain ⟨y, hy, e⟩ := orbOKR_cover hexCode (fun i => wordElt g (hexDecode nW[i]!))
      (fun j y x => hexActOK lineTab (hexWordArrs G nW)[j]! y x) hsurj hact hexCode_injective
      hexCode_lt hok' hbl
    refine ⟨y, ?_, e⟩
    have : Subgroup.closure ((fun i => wordElt g (hexDecode nW[i]!)) ''
        Set.Iio (hexWordArrs G nW).size) ≤ MulAction.stabilizer X (Sum.inr 0 : HexVtx) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi', rfl⟩
      exact hfixL i hi'
    exact this hy
  refine ⟨?_, key y0 5 768 _ (by omega) hOrb5, ?_, key m0 6 2048 _ hm0b hOrb6, ?_, ?_⟩
  · rw [hL.dist_eq (hexOfCode y0)]
    show lay[hexCode (hexOfCode y0)]! = 5
    rw [hexCode_hexOfCode (by omega)]
    exact hlay5
  · rw [hL.dist_eq (hexOfCode m0)]
    show lay[hexCode (hexOfCode m0)]! = 6
    rw [hexCode_hexOfCode hm0b]
    exact hlay6
  · have hnd : (hexNbr lineTab ptL (hexCode (Sum.inr 0 : HexVtx))).Nodup := by
      obtain ⟨h1, h2, h3⟩ := hexPtsOK_spec hp 0 (by norm_num)
      simp only [Nat.mul_zero, Nat.zero_add] at h1 h2 h3
      simp [hexNbr, hexCode, List.range_succ, List.nodup_cons]
      omega
    rw [ncard_neighborSet_eq hp hi _ hnd]
    simp [hexNbr, hexCode]
  · refine two_of_pairs (U := fun a => hexOfCode lineTab[a]!) (k := 3) ?_ ?_
    · intro u hu
      obtain ⟨k, hk, hku⟩ := (mem_hexNbr_line (pts := lineTab) (ptL := ptL)
        (v := ((0 : Fin 2457) : ℕ))).1 ((hexAdj_iff_nbr hp hi (Sum.inr 0) u).1 hu)
      have hku' : lineTab[k]! = hexCode u := by simpa using hku
      refine ⟨k, hk, ?_⟩
      show u = hexOfCode lineTab[k]!
      rw [hku', hexOfCode_hexCode]
    · intro i hi' j hj hij
      obtain ⟨idx, hidx, hA, hB⟩ := hTpairs i hi' j hj hij
      have hidx' : idx < tW.length := by rwa [hexWordArrs_size] at hidx
      have hx := actsAs_listElt hg hT1 hidx'
      have hlt : ∀ k < 3, lineTab[k]! < 819 := fun k hk => by
        simpa using hexPtsOK_lt hp (v := 0) (by norm_num) hk
      refine ⟨wordElt g (hexDecode tW[idx]!), ?_, ?_, ?_, ?_⟩
      · have := smul_hexOfCode_of_actOK hmeet hp hx (by norm_num : 819 < 3276)
          (by norm_num : 819 < 3276) (hTfix idx hidx).1
        rwa [hexOfCode_819] at this
      · exact smul_hexOfCode_of_actOK hmeet hp hx (by omega) (by omega) (hTfix idx hidx).2
      · obtain ⟨q, hq, hxq⟩ := hx ⟨lineTab[0]!, hlt 0 (by norm_num)⟩
        show _ • hexOfCode lineTab[0]! = hexOfCode lineTab[i]!
        rw [hexOfCode_inl (hlt 0 (by norm_num)), hexOfCode_inl (hlt i hi'), hxq]
        exact congrArg Sum.inl (Fin.ext (by rw [← hq]; exact hA))
      · obtain ⟨q, hq, hxq⟩ := hx ⟨lineTab[1]!, hlt 1 (by norm_num)⟩
        show _ • hexOfCode lineTab[1]! = hexOfCode lineTab[j]!
        rw [hexOfCode_inl (hlt 1 (by norm_num)), hexOfCode_inl (hlt j hj), hxq]
        exact congrArg Sum.inl (Fin.ext (by rw [← hq]; exact hB))

end Line

@[expose] def hexB0F : Fin 819 := ⟨hexB0, by decide⟩

@[expose] def hexY0F : Fin 819 := ⟨hexY0, by decide⟩

@[expose] def hexM0F : Fin 2457 := ⟨hexM0 - 819, by decide⟩

section Main

variable {X : Type u} [Group X] [MulAction X HexVtx] [GraphAction X hexGraph]

structure HexGeometry (X : Type u) [Group X] [MulAction X HexVtx] [GraphAction X hexGraph]
    (g : ℕ → X) : Prop where
  polygon : IsGenPolygon hexGraph 6
  cover : ∀ x : HexVtx, ∃ y : X, y • (Sum.inl 0 : HexVtx) = x ∨ y • (Sum.inr 0 : HexVtx) = x
  pt : HexPt X hexGraph (Sum.inl 0) (Sum.inl hexB0F)
  ln : HexLn X hexGraph (Sum.inr 0) (Sum.inl hexY0F) (Sum.inr hexM0F)
  lines : ∀ v : Fin 2457, ∃ y ∈ Subgroup.closure (g '' Set.Iio 8),
    y • (Sum.inr 0 : HexVtx) = Sum.inr v

theorem hexGeometry_of_check {g : ℕ → X} (hg : ∀ j < 8, ActsAs (g j) permArrs[j]!)
    (h : d4GeoCheck lineTab lay0 permArrs = true) : HexGeometry X g := by
  obtain ⟨hp, hi, hmeetOK, hz, hGs, -, -, hl0, hl1, hcyc, hlines, hpt, hln⟩ := d4GeoCheck_spec h
  have hmeet : LineMeet := lineMeet_of_check hp hi hmeetOK
  have hg' : ∀ j < permArrs.size, ActsAs (g j) permArrs[j]! := fun j hj =>
    hg j (by rwa [hGs] at hj)
  have hPt := hexPt_of_check hg' hmeet hp hi hl0 hpt
  have hLn := hexLn_of_check hg' hmeet hp hi hl1 hln
  have e1 : hexOfCode hexB0 = Sum.inl hexB0F := hexOfCode_inl (by decide)
  have e2 : hexOfCode hexY0 = Sum.inl hexY0F := hexOfCode_inl (by decide)
  have e3 : hexOfCode hexM0 = Sum.inr hexM0F := hexOfCode_inr (by decide) (by decide)
  rw [e1] at hPt
  rw [e2, e3] at hLn
  have hL0 : Layers hexGraph 6 (Sum.inl 0) (fun x => ((hexLayBFS lineTab (hexPtL lineTab) 0).1)[
      hexCode x]!) := by
    have := layers_of_hexLayOK hp hi hl0
    rwa [hexOfCode_zero] at this
  have hconn : hexGraph.Connected :=
    { preconnected := fun u v => (hL0.reachable u).symm.trans (hL0.reachable v) }
  have hadj : hexGraph.Adj (Sum.inl 0) (Sum.inr 0) := hexGraph_adj_inl_inr.2 ⟨0, by norm_num, hz⟩
  have hcov := cover_of_flags (X := X) hconn
    (fun b hb => by
      obtain ⟨k, h1, h2⟩ := hPt.flag hadj hb
      exact ⟨k, h1, h2⟩)
    (fun b hb => by
      obtain ⟨k, h1, h2⟩ := hLn.flag hadj.symm hb
      exact ⟨k, h1, h2⟩)
  have hv : ∀ (x : HexVtx) (n : ℕ), (hexGraph.neighborSet x).ncard = n → 2 ≤ n →
      2 ≤ (hexGraph.neighborSet x).encard := by
    intro x n hx hn
    have hfin : (hexGraph.neighborSet x).Finite := Set.finite_of_ncard_ne_zero (by omega)
    rw [← hfin.cast_ncard_eq, hx]
    exact_mod_cast hn
  have hb6 := (hexPtLocalOK_spec (H := hexWordArrs permArrs hexHWords)
    (P := hexWordArrs permArrs hexPWords) rfl rfl hpt).2.2.2.1
  have hb0 := (hexPtLocalOK_spec (H := hexWordArrs permArrs hexHWords)
    (P := hexWordArrs permArrs hexPWords) rfl rfl hpt).2.2.1
  have hpoly := isGenPolygon_hex_cov hp hi hl0 hl1 hcyc (b := hexB0) (by omega) hb6 hcov
    (hv _ 9 hPt.card (by norm_num)) (hv _ 3 hLn.card (by norm_num))
  refine ⟨hpoly, hcov, hPt, hLn, fun v => ?_⟩
  have hsurj : ∀ c < 3276, ∃ w : HexVtx, hexCode w = c := fun c hc =>
    ⟨hexOfCode c, hexCode_hexOfCode hc⟩
  have hact : ∀ j < permArrs.size, ∀ v w : HexVtx,
      hexActOK lineTab permArrs[j]! (hexCode v) (hexCode w) = true → g j • v = w := by
    intro j hj v w hvw
    have := smul_hexOfCode_of_actOK hmeet hp (hg' j hj) (hexCode_lt v) (hexCode_lt w) hvw
    rwa [hexOfCode_hexCode, hexOfCode_hexCode] at this
  have hok : orbOKR 3276 permArrs.size (fun j y x => hexActOK lineTab permArrs[j]! y x)
      (hexCode (Sum.inr 0 : HexVtx)) 2457 (fun x => decide (819 ≤ x) && decide (x < 3276))
      (orbBFS 3276 permArrs.size (hexActS lineTab (hexLineKeyMap lineTab) permArrs)
        819) = true := by
    unfold hexLinesOK at hlines
    exact hlines
  obtain ⟨y, hy, e⟩ := orbOKR_cover hexCode g
    (fun j y x => hexActOK lineTab permArrs[j]! y x) hsurj hact hexCode_injective hexCode_lt hok
    (v := (Sum.inr v : HexVtx)) (by
      have := hexCode_lt (Sum.inr v : HexVtx)
      have h2 : 819 ≤ hexCode (Sum.inr v : HexVtx) := by
        show 819 ≤ 819 + (v : ℕ)
        omega
      simp [h2, this])
  rw [permArrs_size] at hy
  exact ⟨y, hy, e⟩

end Main

theorem hexLay0_dist (h : d4GeoCheck lineTab lay0 permArrs = true) (x : Fin 819) :
    hexGraph.dist (Sum.inl 0) (Sum.inl x) = lay0[(x : ℕ)]! := by
  obtain ⟨hp, hi, -, -, -, -, hlay0, hl0, -⟩ := d4GeoCheck_spec h
  have hL0 := layers_of_hexLayOK hp hi hl0
  rw [hexOfCode_zero] at hL0
  rw [hL0.dist_eq (Sum.inl x), hlay0 x x.2]
  rfl

end CFSG.Quasithin.D4Hex
