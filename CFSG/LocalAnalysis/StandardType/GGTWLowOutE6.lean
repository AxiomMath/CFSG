module

public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE6Aux
public import CFSG.LocalAnalysis.StandardType.GGTWLowEnum
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggTWLE6_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid 3 6 q)
    (w : GGTWLE6) (hf : ggTWLFrameOK 3 6 = true) (h : ggTWLE6Test 3 6 news w = true) :
    GGTWLowE6Outcome (ggTWGens 3 6 (ggTWNNews 3 6 news)) := by
  have h' := h
  simp only [ggTWLE6Test, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc, beq_iff_eq] at h'
  obtain ⟨hsl, hgl, hswl, hotl, hsV, hgwV, hswV, hotV, hwordTg, hwordTs, hcox,
    hpar, hnodup⟩ := h'
  set Ts : List (List (List ℕ)) := List.map (ggTWLMatOfPair 3 (6 - 1)) w.s with hTs
  set Tg : List (List (List ℕ)) := ggTWLGenMats 3 6 news with hTg
  set V : List (List ℕ) := ggTWLOrbitPts 3 6 news w.ot with hV
  let s : Fin 6 → Module.End (ZMod 3) (GGTWE 3 6) := fun i => ggTWLMatLin 3 5 (Ts.getD i.val [])
  have hsl6 : w.s.length = 6 := hsl
  have hs_getD (i : Fin 6) : Ts.getD i.val [] = ggTWLMatOfPair 3 5 (w.s.getD i.val ([], [])) := by
    rw [hTs]; exact l05nL6_Ts_getD (by rw [hsl6]; exact i.isLt)
  have hs_val (i : Fin 6) : GGTWNValid 3 6 (w.s.getD i.val ([], [])) := by
    have hi : i.val < w.s.length := by rw [hsl6]; exact i.isLt
    have hmem : w.s.getD i.val ([], []) ∈ w.s := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    obtain ⟨h1, h2, h3⟩ := hsV _ hmem
    exact ⟨h1, h2, by simpa [ggDepANDot, Nat.mod_mod] using h3⟩
  have hs_refl : ∀ i, GGTWIsRefl (s i) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hs_val i
    refine ⟨ggTWNToZ 3 6 (w.s.getD i.val ([], [])).1, ggTWNToZ 3 6 (w.s.getD i.val ([], [])).2,
      l05nL6_dot_of_valid ⟨h1, h2, h3⟩, ?_⟩
    show s i = ggTWRefl _ _
    rw [show s i = ggTWLMatLin 3 5 (Ts.getD i.val []) from rfl, hs_getD i,
      (ggTWLMatOfPair_lin (p := 3) (N := 6) ⟨h1, h2, h3⟩).2]
  have hTs_wf : ∀ t ∈ Ts, ggTWLMatWF 5 t := by
    intro t ht
    rw [hTs] at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨h1, h2, h3⟩ := hsV q hq
    exact (ggTWLMatOfPair_lin (p := 3) (N := 6)
      (q := q) ⟨h1, h2, by simpa [ggDepANDot, Nat.mod_mod] using h3⟩).1
  have hTg_wf : ∀ t ∈ Tg, ggTWLMatWF 5 t := by
    intro t ht
    rw [hTg, ggTWLGenMats] at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
    rw [List.mem_range] at hg
    exact (ggTWLMatOfPair_lin (p := 3) (N := 6) (q := ggTWNGen 3 6 news g)
      (ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews
        (by simpa using hg))).1
  have hTg_lin_mem : ∀ t ∈ Tg,
      ggTWLMatLin 3 5 t ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) := by
    intro t ht
    rw [hTg, ggTWLGenMats] at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
    rw [List.mem_range] at hg
    rw [(ggTWLMatOfPair_lin (p := 3) (N := 6) (q := ggTWNGen 3 6 news g)
      (ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews
        (by simpa using hg))).2]
    exact ggTWNGen_mem (p := 3) (N := 6) (by norm_num) (by norm_num) (by simpa using hg)
  have hTs_lin_mem : ∀ t ∈ Ts, ggTWLMatLin 3 5 t ∈ Submonoid.closure (Set.range s) := by
    intro t ht
    rw [hTs] at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    refine Submonoid.subset_closure ⟨⟨k, by simpa [hsl6] using hk⟩, ?_⟩
    show ggTWLMatLin 3 5 (Ts.getD k []) = ggTWLMatLin 3 5 (ggTWLMatOfPair 3 5 (w.s[k]))
    rw [hTs, l05nL6_Ts_getD (by simpa using hk), List.getD_eq_getElem _ _ hk]
  have hTglen : Tg.length = 5 + news.length := by
    rw [hTg, ggTWLGenMats]; simp [List.length_map, List.length_range]
  have hs_mem : ∀ i, s i ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) := by
    intro i
    have hi : i.val < w.s.length := by rw [hsl6]; exact i.isLt
    have hwsw : ∀ k ∈ w.sw.getD i.val [], k < Tg.length := by
      intro k hk
      have hmem : w.sw.getD i.val [] ∈ w.sw := by
        rw [List.getD_eq_getElem _ _ (by rw [hswl]; exact i.isLt)]
        exact List.getElem_mem _
      have := hswV _ hmem k hk
      rwa [hTglen]
    have hwewf : ggTWLMatWF 5 (ggTWLWordMat 3 5 Tg (w.sw.getD i.val [])) :=
      (ggTWLWordMat_lin (p := 3) (d := 5) hTg_wf hwsw).1
    have hmemTs : Ts.getD i.val [] ∈ Ts := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi)]
      exact List.getElem_mem _
    have heq := (ggTWLMatEq_iff (hTs_wf _ hmemTs) hwewf).mp (hwordTg i.val i.isLt)
    rw [show s i = ggTWLMatLin 3 5 (Ts.getD i.val []) from rfl, heq]
    exact l05nL6_word_mem hTg_wf hTg_lin_mem hwsw
  have hS_lin_mem : ∀ g < 5 + news.length,
      ggTWLMatLin 3 5 (Tg.getD g []) ∈ Submonoid.closure (Set.range s) := by
    intro g hg
    have hw : ∀ k ∈ w.gw.getD g [], k < Ts.length := by
      intro k hk
      have hmem : w.gw.getD g [] ∈ w.gw := by
        rw [List.getD_eq_getElem _ _ (by rw [hgl]; exact hg)]
        exact List.getElem_mem _
      have := hgwV _ hmem k hk
      rwa [hTs, List.length_map, hsl6]
    have hwewf : ggTWLMatWF 5 (ggTWLWordMat 3 5 Ts (w.gw.getD g [])) :=
      (ggTWLWordMat_lin (p := 3) (d := 5) hTs_wf hw).1
    have hmemTg : Tg.getD g [] ∈ Tg := by
      rw [List.getD_eq_getElem _ _ (by rw [hTglen]; exact hg)]
      exact List.getElem_mem _
    have heq := (ggTWLMatEq_iff (hTg_wf _ hmemTg) hwewf).mp (hwordTs g hg)
    rw [heq]
    exact l05nL6_word_mem hTs_wf hTs_lin_mem hw
  have hgen_lin : ∀ x ∈ ggTWGens 3 6 (ggTWNNews 3 6 news),
      x ∈ Submonoid.closure (Set.range s) := by
    intro x hx
    rw [ggTWGens] at hx
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := hx
      have hiv : i.val + 1 < 6 := by have := i.isLt; omega
      have hgv : GGTWNValid 3 6 (ggTWNGen 3 6 news i.val) :=
        ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews
          (by have := i.isLt; simp only [Nat.reduceSub]; omega)
      have hgen : ggTWNGen 3 6 news i.val = (ggTWNH 3 6 i.val, ggTWNA 3 6 i.val) := by
        simp only [ggTWNGen, if_pos hiv]
      have hlin : ggTWLMatLin 3 5 (Tg.getD i.val []) =
          ggTWRefl (ggTWh 3 6 i) (ggTWα 3 6 i) := by
        rw [l05nL6_Tg_getD (by have := i.isLt; simp only [Nat.reduceSub]; omega),
          (ggTWLMatOfPair_lin (p := 3) (N := 6) hgv).2, hgen]
        change ggTWRefl (ggTWNToZ 3 6 (ggTWNH 3 6 i.val)) (ggTWNToZ 3 6 (ggTWNA 3 6 i.val)) =
          ggTWRefl (ggTWh 3 6 i) (ggTWα 3 6 i)
        rw [ggTWNH_toZ, ggTWNA_toZ]
      change ggTWRefl (ggTWh 3 6 i) (ggTWα 3 6 i) ∈ Submonoid.closure (Set.range s)
      rw [← hlin]
      exact hS_lin_mem i.val (by have := i.isLt; simp only [Nat.reduceSub]; omega)
    · obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := ht
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      set g := 5 + k with hgdef
      have hglt : g < 5 + news.length := by rw [hgdef]; omega
      have hgv : GGTWNValid 3 6 (ggTWNGen 3 6 news g) :=
        ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews (by simpa using hglt)
      have hgen : ggTWNGen 3 6 news g = news[k] := by
        rw [hgdef, ggTWNGen, if_neg (by omega),
          show 5 + k + 1 - 6 = k by omega, List.getD_eq_getElem _ _ hk]
      have hlin : ggTWLMatLin 3 5 (Tg.getD g []) =
          ggTWRefl (ggTWNToZ 3 6 (news[k]).1) (ggTWNToZ 3 6 (news[k]).2) := by
        rw [l05nL6_Tg_getD hglt, (ggTWLMatOfPair_lin (p := 3) (N := 6) hgv).2, hgen]
      change ggTWRefl (ggTWNToZ 3 6 (news[k]).1) (ggTWNToZ 3 6 (news[k]).2) ∈
        Submonoid.closure (Set.range s)
      rw [← hlin]
      exact hS_lin_mem g hglt
  have hclosure : Submonoid.closure (Set.range s) =
      Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) := by
    refine le_antisymm ?_ ?_
    · rw [Submonoid.closure_le]
      rintro x ⟨i, rfl⟩
      exact hs_mem i
    · rw [Submonoid.closure_le]
      exact hgen_lin
  have hcoxrel : ∀ i j : Fin 6, (s i * s j) ^ (CoxeterMatrix.E₆.M i j) = 1 := by
    intro i j
    have hA : ggTWLMatWF 5 (Ts.getD i.val []) := hTs_wf _ (by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hsl6]; exact i.isLt)]
      exact List.getElem_mem _)
    have hB : ggTWLMatWF 5 (Ts.getD j.val []) := hTs_wf _ (by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hsl6]; exact j.isLt)]
      exact List.getElem_mem _)
    obtain ⟨hAB, hmul⟩ := ggTWLMatMul_lin (p := 3) (d := 5) hA hB
    obtain ⟨hP, hpow⟩ := ggTWLMatPow_lin (p := 3) (d := 5) hAB (ggTWLE6M i.val j.val)
    obtain ⟨hOne, hOneLin⟩ := ggTWLMatOne_lin (p := 3) (d := 5)
    have heq := (ggTWLMatEq_iff hP hOne).mp (hcox i.val i.isLt j.val j.isLt)
    have hmain : (s i * s j) ^ (ggTWLE6M i.val j.val) = 1 := by
      calc (s i * s j) ^ (ggTWLE6M i.val j.val)
          = (ggTWLMatLin 3 5 (Ts.getD i.val []) *
              ggTWLMatLin 3 5 (Ts.getD j.val [])) ^ (ggTWLE6M i.val j.val) := rfl
        _ = (ggTWLMatLin 3 5 (ggTWLMatMul 3 5 (Ts.getD i.val []) (Ts.getD j.val []))) ^
              (ggTWLE6M i.val j.val) := by rw [hmul]
        _ = ggTWLMatLin 3 5 (ggTWLMatPow 3 5
              (ggTWLMatMul 3 5 (Ts.getD i.val []) (Ts.getD j.val []))
              (ggTWLE6M i.val j.val)) := hpow.symm
        _ = ggTWLMatLin 3 5 (ggTWLMatOne 5) := heq
        _ = 1 := hOneLin
    rwa [l05nL6_e6M i j] at hmain
  haveI : Finite (Module.End (ZMod 3) (GGTWE 3 6)) :=
    Finite.of_injective (fun f : Module.End (ZMod 3) (GGTWE 3 6) => (f : GGTWE 3 6 → GGTWE 3 6))
      (fun a b hab => LinearMap.ext (congrFun hab))
  have hframe_card : 720 ≤ Nat.card (Submonoid.closure (ggTWFrameGens 3 6)) :=
    ggTWLFrameOK_sound (p := 3) (N := 6) (by norm_num) (by norm_num) hf
  have hFfix : ∀ f ∈ Submonoid.closure (ggTWFrameGens 3 6), f (ggTWx 3 6) = ggTWx 3 6 := by
    intro f hf
    induction hf using Submonoid.closure_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact l05nL6_frame_gen_fixes i
    | one => rfl
    | mul x y _ _ ihx ihy => rw [Module.End.mul_apply, ihy, ihx]
  have hFle : Submonoid.closure (ggTWFrameGens 3 6) ≤
      Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) := by
    rw [Submonoid.closure_le]
    intro x hx
    exact Submonoid.subset_closure (Or.inl hx)
  have hsim := l05nL6_sim_orbit hnews w.ot hpar
    (by
      intro j hj
      exact hotV (w.ot.getD j (0, 0)) (by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _))
  obtain ⟨hVlen, hVptlen, hVapply, hVmem⟩ := hsim
  have hfoldlen : ∀ (L0 : List (List ℕ)) (l : List (Nat × Nat)),
      (l.foldl (fun L e => L ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (L.getD e.1 [])]) L0).length
        = l.length + L0.length := by
    intro L0 l
    induction l generalizing L0 with
    | nil => simp
    | cons e l ih =>
        calc (List.foldl (fun L e' =>
                L ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e'.2) (L.getD e'.1 [])]) L0 (e :: l)).length
            = (List.foldl (fun L e' =>
                L ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e'.2) (L.getD e'.1 [])])
                (L0 ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (L0.getD e.1 [])]) l).length := by
              rw [List.foldl_cons]
          _ = l.length +
                (L0 ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (L0.getD e.1 [])]).length := ih _
          _ = l.length + (L0.length + 1) := by rw [List.length_append, List.length_singleton]
          _ = (e :: l).length + L0.length := by rw [List.length_cons]; omega
  have hVlen72 : V.length = 72 := by
    rw [hV, ggTWLOrbitPts, hfoldlen, hotl]
    norm_num
  let Gf : Fin 72 → Module.End (ZMod 3) (GGTWE 3 6) :=
    fun k => (l05nL6_endFold news w.ot).getD k.val 1
  have hGfapply (k : Fin 72) : Gf k (ggTWx 3 6) = ggTWNToZ 3 6 (V.getD k.val []) := by
    have hk : k.val < (ggTWLOrbitPts 3 6 news w.ot).length := by rw [hVlen72]; exact k.isLt
    exact hVapply k.val hk
  have hGfmem (k : Fin 72) : Gf k ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) :=
    hVmem k.val (by rw [hVlen, hVlen72]; exact k.isLt)
  have hGfptlen (k : Fin 72) : (V.getD k.val []).length = 5 :=
    hVptlen k.val (by rw [hVlen72]; exact k.isLt)
  have hinv : ∀ g ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)),
      ∃ h ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)), h * g = 1 :=
    l05nL6_closure_inv (l05nL6_S_invol hnews)
  have hdistinct : ∀ i j : Fin 72, i ≠ j → ggTWNToZ 3 6 (V.getD i.val []) ≠
      ggTWNToZ 3 6 (V.getD j.val []) := by
    intro i j hij htoZ
    have hui : (V.getD i.val []).length = 5 := hGfptlen i
    have huj : (V.getD j.val []).length = 5 := hGfptlen j
    have hveq : ggTWLVecEq 3 (V.getD i.val []) (V.getD j.val []) = true :=
      l05nL6_veceq_of_toZ hui huj htoZ
    have hmat : ggTWLMatEq 3 [V.getD i.val []] [V.getD j.val []] = true := by
      simpa [ggTWLMatEq] using hveq
    have hi : i.val < V.length := by rw [hVlen72]; exact i.isLt
    have hj : j.val < V.length := by rw [hVlen72]; exact j.isLt
    have hnod : ggTWLNodup 3 (List.map (fun v => [v]) V) = true := hnodup
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hlt | hgt
    · have h := l05nL6_nodup_getD hnod i.val j.val hlt (by rw [List.length_map]; exact hj)
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
        List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
        ← List.getD_eq_getElem V [] hi, ← List.getD_eq_getElem V [] hj] at h
      rw [h] at hmat
      exact Bool.false_ne_true hmat
    · have hveq' : ggTWLVecEq 3 (V.getD j.val []) (V.getD i.val []) = true :=
        l05nL6_veceq_of_toZ huj hui htoZ.symm
      have hmat' : ggTWLMatEq 3 [V.getD j.val []] [V.getD i.val []] = true := by
        simpa [ggTWLMatEq] using hveq'
      have h := l05nL6_nodup_getD hnod j.val i.val hgt (by rw [List.length_map]; exact hi)
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
        List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
        ← List.getD_eq_getElem V [] hj, ← List.getD_eq_getElem V [] hi] at h
      rw [h] at hmat'
      exact Bool.false_ne_true hmat'
  let φ : (Submonoid.closure (ggTWFrameGens 3 6)) × Fin 72 →
      Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) := fun x =>
    ⟨Gf x.2 * (x.1 : Module.End (ZMod 3) (GGTWE 3 6)),
      Submonoid.mul_mem _ (hGfmem x.2) (hFle x.1.2)⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨f1, k1⟩ ⟨f2, k2⟩ heq
    have hx : Gf k1 (ggTWx 3 6) = Gf k2 (ggTWx 3 6) := by
      have h := congrArg (fun z : Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) =>
        (z : Module.End (ZMod 3) (GGTWE 3 6)) (ggTWx 3 6)) heq
      simpa only [φ, Module.End.mul_apply, hFfix f1 f1.2, hFfix f2 f2.2] using h
    have hk : k1 = k2 := by
      by_contra hne
      exact hdistinct k1 k2 hne (by rw [← hGfapply k1, ← hGfapply k2]; exact hx)
    subst hk
    obtain ⟨h, hhmem, hhg⟩ := hinv (Gf k1) (hGfmem k1)
    have hfe : (f1 : Module.End (ZMod 3) (GGTWE 3 6)) = f2 := by
      have h2 : Gf k1 * (f1 : Module.End (ZMod 3) (GGTWE 3 6)) =
          Gf k1 * (f2 : Module.End (ZMod 3) (GGTWE 3 6)) := by
        simpa only [φ] using congrArg
          (fun z : Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) =>
            (z : Module.End (ZMod 3) (GGTWE 3 6))) heq
      have h3 := congrArg (fun z : Module.End (ZMod 3) (GGTWE 3 6) => h * z) h2
      rwa [← mul_assoc, hhg, one_mul, ← mul_assoc, hhg, one_mul] at h3
    exact Prod.ext (Subtype.ext hfe) rfl
  have hcard : 51840 ≤ Nat.card (Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news))) := by
    have hle := Nat.card_le_card_of_injective φ hφinj
    rw [Nat.card_prod, Nat.card_fin] at hle
    calc 51840 = 720 * 72 := by norm_num
      _ ≤ Nat.card (Submonoid.closure (ggTWFrameGens 3 6)) * 72 :=
          Nat.mul_le_mul_right 72 hframe_card
      _ ≤ Nat.card (Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news))) := hle
  exact ⟨hcard, s, hs_refl, hclosure, hcoxrel⟩

end CFSG.StandardType

end
