module

public import CFSG.LocalAnalysis.StandardType.GGDepELLowPZA
public import CFSG.LocalAnalysis.StandardType.GGDepELNatWord
public import CFSG.LocalAnalysis.StandardType.GGTWLowEnum
public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE6Aux
public import CFSG.LocalAnalysis.StandardType.GGTWLowPZA

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall
  Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nPB_isRefl_of_valid {q : GGDepANPair} (hq : GGDepELNValid q) :
    GGDepELIsRefl (ggDepELNRflOf q) :=
  ⟨ggDepELToZ q.1, ggDepELToZ q.2, ggDepELNValid_dot hq, rfl⟩

private lemma l05nPB_refl_mul_self_of_isRefl (r : Module.End (ZMod 3) (GGDepAE 3 6))
    (hr : GGDepELIsRefl r) : r * r = 1 := by
  rcases hr with ⟨c, f, h, rfl⟩
  exact l05nL6_refl_invol c f h

private lemma l05nPB_fix_refl {q : GGDepANPair} {z : List ℕ} (hq : GGDepELNValid q)
    (hz : z.length = 6) (h : ggDepANDot 3 q.2 z = 0) :
    ggDepELNRflOf q (ggDepELToZ z) = ggDepELToZ z := by
  have hdot : ggDepAdot (ggDepELToZ q.2) (ggDepELToZ z) = 0 := by
    have hcast := ggDepELDot_cast (a := q.2) (b := z) hq.2.1 hz
    rw [h] at hcast
    exact hcast.symm
  show ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2) (ggDepELToZ z) = ggDepELToZ z
  rw [l05nNC_refl_apply, hdot, zero_smul, sub_zero]

private lemma l05nPB_conj_fold (C : Submonoid (Module.End (ZMod 3) (GGDepAE 3 6)))
    (q : GGDepANPair) (hq : GGDepELNValid q) :
    ∀ fixes : List GGDepANPair,
      (∀ g ∈ fixes, GGDepELNValid g) →
      (∀ g ∈ fixes, ggDepELNRflOf g ∈ C) →
      ∃ G ∈ C, ∃ G' ∈ C, G * G' = 1 ∧
        GGDepELNValid (fixes.foldr (fun g acc => ggDepANConj 3 acc g) q) ∧
        ggDepELNRflOf (fixes.foldr (fun g acc => ggDepANConj 3 acc g) q) =
          G * ggDepELNRflOf q * G' := by
  intro fixes
  induction fixes with
  | nil =>
      intro _ _
      exact ⟨1, C.one_mem, 1, C.one_mem, by simp, by simpa using hq, by simp⟩
  | cons g gs ih =>
      intro hfixv hfixmem
      have hgv : GGDepELNValid g := hfixv g (by simp)
      have hgsv : ∀ g' ∈ gs, GGDepELNValid g' := fun g' hg' => hfixv g' (by simp [hg'])
      have hgmem : ggDepELNRflOf g ∈ C := hfixmem g (by simp)
      have hgsmem : ∀ g' ∈ gs, ggDepELNRflOf g' ∈ C := fun g' hg' => hfixmem g' (by simp [hg'])
      obtain ⟨G, hG, G', hG', hGG', hvrest, hEq⟩ := ih hgsv hgsmem
      refine ⟨ggDepELNRflOf g * G, Submonoid.mul_mem _ hgmem hG,
        G' * ggDepELNRflOf g, Submonoid.mul_mem _ hG' hgmem, ?_, ?_, ?_⟩
      · calc (ggDepELNRflOf g * G) * (G' * ggDepELNRflOf g)
            = ggDepELNRflOf g * (G * G') * ggDepELNRflOf g := by simp only [mul_assoc]
          _ = ggDepELNRflOf g * 1 * ggDepELNRflOf g := by rw [hGG']
          _ = ggDepELNRflOf g * ggDepELNRflOf g := by rw [mul_one]
          _ = 1 := l05nPB_refl_mul_self_of_isRefl _ (l05nPB_isRefl_of_valid hgv)
      · rw [List.foldr_cons]
        exact (ggDepELNConj_rfl hvrest hgv).1
      · rw [List.foldr_cons, (ggDepELNConj_rfl hvrest hgv).2, hEq]
        simp only [mul_assoc]

private lemma l05nPB_word_cons (news : List GGDepANPair) (q : GGDepANPair) (g : ℕ)
    (w : List ℕ) :
    ggDepELNWord news q (g :: w) =
      ggDepANConj 3 (ggDepELNWord news q w) (ggDepELNGen news g) := by
  simp [ggDepELNWord]

private lemma l05nPB_word_J {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (S : Submonoid (Module.End (ZMod 3) (GGDepAE 3 6)))
    (w : List ℕ) (hw : ∀ g ∈ w, g < 6 + news.length)
    (hmem : ∀ g ∈ w, ggDepELNRflOf (ggDepELNGen news g) ∈ S)
    (q : GGDepANPair) (hq : GGDepELNValid q) (hqm : ggDepELNRflOf q ∈ S) :
    GGDepELNValid (ggDepELNWord news q w) ∧ ggDepELNRflOf (ggDepELNWord news q w) ∈ S := by
  induction w generalizing q with
  | nil => simpa [ggDepELNWord] using ⟨hq, hqm⟩
  | cons g w ih =>
      rw [l05nPB_word_cons]
      have hg : g < 6 + news.length := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < 6 + news.length := fun g' hg' => hw g' (by simp [hg'])
      have hmem' : ∀ g' ∈ w, ggDepELNRflOf (ggDepELNGen news g') ∈ S :=
        fun g' hg' => hmem g' (by simp [hg'])
      obtain ⟨ihV, ihM⟩ := ih hw' hmem' q hq hqm
      have hG : GGDepELNValid (ggDepELNGen news g) := ggDepELNGen_valid hnews hg
      refine ⟨(ggDepELNConj_rfl ihV hG).1, ?_⟩
      rw [(ggDepELNConj_rfl ihV hG).2]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g (by simp)) ihM) (hmem g (by simp))

private lemma l05nPB_orbit_involution (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (z : GGDepAE 3 6)
    (hfix : ∀ s ∈ ggDepELPZFixRefl gens z, s * s = 1) :
    ∀ t ∈ ggDepELPZOrbit gens z, t * t = 1 := by
  intro t ht
  rcases ht with ⟨r, hrJ, g, hg, g', hg', hgg', rfl⟩
  have hrr : r * r = 1 := l05nPB_refl_mul_self_of_isRefl r hrJ.2
  have hg'g : g' * g = 1 := mul_eq_one_comm.mp hgg'
  calc (g * r * g') * (g * r * g') = g * (r * (g' * g) * r) * g' := by simp only [mul_assoc]
    _ = g * (r * 1 * r) * g' := by rw [hg'g]
    _ = g * (r * r) * g' := by rw [mul_one]
    _ = g * 1 * g' := by rw [hrr]
    _ = 1 := by rw [mul_one, hgg']

private lemma l05nPB_foldl_lcm_dvd {L : List (ℕ × Bool)} {N a : ℕ} (ha : a ∣ N)
    (h : ∀ o ∈ L, o.1 ∣ N) : (L.foldl (fun k o => Nat.lcm k o.1) a) ∣ N := by
  induction L generalizing a with
  | nil => simpa using ha
  | cons o os ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.lcm_dvd ha (h o (by simp))) (fun o' ho' => h o' (by simp [ho']))

theorem ggDepELPZTest_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (y : List ℕ) (hy : y.length = 6) (w : GGDepELPZ)
    (h : ggDepELPZTest news y w = true) :
    (w.c0 : ZMod 3) ≠ 0 ∧
      GGDepELPZBad (ggDepELGens (ggDepELNNews news))
        (ggDepELx + (w.c0 : ZMod 3) • ggDepELToZ y) := by
  simp only [ggDepELPZTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  set fixP : List GGDepANPair :=
    w.fixs.map (fun e => ggDepELNWord news (ggDepELNGen news e.1) e.2) with hfixP
  set orbP : List GGDepANPair := w.orbs.map (fun e =>
      e.2.2.foldr (fun k acc => ggDepANConj 3 acc (fixP.getD k ([], [])))
        (ggDepELNWord news (ggDepELNGen news e.1) e.2.1)) with horbP
  set Om : List (List (List ℕ)) := orbP.map (ggTWLMatOfPair 3 6) with hOm
  set a : List (List ℕ) := ggTWLWordMat 3 6 Om w.cen with ha
  set A : Set (Module.End (ZMod 3) (GGDepAE 3 6)) := ggDepELGens (ggDepELNNews news) with hA
  set zvec : GGDepAE 3 6 := ggDepELx + (w.c0 : ZMod 3) • ggDepELToZ y with hzvec
  set M : Submonoid (Module.End (ZMod 3) (GGDepAE 3 6)) :=
    Submonoid.closure (ggDepELPZOrbit A zvec) with hM
  set Sm : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
    {g | ∃ t ∈ Om, g = ggTWLMatLin 3 6 t} with hSm
  set K : ℕ := (w.subs.map (ggDepELSubOrd Om)).foldl (fun k o => Nat.lcm k o.1) 1 with hK
  obtain ⟨hX, harith⟩ := h
  obtain ⟨hW, ha_ne, ha_comm⟩ := hX
  obtain ⟨⟨⟨⟨⟨⟨⟨hc0, hc0p⟩, hfixs⟩, horbs⟩, hsubs⟩, hcenlt⟩, hfixdot⟩, henum⟩ := hW
  have hztest : ggDepELToZ (ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 w.c0 y)) = zvec := by
    rw [hzvec, ggDepELToZ_add ggDepELNX_length (ggDepELSmul_length w.c0 hy), ggDepELNX_toZ,
      show ggDepELToZ (ggDepANSmul 3 w.c0 y) = (w.c0 : ZMod 3) • ggDepELToZ y from
        ggDepELToZ_smul hy w.c0]
  refine ⟨?_, ?_⟩
  · intro hz
    have hdvd : 3 ∣ w.c0 := (ZMod.natCast_eq_zero_iff w.c0 3).mp hz
    have hle : 3 ≤ w.c0 := Nat.le_of_dvd hc0 hdvd
    omega
  · rw [GGDepELPZBad]
    haveI : Fintype (Module.End (ZMod 3) (GGDepAE 3 6)) :=
      Fintype.ofInjective
        (fun f : Module.End (ZMod 3) (GGDepAE 3 6) => (f : GGDepAE 3 6 → GGDepAE 3 6))
        (fun f g h => LinearMap.ext (fun x => congrFun h x))
    have hfix_all : ∀ s ∈ fixP, GGDepELNValid s ∧
        ggDepELNRflOf s ∈ ggDepELPZFixRefl A zvec := by
      intro s hs
      have hdotmod : ggDepANDot 3 s.2 (ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 w.c0 y)) = 0 :=
        beq_iff_eq.mp (hfixdot s hs)
      rw [hfixP] at hs
      rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
      obtain ⟨he1, he2⟩ := hfixs e he
      have hvg : GGDepELNValid (ggDepELNGen news e.1) := ggDepELNGen_valid hnews he1
      have hmg : ggDepELNRflOf (ggDepELNGen news e.1) ∈ Submonoid.closure A :=
        ggDepELNGen_mem he1
      obtain ⟨hv, hm⟩ := ggDepELNWord_valid_mem hnews hvg hmg he2
      have hzl : (ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 w.c0 y)).length = 6 :=
        ggDepELAdd_length ggDepELNX_length (ggDepELSmul_length w.c0 hy)
      have hfixz : ggDepELNRflOf (ggDepELNWord news (ggDepELNGen news e.1) e.2) zvec = zvec := by
        rw [← hztest]
        exact l05nPB_fix_refl hv hzl hdotmod
      exact ⟨hv, hm, l05nPB_isRefl_of_valid hv, hfixz⟩
    have horbit : ∀ q ∈ orbP, GGDepELNValid q ∧
        ggDepELNRflOf q ∈ ggDepELPZOrbit A zvec := by
      intro q hq
      rw [horbP] at hq
      rcases List.mem_map.mp hq with ⟨e, he, rfl⟩
      obtain ⟨⟨heJ, heJw⟩, hefix⟩ := horbs e he
      have he1lt : e.1 < 6 := ggDepELNInJ_lt heJ
      let qin : GGDepANPair := ggDepELNWord news (ggDepELNGen news e.1) e.2.1
      have hJmem : ggDepELNRflOf (ggDepELNGen news e.1) ∈
          Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
            Set.univ) := by
        have hgen : ggDepELNGen news e.1 = (ggDepELNH e.1, ggDepELNA e.1) := by
          rw [ggDepELNGen, if_pos he1lt]
        rw [hgen]
        refine Submonoid.subset_closure ⟨⟨⟨e.1, he1lt⟩, (ggDepELNInJ_iff ⟨e.1, he1lt⟩).mp heJ⟩,
          Set.mem_univ _, ?_⟩
        change ggDepELrefl ⟨e.1, he1lt⟩ =
          ggDepARefl (ggDepELToZ (ggDepELNH e.1)) (ggDepELToZ (ggDepELNA e.1))
        rw [ggDepELNH_toZ ⟨e.1, he1lt⟩, ggDepELNA_toZ ⟨e.1, he1lt⟩]
        rfl
      have hmemJ : ∀ g ∈ e.2.1, ggDepELNRflOf (ggDepELNGen news g) ∈
          Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
            Set.univ) := by
        intro g hg
        have hgJ : ggDepELNInJ g = true := heJw g hg
        have hglt : g < 6 := ggDepELNInJ_lt hgJ
        have hgen : ggDepELNGen news g = (ggDepELNH g, ggDepELNA g) := by
          rw [ggDepELNGen, if_pos hglt]
        rw [hgen]
        refine Submonoid.subset_closure ⟨⟨⟨g, hglt⟩, (ggDepELNInJ_iff ⟨g, hglt⟩).mp hgJ⟩,
          Set.mem_univ _, ?_⟩
        change ggDepELrefl ⟨g, hglt⟩ =
          ggDepARefl (ggDepELToZ (ggDepELNH g)) (ggDepELToZ (ggDepELNA g))
        rw [ggDepELNH_toZ ⟨g, hglt⟩, ggDepELNA_toZ ⟨g, hglt⟩]
        rfl
      have hwlt : ∀ g ∈ e.2.1, g < 6 + news.length := by
        intro g hg
        have := ggDepELNInJ_lt (heJw g hg)
        omega
      obtain ⟨hqinV, hqinM⟩ := l05nPB_word_J hnews
        (Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
          Set.univ)) e.2.1 hwlt hmemJ (ggDepELNGen news e.1)
        (ggDepELNGen_valid hnews (by omega)) hJmem
      have hqinJ : ggDepELNRflOf qin ∈ ggDepELPZJRefl := by
        rw [ggDepELPZJRefl]
        exact ⟨hqinM, l05nPB_isRefl_of_valid hqinV⟩
      set fixes : List GGDepANPair := e.2.2.map (fun k => fixP.getD k ([], [])) with hfixes
      have hgetmem : ∀ k ∈ e.2.2, fixP.getD k ([], []) ∈ fixP := by
        intro k hk
        have hklt : k < fixP.length := hefix k hk
        rw [List.getD_eq_getElem (l := fixP) (d := ([], [])) (n := k) hklt]
        exact List.getElem_mem hklt
      have hfixe_v : ∀ g ∈ fixes, GGDepELNValid g := by
        intro g hg
        rw [hfixes] at hg
        rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
        exact (hfix_all _ (hgetmem k hk)).1
      have hfixe_m : ∀ g ∈ fixes,
          ggDepELNRflOf g ∈ Submonoid.closure (ggDepELPZFixRefl A zvec) := by
        intro g hg
        rw [hfixes] at hg
        rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
        exact Submonoid.subset_closure (hfix_all _ (hgetmem k hk)).2
      obtain ⟨G, hG, G', hG', hGG', hvfold, hfold⟩ :=
        l05nPB_conj_fold (Submonoid.closure (ggDepELPZFixRefl A zvec)) qin hqinV
          fixes hfixe_v hfixe_m
      have hfoldmap : fixes.foldr (fun g acc => ggDepANConj 3 acc g) qin =
          e.2.2.foldr (fun k acc => ggDepANConj 3 acc (fixP.getD k ([], []))) qin :=
        List.foldr_map
      rw [hfoldmap] at hvfold hfold
      exact ⟨hvfold, ⟨ggDepELNRflOf qin, hqinJ, G, hG, G', hG', hGG', hfold⟩⟩
    have hTWC : ∀ t ∈ Om, ∃ q ∈ orbP, t = ggTWLMatOfPair 3 6 q := by
      intro t ht
      rw [hOm] at ht
      rcases List.mem_map.mp ht with ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    have hOm_valid : ∀ t ∈ Om, ggTWLMatWF 6 t := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := hTWC t ht
      exact (ggTWLMatOfPair_lin (p := 3) (N := 7) (horbit q hq).1).1
    have hSm_refl : ∀ s ∈ Sm, s * s = 1 := by
      intro s hs
      rw [hSm] at hs
      rcases hs with ⟨t, ht, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hTWC t ht
      rw [(ggTWLMatOfPair_lin (p := 3) (N := 7) (horbit q hq).1).2]
      exact l05nPB_refl_mul_self_of_isRefl _ (l05nPB_isRefl_of_valid (horbit q hq).1)
    have hS_orbit : ∀ s ∈ ggDepELPZOrbit A zvec, s * s = 1 :=
      l05nPB_orbit_involution A zvec (fun s hs => l05nPB_refl_mul_self_of_isRefl s hs.2.1)
    have hSm_sub : Sm ⊆ (M : Set (Module.End (ZMod 3) (GGDepAE 3 6))) := by
      intro s hs
      rw [hSm] at hs
      rcases hs with ⟨t, ht, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hTWC t ht
      rw [(ggTWLMatOfPair_lin (p := 3) (N := 7) (horbit q hq).1).2]
      exact Submonoid.subset_closure (horbit q hq).2
    have hSmdvdM : Nat.card ↥(Submonoid.closure Sm) ∣ Nat.card ↥M :=
      ggDepEL_card_dvd (S := ggDepELPZOrbit A zvec) (S' := Sm) hS_orbit hSm_sub
    have hSubOrd : ∀ gs ∈ w.subs, (ggDepELSubOrd Om gs).1 ∣
        Nat.card ↥(Submonoid.closure Sm) := by
      intro gs hgs
      set T : List (List (List ℕ)) := gs.map (ggTWLWordMat 3 6 Om) with hT
      set par : List (Nat × Nat) := ggTWLBfsTree 3 6 T 1000 with hpar
      have hEnumOK : ggTWLEnumOK 3 6 T par = true := by
        have hmem : ggDepELSubOrd Om gs ∈ w.subs.map (ggDepELSubOrd Om) :=
          List.mem_map.mpr ⟨gs, hgs, rfl⟩
        have hh := henum _ hmem
        simpa only [ggDepELSubOrd, hT, hpar] using hh
      have hwu : ∀ u ∈ gs, ∀ k ∈ u, k < Om.length := by
        intro u hu k hk
        simpa only [hOm, List.length_map] using hsubs gs hgs u hu k hk
      have hTvalid : ∀ t ∈ T, ggTWLMatWF 6 t := by
        intro t ht
        rw [hT] at ht
        rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
        exact (ggTWLWordMat_lin (p := 3) (d := 6) hOm_valid (hwu u hu)).1
      have hEnumRes := ggTWLEnum_sound (p := 3) (d := 6) hTvalid par hEnumOK
      have hsubSgs : {g | ∃ t ∈ T, g = ggTWLMatLin 3 6 t} ⊆
          (Submonoid.closure Sm : Set (Module.End (ZMod 3) (GGDepAE 3 6))) := by
        rintro g ⟨t, ht, rfl⟩
        rw [hT] at ht
        rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
        rw [(ggTWLWordMat_lin (p := 3) (d := 6) hOm_valid (hwu u hu)).2]
        refine Submonoid.list_prod_mem (Submonoid.closure Sm) (fun g hg => ?_)
        rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
        have hklt : k < Om.length := hwu u hu k hk
        rw [List.getD_eq_getElem (l := Om) (d := []) (n := k) hklt]
        exact Submonoid.subset_closure ⟨Om[k], List.getElem_mem hklt, rfl⟩
      have hCardEq : Nat.card ↥(Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin 3 6 t}) =
          (ggDepELSubOrd Om gs).1 := by
        rw [hEnumRes.2.2]
        simp only [ggDepELSubOrd]
        rw [← hT, ← hpar]
      have hdvd := ggDepEL_card_dvd (S := Sm) (S' := {g | ∃ t ∈ T, g = ggTWLMatLin 3 6 t})
        hSm_refl hsubSgs
      rwa [hCardEq] at hdvd
    have hKdvdSm : K ∣ Nat.card ↥(Submonoid.closure Sm) := by
      rw [hK]
      exact l05nPB_foldl_lcm_dvd (one_dvd _) (fun o ho => by
        rcases List.mem_map.mp ho with ⟨gs, hgs, rfl⟩
        exact hSubOrd gs hgs)
    have hKdvdM : K ∣ Nat.card ↥M := dvd_trans hKdvdSm hSmdvdM
    intro r n c ht hlo hhi hbad
    rcases hbad with ⟨hdvdn, hcen⟩
    obtain ⟨hn, hc, _⟩ :=
      ggTWLPZArith_sound harith ht hlo hhi (dvd_trans hKdvdM hdvdn)
    have hMcard : Nat.card ↥M = K := by
      rw [hn] at hdvdn
      exact Nat.dvd_antisymm hdvdn hKdvdM
    have hcentre1 : ggDepELCentreCard M = 1 := by
      have hcc := hcen (hMcard.trans hn.symm)
      rw [hc] at hcc
      exact hcc
    have hwc : ∀ k ∈ w.cen, k < Om.length := by
      intro k hk
      simpa only [hOm, List.length_map] using hcenlt k hk
    have ha_ne' : ggTWLMatEq 3 a (ggTWLMatOne 6) = false := by simpa using ha_ne
    have haWF : ggTWLMatWF 6 a := by
      rw [ha]
      exact (ggTWLWordMat_lin (p := 3) (d := 6) hOm_valid hwc).1
    have honeWF : ggTWLMatWF 6 (ggTWLMatOne 6) := (ggTWLMatOne_lin (p :=
      3) (d := 6)).1
    have hlin_a_ne : ggTWLMatLin 3 6 a ≠ 1 := by
      intro heq
      have htrue : ggTWLMatEq 3 a (ggTWLMatOne 6) = true :=
        (ggTWLMatEq_iff haWF honeWF).mpr (by rw [heq, (ggTWLMatOne_lin (p := 3) (d := 6)).2])
      rw [htrue] at ha_ne'
      exact Bool.false_ne_true ha_ne'.symm
    have hcommT : ∀ t ∈ Om, ggTWLMatLin 3 6 a * ggTWLMatLin 3 6 t =
        ggTWLMatLin 3 6 t * ggTWLMatLin 3 6 a := by
      intro t ht
      have hcomm := ha_comm t ht
      have htWF : ggTWLMatWF 6 t := hOm_valid t ht
      have h1 := (ggTWLMatMul_lin (p := 3) (d := 6) haWF htWF).2
      have h2 := (ggTWLMatMul_lin (p := 3) (d := 6) htWF haWF).2
      rw [← h1, ← h2]
      exact (ggTWLMatEq_iff (ggTWLMatMul_lin haWF htWF).1
        (ggTWLMatMul_lin htWF haWF).1).mp hcomm
    have hlin_a_Sm : ggTWLMatLin 3 6 a ∈ Submonoid.closure Sm := by
      rw [ha, (ggTWLWordMat_lin (p := 3) (d := 6) hOm_valid hwc).2]
      refine Submonoid.list_prod_mem (Submonoid.closure Sm) (fun g hg => ?_)
      rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
      have hklt : k < Om.length := hwc k hk
      rw [List.getD_eq_getElem (l := Om) (d := []) (n := k) hklt]
      exact Submonoid.subset_closure ⟨Om[k], List.getElem_mem hklt, rfl⟩
    have hSm_card : Nat.card ↥(Submonoid.closure Sm) = Nat.card ↥M := by
      refine Nat.dvd_antisymm hSmdvdM ?_
      rw [hMcard]
      exact hKdvdSm
    have hHM : Submonoid.closure Sm ≤ M := Submonoid.closure_le.mpr hSm_sub
    have hHMeq : Submonoid.closure Sm = M := by
      have hset : (↑(Submonoid.closure Sm) : Set (Module.End (ZMod 3) (GGDepAE 3 6))) = ↑M :=
        Set.Finite.eq_of_subset_of_card_le
          (Set.finite_univ.subset (Set.subset_univ (M : Set (Module.End (ZMod 3) (GGDepAE 3 6)))))
          (fun x hx => hHM hx) (le_of_eq hSm_card.symm)
      exact SetLike.ext (Set.ext_iff.mp hset)
    have hlin_a_M : ggTWLMatLin 3 6 a ∈ M := by
      rw [← hHMeq]
      exact hlin_a_Sm
    have hcentH : ∀ y ∈ Submonoid.closure Sm,
        ggTWLMatLin 3 6 a * y = y * ggTWLMatLin 3 6 a := by
      intro y hy
      induction hy using Submonoid.closure_induction with
      | mem t ht =>
          rcases ht with ⟨t', ht', rfl⟩
          exact hcommT t' ht'
      | one => simp
      | mul x y _ _ ihx ihy =>
          calc ggTWLMatLin 3 6 a * (x * y)
              = (ggTWLMatLin 3 6 a * x) * y := by rw [mul_assoc]
            _ = (x * ggTWLMatLin 3 6 a) * y := by rw [ihx]
            _ = x * (ggTWLMatLin 3 6 a * y) := by rw [mul_assoc]
            _ = x * (y * ggTWLMatLin 3 6 a) := by rw [ihy]
            _ = (x * y) * ggTWLMatLin 3 6 a := by rw [mul_assoc]
    have hcentM : ∀ y ∈ M, ggTWLMatLin 3 6 a * y = y * ggTWLMatLin 3 6 a := by
      intro y hy
      exact hcentH y (by rw [hHMeq]; exact hy)
    let z0 : {g : ↥M // ∀ h : ↥M, g * h = h * g} :=
      ⟨⟨ggTWLMatLin 3 6 a, hlin_a_M⟩, fun h => Subtype.ext (hcentM h.1 h.2)⟩
    let z1 : {g : ↥M // ∀ h : ↥M, g * h = h * g} := ⟨1, fun h => by simp⟩
    have hz01 : z0 ≠ z1 := by
      intro heq
      have hval : (z0 : ↥M) = (z1 : ↥M) := congrArg Subtype.val heq
      have hcoe : (z0 : Module.End (ZMod 3) (GGDepAE 3 6)) =
          (z1 : Module.End (ZMod 3) (GGDepAE 3 6)) := congrArg Subtype.val hval
      apply hlin_a_ne
      simpa [z0, z1] using hcoe
    haveI : Nontrivial {g : ↥M // ∀ h : ↥M, g * h = h * g} := ⟨z0, z1, hz01⟩
    have h2 : 1 < ggDepELCentreCard M := by
      rw [ggDepELCentreCard]
      exact Finite.one_lt_card
    omega

end CFSG.StandardType

end
