module

public import CFSG.LocalAnalysis.StandardType.GGTWLowMatMul

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLE_replay_snoc (p d : ℕ) (T : List (List (List ℕ))) (l : List (Nat × Nat))
    (e : Nat × Nat) :
    ggTWLReplay p d T (l ++ [e]) =
      ggTWLReplay p d T l ++
        [ggTWLMatMul p d ((ggTWLReplay p d T l).getD e.1 []) (T.getD e.2 [])] := by
  simp only [ggTWLReplay, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma l05nLE_replay_length (p d : ℕ) (T : List (List (List ℕ)))
    (par : List (Nat × Nat)) : (ggTWLReplay p d T par).length = par.length + 1 := by
  induction par using List.reverseRecOn with
  | nil => simp [ggTWLReplay]
  | append_singleton l e ih =>
      rw [l05nLE_replay_snoc, List.length_append, ih]
      simp

private lemma l05nLE_one_mem_replay (p d : ℕ) (T : List (List (List ℕ)))
    (par : List (Nat × Nat)) : ggTWLMatOne d ∈ ggTWLReplay p d T par := by
  induction par using List.reverseRecOn with
  | nil => simp [ggTWLReplay]
  | append_singleton l e ih =>
      rw [l05nLE_replay_snoc]
      exact List.mem_append_left _ ih

private lemma l05nLE_nodup_pairwise {p : ℕ} {L : List (List (List ℕ))}
    (h : ggTWLNodup p L = true) :
    L.Pairwise (fun a b => ggTWLMatEq p a b = false) := by
  induction L with
  | nil => simp
  | cons a l ih =>
      rw [ggTWLNodup, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rw [List.pairwise_cons]
      refine ⟨?_, ih h2⟩
      intro b hb
      have := (List.all_eq_true.mp h1) b hb
      simpa using this

private lemma l05nLE_nodup_getElem_lt {p : ℕ} {L : List (List (List ℕ))}
    (h : ggTWLNodup p L = true) {i j : ℕ} (hi : i < L.length) (hj : j < L.length)
    (hij : i < j) : ggTWLMatEq p (L[i]) (L[j]) = false :=
  (List.pairwise_iff_getElem.mp (l05nLE_nodup_pairwise h)) i j hi hj hij

private lemma l05nLE_replay_wf_mem {p d : ℕ} [Fact p.Prime] {T : List (List (List ℕ))}
    (hT : ∀ t ∈ T, ggTWLMatWF d t) (par : List (Nat × Nat))
    (hix : (List.range par.length).all (fun i =>
      decide ((par.getD i (0, 0)).1 < i + 1) &&
      decide ((par.getD i (0, 0)).2 < T.length)) = true) :
    (∀ M ∈ ggTWLReplay p d T par, ggTWLMatWF d M) ∧
      (∀ M ∈ ggTWLReplay p d T par,
        ggTWLMatLin p d M ∈
          Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t}) := by
  have key : ∀ i, i ≤ par.length →
      (∀ M ∈ ggTWLReplay p d T (par.take i), ggTWLMatWF d M) ∧
        (∀ M ∈ ggTWLReplay p d T (par.take i),
          ggTWLMatLin p d M ∈
            Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t}) := by
    intro i
    induction i with
    | zero =>
        intro _
        constructor
        · intro M hM
          simp only [List.take_zero, ggTWLReplay, List.foldl_nil, List.mem_singleton] at hM
          rw [hM]
          exact (ggTWLMatOne_lin (p := p) (d := d)).1
        · intro M hM
          simp only [List.take_zero, ggTWLReplay, List.foldl_nil, List.mem_singleton] at hM
          rw [hM, (ggTWLMatOne_lin (p := p) (d := d)).2]
          exact Submonoid.one_mem _
    | succ i ih =>
        intro hi
        have hi' : i < par.length := by omega
        obtain ⟨ihWF, ihIN⟩ := ih (by omega)
        have htake : par.take (i + 1) = par.take i ++ [par[i]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi']
          simp
        rw [htake, l05nLE_replay_snoc]
        have hcheck := (List.all_eq_true.mp hix) i (List.mem_range.mpr hi')
        rw [List.getD_eq_getElem par (0, 0) hi'] at hcheck
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
        obtain ⟨hple, hglt⟩ := hcheck
        have hlen_take : (ggTWLReplay p d T (par.take i)).length = i + 1 := by
          rw [l05nLE_replay_length]
          rw [List.length_take, Nat.min_eq_left (by omega)]
        have hparent_mem : (ggTWLReplay p d T (par.take i)).getD (par[i]).1 [] ∈
            ggTWLReplay p d T (par.take i) := by
          rw [List.getD_eq_getElem _ [] (by rw [hlen_take]; exact hple)]
          exact List.getElem_mem _
        have hgen_mem : T.getD (par[i]).2 [] ∈ T := by
          rw [List.getD_eq_getElem T [] hglt]
          exact List.getElem_mem hglt
        have hmul := ggTWLMatMul_lin (p := p) (d := d)
          (ihWF _ hparent_mem) (hT _ hgen_mem)
        constructor
        · intro M hM
          rw [List.mem_append, List.mem_singleton] at hM
          rcases hM with hM | rfl
          · exact ihWF M hM
          · exact hmul.1
        · intro M hM
          rw [List.mem_append, List.mem_singleton] at hM
          rcases hM with hM | rfl
          · exact ihIN M hM
          · rw [hmul.2]
            exact Submonoid.mul_mem _ (ihIN _ hparent_mem)
              (Submonoid.subset_closure ⟨T.getD (par[i]).2 [], hgen_mem, rfl⟩)
  have hfin := key par.length le_rfl
  rwa [List.take_length] at hfin

theorem ggTWLEnum_sound {p d : ℕ} [Fact p.Prime] {T : List (List (List ℕ))}
    (hT : ∀ t ∈ T, ggTWLMatWF d t) (par : List (Nat × Nat))
    (h : ggTWLEnumOK p d T par = true) :
    (∀ M ∈ ggTWLReplay p d T par, ggTWLMatWF d M) ∧
      ((Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
          Submonoid (Module.End (ZMod p) (GGDepAE p d))) :
            Set (Module.End (ZMod p) (GGDepAE p d))) =
        {g | ∃ M ∈ ggTWLReplay p d T par, g = ggTWLMatLin p d M} ∧
      Nat.card ↥(Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t}) =
        (ggTWLReplay p d T par).length := by
  have h' := h
  simp only [ggTWLEnumOK, Bool.and_eq_true] at h'
  obtain ⟨⟨hix, hclraw⟩, hnd⟩ := h'
  have hkey := l05nLE_replay_wf_mem (p := p) (d := d) (T := T) hT par hix
  have hWF : ∀ M ∈ ggTWLReplay p d T par, ggTWLMatWF d M := hkey.1
  have hIN := hkey.2
  have hcl : ∀ a ∈ ggTWLReplay p d T par, ∀ t ∈ T,
      ∃ b ∈ ggTWLReplay p d T par, ggTWLMatEq p b (ggTWLMatMul p d a t) = true := by
    intro a ha t ht
    exact List.any_eq_true.mp ((List.all_eq_true.mp ((List.all_eq_true.mp hclraw) a ha)) t ht)
  have hgen : ∀ t ∈ T, ggTWLMatLin p d t ∈
      {g : Module.End (ZMod p) (GGDepAE p d) |
        ∃ M ∈ ggTWLReplay p d T par, g = ggTWLMatLin p d M} := by
    intro t ht
    obtain ⟨b, hb, hbeq⟩ := hcl (ggTWLMatOne d) (l05nLE_one_mem_replay p d T par) t ht
    have hbWF := hWF b hb
    have hmul := ggTWLMatMul_lin (p := p) (d := d)
      (ggTWLMatOne_lin (p := p) (d := d)).1 (hT t ht)
    have hlin := (ggTWLMatEq_iff (p := p) (d := d) hbWF hmul.1).mp hbeq
    rw [hmul.2, (ggTWLMatOne_lin (p := p) (d := d)).2, one_mul] at hlin
    exact ⟨b, hb, hlin.symm⟩
  have hle : (Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
      Set (Module.End (ZMod p) (GGDepAE p d))) ⊆
      {g | ∃ M ∈ ggTWLReplay p d T par, g = ggTWLMatLin p d M} := by
    intro g hg
    refine Submonoid.closure_induction_right
      (motive := fun x _ => x ∈ {g : Module.End (ZMod p) (GGDepAE p d) |
        ∃ M ∈ ggTWLReplay p d T par, g = ggTWLMatLin p d M}) ?_ ?_ hg
    · exact ⟨ggTWLMatOne d, l05nLE_one_mem_replay p d T par,
        ((ggTWLMatOne_lin (p := p) (d := d)).2).symm⟩
    · intro x hx y hy hxim
      obtain ⟨M, hM, rfl⟩ := hxim
      obtain ⟨t, ht, rfl⟩ := hy
      obtain ⟨b, hb, hbeq⟩ := hcl M hM t ht
      have hmul := ggTWLMatMul_lin (p := p) (d := d) (hWF M hM) (hT t ht)
      have hlin := (ggTWLMatEq_iff (p := p) (d := d) (hWF b hb) hmul.1).mp hbeq
      rw [hmul.2] at hlin
      exact ⟨b, hb, hlin.symm⟩
  have hge : {g | ∃ M ∈ ggTWLReplay p d T par, g = ggTWLMatLin p d M} ⊆
      (Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
        Set (Module.End (ZMod p) (GGDepAE p d))) := by
    rintro g ⟨M, hM, rfl⟩
    exact hIN M hM
  refine ⟨hWF, Set.Subset.antisymm hle hge, ?_⟩
  let L := ggTWLReplay p d T par
  let f : Fin L.length → Module.End (ZMod p) (GGDepAE p d) := fun i => ggTWLMatLin p d (L[i])
  have hf_inj : Function.Injective f := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    change ggTWLMatLin p d (L[i]) = ggTWLMatLin p d (L[j]) at hij
    by_contra hne
    have hneval : i ≠ j := fun hh => hne (Fin.ext hh)
    rcases Nat.lt_or_gt_of_ne hneval with hlt | hgt
    · have hfalse := l05nLE_nodup_getElem_lt (p := p) hnd hi hj hlt
      have htrue : ggTWLMatEq p (L[i]) (L[j]) = true :=
        (ggTWLMatEq_iff (p := p) (d := d) (hWF _ (List.getElem_mem hi))
          (hWF _ (List.getElem_mem hj))).mpr hij
      rw [htrue] at hfalse
      exact Bool.noConfusion hfalse
    · have hfalse := l05nLE_nodup_getElem_lt (p := p) hnd hj hi hgt
      have htrue : ggTWLMatEq p (L[j]) (L[i]) = true :=
        (ggTWLMatEq_iff (p := p) (d := d) (hWF _ (List.getElem_mem hj))
          (hWF _ (List.getElem_mem hi))).mpr hij.symm
      rw [htrue] at hfalse
      exact Bool.noConfusion hfalse
  have hrange : {g | ∃ M ∈ L, g = ggTWLMatLin p d M} = Set.range f := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
      exact Set.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨L[i], List.getElem_mem i.isLt, rfl⟩
  have hle' : (Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
      Set (Module.End (ZMod p) (GGDepAE p d))) ⊆ Set.range f := by
    rw [hrange] at hle
    exact hle
  have hge' : Set.range f ⊆ (Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
      Set (Module.End (ZMod p) (GGDepAE p d))) := by
    rw [hrange] at hge
    exact hge
  have hEq : (Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
      Set (Module.End (ZMod p) (GGDepAE p d))) = Set.range f :=
    Set.Subset.antisymm hle' hge'
  calc Nat.card ↥(Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t}) =
        Nat.card ↥((Submonoid.closure {g | ∃ t ∈ T, g = ggTWLMatLin p d t} :
          Submonoid (Module.End (ZMod p) (GGDepAE p d))) :
            Set (Module.End (ZMod p) (GGDepAE p d))) := rfl
    _ = Nat.card ↥(Set.range f) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hEq]))
    _ = Nat.card (Fin L.length) :=
        Nat.card_congr (Equiv.ofInjective f hf_inj).symm
    _ = L.length := Nat.card_fin L.length
    _ = (ggTWLReplay p d T par).length := rfl

private lemma l05nLE_frameMats_wf {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) :
    ∀ t ∈ ggTWLFrameMats p N, ggTWLMatWF (N - 1) t := by
  intro t ht
  rw [ggTWLFrameMats] at ht
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
  have hg' : g < N - 1 := List.mem_range.mp hg
  have hgN : g + 1 < N := by omega
  have hval : GGTWNValid p N (ggTWNGen p N [] g) :=
    ggTWNGen_valid hp hN (by simp) (by simpa using hg')
  have hgen : ggTWNGen p N [] g = (ggTWNH p N g, ggTWNA p N g) := by
    simp [ggTWNGen, hgN]
  rw [← hgen]
  exact (ggTWLMatOfPair_lin (p := p) (N := N) (q := ggTWNGen p N [] g) hval).1

private lemma l05nLE_frameMats_lin {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) :
    {g : Module.End (ZMod p) (GGDepAE p (N - 1)) |
        ∃ t ∈ ggTWLFrameMats p N, g = ggTWLMatLin p (N - 1) t} = ggTWFrameGens p N := by
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [ggTWLFrameMats] at ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    have ha' : a < N - 1 := List.mem_range.mp ha
    have haN : a + 1 < N := by omega
    have hval : GGTWNValid p N (ggTWNGen p N [] a) :=
      ggTWNGen_valid hp hN (by simp) (by simpa using ha')
    have hgen : ggTWNGen p N [] a = (ggTWNH p N a, ggTWNA p N a) := by
      simp [ggTWNGen, haN]
    have hlin := (ggTWLMatOfPair_lin (p := p) (N := N) (q := ggTWNGen p N [] a) hval).2
    rw [hgen] at hlin
    rw [hlin]
    refine Set.mem_range.mpr ⟨⟨a, ha'⟩, ?_⟩
    simp only [ggTWNRflOf]
    rw [ggTWNH_toZ (p := p) (N := N) ⟨a, ha'⟩, ggTWNA_toZ (p := p) (N := N) ⟨a, ha'⟩]
  · rintro ⟨i, rfl⟩
    refine ⟨ggTWLMatOfPair p (N - 1) (ggTWNH p N i.val, ggTWNA p N i.val), ?_, ?_⟩
    · rw [ggTWLFrameMats]
      exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    · have hiN : i.val + 1 < N := by omega
      have hval : GGTWNValid p N (ggTWNGen p N [] i.val) :=
        ggTWNGen_valid hp hN (by simp) (by simpa using i.isLt)
      have hgen : ggTWNGen p N [] i.val = (ggTWNH p N i.val, ggTWNA p N i.val) := by
        simp [ggTWNGen, hiN]
      have hlin := (ggTWLMatOfPair_lin (p := p) (N := N) (q := ggTWNGen p N [] i.val) hval).2
      rw [hgen] at hlin
      rw [hlin]
      simp only [ggTWNRflOf]
      rw [ggTWNH_toZ (i := i), ggTWNA_toZ (i := i)]

theorem ggTWLFrameOK_sound {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    (h : ggTWLFrameOK p N = true) :
    720 ≤ Nat.card ↥(Submonoid.closure (ggTWFrameGens p N)) := by
  have h' := h
  simp only [ggTWLFrameOK, Bool.and_eq_true] at h'
  obtain ⟨hlen, hOK⟩ := h'
  have hlen' : 720 ≤ (ggTWLReplay p (N - 1) (ggTWLFrameMats p N)
      (ggTWLBfsTree p (N - 1) (ggTWLFrameMats p N) 1000)).length := of_decide_eq_true hlen
  have hT := l05nLE_frameMats_wf (p := p) (N := N) hp hN
  have hcard := (ggTWLEnum_sound (p := p) (d := N - 1) (T := ggTWLFrameMats p N) hT
    (ggTWLBfsTree p (N - 1) (ggTWLFrameMats p N) 1000) hOK).2.2
  rw [← l05nLE_frameMats_lin (p := p) (N := N) hp hN]
  exact hcard ▸ hlen'

end CFSG.StandardType

end
