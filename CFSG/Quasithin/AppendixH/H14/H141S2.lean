module

public import CFSG.Quasithin.AppendixH.H14.H141SInst
public import CFSG.Quasithin.AppendixH.H14.H141F4Hyp
public import CFSG.Quasithin.AppendixH.H14.H141Perf

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin

theorem sigC_sigC {s t c : ℕ} (hs : s < 2) (ht : t < 2) (hc : c < 4) :
    sigC t (sigC s c) = sigC ((s + t) % 2) c := by
  interval_cases s <;> interval_cases t <;> interval_cases c <;> decide +kernel

theorem hypCodes_mem_codes18 : hypCodes.all (fun p => codes18.contains p) = true := by
  decide +kernel

@[expose] noncomputable def actS :
    ↥(MY M24g stdS) →* MulAut (Multiplicative (Fin 3 → GF4)) :=
  actHom engine_S.normal (tab64Equiv tabS_ok coordF4)

@[expose] def semiOK (st : ℕ) : Bool :=
  (List.range 2).any fun s => (List.range 4).all fun c => (List.range 64).all fun n =>
    linAct st (smulCode3 c n) == smulCode3 (sigC s c) (linAct st n)

@[expose] def codes18OK (st : ℕ) : Bool :=
  codes18.all fun v => codes18.contains (linAct st v)

theorem semiOK_gens : gmS.all semiOK = true := by
  decide +kernel

theorem codes18OK_gens : gmS.all codes18OK = true := by
  decide +kernel

theorem semilinear_of_reach {st : ℕ} (h : StReach gmS st) :
    ∃ s < 2, ∀ c < 4, ∀ n < 64, linAct st (smulCode3 c n) = smulCode3 (sigC s c) (linAct st n) := by
  refine StReach.rec (motive := fun st _ => ∃ s < 2, ∀ c < 4, ∀ n < 64,
      linAct st (smulCode3 c n) = smulCode3 (sigC s c) (linAct st n)) ?_ ?_ h
  · refine ⟨0, by norm_num, fun c hc n hn => ?_⟩
    rw [linAct_idSt (smulCode3_lt c n hc hn), linAct_idSt hn]
    rfl
  · intro j st' hj hst' ih
    obtain ⟨s, hs2, hsem⟩ := ih
    have hmem : gmS.getD j 0 ∈ gmS := by
      rw [List.getD_eq_getElem (l := gmS) (d := 0) hj]
      exact List.getElem_mem hj
    obtain ⟨t, ht_range, htall⟩ :=
      List.any_eq_true.mp (List.all_eq_true.mp semiOK_gens _ hmem)
    have ht2 : t < 2 := List.mem_range.mp ht_range
    refine ⟨(s + t) % 2, Nat.mod_lt _ (by norm_num), fun c hc n hn => ?_⟩
    have hgen_at : linAct (gmS.getD j 0) (smulCode3 (sigC s c) (linAct st' n)) =
        smulCode3 (sigC t (sigC s c)) (linAct (gmS.getD j 0) (linAct st' n)) := by
      have h1 := List.all_eq_true.mp htall (sigC s c) (List.mem_range.mpr (sigC_lt hc))
      exact beq_iff_eq.mp
        (List.all_eq_true.mp h1 (linAct st' n) (List.mem_range.mpr (linAct_lt st' n)))
    calc linAct (compSt (gmS.getD j 0) st') (smulCode3 c n)
        = linAct (gmS.getD j 0) (linAct st' (smulCode3 c n)) :=
          linAct_compSt (gmS.getD j 0) st' (smulCode3 c n)
      _ = linAct (gmS.getD j 0) (smulCode3 (sigC s c) (linAct st' n)) := by
          rw [hsem c hc n hn]
      _ = smulCode3 (sigC t (sigC s c)) (linAct (gmS.getD j 0) (linAct st' n)) := hgen_at
      _ = smulCode3 (sigC ((s + t) % 2) c)
            (linAct (gmS.getD j 0) (linAct st' n)) := by rw [sigC_sigC hs2 ht2 hc]
      _ = smulCode3 (sigC ((s + t) % 2) c)
            (linAct (compSt (gmS.getD j 0) st') n) := by rw [linAct_compSt]

theorem codes18_of_reach {st : ℕ} (h : StReach gmS st) :
    ∀ v ∈ codes18, codes18.contains (linAct st v) = true := by
  refine StReach.rec (motive := fun st _ => ∀ v ∈ codes18,
      codes18.contains (linAct st v) = true) ?_ ?_ h
  · intro v hv
    rw [linAct_idSt (codes18_lt v hv)]
    exact List.contains_iff_mem.mpr hv
  · intro j st' hj hst' ih v hv
    have hmem : gmS.getD j 0 ∈ gmS := by
      rw [List.getD_eq_getElem (l := gmS) (d := 0) hj]
      exact List.getElem_mem hj
    have hcheck := List.all_eq_true.mp (List.all_eq_true.mp codes18OK_gens _ hmem)
      (linAct st' v) (List.contains_iff_mem.mp (ih v hv))
    rw [linAct_compSt]
    exact hcheck

theorem exists_state_S (g : ↥(MY M24g stdS)) :
    ∃ st, StReach gmS st ∧ ∀ n < 64,
      (g : S24) * tab64Perm tabS n * (g : S24)⁻¹ = tab64Perm tabS (linAct st n) := by
  obtain ⟨st, hst, hact⟩ := engine_S.action g g.2
  obtain ⟨e, he, he1⟩ := List.mem_map.mp hst
  refine ⟨st, ?_, hact⟩
  rw [← he1]
  exact (sbfsOK_sound bfsS_ok).2.2 e he

theorem actS_apply_state (g : ↥(MY M24g stdS)) {st : ℕ}
    (hst : ∀ n < 64,
      (g : S24) * tab64Perm tabS n * (g : S24)⁻¹ = tab64Perm tabS (linAct st n)) {n : ℕ}
    (hn : n < 64) :
    actS g (Multiplicative.ofAdd (wOfCode3 n)) = Multiplicative.ofAdd (wOfCode3 (linAct st n)) := by
  exact actHom_tab64Equiv_state tabS_ok coordF4 engine_S.normal g hst hn

theorem actS_mem (g : ↥(MY M24g stdS)) :
    actS g ∈ hatS6set GF4 OmegaH := by
  obtain ⟨st, hreach, hst⟩ := exists_state_S g
  obtain ⟨s, hs, hsem⟩ := semilinear_of_reach hreach
  have hsem3 : SemilinearOf3 (sigE s) (actS g) := by
    intro c w
    have hcode : codeOf3 w < 64 := codeOf3_lt w
    have hcodec : codeOf3 (c • w) < 64 := codeOf3_lt (c • w)
    have h1 : actS g (Multiplicative.ofAdd (c • w)) =
        Multiplicative.ofAdd (wOfCode3 (linAct st (codeOf3 (c • w)))) := by
      have hcw : Multiplicative.ofAdd (c • w) =
          Multiplicative.ofAdd (wOfCode3 (codeOf3 (c • w))) := by
        rw [wOfCode3_codeOf3]
      rw [hcw]
      exact actS_apply_state g hst hcodec
    have h2 : Multiplicative.toAdd (actS g (Multiplicative.ofAdd w)) =
        wOfCode3 (linAct st (codeOf3 w)) := by
      have hw : Multiplicative.ofAdd w = Multiplicative.ofAdd (wOfCode3 (codeOf3 w)) := by
        rw [wOfCode3_codeOf3]
      rw [hw]
      exact congrArg Multiplicative.toAdd (actS_apply_state g hst hcode)
    rw [h1, h2]
    have hkey := semilinear3_of_code (M := linAct st) s hs (fun n _ => linAct_lt st n) hsem c w
    rw [hkey, sigE_apply]
  have hp : ∀ p ∈ hypCodes, codes18.contains
      (codeOf3 (Multiplicative.toAdd (actS g (Multiplicative.ofAdd (wOfCode3 p))))) = true := by
    intro p hp_mem
    have hp18 : p ∈ codes18 := List.contains_iff_mem.mp
      (List.all_eq_true.mp hypCodes_mem_codes18 p hp_mem)
    have hp_lt : p < 64 := codes18_lt p hp18
    rw [actS_apply_state g hst hp_lt, toAdd_ofAdd,
      codeOf3_wOfCode3 (linAct_lt st p)]
    exact codes18_of_reach hreach p hp18
  change actS g ∈ gammaLset 3 GF4 ∧ PermutesPoints (actS g) OmegaH
  refine ⟨?_, ?_⟩
  · rw [mem_gammaLset3_iff]
    exact ⟨sigE s, hsem3⟩
  · exact permutesPoints_of_codes hsem3 hp

@[expose] def keyCoverCheck : Bool :=
  (List.range 2).all fun s => codes18.all fun v0 => codes18.all fun v1 => codes18.all fun v2 =>
    !keyGood s v0 v1 v2 || bfsS.any fun e =>
      (col e.1 0 == v0) && (col e.1 2 == v1) && (col e.1 4 == v2) &&
        (List.range 64).all fun n => linAct e.1 n == mKey s v0 v1 v2 n

private def keyCoverCheckV (s v0 : ℕ) : Bool :=
  codes18.all fun v1 => codes18.all fun v2 =>
    !keyGood s v0 v1 v2 || bfsS.any fun e =>
      (col e.1 0 == v0) && (col e.1 2 == v1) && (col e.1 4 == v2) &&
        (List.range 64).all fun n => linAct e.1 n == mKey s v0 v1 v2 n

private def keyCoverCheckSlice (l : List ℕ) (s : ℕ) : Bool :=
  l.all fun v0 => keyCoverCheckV s v0

private theorem codes18_split :
    codes18 = codes18.take 6 ++ ((codes18.drop 6).take 6 ++ codes18.drop 12) := by
  decide

private theorem keyCoverCheckSlice_take_zero :
    keyCoverCheckSlice (codes18.take 6) 0 = true := by decide +kernel

private theorem keyCoverCheckSlice_take_one :
    keyCoverCheckSlice (codes18.take 6) 1 = true := by decide +kernel

private theorem keyCoverCheckSlice_mid_zero :
    keyCoverCheckSlice ((codes18.drop 6).take 6) 0 = true := by decide +kernel

private theorem keyCoverCheckSlice_mid_one :
    keyCoverCheckSlice ((codes18.drop 6).take 6) 1 = true := by decide +kernel

private theorem keyCoverCheckSlice_drop_zero :
    keyCoverCheckSlice (codes18.drop 12) 0 = true := by decide +kernel

private theorem keyCoverCheckSlice_drop_one :
    keyCoverCheckSlice (codes18.drop 12) 1 = true := by decide +kernel

private theorem keyCoverCheckSlice_append {l₁ l₂ : List ℕ} {s : ℕ}
    (h₁ : keyCoverCheckSlice l₁ s = true) (h₂ : keyCoverCheckSlice l₂ s = true) :
    keyCoverCheckSlice (l₁ ++ l₂) s = true := by
  simp only [keyCoverCheckSlice] at h₁ h₂ ⊢
  rw [List.all_append, h₁, h₂]
  rfl

private theorem keyCoverCheckSlice_codes18 {s : ℕ} (hs : s < 2) :
    keyCoverCheckSlice codes18 s = true := by
  have hs' : s = 0 ∨ s = 1 := by omega
  rcases hs' with rfl | rfl
  · rw [codes18_split]
    exact keyCoverCheckSlice_append keyCoverCheckSlice_take_zero
      (keyCoverCheckSlice_append keyCoverCheckSlice_mid_zero keyCoverCheckSlice_drop_zero)
  · rw [codes18_split]
    exact keyCoverCheckSlice_append keyCoverCheckSlice_take_one
      (keyCoverCheckSlice_append keyCoverCheckSlice_mid_one keyCoverCheckSlice_drop_one)

theorem keyCoverCheck_eq : keyCoverCheck = true := by
  have h : (List.range 2).all (fun s => codes18.all fun v0 => keyCoverCheckV s v0) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    have hslice := keyCoverCheckSlice_codes18 (List.mem_range.mp hs)
    simpa only [keyCoverCheckSlice] using hslice
  simpa only [keyCoverCheck, keyCoverCheckV] using h

theorem actS_surj :
    ∀ γ ∈ hatS6set GF4 OmegaH, ∃ g : ↥(MY M24g stdS), actS g = γ := by
  intro γ hγ
  obtain ⟨s, hs, v0, hv0, v1, hv1, v2, hv2, hgood, hsem, hform⟩ :=
    exists_key3_of_mem_hatS6set hγ
  have hcheck0 : (List.range 2).all (fun s => codes18.all fun v0 => codes18.all fun v1 =>
      codes18.all fun v2 => !keyGood s v0 v1 v2 || bfsS.any fun e =>
        (col e.1 0 == v0) && (col e.1 2 == v1) && (col e.1 4 == v2) &&
          (List.range 64).all fun n => linAct e.1 n == mKey s v0 v1 v2 n) = true := by
    simpa only [keyCoverCheck] using keyCoverCheck_eq
  have hcheck := List.all_eq_true.mp hcheck0 s (List.mem_range.mpr hs)
  have hcheck := List.all_eq_true.mp hcheck v0 hv0
  have hcheck := List.all_eq_true.mp hcheck v1 hv1
  have hcheck := List.all_eq_true.mp hcheck v2 hv2
  rw [Bool.or_eq_true] at hcheck
  rcases hcheck with hbad | hany
  · simp [hgood] at hbad
  · obtain ⟨e, he, hall⟩ := List.any_eq_true.mp hany
    have hall64 : ((List.range 64).all fun n => linAct e.1 n == mKey s v0 v1 v2 n) = true := by
      rw [Bool.and_eq_true] at hall
      exact hall.2
    have halln : ∀ n < 64, linAct e.1 n = mKey s v0 v1 v2 n := by
      intro n hn
      exact beq_iff_eq.mp (List.all_eq_true.mp hall64 n (List.mem_range.mpr hn))
    obtain ⟨x, hx, hxact⟩ := engine_S.realize e.1 (List.mem_map.mpr ⟨e, he, rfl⟩)
    refine ⟨⟨x, hx⟩, ?_⟩
    refine MulEquiv.ext fun v => ?_
    have hv : v = Multiplicative.ofAdd (wOfCode3 (codeOf3 (Multiplicative.toAdd v))) := by
      rw [wOfCode3_codeOf3, ofAdd_toAdd]
    have hcodev : codeOf3 (Multiplicative.toAdd v) < 64 := codeOf3_lt _
    have hγeq : γ (Multiplicative.ofAdd (wOfCode3 (codeOf3 (Multiplicative.toAdd v)))) =
        Multiplicative.ofAdd (wOfCode3 (mKey s v0 v1 v2 (codeOf3 (Multiplicative.toAdd v)))) := by
      have := congrArg (fun m => Multiplicative.ofAdd (wOfCode3 m)) (hform _ hcodev)
      simpa only [ofAdd_toAdd, wOfCode3_codeOf3] using this
    calc actS ⟨x, hx⟩ v
        = actS ⟨x, hx⟩ (Multiplicative.ofAdd
            (wOfCode3 (codeOf3 (Multiplicative.toAdd v)))) := congrArg (actS ⟨x, hx⟩) hv
      _ = Multiplicative.ofAdd
            (wOfCode3 (linAct e.1 (codeOf3 (Multiplicative.toAdd v)))) :=
          actS_apply_state ⟨x, hx⟩ hxact hcodev
      _ = Multiplicative.ofAdd
            (wOfCode3 (mKey s v0 v1 v2 (codeOf3 (Multiplicative.toAdd v)))) := by
          rw [halln _ hcodev]
      _ = γ (Multiplicative.ofAdd (wOfCode3 (codeOf3 (Multiplicative.toAdd v)))) := hγeq.symm
      _ = γ v := (congrArg γ hv).symm

theorem stdMS_conjIso :
    ConjIso (MY M24g stdS) (tab64Sub tabS tabS_ok) (Multiplicative (Fin 3 → GF4))
      (hatS6set GF4 OmegaH) (tab64Equiv tabS_ok coordF4) actS := by
  exact conjIso_of_actHom engine_S.le engine_S.normal (tab64Equiv tabS_ok coordF4)
    (hatS6set GF4 OmegaH) actS_mem actS_surj engine_S.selfCentralizing

theorem actS_perfectCore_linear :
    ∀ g : ↥(MY M24g stdS), (g : S24) ∈ perfectCore (MY M24g stdS) → IsKLinearAut (actS g) := by
  exact perfectCore_isKLinear actS (fun g => (actS_mem g).1)

end CFSG.Quasithin.AppendixH.H14
