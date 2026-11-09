module

public import CFSG.Quasithin.Background.HFCodeInputs
public import CFSG.Quasithin.Background.HMathieuEnumOrb
public import CFSG.Quasithin.Background.HMathieuFacts24Base
public import CFSG.Quasithin.Background.HMathieuCodeInvBase

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

section Fix

variable {P : Type*} [Group P] {n : ℕ} {act : P → ℕ → ℕ}

theorem all_fix_iff_subprods (hmul : ∀ s t, ∀ m < 2 ^ n, act (s * t) m = act s (act t m))
    (hone : ∀ m < 2 ^ n, act 1 m = m) {m : ℕ} (hm : m < 2 ^ n) :
    ∀ l : List P, (∀ s ∈ l, act s m = m) ↔ ∀ s ∈ subprods l, act s m = m
  | [] => by
    simp only [List.not_mem_nil, false_imp_iff, forall_const, true_iff, subprods,
      List.mem_singleton, forall_eq]
    exact hone m hm
  | y :: l => by
    refine ⟨fun h s hs => ?_, fun h s hs => h s (mem_subprods_of_mem hs)⟩
    have hl := (all_fix_iff_subprods hmul hone hm l).1 fun s hs => h s (List.mem_cons_of_mem y hs)
    rcases mem_subprods_cons.1 hs with hs | ⟨w, hw, rfl⟩
    · exact hl s hs
    · rw [hmul y w m hm, hl w hw, h y List.mem_cons_self]

theorem fixMasks_span (hmul : ∀ s t, ∀ m < 2 ^ n, act (s * t) m = act s (act t m))
    (hone : ∀ m < 2 ^ n, act 1 m = m) {l r : List P}
    (h : ∀ x, x ∈ subprods l ↔ x ∈ subprods r) : fixMasks n act l = fixMasks n act r := by
  unfold fixMasks
  refine List.filter_congr fun m hm => ?_
  have hm' : m < 2 ^ n := List.mem_range.1 hm
  have e1 := all_fix_iff_subprods hmul hone hm' l
  have e2 := all_fix_iff_subprods hmul hone hm' r
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, beq_iff_eq]
  rw [e1, e2]
  exact forall_congr' fun s => imp_congr (h s) Iff.rfl

theorem length_filter_range_perm (N : ℕ) (σ τ : ℕ → ℕ) (hσ : ∀ m < N, σ m < N)
    (hτ : ∀ m < N, τ m < N) (hστ : ∀ m < N, σ (τ m) = m) (hτσ : ∀ m < N, τ (σ m) = m)
    (p : ℕ → Bool) :
    ((List.range N).filter fun m => p (σ m)).length = ((List.range N).filter p).length := by
  have hperm : ((List.range N).map σ).Perm (List.range N) := by
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun x => ?_
    · refine (List.nodup_range).map_on fun a ha b hb e => ?_
      rw [← hτσ a (List.mem_range.1 ha), e, hτσ b (List.mem_range.1 hb)]
    · simp only [List.mem_map, List.mem_range]
      exact ⟨fun ⟨a, ha, e⟩ => e ▸ hσ a ha, fun hx => ⟨τ x, hτ x hx, hστ x hx⟩⟩
  rw [← (hperm.filter p).length_eq, List.filter_map, List.length_map]
  rfl

theorem length_fixMasks_conj (hmul : ∀ s t, ∀ m < 2 ^ n, act (s * t) m = act s (act t m))
    (hone : ∀ m < 2 ^ n, act 1 m = m) (hlt : ∀ s, ∀ m < 2 ^ n, act s m < 2 ^ n) (g : P)
    (l : List P) :
    (fixMasks n act (l.map (MulAut.conj g))).length = (fixMasks n act l).length := by
  have hinv : ∀ x, ∀ m < 2 ^ n, act x⁻¹ (act x m) = m := fun x m hm => by
    rw [← hmul _ _ m hm, inv_mul_cancel, hone m hm]
  have hinv' : ∀ x, ∀ m < 2 ^ n, act x (act x⁻¹ m) = m := fun x m hm => by
    rw [← hmul _ _ m hm, mul_inv_cancel, hone m hm]
  unfold fixMasks
  rw [← length_filter_range_perm (2 ^ n) (act g⁻¹) (act g) (hlt _) (hlt _) (hinv g) (hinv' g)
    (fun m => l.all fun s => act s m == m)]
  congr 1
  refine List.filter_congr fun m hm => ?_
  have hm' : m < 2 ^ n := List.mem_range.1 hm
  have hg := hlt g⁻¹ m hm'
  rw [Bool.eq_iff_iff]
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq,
    MulAut.conj_apply]
  refine forall₂_congr fun s _ => ?_
  rw [hmul _ _ m hm', hmul _ _ _ hg]
  constructor
  · intro e
    have := congrArg (act g⁻¹) e
    rwa [hinv g _ (hlt _ _ hg)] at this
  · intro e
    rw [e, hinv' g m hm']

end Fix

section Normal

variable {d : ℕ} (T : PT d) [Fact (T.check = true)]

theorem normalChainB_iff (l : List T.Elem) :
    normalChainB T l = true ↔ ∀ t : T.Elem, ∀ a ∈ l, t * a * t⁻¹ ∈ subprods l := by
  simp only [normalChainB, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
    forall_const]
  exact ⟨fun h t => by simpa using h (T.elemEquiv t), fun h i => h _⟩

theorem subprods_mem_of_mem {P : Type*} [Group P] (f : P →* P) (S : Set P) (h1 : (1 : P) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    ∀ l : List P, (∀ a ∈ l, f a ∈ S) → ∀ s ∈ subprods l, f s ∈ S
  | [], _, s, hs => by
    simp only [subprods, List.mem_singleton] at hs
    rw [hs, map_one]
    exact h1
  | y :: l, h, s, hs => by
    have hl := subprods_mem_of_mem f S h1 hmul l fun a ha => h a (List.mem_cons_of_mem y ha)
    rcases mem_subprods_cons.1 hs with hs | ⟨w, hw, rfl⟩
    · exact hl s hs
    · rw [map_mul]
      exact hmul _ (h y List.mem_cons_self) _ (hl w hw)

theorem normalChainB_iff_subprods {l : List T.Elem} (hl : IsCommInvol l) :
    normalChainB T l = true ↔ ∀ t : T.Elem, ∀ s ∈ subprods l, t * s * t⁻¹ ∈ subprods l := by
  rw [normalChainB_iff]
  refine ⟨fun h t => ?_, fun h t a ha => h t a (mem_subprods_of_mem ha)⟩
  have := subprods_mem_of_mem (MulAut.conj t).toMonoidHom {x | x ∈ subprods l}
    (one_mem_subprods l) (mul_mem_subprods hl) l (fun a ha => h t a ha)
  simpa [MulAut.conj_apply] using this

theorem normalChainB_span {l r : List T.Elem} (hl : IsCommInvol l) (hr : IsCommInvol r)
    (h : ∀ x, x ∈ subprods l ↔ x ∈ subprods r) : normalChainB T l = normalChainB T r := by
  rw [Bool.eq_iff_iff, normalChainB_iff_subprods T hl, normalChainB_iff_subprods T hr]
  exact forall_congr' fun t => ⟨fun H s hs => (h _).1 (H s ((h s).2 hs)),
    fun H s hs => (h _).2 (H s ((h s).1 hs))⟩

theorem normalChainB_conj (g : T.Elem) (l : List T.Elem) :
    normalChainB T (l.map (MulAut.conj g)) = normalChainB T l := by
  rw [Bool.eq_iff_iff, normalChainB_iff, normalChainB_iff, subprods_map_mulEquiv]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    MulAut.conj_apply]
  constructor
  · intro H t a ha
    obtain ⟨s, hs, e⟩ := H (g * t * g⁻¹) a ha
    have : s = t * a * t⁻¹ := by
      have e' := congrArg (fun x => g⁻¹ * x * g) e
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at e'
      rw [e', mul_inv_rev, mul_inv_rev, inv_inv]
      group
    exact this ▸ hs
  · intro H t a ha
    refine ⟨g⁻¹ * t * g * a * (g⁻¹ * t * g)⁻¹, H _ a ha, ?_⟩
    group

end Normal

open CFSG.Monster.Code

theorem codeAct24_toW (s : T24s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    rhoC11 AutPerm le_rfl (phi24 s) (toW 11 m) = toW 11 (codeAct24 s m) := by
  rw [codeAct24, actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
  exact rhoC11_toW AutPerm le_rfl _ (T24s2.hasArr_toSub _ _ s) m

theorem codeAct24_lt (s : T24s2.Elem) (m : ℕ) (hm : m < 2 ^ 11) : codeAct24 s m < 2 ^ 11 := by
  rw [codeAct24, actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
  exact actC11_lt _ _

theorem codeAct24_mul (s t : T24s2.Elem) (m : ℕ) (hm : m < 2 ^ 11) :
    codeAct24 (s * t) m = codeAct24 s (codeAct24 t m) := by
  refine toW_inj (codeAct24_lt _ m hm) (codeAct24_lt _ _ (codeAct24_lt _ m hm)) ?_
  rw [← codeAct24_toW _ hm, ← codeAct24_toW _ (codeAct24_lt _ m hm), ← codeAct24_toW _ hm,
    map_mul, map_mul, MulAut.mul_apply]

theorem codeAct24_one (m : ℕ) (hm : m < 2 ^ 11) : codeAct24 1 m = m := by
  refine toW_inj (codeAct24_lt _ m hm) hm ?_
  rw [← codeAct24_toW _ hm, map_one, map_one, MulAut.one_apply]

theorem codeFixMasks24_eq_fixMasks {l : List T24s2.Elem} (hl : ∀ a ∈ l, a * a = 1) :
    codeFixMasks24 l = fixMasks 11 codeAct24 l := by
  cases l with
  | nil => rfl
  | cons a l =>
    have ha := hl a List.mem_cons_self
    have htab : codeFixTab24[a.idx]! = fixMasks 11 codeAct24 [a] := by
      rw [codeFixTab24, getElem!_pos _ a.idx (by simpa using a.lt), Array.getElem_ofFn]
      have : T24s2.elemEquiv.symm ⟨a.idx, a.lt⟩ = a := rfl
      simp only [this, ha, ↓reduceIte]
    rw [codeFixMasks24, htab, ← fixMasks_cons]

theorem predHF24_span (l r : List T24s2.Elem) (hl : IndepList l) (hr : IndepList r)
    (hlen : l.length = r.length) (h : ∀ x, x ∈ subprods l ↔ x ∈ subprods r) :
    predHF24 l = predHF24 r := by
  have hcl := isCommInvol_of_indepList hl
  have hcr := isCommInvol_of_indepList hr
  unfold predHF24
  rw [codeFixMasks24_eq_fixMasks hcl.1, codeFixMasks24_eq_fixMasks hcr.1,
    fixMasks_span codeAct24_mul codeAct24_one h, normalChainB_span T24s2 hcl hcr h, hlen]

theorem predHF24_conj (g : T24s2.Elem) (l : List T24s2.Elem) (hl : IndepList l) :
    predHF24 (l.map (MulAut.conj g)) = predHF24 l := by
  have hcl := isCommInvol_of_indepList hl
  have hcg := isCommInvol_of_indepList (indepList_map (MulAut.conj g) hl)
  unfold predHF24
  rw [codeFixMasks24_eq_fixMasks hcl.1, codeFixMasks24_eq_fixMasks hcg.1,
    length_fixMasks_conj codeAct24_mul codeAct24_one codeAct24_lt, normalChainB_conj,
    List.length_map]

end CFSG.Quasithin.H.Mathieu
