module

public import CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs
public import CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Recognition.McLMultiplier CFSG.CosetTable

section Words

variable {G : Type*} [Group G]

theorem lift_mk_nil (g : Fin 6 → G) :
    FreeGroup.lift g (FreeGroup.mk ([] : List (Fin 6 × Bool))) = 1 := by
  rw [← FreeGroup.one_eq_mk, map_one]

theorem lift_mk_cons (g : Fin 6 → G) (l : Fin 6 × Bool) (w : List (Fin 6 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (l :: w)) =
      (if l.2 then g l.1 else (g l.1)⁻¹) * FreeGroup.lift g (FreeGroup.mk w) := by
  have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
  rw [e, map_mul, lift_mk_single]

theorem lift_mk_kLetter (g : Fin 6 → G) : FreeGroup.lift g (FreeGroup.mk [kLetter]) = g 5 := by
  rw [lift_mk_single]
  rfl

theorem lift_derivInvLetter {g : Fin 6 → G} (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1)
    (l : Fin 6 × Bool) :
    FreeGroup.lift g (FreeGroup.mk [derivInvLetter l]) =
      (FreeGroup.lift g (FreeGroup.mk [l]))⁻¹ := by
  obtain ⟨i, b⟩ := l
  rw [lift_mk_single, lift_mk_single]
  by_cases hi : i.val = 1
  · cases b <;> simp [derivInvLetter, hi]
  · have h' : (g i)⁻¹ = g i := inv_eq_of_mul_eq_one_right (hinv i hi)
    cases b <;> simp [derivInvLetter, hi, h']

theorem lift_derivInv {g : Fin 6 → G} (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1)
    (w : List (Fin 6 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (derivInv w)) = (FreeGroup.lift g (FreeGroup.mk w))⁻¹ := by
  induction w with
  | nil => simp [derivInv]
  | cons l w ih =>
    have e : derivInv (l :: w) = derivInv w ++ [derivInvLetter l] := by simp [derivInv]
    have e' : FreeGroup.lift g (FreeGroup.mk (l :: w)) =
        FreeGroup.lift g (FreeGroup.mk [l]) * FreeGroup.lift g (FreeGroup.mk w) :=
      lift_mk_append g [l] w
    rw [e, lift_mk_append, ih, lift_derivInvLetter hinv, e', mul_inv_rev]

theorem lift_mk_kLetter_cons (g : Fin 6 → G) (w : List (Fin 6 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (kLetter :: w)) = g 5 * FreeGroup.lift g (FreeGroup.mk w) := by
  simp [kLetter]

end Words

section Steps

variable {G : Type*} [Group G] {g : Fin 6 → G}

theorem replaceAt_eq {cur old new r : List (Fin 6 × Bool)} {pos : ℕ}
    (h : replaceAt cur pos old new = some r) :
    cur = cur.take pos ++ old ++ cur.drop (pos + old.length) ∧
      r = cur.take pos ++ new ++ cur.drop (pos + old.length) := by
  unfold replaceAt at h
  split_ifs at h with hc
  · refine ⟨?_, (Option.some.inj h).symm⟩
    have e1 := List.take_append_drop old.length (cur.drop pos)
    rw [hc, List.drop_drop] at e1
    calc cur = cur.take pos ++ cur.drop pos := (List.take_append_drop pos cur).symm
      _ = cur.take pos ++ (old ++ cur.drop (pos + old.length)) := by rw [e1]
      _ = cur.take pos ++ old ++ cur.drop (pos + old.length) := (List.append_assoc _ _ _).symm

theorem lift_replaceAt {cur old new r : List (Fin 6 × Bool)} {pos : ℕ}
    (h : replaceAt cur pos old new = some r)
    (hon : FreeGroup.lift g (FreeGroup.mk old) = FreeGroup.lift g (FreeGroup.mk new)) :
    FreeGroup.lift g (FreeGroup.mk cur) = FreeGroup.lift g (FreeGroup.mk r) := by
  obtain ⟨h1, h2⟩ := replaceAt_eq h
  calc FreeGroup.lift g (FreeGroup.mk cur)
      = FreeGroup.lift g (FreeGroup.mk (cur.take pos ++ old ++ cur.drop (pos + old.length))) :=
        congrArg (fun x => FreeGroup.lift g (FreeGroup.mk x)) h1
    _ = FreeGroup.lift g (FreeGroup.mk (cur.take pos ++ new ++ cur.drop (pos + old.length))) := by
        rw [lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_append, hon]
    _ = FreeGroup.lift g (FreeGroup.mk r) := by rw [h2]

theorem ruleOK_sound
    {rules : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))}
    (hr : ∀ p ∈ rules, FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2))
    {old new : List (Fin 6 × Bool)} (h : ruleOK rules old new = true) :
    FreeGroup.lift g (FreeGroup.mk old) = FreeGroup.lift g (FreeGroup.mk new) := by
  simp only [ruleOK, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨p, hp, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]
    exact hr p hp
  · rw [← h1, ← h2]
    exact (hr p hp).symm

theorem dist2KRules_sound (hk : g 5 * g 5 = 1) :
    ∀ p ∈ dist2KRules,
      FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2) := by
  have e : FreeGroup.lift g (FreeGroup.mk kkRel) = 1 := by
    have e' : FreeGroup.mk kkRel = FreeGroup.mk [kLetter] * FreeGroup.mk [kLetter] := rfl
    rw [e', map_mul, lift_mk_kLetter]
    exact hk
  intro p hp
  simp only [dist2KRules, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [e, lift_mk_nil]
  · simp only [e, lift_mk_nil]

theorem eRule_one (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) {U V : List (Fin 6 × Bool)}
    (h : FreeGroup.lift g (FreeGroup.mk (kLetter :: (U ++ kLetter :: V))) = 1) :
    FreeGroup.lift g (FreeGroup.mk (kLetter :: (U ++ [kLetter]))) =
      FreeGroup.lift g (FreeGroup.mk (derivInv V)) := by
  rw [lift_derivInv hinv]
  simp only [lift_mk_kLetter_cons, lift_mk_append, lift_mk_nil, mul_one] at h ⊢
  apply eq_inv_of_mul_eq_one_left
  rw [← h]
  group

theorem eRule_two (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (hk : g 5 * g 5 = 1)
    {U V : List (Fin 6 × Bool)}
    (h : FreeGroup.lift g (FreeGroup.mk (kLetter :: (U ++ kLetter :: V))) = 1) :
    FreeGroup.lift g (FreeGroup.mk (kLetter :: (derivInv U ++ [kLetter]))) =
      FreeGroup.lift g (FreeGroup.mk V) := by
  have h1 := eRule_one hinv h
  have hk' : (g 5)⁻¹ = g 5 := inv_eq_of_mul_eq_one_right hk
  rw [lift_derivInv hinv] at h1
  simp only [lift_mk_kLetter_cons, lift_mk_append, lift_mk_nil, mul_one,
    lift_derivInv hinv] at h1 ⊢
  have h2 : FreeGroup.lift g (FreeGroup.mk V) =
      (g 5 * (FreeGroup.lift g (FreeGroup.mk U) * g 5))⁻¹ := by
    rw [h1, inv_inv]
  rw [h2]
  simp only [mul_inv_rev, hk', mul_assoc]

theorem dist2ERules_sound (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (hk : g 5 * g 5 = 1)
    (hE : ∀ e ∈ dist2EEvs, FreeGroup.lift g (FreeGroup.mk (eRelOf e)) = 1) :
    ∀ p ∈ dist2ERules,
      FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2) := by
  intro p hp
  simp only [dist2ERules, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨e, he, rfl | rfl⟩ := hp
  · exact eRule_one hinv (hE e he)
  · exact eRule_two hinv hk (hE e he)

theorem tRule_one (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (hk : g 5 * g 5 = 1)
    {s₁ s₂ s₃ : List (Fin 6 × Bool)}
    (h : FreeGroup.lift g
      (FreeGroup.mk (kLetter :: (s₁ ++ kLetter :: (s₂ ++ kLetter :: s₃)))) = 1) :
    FreeGroup.lift g (FreeGroup.mk (kLetter :: (s₁ ++ [kLetter]))) =
      FreeGroup.lift g (FreeGroup.mk (derivInv s₃ ++ kLetter :: derivInv s₂)) := by
  have hk' : (g 5)⁻¹ = g 5 := inv_eq_of_mul_eq_one_right hk
  simp only [lift_mk_kLetter_cons, lift_mk_append, lift_mk_nil, mul_one,
    lift_derivInv hinv] at h ⊢
  have h1 : g 5 * (FreeGroup.lift g (FreeGroup.mk s₁) * g 5) *
      (FreeGroup.lift g (FreeGroup.mk s₂) * (g 5 * FreeGroup.lift g (FreeGroup.mk s₃))) = 1 := by
    rw [← h]
    group
  have h2 := eq_inv_of_mul_eq_one_left h1
  rw [h2]
  simp only [mul_inv_rev, hk', mul_assoc]

theorem tRule_two (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (hk : g 5 * g 5 = 1)
    {s₁ s₂ s₃ : List (Fin 6 × Bool)}
    (h : FreeGroup.lift g
      (FreeGroup.mk (kLetter :: (s₁ ++ kLetter :: (s₂ ++ kLetter :: s₃)))) = 1) :
    FreeGroup.lift g (FreeGroup.mk [kLetter]) =
      FreeGroup.lift g (FreeGroup.mk
        (derivInv s₂ ++ kLetter :: (derivInv s₁ ++ kLetter :: derivInv s₃))) := by
  have hk' : (g 5)⁻¹ = g 5 := inv_eq_of_mul_eq_one_right hk
  simp only [lift_mk_kLetter_cons, lift_mk_append, lift_mk_nil, mul_one,
    lift_derivInv hinv] at h ⊢
  have h1 : g 5 * (FreeGroup.lift g (FreeGroup.mk s₁) * g 5) *
      (FreeGroup.lift g (FreeGroup.mk s₂) * (g 5 * FreeGroup.lift g (FreeGroup.mk s₃))) = 1 := by
    rw [← h]
    group
  have h3 : FreeGroup.lift g (FreeGroup.mk s₂) * (g 5 * FreeGroup.lift g (FreeGroup.mk s₃)) =
      g 5 * ((FreeGroup.lift g (FreeGroup.mk s₁))⁻¹ * g 5) := by
    rw [eq_inv_of_mul_eq_one_right h1]
    simp only [mul_inv_rev, hk', mul_assoc]
  calc g 5 = (FreeGroup.lift g (FreeGroup.mk s₂))⁻¹ *
        (FreeGroup.lift g (FreeGroup.mk s₂) * (g 5 * FreeGroup.lift g (FreeGroup.mk s₃))) *
        (FreeGroup.lift g (FreeGroup.mk s₃))⁻¹ := by group
    _ = (FreeGroup.lift g (FreeGroup.mk s₂))⁻¹ *
        (g 5 * ((FreeGroup.lift g (FreeGroup.mk s₁))⁻¹ * g 5)) *
        (FreeGroup.lift g (FreeGroup.mk s₃))⁻¹ := by rw [h3]
    _ = (FreeGroup.lift g (FreeGroup.mk s₂))⁻¹ *
        (g 5 * ((FreeGroup.lift g (FreeGroup.mk s₁))⁻¹ *
          (g 5 * (FreeGroup.lift g (FreeGroup.mk s₃))⁻¹))) := by group

theorem trRel_dist2TrEv :
    trRel dist2TrEv = kLetter :: (rhoS1 ++ kLetter :: (rhoS2 ++ kLetter :: rhoS3)) := by
  simp [trRel, dist2TrEv]

theorem dist2TRules_sound (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (hk : g 5 * g 5 = 1)
    (hρ : FreeGroup.lift g (FreeGroup.mk (trRel dist2TrEv)) = 1) :
    ∀ p ∈ dist2TRules,
      FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2) := by
  rw [trRel_dist2TrEv] at hρ
  intro p hp
  simp only [dist2TRules, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact tRule_one hinv hk hρ
  · exact tRule_two hinv hk hρ

theorem dist2StepOK_sound {cells : List (List (Fin 6 × Bool))}
    (hB : ∀ w ∈ cells, FreeGroup.lift g (FreeGroup.mk w) = 1)
    (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (hk : g 5 * g 5 = 1)
    (hE : ∀ e ∈ dist2EEvs, FreeGroup.lift g (FreeGroup.mk (eRelOf e)) = 1)
    (hρ : FreeGroup.lift g (FreeGroup.mk (trRel dist2TrEv)) = 1) {s : Dist2Step}
    (h : dist2StepOK cells s = true) :
    FreeGroup.lift g (FreeGroup.mk (parseWord s.old)) =
      FreeGroup.lift g (FreeGroup.mk (parseWord s.new)) := by
  unfold dist2StepOK at h
  split at h
  · simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨c, hc, hce⟩ := h
    have h1 := hB c hc
    rw [hce, lift_mk_append, lift_derivInv hinv] at h1
    exact mul_inv_eq_one.1 h1
  · exact ruleOK_sound (dist2KRules_sound hk) h
  · exact ruleOK_sound (dist2ERules_sound hinv hk hE) h
  · exact ruleOK_sound (dist2TRules_sound hinv hk hρ) h

theorem dist2Replay_sound {cells : List (List (Fin 6 × Bool))}
    (hstep : ∀ s : Dist2Step, dist2StepOK cells s = true →
      FreeGroup.lift g (FreeGroup.mk (parseWord s.old)) =
        FreeGroup.lift g (FreeGroup.mk (parseWord s.new))) :
    ∀ (steps : List Dist2Step) (cur : List (Fin 6 × Bool)), dist2Replay cells cur steps = true →
      FreeGroup.lift g (FreeGroup.mk cur) = 1 := by
  intro steps
  induction steps with
  | nil =>
    intro cur h
    have : cur = [] := List.isEmpty_iff.1 h
    rw [this, lift_mk_nil]
  | cons s ss ih =>
    intro cur h
    unfold dist2Replay at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hs, h⟩ := h
    rcases hr : replaceAt cur s.pos (parseWord s.old) (parseWord s.new) with _ | cur'
    · rw [hr] at h
      exact absurd h (by simp)
    · rw [hr] at h
      rw [lift_replaceAt hr (hstep s hs)]
      exact ih cur' h

end Steps

section Soundness

variable {G : Type*} [Group G]

theorem lift_dist2_eq_one_of_replays (g : Fin 6 → G)
    (hB : ∀ w ∈ dist2BWords, FreeGroup.lift g (FreeGroup.mk w) = 1)
    (hk : g 5 * g 5 = 1)
    (hE : ∀ e ∈ dist2EEvs, FreeGroup.lift g (FreeGroup.mk (eRelOf e)) = 1)
    (hρ : FreeGroup.lift g (FreeGroup.mk (trRel dist2TrEv)) = 1)
    (h : dist2Replays = true) :
    ∀ r ∈ dist2Relators, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
  unfold dist2Replays at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hstarts, hders⟩ := h
  have hcc : ∀ j ∈ [(0 : Fin 6), 2, 3, 4], g j * g j = 1 := by
    intro j hj
    have hmem : [(j, true), (j, true)] ∈ dist2BWords := by
      simp only [dist2BWords, List.mem_eraseDups, List.mem_append, List.mem_map]
      exact Or.inl ⟨j, hj, rfl⟩
    simpa [lift_mk_cons, lift_mk_nil] using hB _ hmem
  have hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1 := by
    intro i hi
    fin_cases i
    · exact hcc 0 (by simp)
    · exact absurd rfl hi
    · exact hcc 2 (by simp)
    · exact hcc 3 (by simp)
    · exact hcc 4 (by simp)
    · exact hk
  have hstep := fun s => dist2StepOK_sound hB hinv hk hE hρ (s := s)
  intro r hr
  rw [← hstarts] at hr
  simp only [List.mem_map] at hr
  obtain ⟨d, hd, rfl⟩ := hr
  exact dist2Replay_sound hstep d.steps _ (hders d hd)

theorem lift_dist2_eq_one (g : Fin 6 → G)
    (hB : ∀ w : List (Fin 6 × Bool), bWordCheck w = true → FreeGroup.lift g (FreeGroup.mk w) = 1)
    (hk : g 5 * g 5 = 1)
    (hE : ∀ e ∈ dist2EEvs, FreeGroup.lift g (FreeGroup.mk (eRelOf e)) = 1)
    (hρ : FreeGroup.lift g (FreeGroup.mk (trRel dist2TrEv)) = 1)
    (h : dist2Check = true) :
    ∀ r ∈ dist2Relators, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
  simp only [dist2Check, Bool.and_eq_true, dist2BCheck, List.all_eq_true] at h
  exact lift_dist2_eq_one_of_replays g (fun w hw => hB w (h.1.2 w hw)) hk hE hρ h.2

theorem mk_dist2_mem_normalClosure {S : Set (FreeGroup (Fin 6))}
    (hB : ∀ w ∈ dist2BWords, FreeGroup.mk w ∈ S) (hk : FreeGroup.mk kkRel ∈ S)
    (hE : ∀ e ∈ dist2EEvs, FreeGroup.mk (eRelOf e) ∈ S)
    (hρ : FreeGroup.mk (trRel dist2TrEv) ∈ S) (h : dist2Replays = true) :
    ∀ r ∈ dist2Relators, FreeGroup.mk r ∈ Subgroup.normalClosure S := by
  let N : Subgroup (FreeGroup (Fin 6)) := Subgroup.normalClosure S
  let g : Fin 6 → FreeGroup (Fin 6) ⧸ N := fun i => QuotientGroup.mk (FreeGroup.of i)
  have hlift : ∀ w : List (Fin 6 × Bool),
      FreeGroup.lift g (FreeGroup.mk w) = QuotientGroup.mk (FreeGroup.mk w) := by
    have e : FreeGroup.lift g = QuotientGroup.mk' N :=
      FreeGroup.ext_hom _ _ fun i => by simp [g]
    intro w
    exact DFunLike.congr_fun e (FreeGroup.mk w)
  have hone : ∀ w, FreeGroup.mk w ∈ S → FreeGroup.lift g (FreeGroup.mk w) = 1 := by
    intro w hw
    rw [hlift]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure hw)
  have hkk : g 5 * g 5 = 1 := by
    have e : FreeGroup.lift g (FreeGroup.mk kkRel) = g 5 * g 5 := by
      have e' : FreeGroup.mk kkRel = FreeGroup.mk [kLetter] * FreeGroup.mk [kLetter] := rfl
      rw [e', map_mul, lift_mk_kLetter]
    rw [← e]
    exact hone _ hk
  intro r hr
  have h1 := lift_dist2_eq_one_of_replays g (fun w hw => hone w (hB w hw)) hkk
    (fun e he => hone _ (hE e he)) (hone _ hρ) h r hr
  rw [hlift] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

end Soundness

section Final

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem lift_gOf_dist2 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) (hT : Ly243.trCheck = true)
    (hτ : Tau.tauOK = true) (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) (M : ModelGlue)
    (hMtx : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val []) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k)
    (hd : dist2Check = true) :
    ∀ r ∈ dist2Relators, FreeGroup.lift (gOf φ k) (FreeGroup.mk r) = 1 := by
  have hev := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hd).1).1
  simp only [dist2Evidence, Bool.and_eq_true, List.all_eq_true] at hev
  obtain ⟨hE, hρ⟩ := hev
  refine lift_dist2_eq_one (gOf φ k) (fun w hw => lift_gOf_bword_eq_one φ k hM.tab hw) ?_ ?_ ?_ hd
  · simpa [gOf] using hk.mul_self
  · intro e he
    exact lift_gOf_erel φ hφY M hk hY hM.tab (hE e he)
  · exact lift_gOf_trrel D S hY hT hτ hM.tab φ hφY hφT hφK M hMtx hk hρ

end Final

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
