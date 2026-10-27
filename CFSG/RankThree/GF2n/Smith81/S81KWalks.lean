module

public import CFSG.RankThree.GF2n.Smith81.S81KLevi

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.EPilot
  CFSG.RankThree.GF2n.Smith81.D6X CFSG.RankThree.GF2n.Smith81.E7X
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.MinuscT

section Frames


variable (K : Type) [Field K] in
@[expose] def FrameProdConjD (F F' : List Rt) : Prop :=
  ∃ g ∈ rootSpan .E7 K (perpRoots .E7), g * (F.map fun σ => pinnedX .E7 K σ 1).prod * g⁻¹ =
    (F'.map fun σ => pinnedX .E7 K σ 1).prod

variable {K : Type} [Field K]

theorem FrameProdConjD.refl (F : List Rt) : FrameProdConjD K F F :=
  ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem FrameProdConjD.trans {F F' F'' : List Rt} (h₁ : FrameProdConjD K F F')
    (h₂ : FrameProdConjD K F' F'') : FrameProdConjD K F F'' := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [← e₂, ← e₁]
  group

theorem weylElt_mem_rootSpan_perpRoots {j : Fin Tag.E7.rank} (hj : j ≠ highNode .E7) :
    weylElt .E7 K j 1 ∈ rootSpan .E7 K (perpRoots .E7) :=
  sup_le (rootSubgroup_le_rootSpan_perpRoots (single_mem_perpRoots hj))
    (rootSubgroup_le_rootSpan_perpRoots (neg_single_mem_perpRoots hj)) (weylElt_mem_rootPair j 1)

theorem e4Reps_mem_perpRoots : ∀ T ∈ e4Reps, ∀ σ ∈ T, σ ∈ perpRoots .E7 := by
  have h1 : (e4Reps.all fun T => T.all fun σ => RootOps.isRootB .E7 σ &&
      decide (σ (highNode .E7) = 0)) = true := by decide +kernel
  intro T hT σ hσ
  have := List.all_eq_true.1 (List.all_eq_true.1 h1 T hT) σ hσ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨RootOps.isRootB_iff.1 this.1, this.2⟩

end Frames

section Moves


variable {K : Type} [Field K] [CharP K 2]

theorem frameProdConjD_of_perm {F F' : List Rt} (hF : ∀ σ ∈ F, IsRoot .E7 σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (hp : F.Perm F') :
    FrameProdConjD K F F' :=
  ⟨1, one_mem _, by
    rw [one_mul, inv_one, mul_one]
    exact classD4_frame_prod_perm (Or.inr (Or.inr (Or.inl rfl))) hF horth hp fun _ => (1 : K)⟩

theorem frameProdConjD_map_reflect {j : Fin Tag.E7.rank} (hj : j ≠ highNode .E7)
    {F : List Rt} (hF : ∀ σ ∈ F, IsRoot .E7 σ) : FrameProdConjD K F (F.map (reflect .E7 j)) := by
  obtain ⟨η, hη, h⟩ := classDescent_exists_sign_conj_list_prod (K := K) j
  refine ⟨weylElt .E7 K j 1, weylElt_mem_rootSpan_perpRoots hj, ?_⟩
  have h' := h (fun _ => 1) F hF
  simp only [mul_one] at h'
  rw [h', List.map_map]
  refine congrArg List.prod (List.map_congr_left fun σ hσ => ?_)
  rw [frameWalk_eq_one_of_mul_self (hη σ (hF σ hσ))]
  rfl

theorem frameProdConjD_d4 {a b c d θ : Rt} (hp : IsD4Pattern .E7 a b c d)
    (hθ : a + b + 2 • c + d = θ) (ha : a ∈ perpRoots .E7) (hb : b ∈ perpRoots .E7)
    (hd : d ∈ perpRoots .E7) (hθp : θ ∈ perpRoots .E7) {F P : List Rt}
    (hFP : F.Perm (a :: b :: d :: θ :: P)) (hF : ∀ σ ∈ F, IsRoot .E7 σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    FrameProdConjD K F (a :: b :: d :: P) := by
  have hτ : (Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8) :=
    Or.inr (Or.inr (Or.inl rfl))
  have horth' : (a :: b :: d :: θ :: P).Pairwise fun σ σ' => iform σ σ' = 0 :=
    hFP.pairwise horth fun h => by rw [iform_comm]; exact h
  have hF' : ∀ σ ∈ a :: b :: d :: θ :: P, IsRoot .E7 σ := fun σ hσ => hF σ (hFP.mem_iff.2 hσ)
  have hc0 : c (highNode .E7) = 0 := by
    have h1 := congrFun hθ (highNode .E7)
    simp only [Pi.add_apply, Pi.smul_apply] at h1
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h1
    have h2 := ha.2
    have h3 := hb.2
    have h4 := hd.2
    have h5 := hθp.2
    omega
  obtain ⟨rac, rbc, rcd, -, -, rbcd, -, -⟩ := IsD4Pattern.isRoot_add hτ hp
  have m1 : c + d ∈ perpRoots .E7 := ⟨rcd, by simp [hc0, hd.2]⟩
  have m2 : b + c ∈ perpRoots .E7 := ⟨rbc, by simp [hc0, hb.2]⟩
  have m3 : a + c ∈ perpRoots .E7 := ⟨rac, by simp [hc0, ha.2]⟩
  have m4 : b + c + d ∈ perpRoots .E7 := ⟨rbcd, by simp [hc0, hb.2, hd.2]⟩
  refine (frameProdConjD_of_perm hF horth hFP).trans ?_
  have hP : ∀ ρ ∈ P, IsRoot .E7 ρ ∧ iform ρ a = 0 ∧ iform ρ b = 0 ∧ iform ρ d = 0 ∧
      iform ρ θ = 0 := by
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at horth'
    obtain ⟨⟨-, -, -, hPa⟩, ⟨-, -, hPb⟩, ⟨-, hPd⟩, hPθ, -⟩ := horth'
    intro ρ hρ
    refine ⟨hF' ρ (by simp [hρ]), ?_, ?_, ?_, ?_⟩ <;> rw [iform_comm]
    exacts [hPa ρ hρ, hPb ρ hρ, hPd ρ hρ, hPθ ρ hρ]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key := classD4_conj_frame hτ h2 hp hθ hP fun _ => (1 : K)
  refine ⟨pinnedX .E7 K (c + d) 1 * pinnedX .E7 K (b + c) 1 * pinnedX .E7 K (a + c) 1 *
    pinnedX .E7 K (b + c + d) 1, mul_mem (mul_mem (mul_mem (pinnedX_mem_rootSpan m1 _)
      (pinnedX_mem_rootSpan m2 _)) (pinnedX_mem_rootSpan m3 _)) (pinnedX_mem_rootSpan m4 _), ?_⟩
  simp only [List.map_cons, List.prod_cons] at key ⊢
  simpa only [mul_assoc] using key

@[expose] def FramePosD (F : List ℕ) : Prop :=
  ∀ k ∈ F, k < Tag.E7.rootCertificate.roots.length ∧
    Tag.E7.rootCertificate.root k (highNode .E7) = 0

@[expose] def frameMoveD6B : FrameWalkMove → Bool
  | .word ω => ω.all fun i => decide (i % 7 ≠ 0)
  | .d4 _ _ _ _ _ => true

theorem idx_ne_highNode {i : ℕ} (h : i % 7 ≠ 0) : Tag.E7.idx i ≠ highNode .E7 := by
  intro e
  apply h
  have := congrArg Fin.val e
  simpa [Tag.idx, highNode, show Tag.E7.rank = 7 from rfl] using this

theorem frameWalk_word_soundD (ω : List ℕ) (hω : ∀ i ∈ ω, i % 7 ≠ 0) : ∀ {F : List ℕ},
    FramePosD F → (F.map Tag.E7.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) →
    FramePosD (F.map (wordPos Tag.E7.rootCertificate ω)) ∧
      ((F.map (wordPos Tag.E7.rootCertificate ω)).map Tag.E7.rootCertificate.root).Pairwise
        (fun σ σ' => iform σ σ' = 0) ∧
      FrameProdConjD K (F.map Tag.E7.rootCertificate.root)
        ((F.map (wordPos Tag.E7.rootCertificate ω)).map Tag.E7.rootCertificate.root) := by
  induction ω with
  | nil =>
    intro F hF horth
    have e : F.map (wordPos Tag.E7.rootCertificate []) = F := by
      conv_rhs => rw [← List.map_id F]
      rfl
    rw [e]
    exact ⟨hF, horth, .refl _⟩
  | cons i ω ih =>
    intro F hF horth
    have hC := Tag.E7.rootCertificate_check
    have hi : Tag.E7.idx i ≠ highNode .E7 := idx_ne_highNode (hω i List.mem_cons_self)
    have hω' : ∀ j ∈ ω, j % 7 ≠ 0 := fun j hj => hω j (List.mem_cons_of_mem _ hj)
    have e : F.map (wordPos Tag.E7.rootCertificate (i :: ω)) =
        (F.map fun k => Tag.E7.rootCertificate.image k (Tag.E7.idx i)).map
          (wordPos Tag.E7.rootCertificate ω) := by
      rw [List.map_map]
      rfl
    have hF₁ : FramePosD (F.map fun k => Tag.E7.rootCertificate.image k (Tag.E7.idx i)) := by
      intro k hk
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
      obtain ⟨h1, h2⟩ := image_spec_of_check hC (hF k' hk').1 (Tag.E7.idx i)
      refine ⟨h1, ?_⟩
      rw [h2, reflect_apply_of_ne _ (Ne.symm hi)]
      exact (hF k' hk').2
    have e₁ : (F.map fun k => Tag.E7.rootCertificate.image k (Tag.E7.idx i)).map
        Tag.E7.rootCertificate.root =
        (F.map Tag.E7.rootCertificate.root).map (reflect .E7 (Tag.E7.idx i)) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun k hk => (image_spec_of_check hC (hF k hk).1 _).2
    have horth₁ : ((F.map fun k => Tag.E7.rootCertificate.image k (Tag.E7.idx i)).map
        Tag.E7.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) := by
      rw [e₁, List.pairwise_map]
      exact horth.imp fun h => by rw [iform_reflect]; exact h
    obtain ⟨h₁, h₂, h₃⟩ := ih hω' hF₁ horth₁
    have hroots : ∀ σ ∈ F.map Tag.E7.rootCertificate.root, IsRoot .E7 σ := by
      intro σ hσ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
      exact RootCertificate.isRoot_root hC k (hF k hk).1
    rw [e]
    refine ⟨h₁, h₂, ?_⟩
    have h₀ := frameProdConjD_map_reflect (K := K) hi hroots
    rw [← e₁] at h₀
    exact h₀.trans h₃

theorem frameWalkStep_soundD {F F' : List ℕ} {m : FrameWalkMove} (hm : frameMoveD6B m = true)
    (hF : FramePosD F)
    (horth : (F.map Tag.E7.rootCertificate.root).Pairwise fun σ σ' => iform σ σ' = 0)
    (h : frameWalkStep .E7 F m = some F') :
    FramePosD F' ∧ (F'.map Tag.E7.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      FrameProdConjD K (F.map Tag.E7.rootCertificate.root)
        (F'.map Tag.E7.rootCertificate.root) := by
  have hC := Tag.E7.rootCertificate_check
  cases m with
  | word ω =>
    simp only [frameWalkStep, Option.some.injEq] at h
    subst h
    exact frameWalk_word_soundD ω (by simpa [frameMoveD6B] using hm) hF horth
  | d4 a b c d θ =>
    simp only [frameWalkStep] at h
    split_ifs at h with hB
    simp only [Option.some.injEq] at h
    subst h
    simp only [frameWalkD4B, Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hac⟩, hbc⟩, hdc⟩, hab⟩, had⟩, hbd⟩, hθ⟩, hperm⟩ := hB
    have hperm' := List.isPerm_iff.1 hperm
    set P := frameWalkRest F a b d θ
    have hmem : ∀ k ∈ a :: b :: d :: θ :: P, k ∈ F := fun k hk => hperm'.mem_iff.2 hk
    have hroot : ∀ k ∈ F, IsRoot .E7 (Tag.E7.rootCertificate.root k) := fun k hk =>
      RootCertificate.isRoot_root hC k (hF k hk).1
    have hpat : IsD4Pattern .E7 (Tag.E7.rootCertificate.root a) (Tag.E7.rootCertificate.root b)
        (Tag.E7.rootCertificate.root c) (Tag.E7.rootCertificate.root d) :=
      ⟨hroot a (hmem a (by simp)), hroot b (hmem b (by simp)),
        RootCertificate.isRoot_root hC c hc, hroot d (hmem d (by simp)), hac, hbc, hdc, hab,
        had, hbd⟩
    have hθ' : Tag.E7.rootCertificate.root a + Tag.E7.rootCertificate.root b +
        2 • Tag.E7.rootCertificate.root c + Tag.E7.rootCertificate.root d =
          Tag.E7.rootCertificate.root θ :=
      (RootCertificate.eq_of_ofFn_beq hθ).symm
    have hFP : (F.map Tag.E7.rootCertificate.root).Perm
        ((a :: b :: d :: θ :: P).map Tag.E7.rootCertificate.root) := hperm'.map _
    have hFr : ∀ σ ∈ F.map Tag.E7.rootCertificate.root, IsRoot .E7 σ := by
      intro σ hσ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
      exact hroot k hk
    have hpd : ∀ k ∈ F, Tag.E7.rootCertificate.root k ∈ perpRoots .E7 := fun k hk =>
      ⟨hroot k hk, (hF k hk).2⟩
    refine ⟨fun k hk => hF k ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hmem _ (by simp)
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hmem _ (by simp)
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hmem _ (by simp)
      exact hmem _ (by simp [hk])
    · have horth' := hFP.pairwise horth fun h => by rw [iform_comm]; exact h
      refine horth'.sublist ?_
      simp only [List.map_cons]
      exact ((((List.Sublist.refl _).cons _).cons_cons _).cons_cons _).cons_cons _
    · exact frameProdConjD_d4 hpat hθ' (hpd a (hmem a (by simp))) (hpd b (hmem b (by simp)))
        (hpd d (hmem d (by simp))) (hpd θ (hmem θ (by simp))) hFP hFr horth

theorem frameWalkRun_soundD : ∀ (ms : List FrameWalkMove) {F F' : List ℕ},
    (∀ m ∈ ms, frameMoveD6B m = true) → FramePosD F →
    (F.map Tag.E7.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) →
    frameWalkRun .E7 F ms = some F' →
    FramePosD F' ∧ (F'.map Tag.E7.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      FrameProdConjD K (F.map Tag.E7.rootCertificate.root) (F'.map Tag.E7.rootCertificate.root)
  | [], F, F', _, hF, horth, h => by
    simp only [frameWalkRun, Option.some.injEq] at h
    subst h
    exact ⟨hF, horth, .refl _⟩
  | m :: ms, F, F', hms, hF, horth, h => by
    simp only [frameWalkRun, Option.bind_eq_some_iff] at h
    obtain ⟨F₁, h₁, h₂⟩ := h
    obtain ⟨hF₁, horth₁, hc₁⟩ := frameWalkStep_soundD (K := K) (hms m List.mem_cons_self) hF
      horth h₁
    obtain ⟨hF₂, horth₂, hc₂⟩ := frameWalkRun_soundD ms
      (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hF₁ horth₁ h₂
    exact ⟨hF₂, horth₂, hc₁.trans hc₂⟩

theorem frameWalkEnds_soundD {F T : List ℕ} {ms : List FrameWalkMove}
    (hms : ∀ m ∈ ms, frameMoveD6B m = true) (hF : FramePosD F)
    (horth : (F.map Tag.E7.rootCertificate.root).Pairwise fun σ σ' => iform σ σ' = 0)
    (h : frameWalkEnds .E7 F ms T = true) :
    FrameProdConjD K (F.map Tag.E7.rootCertificate.root) (T.map Tag.E7.rootCertificate.root) := by
  unfold frameWalkEnds at h
  split at h
  · rename_i F' hrun
    obtain ⟨hF', horth', hc⟩ := frameWalkRun_soundD (K := K) ms hms hF horth hrun
    have hp : F'.Perm T := List.isPerm_iff.1 h
    refine hc.trans (frameProdConjD_of_perm (fun σ hσ => ?_) horth' (hp.map _))
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
    exact RootCertificate.isRoot_root Tag.E7.rootCertificate_check k (hF' k hk).1
  · exact absurd h Bool.false_ne_true

theorem frameWalkCheck_soundD {casc : List ℕ} {targets : List (List ℕ)}
    {data : List (List ℕ × List FrameWalkMove × ℕ)}
    (h : frameWalkCheck .E7 casc targets data = true)
    (hdata : ∀ e ∈ data, ∀ m ∈ e.2.1, frameMoveD6B m = true) (hcasc : FramePosD casc)
    (horth : (casc.map Tag.E7.rootCertificate.root).Pairwise fun σ σ' => iform σ σ' = 0)
    {S : List ℕ} (hS : S.Sublist casc) (hne : S ≠ []) :
    ∃ T ∈ targets, FrameProdConjD K (S.map Tag.E7.rootCertificate.root)
      (T.map Tag.E7.rootCertificate.root) := by
  simp only [frameWalkCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨-, hall⟩ := h
  rcases hall S (mem_frameWalkSublists hS) with he | ⟨e, he, ⟨⟨rfl, hi⟩, hend⟩⟩
  · exact absurd (List.isEmpty_iff.1 he) hne
  · refine ⟨targets.getD e.2.2 [], ?_, frameWalkEnds_soundD (hdata e he)
      (fun k hk => hcasc k (hS.subset hk)) (horth.sublist (hS.map _)) hend⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

end Moves

section Data

@[expose] def d6WalkCasc : List ℕ := [93, 50, 4, 6, 1, 2]

@[expose] def d6WalkTargets : List (List ℕ) :=
  [[1], [2, 1], [23, 24], [2, 50, 1], [2, 75, 76], [1, 4, 6], [1, 2, 4, 6]]

@[expose] def d6Walks : List (List ℕ × List FrameWalkMove × ℕ) :=
  [([93], [.word [5, 4, 3, 2, 6, 5, 4, 3]], 0),
    ([50], [.word [3, 2, 4, 3]], 0),
    ([4], [.word [3, 1, 4, 3]], 0),
    ([6], [.word [5, 4, 3, 1, 6, 5, 4, 3]], 0),
    ([1], [], 0),
    ([2], [.word [3, 1, 2, 3]], 0),
    ([93, 50], [.word [3, 2, 4, 3, 5, 4, 3, 2, 6, 5]], 2),
    ([93, 4], [.word [3, 1, 4, 3, 5, 4, 3, 2, 6, 5]], 2),
    ([93, 6], [.word [5, 4, 3, 1, 6, 5, 4, 3]], 1),
    ([93, 1], [.word [5, 4, 3, 2, 6, 5]], 2),
    ([93, 2], [.word [3, 1, 2, 3, 5, 4, 3, 2, 6, 5]], 2),
    ([50, 4], [.word [3, 1, 4, 3]], 1),
    ([50, 6], [.word [3, 1, 4, 3, 5, 4, 3, 1, 6, 5]], 2),
    ([50, 1], [.word [3, 2]], 2),
    ([50, 2], [.word [3, 1, 5, 4, 3, 1, 2, 3, 4, 5]], 2),
    ([4, 6], [.word [3, 2, 4, 3, 5, 4, 3, 1, 6, 5]], 2),
    ([4, 1], [.word [3, 2, 5, 4, 3, 1, 2, 3, 4, 5]], 2),
    ([4, 2], [.word [3, 1]], 2),
    ([6, 1], [.word [3, 1, 2, 3, 5, 4, 3, 1, 6, 5]], 2),
    ([6, 2], [.word [5, 4, 3, 1, 6, 5]], 2),
    ([1, 2], [], 1),
    ([93, 50, 4], [.word [3, 1, 4, 3, 5, 4, 6, 5]], 3),
    ([93, 50, 6], [.word [3, 1, 4, 3, 5, 4, 3, 1, 6, 5, 4, 3]], 3),
    ([93, 50, 1], [.word [3, 1, 2, 3, 5, 4, 3, 1, 2, 3, 4, 5]], 5),
    ([93, 50, 2], [.word [5, 4]], 4),
    ([93, 4, 6], [.word [3, 1, 4, 3, 5, 4, 3, 2, 6, 5, 4, 3]], 3),
    ([93, 4, 1], [.word [3, 1, 2, 3, 5, 4]], 4),
    ([93, 4, 2], [.word [5, 4, 3, 1, 2, 3, 4, 5]], 5),
    ([93, 6, 1], [.word [5, 4, 3, 2, 6, 5, 4, 3]], 3),
    ([93, 6, 2], [.word [5, 4, 3, 1, 6, 5, 4, 3]], 3),
    ([93, 1, 2], [.word [5, 4, 6, 5]], 3),
    ([50, 4, 6], [.word [3, 1, 4, 3, 5, 4, 3, 1, 2, 3, 6, 5]], 3),
    ([50, 4, 1], [.word [3, 2, 4, 3]], 3),
    ([50, 4, 2], [.word [3, 1, 4, 3]], 3),
    ([50, 6, 1], [.word [5, 4, 3, 1, 2, 3]], 4),
    ([50, 6, 2], [.word [3, 1, 2, 3]], 5),
    ([50, 1, 2], [], 3),
    ([4, 6, 1], [], 5),
    ([4, 6, 2], [.word [3, 1, 2, 3, 5, 4, 3, 1, 2, 3]], 4),
    ([4, 1, 2], [.word [3, 1, 2, 3]], 3),
    ([6, 1, 2], [.word [5, 4, 3, 1, 2, 3, 6, 5]], 3),
    ([93, 50, 4, 6], [.word [3, 1, 4, 3, 5, 4, 6, 5], .d4 2 1 35 50 4], 3),
    ([93, 50, 4, 1], [.word [3, 1, 4, 3, 5, 4, 3, 1, 2, 3, 4, 5]], 6),
    ([93, 50, 4, 2], [.word [3, 2, 4, 3, 5, 4, 3, 1, 2, 3, 4, 5]], 6),
    ([93, 50, 6, 1], [.word [3, 1, 2, 3, 5, 4, 3, 2, 6, 5, 4, 3]], 6),
    ([93, 50, 6, 2], [.word [3, 1, 2, 3, 5, 4, 3, 1, 6, 5, 4, 3]], 6),
    ([93, 50, 1, 2], [.word [3, 1, 2, 3, 5, 4, 3, 1, 2, 3, 4, 5]], 6),
    ([93, 4, 6, 1], [.word [5, 4, 3, 1, 6, 5, 4, 3]], 6),
    ([93, 4, 6, 2], [.word [5, 4, 3, 2, 6, 5, 4, 3]], 6),
    ([93, 4, 1, 2], [.word [5, 4, 3, 1, 2, 3, 4, 5]], 6),
    ([93, 6, 1, 2], [.word [5, 4, 6, 5], .d4 2 1 35 50 4], 3),
    ([50, 4, 6, 1], [.word [3, 1, 4, 3]], 6),
    ([50, 4, 6, 2], [.word [3, 2, 4, 3]], 6),
    ([50, 4, 1, 2], [.d4 2 1 35 50 4], 3),
    ([50, 6, 1, 2], [.word [3, 1, 2, 3]], 6),
    ([4, 6, 1, 2], [], 6),
    ([93, 50, 4, 6, 1], [.word [3, 1, 4, 3], .d4 6 2 28 1 93], 6),
    ([93, 50, 4, 6, 2], [.word [3, 2, 4, 3], .d4 6 2 28 1 93], 6),
    ([93, 50, 4, 1, 2], [.word [5, 4, 3, 1, 2, 3, 4, 5], .d4 4 2 3 1 50], 6),
    ([93, 50, 6, 1, 2], [.word [3, 1, 2, 3], .d4 6 2 28 1 93], 6),
    ([93, 4, 6, 1, 2], [.d4 6 2 28 1 93], 6),
    ([50, 4, 6, 1, 2], [.d4 4 2 3 1 50], 6),
    ([93, 50, 4, 6, 1, 2], [.d4 6 4 43 93 50, .d4 6 2 28 1 93], 6)]

theorem d6Walks_check : frameWalkCheck .E7 d6WalkCasc d6WalkTargets d6Walks = true := by
  decide +kernel

theorem d6Walks_frameMoveD6B : ∀ e ∈ d6Walks, ∀ m ∈ e.2.1, frameMoveD6B m = true := by
  intro e he m hm
  have h : (d6Walks.all fun e => e.2.1.all frameMoveD6B) = true := by decide +kernel
  exact List.all_eq_true.1 (List.all_eq_true.1 h e he) m hm

theorem d6WalkCasc_map : d6WalkCasc.map Tag.E7.rootCertificate.root = cascadeD6 := by
  apply List.map_injective_iff.2 List.ofFn_injective
  decide +kernel

theorem d6WalkTargets_map :
    d6WalkTargets.map (List.map Tag.E7.rootCertificate.root) = e4Reps := by
  apply List.map_injective_iff.2 (List.map_injective_iff.2 List.ofFn_injective)
  decide +kernel

theorem d6WalkCasc_framePosD : FramePosD d6WalkCasc := by
  unfold FramePosD
  decide +kernel

end Data

section Final


theorem lamFrameWalk_holds : LamFrameWalkStatement := by
  intro K _ _ _ S hS hne
  rw [← d6WalkCasc_map] at hS
  obtain ⟨Sp, hSp, rfl⟩ := List.sublist_map_iff.1 hS
  have hne' : Sp ≠ [] := by
    rintro rfl
    exact hne rfl
  have horth : (d6WalkCasc.map Tag.E7.rootCertificate.root).Pairwise
      fun σ σ' => iform σ σ' = 0 := by
    rw [d6WalkCasc_map]
    exact cascadeD6_pairwise_iform
  obtain ⟨T, hT, g, hg, he⟩ := frameWalkCheck_soundD (K := K) d6Walks_check
    d6Walks_frameMoveD6B d6WalkCasc_framePosD horth hSp hne'
  have hS' : ∀ σ ∈ Sp.map Tag.E7.rootCertificate.root, σ ∈ perpRoots .E7 := fun σ hσ =>
    cascadeD6_mem_perpRoots σ (d6WalkCasc_map ▸ (hSp.map _).subset hσ)
  have hTe4 : T.map Tag.E7.rootCertificate.root ∈ e4Reps := by
    rw [← d6WalkTargets_map]
    exact List.mem_map_of_mem hT
  have hT' := e4Reps_mem_perpRoots _ hTe4
  refine ⟨T.map Tag.E7.rootCertificate.root, hTe4, psiLev K ⟨g, hg⟩, psiLev_mem_LamG _, ?_⟩
  have hP1 : ((Sp.map Tag.E7.rootCertificate.root).map fun σ => pinnedX .E7 K σ
      ((fun _ => (1 : K)) σ)).prod ∈ rootSpan .E7 K (perpRoots .E7) :=
    classDescent_list_prod_mem_rootSpan _ hS' (fun _ => (1 : K))
  have hP2 : ((T.map Tag.E7.rootCertificate.root).map fun σ => pinnedX .E7 K σ
      ((fun _ => (1 : K)) σ)).prod ∈ rootSpan .E7 K (perpRoots .E7) :=
    classDescent_list_prod_mem_rootSpan _ hT' (fun _ => (1 : K))
  have hconj : (⟨g, hg⟩ : ↥(rootSpan .E7 K (perpRoots .E7))) * ⟨_, hP1⟩ * ⟨g, hg⟩⁻¹ =
      ⟨_, hP2⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact he
  have h1 := congrArg (psiLev K) hconj
  rw [map_mul, map_mul, map_inv, psiLev_list_prod _ hS' (fun _ => (1 : K)),
    psiLev_list_prod _ hT' (fun _ => (1 : K))] at h1
  rw [prod_xm_one_eq_tS, prod_xm_one_eq_tS] at h1
  exact h1

end Final

end CFSG.RankThree.GF2n.Smith81.SK
