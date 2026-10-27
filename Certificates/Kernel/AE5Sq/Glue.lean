module

public import Certificates.Kernel.AE5Sq.Checks
public import CFSG.Certificates.Kernel.WrPackSound

public section

namespace CFSG.KD.AE5Sq

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  Certificates.AE117 Certificates.AE5Sq

theorem finAll_iff' {α : Type} {s : Finset α} {f : α → Bool} :
    finAll s f = true ↔ ∀ x ∈ s, f x = true := by
  simp [finAll]

theorem pins : Ylit = Y60W.map enc ∧ Vlit = Vall 5 ∧ a0lit = enc (a0 ()) ∧ b0lit = enc (b0 ()) ∧
    pilit = enc (allOnes 5) := by
  have h := ae5s_pins
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem pins2 : P60lit = P60W.map lvl ∧ V16lit = Veven 5 ∧ M10lit = M10W.map (·.map enc) ∧
    e10 = 654820258320 := by
  have h := ae5s_pins2
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem hn5 : 5 ≤ 8 := by norm_num

theorem he5 : enc (1 : Wr 5) = 654820258320 := pins2.2.2.2

theorem hp5 : enc (allOnes 5) = pilit := pins.2.2.2.2.symm

theorem mem_chain (σ : Equiv.Perm (Fin 5)) : σ ∈ chainProds chain5 := by
  have hnd := chainOK_nodup [0, 1, 2, 3] chain5 ae5s_chain
  have hc : (chainProds chain5).toFinset.card = Fintype.card (Equiv.Perm (Fin 5)) := by
    rw [List.toFinset_card_of_nodup hnd, chainProds_length, ae5s_chain_len, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have hσ : σ ∈ (chainProds chain5).toFinset := by
    rw [Finset.eq_univ_of_card _ hc]
    exact Finset.mem_univ σ
  exact List.mem_toFinset.1 hσ

theorem mem_P120 (σ : Equiv.Perm (Fin 5)) : lvl σ ∈ P120 := by
  unfold P120
  rw [prods_eq (e := e10) hn5 rfl]
  exact List.mem_map_of_mem (mem_chain σ)

theorem mem_P60 {σ : Equiv.Perm (Fin 5)} (hσ : Equiv.Perm.sign σ = 1) : lvl σ ∈ P60lit := by
  rw [pins2.1]
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨mem_chain σ, decide_eq_true hσ⟩)

theorem mem_Vlit (v : Fin 5 → ZMod 2) : enc (ofVec v) ∈ Vlit := by
  rw [pins.2.1]
  exact mem_Vall v

theorem mem_V16 {v : Fin 5 → ZMod 2} (hv : ∑ i, v i = 0) : enc (ofVec v) ∈ V16lit := by
  rw [pins2.2.1, Veven_eq]
  exact List.mem_map_of_mem (mem_VevenW hv)

theorem memAtL_quad (a b c d : Fin 5) (hn : [a, b, c, d].Nodup) (hs : [a, b, c, d].Pairwise (· ≤ ·))
    (x : Bool) : memAtL [a, b, c, d].toFinset x = memLC a b c d x := by
  unfold memAtL
  rw [(List.toFinset_sort (· ≤ ·) hn).2 hs]

theorem memAtL₀ (x : Bool) : memAtL ({0, 1, 2, 3} : Finset (Fin 5)) x = memLC 0 1 2 3 x := by
  have h : ({0, 1, 2, 3} : Finset (Fin 5)) = ([0, 1, 2, 3] : List (Fin 5)).toFinset := by decide
  rw [h]
  exact memAtL_quad _ _ _ _ (by decide) (by decide) x

theorem memAtL₁ (x : Bool) : memAtL ({0, 1, 2, 4} : Finset (Fin 5)) x = memLC 0 1 2 4 x := by
  have h : ({0, 1, 2, 4} : Finset (Fin 5)) = ([0, 1, 2, 4] : List (Fin 5)).toFinset := by decide
  rw [h]
  exact memAtL_quad _ _ _ _ (by decide) (by decide) x

theorem memAtL₂ (x : Bool) : memAtL ({0, 1, 3, 4} : Finset (Fin 5)) x = memLC 0 1 3 4 x := by
  have h : ({0, 1, 3, 4} : Finset (Fin 5)) = ([0, 1, 3, 4] : List (Fin 5)).toFinset := by decide
  rw [h]
  exact memAtL_quad _ _ _ _ (by decide) (by decide) x

theorem memAtL₃ (x : Bool) : memAtL ({0, 2, 3, 4} : Finset (Fin 5)) x = memLC 0 2 3 4 x := by
  have h : ({0, 2, 3, 4} : Finset (Fin 5)) = ([0, 2, 3, 4] : List (Fin 5)).toFinset := by decide
  rw [h]
  exact memAtL_quad _ _ _ _ (by decide) (by decide) x

theorem memAtL₄ (x : Bool) : memAtL ({1, 2, 3, 4} : Finset (Fin 5)) x = memLC 1 2 3 4 x := by
  have h : ({1, 2, 3, 4} : Finset (Fin 5)) = ([1, 2, 3, 4] : List (Fin 5)).toFinset := by decide
  rw [h]
  exact memAtL_quad _ _ _ _ (by decide) (by decide) x

theorem memAtL_of_alphas {α : Finset (Fin 5)} (hα : α ∈ alphas) :
    ∃ q ∈ alphaQ, ∀ x, memAtL α x = memLC q.1 q.2.1 q.2.2.1 q.2.2.2 x := by
  simp only [alphas, List.mem_cons, List.not_mem_nil, or_false] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 1, 2, 3), by simp [alphaQ], memAtL₀⟩
  · exact ⟨(0, 1, 2, 4), by simp [alphaQ], memAtL₁⟩
  · exact ⟨(0, 1, 3, 4), by simp [alphaQ], memAtL₂⟩
  · exact ⟨(0, 2, 3, 4), by simp [alphaQ], memAtL₃⟩
  · exact ⟨(1, 2, 3, 4), by simp [alphaQ], memAtL₄⟩

theorem memAtL_of_alphaQ {q : Fin 5 × Fin 5 × Fin 5 × Fin 5} (hq : q ∈ alphaQ) :
    ∃ α ∈ alphas, ∀ x, memAtL α x = memLC q.1 q.2.1 q.2.2.1 q.2.2.2 x := by
  simp only [alphaQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨{0, 1, 2, 3}, by simp [alphas], memAtL₀⟩
  · exact ⟨{0, 1, 2, 4}, by simp [alphas], memAtL₁⟩
  · exact ⟨{0, 1, 3, 4}, by simp [alphas], memAtL₂⟩
  · exact ⟨{0, 2, 3, 4}, by simp [alphas], memAtL₃⟩
  · exact ⟨{1, 2, 3, 4}, by simp [alphas], memAtL₄⟩

theorem genOK_k : genOK () = true := by
  change (alphas.all fun α => [true, false].all fun b => genB (memAtL α b)) = true
  rw [List.all_eq_true]
  intro α hα
  obtain ⟨q, hq, hm⟩ := memAtL_of_alphas hα
  simp only [hm]
  exact List.all_eq_true.1 ae5s_gen q hq

theorem pairsOK_k : pairsOK (a5Fin ()) (evenFin5 ()) = true := by
  have hq8 : q8OK 5 654820258320 pilit P60lit V16lit (M10W.map (·.map enc)) = true := by
    rw [← pins2.2.2.1]
    exact ae5s_q8
  unfold pairsOK
  rw [finAll_iff']
  intro τx hτx
  rw [finAll_iff']
  intro vx hvx
  simp only [a5Fin, evenFin5, Finset.mem_filter, Finset.mem_univ, true_and] at hτx hvx
  cases hx4 : ord4Pi ⟨vx, τx⟩
  · rfl
  rw [Bool.not_true, Bool.false_or, finAll_iff']
  intro τy hτy
  rw [finAll_iff']
  intro vy hvy
  simp only [a5Fin, evenFin5, Finset.mem_filter, Finset.mem_univ, true_and] at hτy hvy
  cases hq : q8Pair ⟨vx, τx⟩ ⟨vy, τy⟩
  · rfl
  rw [Bool.not_true, Bool.false_or]
  obtain ⟨m, hm, ⟨a, ha, hax⟩, ⟨a', ha', hay⟩⟩ :=
    q8OK_sound hn5 he5 hp5 hq8 ⟨vx, τx⟩ ⟨vy, τy⟩ (mem_P60 hτx) (mem_V16 hvx) (mem_P60 hτy)
      (mem_V16 hvy) hq
  obtain ⟨r, hr, hmr⟩ := List.mem_flatMap.1 hm
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hmr
  obtain ⟨α, hα, hαm⟩ := memAtL_of_alphaQ hr
  refine List.any_eq_true.2 ⟨α, hα, List.any_eq_true.2 ⟨b, hb, ?_⟩⟩
  simp only [inMem, hαm, Bool.and_eq_true, List.any_eq_true]
  exact ⟨⟨a, ha, hax⟩, ⟨a', ha', hay⟩⟩

theorem sqOK_k : sqOK Finset.univ Finset.univ = true := by
  have hsq : CFSG.KC.WrPack.sqOK 5 pilit ([a0 (), b0 ()].map enc) P120 Vlit (Y60W.map enc) = true := by
    rw [← pins.1]
    have h := ae5s_sq
    rw [pins.2.2.1, pins.2.2.2.1] at h
    exact h
  unfold Certificates.AE5Sq.sqOK
  rw [finAll_iff']
  intro τ _
  rw [finAll_iff']
  intro v _
  dsimp only
  generalize (⟨v, τ⟩ : Wr 5) = c
  rw [Bool.or_eq_true]
  by_cases hcond : (eqPi (c * c * (c * c) * a0 ()) (a0 () * (c * c * (c * c))) &&
      eqPi (c * c * (c * c) * b0 ()) (b0 () * (c * c * (c * c)))) = true
  · right
    rw [Bool.and_eq_true] at hcond
    have hc : ∀ s ∈ [a0 (), b0 ()], eqPi (c * c * (c * c) * s) (s * (c * c * (c * c))) = true := by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hcond.1
      · exact hcond.2
    obtain ⟨y, hy, hyc⟩ := sqOK_sound hn5 hp5 hsq c (mem_P120 c.perm) (mem_Vlit c.vec) hc
    obtain ⟨r, hr, hyr⟩ := List.mem_flatMap.1 hy
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.1 hyr
    obtain ⟨α, hα, hαm⟩ := memAtL_of_alphaQ hr
    have hy4 : ord4Pi y = true := List.all_eq_true.1 ae5s_ord4 y hy
    refine List.any_eq_true.2 ⟨α, hα, List.any_eq_true.2 ⟨b, hb, List.any_eq_true.2 ⟨y, ?_, ?_⟩⟩⟩
    · rw [hαm]
      exact List.mem_of_mem_drop hyb
    · rw [hy4, hyc]
      rfl
  · left
    rw [Bool.not_eq_true']
    simpa using hcond

theorem check_k : Certificates.AE5Sq.check () = true := by
  have h1 : decide ((a0 ()).vec ∈ evenFin5 ()) = true := decide_eq_true (by
    simp only [evenFin5, Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel)
  have h2 : decide ((a0 ()).perm ∈ a5Fin ()) = true := decide_eq_true (by
    simp only [a5Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel)
  have h3 : decide ((b0 ()).vec ∈ evenFin5 ()) = true := decide_eq_true (by
    simp only [evenFin5, Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel)
  have h4 : decide ((b0 ()).perm ∈ a5Fin ()) = true := decide_eq_true (by
    simp only [a5Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel)
  unfold Certificates.AE5Sq.check
  rw [h1, h2, h3, h4, genOK_k, pairsOK_k, sqOK_k]
  rfl

end CFSG.KD.AE5Sq

end
