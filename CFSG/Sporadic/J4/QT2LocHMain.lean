
module

public import CFSG.Sporadic.J4.QT2LocHProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

structure HCfg (V : Subgroup J) (x d : J) : Prop where
  hVH : V ≤ Hj
  hx : x ∈ Hj
  hd : d ∈ Hj
  hVcard : Nat.card V = 16
  hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  hV2 : ∀ a ∈ V, a * a = 1
  hx5 : orderOf x = 5
  hd2 : d * d = 1
  hVx : ∀ v ∈ V, x * v * x⁻¹ ∈ V
  hVd : ∀ v ∈ V, d * v * d⁻¹ ∈ V
  hfpf : ∀ v ∈ V, x * v = v * x → v = 1
  hxd : (x * d) ^ 3 ∈ V
  hfix : ∃ v ∈ V, v ≠ 1 ∧ (x * d) * v = v * (x * d)

@[expose] def HConcl (V : Subgroup J) (x d : J) : Prop :=
  ∃ y ∈ Eg uJ 11, y ≠ 1 ∧ x * y = y * x ∧ d * y = y * d ∧ ∀ v ∈ V, v * y = y * v

theorem pow_conj_mem {V : Subgroup J} {x : J} (h : ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ∀ n : ℕ, ∀ v ∈ V, x ^ n * v * (x ^ n)⁻¹ ∈ V :=
  pow_conj_mem_gen h

theorem conj_cancel {h a b : J} (e : h * a * h⁻¹ = h * b * h⁻¹) : a = b := by
  have := mul_right_cancel e
  exact mul_left_cancel this

theorem fpf_pow_of {G : Type*} [Group G] {V : Subgroup G} {ξ : G} {k : ℕ}
    (hfpf : ∀ v ∈ V, ξ ^ k * v = v * ξ ^ k → v = 1) : ∀ v ∈ V, ξ * v = v * ξ → v = 1 :=
  fun v hv h => hfpf v hv (Commute.pow_left (show Commute ξ v from h) k).eq

theorem fiveElt_exp_inv (hM : MatFacts) {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) :
    ∃ m : ℕ, (fiveElt ^ k) ^ m = fiveElt := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨3, by rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ, fiveElt_pow hM, one_mul]⟩
  · exact ⟨2, by rw [← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_succ, fiveElt_pow hM, one_mul]⟩
  · exact ⟨4, by
      rw [← pow_mul, show 4 * 4 = 5 * 3 + 1 by norm_num, pow_succ, pow_mul, fiveElt_pow hM,
        one_pow, one_mul]⟩

theorem xi_conj_mem (hM : MatFacts) {V : Subgroup J} {k : ℕ}
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4)
    (hVx : ∀ v ∈ V, fiveElt ^ k * v * (fiveElt ^ k)⁻¹ ∈ V) :
    ∀ v ∈ V, fiveElt * v * fiveElt⁻¹ ∈ V := by
  obtain ⟨m, hm⟩ := fiveElt_exp_inv hM hk
  intro v hv
  have := pow_conj_mem hVx m v hv
  rwa [hm] at this

theorem xi_fpf {V : Subgroup J} {k : ℕ}
    (hfpf : ∀ v ∈ V, fiveElt ^ k * v = v * fiveElt ^ k → v = 1) :
    ∀ v ∈ V, fiveElt * v = v * fiveElt → v = 1 :=
  fpf_pow_of hfpf

theorem span4_mem {S : Set ℕ} (h0 : 0 ∈ S) (hx : ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S)
    (hξ : ∀ c ∈ S, actT xiT c ∈ S) {v : ℕ} (hv : v ∈ S) : ∀ s ∈ span4 v, s ∈ S := by
  intro s hs
  unfold span4 at hs
  simp only [List.mem_map, List.mem_range] at hs
  obtain ⟨m, -, rfl⟩ := hs
  have hw1 := hξ v hv
  have hw2 := hξ _ hw1
  have hw3 := hξ _ hw2
  have hite : ∀ (b : Prop) [Decidable b] (w : ℕ), w ∈ S → (if b then w else 0) ∈ S := by
    intro b _ w hw
    split_ifs <;> assumption
  exact hx _ (hx _ (hx _ (hite _ _ hv) _ (hite _ _ hw1)) _ (hite _ _ hw2)) _ (hite _ _ hw3)

theorem exists_line {Sset : Set ℕ} (h0 : 0 ∈ Sset) (hx : ∀ a ∈ Sset, ∀ b ∈ Sset, a ^^^ b ∈ Sset)
    (hξ : ∀ c ∈ Sset, actT xiT c ∈ Sset) (hfpf : ∀ c ∈ Sset, c ≠ 0 → actT xiT c ≠ c)
    (hlt : ∀ c ∈ Sset, c < 2048) (hcard : Sset.ncard = 16) :
    ∃ S ∈ lines17, ∀ c, c ∈ S ↔ c ∈ Sset := by
  have hfin : Sset.Finite := (Set.finite_Iio 2048).subset fun c hc => hlt c hc
  obtain ⟨c0, hc0, hc0ne⟩ : ∃ c ∈ Sset, c ≠ 0 := by
    by_contra hcon
    have hsub : Sset ⊆ {0} := fun c hc => by
      by_contra hne
      exact hcon ⟨c, hc, hne⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
    rw [hcard] at this
    simp at this
  have hsub := span4_mem h0 hx hξ hc0
  have hfpfL : fpfL (span4 c0) = true := by
    unfold fpfL
    rw [List.all_eq_true]
    intro s hs
    by_cases hs0 : s = 0
    · simp [hs0]
    · have := hfpf s (hsub s hs) hs0
      simp [hs0, this]
  have hlen : (span4 c0).eraseDups.length = 16 := by
    have h := chkLines_true
    unfold chkLines at h
    rw [List.all_eq_true] at h
    have := h c0 (List.mem_range.2 (hlt c0 hc0))
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    rcases this with (h1 | h2) | h3
    · exact absurd h1 hc0ne
    · rw [hfpfL] at h2
      exact absurd h2 (by simp)
    · exact h3
  have hLS : ∀ c, c ∈ (span4 c0).eraseDups → c ∈ Sset := fun c hc =>
    hsub c (List.mem_eraseDups.1 hc)
  have hLeq : (↑(span4 c0).eraseDups.toFinset : Set ℕ) = Sset := by
    have hnd : (span4 c0).eraseDups.Nodup := eraseDups_nodup _ _ le_rfl
    refine Set.eq_of_subset_of_ncard_le (fun c hc => hLS c (by simpa using hc)) ?_ hfin
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen, hcard]
  have hinvL : invL (span4 c0) = true := by
    unfold invL
    rw [List.all_eq_true]
    intro s hs
    have h1 := hξ s (hsub s hs)
    rw [← hLeq] at h1
    have h2 : actT xiT s ∈ span4 c0 := List.mem_eraseDups.1 (by simpa using h1)
    simpa using h2
  refine ⟨((span4 c0).eraseDups).mergeSort, ?_, fun c => ?_⟩
  · unfold lines17
    rw [List.mem_eraseDups, List.mem_map]
    refine ⟨c0, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨List.mem_range.2 (hlt c0 hc0), ?_⟩
    simp [hc0ne, hfpfL, hinvL]
  · rw [List.mem_mergeSort]
    constructor
    · intro hc
      exact hLS c hc
    · intro hc
      rw [← hLeq] at hc
      simpa using hc

theorem duad_props : ∀ c ∈ duadL, c ≠ 0 ∧ c < 2048 := by
  have h := chkDuad_true
  unfold chkDuad at h
  rw [List.all_eq_true] at h
  intro c hc
  simpa using h c hc

theorem hconcl_of_duad (hM : MatFacts) {V : Subgroup J} {x d : J} {tx td : List ℕ}
    (hAx : Acts x tx) (hAd : Acts d td) {c : ℕ} (hcd : c ∈ duadL) (h1 : actT tx c = c)
    (h2 : actT td c = c) (h3 : ∀ v ∈ V, ∃ t, Acts v t ∧ actT t c = c) : HConcl V x d := by
  obtain ⟨hc0, hclt⟩ := duad_props c hcd
  refine ⟨eta uJ 11 c, eta_mem_Eg 11 le_rfl c, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [← eta_zero uJ 11] at h
    exact hc0 (eta_inj hM c hclt 0 (by norm_num) h)
  · have := hAx.2 c hclt
    rw [h1] at this
    calc x * eta uJ 11 c = (x * eta uJ 11 c * x⁻¹) * x := by group
      _ = eta uJ 11 c * x := by rw [this]
  · have := hAd.2 c hclt
    rw [h2] at this
    calc d * eta uJ 11 c = (d * eta uJ 11 c * d⁻¹) * d := by group
      _ = eta uJ 11 c * d := by rw [this]
  · intro v hv
    obtain ⟨t, hAt, ht⟩ := h3 v hv
    have := hAt.2 c hclt
    rw [ht] at this
    calc v * eta uJ 11 c = (v * eta uJ 11 c * v⁻¹) * v := by group
      _ = eta uJ 11 c * v := by rw [this]

theorem caseII_check {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) {d' : List ℕ}
    (hd' : d' ∈ isetT) (hcube : cubeT (compT (xiK k) d') = idT) :
    (∃ c ∈ duadL, actT (xiK k) c = c ∧ actT d' c = c) ∨
      ∀ S ∈ lines17, (∀ s ∈ S, actT d' s ∈ S) →
        ∀ s ∈ S, s = 0 ∨ actT (compT (xiK k) d') s ≠ s := by
  have hkm : k ∈ [1, 2, 3, 4] := by rcases hk with rfl | rfl | rfl | rfl <;> simp
  have h := chkCaseII_true k hkm
  unfold chkCaseII at h
  rw [List.all_eq_true] at h
  have h1 := h d' hd'
  rw [hcube] at h1
  simp only [Bool.or_eq_true, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_self_eq_true, Bool.not_true, Bool.false_eq_true, false_or,
    bne_iff_ne, ne_eq] at h1
  rcases h1 with ⟨c, hc, hc1, hc2⟩ | h4
  · exact Or.inl ⟨c, hc, hc1, hc2⟩
  · right
    intro S hS hinv s hs
    have h5 := h4 S hS
    rcases h5 with h6 | h7
    · exfalso
      have h8 : (S.all fun s => S.contains (actT d' s)) = true := by
        rw [List.all_eq_true]
        intro s' hs'
        simpa using hinv s' hs'
      rw [h8] at h6
      exact absurd h6 (by simp)
    · exact h7 s hs

theorem caseII (hF : J4Facts) {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) {V : Subgroup J}
    {d : J} (hc : HCfg V (fiveElt ^ k) d) (hVE : V ≤ Eg uJ 11) : HConcl V (fiveElt ^ k) d := by
  have hM := hF.mat
  have hξV := xi_conj_mem hM hk hc.hVx
  have hξfpf := xi_fpf hc.hfpf
  obtain ⟨td, hAd⟩ := acts_exists_of_mem_Hj hM d hc.hd
  have htd : td ∈ isetT := iset_complete hM hF hc.hd hc.hd2 hAd
  have hAx := acts_xiK hM k
  have hAxd : Acts (fiveElt ^ k * d) (compT (xiK k) td) := hAx.mul hAd
  have hcube : cubeT (compT (xiK k) td) = idT := by
    have h1 := acts_pow hAxd 3
    have h2 : Acts ((fiveElt ^ k * d) ^ 3) idT := Acts.of_mem_Eg hM (hVE hc.hxd)
    exact Acts.unique hM h1 h2
  have hAξ := acts_xi hM
  obtain ⟨Sset, hSset⟩ : ∃ S : Set ℕ, ∀ c, c ∈ S ↔ c < 2048 ∧ eta uJ 11 c ∈ V :=
    ⟨{c | c < 2048 ∧ eta uJ 11 c ∈ V}, fun c => Iff.rfl⟩
  have h0 : 0 ∈ Sset := (hSset 0).2 ⟨by norm_num, by rw [eta_zero]; exact V.one_mem⟩
  have hx : ∀ a ∈ Sset, ∀ b ∈ Sset, a ^^^ b ∈ Sset := by
    intro a ha b hb
    have ha' := (hSset a).1 ha
    have hb' := (hSset b).1 hb
    refine (hSset _).2 ⟨Nat.xor_lt_two_pow (n := 11) ha'.1 hb'.1, ?_⟩
    rw [eta_xor (elem_uJ hM) (m := 11) le_rfl a b]
    exact V.mul_mem ha'.2 hb'.2
  have hξ : ∀ c ∈ Sset, actT xiT c ∈ Sset := by
    intro c hcS
    have hcS' := (hSset c).1 hcS
    refine (hSset _).2 ⟨by simpa using actT_lt hAξ.1 c, ?_⟩
    have := hξV _ hcS'.2
    rwa [hAξ.2 c hcS'.1] at this
  have hdS : ∀ c ∈ Sset, actT td c ∈ Sset := by
    intro c hcS
    have hcS' := (hSset c).1 hcS
    refine (hSset _).2 ⟨by simpa using actT_lt hAd.1 c, ?_⟩
    have := hc.hVd _ hcS'.2
    rwa [hAd.2 c hcS'.1] at this
  have hfpf : ∀ c ∈ Sset, c ≠ 0 → actT xiT c ≠ c := by
    intro c hcS hc0 heq
    have hcS' := (hSset c).1 hcS
    have h1 := hAξ.2 c hcS'.1
    rw [heq] at h1
    have h2 : fiveElt * eta uJ 11 c = eta uJ 11 c * fiveElt := by
      calc fiveElt * eta uJ 11 c = (fiveElt * eta uJ 11 c * fiveElt⁻¹) * fiveElt := by group
        _ = eta uJ 11 c * fiveElt := by rw [h1]
    have h3 := hξfpf _ hcS'.2 h2
    rw [← eta_zero uJ 11] at h3
    exact hc0 (eta_inj hM c hcS'.1 0 (by norm_num) h3)
  have hlt : ∀ c ∈ Sset, c < 2048 := fun c hcS => ((hSset c).1 hcS).1
  have hcard : Sset.ncard = 16 := by
    have himg : (fun c => eta uJ 11 c) '' Sset = (V : Set J) := by
      ext v
      constructor
      · rintro ⟨c, hcS, rfl⟩
        exact ((hSset c).1 hcS).2
      · intro hv
        obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hVE hv)
        exact ⟨c, (hSset c).2 ⟨hcl, hv⟩, rfl⟩
    have hinj : Set.InjOn (fun c => eta uJ 11 c) Sset := fun a ha b hb e =>
      eta_inj hM a ((hSset a).1 ha).1 b ((hSset b).1 hb).1 e
    rw [← Set.InjOn.ncard_image hinj, himg]
    have := hc.hVcard
    rw [← this]
    exact (Nat.card_coe_set_eq (V : Set J)).symm
  obtain ⟨S, hS, hSeq⟩ := exists_line h0 hx hξ hfpf hlt hcard
  have hdur : ∀ s ∈ S, actT td s ∈ S := fun s hs => (hSeq _).2 (hdS s ((hSeq s).1 hs))
  rcases caseII_check hk htd hcube with ⟨c, hcd, hc1, hc2⟩ | hno
  ·
    exact hconcl_of_duad hM hAx hAd hcd hc1 hc2 fun v hv =>
      ⟨idT, Acts.of_mem_Eg hM (hVE hv), actT_idT (duad_props c hcd).2⟩
  · exfalso
    obtain ⟨v, hv, hv1, hvf⟩ := hc.hfix
    obtain ⟨s0, hs0lt, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hVE hv)
    have hs0S : s0 ∈ S := (hSeq s0).2 ((hSset s0).2 ⟨hs0lt, hv⟩)
    have hs0ne : s0 ≠ 0 := by
      intro h
      apply hv1
      rw [h, eta_zero]
    have h1 := hno S hS hdur s0 hs0S
    rcases h1 with h2 | h3
    · exact hs0ne h2
    · apply h3
      have h4 := hAxd.2 s0 hs0lt
      have h5 : fiveElt ^ k * d * eta uJ 11 s0 * (fiveElt ^ k * d)⁻¹ = eta uJ 11 s0 := by
        calc fiveElt ^ k * d * eta uJ 11 s0 * (fiveElt ^ k * d)⁻¹ =
            ((fiveElt ^ k * d) * eta uJ 11 s0) * (fiveElt ^ k * d)⁻¹ := rfl
          _ = (eta uJ 11 s0 * (fiveElt ^ k * d)) * (fiveElt ^ k * d)⁻¹ := by rw [hvf]
          _ = eta uJ 11 s0 := by group
      rw [h5] at h4
      exact (eta_inj hM s0 hs0lt _ (actT_lt hAxd.1 s0) h4).symm

theorem chkV_props :
    (∀ G ∈ vGroups, G.length = 16 ∧ G.Nodup ∧ ∀ y ∈ G, y = idT ∨ ∀ g ∈ G, g ∈ spanT y) ∧
      ∀ y ∈ isetT, commProd y = true → ∃ G ∈ vGroups, y ∈ G := by
  have h := chkV_true
  unfold chkV at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  refine ⟨fun G hG => ?_, fun y hy hcp => ?_⟩
  · obtain ⟨⟨hlen, hnd⟩, hsp⟩ := h1 G hG
    refine ⟨hlen, hnd, fun y hy => ?_⟩
    rcases hsp y hy with h3 | h3
    · exact Or.inl h3
    · exact Or.inr fun g hg => by simpa using h3 g hg
  · rcases h2 y hy with h3 | h3
    · rw [hcp] at h3
      exact absurd h3 (by simp)
    · exact h3

theorem caseI_check {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) {G : List (List ℕ)}
    (hG : G ∈ vGroups) {d' : List ℕ} (hd' : d' ∈ isetT) (hnorm : ∀ g ∈ G, cjT d' g ∈ G)
    (hcube : cubeT (compT (xiK k) d') ∈ G) :
    ∃ c ∈ duadL, actT (xiK k) c = c ∧ actT d' c = c ∧ ∀ g ∈ G, actT g c = c := by
  have hkm : k ∈ [1, 2, 3, 4] := by rcases hk with rfl | rfl | rfl | rfl <;> simp
  have h := chkCaseI_true k hkm
  unfold chkCaseI at h
  rw [List.all_eq_true] at h
  have h1 := h G hG
  rw [List.all_eq_true] at h1
  have h2 := h1 d' hd'
  have hA : (G.all fun g => G.contains (cjT d' g)) = true := by
    rw [List.all_eq_true]
    intro g hg
    simpa using hnorm g hg
  have hB : G.contains (cubeT (compT (xiK k) d')) = true := by simpa using hcube
  simp only [hA, hB, Bool.not_true, Bool.false_or] at h2
  rw [List.any_eq_true] at h2
  obtain ⟨c, hc, hc'⟩ := h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc'
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc'
  exact ⟨c, hc, hc1, hc2, hc3⟩

theorem acts_xiConj {v : J} {t : List ℕ} (hM : MatFacts) (h : Acts v t) :
    Acts (fiveElt * v * fiveElt⁻¹) (xiConj t) := by
  have hξ := acts_xi hM
  have h4 : Acts fiveElt⁻¹ (powT xiT 4) := by
    have := acts_pow hξ 4
    have e : fiveElt ^ 4 = fiveElt⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, fiveElt_pow hM]
    rwa [e] at this
  have h1 := hξ.mul (h.mul h4)
  rw [← mul_assoc] at h1
  exact h1

theorem subsetProds_mem {TV : Set (List ℕ)} (h1 : idT ∈ TV)
    (hmul : ∀ t ∈ TV, ∀ t' ∈ TV, compT t t' ∈ TV) :
    ∀ c : List (List ℕ), (∀ t ∈ c, t ∈ TV) → ∀ t ∈ subsetProds c, t ∈ TV
  | [], _, t, ht => by
    have hsp : subsetProds [] = [idT] := rfl
    rw [hsp, List.mem_singleton] at ht
    rw [ht]
    exact h1
  | x :: c, hc, t, ht => by
    have hc' : ∀ t ∈ c, t ∈ TV := fun t ht => hc t (List.mem_cons_of_mem _ ht)
    have hx : x ∈ TV := hc x (List.mem_cons_self ..)
    have ih := subsetProds_mem h1 hmul c hc'
    have hsp : subsetProds (x :: c) = subsetProds c ++ (subsetProds c).map (compT x) := rfl
    rw [hsp, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · exact ih t ht
    · exact hmul x hx u (ih u hu)

theorem tables_comm {V : Subgroup J} (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hM : MatFacts)
    {a b : J} (ha : a ∈ V) (hb : b ∈ V) {ta tb : List ℕ} (hAa : Acts a ta) (hAb : Acts b tb) :
    compT ta tb = compT tb ta := by
  have h1 := hAa.mul hAb
  have h2 := hAb.mul hAa
  rw [hVab a ha b hb] at h1
  exact Acts.unique hM h1 h2

theorem caseI (hF : J4Facts) {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) {V : Subgroup J}
    {d : J} (hc : HCfg V (fiveElt ^ k) d) (hVE : V ⊓ Eg uJ 11 = ⊥) :
    HConcl V (fiveElt ^ k) d := by
  have hM := hF.mat
  have hξV := xi_conj_mem hM hk hc.hVx
  have hξfpf := xi_fpf hc.hfpf
  obtain ⟨td, hAd⟩ := acts_exists_of_mem_Hj hM d hc.hd
  have htd : td ∈ isetT := iset_complete hM hF hc.hd hc.hd2 hAd
  have hAx := acts_xiK hM k
  have hAxd : Acts (fiveElt ^ k * d) (compT (xiK k) td) := hAx.mul hAd
  obtain ⟨TV, hTV⟩ : ∃ T : Set (List ℕ), ∀ t, t ∈ T ↔ ∃ v ∈ V, Acts v t :=
    ⟨{t | ∃ v ∈ V, Acts v t}, fun t => Iff.rfl⟩
  have hTV1 : idT ∈ TV := (hTV _).2 ⟨1, V.one_mem, Acts.one⟩
  have hTVmul : ∀ t ∈ TV, ∀ t' ∈ TV, compT t t' ∈ TV := by
    intro t ht t' ht'
    obtain ⟨v, hv, hA⟩ := (hTV t).1 ht
    obtain ⟨v', hv', hA'⟩ := (hTV t').1 ht'
    exact (hTV _).2 ⟨v * v', V.mul_mem hv hv', hA.mul hA'⟩
  have hTVi : ∀ t ∈ TV, t ∈ isetT := by
    intro t ht
    obtain ⟨v, hv, hA⟩ := (hTV t).1 ht
    exact iset_complete hM hF (hc.hVH hv) (hc.hV2 v hv) hA
  obtain ⟨v0, hv0, hv0ne⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 fun v hv => by
      by_contra hne
      exact hcon ⟨v, hv, hne⟩
    have h16 := hc.hVcard
    rw [hbot] at h16
    simp at h16
  obtain ⟨y0, hAy0⟩ := acts_exists_of_mem_Hj hM v0 (hc.hVH hv0)
  have hy0TV : y0 ∈ TV := (hTV _).2 ⟨v0, hv0, hAy0⟩
  have hy0I : y0 ∈ isetT := hTVi _ hy0TV
  have hy0ne : y0 ≠ idT := by
    intro h
    rw [h] at hAy0
    have hmem : v0 ∈ Eg uJ 11 := by
      refine centralizer_Hj hM hF v0 (hc.hVH hv0) fun y hy => ?_
      obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hAy0.2 c hcl
      rw [actT_idT hcl] at this
      calc v0 * eta uJ 11 c = (v0 * eta uJ 11 c * v0⁻¹) * v0 := by group
        _ = eta uJ 11 c * v0 := by rw [this]
    have hmem' : v0 ∈ V ⊓ Eg uJ 11 := ⟨hv0, hmem⟩
    rw [hVE] at hmem'
    exact hv0ne ((Subgroup.mem_bot).1 hmem')
  obtain ⟨w, hw⟩ : ∃ w : ℕ → J, ∀ i, w i = fiveElt ^ i * v0 * (fiveElt ^ i)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hwV : ∀ i, w i ∈ V := fun i => by rw [hw]; exact pow_conj_mem hξV i v0 hv0
  have hwsucc : ∀ i, fiveElt * w i * fiveElt⁻¹ = w (i + 1) := fun i => by
    rw [hw, hw, conj_step]
  have hw0 : w 0 = v0 := by simp [hw]
  have hA0 : Acts (w 0) y0 := by rw [hw0]; exact hAy0
  have hA1 : Acts (w 1) (xiConj y0) := by
    have := acts_xiConj hM hA0
    rwa [hwsucc 0] at this
  have hA2 : Acts (w 2) (xiConj (xiConj y0)) := by
    have := acts_xiConj hM hA1
    rwa [hwsucc 1] at this
  have hA3 : Acts (w 3) (xiConj (xiConj (xiConj y0))) := by
    have := acts_xiConj hM hA2
    rwa [hwsucc 2] at this
  have hA4 : Acts (w 4) (xiConj (xiConj (xiConj (xiConj y0)))) := by
    have := acts_xiConj hM hA3
    rwa [hwsucc 3] at this
  have hN : w 0 * w 1 * w 2 * w 3 * w 4 = 1 :=
    norm_five_eq_one w hw (fiveElt_pow hM) hv0 hc.hVab hξV hξfpf
  have hcp : commProd y0 = true := by
    unfold commProd
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := tables_comm hc.hVab hM (hwV 0) (hwV 1) hA0 hA1
      simpa using this
    · simp only [xiConjs]
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]
        intro i hi
        rw [List.all_eq_true]
        intro j hj
        simp only [List.mem_range] at hi hj
        have hti : ∀ i < 5, ∃ a ∈ V, Acts a ([y0, xiConj y0, xiConj (xiConj y0),
            xiConj (xiConj (xiConj y0)), xiConj (xiConj (xiConj (xiConj y0)))].getD i idT) := by
          intro i hi
          interval_cases i
          · exact ⟨w 0, hwV 0, hA0⟩
          · exact ⟨w 1, hwV 1, hA1⟩
          · exact ⟨w 2, hwV 2, hA2⟩
          · exact ⟨w 3, hwV 3, hA3⟩
          · exact ⟨w 4, hwV 4, hA4⟩
        obtain ⟨a, ha, hAa⟩ := hti i hi
        obtain ⟨b, hb, hAb⟩ := hti j hj
        simpa using tables_comm hc.hVab hM ha hb hAa hAb
      · have h1 := hA0.mul (hA1.mul (hA2.mul (hA3.mul (hA4.mul Acts.one))))
        have e : w 0 * (w 1 * (w 2 * (w 3 * (w 4 * 1)))) = 1 := by
          calc w 0 * (w 1 * (w 2 * (w 3 * (w 4 * 1)))) = w 0 * w 1 * w 2 * w 3 * w 4 := by group
            _ = 1 := hN
        rw [e] at h1
        have := Acts.unique hM h1 Acts.one
        simpa using this
  obtain ⟨hGprops, hGcover⟩ := chkV_props
  obtain ⟨G, hG, hy0G⟩ := hGcover y0 hy0I hcp
  obtain ⟨hGlen, hGnd, hGspan⟩ := hGprops G hG
  have hspan : ∀ g ∈ G, g ∈ spanT y0 := (hGspan y0 hy0G).resolve_left hy0ne
  have hspanTV : ∀ t ∈ spanT y0, t ∈ TV := by
    intro t ht
    unfold spanT at ht
    rw [List.mem_eraseDups] at ht
    refine subsetProds_mem hTV1 hTVmul (xiConjs y0) ?_ t ht
    intro t' ht'
    simp only [xiConjs, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl | rfl | rfl
    · exact hy0TV
    · exact (hTV _).2 ⟨w 1, hwV 1, hA1⟩
    · exact (hTV _).2 ⟨w 2, hwV 2, hA2⟩
    · exact (hTV _).2 ⟨w 3, hwV 3, hA3⟩
    · exact (hTV _).2 ⟨w 4, hwV 4, hA4⟩
  have hGTV : ∀ g ∈ G, g ∈ TV := fun g hg => hspanTV g (hspan g hg)
  let f : V → List ℕ := fun v => Classical.choose (acts_exists_of_mem_Hj hM v.1 (hc.hVH v.2))
  have hf : ∀ v : V, Acts v.1 (f v) := fun v =>
    Classical.choose_spec (acts_exists_of_mem_Hj hM v.1 (hc.hVH v.2))
  have hTVsub : TV ⊆ Set.range f := by
    intro t ht
    obtain ⟨v, hv, hA⟩ := (hTV t).1 ht
    exact ⟨⟨v, hv⟩, Acts.unique hM (hf ⟨v, hv⟩) hA⟩
  have hTVfin : TV.Finite := (Set.finite_range f).subset hTVsub
  have hTVcard : TV.ncard ≤ 16 := by
    calc TV.ncard ≤ (Set.range f).ncard := Set.ncard_le_ncard hTVsub (Set.finite_range f)
      _ = (f '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set V).ncard := Set.ncard_image_le Set.finite_univ
      _ = Nat.card V := Set.ncard_univ V
      _ = 16 := hc.hVcard
  have hGcard : ({t | t ∈ G} : Set (List ℕ)).ncard = 16 := by
    have e : {t | t ∈ G} = ↑G.toFinset := by
      ext t
      simp
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hGnd, hGlen]
  have hTVeq : ({t | t ∈ G} : Set (List ℕ)) = TV :=
    Set.eq_of_subset_of_ncard_le (fun g hg => hGTV g hg) (by rw [hGcard]; exact hTVcard) hTVfin
  have hTVG : ∀ t ∈ TV, t ∈ G := fun t ht => by
    rw [← hTVeq] at ht
    exact ht
  have hnorm : ∀ g ∈ G, cjT td g ∈ G := by
    intro g hg
    obtain ⟨v, hv, hA⟩ := (hTV g).1 (hGTV g hg)
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hc.hd2
    have hAdi : Acts d⁻¹ td := by rw [hdinv]; exact hAd
    have h1 := hAd.mul (hA.mul hAdi)
    rw [← mul_assoc] at h1
    exact hTVG _ ((hTV _).2 ⟨d * v * d⁻¹, hc.hVd v hv, h1⟩)
  have hcubeG : cubeT (compT (xiK k) td) ∈ G :=
    hTVG _ ((hTV _).2 ⟨(fiveElt ^ k * d) ^ 3, hc.hxd, acts_pow hAxd 3⟩)
  obtain ⟨c, hcd, hc1, hc2, hc3⟩ := caseI_check hk hG htd hnorm hcubeG
  refine hconcl_of_duad hM hAx hAd hcd hc1 hc2 fun v hv => ?_
  have hvTV : f ⟨v, hv⟩ ∈ TV := (hTV _).2 ⟨v, hv, hf ⟨v, hv⟩⟩
  exact ⟨f ⟨v, hv⟩, hf ⟨v, hv⟩, hc3 _ (hTVG _ hvTV)⟩

theorem hpart_inner (hF : J4Facts) {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4)
    {V : Subgroup J} {d : J} (hc : HCfg V (fiveElt ^ k) d) : HConcl V (fiveElt ^ k) d := by
  have hM := hF.mat
  have hdich := eq_bot_or_eq_of_fpf (fiveElt ^ k) hc.hx5 V (V ⊓ Eg uJ 11) hc.hVcard inf_le_left
    (fun w hw => ⟨hc.hVx w hw.1, Hj_normalizes_Eg hM _ hc.hx w hw.2⟩)
    (fun w hw h => hc.hfpf w hw.1 h)
  rcases hdich with hbot | hall
  · exact caseI hF hk hc hbot
  · exact caseII hF hk hc (inf_eq_left.1 hall)

theorem HCfg.conj {V : Subgroup J} {x d : J} (hc : HCfg V x d) {h : J} (hh : h ∈ Hj) :
    HCfg (conjSub h⁻¹ V) (h⁻¹ * x * h) (h⁻¹ * d * h) := by
  have hmem : ∀ y, y ∈ conjSub h⁻¹ V ↔ h * y * h⁻¹ ∈ V := fun y => by
    rw [mem_conjSub]
    simp
  have hH : ∀ y, y ∈ Hj → h⁻¹ * y * h ∈ Hj := fun y hy =>
    Hj.mul_mem (Hj.mul_mem (Hj.inv_mem hh) hy) hh
  refine ⟨?_, hH _ hc.hx, hH _ hc.hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have := hc.hVH ((hmem y).1 hy)
    have e : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [e]
    exact hH _ this
  · exact (card_conjSub _ _).trans hc.hVcard
  · intro a ha b hb
    have h1 := hc.hVab _ ((hmem a).1 ha) _ ((hmem b).1 hb)
    apply conj_cancel (h := h)
    calc h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      _ = (h * b * h⁻¹) * (h * a * h⁻¹) := h1
      _ = h * (b * a) * h⁻¹ := by group
  · intro a ha
    have h1 := hc.hV2 _ ((hmem a).1 ha)
    apply conj_cancel (h := h)
    calc h * (a * a) * h⁻¹ = (h * a * h⁻¹) * (h * a * h⁻¹) := by group
      _ = 1 := h1
      _ = h * 1 * h⁻¹ := by group
  · have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective x
    rw [← hc.hx5, ← this]
    simp
  · have e : (h⁻¹ * d * h) * (h⁻¹ * d * h) = h⁻¹ * (d * d) * h := by group
    rw [e, hc.hd2]
    group
  · intro v hv
    rw [hmem] at hv ⊢
    have := hc.hVx _ hv
    have e : h * (h⁻¹ * x * h * v * (h⁻¹ * x * h)⁻¹) * h⁻¹ = x * (h * v * h⁻¹) * x⁻¹ := by group
    rwa [e]
  · intro v hv
    rw [hmem] at hv ⊢
    have := hc.hVd _ hv
    have e : h * (h⁻¹ * d * h * v * (h⁻¹ * d * h)⁻¹) * h⁻¹ = d * (h * v * h⁻¹) * d⁻¹ := by group
    rwa [e]
  · intro v hv hcomm
    rw [hmem] at hv
    have h1 : x * (h * v * h⁻¹) = (h * v * h⁻¹) * x := by
      calc x * (h * v * h⁻¹) = h * ((h⁻¹ * x * h) * v) * h⁻¹ := by group
        _ = h * (v * (h⁻¹ * x * h)) * h⁻¹ := by rw [hcomm]
        _ = (h * v * h⁻¹) * x := by group
    have := hc.hfpf _ hv h1
    apply conj_cancel (h := h)
    rw [this]
    group
  · rw [hmem]
    have e : h * ((h⁻¹ * x * h) * (h⁻¹ * d * h)) ^ 3 * h⁻¹ = (x * d) ^ 3 := by
      have : (h⁻¹ * x * h) * (h⁻¹ * d * h) = h⁻¹ * (x * d) * h := by group
      rw [this]
      have := conj_pow (a := h⁻¹) (b := x * d) (i := 3)
      simp only [inv_inv] at this
      rw [this]
      group
    have e2 : h * ((h⁻¹ * x * h) * (h⁻¹ * d * h)) ^ 3 * h⁻¹ ∈ V := by
      rw [e]
      exact hc.hxd
    exact e2
  · obtain ⟨v, hv, hv1, hvf⟩ := hc.hfix
    refine ⟨h⁻¹ * v * h, by simpa using mem_conjSub_of_mem h⁻¹ hv, ?_, ?_⟩
    · intro h1
      exact hv1 (eq_one_of_conj_eq_one h1)
    · have e1 : (h⁻¹ * x * h) * (h⁻¹ * d * h) * (h⁻¹ * v * h) = h⁻¹ * ((x * d) * v) * h := by
        group
      have e2 : (h⁻¹ * v * h) * ((h⁻¹ * x * h) * (h⁻¹ * d * h)) = h⁻¹ * (v * (x * d)) * h := by
        group
      rw [e1, e2, hvf]

theorem HConcl.of_conj {V : Subgroup J} {x d h : J} (hh : h ∈ Hj) (hM : MatFacts)
    (hc : HConcl (conjSub h⁻¹ V) (h⁻¹ * x * h) (h⁻¹ * d * h)) : HConcl V x d := by
  obtain ⟨y, hyE, hy1, hxy, hdy, hVy⟩ := hc
  have hmem : ∀ z, z ∈ conjSub h⁻¹ V ↔ h * z * h⁻¹ ∈ V := fun z => by
    rw [mem_conjSub]
    simp
  refine ⟨h * y * h⁻¹, Hj_normalizes_Eg hM h hh y hyE, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hy1
    apply conj_cancel (h := h)
    rw [h1]
    group
  · calc x * (h * y * h⁻¹) = h * ((h⁻¹ * x * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * x * h)) * h⁻¹ := by rw [hxy]
      _ = (h * y * h⁻¹) * x := by group
  · calc d * (h * y * h⁻¹) = h * ((h⁻¹ * d * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * d * h)) * h⁻¹ := by rw [hdy]
      _ = (h * y * h⁻¹) * d := by group
  · intro v hv
    have hv' : h⁻¹ * v * h ∈ conjSub h⁻¹ V := by simpa using mem_conjSub_of_mem h⁻¹ hv
    have := hVy _ hv'
    calc v * (h * y * h⁻¹) = h * ((h⁻¹ * v * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * v * h)) * h⁻¹ := by rw [this]
      _ = (h * y * h⁻¹) * v := by group

theorem hpart_core (hF : J4Facts) {V : Subgroup J} {x d : J} (hc : HCfg V x d) : HConcl V x d := by
  have hM := hF.mat
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h, k, hk⟩ := exists_conj_pow_of_card (G := ↥Hj) (p := 5)
    (card_Hj_factorization_five hF) (x := ⟨fiveElt, fiveElt_mem_Hj⟩) (y := ⟨x, hc.hx⟩)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_fiveElt hM)
    (by rw [Subgroup.orderOf_mk]; exact hc.hx5)
  have hk' : x = (h : J) * fiveElt ^ k * (h : J)⁻¹ := by
    have := congrArg Subtype.val hk
    simpa using this
  have hk5 : fiveElt ^ k = fiveElt ^ (k % 5) := by
    conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul, fiveElt_pow hM, one_pow, one_mul]
  have hkne : k % 5 ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk5
    have hx1 : x = 1 := by
      rw [hk', hk5]
      group
    have := hc.hx5
    rw [hx1, orderOf_one] at this
    omega
  have hkr : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  have hcj := hc.conj h.2
  have e : (h : J)⁻¹ * x * (h : J) = fiveElt ^ (k % 5) := by
    rw [hk', ← hk5]
    group
  rw [e] at hcj
  have h2 := hpart_inner hF hkr hcj
  rw [← e] at h2
  exact HConcl.of_conj h.2 hM h2

end CFSG.Sporadic.J4.QT2
