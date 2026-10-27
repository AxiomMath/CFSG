module

public import CFSG.LargeExtraspecial.O62Nine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

@[expose] def s16c1_coverPairs : List (ℕ × ℕ) := [
  (3, 13), (7, 11), (16, 32), (17, 36), (18, 42), (21, 33), (20, 37), (24, 34), (26, 40),
  (22, 47), (25, 38), (31, 41), (3, 17), (3, 41), (3, 53), (7, 24), (7, 34), (11, 20),
  (11, 49), (12, 21), (12, 52), (13, 36), (14, 33), (18, 36), (31, 37), (12, 38), (13, 50),
  (14, 22), (17, 40), (7, 49), (11, 34), (18, 38), (25, 33), (14, 20), (16, 47), (20, 38),
  (21, 32), (21, 37), (7, 17), (11, 17), (12, 22), (12, 53), (13, 34), (21, 36), (22, 34),
  (24, 41), (25, 32), (3, 33), (11, 33), (14, 52), (16, 40), (18, 40), (20, 36), (3, 37),
  (14, 17), (17, 37), (26, 42), (3, 25), (3, 49), (3, 57), (7, 18), (7, 33), (7, 40),
  (7, 50), (11, 18), (11, 36), (11, 50), (11, 52), (12, 36), (12, 37), (12, 54), (13, 18),
  (13, 20), (13, 21), (13, 37), (13, 53), (14, 49), (17, 41), (20, 33), (20, 34), (24, 33),
  (24, 42), (25, 40), (26, 34)]

@[expose] def s16c1_goodPair (p : ℕ × ℕ) : Bool :=
  qB true p.1 && qB true p.2 &&
    (npowC (wordC [p.1, p.2]) 3 == one) && (wordC [p.1, p.2] != one)

@[expose] def s16c1_fixes2 (m u v : ℕ) : Bool := act m u == u && act m v == v

@[expose] def s16c1_geoWit (u v : ℕ) : Bool :=
  s16c1_coverPairs.any fun p => s16c1_fixes2 (wordC [p.1, p.2]) u v

@[expose] def s16c1_checkGeo2 : Bool :=
  s16c1_coverPairs.all s16c1_goodPair &&
    (List.range 64).all fun u => (List.range 64).all fun v =>
      u == 0 || v == 0 || u == v || s16c1_geoWit u v

theorem s16c1_checkGeo2_ok : s16c1_checkGeo2 = true := by decide +kernel

@[expose] def s16c1_spanV : List ℕ → List ℕ
  | [] => [0]
  | x :: xs => s16c1_spanV xs ++ (s16c1_spanV xs).map (· ^^^ x)

@[expose] def s16c1_inSpan (bs : List ℕ) (x : ℕ) : Bool := (s16c1_spanV bs).contains x

@[expose] def s16c1_closeStep (gens : List ℕ) (bs : List ℕ) : List ℕ :=
  gens.foldl (fun acc g => bs.foldl
    (fun acc' b => if s16c1_inSpan acc' (act g b) then acc' else act g b :: acc') acc) bs

@[expose] def s16c1_closeV (gens : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, bs => bs
  | n + 1, bs => s16c1_closeV gens n (s16c1_closeStep gens bs)

@[expose] def s16c1_bilin (x y : ℕ) : Bool :=
  (x.testBit 0 && y.testBit 1) ^^ (x.testBit 1 && y.testBit 0) ^^ (x.testBit 2 && y.testBit 3) ^^
    (x.testBit 3 && y.testBit 2) ^^ (x.testBit 4 && y.testBit 5) ^^ (x.testBit 5 && y.testBit 4)

@[expose] def s16c1_irrWords : List (List ℕ) := [[13, 17, 32, 41], [16, 57]]

@[expose] def s16c1_irrGens : List ℕ := s16c1_irrWords.map wordC

@[expose] def s16c1_irrWordsOK : Bool :=
  s16c1_irrWords.all fun w => (w.all fun n => qB true n) && (w.length % 2 == 0) &&
    (act (wordC w) 1 == 1)

@[expose] def s16c1_checkIrr : Bool :=
  s16c1_irrWordsOK && (List.range 64).all fun u =>
    u == 0 || u == 1 ||
      (List.range 64).all fun t =>
        (s16c1_bilin u 1 == false && s16c1_bilin t 1 == true) ||
          s16c1_inSpan (s16c1_closeV s16c1_irrGens 7 [u]) t

theorem s16c1_checkIrr_ok : s16c1_checkIrr = true := by decide +kernel

private theorem s16c1_vec_zero : vec 0 = (0 : V₀) := by
  funext i
  simp [vec, bitZ]

private theorem s16c1_vec_xor (x y : ℕ) : vec (x ^^^ y) = vec x + vec y := by
  funext i
  simp [vec, bitZ_xor]

private theorem s16c1_act_vec {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hg : HasCode g m) (n : ℕ) :
    g (vec n) = vec (act m n) := by
  calc g (vec n) = (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀)).mulVec (vec n) :=
        (LinearMap.toMatrix'_mulVec _ _).symm
    _ = (mat m).mulVec (vec n) := by rw [hg]
    _ = vec (act m n) := (vec_act m n).symm

private theorem s16c1_exists_vec (u : V₀) : ∃ n : ℕ, n < 64 ∧ vec n = u := by
  have h : ∀ u : V₀, ∃ n : Fin 64, vec (n : ℕ) = u := by decide +kernel
  obtain ⟨n, hn⟩ := h u
  exact ⟨n, n.isLt, hn⟩

private theorem s16c1_add_self (x : V₀) : x + x = 0 := by
  rw [← one_smul (ZMod 2) x, ← add_smul, show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem s16c1_neg_eq_self (x : V₀) : -x = x :=
  (eq_neg_of_add_eq_zero_left (s16c1_add_self x)).symm

private theorem s16c1_add_ne_zero {u v : V₀} (huv : u ≠ v) : u + v ≠ 0 := by
  intro h
  apply huv
  calc u = u + 0 := (add_zero u).symm
    _ = u + (v + v) := by rw [s16c1_add_self v]
    _ = (u + v) + v := by rw [add_assoc]
    _ = 0 + v := by rw [h]
    _ = v := zero_add v

private theorem s16c1_ne_add_right {u v : V₀} (hu : u ≠ 0) : u + v ≠ v := by
  intro h
  apply hu
  calc u = u + 0 := (add_zero u).symm
    _ = u + (v + v) := by rw [s16c1_add_self v]
    _ = (u + v) + v := by rw [add_assoc]
    _ = v + v := by rw [h]
    _ = 0 := s16c1_add_self v

private theorem s16c1_ne_add_left {u v : V₀} (hv : v ≠ 0) : u + v ≠ u := by
  intro h
  apply hv
  calc v = 0 + v := (zero_add v).symm
    _ = (u + u) + v := by rw [s16c1_add_self u]
    _ = u + (u + v) := by rw [add_assoc]
    _ = u + u := by rw [h]
    _ = 0 := s16c1_add_self u

private theorem s16c1_one_testBit (k : ℕ) : (1 : ℕ).testBit k = decide (k = 0) := by
  cases k with
  | zero => rfl
  | succ k => simp [Nat.testBit_succ]

private theorem s16c1_bilin_one (x : ℕ) : s16c1_bilin x 1 = x.testBit 1 := by
  simp [s16c1_bilin, s16c1_one_testBit]

private theorem s16c1_bilin_one_iff (m : ℕ) :
    s16c1_bilin m 1 = false ↔ (vec m) 1 = 0 := by
  rw [s16c1_bilin_one]
  cases h : m.testBit 1 <;> simp [vec, bitZ, h]

private theorem s16c1_vec_one_ne_zero : (vec 1 : V₀) ≠ 0 := by decide +kernel

private def s16c1_coordKer : AddSubgroup V₀ where
  carrier := {x | x 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    simp [Pi.add_apply, hx, hy]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp [Pi.neg_apply, hx]

private theorem s16c1_card_V₀ : Nat.card V₀ = 64 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  norm_num [ZMod.card]

private theorem s16c1_card_coordKer : Nat.card s16c1_coordKer = 32 := by
  change ({x : V₀ | x 1 = 0} : Set V₀).ncard = 32
  rw [Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_ofPred]
  decide +kernel

private theorem s16c1_inSpan_iff (bs : List ℕ) (t : ℕ) :
    s16c1_inSpan bs t = true ↔ t ∈ s16c1_spanV bs := by
  rw [s16c1_inSpan]
  exact List.contains_iff_mem

private theorem s16c1_spanV_mem {S : AddSubgroup V₀} (bs : List ℕ)
    (hbs : ∀ b ∈ bs, vec b ∈ S) : ∀ x ∈ s16c1_spanV bs, vec x ∈ S := by
  induction bs with
  | nil =>
    intro x hx
    simp only [s16c1_spanV, List.mem_singleton] at hx
    rw [hx, s16c1_vec_zero]
    exact S.zero_mem
  | cons b bs ih =>
    intro x hx
    simp only [s16c1_spanV, List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨z, hz, rfl⟩
    · exact ih (fun y hy => hbs y (by simp [hy])) x hx
    · rw [s16c1_vec_xor]
      exact add_mem (ih (fun y hy => hbs y (by simp [hy])) z hz) (hbs b (by simp))

private def s16c1_closeAcc (g : ℕ) (acc bs : List ℕ) : List ℕ :=
  bs.foldl (fun acc' b => if s16c1_inSpan acc' (act g b) then acc' else act g b :: acc') acc

private theorem s16c1_closeAcc_mem {S : AddSubgroup V₀} {g : ℕ}
    (hg : ∀ n, vec n ∈ S → vec (act g n) ∈ S) (bs : List ℕ) :
    ∀ acc : List ℕ, (∀ b ∈ acc, vec b ∈ S) → (∀ b ∈ bs, vec b ∈ S) →
      ∀ b ∈ s16c1_closeAcc g acc bs, vec b ∈ S := by
  induction bs with
  | nil => intro acc hacc _ b hb; exact hacc b hb
  | cons b bs ih =>
    intro acc hacc hbs
    have hstep : ∀ c ∈ (if s16c1_inSpan acc (act g b) then acc else act g b :: acc),
        vec c ∈ S := by
      by_cases h : s16c1_inSpan acc (act g b)
      · rw [if_pos h]; exact hacc
      · rw [if_neg h]
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hg b (hbs b (by simp))
        · exact hacc c hc
    exact ih _ hstep (fun c hc => hbs c (by simp [hc]))

private theorem s16c1_closeStep_eq (gens bs : List ℕ) :
    s16c1_closeStep gens bs = gens.foldl (fun acc g => s16c1_closeAcc g acc bs) bs := rfl

private theorem s16c1_closeStep_mem {S : AddSubgroup V₀} {gens : List ℕ}
    (hgen : ∀ g ∈ gens, ∀ n, vec n ∈ S → vec (act g n) ∈ S) (bs : List ℕ)
    (hbs : ∀ b ∈ bs, vec b ∈ S) : ∀ b ∈ s16c1_closeStep gens bs, vec b ∈ S := by
  have key : ∀ (gens : List ℕ), (∀ g ∈ gens, ∀ n, vec n ∈ S → vec (act g n) ∈ S) →
      ∀ acc : List ℕ, (∀ b ∈ acc, vec b ∈ S) →
        ∀ b ∈ gens.foldl (fun acc g => s16c1_closeAcc g acc bs) acc, vec b ∈ S := by
    intro gens
    induction gens with
    | nil => intro _ acc hacc b hb; exact hacc b hb
    | cons g gs ih =>
      intro hgen acc hacc
      exact ih (fun x hx => hgen x (by simp [hx])) (s16c1_closeAcc g acc bs)
        (s16c1_closeAcc_mem (hgen g (by simp)) bs acc hacc hbs)
  rw [s16c1_closeStep_eq]
  exact key gens hgen bs hbs

private theorem s16c1_closeV_mem {S : AddSubgroup V₀} {gens : List ℕ}
    (hgen : ∀ g ∈ gens, ∀ n, vec n ∈ S → vec (act g n) ∈ S) (n : ℕ) (bs : List ℕ)
    (hbs : ∀ b ∈ bs, vec b ∈ S) :
    ∀ b ∈ s16c1_closeV gens n bs, vec b ∈ S := by
  induction n generalizing bs with
  | zero => intro b hb; exact hbs b hb
  | succ n ih =>
    intro b hb
    exact ih (s16c1_closeStep gens bs) (s16c1_closeStep_mem hgen bs hbs) b hb

private theorem s16c1_checkIrr_step {u : ℕ} (hu64 : u < 64) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (t : ℕ) (ht64 : t < 64) :
    (s16c1_bilin u 1 = false ∧ s16c1_bilin t 1 = true) ∨
      s16c1_inSpan (s16c1_closeV s16c1_irrGens 7 [u]) t = true := by
  have h := s16c1_checkIrr_ok
  simp only [s16c1_checkIrr, s16c1_irrWordsOK, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.2 u (List.mem_range.mpr hu64)
  have hu0' : (u == 0) = false := beq_eq_false_iff_ne.mpr hu0
  have hu1' : (u == 1) = false := beq_eq_false_iff_ne.mpr hu1
  rw [hu0', hu1'] at h'
  simp only [Bool.false_or] at h'
  have ht := List.all_eq_true.mp h' t (List.mem_range.mpr ht64)
  rcases Bool.or_eq_true_iff.mp ht with h | h
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact Or.inl ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2⟩
  · exact Or.inr h

private theorem s16c1_irrWord_data {w : List ℕ} (hw : w ∈ s16c1_irrWords) :
    (∀ n ∈ w, qB true n = true) ∧ Even w.length ∧ act (wordC w) 1 = 1 := by
  have h := s16c1_checkIrr_ok
  simp only [s16c1_checkIrr, s16c1_irrWordsOK, Bool.and_eq_true, List.all_eq_true] at h
  have hw' := h.1 w hw
  obtain ⟨⟨hletters, heven⟩, hfix⟩ := hw'
  exact ⟨hletters, even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr (beq_iff_eq.mp heven)),
    beq_iff_eq.mp hfix⟩

theorem s16c1_omega0_geo2 (P : AddSubgroup V₀) (hP : Nat.card P = 4) :
    ∃ g ∈ Ω₀ true, orderOf g = 3 ∧ ∀ p ∈ P, g p = p := by
  classical
  have h0 : (Finset.univ.filter (fun x : P => ¬ (x : V₀) ≠ 0)).card = 1 :=
    Finset.card_eq_one.mpr ⟨0, by ext x; simp⟩
  have huniv : (Finset.univ : Finset P).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hP
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P))
    (p := fun x : P => (x : V₀) ≠ 0)
  rw [huniv, h0] at hsum
  have hlt : 1 < (Finset.univ.filter (fun x : P => (x : V₀) ≠ 0)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  have hu0 : (a : V₀) ≠ 0 := (Finset.mem_filter.mp ha).2
  have hv0 : (b : V₀) ≠ 0 := (Finset.mem_filter.mp hb).2
  have huv : (a : V₀) ≠ (b : V₀) := fun h => hab (Subtype.ext h)
  have huP : (a : V₀) ∈ P := a.2
  have hvP : (b : V₀) ∈ P := b.2
  obtain ⟨nu, hnu64, hnu⟩ := s16c1_exists_vec (a : V₀)
  obtain ⟨nv, hnv64, hnv⟩ := s16c1_exists_vec (b : V₀)
  have hnu0 : nu ≠ 0 := by
    intro h
    exact hu0 (by rw [← hnu, h, s16c1_vec_zero])
  have hnv0 : nv ≠ 0 := by
    intro h
    exact hv0 (by rw [← hnv, h, s16c1_vec_zero])
  have hnuv : nu ≠ nv := by
    intro h
    exact huv (by rw [← hnu, h, hnv])
  have hwit : s16c1_geoWit nu nv = true := by
    have h := s16c1_checkGeo2_ok
    simp only [s16c1_checkGeo2, Bool.and_eq_true, List.all_eq_true] at h
    have h2 := h.2 nu (List.mem_range.mpr hnu64)
    have h2' := h2 nv (List.mem_range.mpr hnv64)
    have hnu0' : (nu == 0) = false := beq_eq_false_iff_ne.mpr hnu0
    have hnv0' : (nv == 0) = false := beq_eq_false_iff_ne.mpr hnv0
    have hnuv' : (nu == nv) = false := beq_eq_false_iff_ne.mpr hnuv
    rw [hnu0', hnv0', hnuv'] at h2'
    simpa using h2'
  obtain ⟨p, hp_mem, hp_fix⟩ := List.any_eq_true.mp hwit
  have hgood : s16c1_goodPair p = true := by
    have h := s16c1_checkGeo2_ok
    simp only [s16c1_checkGeo2, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1 p hp_mem
  rw [s16c1_goodPair] at hgood
  simp only [Bool.and_eq_true_iff] at hgood
  obtain ⟨⟨⟨hq1, hq2⟩, hpow⟩, hne⟩ := hgood
  have hfixu : act (wordC [p.1, p.2]) nu = nu := by
    have h := hp_fix
    simp only [s16c1_fixes2, Bool.and_eq_true] at h
    exact beq_iff_eq.mp h.1
  have hfixv : act (wordC [p.1, p.2]) nv = nv := by
    have h := hp_fix
    simp only [s16c1_fixes2, Bool.and_eq_true] at h
    exact beq_iff_eq.mp h.2
  have hgu : wordProd [p.1, p.2] (a : V₀) = (a : V₀) := by
    rw [← hnu, s16c1_act_vec (hasCode_wordProd [p.1, p.2]) nu, hfixu]
  have hgv : wordProd [p.1, p.2] (b : V₀) = (b : V₀) := by
    rw [← hnv, s16c1_act_vec (hasCode_wordProd [p.1, p.2]) nv, hfixv]
  have hcl_le : AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀) ≤ P := by
    rw [AddSubgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huP
    · exact hvP
  have hcard4fin :
      ({(0 : V₀), (a : V₀), (b : V₀), (a : V₀) + (b : V₀)} : Finset V₀).card = 4 :=
    Finset.card_eq_four.mpr ⟨0, (a : V₀), (b : V₀), (a : V₀) + (b : V₀),
      hu0.symm, hv0.symm, (s16c1_add_ne_zero huv).symm, huv,
      (s16c1_ne_add_left hv0).symm, (s16c1_ne_add_right hu0).symm, rfl⟩
  have hcard4 :
      ({(0 : V₀), (a : V₀), (b : V₀), (a : V₀) + (b : V₀)} : Set V₀).ncard = 4 := by
    rw [Set.ncard_eq_toFinset_card']
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact hcard4fin
  have hcard_ge : Nat.card P ≤
      Nat.card (AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀)) := by
    rw [hP]
    have hsub : ({(0 : V₀), (a : V₀), (b : V₀), (a : V₀) + (b : V₀)} : Set V₀) ⊆
        (AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀) : Set V₀) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact zero_mem _
      · exact AddSubgroup.subset_closure (by simp)
      · exact AddSubgroup.subset_closure (by simp)
      · exact add_mem (AddSubgroup.subset_closure (by simp))
          (AddSubgroup.subset_closure (by simp))
    calc 4 = ({(0 : V₀), (a : V₀), (b : V₀), (a : V₀) + (b : V₀)} : Set V₀).ncard :=
          hcard4.symm
      _ ≤ (AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀) : Set V₀).ncard :=
          Set.ncard_le_ncard hsub
      _ = Nat.card (AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀)) :=
          Nat.card_coe_set_eq _
  have hcl_eq : AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀) = P :=
    AddSubgroup.eq_of_le_of_card_ge hcl_le hcard_ge
  refine ⟨wordProd [p.1, p.2], ?_, ?_, ?_⟩
  · refine (wordProd_mem_omegaGroup_iff (minus := true) ?_).mpr ?_
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hq1
      · rcases List.mem_cons.mp hn with rfl | hn
        · exact hq2
        · exact absurd hn (by simp)
    · exact even_iff_exists_two_mul.mpr ⟨1, by simp⟩
  · have h3 : wordProd [p.1, p.2] ^ 3 = 1 := by
      have h := hasCode_pow (hasCode_wordProd [p.1, p.2]) 3
      rw [beq_iff_eq.mp hpow] at h
      exact h.eq_of_equiv hasCode_one
    have hne1 : wordProd [p.1, p.2] ≠ 1 := by
      intro h
      exact (bne_iff_ne.mp hne) ((eq_iff_of_hasCode (hasCode_wordProd _) hasCode_one
        (wordC_lt _) one_lt).mp h)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 hne1
  · intro q hq
    let F : AddSubgroup V₀ :=
      { carrier := {x | wordProd [p.1, p.2] x = x}
        zero_mem' := by
          show (wordProd [p.1, p.2]) 0 = 0
          exact map_zero _
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy
          simp [map_add, hx, hy]
        neg_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at hx
          show (wordProd [p.1, p.2]) (-x) = -x
          rw [s16c1_neg_eq_self x, hx] }
    have hF : AddSubgroup.closure ({(a : V₀), (b : V₀)} : Set V₀) ≤ F := by
      rw [AddSubgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hgu
      · exact hgv
    rw [← hcl_eq] at hq
    exact hF hq

theorem s16c1_omega0_irr_z0 (S : AddSubgroup V₀)
    (hS : ∀ g ∈ Ω₀ true, g (vec 1) = vec 1 → ∀ s ∈ S, g s ∈ S) :
    Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 32 ∨ Nat.card S = 64 := by
  classical
  have hgen : ∀ g ∈ s16c1_irrGens, ∀ n, vec n ∈ S → vec (act g n) ∈ S := by
    intro g hg n hn
    rw [s16c1_irrGens] at hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hletters, heven, hfix⟩ := s16c1_irrWord_data hw
    have hmem : wordProd w ∈ Ω₀ true := (wordProd_mem_omegaGroup_iff hletters).mpr heven
    have hfixv : wordProd w (vec 1) = vec 1 := by
      rw [s16c1_act_vec (hasCode_wordProd w) 1, hfix]
    have hmemS := hS (wordProd w) hmem hfixv (vec n) hn
    rwa [s16c1_act_vec (hasCode_wordProd w) n] at hmemS
  have hclose : ∀ u, vec u ∈ S → ∀ t,
      s16c1_inSpan (s16c1_closeV s16c1_irrGens 7 [u]) t = true → vec t ∈ S := by
    intro u hu t ht
    have hbs : ∀ b ∈ [u], vec b ∈ S := by
      intro b hb
      rw [List.mem_singleton] at hb
      rw [hb]
      exact hu
    have hcl := s16c1_closeV_mem (S := S) (gens := s16c1_irrGens) hgen 7 [u] hbs
    exact s16c1_spanV_mem (s16c1_closeV s16c1_irrGens 7 [u]) hcl t
      ((s16c1_inSpan_iff _ t).mp ht)
  by_cases ha : ∃ n : ℕ, n < 64 ∧ vec n ∈ S ∧ s16c1_bilin n 1 = true
  · obtain ⟨n, hn64, hnS, hn1⟩ := ha
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp [s16c1_bilin_one, s16c1_one_testBit] at hn1
    have hn1' : n ≠ 1 := by
      rintro rfl
      simp [s16c1_bilin_one, s16c1_one_testBit] at hn1
    have htop : S = ⊤ := by
      refine le_antisymm le_top ?_
      intro x _
      obtain ⟨t, ht64, rfl⟩ := s16c1_exists_vec x
      rcases s16c1_checkIrr_step hn64 hn0 hn1' t ht64 with ⟨hbu, -⟩ | hspan
      · rw [hn1] at hbu
        exact (Bool.false_ne_true hbu.symm).elim
      · exact hclose n hnS t hspan
    rw [htop, AddSubgroup.card_top, s16c1_card_V₀]
    exact Or.inr (Or.inr (Or.inr rfl))
  · have hno : ∀ n, n < 64 → vec n ∈ S → s16c1_bilin n 1 = false := by
      intro n hn64 hnS
      cases hb : s16c1_bilin n 1 with
      | false => rfl
      | true => exact absurd ⟨n, hn64, hnS, hb⟩ ha
    by_cases hcaseb : ∃ n : ℕ, n < 64 ∧ vec n ∈ S ∧ n ≠ 0 ∧ n ≠ 1
    · obtain ⟨n, hn64, hnS, hn0, hn1⟩ := hcaseb
      have hSeq : S = s16c1_coordKer := by
        apply le_antisymm
        · intro s hs
          obtain ⟨m, hm64, rfl⟩ := s16c1_exists_vec s
          show (vec m) 1 = 0
          exact (s16c1_bilin_one_iff m).mp (hno m hm64 hs)
        · intro x hx
          obtain ⟨m, hm64, rfl⟩ := s16c1_exists_vec x
          have hmfalse : s16c1_bilin m 1 = false :=
            (s16c1_bilin_one_iff m).mpr (show (vec m) 1 = 0 from hx)
          rcases s16c1_checkIrr_step hn64 hn0 hn1 m hm64 with ⟨-, hbt⟩ | hspan
          · rw [hmfalse] at hbt
            exact (Bool.false_ne_true hbt).elim
          · exact hclose n hnS m hspan
      rw [hSeq, s16c1_card_coordKer]
      simp
    · have hc : ∀ n, n < 64 → vec n ∈ S → n = 0 ∨ n = 1 := by
        intro n hn64 hnS
        by_contra h
        push Not at h
        exact hcaseb ⟨n, hn64, hnS, h.1, h.2⟩
      have hle : ∀ s ∈ S, s = 0 ∨ s = vec 1 := by
        intro s hs
        obtain ⟨m, hm64, rfl⟩ := s16c1_exists_vec s
        rcases hc m hm64 hs with rfl | rfl
        · exact Or.inl s16c1_vec_zero
        · exact Or.inr rfl
      have hcard_le : Nat.card S ≤ 2 := by
        have hinj : Function.Injective
            (fun s : S => if (s : V₀) = 0 then (0 : Fin 2) else 1) := by
          intro s t hst
          rcases hle s s.2 with hs0 | hs1 <;> rcases hle t t.2 with ht0 | ht1
          · exact Subtype.ext (by rw [hs0, ht0])
          · exfalso
            have h01 : (0 : Fin 2) = 1 := by
              simpa [hs0, ht1, s16c1_vec_one_ne_zero] using hst
            exact absurd h01 (by decide)
          · exfalso
            have h10 : (1 : Fin 2) = 0 := by
              simpa [hs1, ht0, s16c1_vec_one_ne_zero] using hst
            exact absurd h10 (by decide)
          · exact Subtype.ext (by rw [hs1, ht1])
        calc Nat.card S ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
          _ = 2 := by simp
      haveI : Nonempty S := ⟨⟨0, S.zero_mem⟩⟩
      have hpos : 0 < Nat.card S := Finite.card_pos
      have hcards : Nat.card S = 1 ∨ Nat.card S = 2 := by omega
      rcases hcards with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
