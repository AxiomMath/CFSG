module

public import CFSG.Quasithin.Background.B3Named
public import CFSG.Quasithin.Background.B3Sign
public import CFSG.Quasithin.Background.B3Class

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] def Dc (n : ℕ) : List Tab := AmL n (n / 2)

@[expose] def DLc (n : ℕ) : List Tab := (Dc n).filter isEvenT

@[expose] def regB (n : ℕ) (K : List Tab) : Bool :=
  (List.range n).all (fun j => K.any (fun t => t.getD 0 0 == j))

@[expose] def isHypT (n : ℕ) (K : List Tab) : Bool :=
  K.all (fun t => (Dc n).contains t) && 2 * K.length == (Dc n).length && !(seteqT K (DLc n))

@[expose] def isE8T (n : ℕ) (K : List Tab) : Bool :=
  n == 8 && K.length == 8 && K.all isEvenT && regB n K

@[expose] def isRepB (n : ℕ) (k : Mod) (K : List Tab) : Bool :=
  (List.range (n / 2)).any (fun i => seteqT K (AmL n (i + 1))) || seteqT K (DLc n) ||
    seteqT K (A0L n) || isHypT n K || (k == Mod.ut0 && isE8T n K)

@[expose] def chkNamed (n : ℕ) : Bool :=
  (List.range (n / 2)).all (fun i => chkGen n (gensAm n (i + 1)) && memD (Dl n) (AmL n (i + 1))) &&
  chkGen n (gensAm n (n / 2)) && chkGen n (gensA0 n) && memD (Dl n) (A0L n) &&
  subOK n (DLc n) && memD (Dl n) (DLc n) && memD (Dl n) (Dc n) &&
  (Dc n).all (fun t => (Tl n).contains t)

@[expose] def chkB (n : ℕ) (k : Mod) (e m : ℕ) : Bool :=
  chkT n e m && chkClassify n k (isRepB n k) && chkNamed n

@[expose] def Hset (n : ℕ) : Set (Subgroup (Gp n)) :=
  {B | ∃ γ : Gp n, ∃ H : Subgroup (Gp n), H ≤ Dsub n ∧ Nat.card (Dsub n) = 2 * Nat.card H ∧
    H ≠ Dsub n ⊓ alternatingGroup (Fin n) ∧ B = cj γ H}

@[expose] def Rset (n : ℕ) : Set (Subgroup (Gp n)) :=
  {A | A ≤ alternatingGroup (Fin n) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧
    Nat.card A = 8 ∧ ∀ i j : Fin n, ∃! a : Gp n, a ∈ A ∧ a i = j}

theorem chkNamed_spec (h : chkNamed n = true) :
    (∀ i < n / 2, chkGen n (gensAm n (i + 1)) = true ∧ memD (Dl n) (AmL n (i + 1)) = true) ∧
    chkGen n (gensAm n (n / 2)) = true ∧ chkGen n (gensA0 n) = true ∧
    memD (Dl n) (A0L n) = true ∧ subOK n (DLc n) = true ∧ memD (Dl n) (DLc n) = true ∧
    memD (Dl n) (Dc n) = true ∧ (∀ t ∈ Dc n, t ∈ Tl n) := by
  simp only [chkNamed, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun i hi => by simpa using h1 i hi, h2, h3, h4, h5, h6, h7, h8⟩

theorem Am_eq {i : ℕ} (hg : chkGen n (gensAm n (i + 1)) = true) :
    Am n (i + 1) = subOf n (AmL n (i + 1)) :=
  closure_eq_of_chkGen hg

theorem subOK_AmL {i : ℕ} (hg : chkGen n (gensAm n (i + 1)) = true) :
    subOK n (AmL n (i + 1)) = true := by
  simp only [chkGen, Bool.and_eq_true] at hg
  exact hg.1.1

theorem A0_eq (hg : chkGen n (gensA0 n) = true) : A0 n = subOf n (A0L n) :=
  closure_eq_of_chkGen hg

theorem subOK_A0L (hg : chkGen n (gensA0 n) = true) : subOK n (A0L n) = true := by
  simp only [chkGen, Bool.and_eq_true] at hg
  exact hg.1.1

theorem Dsub_eq (hg : chkGen n (gensAm n (n / 2)) = true) : Dsub n = subOf n (Dc n) := by
  unfold Dsub Dc
  exact closure_eq_of_chkGen hg

theorem subOK_Dc (hg : chkGen n (gensAm n (n / 2)) = true) : subOK n (Dc n) = true := by
  simp only [chkGen, Bool.and_eq_true] at hg
  exact hg.1.1

theorem subOf_eq_of_iff {L L' : List Tab} (hL : subOK n L = true) (hL' : subOK n L' = true)
    (h : ∀ t, t ∈ L ↔ t ∈ L') : subOf n L = subOf n L' := by
  ext x
  rw [mem_subOf hL, mem_subOf hL', h]

theorem DL_eq (hg : chkGen n (gensAm n (n / 2)) = true) (hDL : subOK n (DLc n) = true) :
    Dsub n ⊓ alternatingGroup (Fin n) = subOf n (DLc n) := by
  have hDc := subOK_Dc hg
  ext x
  rw [Subgroup.mem_inf, Dsub_eq hg, mem_subOf hDc, mem_alternatingGroup_iff, mem_subOf hDL]
  simp [DLc, List.mem_filter]

theorem subOf_memD {T : List Tab} {D : List (List Tab)} (hD : chkEA n T D = true) {L : List Tab}
    (hL : subOK n L = true) (hm : memD D L = true) :
    (∀ x ∈ subOf n L, ∀ y ∈ subOf n L, x * y = y * x) ∧ (∀ x ∈ subOf n L, x * x = 1) ∧
      (∀ x ∈ subOf n L, tab x ∈ T) := by
  obtain ⟨B, hB, hBL⟩ := memD_spec hm
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  obtain ⟨hBok, hBT, hBc, hBs⟩ := hmem B hB
  have heq : subOf n B = subOf n L := subOf_eq_of_iff hBok hL hBL
  rw [← heq]
  refine ⟨subOf_comm hBok hBc, subOf_sq hBok hBs, fun x hx => hBT _ ((mem_subOf hBok).1 hx)⟩

theorem card_Dsub (hg : chkGen n (gensAm n (n / 2)) = true) :
    Nat.card (Dsub n) = (Dc n).length := by
  rw [Dsub_eq hg, card_subOf (subOK_Dc hg)]

theorem isHypT_subOf {C : List Tab} (hCok : subOK n C = true)
    (hg : chkGen n (gensAm n (n / 2)) = true) (hDL : subOK n (DLc n) = true)
    (h : isHypT n C = true) :
    subOf n C ≤ Dsub n ∧ Nat.card (Dsub n) = 2 * Nat.card (subOf n C) ∧
      subOf n C ≠ Dsub n ⊓ alternatingGroup (Fin n) := by
  simp only [isHypT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hDc := subOK_Dc hg
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_subOf hCok] at hx
    rw [Dsub_eq hg, mem_subOf hDc]
    exact h1 _ hx
  · rw [card_Dsub hg, card_subOf hCok]
    exact h2.symm
  · intro heq
    rw [DL_eq hg hDL] at heq
    have h4 : seteqT C (DLc n) = true := by
      simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
      constructor
      · intro t ht
        obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
        have hx : x ∈ subOf n C := (mem_subOf hCok).2 ht
        rw [heq, mem_subOf hDL] at hx
        exact hx
      · intro t ht
        obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hDL).1 t ht)
        have hx : x ∈ subOf n (DLc n) := (mem_subOf hDL).2 ht
        rw [← heq, mem_subOf hCok] at hx
        exact hx
    rw [h4] at h3
    exact absurd h3 (by simp)

theorem exists_isHypT (hT : subOK n (Tl n) = true) (hD : chkEA n (Tl n) (Dl n) = true)
    (hnamed : chkNamed n = true) {H : Subgroup (Gp n)} (hH : H ≤ Dsub n)
    (hcard : Nat.card (Dsub n) = 2 * Nat.card H)
    (hne : H ≠ Dsub n ⊓ alternatingGroup (Fin n)) :
    ∃ C ∈ Dl n, subOK n C = true ∧ isHypT n C = true ∧ H = subOf n C := by
  obtain ⟨-, hg, -, -, hDL, -, hDm, -⟩ := chkNamed_spec hnamed
  have hDc := subOK_Dc hg
  obtain ⟨hDcomm, hDsq, hDT⟩ := subOf_memD hD hDc hDm
  have hHD : ∀ x ∈ H, x ∈ subOf n (Dc n) := fun x hx => by rw [← Dsub_eq hg]; exact hH hx
  obtain ⟨C, hC, hCok, hHC⟩ := exists_mem_D hT hD H (fun x hx => hDT x (hHD x hx))
    (fun a ha b hb => hDcomm a (hHD a ha) b (hHD b hb)) (fun a ha => hDsq a (hHD a ha))
  have hHeq : H = subOf n C := subOf_eq hCok hHC
  refine ⟨C, hC, hCok, ?_, hHeq⟩
  simp only [isHypT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq,
    Bool.not_eq_true']
  refine ⟨⟨fun t ht => ?_, ?_⟩, ?_⟩
  · obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
    have hx : x ∈ H := (hHC x).2 ht
    have := hHD x hx
    rwa [mem_subOf hDc] at this
  · have h1 : Nat.card H = C.length := by rw [hHeq, card_subOf hCok]
    have h2 := card_Dsub hg
    omega
  · by_contra hcon
    have hcon' : seteqT C (DLc n) = true := by simpa using hcon
    apply hne
    rw [hHeq, DL_eq hg hDL]
    exact subOf_congr hCok hDL hcon'

theorem Rset_cj {A : Subgroup (Gp n)} (hA : A ∈ Rset n) (γ : Gp n) : cj γ A ∈ Rset n := by
  obtain ⟨hL, hcomm, hsq, hcard, hreg⟩ := hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_cj] at hx
    have h1 := hL hx
    rw [Equiv.Perm.mem_alternatingGroup] at h1 ⊢
    have hs : Equiv.Perm.sign (γ⁻¹ * x * γ) = Equiv.Perm.sign x := by
      rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_comm (Equiv.Perm.sign γ) (Equiv.Perm.sign x),
        mul_assoc, Int.units_mul_self, mul_one]
    rw [← hs]
    exact h1
  · intro a ha b hb
    rw [mem_cj] at ha hb
    have h1 := congrArg (fun x => γ * x * γ⁻¹) (hcomm _ ha _ hb)
    simpa [mul_assoc] using h1
  · intro a ha
    rw [mem_cj] at ha
    have h1 := congrArg (fun x => γ * x * γ⁻¹) (hsq _ ha)
    simpa [mul_assoc] using h1
  · unfold cj
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact hcard
  · intro i j
    obtain ⟨a', ⟨ha'A, ha'ij⟩, huniq⟩ := hreg (γ⁻¹ i) (γ⁻¹ j)
    refine ⟨γ * a' * γ⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_cj]
      simpa [mul_assoc] using ha'A
    · calc (γ * a' * γ⁻¹) i = γ (a' (γ⁻¹ i)) := rfl
        _ = γ (γ⁻¹ j) := by rw [ha'ij]
        _ = j := by simp
    · rintro b ⟨hbA, hbij⟩
      rw [mem_cj] at hbA
      have h1 : γ⁻¹ * b * γ = a' := by
        apply huniq
        refine ⟨hbA, ?_⟩
        simp [Equiv.Perm.mul_apply, hbij]
      rw [← h1]
      simp [mul_assoc]

theorem isE8T_mem_Rset {C : List Tab} (hCok : subOK n C = true)
    (hcomm : ∀ a ∈ C, ∀ b ∈ C, mulT a b = mulT b a) (hsq : ∀ a ∈ C, mulT a a = idT n)
    (h : isE8T n C = true) : subOf n C ∈ Rset n := by
  classical
  simp only [isE8T, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hn8, hlen⟩, heven⟩, hreg⟩ := h
  subst hn8
  refine ⟨?_, subOf_comm hCok hcomm, subOf_sq hCok hsq, ?_, ?_⟩
  · intro x hx
    rw [mem_subOf hCok] at hx
    rw [mem_alternatingGroup_iff]
    exact heven _ hx
  · rw [card_subOf hCok, hlen]
  · have horb : ∀ j : Fin 8, ∃ a ∈ subOf 8 C, a 0 = j := by
      intro j
      simp only [regB, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at hreg
      obtain ⟨t, ht, htj⟩ := hreg j j.isLt
      obtain ⟨a, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
      refine ⟨a, (mem_subOf hCok).2 ht, ?_⟩
      apply Fin.ext
      have := getD_tab a 0
      simp only [Fin.val_zero] at this
      rw [← this]
      exact htj
    have htrans : ∀ i j : Fin 8, ∃ a ∈ subOf 8 C, a i = j := by
      intro i j
      obtain ⟨ai, hai, haii⟩ := horb i
      obtain ⟨aj, haj, hajj⟩ := horb j
      refine ⟨aj * ai⁻¹, (subOf 8 C).mul_mem haj ((subOf 8 C).inv_mem hai), ?_⟩
      have h1 : ai⁻¹ i = 0 := by rw [← haii]; simp
      simp [Equiv.Perm.mul_apply, h1, hajj]
    intro i j
    have hbij : Function.Bijective (fun a : subOf 8 C => (a : Gp 8) i) := by
      rw [Fintype.bijective_iff_surjective_and_card]
      refine ⟨?_, ?_⟩
      · intro j
        obtain ⟨a, ha, haj⟩ := htrans i j
        exact ⟨⟨a, ha⟩, haj⟩
      · rw [← Nat.card_eq_fintype_card, card_subOf hCok, hlen, Fintype.card_fin]
    obtain ⟨⟨a, ha⟩, haj, huniq⟩ := hbij.existsUnique j
    exact ⟨a, ⟨ha, haj⟩, fun b hb => congrArg Subtype.val (huniq ⟨b, hb.1⟩ hb.2)⟩

theorem isE8T_of_mem_Rset {C : List Tab} (hCok : subOK n C = true) (hn : n = 8)
    {K : Subgroup (Gp n)} (hK : K ∈ Rset n) (hKC : ∀ x : Gp n, x ∈ K ↔ tab x ∈ C) :
    isE8T n C = true := by
  obtain ⟨hL, -, -, hcard, hreg⟩ := hK
  have hKeq : K = subOf n C := subOf_eq hCok hKC
  simp only [isE8T, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hn, ?_⟩, ?_⟩, ?_⟩
  · rw [← card_subOf hCok, ← hKeq]
    exact hcard
  · intro t ht
    obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
    rw [← mem_alternatingGroup_iff]
    exact hL ((hKC x).2 ht)
  · simp only [regB, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq]
    intro j hj
    subst hn
    obtain ⟨a, ⟨haK, haj⟩, -⟩ := hreg 0 ⟨j, hj⟩
    refine ⟨tab a, (hKC a).1 haK, ?_⟩
    have := getD_tab a 0
    simp only [Fin.val_zero] at this
    rw [this, haj]

theorem offenders_caseB (hn5 : 5 ≤ n) (k : Mod) {e m : ℕ} (h : chkB n k e m = true) :
    ∀ A : Subgroup (Gp n), IsOffG n k A ↔
      (A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
        (∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∨ A ∈ Hset n) ∨
      (k = Mod.ut0 ∧ n = 8 ∧ A ∈ Rset n) := by
  simp only [chkB, Bool.and_eq_true] at h
  obtain ⟨⟨hT, hcl⟩, hnamed⟩ := h
  have hT' : subOK n (Tl n) = true := by
    simp only [chkT, Bool.and_eq_true] at hT
    exact hT.1.1.1
  have hEA : chkEA n (Tl n) (Dl n) = true := by
    simp only [chkClassify, Bool.and_eq_true] at hcl
    exact hcl.1.1
  obtain ⟨S, hS⟩ := exists_sylow_of_chkT hT
  obtain ⟨hAm, hg, hgA0, hmA0, hDL, hmDL, hmDc, hDT⟩ := chkNamed_spec hnamed
  have hcls := classify_filter hn5 k hT hcl
  obtain ⟨-, hmem, -⟩ := chkEA_spec hEA
  intro A
  rw [hcls A]
  constructor
  · rintro ⟨C, hC, hrep, γ, rfl⟩
    obtain ⟨hCok, -, hCcomm, hCsq⟩ := hmem C hC
    simp only [isRepB, Bool.or_eq_true, List.any_eq_true, List.mem_range] at hrep
    rcases hrep with ((((⟨i, hi, hCi⟩ | hDLc) | hA0c) | hhyp) | hE8)
    · left; right; right; left
      refine ⟨i, hi, mem_conjClass.2 ⟨γ, ?_⟩⟩
      rw [Am_eq (hAm i hi).1, subOf_congr hCok (subOK_AmL (hAm i hi).1) hCi]
    · left; left
      refine mem_conjClass.2 ⟨γ, ?_⟩
      rw [DL_eq hg hDL, subOf_congr hCok hDL hDLc]
    · left; right; left
      refine mem_conjClass.2 ⟨γ, ?_⟩
      rw [A0_eq hgA0, subOf_congr hCok (subOK_A0L hgA0) hA0c]
    · left; right; right; right
      obtain ⟨h1, h2, h3⟩ := isHypT_subOf hCok hg hDL hhyp
      exact ⟨γ, subOf n C, h1, h2, h3, rfl⟩
    · right
      simp only [Bool.and_eq_true, beq_iff_eq] at hE8
      obtain ⟨hk, hE8⟩ := hE8
      have hn8 : n = 8 := by
        simp only [isE8T, Bool.and_eq_true, beq_iff_eq] at hE8
        exact hE8.1.1.1
      exact ⟨hk, hn8, Rset_cj (isE8T_mem_Rset hCok hCcomm hCsq hE8) γ⟩
  · rintro ((hDL' | hA0' | ⟨i, hi, hAi⟩ | hH) | ⟨hk, hn8, hR⟩)
    · obtain ⟨γ, rfl⟩ := mem_conjClass.1 hDL'
      obtain ⟨B, hB, hBt⟩ := memD_spec hmDL
      obtain ⟨hBok, -⟩ := hmem B hB
      have hset : seteqT B (DLc n) = true := by
        simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
        exact ⟨fun t ht => (hBt t).1 ht, fun t ht => (hBt t).2 ht⟩
      refine ⟨B, hB, by simp [isRepB, hset], γ, ?_⟩
      rw [DL_eq hg hDL]
      exact congrArg (cj γ) (subOf_eq_of_iff hDL hBok (fun t => (hBt t).symm))
    · obtain ⟨γ, rfl⟩ := mem_conjClass.1 hA0'
      obtain ⟨B, hB, hBt⟩ := memD_spec hmA0
      obtain ⟨hBok, -⟩ := hmem B hB
      have hset : seteqT B (A0L n) = true := by
        simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
        exact ⟨fun t ht => (hBt t).1 ht, fun t ht => (hBt t).2 ht⟩
      refine ⟨B, hB, by simp [isRepB, hset], γ, ?_⟩
      rw [A0_eq hgA0]
      exact congrArg (cj γ) (subOf_eq_of_iff (subOK_A0L hgA0) hBok (fun t => (hBt t).symm))
    · obtain ⟨γ, rfl⟩ := mem_conjClass.1 hAi
      obtain ⟨hgi, hmi⟩ := hAm i hi
      obtain ⟨B, hB, hBt⟩ := memD_spec hmi
      obtain ⟨hBok, -⟩ := hmem B hB
      have hset : seteqT B (AmL n (i + 1)) = true := by
        simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
        exact ⟨fun t ht => (hBt t).1 ht, fun t ht => (hBt t).2 ht⟩
      refine ⟨B, hB, ?_, γ, ?_⟩
      · simp only [isRepB, Bool.or_eq_true, List.any_eq_true, List.mem_range]
        left; left; left; left
        exact ⟨i, hi, hset⟩
      · rw [Am_eq hgi]
        exact congrArg (cj γ) (subOf_eq_of_iff (subOK_AmL hgi) hBok (fun t => (hBt t).symm))
    · obtain ⟨γ, H, hH, hcard, hne, rfl⟩ := hH
      obtain ⟨C, hC, hCok, hhyp, hHC⟩ := exists_isHypT hT' hEA hnamed hH hcard hne
      refine ⟨C, hC, ?_, γ, by rw [hHC]⟩
      simp [isRepB, hhyp]
    · have hcomm := hR.2.1
      have hsq := hR.2.2.1
      obtain ⟨γ, hγ⟩ := exists_conj_le_sylow S A (isPGroup_of_sq hsq)
      have hK := Rset_cj hR γ
      obtain ⟨C, hC, hCok, hKC⟩ := exists_mem_D hT' hEA (cj γ A)
        (fun x hx => by
          have := hγ hx
          rw [hS] at this
          exact (mem_subOf hT').1 this) hK.2.1 hK.2.2.1
      have hE8 : isE8T n C = true := isE8T_of_mem_Rset hCok hn8 hK hKC
      refine ⟨C, hC, ?_, γ⁻¹, ?_⟩
      · simp [isRepB, hk, hE8]
      · rw [← subOf_eq hCok hKC, cj_inv_cj]

end CFSG.Quasithin.B3
