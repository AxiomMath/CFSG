module

public import CFSG.Quasithin.Background.B3Off

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem cj_mul (a b : Gp n) (A : Subgroup (Gp n)) : cj (a * b) A = cj a (cj b A) := by
  ext x
  simp only [mem_cj]
  simp [mul_assoc]

@[expose] def conjT (g : Tab) (A : List Tab) : List Tab := A.map (cjT g)

theorem cjT_tab (γ y : Gp n) : cjT (tab γ) (tab y) = tab (γ * y * γ⁻¹) := by
  unfold cjT
  rw [← tab_mul, ← tab_inv, ← tab_mul]

theorem cj_subOf_eq {L K : List Tab} (hL : subOK n L = true) (hK : subOK n K = true) {g : Tab}
    (hg : isTab n g = true) (h : seteqT (conjT g L) K = true) :
    ∃ γ : Gp n, cj γ (subOf n L) = subOf n K := by
  obtain ⟨γ, rfl⟩ := exists_tab_eq hg
  refine ⟨γ, ?_⟩
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, conjT,
    List.mem_map] at h
  obtain ⟨h1, h2⟩ := h
  ext x
  rw [mem_cj, mem_subOf hL, mem_subOf hK]
  constructor
  · intro hx
    have := h1 (cjT (tab γ) (tab (γ⁻¹ * x * γ))) ⟨_, hx, rfl⟩
    rw [cjT_tab] at this
    simpa [mul_assoc] using this
  · intro hx
    obtain ⟨l, hl, hlx⟩ := h2 _ hx
    obtain ⟨y, rfl⟩ := exists_tab_eq ((subOK_spec hL).1 l hl)
    rw [cjT_tab] at hlx
    have h3 := tab_injective hlx
    rw [← h3]
    simpa [mul_assoc] using hl

@[expose] def chkT (n e m : ℕ) : Bool :=
  subOK n (Tl n) && (Tl n).length == 2 ^ e && n.factorial == 2 ^ e * m && m % 2 == 1

theorem exists_sylow_of_chkT {e m : ℕ} (h : chkT n e m = true) :
    ∃ S : Sylow 2 (Gp n), (S : Subgroup (Gp n)) = subOf n (Tl n) := by
  simp only [chkT, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hT, hc⟩, hf⟩, hm⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (subOf n (Tl n)) = 2 ^ e := by rw [card_subOf hT, hc]
  have hp : IsPGroup 2 (subOf n (Tl n)) := IsPGroup.of_card hcard
  refine ⟨hp.toSylow ?_, rfl⟩
  have h1 := Subgroup.card_mul_index (subOf n (Tl n))
  rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin, hf] at h1
  have h2 : (subOf n (Tl n)).index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [h2]
  omega

theorem isPGroup_of_sq {A : Subgroup (Gp n)} (h : ∀ a ∈ A, a * a = 1) : IsPGroup 2 A := by
  intro x
  refine ⟨1, ?_⟩
  have := h x x.2
  apply Subtype.ext
  simpa [pow_two] using this

theorem cj_inv_cj (g : Gp n) (A : Subgroup (Gp n)) : cj g⁻¹ (cj g A) = A := by
  have := cj_cj_inv g⁻¹ A
  simpa using this

theorem classification (hn : 5 ≤ n) (k : Mod) {D reps : List (List Tab)} {S : Sylow 2 (Gp n)}
    (hS : (S : Subgroup (Gp n)) = subOf n (Tl n)) (hT : subOK n (Tl n) = true)
    (hD : chkEA n (Tl n) D = true)
    (hreps : ∀ L ∈ reps, L ∈ D ∧ offOK n k D L = true)
    (hcover : ∀ K ∈ D, offOK n k D K = true →
      ∃ L ∈ reps, ∃ g, isTab n g = true ∧ seteqT (conjT g L) K = true) :
    ∀ A : Subgroup (Gp n), IsOffG n k A ↔ ∃ L ∈ reps, ∃ γ : Gp n, A = cj γ (subOf n L) := by
  intro A
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  constructor
  · intro hA
    have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have h1 := hA.2.2.1.1 (Mod.act n k a) (Subgroup.mem_map_of_mem _ ha) (Mod.act n k b)
        (Subgroup.mem_map_of_mem _ hb)
      apply act_injective hn k
      simpa [map_mul] using h1
    have hsq : ∀ a ∈ A, a * a = 1 := by
      intro a ha
      have h1 := hA.2.2.1.2 (Mod.act n k a) (Subgroup.mem_map_of_mem _ ha)
      apply act_injective hn k
      rw [map_mul, map_one]
      simpa [pow_two] using h1
    obtain ⟨γ, hγ⟩ := exists_conj_le_sylow S A (isPGroup_of_sq hsq)
    have hKcomm : ∀ a ∈ cj γ A, ∀ b ∈ cj γ A, a * b = b * a := by
      intro a ha b hb
      rw [mem_cj] at ha hb
      have h1 := congrArg (fun x => γ * x * γ⁻¹) (hcomm _ ha _ hb)
      simpa [mul_assoc] using h1
    have hKsq : ∀ a ∈ cj γ A, a * a = 1 := by
      intro a ha
      rw [mem_cj] at ha
      have h1 := congrArg (fun x => γ * x * γ⁻¹) (hsq _ ha)
      simpa [mul_assoc] using h1
    have hKoff : IsOffG n k (cj γ A) := hA.cj γ
    obtain ⟨C, hC, hCok, hKC⟩ := exists_mem_D hT hD (cj γ A)
      (fun x hx => by
        have := hγ hx
        rw [hS] at this
        exact (mem_subOf hT).1 this) hKcomm hKsq
    have hKeq : cj γ A = subOf n C := subOf_eq hCok hKC
    have hoff : offOK n k D C = true :=
      (isOffG_iff_offOK hn k hT hD hC).1 (by rw [← hKeq]; exact hKoff)
    obtain ⟨L, hL, g, hg, hseteq⟩ := hcover C hC hoff
    obtain ⟨δ, hδ⟩ := cj_subOf_eq (hmem L (hreps L hL).1).1 hCok hg hseteq
    refine ⟨L, hL, γ⁻¹ * δ, ?_⟩
    rw [cj_mul, hδ, ← hKeq, cj_inv_cj]
  · rintro ⟨L, hL, γ, rfl⟩
    exact ((isOffG_iff_offOK hn k hT hD (hreps L hL).1).2 (hreps L hL).2).cj γ

@[expose] def lexLE : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a == b then lexLE as bs else false

@[expose] def canonT (A : List Tab) : List Tab := A.mergeSort lexLE

@[expose] def sgensOf (n : ℕ) : List Tab :=
  (List.range (n - 1)).map (fun i =>
    (List.range n).map (fun j => if j == i then i + 1 else if j == i + 1 then i else j))

@[expose] def classStep (sgens : List Tab)
    (st : Std.HashMap (List Tab) Tab × List (List Tab × Tab)) (e : List Tab × Tab) :
    Std.HashMap (List Tab) Tab × List (List Tab × Tab) :=
  sgens.foldl (fun (acc : Std.HashMap (List Tab) Tab × List (List Tab × Tab)) s =>
    let K' := canonT (conjT s e.1)
    if acc.1.contains K' then acc
    else (acc.1.insert K' (mulT s e.2), (K', mulT s e.2) :: acc.2)) st

@[expose] def classLoop (sgens : List Tab) :
    ℕ → Std.HashMap (List Tab) Tab → List (List Tab × Tab) → Std.HashMap (List Tab) Tab
  | 0, m, _ => m
  | fuel + 1, m, fr =>
      if fr.isEmpty then m
      else
        let st := fr.foldl (classStep sgens) (m, [])
        classLoop sgens fuel st.1 st.2

@[expose] def classMap (n : ℕ) (sgens : List Tab) (L : List Tab) : Std.HashMap (List Tab) Tab :=
  classLoop sgens 400 (Std.HashMap.emptyWithCapacity.insert (canonT L) (idT n)) [(canonT L, idT n)]

@[expose] def mkDF (n : ℕ) (k : Mod) (D : List (List Tab)) : List (List Tab × ℕ) :=
  D.map (fun B => (B, Fval n k B))

@[expose] def offP (DF : List (List Tab × ℕ)) (p : List Tab × ℕ) : Bool :=
  !(p.1.length == 1) && DF.all (fun q => !(q.1.all (fun t => p.1.contains t)) || decide (q.2 ≤ p.2))

theorem offP_mkDF (n : ℕ) (k : Mod) (D : List (List Tab)) (A : List Tab) :
    offP (mkDF n k D) (A, Fval n k A) = offOK n k D A := by
  simp [offP, mkDF, offOK, List.all_map, Function.comp_def]

@[expose] def coverOK (n : ℕ) (k : Mod) (D reps : List (List Tab)) : Bool :=
  let DF := mkDF n k D
  let RM := reps.map (fun L => (L, classMap n (sgensOf n) L))
  DF.all (fun p => !(offP DF p) ||
    RM.any (fun q => match q.2.get? (canonT p.1) with
      | some g => isTab n g && seteqT (conjT g q.1) p.1
      | none => false))

theorem coverOK_spec {k : Mod} {D reps : List (List Tab)} (h : coverOK n k D reps = true) :
    ∀ K ∈ D, offOK n k D K = true →
      ∃ L ∈ reps, ∃ g, isTab n g = true ∧ seteqT (conjT g L) K = true := by
  intro K hK hoff
  unfold coverOK at h
  simp only [List.all_eq_true] at h
  have h1 := h (K, Fval n k K) (List.mem_map.2 ⟨K, hK, rfl⟩)
  rw [offP_mkDF, hoff] at h1
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_map] at h1
  obtain ⟨q, ⟨L, hL, rfl⟩, hq⟩ := h1
  refine ⟨L, hL, ?_⟩
  cases hg : (classMap n (sgensOf n) L).get? (canonT K) with
  | none => rw [hg] at hq; simp at hq
  | some g =>
    rw [hg] at hq
    simp only [Bool.and_eq_true] at hq
    exact ⟨g, hq.1, hq.2⟩

@[expose] def chkClassify (n : ℕ) (k : Mod) (pr : List Tab → Bool) : Bool :=
  let DF := mkDF n k (Dl n)
  chkEA n (Tl n) (Dl n) &&
  ((Dl n).filter pr).all (fun L => offP DF (L, Fval n k L)) &&
  coverOK n k (Dl n) ((Dl n).filter pr)

theorem classify_filter (hn : 5 ≤ n) (k : Mod) {pr : List Tab → Bool} {e m : ℕ}
    (hT : chkT n e m = true) (h : chkClassify n k pr = true) :
    ∀ A : Subgroup (Gp n), IsOffG n k A ↔
      ∃ C ∈ Dl n, pr C = true ∧ ∃ γ : Gp n, A = cj γ (subOf n C) := by
  simp only [chkClassify, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hEA, hoff⟩, hcov⟩ := h
  obtain ⟨S, hS⟩ := exists_sylow_of_chkT hT
  have hT' : subOK n (Tl n) = true := by
    simp only [chkT, Bool.and_eq_true] at hT
    exact hT.1.1.1
  have hcls := classification hn k hS hT' hEA (reps := (Dl n).filter pr)
    (fun L hL => by
      refine ⟨(List.mem_filter.1 hL).1, ?_⟩
      rw [← offP_mkDF]
      exact hoff L hL)
    (coverOK_spec hcov)
  intro A
  rw [hcls A]
  constructor
  · rintro ⟨L, hL, γ, hA⟩
    obtain ⟨hLD, hLp⟩ := List.mem_filter.1 hL
    exact ⟨L, hLD, hLp, γ, hA⟩
  · rintro ⟨C, hC, hpC, γ, hA⟩
    exact ⟨C, List.mem_filter.2 ⟨hC, hpC⟩, γ, hA⟩

end CFSG.Quasithin.B3
