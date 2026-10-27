module

public import Certificates.Certificate7191
public import CFSG.Quasithin.H13.L32NS7Model

public section

namespace CFSG.Quasithin.H13.O3Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert

theorem o3Check_eq : o3Check = true :=
  Certificates.certificate7191

theorem o3Check_parts :
    basicB = true ∧ h1B = true ∧ ∀ c ∈ [0, 1], pB c = true ∧ wB c = true ∧ invB c = true ∧
      ovB c = true ∧ kB c = true ∧ cenB c = true := by
  have h := o3Check_eq
  simp only [o3Check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun c hc => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, d⟩, e⟩, f⟩, g⟩ := h3 c hc
  exact ⟨a, b, d, e, f, g⟩

theorem q3_eq : q3 = q5n := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem o3G_cols : o3G = [colsOf (o3l0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (o3l1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (o3l2 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (o3r0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (o3r1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (o3r2 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem fG_cols : fG = colsOf (o3field : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  decide +kernel

theorem sG_cols : sG = colsOf (o3swap : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  decide +kernel

theorem gens_unit : ∀ c ∈ o3G ++ [fG, sG], ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  rw [o3G_cols, fG_cols, sG_cols]
  intro c hc
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨o3l0, (dec8_colsOf _).symm⟩
  · exact ⟨o3l1, (dec8_colsOf _).symm⟩
  · exact ⟨o3l2, (dec8_colsOf _).symm⟩
  · exact ⟨o3r0, (dec8_colsOf _).symm⟩
  · exact ⟨o3r1, (dec8_colsOf _).symm⟩
  · exact ⟨o3r2, (dec8_colsOf _).symm⟩
  · exact ⟨o3field, (dec8_colsOf _).symm⟩
  · exact ⟨o3swap, (dec8_colsOf _).symm⟩

theorem omega3_eq : omega3 = genSub o3G := by
  show Subgroup.closure _ = genSub o3G
  unfold genSub
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, o3G_cols,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h)))))

theorem omega3F_eq : omega3F = genSub (o3G ++ [fG]) := by
  show Subgroup.closure _ = genSub (o3G ++ [fG])
  unfold genSub
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, o3G_cols, fG_cols,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · rintro (h | h | h | h | h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h))))))

theorem omega3N_eq : omega3N = genSub (o3G ++ [fG, sG]) := by
  show Subgroup.closure _ = genSub (o3G ++ [fG, sG])
  unfold genSub
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, o3G_cols, fG_cols,
    sG_cols, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · rintro (h | h | h | h | h | h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h)))))))

theorem basic_spec :
    (subB o3G om3E = true ∧ om3E.length = 3600) ∧
    (subB (o3G ++ [fG]) om3FE = true ∧ om3FE.length = 7200) ∧
    (subB (o3G ++ [fG, sG]) omNE = true ∧ omNE.length = 14400) ∧
    (subB (o3G ++ [sG]) h1E = true ∧ h1E.length = 7200) ∧
    (subB (o3G ++ [sfG]) h2E = true ∧ h2E.length = 7200) ∧
    mul8 sG sG = one8 ∧ mul8 fG fG = one8 ∧ mul8 sG fG = mul8 fG sG ∧
    ∀ x ∈ omNE, x ∈ om3E ∨ mul8 sG x ∈ om3E ∨ mul8 fG x ∈ om3E ∨ mul8 sfG x ∈ om3E := by
  have h := o3Check_parts.1
  simp only [basicB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩, ⟨h9, h10⟩, h11, h12, h13, fun x hx => ?_⟩
  rcases h14 x hx with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mem_omega3N_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ omega3N ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ omNE := by
  rw [omega3N_eq]
  exact mem_genSub_iff_of basic_spec.2.2.1.1 gens_unit u

theorem card_omega3N : Nat.card omega3N = 14400 := by
  rw [omega3N_eq, card_genSub_of basic_spec.2.2.1.1 gens_unit]
  exact basic_spec.2.2.1.2

theorem exists_mem_omega3N {c : List ℕ} (hc : c ∈ omNE) :
    ∃ u ∈ omega3N, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  rw [omega3N_eq]
  exact exists_evalW _ (subB_spec basic_spec.2.2.1.1).2.2.2.2 gens_unit w

theorem unit_of_omNE {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ omNE) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_omega3N (h g hg); ⟨u, hu⟩

theorem genSub_le_omega3N {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ omNE) : genSub gens ≤ omega3N :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_omega3N_iff u).mpr (h _ hu)

theorem colsOf_mem_omNE {u : GL (Fin 8) (ZMod 2)}
    (hu : u ∈ omega3N) : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ omNE :=
  (mem_omega3N_iff u).mp hu

theorem gens_mem_omNE : ∀ g ∈ o3G ++ [fG, sG], g ∈ omNE := by
  intro g hg
  obtain ⟨u, hu⟩ := gens_unit g hg
  rw [← colsOf_dec8 ((subB_spec basic_spec.2.2.1.1).2.2.2.2 g hg), ← hu]
  exact colsOf_mem_omNE (by
    rw [omega3N_eq]
    exact mem_genSub_of_mem (subB_spec basic_spec.2.2.1.1).2.2.2.2 hg hu)

theorem mem_omega3_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ omega3 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ om3E := by
  rw [omega3_eq]
  exact mem_genSub_iff_of basic_spec.1.1
    (unit_of_omNE fun g hg => gens_mem_omNE g (List.mem_append_left _ hg)) u

theorem card_omega3 : Nat.card omega3 = 3600 := by
  rw [omega3_eq, card_genSub_of basic_spec.1.1
    (unit_of_omNE fun g hg => gens_mem_omNE g (List.mem_append_left _ hg))]
  exact basic_spec.1.2

theorem mem_omega3F_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ omega3F ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ om3FE := by
  rw [omega3F_eq]
  refine mem_genSub_iff_of basic_spec.2.1.1 (unit_of_omNE fun g hg => gens_mem_omNE g ?_) u
  simp only [List.mem_append, List.mem_singleton] at hg ⊢
  rcases hg with hg | rfl
  · exact Or.inl hg
  · simp

theorem card_omega3F : Nat.card omega3F = 7200 := by
  rw [omega3F_eq, card_genSub_of basic_spec.2.1.1 (unit_of_omNE fun g hg => gens_mem_omNE g ?_)]
  · exact basic_spec.2.1.2
  · simp only [List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with hg | rfl
    · exact Or.inl hg
    · simp

theorem omega3_le_omega3F : omega3 ≤ omega3F := by
  rw [omega3_eq, omega3F_eq]
  exact Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem omega3F_le_omega3N : omega3F ≤ omega3N := by
  rw [omega3F_eq, omega3N_eq]
  refine Subgroup.closure_mono fun _ hu => ?_
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hu ⊢
  tauto

@[expose] def H1 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (o3G ++ [sG])

@[expose] def H2 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (o3G ++ [sfG])

theorem sfG_mem : sfG ∈ omNE := by
  have hs : sG ∈ o3G ++ [fG, sG] := by simp
  have hf : fG ∈ o3G ++ [fG, sG] := by simp
  exact (subB_spec basic_spec.2.2.1.1).2.1 _ (gens_mem_omNE fG hf) _ hs

theorem h1G_mem : ∀ g ∈ o3G ++ [sG], g ∈ omNE := by
  intro g hg
  apply gens_mem_omNE
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  tauto

theorem h2G_mem : ∀ g ∈ o3G ++ [sfG], g ∈ omNE := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact gens_mem_omNE g (List.mem_append_left _ hg)
  · exact sfG_mem

theorem mem_H1_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ H1 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ h1E :=
  mem_genSub_iff_of basic_spec.2.2.2.1.1 (unit_of_omNE h1G_mem) u

theorem card_H1 : Nat.card H1 = 7200 := by
  rw [H1, card_genSub_of basic_spec.2.2.2.1.1 (unit_of_omNE h1G_mem)]
  exact basic_spec.2.2.2.1.2

theorem mem_H2_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ H2 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ h2E :=
  mem_genSub_iff_of basic_spec.2.2.2.2.1.1 (unit_of_omNE h2G_mem) u

theorem card_H2 : Nat.card H2 = 7200 := by
  rw [H2, card_genSub_of basic_spec.2.2.2.2.1.1 (unit_of_omNE h2G_mem)]
  exact basic_spec.2.2.2.2.1.2

theorem omega3_le_H2 : omega3 ≤ H2 := by
  rw [omega3_eq]
  exact Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem H2_le_omega3N : H2 ≤ omega3N := genSub_le_omega3N h2G_mem

theorem fG_unit_eq : dec8 fG = (o3field : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  rw [fG_cols, dec8_colsOf]

theorem colsOf_swap_mul (u : GL (Fin 8) (ZMod 2)) :
    colsOf ((o3swap * u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      mul8 sG (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  rw [Units.val_mul, colsOf_mul, sG_cols]

theorem colsOf_field_mul (u : GL (Fin 8) (ZMod 2)) :
    colsOf ((o3field * u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      mul8 fG (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  rw [Units.val_mul, colsOf_mul, fG_cols]

theorem colsOf_swapField_mul (u : GL (Fin 8) (ZMod 2)) :
    colsOf ((o3swap * o3field * u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      mul8 sfG (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  rw [Units.val_mul, colsOf_mul, Units.val_mul, colsOf_mul, sfG, sG_cols, fG_cols]

theorem field_mem_omega3F : o3field ∈ omega3F := by
  rw [omega3F_eq]
  exact mem_genSub_of_mem (subB_spec basic_spec.2.1.1).2.2.2.2
    (List.mem_append_right _ (List.mem_singleton_self fG)) fG_unit_eq.symm

theorem card_eq_of_between {Y X : Subgroup (GL (Fin 8) (ZMod 2))}
    (hY : Nat.card Y = 7200) (hYX : Y ≤ X) (hX : X ≤ omega3N) :
    Nat.card X = 7200 ∨ Nat.card X = 14400 := by
  obtain ⟨t, ht⟩ := hY ▸ Subgroup.card_dvd_of_le hYX
  have h2 : Nat.card X ∣ 14400 := card_omega3N ▸ Subgroup.card_dvd_of_le hX
  rw [ht] at h2 ⊢
  have ht2 : t ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7200) (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with rfl | rfl
  · left; rfl
  · right; rfl

theorem eq_of_le_omega3N {X : Subgroup (GL (Fin 8) (ZMod 2))}
    (h3X : omega3 ≤ X) (hXN : X ≤ omega3N) {x : GL (Fin 8) (ZMod 2)} (hxX : x ∈ X)
    (hxF : x ∉ omega3F) : X = H1 ∨ X = H2 ∨ X = omega3N := by
  have hx := colsOf_mem_omNE (hXN hxX)
  have hfin : ∀ {Y : Subgroup (GL (Fin 8) (ZMod 2))}, Nat.card Y = 7200 → Y ≤ X →
      X = Y ∨ X = omega3N := by
    intro Y hY hYX
    rcases card_eq_of_between hY hYX hXN with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hYX (by rw [h, hY])).symm
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hXN (by rw [h, card_omega3N]))
  rcases basic_spec.2.2.2.2.2.2.2.2 _ hx with h | h | h | h
  · exact absurd (omega3_le_omega3F ((mem_omega3_iff x).mpr h)) hxF
  ·
    have hsx : o3swap * x ∈ omega3 := (mem_omega3_iff _).mpr (by rw [colsOf_swap_mul]; exact h)
    have hs : o3swap ∈ X := by
      have := X.mul_mem (h3X hsx) (X.inv_mem hxX)
      simpa using this
    have hH1 : H1 ≤ X := by
      refine (Subgroup.closure_le _).mpr fun u hu => ?_
      rcases List.mem_append.mp hu with hu | hu
      · exact h3X (by rw [omega3_eq]; exact Subgroup.subset_closure hu)
      · have : u = o3swap := eq_of_colsOf_eq (by rw [List.mem_singleton.mp hu, sG_cols])
        rw [this]; exact hs
    rcases hfin card_H1 hH1 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  ·
    exfalso
    have hfx : o3field * x ∈ omega3 := (mem_omega3_iff _).mpr (by rw [colsOf_field_mul]; exact h)
    apply hxF
    have := omega3F.mul_mem (omega3F.inv_mem field_mem_omega3F) (omega3_le_omega3F hfx)
    simpa using this
  ·
    have hsx : o3swap * o3field * x ∈ omega3 :=
      (mem_omega3_iff _).mpr (by rw [colsOf_swapField_mul]; exact h)
    have hs : o3swap * o3field ∈ X := by
      have := X.mul_mem (h3X hsx) (X.inv_mem hxX)
      simpa using this
    have hH2 : H2 ≤ X := by
      refine (Subgroup.closure_le _).mpr fun u hu => ?_
      rcases List.mem_append.mp hu with hu | hu
      · exact h3X (by rw [omega3_eq]; exact Subgroup.subset_closure hu)
      · have : u = o3swap * o3field := eq_of_colsOf_eq (by
          rw [List.mem_singleton.mp hu, Units.val_mul, colsOf_mul, sfG, sG_cols, fG_cols])
        rw [this]; exact hs
    rcases hfin card_H2 hH2 with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

end CFSG.Quasithin.H13.O3Cert
