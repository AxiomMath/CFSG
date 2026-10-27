module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Faith
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverFlag

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates
open scoped Pointwise

set_option linter.unusedSectionVars false

theorem countP_range_eq (lab : Array ℕ) (c n : ℕ) :
    (List.range n).countP (fun x => lab[x]! == c) =
      ((Finset.range n).filter fun x => lab[x]! = c).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : lab[n]! = c
    · simp [h]
    · simp [h]

theorem labelCount_eq_card (n : ℕ) (lab : Array ℕ) (c : ℕ) :
    labelCount n lab c = Nat.card {x : Fin n // lab[(x : ℕ)]! = c} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, labelCount, countP_range_eq,
    ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩


section Gens

@[expose] noncomputable def uGen (i : ℕ) : D := [d4GenG 0, d4GenG 1, d4GenG 2, d4GenG 6].getD i 1

theorem uGen_eq_uGH {i : ℕ} (hi : i < 4) : uGen i = uGH i := by
  interval_cases i <;> rfl

theorem uGen_mem_B {i : ℕ} (hi : i < 4) : uGen i ∈ d4B := by
  interval_cases i
  · exact gen_mem_B (j := 0) (Or.inl rfl)
  · exact gen_mem_B (j := 1) (Or.inr (Or.inl rfl))
  · exact gen_mem_B (j := 2) (Or.inr (Or.inr (Or.inl rfl)))
  · exact gen_mem_B (j := 6) (Or.inr (Or.inr (Or.inr rfl)))

theorem uPtArrs_get0 : uPtArrs[0]! = permArrs[0]! := by simp [uPtArrs]

theorem uPtArrs_get1 : uPtArrs[1]! = permArrs[1]! := by simp [uPtArrs]

theorem uPtArrs_get2 : uPtArrs[2]! = permArrs[2]! := by simp [uPtArrs]

theorem uPtArrs_get3 : uPtArrs[3]! = permArrs[6]! := by simp [uPtArrs]

end Gens


section Orbits

theorem ovU_parts : uPtArrs.size = 4 ∧ ovURep.length = 6 ∧ ovURep[0]! = 0 ∧ ovURep[1]! = 1 ∧
    orbitLabelOK 819 uPtArrs 6 ovUForest.1 ovURep.toArray ovUForest.2.1 ovUForest.2.2.1
      ovUForest.2.2.2 = true ∧ ovUForest.1[5]! = 1 ∧
    labelCount 819 ovUForest.1 0 = 1 ∧ labelCount 819 ovUForest.1 1 = 2 ∧
    labelCount 819 ovUForest.1 2 = 16 ∧ labelCount 819 ovUForest.1 3 = 32 ∧
    labelCount 819 ovUForest.1 4 = 256 ∧ labelCount 819 ovUForest.1 5 = 512 := by
  have h := overCheck_parts.2.1
  simp only [ovUCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have h8 : labelCount 819 ovUForest.1 0 = 1 ∧ labelCount 819 ovUForest.1 1 = 2 ∧
      labelCount 819 ovUForest.1 2 = 16 ∧ labelCount 819 ovUForest.1 3 = 32 ∧
      labelCount 819 ovUForest.1 4 = 256 ∧ labelCount 819 ovUForest.1 5 = 512 := by
    simpa [List.range_succ] using h7
  exact ⟨h1, h2, h3, h4, h5, h6, h8⟩

theorem uPt_rep : ∀ i < uPtArrs.size, Rep 819 uPtArrs[i]! (act (uGen i)) := by
  intro i hi
  have h4 : uPtArrs.size = 4 := ovU_parts.1
  rw [h4] at hi
  interval_cases i
  · rw [uPtArrs_get0]
    exact act_gen (j := 0) (by norm_num)
  · rw [uPtArrs_get1]
    exact act_gen (j := 1) (by norm_num)
  · rw [uPtArrs_get2]
    exact act_gen (j := 2) (by norm_num)
  · rw [uPtArrs_get3]
    exact act_gen (j := 6) (by norm_num)

@[expose] noncomputable def GU : Subgroup (Equiv.Perm (Fin 819)) :=
  genGroup uPtArrs (fun i => act (uGen i))

theorem GU_eq : GU = d4U.map act := by
  have h4 : uPtArrs.size = 4 := ovU_parts.1
  apply le_antisymm
  · rw [GU, genGroup, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 4 := by simpa [h4] using hi
    refine ⟨uGH i, Subgroup.subset_closure ⟨i, ?_, rfl⟩, by
      show act (uGH i) = act (uGen i)
      rw [uGen_eq_uGH hi']⟩
    rw [uGens_size]
    exact hi'
  · rw [Subgroup.map_le_iff_le_comap, d4U, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 4 := by simpa [uGens_size] using hk
    show act (uGH k) ∈ GU
    rw [← uGen_eq_uGH hk']
    exact Subgroup.subset_closure ⟨k, by simpa [h4] using hk', rfl⟩

theorem orbit_GU (p : Fin 819) :
    MulAction.orbit GU p = {q : Fin 819 | ovUForest.1[(q : ℕ)]! = ovUForest.1[(p : ℕ)]!} := by
  obtain ⟨-, -, -, -, hU, -⟩ := ovU_parts
  unfold GU
  have hc : ovUForest.1[(p : ℕ)]! < 6 := (orbitLabelOK_parts hU).1 p p.2
  have h := orbit_eq_label hU (gs := fun i => act (uGen i)) uPt_rep hc
  have hp : p ∈ {x : Fin 819 | ovUForest.1[(x : ℕ)]! = ovUForest.1[(p : ℕ)]!} := rfl
  rw [← h] at hp
  rw [← MulAction.orbit_eq_iff.2 hp] at h
  exact h

theorem card_orbit_GU (p : Fin 819) :
    Nat.card (MulAction.orbit GU p) = labelCount 819 ovUForest.1 ovUForest.1[(p : ℕ)]! := by
  rw [orbit_GU, labelCount_eq_card]
  rfl

end Orbits

section Normalizer

theorem mem_GU_iff {g : Equiv.Perm (Fin 819)} : g ∈ GU ↔ ∃ u ∈ d4U, act u = g := by
  rw [GU_eq]
  exact Subgroup.mem_map

theorem normalizer_orbit {x : D} (hx : x ∈ Subgroup.normalizer (d4U : Set D)) (p : Fin 819) :
    MulAction.orbit GU (act x p) = (act x) '' MulAction.orbit GU p := by
  have hx' := Subgroup.mem_normalizer_iff.1 hx
  have hxi' := Subgroup.mem_normalizer_iff.1 (inv_mem hx)
  ext q
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨u, hu, rfl⟩ := mem_GU_iff.1 hg
    have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ d4U := (hxi' u).1 hu
    refine ⟨act (x⁻¹ * u * x⁻¹⁻¹) p,
      ⟨⟨act (x⁻¹ * u * x⁻¹⁻¹), mem_GU_iff.2 ⟨_, hu', rfl⟩⟩, rfl⟩, ?_⟩
    show act x (act (x⁻¹ * u * x⁻¹⁻¹) p) = act u (act x p)
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← Equiv.Perm.mul_apply, ← map_mul]
    congr 2
    group
  · rintro ⟨q', ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    obtain ⟨u, hu, rfl⟩ := mem_GU_iff.1 hg
    have hu' : x * u * x⁻¹ ∈ d4U := (hx' u).1 hu
    refine ⟨⟨act (x * u * x⁻¹), mem_GU_iff.2 ⟨_, hu', rfl⟩⟩, ?_⟩
    show act (x * u * x⁻¹) (act x p) = act x (act u p)
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← Equiv.Perm.mul_apply, ← map_mul]
    congr 2
    group

theorem card_orbit_normalizer {x : D} (hx : x ∈ Subgroup.normalizer (d4U : Set D)) (p : Fin 819) :
    Nat.card (MulAction.orbit GU (act x p)) = Nat.card (MulAction.orbit GU p) := by
  rw [normalizer_orbit hx p]
  exact Nat.card_image_of_injective (act x).injective _

theorem lab_lt (p : Fin 819) : ovUForest.1[(p : ℕ)]! < 6 :=
  (orbitLabelOK_parts ovU_parts.2.2.2.2.1).1 p p.2

theorem count_inj {a b : ℕ} (ha : a < 6) (hb : b < 6)
    (h : labelCount 819 ovUForest.1 a = labelCount 819 ovUForest.1 b) : a = b := by
  obtain ⟨-, -, -, -, -, -, h0, h1, h2, h3, h4, h5⟩ := ovU_parts
  interval_cases a <;> interval_cases b <;> simp_all

theorem normalizer_label {x : D} (hx : x ∈ Subgroup.normalizer (d4U : Set D)) (p : Fin 819) :
    ovUForest.1[((act x p : Fin 819) : ℕ)]! = ovUForest.1[(p : ℕ)]! := by
  apply count_inj (lab_lt _) (lab_lt _)
  rw [← card_orbit_GU, ← card_orbit_GU]
  exact card_orbit_normalizer hx p

abbrev uPt1 : Fin 819 := ⟨1, by norm_num⟩

abbrev uPt5 : Fin 819 := ⟨5, by norm_num⟩

theorem lab_pt0 : ovUForest.1[(pt0 : ℕ)]! = 0 := by
  obtain ⟨-, -, h3, -, hU, -⟩ := ovU_parts
  have := ((orbitLabelOK_parts hU).2.2.1 0 (by norm_num)).2.1
  simpa [List.getElem!_toArray, h3] using this

theorem lab_pt1 : ovUForest.1[(uPt1 : ℕ)]! = 1 := by
  obtain ⟨-, -, -, h4, hU, -⟩ := ovU_parts
  have := ((orbitLabelOK_parts hU).2.2.1 1 (by norm_num)).2.1
  simpa [List.getElem!_toArray, h4] using this

theorem lab_pt5 : ovUForest.1[(uPt5 : ℕ)]! = 1 := ovU_parts.2.2.2.2.2.1

theorem class_zero : {q : Fin 819 | ovUForest.1[(q : ℕ)]! = 0} = {pt0} := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro q hq
    rw [Set.mem_singleton_iff.1 hq]
    exact lab_pt0
  · have h := card_orbit_GU pt0
    rw [lab_pt0, ovU_parts.2.2.2.2.2.2.1, orbit_GU, lab_pt0] at h
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq]
    exact h.le
  · exact Set.toFinite _

theorem class_one : {q : Fin 819 | ovUForest.1[(q : ℕ)]! = 1} = {uPt1, uPt5} := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro q hq
    rcases hq with rfl | rfl
    · exact lab_pt1
    · exact lab_pt5
  · have h := card_orbit_GU uPt1
    rw [lab_pt1, ovU_parts.2.2.2.2.2.2.2.1, orbit_GU, lab_pt1] at h
    rw [Set.ncard_pair (by decide), ← Nat.card_coe_set_eq]
    exact h.le
  · exact Set.toFinite _

theorem normalizer_fixes_pt0 {x : D} (hx : x ∈ Subgroup.normalizer (d4U : Set D)) :
    act x pt0 = pt0 := by
  have h := normalizer_label hx pt0
  rw [lab_pt0] at h
  have : act x pt0 ∈ {q : Fin 819 | ovUForest.1[(q : ℕ)]! = 0} := h
  rw [class_zero] at this
  exact this

theorem normalizer_maps_class_one {x : D} (hx : x ∈ Subgroup.normalizer (d4U : Set D))
    {p : Fin 819} (hp : p = uPt1 ∨ p = uPt5) : act x p = uPt1 ∨ act x p = uPt5 := by
  have h := normalizer_label hx p
  have hl : ovUForest.1[(p : ℕ)]! = 1 := by rcases hp with rfl | rfl; exact lab_pt1; exact lab_pt5
  rw [hl] at h
  have : act x p ∈ {q : Fin 819 | ovUForest.1[(q : ℕ)]! = 1} := h
  rw [class_one] at this
  exact this

theorem normalizer_d4U_le_d4B : Subgroup.normalizer (d4U : Set D) ≤ d4B := by
  intro x hx
  change x ∈ d4H ⊓ d4N
  refine Subgroup.mem_inf.2 ⟨(mem_d4H_iff_act x).2 (normalizer_fixes_pt0 hx), ?_⟩
  rw [mem_d4N_iff_image]
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    simp only [line0, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hr ⊢
    obtain ⟨q, hq, rfl⟩ := hr
    rcases hq with rfl | rfl | rfl
    · exact Or.inl (normalizer_fixes_pt0 hx)
    · exact Or.inr (normalizer_maps_class_one hx (Or.inl rfl))
    · exact Or.inr (normalizer_maps_class_one hx (Or.inr rfl))
  · rw [Finset.card_image_of_injective _ (act x).injective]

end Normalizer

section Zeta

theorem rep_unique {n : ℕ} {a : Array ℕ} {σ τ : Equiv.Perm (Fin n)} (h1 : Rep n a σ)
    (h2 : Rep n a τ) : σ = τ :=
  Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

theorem rep_ptPowArr {a : Array ℕ} {σ : Equiv.Perm (Fin 819)} (h : Rep 819 a σ) :
    ∀ k : ℕ, Rep 819 (ptPowArr a k) (σ ^ k)
  | 0 => by simpa [ptPowArr] using rep_idA (n := 819)
  | k + 1 => by simpa [ptPowArr, pow_succ'] using rep_compA h (rep_ptPowArr h k)

theorem gen_mem_d4U {k : ℕ} (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 6) : d4GenG k ∈ d4U := by
  have key : ∀ i < 4, uGH i ∈ d4U := fun i hi =>
    Subgroup.subset_closure ⟨i, by rw [uGens_size]; exact hi, rfl⟩
  rcases hk with rfl | rfl | rfl | rfl
  · exact key 0 (by norm_num)
  · exact key 1 (by norm_num)
  · exact key 2 (by norm_num)
  · exact key 3 (by norm_num)

theorem d4Word_mem_d4U : ∀ w : List ℕ, (∀ k ∈ w, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 6) →
    d4Word w ∈ d4U
  | [], _ => by simp [d4Word]
  | k :: w, hw => by
    have : d4Word (k :: w) = d4GenG k * d4Word w := by simp [d4Word]
    rw [this]
    exact d4U.mul_mem (gen_mem_d4U (hw k List.mem_cons_self))
      (d4Word_mem_d4U w fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))

theorem d4U_le_d4B' : d4U ≤ d4B := by
  rw [d4U, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 4 := by simpa [uGens_size] using hk
  show uGH k ∈ d4B
  rw [← uGen_eq_uGH hk']
  exact uGen_mem_B hk'

variable (hs : IsSimpleGroup D)
include hs

theorem d4Zeta_pow_seven : d4Zeta ^ 7 = 1 := by
  obtain ⟨-, -, h3, -⟩ := ovZeta_parts
  apply act_injective hs
  have hr := rep_ptPowArr (rep_ptWordArr (w := [3, 2, 4, 2]) (by decide)) 7
  rw [h3] at hr
  rw [map_pow, map_one]
  exact rep_unique hr (rep_idA (n := 819))

theorem zeta_conj_aux {j : ℕ} (hj : j < 8) {w : List ℕ} (hw : ∀ k ∈ w, k < 8)
    (h : compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[j]! =
      compA 819 (ptWordArr w) (ptWordArr [3, 2, 4, 2])) :
    d4Zeta * d4GenG j = d4Word w * d4Zeta := by
  apply act_injective hs
  have h1 := rep_compA (rep_ptWordArr (w := [3, 2, 4, 2]) (by decide)) (act_gen hj)
  have h2 := rep_compA (rep_ptWordArr hw) (rep_ptWordArr (w := [3, 2, 4, 2]) (by decide))
  rw [h] at h1
  rw [map_mul, map_mul]
  exact rep_unique h1 h2

theorem zeta_conj_gen {k : ℕ} (hk : k < 4) : ∃ u ∈ d4U, d4Zeta * uGen k * d4Zeta⁻¹ = u := by
  obtain ⟨-, -, -, h4, h5, h6, h7, -⟩ := ovZeta_parts
  interval_cases k
  · refine ⟨d4Word [2], d4Word_mem_d4U _ (by decide), ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact zeta_conj_aux hs (j := 0) (by norm_num) (by decide) h4
  · refine ⟨d4Word [0, 1], d4Word_mem_d4U _ (by decide), ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact zeta_conj_aux hs (j := 1) (by norm_num) (by decide) h5
  · refine ⟨d4Word [1, 2], d4Word_mem_d4U _ (by decide), ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact zeta_conj_aux hs (j := 2) (by norm_num) (by decide) h6
  · refine ⟨d4Word [0, 2, 6, 0, 2], d4Word_mem_d4U _ (by decide), ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact zeta_conj_aux hs (j := 6) (by norm_num) (by decide) h7

end Zeta

end CFSG.Quasithin.D4Hex
