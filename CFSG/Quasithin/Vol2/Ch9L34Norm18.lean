module

public import CFSG.Quasithin.Vol2.Ch9L34NormGen
public import CFSG.Quasithin.Vol2.Ch9L34Ech
public import CFSG.Quasithin.Vol2.Ch9L34M18

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M

abbrev img18 : Subgroup (MulAut W18) := img rho18GL

@[expose] def c18 (g : GL (Fin 3) F4) : List ℕ :=
  cols (g : Matrix (Fin 3) (Fin 3) F4) ++
    (cols (grGL g : Matrix (Fin 3) (Fin 3) F4)).map (512 * ·)

theorem length_cols (g : Matrix (Fin 3) (Fin 3) F4) : (cols g).length = 9 := length_matOf _ _

theorem rho9_toW (g : GL (Fin 3) F4) (m : ℕ) :
    rho9 g (toW 9 m) = toW 9 (actM (cols (g : Matrix (Fin 3) (Fin 3) F4)) m) := by
  have hm : m % 512 < 512 := Nat.mod_lt _ (by norm_num)
  have h1 := rho9_toW9 g ⟨m % 512, hm⟩
  have h2 := actM_cols (g : Matrix (Fin 3) (Fin 3) F4) ⟨m % 512, hm⟩
  have h3 := actM_mod (cols (g : Matrix (Fin 3) (Fin 3) F4)) m
  rw [length_cols, show (2 : ℕ) ^ 9 = 512 by norm_num] at h3
  have e1 : toW 9 m = toW9 ⟨m % 512, hm⟩ := by
    rw [toW9_apply, ← toW_mod 9 m]
    rfl
  rw [e1, h1, toW9_apply, ← h3, h2]

theorem actM_cols_lt (g : Matrix (Fin 3) (Fin 3) F4) (m : ℕ) : actM (cols g) m < 512 :=
  actM_lt (k := 9) (fun c hc => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    exact (act _ _).2) m

theorem actsBy_c18 (g : GL (Fin 3) F4) : ActsBy coords18 (rho18GL g) (c18 g) := by
  intro m hm
  refine (rho18GL_apply g _).trans ?_
  rw [coords18_vm, c18]
  simp only
  rw [actM_append, length_cols, actM_map_mul512, rho9_toW, rho9_toW,
    xor_eq_add (actM_cols_lt _ _), coords18_vm_add (actM_cols_lt _ _)]
  norm_num

theorem act_c18 (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 18) :
    rho18GL g (coords18.vm m) = coords18.vm (actM (c18 g) m) :=
  actsBy_c18 g m hm

theorem allLt_c18 (g : GL (Fin 3) F4) : AllLt 18 (c18 g) = true := by
  rw [AllLt, List.all_eq_true]
  intro x hx
  rw [c18, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    have := (act (g : Matrix (Fin 3) (Fin 3) F4) ⟨2 ^ j % 512, Nat.mod_lt _ (by norm_num)⟩).2
    simp only [decide_eq_true_eq]
    have h : actN (g : Matrix (Fin 3) (Fin 3) F4) (2 ^ j) < 512 := (act _ _).2
    omega
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
    have h : actN (grGL g : Matrix (Fin 3) (Fin 3) F4) (2 ^ j) < 512 := (act _ _).2
    simp only [decide_eq_true_eq]
    omega

@[expose] def gen18 : Set (MulAut W18) :=
  {slRep rho18GL (uSL (f4c 1) 0 0), slRep rho18GL (uSL (f4c 2) 0 0),
    slRep rho18GL (uSL 0 0 (f4c 1)), slRep rho18GL (uSL 0 0 (f4c 2))}

abbrev P18 : Subgroup (MulAut W18) := Subgroup.closure gen18

theorem P18_le : P18 ≤ img18 := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl) <;> exact slRep_mem_img _ _

@[expose] def st18 (w : ℕ) : ℕ :=
  stack4 18 (c18 (uGL (f4c 1) 0 0)) (c18 (uGL (f4c 2) 0 0)) (c18 (uGL 0 0 (f4c 1)))
    (c18 (uGL 0 0 (f4c 2))) w

@[expose] def ker18 : List ℕ := echKer 18 st18

theorem ker18_spec :
    ker18.length = 16 ∧ AllLt 18 ker18 = true ∧ echOK (ker18.map st18) = true := by
  decide +kernel

theorem card_fixV_P18_le : Nat.card (fixV P18) ≤ 4 := by
  obtain ⟨hl, hws, hech⟩ := ker18_spec
  have h := two_pow_mul_card_le_four coords18 (actsBy_c18 _) (actsBy_c18 _) (actsBy_c18 _)
    (actsBy_c18 _) (allLt_c18 _) (allLt_c18 _) (allLt_c18 _) (allLt_c18 _) hws hech
    (F := fixV P18) fun v hv => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := hv _ (Subgroup.subset_closure (Or.inl rfl))
        rwa [slRep_uSL] at this
      · have := hv _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
        rwa [slRep_uSL] at this
      · have := hv _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl))))
        rwa [slRep_uSL] at this
      · have := hv _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl))))
        rwa [slRep_uSL] at this
  rw [hl] at h
  omega

theorem fix18_masks : ∀ m ∈ [0, 1, 512, 513],
    actM (c18 (uGL (f4c 1) 0 0)) m = m ∧ actM (c18 (uGL (f4c 2) 0 0)) m = m ∧
      actM (c18 (uGL 0 0 (f4c 1))) m = m ∧ actM (c18 (uGL 0 0 (f4c 2))) m = m := by
  decide +kernel

theorem lt_of_mem18 {m : ℕ} (hm : m ∈ [0, 1, 512, 513]) : m < 2 ^ 18 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

theorem mem_fixV_P18 {m : ℕ} (hm : m ∈ [0, 1, 512, 513]) : coords18.vm m ∈ fixV P18 := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := fix18_masks m hm
  have hlt := lt_of_mem18 hm
  apply mem_fixV_closure
  rintro _ (rfl | rfl | rfl | rfl) <;> rw [slRep_uSL]
  · exact (actsBy_c18 _ m hlt).trans (congrArg _ e₁)
  · exact (actsBy_c18 _ m hlt).trans (congrArg _ e₂)
  · exact (actsBy_c18 _ m hlt).trans (congrArg _ e₃)
  · exact (actsBy_c18 _ m hlt).trans (congrArg _ e₄)

theorem vm18_ne {a b : ℕ} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) (hab : a ≠ b) :
    coords18.vm a ≠ coords18.vm b := fun h => hab (coords18.vm_inj a b ha hb h)

theorem fixV_P18 {w : W18} (hw : w ∈ fixV P18) :
    w = coords18.vm 0 ∨ w = coords18.vm 1 ∨ w = coords18.vm 512 ∨ w = coords18.vm 513 := by
  classical
  set T : Finset W18 := {coords18.vm 0, coords18.vm 1, coords18.vm 512, coords18.vm 513} with hT
  have hTcard : T.card = 4 := by
    rw [hT, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (vm18_ne (by norm_num) (by norm_num) (by norm_num))]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨vm18_ne (by norm_num) (by norm_num) (by norm_num),
        vm18_ne (by norm_num) (by norm_num) (by norm_num)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨vm18_ne (by norm_num) (by norm_num) (by norm_num),
        vm18_ne (by norm_num) (by norm_num) (by norm_num),
        vm18_ne (by norm_num) (by norm_num) (by norm_num)⟩
  have hsub : (T : Set W18) ⊆ (fixV P18 : Set W18) := by
    intro x hx
    simp only [hT, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact mem_fixV_P18 (by simp)
  have hfin : (fixV P18 : Set W18).Finite := Set.toFinite _
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq]
    exact card_fixV_P18_le) hfin
  have hw' : w ∈ (T : Set W18) := heq ▸ hw
  simpa [hT] using hw'

@[expose] def words18 : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (16, 1), (32, 1), (48, 1), (0, 4), (1, 4), (2, 4), (4, 4), (8, 4), (16, 4),
    (17, 4), (18, 4), (20, 4), (24, 4), (32, 4), (48, 4), (0, 17)]

abbrev uC (p : ℕ) : GL (Fin 3) F4 := uGL (f4c p) (f4c (p / 4)) (f4c (p / 16))

@[expose] def orb18 (v : ℕ) : List ℕ :=
  words18.map fun pq => actM (c18 (uC pq.1)) (actM (c18 w0GL) (actM (c18 (uC pq.2))
    (actM (c18 w0GL) v)))

theorem orb18_spec :
    combOK (orb18 513) (echComb (orb18 513)) = true ∧
      pivOK 18 ((echComb (orb18 513)).map Prod.fst) = true := by
  decide +kernel

theorem closure_orbit18 :
    Subgroup.closure {x | ∃ γ ∈ img18, γ (coords18.vm 513) = x} = ⊤ := by
  obtain ⟨hc, hp⟩ := orb18_spec
  refine eq_top_of_comb coords18 hc hp fun o ho => ?_
  obtain ⟨⟨p, q⟩, -, rfl⟩ := List.mem_map.1 ho
  refine Subgroup.subset_closure ⟨slRep rho18GL (uSL (f4c p) (f4c (p / 4)) (f4c (p / 16)) *
    w0SL * uSL (f4c q) (f4c (q / 4)) (f4c (q / 16)) * w0SL), slRep_mem_img _ _, ?_⟩
  have lt1 := actM_lt (allLt_spec (allLt_c18 w0GL)) 513
  have lt2 := actM_lt (allLt_spec (allLt_c18 (uC q))) (actM (c18 w0GL) 513)
  have lt3 := actM_lt (allLt_spec (allLt_c18 w0GL)) (actM (c18 (uC q)) (actM (c18 w0GL) 513))
  simp only [map_mul, MulAut.mul_apply, slRep_uSL, slRep_w0SL]
  rw [act_c18 w0GL (by norm_num), act_c18 (uC q) lt1, act_c18 w0GL lt2, act_c18 (uC p) lt3]

theorem closure_orbit_le_fst {a : W9} :
    Subgroup.closure {x | ∃ γ ∈ img18, γ ((a, 1) : W18) = x} ≤ (⊤ : Subgroup W9).prod ⊥ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  refine ⟨Subgroup.mem_top _, ?_⟩
  change rho9 (grGL (SpecialLinearGroup.toGL g)) 1 ∈ (⊥ : Subgroup W9)
  rw [map_one]
  exact Subgroup.one_mem _

theorem closure_orbit_le_snd {a : W9} :
    Subgroup.closure {x | ∃ γ ∈ img18, γ ((1, a) : W18) = x} ≤ (⊥ : Subgroup W9).prod ⊤ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  refine ⟨?_, Subgroup.mem_top _⟩
  change rho9 (SpecialLinearGroup.toGL g) 1 ∈ (⊥ : Subgroup W9)
  rw [map_one]
  exact Subgroup.one_mem _

theorem nc18 : ∃ a b : SpecialLinearGroup (Fin 3) F4,
    slRep rho18GL a * slRep rho18GL b ≠ slRep rho18GL b * slRep rho18GL a := by
  refine ⟨uSL (f4c 1) 0 0, uSL 0 0 (f4c 1), fun h => ?_⟩
  have e := congrArg (fun F : MulAut W18 => F (coords18.vm 4)) h
  simp only [MulAut.mul_apply, slRep_uSL] at e
  rw [act_c18 _ (by norm_num), act_c18 _ (actM_lt (allLt_spec (allLt_c18 _)) 4),
    act_c18 _ (by norm_num), act_c18 _ (actM_lt (allLt_spec (allLt_c18 _)) 4)] at e
  have e2 := coords18.vm_inj _ _ (actM_lt (allLt_spec (allLt_c18 _)) _)
    (actM_lt (allLt_spec (allLt_c18 _)) _) e
  revert e2
  decide +kernel

theorem rho18GL_mem_range (g : GL (Fin 3) F4) : rho18GL g ∈ rho18.range :=
  ⟨SemidirectProduct.inl g, by rw [rho18_apply]; simp⟩

theorem fld18_mem_range : fld18 ∈ rho18.range := by
  refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1, 0)), ?_⟩
  rw [rho18_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
    out18, c22Hom_apply]
  simp

theorem swap18_mem_range : swap18 ∈ rho18.range := by
  refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (0, 1)), ?_⟩
  rw [rho18_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
    out18, c22Hom_apply]
  simp

theorem range_le_normalizer18 :
    rho18.range ≤ Subgroup.normalizer (img18 : Set (MulAut W18)) := by
  rintro _ ⟨x, rfl⟩
  rw [rho18_apply, out18]
  exact mul_c22Hom_mem_normalizer rho18GL rho18GL_frobGL rho18GL_grGL _ _ _ _ _

theorem odd18 : Odd (Nat.card {w : W18 // w ≠ 1 ∧ (∀ p ∈ P18, p w = w) ∧
    Subgroup.closure {v | ∃ γ ∈ img18, γ w = v} = ⊤}) := by
  classical
  have h1 : coords18.vm 1 = ((toW 9 1, 1) : W18) := by
    rw [coords18_vm]
    exact Prod.ext rfl (toW_zero 9)
  have h512 : coords18.vm 512 = ((1, toW 9 1) : W18) := by
    rw [coords18_vm]
    refine Prod.ext ?_ rfl
    rw [← toW_mod 9 512]
    exact toW_zero 9
  have hfst : (1, toW 9 1) ∉ ((⊤ : Subgroup W9).prod ⊥ : Subgroup W18) := fun h => by
    have h2 := (Subgroup.mem_prod.1 h).2
    rw [Subgroup.mem_bot] at h2
    exact absurd (toW_inj (n := 9) (by norm_num) (by norm_num) (h2.trans (toW_zero 9).symm))
      (by norm_num)
  have hsnd : (toW 9 1, 1) ∉ ((⊥ : Subgroup W9).prod ⊤ : Subgroup W18) := fun h => by
    have h2 := (Subgroup.mem_prod.1 h).1
    rw [Subgroup.mem_bot] at h2
    exact absurd (toW_inj (n := 9) (by norm_num) (by norm_num) (h2.trans (toW_zero 9).symm))
      (by norm_num)
  have hset : {w : W18 | w ≠ 1 ∧ (∀ p ∈ P18, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img18, γ w = v} = ⊤} = {coords18.vm 513} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hw1, hw2, hw3⟩
      rcases fixV_P18 hw2 with rfl | rfl | rfl | rfl
      · exact absurd coords18.vm_zero hw1
      · rw [h1] at hw3
        exact absurd (closure_orbit_le_fst (hw3 ▸ Subgroup.mem_top ((1, toW 9 1) : W18))) hfst
      · rw [h512] at hw3
        exact absurd (closure_orbit_le_snd (hw3 ▸ Subgroup.mem_top ((toW 9 1, 1) : W18))) hsnd
      · rfl
    · rintro rfl
      refine ⟨fun h => vm18_ne (a := 513) (b := 0) (by norm_num) (by norm_num) (by norm_num)
        (h.trans coords18.vm_zero.symm), mem_fixV_P18 (by simp), closure_orbit18⟩
  have hcard : Nat.card {w : W18 // w ≠ 1 ∧ (∀ p ∈ P18, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img18, γ w = v} = ⊤} = Set.ncard {w : W18 | w ≠ 1 ∧
        (∀ p ∈ P18, p w = w) ∧ Subgroup.closure {v | ∃ γ ∈ img18, γ w = v} = ⊤} :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_singleton]
  decide

theorem exists_conj_le18 {A : Subgroup (MulAut W18)}
    (hA : A ≤ Subgroup.normalizer (img18 : Set (MulAut W18))) (h2 : IsPGroup 2 A) :
    ∃ n ∈ Subgroup.normalizer (img18 : Set (MulAut W18)),
      A.map (MulAut.conj n).toMonoidHom ≤ rho18.range :=
  exists_conj_le_of_normalizer rho18GL rho18GL_frobGL rho18GL_grGL nc18 rho18GL_mem_range
    fld18_mem_range swap18_mem_range range_le_normalizer18 P18_le odd18 hA h2

end CFSG.Quasithin.H13.Ch9.L34N
