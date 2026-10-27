module

public import CFSG.Quasithin.EmptyFaithful.ModGChkC
public import CFSG.Quasithin.EmptyFaithful.ModGChkA

public section

namespace CFSG.Quasithin.ModG

open CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

@[expose] def pChk (uK uiK : ℕ) (rW : List (List ℕ)) : Bool :=
  anyL (fun x => memB x SK) (rW.map fun w => evc (alph4K uK uiK) (invW 4 w)) &&
    allL (fun a => allL (fun rc => anyL (fun rpi => memB (comp rpi (comp a rc)) SK)
      (rW.map fun w => evc (alph4K uK uiK) (invW 4 w))) (rW.map (evc (alph4K uK uiK))))
      (alph4K uK uiK)

theorem coset_closure (u : Mg) (uK uiK : ℕ) (hu : cd u = uK) (hui : cd u⁻¹ = uiK)
    (rW : List (List ℕ)) (hrW : ∀ w ∈ rW, ∀ l ∈ w, l < 2 * 4) (h : pChk uK uiK rW = true) :
    ∀ p ∈ Subgroup.closure ({x | x ∈ Ls} ∪ {u}), ∃ w ∈ rW, (ev (alph4 u) w)⁻¹ * p ∈ Sg := by
  simp only [pChk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hcdA : (alph4 u).map cd = alph4K uK uiK := by rw [alph4_cd, hu, hui]
  have hcdr : ∀ w, cd (ev (alph4 u) w) = evc (alph4K uK uiK) w := by
    intro w
    rw [c_ev cd cd_mul cd_one, hcdA]
  have hcdri : ∀ w ∈ rW, cd ((ev (alph4 u) w)⁻¹) = evc (alph4K uK uiK) (invW 4 w) := by
    intro w hw
    rw [← ev_invW (alph4_inv u) w (hrW w hw), hcdr]
  have hmemSg : ∀ g : Mg, memB (cd g) SK = true → g ∈ Sg := by
    intro g hg
    rw [mem_Sg_iff]
    rw [← SEl_cd] at hg
    exact mem_of_cd_mem (memB_iff.1 hg)
  have core : ∀ a ∈ alph4 u, ∀ q : Mg, (∃ w ∈ rW, (ev (alph4 u) w)⁻¹ * q ∈ Sg) →
      ∃ w' ∈ rW, (ev (alph4 u) w')⁻¹ * (a * q) ∈ Sg := by
    intro a haA q ⟨w, hw, hwq⟩
    have hcda : cd a ∈ alph4K uK uiK := by
      rw [← hcdA]
      exact cd_mem_of_mem haA
    have h3 := allL_iff.1 h2 (cd a) hcda
    have h4 := anyL_iff.1 (allL_iff.1 h3 (evc (alph4K uK uiK) w)
      (List.mem_map.2 ⟨w, hw, rfl⟩))
    obtain ⟨x, hx, hx'⟩ := h4
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hx
    refine ⟨w', hw', ?_⟩
    have hk : (ev (alph4 u) w')⁻¹ * (a * ev (alph4 u) w) ∈ Sg := by
      apply hmemSg
      rw [cd_mul, cd_mul, hcdri w' hw', hcdr w]
      exact hx'
    have : (ev (alph4 u) w')⁻¹ * (a * q) =
        ((ev (alph4 u) w')⁻¹ * (a * ev (alph4 u) w)) * ((ev (alph4 u) w)⁻¹ * q) := by group
    rw [this]
    exact Sg.mul_mem hk hwq
  have hgenA : ∀ a ∈ ({x | x ∈ Ls} ∪ {u} : Set Mg), a ∈ alph4 u := by
    intro a ha
    rcases ha with ha | ha
    · obtain ⟨i, hi, hia⟩ := List.getElem_of_mem (show a ∈ Ls from ha)
      have hi6 : i < 6 := by
        have := hi
        rw [Ls, invAlph_length, List.length_map, sWd_len] at this
        omega
      have hai : a = Ls.getD i 1 := by rw [List.getD_eq_getElem _ _ hi, hia]
      rw [hai]
      simp only [alph4, List.mem_cons]
      interval_cases i <;> simp
    · have : a = u := ha
      subst this
      simp [alph4]
  have hinvA : ∀ a ∈ alph4 u, a⁻¹ ∈ alph4 u := by
    intro a ha
    simp only [alph4, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    have hLs : ∀ i < 6, (Ls.getD i 1)⁻¹ = Ls.getD ((i + 3) % 6) 1 := by
      intro i hi
      have h := getD_inv_letter (ls := Ls) (r := 3) Ls_inv (l := i) (by omega)
      exact h.symm
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hLs 0 (by omega)]; simp
    · rw [hLs 1 (by omega)]; simp
    · rw [hLs 2 (by omega)]; simp
    · simp
    · rw [hLs 3 (by omega)]; simp
    · rw [hLs 4 (by omega)]; simp
    · rw [hLs 5 (by omega)]; simp
    · simp
  intro p hp
  induction hp using Subgroup.closure_induction_left with
  | one =>
    obtain ⟨x, hx, hx'⟩ := anyL_iff.1 h1
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    refine ⟨w, hw, ?_⟩
    rw [mul_one]
    apply hmemSg
    rw [hcdri w hw]
    exact hx'
  | mul_left a ha q hq ih => exact core a (hgenA a ha) q ih
  | inv_mul_cancel a ha q hq ih => exact core a⁻¹ (hinvA a (hgenA a ha)) q ih

@[expose] def u1 : Mg := ev Lks8 u1Wd

@[expose] def u2 : Mg := ev Lks8 u2Wd

theorem u1Wd_lt : ∀ l ∈ u1Wd, l < 2 * 4 := by decide +kernel
theorem u2Wd_lt : ∀ l ∈ u2Wd, l < 2 * 4 := by decide +kernel

theorem cd_u1 : cd u1 = evc Lks8K u1Wd := by rw [u1, c_ev cd cd_mul cd_one, Lks8_cd]
theorem cd_u2 : cd u2 = evc Lks8K u2Wd := by rw [u2, c_ev cd cd_mul cd_one, Lks8_cd]

theorem cd_u1_inv : cd u1⁻¹ = evc Lks8K (invW 4 u1Wd) := by
  rw [u1, ← ev_invW Lks8_inv u1Wd u1Wd_lt, c_ev cd cd_mul cd_one, Lks8_cd]

theorem cd_u2_inv : cd u2⁻¹ = evc Lks8K (invW 4 u2Wd) := by
  rw [u2, ← ev_invW Lks8_inv u2Wd u2Wd_lt, c_ev cd cd_mul cd_one, Lks8_cd]

theorem rW1_lt : ∀ w ∈ rW1, ∀ l ∈ w, l < 2 * 4 := by decide +kernel
theorem rW2_lt : ∀ w ∈ rW2, ∀ l ∈ w, l < 2 * 4 := by decide +kernel

theorem pCheck1 : pChk (evc Lks8K u1Wd) (evc Lks8K (invW 4 u1Wd)) rW1 = true := by decide +kernel
theorem pCheck2 : pChk (evc Lks8K u2Wd) (evc Lks8K (invW 4 u2Wd)) rW2 = true := by decide +kernel

@[expose] def P1 : Subgroup Mg := Subgroup.closure ({x | x ∈ Ls} ∪ {u1})

@[expose] def P2 : Subgroup Mg := Subgroup.closure ({x | x ∈ Ls} ∪ {u2})

theorem P1_cosets : ∀ p ∈ P1, ∃ w ∈ rW1, (ev (alph4 u1) w)⁻¹ * p ∈ Sg :=
  coset_closure u1 _ _ cd_u1 cd_u1_inv rW1 rW1_lt pCheck1

theorem P2_cosets : ∀ p ∈ P2, ∃ w ∈ rW2, (ev (alph4 u2) w)⁻¹ * p ∈ Sg :=
  coset_closure u2 _ _ cd_u2 cd_u2_inv rW2 rW2_lt pCheck2

theorem Ls_le_P1 : Sg ≤ P1 := by
  rw [Sg]
  exact Subgroup.closure_mono Set.subset_union_left

theorem Ls_le_P2 : Sg ≤ P2 := by
  rw [Sg]
  exact Subgroup.closure_mono Set.subset_union_left

theorem u1_mem_P1 : u1 ∈ P1 := Subgroup.subset_closure (Or.inr rfl)
theorem u2_mem_P2 : u2 ∈ P2 := Subgroup.subset_closure (Or.inr rfl)

theorem rep_mem_P1 (w : List ℕ) : ev (alph4 u1) w ∈ P1 := by
  refine ev_mem (fun x hx => ?_) w
  have h := Ls_le_P1
  simp only [alph4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h (Subgroup.subset_closure (Ls_mem 0 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 1 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 2 (by omega)))
  · exact u1_mem_P1
  · exact h (Subgroup.subset_closure (Ls_mem 3 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 4 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 5 (by omega)))
  · exact P1.inv_mem u1_mem_P1

theorem rep_mem_P2 (w : List ℕ) : ev (alph4 u2) w ∈ P2 := by
  refine ev_mem (fun x hx => ?_) w
  have h := Ls_le_P2
  simp only [alph4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h (Subgroup.subset_closure (Ls_mem 0 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 1 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 2 (by omega)))
  · exact u2_mem_P2
  · exact h (Subgroup.subset_closure (Ls_mem 3 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 4 (by omega)))
  · exact h (Subgroup.subset_closure (Ls_mem 5 (by omega)))
  · exact P2.inv_mem u2_mem_P2

@[expose] def alph5 : List Mg :=
  [Ls.getD 0 1, Ls.getD 1 1, Ls.getD 2 1, u1, u2, Ls.getD 3 1, Ls.getD 4 1, Ls.getD 5 1, u1⁻¹, u2⁻¹]

@[expose] def alph5K : List ℕ :=
  [LsK.getD 0 kId, LsK.getD 1 kId, LsK.getD 2 kId, evc Lks8K u1Wd, evc Lks8K u2Wd, LsK.getD 3 kId,
    LsK.getD 4 kId, LsK.getD 5 kId, evc Lks8K (invW 4 u1Wd), evc Lks8K (invW 4 u2Wd)]

theorem alph5_cd : alph5.map cd = alph5K := by
  simp only [alph5, alph5K, List.map_cons, List.map_nil, Ls_getD_cd, cd_u1, cd_u2, cd_u1_inv,
    cd_u2_inv]

theorem dgen_check : dgenW.map (evc alph5K) = dK := by decide +kernel

theorem di_eq_ev (j : ℕ) : di j = ev alph5 (dgenW.getD j []) := by
  apply cd_injective
  rw [c_ev cd cd_mul cd_one, alph5_cd, cd_di]
  have h := List.getD_map dgenW [] (n := j) (evc alph5K)
  rw [dgen_check] at h
  have h0 : evc alph5K [] = kId := by decide +kernel
  rw [h0] at h
  exact h

theorem alph5_mem : ∀ x ∈ alph5, x ∈ Subgroup.closure ({x | x ∈ Ls} ∪ {u1, u2}) := by
  intro x hx
  simp only [alph5, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inl (Ls_mem 0 (by omega)))
  · exact Subgroup.subset_closure (Or.inl (Ls_mem 1 (by omega)))
  · exact Subgroup.subset_closure (Or.inl (Ls_mem 2 (by omega)))
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  · exact Subgroup.subset_closure (Or.inl (Ls_mem 3 (by omega)))
  · exact Subgroup.subset_closure (Or.inl (Ls_mem 4 (by omega)))
  · exact Subgroup.subset_closure (Or.inl (Ls_mem 5 (by omega)))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr (Or.inr rfl)))

theorem di_mem_gen (j : ℕ) : di j ∈ Subgroup.closure ({x | x ∈ Ls} ∪ {u1, u2}) := by
  rw [di_eq_ev]
  exact ev_mem alph5_mem _

@[expose] def o1 : Mg := ev Lks8 (oWd.getD 0 [])

@[expose] def o2 : Mg := ev Lks8 (oWd.getD 1 [])

@[expose] def oAlph : List Mg := [o1, o2, o1⁻¹, o2⁻¹]

@[expose] def oAlphK : List ℕ :=
  [evc Lks8K (oWd.getD 0 []), evc Lks8K (oWd.getD 1 []), evc Lks8K (invW 4 (oWd.getD 0 [])),
    evc Lks8K (invW 4 (oWd.getD 1 []))]

theorem oWd_lt : ∀ w ∈ oWd, ∀ l ∈ w, l < 2 * 4 := by decide +kernel

theorem oWd_getD_lt (i : ℕ) : ∀ l ∈ oWd.getD i [], l < 2 * 4 := by
  by_cases h : i < oWd.length
  · rw [List.getD_eq_getElem _ _ h]
    exact oWd_lt _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (not_lt.mp h)]
    intro l hl
    exact absurd hl (List.not_mem_nil)

theorem oAlph_cd : oAlph.map cd = oAlphK := by
  have h1 : cd o1 = evc Lks8K (oWd.getD 0 []) := by rw [o1, c_ev cd cd_mul cd_one, Lks8_cd]
  have h2 : cd o2 = evc Lks8K (oWd.getD 1 []) := by rw [o2, c_ev cd cd_mul cd_one, Lks8_cd]
  have h3 : cd o1⁻¹ = evc Lks8K (invW 4 (oWd.getD 0 [])) := by
    rw [o1, ← ev_invW Lks8_inv _ (oWd_getD_lt 0), c_ev cd cd_mul cd_one, Lks8_cd]
  have h4 : cd o2⁻¹ = evc Lks8K (invW 4 (oWd.getD 1 [])) := by
    rw [o2, ← ev_invW Lks8_inv _ (oWd_getD_lt 1), c_ev cd cd_mul cd_one, Lks8_cd]
  simp only [oAlph, oAlphK, List.map_cons, List.map_nil, h1, h2, h3, h4]

@[expose] def cpow (x : ℕ) : ℕ → ℕ
  | 0 => kId
  | n + 1 => comp x (cpow x n)

theorem cd_pow (x : Mg) (n : ℕ) : cd (x ^ n) = cpow (cd x) n := by
  induction n with
  | zero => rw [pow_zero, cd_one]; rfl
  | succ n ih => rw [pow_succ', cd_mul, ih]; rfl

theorem o_order : cpow (evc Lks8K (oWd.getD 0 [])) 15 = kId ∧ cpow (evc Lks8K (oWd.getD 1 [])) 15 = kId := by
  decide +kernel

theorem o1_pow : o1 ^ 15 = 1 := by
  apply cd_injective
  rw [cd_pow, cd_one, o1, c_ev cd cd_mul cd_one, Lks8_cd]
  exact o_order.1

theorem o2_pow : o2 ^ 15 = 1 := by
  apply cd_injective
  rw [cd_pow, cd_one, o2, c_ev cd cd_mul cd_one, Lks8_cd]
  exact o_order.2

theorem t_check : tW.map (evc oAlphK) =
    [LsK.getD 0 kId, LsK.getD 1 kId, LsK.getD 2 kId, evc Lks8K u1Wd, evc Lks8K u2Wd] := by
  decide +kernel

theorem oAlph_mem : ∀ x ∈ oAlph, x ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
  intro x hx
  simp only [oAlph, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr rfl)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl rfl))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))

theorem tW_eq (i : ℕ) (x : Mg) (c : ℕ) (hc : cd x = c)
    (h : (tW.map (evc oAlphK)).getD i kId = c) : ev oAlph (tW.getD i []) = x := by
  apply cd_injective
  rw [c_ev cd cd_mul cd_one, oAlph_cd, hc, ← h]
  have := List.getD_map tW [] (n := i) (evc oAlphK)
  have h0 : evc oAlphK [] = kId := by decide +kernel
  rw [h0] at this
  exact this.symm

theorem Ls_odd : ∀ x ∈ Ls, x ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
  have h0 : Ls.getD 0 1 ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
    rw [← tW_eq 0 (Ls.getD 0 1) (LsK.getD 0 kId) (Ls_getD_cd 0) (by rw [t_check]; rfl)]
    exact ev_mem oAlph_mem _
  have h1 : Ls.getD 1 1 ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
    rw [← tW_eq 1 (Ls.getD 1 1) (LsK.getD 1 kId) (Ls_getD_cd 1) (by rw [t_check]; rfl)]
    exact ev_mem oAlph_mem _
  have h2 : Ls.getD 2 1 ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
    rw [← tW_eq 2 (Ls.getD 2 1) (LsK.getD 2 kId) (Ls_getD_cd 2) (by rw [t_check]; rfl)]
    exact ev_mem oAlph_mem _
  intro x hx
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hx
  have hi6 : i < 6 := by
    have := hi
    rw [Ls, invAlph_length, List.length_map, sWd_len] at this
    omega
  have hai : x = Ls.getD i 1 := by rw [List.getD_eq_getElem _ _ hi, hia]
  have hinv : ∀ j < 3, Ls.getD (j + 3) 1 = (Ls.getD j 1)⁻¹ := Ls_inv
  rw [hai]
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact (hinv 0 (by omega)) ▸ Subgroup.inv_mem _ h0
  · exact (hinv 1 (by omega)) ▸ Subgroup.inv_mem _ h1
  · exact (hinv 2 (by omega)) ▸ Subgroup.inv_mem _ h2

theorem u1_odd : u1 ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
  rw [← tW_eq 3 u1 (evc Lks8K u1Wd) cd_u1 (by rw [t_check]; rfl)]
  exact ev_mem oAlph_mem _

theorem u2_odd : u2 ∈ Subgroup.closure ({o1, o2} : Set Mg) := by
  rw [← tW_eq 4 u2 (evc Lks8K u2Wd) cd_u2 (by rw [t_check]; rfl)]
  exact ev_mem oAlph_mem _

theorem gen_le_odd : Subgroup.closure ({x | x ∈ Ls} ∪ {u1, u2}) ≤ Subgroup.closure ({o1, o2} : Set Mg) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact Ls_odd x hx
  · rcases hx with rfl | rfl
    · exact u1_odd
    · exact u2_odd

@[expose] def deltaK : ℕ := 426532920769104248462904303653038

theorem pk_delta : pk M22Insp.delta = deltaK := by decide +kernel

theorem pk_delta_inv : pk (M22Insp.delta⁻¹) = deltaK := by decide +kernel

@[expose] def x0 : Mg := ev Lab x0Wd

theorem x0Wd_lt : ∀ l ∈ x0Wd, l < 2 * 2 := by decide +kernel

theorem cd_x0 : cd x0 = evc LabK x0Wd := by rw [x0, c_ev cd cd_mul cd_one, Lab_cd]

theorem cd_x0_inv : cd x0⁻¹ = evc LabK (invW 2 x0Wd) := by
  rw [x0, ← ev_invW Lab_inv x0Wd x0Wd_lt, c_ev cd cd_mul cd_one, Lab_cd]

@[expose] def delta1 : Equiv.Perm (Fin 22) := M22Insp.delta * (x0 : Equiv.Perm (Fin 22))

@[expose] def delta1K : ℕ := comp deltaK (evc LabK x0Wd)

@[expose] def delta1iK : ℕ := comp (evc LabK (invW 2 x0Wd)) deltaK

theorem pk_delta1 : pk delta1 = delta1K := by
  rw [delta1, pk_mul, pk_delta]
  show comp deltaK (cd x0) = _
  rw [cd_x0]
  rfl

theorem pk_delta1_inv : pk delta1⁻¹ = delta1iK := by
  rw [delta1, mul_inv_rev, pk_mul, pk_delta_inv]
  have : pk ((x0 : Equiv.Perm (Fin 22))⁻¹) = cd x0⁻¹ := rfl
  rw [this, cd_x0_inv]
  rfl

theorem delta1_S_check : ∀ i ∈ [0, 1, 2], memB (comp (comp delta1K (LsK.getD i kId)) delta1iK) SK = true := by
  decide +kernel

theorem delta1_B_check : ∀ x ∈ B0l, memB (Nat.sub (dg delta1K x) 1) B0l = true := by decide +kernel

theorem delta1_P1_check :
    anyL (fun rpi => memB (comp rpi (comp (comp delta1K (evc Lks8K u1Wd)) delta1iK)) SK)
      (rW1.map fun w => evc (alph4K (evc Lks8K u1Wd) (evc Lks8K (invW 4 u1Wd))) (invW 4 w)) = true := by
  decide +kernel

theorem delta1_P2_check :
    anyL (fun rpi => memB (comp rpi (comp (comp delta1K (evc Lks8K u2Wd)) delta1iK)) SK)
      (rW2.map fun w => evc (alph4K (evc Lks8K u2Wd) (evc Lks8K (invW 4 u2Wd))) (invW 4 w)) = true := by
  decide +kernel

theorem delta1_S (i : ℕ) (hi : i < 3) :
    ∃ t ∈ SEl, (t : Equiv.Perm (Fin 22)) = delta1 * ((Ls.getD i 1 : Mg) : Equiv.Perm (Fin 22)) * delta1⁻¹ := by
  have h := delta1_S_check i (by simp; omega)
  have h2 : pk (delta1 * ((Ls.getD i 1 : Mg) : Equiv.Perm (Fin 22)) * delta1⁻¹) ∈ SK := by
    rw [pk_mul, pk_mul, pk_delta1, pk_delta1_inv]
    have : pk ((Ls.getD i 1 : Mg) : Equiv.Perm (Fin 22)) = LsK.getD i kId := Ls_getD_cd i
    rw [this]
    exact memB_iff.1 h
  rw [← SEl_cd] at h2
  obtain ⟨t, ht, hte⟩ := List.mem_map.1 h2
  exact ⟨t, ht, pk_injective hte⟩

theorem delta1_B : ∀ x : Fin 22, x.val ∈ B0l → (delta1 x).val ∈ B0l := by
  intro x hx
  rw [val_apply_eq, pk_delta1]
  exact memB_iff.1 (delta1_B_check x.val hx)

theorem conj_in_coset (u : Mg) (uK uiK : ℕ) (hu : cd u = uK) (hui : cd u⁻¹ = uiK)
    (rW : List (List ℕ)) (hrW : ∀ w ∈ rW, ∀ l ∈ w, l < 2 * 4) (g : Equiv.Perm (Fin 22)) (gK : ℕ)
    (hg : pk g = gK)
    (h : anyL (fun rpi => memB (comp rpi gK) SK) (rW.map fun w => evc (alph4K uK uiK) (invW 4 w)) = true) :
    ∃ w ∈ rW, ∃ t ∈ SEl, g = ((ev (alph4 u) w : Mg) : Equiv.Perm (Fin 22)) * (t : Equiv.Perm (Fin 22)) := by
  obtain ⟨x, hx, hx'⟩ := anyL_iff.1 h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  refine ⟨w, hw, ?_⟩
  have hcdA : (alph4 u).map cd = alph4K uK uiK := by rw [alph4_cd, hu, hui]
  have hr : cd ((ev (alph4 u) w)⁻¹) = evc (alph4K uK uiK) (invW 4 w) := by
    rw [← ev_invW (alph4_inv u) w (hrW w hw), c_ev cd cd_mul cd_one, hcdA]
  have h2 : pk ((((ev (alph4 u) w)⁻¹ : Mg) : Equiv.Perm (Fin 22)) * g) ∈ SK := by
    rw [pk_mul, hg]
    have : pk (((ev (alph4 u) w)⁻¹ : Mg) : Equiv.Perm (Fin 22)) = evc (alph4K uK uiK) (invW 4 w) := hr
    rw [this]
    exact memB_iff.1 hx'
  rw [← SEl_cd] at h2
  obtain ⟨t, ht, hte⟩ := List.mem_map.1 h2
  refine ⟨t, ht, ?_⟩
  have h3 : (t : Equiv.Perm (Fin 22)) =
      (((ev (alph4 u) w)⁻¹ : Mg) : Equiv.Perm (Fin 22)) * g := pk_injective hte
  rw [h3]
  simp

theorem delta1_P1 : ∃ w ∈ rW1, ∃ t ∈ SEl,
    delta1 * (u1 : Equiv.Perm (Fin 22)) * delta1⁻¹ =
      ((ev (alph4 u1) w : Mg) : Equiv.Perm (Fin 22)) * (t : Equiv.Perm (Fin 22)) :=
  conj_in_coset u1 _ _ cd_u1 cd_u1_inv rW1 rW1_lt _
    (comp (comp delta1K (evc Lks8K u1Wd)) delta1iK)
    (by rw [pk_mul, pk_mul, pk_delta1, pk_delta1_inv, show pk (u1 : Equiv.Perm (Fin 22)) = evc Lks8K u1Wd from cd_u1]) delta1_P1_check

theorem delta1_P2 : ∃ w ∈ rW2, ∃ t ∈ SEl,
    delta1 * (u2 : Equiv.Perm (Fin 22)) * delta1⁻¹ =
      ((ev (alph4 u2) w : Mg) : Equiv.Perm (Fin 22)) * (t : Equiv.Perm (Fin 22)) :=
  conj_in_coset u2 _ _ cd_u2 cd_u2_inv rW2 rW2_lt _
    (comp (comp delta1K (evc Lks8K u2Wd)) delta1iK)
    (by rw [pk_mul, pk_mul, pk_delta1, pk_delta1_inv, show pk (u2 : Equiv.Perm (Fin 22)) = evc Lks8K u2Wd from cd_u2]) delta1_P2_check

end CFSG.Quasithin.ModG
