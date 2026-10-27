module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6OverCodes

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over

open CFSG.Quasithin.G2U CFSG.Quasithin.H13.MatNCert Matrix
open CFSG.Quasithin.H13.Mat8Cert (b2z)

abbrev GL6 : Type := GL (Fin 6) (ZMod 2)

abbrev M6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

theorem orbR_mem {P : List ℕ → Prop} {act : List ℕ → List ℕ → List ℕ} {dflt t : List ℕ}
    {gens : List (List ℕ)} (h0 : P t) (hstep : ∀ x, P x → ∀ i, P (act x (gens.getD i dflt)))
    (par : List (ℕ × ℕ)) : ∀ x ∈ orbR act dflt t gens par, P x := by
  have key : ∀ (l : List (ℕ × ℕ)) (acc : Array (List ℕ)), (∀ x ∈ acc, P x) →
      ∀ x ∈ l.foldl (fun acc ps => acc.push (act (acc.getD ps.1 t) (gens.getD ps.2 dflt))) acc,
        P x := by
    intro l
    induction l with
    | nil => exact fun acc h => h
    | cons ps l ih =>
      intro acc h
      rw [List.foldl_cons]
      refine ih _ fun x hx => ?_
      rcases Array.mem_push.mp hx with hx | rfl
      · exact h x hx
      · refine hstep _ ?_ _
        rw [Array.getD]
        split_ifs with hp
        · exact h _ (Array.getElem_mem hp)
        · exact h0
  exact key par #[t] (fun x hx => by rw [Array.mem_singleton.mp hx]; exact h0)

theorem testBit_bitsOf (f : ℕ → Bool) (n i : ℕ) :
    (bitsOf f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [bitsOf]
  | succ k ih =>
    rw [bitsOf, Nat.testBit_xor, ih]
    rcases lt_trichotomy i k with h | rfl | h
    · have h1 : ¬ k = i := by omega
      have h2 : i < k + 1 := by omega
      cases hf : f k <;> simp [h, h2, Nat.testBit_two_pow, h1]
    · cases hf : f i <;> simp [Nat.testBit_two_pow, hf]
    · have h1 : ¬ i < k := by omega
      have h2 : ¬ i < k + 1 := by omega
      have h3 : ¬ k = i := by omega
      cases hf : f k <;> simp [h1, h2, Nat.testBit_two_pow, h3]

theorem length_formAct (w g : List ℕ) : (formAct w g).length = 6 := by
  simp [formAct]

theorem decN_formAct {w : List ℕ} (hw : w.length = 6) (g : List ℕ) :
    decN 6 (formAct w g) = (decN 6 g)ᵀ * decN 6 w * decN 6 g := by
  ext i j
  have hj : (j : ℕ) < (formAct w g).length := by rw [length_formAct]; exact j.isLt
  have e1 : decN 6 (formAct w g) i j = b2z (dotN 6 (g.getD i 0) (mvN w (g.getD j 0))) := by
    simp only [decN, Matrix.of_apply, vecN]
    rw [List.getD_eq_getElem _ _ hj]
    simp [formAct, testBit_bitsOf]
  rw [e1, dotN_spec, ← decN_mulVec hw]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [decN, Matrix.of_apply]
  ring

theorem exists_unit_of_inv {n : ℕ} {g h : List ℕ} (hg : ValidN n g) (hh : ValidN n h)
    (e1 : mulN g h = oneN n) (e2 : mulN h g = oneN n) :
    ∃ u : GL (Fin n) (ZMod 2), (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g :=
  ⟨⟨decN n g, decN n h, by rw [← decN_mulN hg.1 hh.1, e1, decN_oneN],
    by rw [← decN_mulN hh.1 hg.1, e2, decN_oneN]⟩, rfl⟩

@[ext] structure Form6 where
  mat : M6

instance : Finite Form6 := Finite.of_injective Form6.mat fun _ _ h => Form6.ext h

instance : MulAction GL6 Form6 where
  smul g w := ⟨(((g⁻¹ : GL6) : M6))ᵀ * w.mat * ((g⁻¹ : GL6) : M6)⟩
  one_smul w := by
    ext1
    show (((1⁻¹ : GL6) : M6))ᵀ * w.mat * ((1⁻¹ : GL6) : M6) = w.mat
    simp
  mul_smul g h w := by
    ext1
    show (((g * h)⁻¹ : GL6) : M6)ᵀ * w.mat * (((g * h)⁻¹ : GL6) : M6) =
      (((g⁻¹ : GL6) : M6))ᵀ * ((((h⁻¹ : GL6) : M6))ᵀ * w.mat * ((h⁻¹ : GL6) : M6)) *
        ((g⁻¹ : GL6) : M6)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem smul_mat (g : GL6) (w : Form6) :
    (g • w).mat = (((g⁻¹ : GL6) : M6))ᵀ * w.mat * ((g⁻¹ : GL6) : M6) := rfl

theorem inv_smul_mat (g : GL6) (w : Form6) :
    (g⁻¹ • w).mat = ((g : M6))ᵀ * w.mat * (g : M6) := by
  rw [smul_mat, inv_inv]

theorem mk_injective : Function.Injective Form6.mk := fun _ _ h => congrArg Form6.mat h

theorem ncard_mat_mem {l : List M6} (hl : l.Nodup) : {w : Form6 | w.mat ∈ l}.ncard = l.length := by
  classical
  have e : {w : Form6 | w.mat ∈ l} = ((l.map Form6.mk).toFinset : Set Form6) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨fun h => ⟨w.mat, h, rfl⟩, fun ⟨a, ha, e⟩ => by subst e; exact ha⟩
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hl.map mk_injective), List.length_map]

theorem flatMap_six (T : ℕ → List M6) :
    (List.range 6).flatMap T = T 0 ++ (T 1 ++ (T 2 ++ (T 3 ++ (T 4 ++ (T 5 ++ []))))) := by
  first
  | rfl
  | simp [List.range_succ]

theorem subset_sum_dvd : ∀ a ∈ [0, 315], ∀ b ∈ [0, 2880], ∀ c ∈ [0, 2880], ∀ d ∈ [0, 3780],
    ∀ e ∈ [0, 4032], 1 + a + b + c + d + e ∣ 13888 →
      1 + a + b + c + d + e = 1 ∨ 1 + a + b + c + d + e = 13888 := by
  decide

@[expose] noncomputable def W0 : Form6 := ⟨decN 6 w0c⟩

@[expose] noncomputable def Sbar : Subgroup GL6 := genSubN 6 sbGens

theorem validN_sbGens : ∀ g ∈ sbGens, ValidN 6 g := fun g hg =>
  validB_iff.mp ((by decide : ∀ g ∈ sbGens, validB 6 g = true) g hg)

theorem mem_orbit_of {s : GL6} {x : List ℕ}
    (e : decN 6 x = ((s : GL6) : M6)ᵀ * W0.mat * (s : M6)) :
    (⟨decN 6 x⟩ : Form6) ∈ MulAction.orbit GL6 W0 :=
  ⟨s⁻¹, Form6.ext (by rw [inv_smul_mat, e])⟩

theorem card_GL6 : Nat.card GL6 = 20158709760 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_stab_mul : Nat.card (MulAction.stabilizer GL6 W0) *
    (MulAction.orbit GL6 W0).ncard = 20158709760 := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index, card_GL6]

theorem length_flatMap_T {T : ℕ → List M6} (hT0 : T 0 = [W0.mat])
    (hsz : ∀ r < 5, (T (r + 1)).length = [315, 2880, 2880, 3780, 4032].getD r 0) :
    ((List.range 6).flatMap T).length = 13888 := by
  have h1 : (T 1).length = 315 := hsz 0 (by norm_num)
  have h2 : (T 2).length = 2880 := hsz 1 (by norm_num)
  have h3 : (T 3).length = 2880 := hsz 2 (by norm_num)
  have h4 : (T 4).length = 3780 := hsz 3 (by norm_num)
  have h5 : (T 5).length = 4032 := hsz 4 (by norm_num)
  rw [flatMap_six]
  simp [hT0, h1, h2, h3, h4, h5]

theorem mem_orbit_T {T : ℕ → List M6} (hT0 : T 0 = [W0.mat])
    (hT : ∀ r < 5, ∀ x ∈ T (r + 1), ∃ u : GL6, (u : M6) = decN 6 (grs.getD r []) ∧
      ∃ s ∈ Sbar, x = ((u * s : GL6) : M6)ᵀ * W0.mat * ((u * s : GL6) : M6)) :
    ∀ x ∈ (List.range 6).flatMap T, (⟨x⟩ : Form6) ∈ MulAction.orbit GL6 W0 := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
  rcases r with _ | r
  · rw [hT0, List.mem_singleton] at hxr
    rw [hxr]
    exact MulAction.mem_orbit_self W0
  · have hr' := List.mem_range.mp hr
    obtain ⟨u, -, s, -, e⟩ := hT r (by omega) x hxr
    exact ⟨(u * s)⁻¹, Form6.ext (by rw [inv_smul_mat]; exact e.symm)⟩

section Max


theorem form_parts :
    (∀ g ∈ sbGens, (decN 6 g)ᵀ * decN 6 w0c * decN 6 g = decN 6 w0c) ∧
    (∀ g ∈ sbGens ++ grs, ∃ u : GL6, (u : M6) = decN 6 g) ∧
    ∃ T : ℕ → List M6, T 0 = [W0.mat] ∧
      (∀ r < 5, (T (r + 1)).length = [315, 2880, 2880, 3780, 4032].getD r 0) ∧
      ((List.range 6).flatMap T).Nodup ∧
      ∀ r < 5, ∀ x ∈ T (r + 1), ∃ u : GL6, (u : M6) = decN 6 (grs.getD r []) ∧
        ∃ s ∈ Sbar, x = ((u * s : GL6) : M6)ᵀ * W0.mat * ((u * s : GL6) : M6) :=
  cert899108_parts.2.2.2.2

theorem sbar_le_stabilizer : Sbar ≤ MulAction.stabilizer GL6 W0 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  have hu' : colsN (u : M6) ∈ sbGens := hu
  rw [SetLike.mem_coe, ← inv_mem_iff, MulAction.mem_stabilizer_iff]
  ext1
  rw [inv_smul_mat, W0, ← decN_colsN (u : M6)]
  exact form_parts.1 _ hu'

theorem le_ncard_orbit : 13888 ≤ (MulAction.orbit GL6 W0).ncard := by
  obtain ⟨-, -, T, hT0, hsz, hnd, hT⟩ := form_parts
  have hsub : {w : Form6 | w.mat ∈ (List.range 6).flatMap T} ⊆ MulAction.orbit GL6 W0 :=
    fun w hw => mem_orbit_T hT0 hT w.mat hw
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [ncard_mat_mem hnd, length_flatMap_T hT0 hsz] at this

theorem stabilizer_eq (hcard : 1451520 ≤ Nat.card Sbar) :
    Nat.card Sbar = 1451520 ∧ Sbar = MulAction.stabilizer GL6 W0 ∧
      (MulAction.orbit GL6 W0).ncard = 13888 := by
  have h1 := card_stab_mul
  have h2 := le_ncard_orbit
  have h3 : Nat.card Sbar ≤ Nat.card (MulAction.stabilizer GL6 W0) :=
    Subgroup.card_le_of_le sbar_le_stabilizer
  have h4 : Nat.card (MulAction.stabilizer GL6 W0) ≤ 1451520 := by
    by_contra h
    have : 1451521 * 13888 ≤ Nat.card (MulAction.stabilizer GL6 W0) *
        (MulAction.orbit GL6 W0).ncard := Nat.mul_le_mul (by omega) h2
    omega
  have h5 : Nat.card Sbar = 1451520 := by omega
  have h6 : Nat.card (MulAction.stabilizer GL6 W0) = 1451520 := by omega
  have h7 : (MulAction.orbit GL6 W0).ncard = 13888 := by
    rw [h6] at h1
    omega
  exact ⟨h5, Subgroup.eq_of_le_of_card_ge sbar_le_stabilizer (by omega), h7⟩

theorem sbar_max (hcard : 1451520 ≤ Nat.card Sbar) {Z : Subgroup GL6} (hZ : Sbar ≤ Z) :
    Z = Sbar ∨ Z = ⊤ := by
  classical
  obtain ⟨-, hstab, horb⟩ := stabilizer_eq hcard
  obtain ⟨-, -, T, hT0, hsz, hnd, hT⟩ := form_parts
  have hLO : {w : Form6 | w.mat ∈ (List.range 6).flatMap T} = MulAction.orbit GL6 W0 := by
    have e := ncard_mat_mem hnd
    rw [length_flatMap_T hT0 hsz] at e
    exact Set.eq_of_subset_of_ncard_le (fun w hw => mem_orbit_T hT0 hT w.mat hw)
      (horb.trans e.symm).le (Set.toFinite _)
  have hsubZ : MulAction.orbit Z W0 ⊆ MulAction.orbit GL6 W0 := fun w hw => by
    obtain ⟨z, e⟩ := MulAction.mem_orbit_iff.mp hw
    exact MulAction.mem_orbit_iff.mpr ⟨(z : GL6), e⟩
  have hdvd : (MulAction.orbit Z W0).ncard ∣ 13888 := by
    have hst : MulAction.stabilizer Z W0 = Sbar.subgroupOf Z := by
      ext z
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hstab, Subgroup.smul_def]
    have h2 := Subgroup.relIndex_mul_index hZ
    have h3 : Sbar.index = 13888 := by rw [hstab, MulAction.index_stabilizer, horb]
    rw [← MulAction.index_stabilizer, hst]
    exact ⟨Z.index, by rw [← h3, ← h2, Subgroup.relIndex]⟩
  have hstable : ∀ s ∈ Sbar, ∀ w ∈ MulAction.orbit Z W0, s • w ∈ MulAction.orbit Z W0 := by
    intro s hs w hw
    obtain ⟨z, e⟩ := MulAction.mem_orbit_iff.mp hw
    exact MulAction.mem_orbit_iff.mpr ⟨⟨s, hZ hs⟩ * z,
      (mul_smul _ _ _).trans (congrArg (fun v => (⟨s, hZ hs⟩ : Z) • v) e)⟩
  have hall : ∀ r < 5, (∃ x ∈ T (r + 1), (⟨x⟩ : Form6) ∈ MulAction.orbit Z W0) →
      ∀ x ∈ T (r + 1), (⟨x⟩ : Form6) ∈ MulAction.orbit Z W0 := by
    rintro r hr ⟨y, hy, hyZ⟩ x hx
    obtain ⟨u, hu, s, hs, e⟩ := hT r hr x hx
    obtain ⟨u', hu', s', hs', e'⟩ := hT r hr y hy
    have huu : u' = u := Units.ext (hu'.trans hu.symm)
    rw [huu] at e'
    have ex : (⟨x⟩ : Form6) = (u * s)⁻¹ • W0 := Form6.ext (by rw [inv_smul_mat]; exact e)
    have ey : (⟨y⟩ : Form6) = (u * s')⁻¹ • W0 := Form6.ext (by rw [inv_smul_mat]; exact e')
    have hxy : (⟨x⟩ : Form6) = (s⁻¹ * s') • (⟨y⟩ : Form6) := by
      rw [ex, ey, ← mul_smul]
      congr 1
      group
    rw [hxy]
    exact hstable _ (mul_mem (inv_mem hs) hs') _ hyZ
  obtain ⟨p, hp⟩ : ∃ p : M6 → Bool, ∀ m, p m = true ↔ (⟨m⟩ : Form6) ∈ MulAction.orbit Z W0 :=
    ⟨fun m => decide ((⟨m⟩ : Form6) ∈ MulAction.orbit Z W0), fun _ => decide_eq_true_iff⟩
  have hc : ∀ r < 5, ((T (r + 1)).filter p).length = 0 ∨
      ((T (r + 1)).filter p).length = [315, 2880, 2880, 3780, 4032].getD r 0 := by
    intro r hr
    by_cases h : ∃ x ∈ T (r + 1), (⟨x⟩ : Form6) ∈ MulAction.orbit Z W0
    · right
      have hf : (T (r + 1)).filter p = T (r + 1) :=
        List.filter_eq_self.mpr fun x hx => (hp x).mpr (hall r hr h x hx)
      rw [hf, hsz r hr]
    · left
      have hf : (T (r + 1)).filter p = [] :=
        List.filter_eq_nil_iff.mpr fun x hx hpx => h ⟨x, hx, (hp x).mp hpx⟩
      rw [hf, List.length_nil]
  have hp0 : p W0.mat = true := (hp _).mpr (MulAction.mem_orbit_self W0)
  have c0 : ((T 0).filter p).length = 1 := by
    rw [hT0, List.filter_cons_of_pos hp0, List.filter_nil, List.length_singleton]
  have c1 : ((T 1).filter p).length = 0 ∨ ((T 1).filter p).length = 315 := hc 0 (by norm_num)
  have c2 : ((T 2).filter p).length = 0 ∨ ((T 2).filter p).length = 2880 := hc 1 (by norm_num)
  have c3 : ((T 3).filter p).length = 0 ∨ ((T 3).filter p).length = 2880 := hc 2 (by norm_num)
  have c4 : ((T 4).filter p).length = 0 ∨ ((T 4).filter p).length = 3780 := hc 3 (by norm_num)
  have c5 : ((T 5).filter p).length = 0 ∨ ((T 5).filter p).length = 4032 := hc 4 (by norm_num)
  have hOZ : MulAction.orbit Z W0 = {w : Form6 | w.mat ∈ ((List.range 6).flatMap T).filter p} := by
    ext w
    rw [Set.mem_setOf_eq, List.mem_filter]
    constructor
    · intro hw
      have hwO := hsubZ hw
      rw [← hLO] at hwO
      exact ⟨hwO, (hp _).mpr hw⟩
    · rintro ⟨-, hw⟩
      exact (hp _).mp hw
  have hlenZ := ncard_mat_mem (hnd.filter p)
  rw [← hOZ, flatMap_six] at hlenZ
  simp only [List.filter_append, List.length_append, List.filter_nil, List.length_nil] at hlenZ
  have hsum : (MulAction.orbit Z W0).ncard = 1 + ((T 1).filter p).length +
      ((T 2).filter p).length + ((T 3).filter p).length + ((T 4).filter p).length +
      ((T 5).filter p).length := by omega
  have m1 : ((T 1).filter p).length ∈ [0, 315] := by rcases c1 with h | h <;> simp [h]
  have m2 : ((T 2).filter p).length ∈ [0, 2880] := by rcases c2 with h | h <;> simp [h]
  have m3 : ((T 3).filter p).length ∈ [0, 2880] := by rcases c3 with h | h <;> simp [h]
  have m4 : ((T 4).filter p).length ∈ [0, 3780] := by rcases c4 with h | h <;> simp [h]
  have m5 : ((T 5).filter p).length ∈ [0, 4032] := by rcases c5 with h | h <;> simp [h]
  rw [hsum] at hdvd
  rcases subset_sum_dvd _ m1 _ m2 _ m3 _ m4 _ m5 hdvd with key | key <;> rw [← hsum] at key
  ·
    left
    refine le_antisymm (fun z hz => ?_) hZ
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp key
    have h1 : (⟨z, hz⟩ : Z) • W0 ∈ MulAction.orbit Z W0 := MulAction.mem_orbit _ _
    have h0 : W0 ∈ MulAction.orbit Z W0 := MulAction.mem_orbit_self W0
    rw [ha, Set.mem_singleton_iff] at h1 h0
    have hzW : z • W0 = W0 := (h1.trans h0.symm : (⟨z, hz⟩ : Z) • W0 = W0)
    rw [hstab]
    exact hzW
  right
  have hZO : MulAction.orbit Z W0 = MulAction.orbit GL6 W0 :=
    Set.eq_of_subset_of_ncard_le hsubZ (horb.trans key.symm).le (Set.toFinite _)
  rw [eq_top_iff]
  intro y _
  have hy : y⁻¹ • W0 ∈ MulAction.orbit Z W0 := by
    rw [hZO]
    exact MulAction.mem_orbit _ _
  obtain ⟨z, e⟩ := MulAction.mem_orbit_iff.mp hy
  have e' : (z : GL6) • W0 = y⁻¹ • W0 := e
  have h2 : y * (z : GL6) ∈ MulAction.stabilizer GL6 W0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, e', smul_inv_smul]
  rw [← hstab] at h2
  have h3 : y = (y * (z : GL6)) * (z : GL6)⁻¹ := by group
  rw [h3]
  exact mul_mem (hZ h2) (inv_mem z.2)

end Max

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
