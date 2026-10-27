module

public import CFSG.Sporadic.Co2Smith.GlRootD1Fix

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

@[expose] noncomputable def d1BGk (g : ℕ) : K :=
  if g < 5 then glE (Native.d1MarkWords.getD g []) else if g == 5 then α3K
  else xRootK (Native.d1BRoot g) (Native.d1BPar g)

@[expose] noncomputable def d1BTk (ν : List ℕ) (g : ℕ) : K :=
  if g < 6 then d1BGk g
  else xRootK (Native.d1BRoot g) (Native.f4mul (Native.d1Nu ν (Native.d1BRoot g)) (Native.d1BPar g))

theorem d1Mark_letters {g : ℕ} (hg : g < 5) :
    ∀ k ∈ Native.d1MarkWords.getD g [], k < 22 :=
  fun k hk => lt_of_mem_glC0Let ((d1Elt_spec.2.2.2.2.2.2.2 g hg).1 k hk)

theorem d1BGk_val (g : ℕ) :
    (d1BGk g).val.val = rowsMatrix 22 (Native.d1BG g) := by
  unfold d1BGk Native.d1BG
  split_ifs with h5 h5'
  · exact glE_val (d1Mark_letters h5)
  · exact α3K_val
  · exact xRootK_val _ _

theorem d1BTk_val (ν : List ℕ) (g : ℕ) :
    (d1BTk ν g).val.val = rowsMatrix 22 (Native.d1BT ν g) := by
  unfold d1BTk Native.d1BT
  split_ifs
  · exact d1BGk_val g
  · exact xRootK_val _ _

theorem d1BRoot_mem (g : ℕ) : Native.d1BRoot g ∈ [0, 1, 2, 4, 5] := by
  unfold Native.d1BRoot
  split_ifs <;> simp

theorem d1BPar_mem (g : ℕ) : Native.d1BPar g ∈ [1, 2, 3] := by
  unfold Native.d1BPar
  split_ifs <;> simp

theorem d1Mark_mem {g : ℕ}
    (hg : g < 5) : glE (Native.d1MarkWords.getD g []) ∈ Ax25 ∧
      glE (Native.d1MarkWords.getD g []) ∈ C0c := by
  have h := d1Elt_spec.2.2.2.2.2.2.2 g hg
  refine ⟨mem_Ax25.2 ⟨mem_Cz_of_comm (comm_of_commRows (glE_val (d1Mark_letters hg)) z0_val'
    h.2.1), comm_of_commRows (glE_val (d1Mark_letters hg)) x25K_val h.2.2⟩,
    glE_mem_C0c h.1⟩

theorem d1BGk_mem
    (g : ℕ) : d1BGk g ∈ Ax25 := by
  unfold d1BGk
  split_ifs with h5 h5'
  · exact (d1Mark_mem h5).1
  · exact α3K_mem_Ax25
  · have := d1BPar_mem g
    exact xRootK_mem_Ax25 (d1BRoot_mem g) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this; omega)

theorem f4mul_one_left : ∀ t ∈ [1, 2, 3], Native.f4mul 1 t = t := by decide

theorem chartD_d1BGk
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz)
    {ν₁ ν₂ ν₄ ν₅ : ℕ} (h0 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 0 t) = xRootK 0 t)
    (h1 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 1 t) = xRootK 1 (Native.f4mul ν₁ t))
    (h2 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 2 t) = xRootK 2 (Native.f4mul ν₂ t))
    (h4 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 4 t) = xRootK 4 (Native.f4mul ν₄ t))
    (h5 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 5 t) = xRootK 5 (Native.f4mul ν₅ t)) (g : ℕ) :
    chartD φ ρ (d1BGk g) = d1BTk [ν₁, ν₂, ν₄, ν₅] g := by
  unfold d1BTk
  split_ifs with h6
  · unfold d1BGk
    split_ifs with h5' h5''
    · exact chartD_of_mem_C0c hm hφz (d1Mark_mem h5').1 (d1Mark_mem h5').2
    · exact chartD_α3K hm hφz
    · exfalso
      simp only [beq_iff_eq] at h5''
      omega
  · have e : d1BGk g = xRootK (Native.d1BRoot g) (Native.d1BPar g) := by
      unfold d1BGk
      rw [ite_eq_right (by omega), ite_eq_right (by simp only [beq_iff_eq]; omega)]
    rw [e]
    have hp := d1BPar_mem g
    have hr := d1BRoot_mem g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr | hr <;> rw [hr]
    · rw [h0 _ hp, show Native.d1Nu [ν₁, ν₂, ν₄, ν₅] 0 = 1 from rfl, f4mul_one_left _ hp]
    · rw [h1 _ hp]
      rfl
    · rw [h2 _ hp]
      rfl
    · rw [h4 _ hp]
      rfl
    · rw [h5 _ hp]
      rfl

theorem d1Break_spec :
    ∀ a ∈ [1, 2, 3], ∀ b ∈ [1, 2, 3], ∀ c ∈ [1, 2, 3], ∀ d ∈ [1, 2, 3],
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨ ∃ e ∈ Native.d1Break, e.1 = [a, b, c, d] ∧
        Native.d1WR Native.d1BG e.2.1 = Native.d1WR Native.d1BG e.2.2 ∧
        Native.d1WR (Native.d1BT [a, b, c, d]) e.2.1 ≠
          Native.d1WR (Native.d1BT [a, b, c, d]) e.2.2 ∧
        Native.validM (Native.d1WR (Native.d1BT [a, b, c, d]) e.2.1) = true ∧
        Native.validM (Native.d1WR (Native.d1BT [a, b, c, d]) e.2.2) = true := by
  have h := d1_parts.2.2.2.2.2.2.2.2
  simp only [Native.d1BreakOK, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq, and_assoc] at h
  exact h

theorem d1Word_val (w : List ℕ) :
    ((w.map d1BGk).prod).val.val = rowsMatrix 22 (Native.d1WR Native.d1BG w) :=
  prod_map_val d1BGk Native.d1BG d1BGk_val w

theorem d1TWord_val (ν w : List ℕ) :
    ((w.map (d1BTk ν)).prod).val.val = rowsMatrix 22 (Native.d1WR (Native.d1BT ν) w) :=
  prod_map_val (d1BTk ν) (Native.d1BT ν) (d1BTk_val ν) w

theorem twist_trivial
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz)
    {ν₁ ν₂ ν₄ ν₅ : ℕ} (hν₁ : ν₁ ∈ [1, 2, 3]) (hν₂ : ν₂ ∈ [1, 2, 3]) (hν₄ : ν₄ ∈ [1, 2, 3])
    (hν₅ : ν₅ ∈ [1, 2, 3]) (h0 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 0 t) = xRootK 0 t)
    (h1 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 1 t) = xRootK 1 (Native.f4mul ν₁ t))
    (h2 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 2 t) = xRootK 2 (Native.f4mul ν₂ t))
    (h4 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 4 t) = xRootK 4 (Native.f4mul ν₄ t))
    (h5 : ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK 5 t) = xRootK 5 (Native.f4mul ν₅ t)) :
    ν₁ = 1 ∧ ν₂ = 1 ∧ ν₄ = 1 ∧ ν₅ = 1 := by
  rcases d1Break_spec ν₁ hν₁ ν₂ hν₂ ν₄ hν₄ ν₅ hν₅ with h | ⟨e, -, -, heq, hne, hv1, hv2⟩
  · exact h
  · exfalso
    have hw : (e.2.1.map d1BGk).prod = (e.2.2.map d1BGk).prod :=
      eq_of_val_rows (d1Word_val _) (d1Word_val _) heq
    have hD := congrArg (chartD φ ρ) hw
    have hmem : ∀ w : List ℕ, ∀ x ∈ w.map d1BGk, x ∈ Ax25 := fun w x hx => by
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact d1BGk_mem g
    rw [chartD_list_prod hm hφz _ (hmem _), chartD_list_prod hm hφz _ (hmem _), List.map_map,
      List.map_map] at hD
    have hfun : chartD φ ρ ∘ d1BGk = d1BTk [ν₁, ν₂, ν₄, ν₅] :=
      funext (chartD_d1BGk hm hφz h0 h1 h2 h4 h5)
    rw [hfun] at hD
    exact hne (eq_of_rowsMatrix_eq hv1 hv2 (by rw [← d1TWord_val, ← d1TWord_val, hD]))

theorem d1_root_cases : ∀ r < 18, ∀ t ∈ [1, 2, 3], Native.glInChart r 0 = true →
    Native.glInChart (Native.glWAct 4 r t).1 0 = true → r ∈ [0, 1, 2, 4, 5, 12, 13, 14, 17] := by
  decide

theorem glWAct4_par : ∀ r < 18, ∀ t ∈ [1, 2, 3], (Native.glWAct 4 r t).2 ∈ [1, 2, 3] := by
  decide

theorem glWAct4_zero : ∀ t ∈ [1, 2, 3], Native.glWAct 4 0 t = (0, t) := by
  decide

theorem xRootK_long {r t : ℕ} (hr : 12 ≤ r) (ht : t ≠ 0) : xRootK r t = xLongK (r - 12) := by
  have ht' : (t == 0) = false := by simpa using ht
  simp only [xRootK, ht', Bool.false_eq_true, ite_false, show ¬ r < 6 by omega,
    show ¬ r < 12 by omega]

theorem xLongK_mem_C0c {k : ℕ} (hk : k ∈ [0, 1, 2, 5]) :
    xLongK k ∈ C0c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact x16K_mem_C0c
  · exact x25K_mem_C0c
  · exact x34K_mem_C0c
  · exact x43K_mem_C0c

theorem chartT_root
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) {y : K} (hy : y ∈ rootSet)
    (hyA : y ∈ Ax25) : chartT φ ρ y = δ1hK * y * δ1hK := by
  obtain ⟨r, hr, t, ht4, rfl⟩ := hy
  by_cases ht0 : t = 0
  · subst ht0
    rw [xRootK_zero_eq, chartT_one hm hφz, mul_one, δ1hK_mul_self]
  have ht : t ∈ [1, 2, 3] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have hc0 := inChart_of_mem_Cz hr ht (mem_Ax25.1 hyA).1
  have hc1 : Native.glInChart (Native.glWAct 4 r t).1 0 = true := by
    have h := conj_δ1hK_mem_Cz_of_Ax25 hyA
    rw [δ1hK_conj_xRootK hr ht4] at h
    exact inChart_of_mem_Cz (glWeyl_spec 4 (by norm_num) r hr t ht4).1 (glWAct4_par r hr t ht) h
  have hcase := d1_root_cases r hr t ht hc0 hc1
  obtain ⟨ν₁, hν₁, hr₁⟩ := chartD_rot hm hφz (r := 1) (by simp)
  obtain ⟨ν₂, hν₂, hr₂⟩ := chartD_rot hm hφz (r := 2) (by simp)
  obtain ⟨ν₄, hν₄, hr₄⟩ := chartD_rot hm hφz (r := 4) (by simp)
  obtain ⟨ν₅, hν₅, hr₅⟩ := chartD_rot hm hφz (r := 5) (by simp)
  have h0 : ∀ s ∈ [1, 2, 3], chartD φ ρ (xRootK 0 s) = xRootK 0 s := fun s hs => by
    rw [chartD, chartT_xRootK_15 hm hφz hs, δ1hK_conj_xRootK (by norm_num) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; omega), glWAct4_zero s hs]
  obtain ⟨e₁, e₂, e₄, e₅⟩ := twist_trivial hm hφz hν₁ hν₂ hν₄ hν₅ h0 hr₁ hr₂ hr₄ hr₅
  have hfix : ∀ r' ∈ [1, 2, 4, 5], ∀ s ∈ [1, 2, 3], chartD φ ρ (xRootK r' s) = xRootK r' s := by
    intro r' hr' s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · rw [hr₁ s hs, e₁, f4mul_one_left s hs]
    · rw [hr₂ s hs, e₂, f4mul_one_left s hs]
    · rw [hr₄ s hs, e₄, f4mul_one_left s hs]
    · rw [hr₅ s hs, e₅, f4mul_one_left s hs]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcase
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chartT_eq_of_chartD (h0 t ht)
  · exact chartT_eq_of_chartD (hfix 1 (by simp) t ht)
  · exact chartT_eq_of_chartD (hfix 2 (by simp) t ht)
  · exact chartT_eq_of_chartD (hfix 4 (by simp) t ht)
  · exact chartT_eq_of_chartD (hfix 5 (by simp) t ht)
  all_goals
    rw [xRootK_long (by norm_num) ht0] at hyA ⊢
    exact chartT_of_mem_C0c hm hφz hyA (xLongK_mem_C0c (by simp))

theorem d1Core_holds
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) : D1Core φ ρ :=
  d1Core_of_chartT hm (phi_zC_of_ne_one φ hz) fun _ hyR hyA =>
    chartT_root hm (phi_zC_of_ne_one φ hz) hyR hyA

end CFSG.Sporadic.Co2Smith
