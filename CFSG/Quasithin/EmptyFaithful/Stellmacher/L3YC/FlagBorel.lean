module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF3

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

section Linear

variable {F : Type} [Field F] [Fintype F]

abbrev glAct (g : GL (Fin 3) F) (x : Fin 3 → F) : Fin 3 → F :=
  (g : Matrix (Fin 3) (Fin 3) F).mulVec x

omit [Fintype F] in
theorem glAct_mul (g h : GL (Fin 3) F) (x : Fin 3 → F) : glAct (g * h) x = glAct g (glAct h x) := by
  simp [glAct, Matrix.mulVec_mulVec]

omit [Fintype F] in
theorem glAct_one (x : Fin 3 → F) : glAct (1 : GL (Fin 3) F) x = x := by
  simp [glAct]

omit [Fintype F] in
theorem gl_ext {g₁ g₂ : GL (Fin 3) F} (h : ∀ x, glAct g₁ x = glAct g₂ x) : g₁ = g₂ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrFun (h (Pi.single j (1 : F))) i
  simpa [glAct, Matrix.mulVec_single_one] using this

omit [Fintype F] in
theorem glAct_injective (g : GL (Fin 3) F) {x y : Fin 3 → F} (h : glAct g x = glAct g y) : x = y := by
  have := congrArg (glAct g⁻¹) h
  rwa [← glAct_mul, ← glAct_mul, inv_mul_cancel, glAct_one, glAct_one] at this

omit [Fintype F] in
theorem exists_gl_of_linear (f f' : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) (h1 : ∀ x, f (f' x) = x)
    (h2 : ∀ x, f' (f x) = x) : ∃ g : GL (Fin 3) F, ∀ x, glAct g x = f x := by
  let u : LinearMap.GeneralLinearGroup F (Fin 3 → F) :=
    ⟨f, f', LinearMap.ext h1, LinearMap.ext h2⟩
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm u, fun x => ?_⟩
  have h := Matrix.GeneralLinearGroup.toLin_apply (Matrix.GeneralLinearGroup.toLin.symm u) x
  rw [MulEquiv.apply_symm_apply] at h
  rw [glAct, ← Matrix.mulVecLin_apply]
  exact h.symm

theorem exists_flag_data (hF : Fintype.card F = 2) {W : AddSubgroup (Fin 3 → F)}
    (hW : Nat.card W = 4) {a : Fin 3 → F} (haW : a ∈ W) (ha0 : a ≠ 0) :
    ∃ g b : GL (Fin 3) F, orderOf g = 3 ∧ glAct g a = a ∧ (∃ w ∈ W, glAct g w ∉ W) ∧
      glAct b a = a ∧ (∀ w ∈ W, glAct b w ∈ W) ∧ b * g * b⁻¹ = g⁻¹ ∧
      ∀ D : Subgroup (GL (Fin 3) F), Nat.card D = 8 →
        (∀ h ∈ D, glAct h a = a ∧ ∀ w ∈ W, glAct h w ∈ W) → b ∈ D := by
  classical
  have hc01 := Stellmacher.PU.L3YC.eq_zero_or_one_of_card_two hF
  have h2 : (2 : F) = 0 := by
    have : (1 : F) + 1 = 0 := by
      rcases hc01 ((1 : F) + 1) with h | h
      · exact h
      · exact absurd (add_eq_right.mp h) one_ne_zero
    rw [← one_add_one_eq_two]
    exact this
  have hdbl : ∀ x : Fin 3 → F, x + x = 0 := fun x => by
    rw [← two_smul F x, h2, zero_smul]
  have hneg : ∀ x : Fin 3 → F, -x = x := fun x => neg_eq_of_add_eq_zero_right (hdbl x)
  have hWcard : (W : Set (Fin 3 → F)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hW
  have hall : Nat.card (Fin 3 → F) = 8 := by
    rw [Nat.card_pi]
    simp [Nat.card_eq_fintype_card, hF]
  obtain ⟨w, hwW, hw0, hwa⟩ : ∃ w ∈ W, w ≠ 0 ∧ w ≠ a := by
    by_contra hcon
    have hsub : (W : Set (Fin 3 → F)) ⊆ {0, a} := by
      intro x hx
      by_contra hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx'
      exact hcon ⟨x, hx, hx'.1, hx'.2⟩
    have h2' : (W : Set (Fin 3 → F)).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans (by simp))
    omega
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → F, v ∉ W := by
    by_contra hcon
    push Not at hcon
    have hall' : W = ⊤ := top_unique fun x _ => hcon x
    have : Nat.card W = Nat.card (Fin 3 → F) := by
      rw [hall']
      exact Nat.card_congr (AddSubgroup.topEquiv).toEquiv
    rw [hall, hW] at this
    omega
  have hav : a + v ∉ W := fun h => hv (by
    have := W.sub_mem h haW
    simpa using this)
  have hwv : w + v ∉ W := fun h => hv (by
    have := W.sub_mem h hwW
    simpa using this)
  have hawv' : a + w + v ∉ W := fun h => hv (by
    have := W.sub_mem (W.sub_mem h haW) hwW
    simpa [sub_add_eq_sub_sub, add_assoc] using this)
  have hWeq : (W : Set (Fin 3 → F)) = {0, a, w, w + a} := by
    have hwa' : w + a ≠ 0 := fun h => hwa (by
      have := eq_neg_of_add_eq_zero_left h
      rw [this, hneg])
    have hsub : ({0, a, w, w + a} : Set (Fin 3 → F)) ⊆ (W : Set (Fin 3 → F)) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact W.zero_mem
      · exact haW
      · exact hwW
      · exact W.add_mem hwW haW
    have hc4 : ({0, a, w, w + a} : Set (Fin 3 → F)).ncard = 4 := by
      have h0a : (0 : Fin 3 → F) ≠ a := fun h => ha0 h.symm
      have h0w : (0 : Fin 3 → F) ≠ w := fun h => hw0 h.symm
      have haw : a ≠ w := fun h => hwa h.symm
      have hawa : a ≠ w + a := fun h => hw0 (by
        have := congrArg (fun u => u - a) h
        simpa using this.symm)
      have hww : w ≠ w + a := fun h => ha0 (by
        have := congrArg (fun u => u - w) h
        simpa using this.symm)
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hww]
      · simp [haw, hawa]
      · simp [h0a, h0w, Ne.symm hwa']
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hc4, hWcard]) (Set.toFinite _)).symm
  have hli : LinearIndependent F ![a, w, v] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • a + c 1 • w + c 2 • v = 0 := by
      simpa [Fin.sum_univ_three] using hc
    clear hc
    have key : c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 := by
      rcases hc01 (c 0) with h0 | h0 <;> rcases hc01 (c 1) with h1 | h1 <;>
        rcases hc01 (c 2) with h2' | h2' <;>
        simp only [h0, h1, h2', zero_smul, one_smul, add_zero, zero_add] at hc' ⊢
      · exact ⟨trivial, trivial, trivial⟩
      · exact absurd (by rw [hc']; exact W.zero_mem) hv
      · exact absurd hc' hw0
      · exact absurd (by rw [hc']; exact W.zero_mem) hwv
      · exact absurd hc' ha0
      · exact absurd (by rw [hc']; exact W.zero_mem) hav
      · exact absurd (hneg a ▸ eq_neg_of_add_eq_zero_right hc') hwa
      · exact absurd (by rw [hc']; exact W.zero_mem) hawv'
    intro i
    fin_cases i
    · exact key.1
    · exact key.2.1
    · exact key.2.2
  have hcard : Fintype.card (Fin 3) = Module.finrank F (Fin 3 → F) := by simp
  let bs : Module.Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbs : ∀ i, bs i = ![a, w, v] i := fun i => by
    simp [bs, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hbs0 : bs 0 = a := by rw [hbs]; rfl
  have hbs1 : bs 1 = w := by rw [hbs]; rfl
  have hbs2 : bs 2 = v := by rw [hbs]; rfl
  obtain ⟨fg, hfga, hfgw, hfgv⟩ : ∃ f : (Fin 3 → F) →ₗ[F] (Fin 3 → F),
      f a = a ∧ f w = v ∧ f v = w + v := by
    refine ⟨bs.constr F ![a, v, w + v], ?_, ?_, ?_⟩
    · have h : (bs.constr F ![a, v, w + v]) (bs 0) = ![a, v, w + v] 0 := bs.constr_basis F _ 0
      rw [hbs0] at h; simpa using h
    · have h : (bs.constr F ![a, v, w + v]) (bs 1) = ![a, v, w + v] 1 := bs.constr_basis F _ 1
      rw [hbs1] at h; simpa using h
    · have h : (bs.constr F ![a, v, w + v]) (bs 2) = ![a, v, w + v] 2 := bs.constr_basis F _ 2
      rw [hbs2] at h; simpa using h
  obtain ⟨fb, hfba, hfbw, hfbv⟩ : ∃ f : (Fin 3 → F) →ₗ[F] (Fin 3 → F),
      f a = a ∧ f w = w ∧ f v = v + w := by
    refine ⟨bs.constr F ![a, w, v + w], ?_, ?_, ?_⟩
    · have h : (bs.constr F ![a, w, v + w]) (bs 0) = ![a, w, v + w] 0 := bs.constr_basis F _ 0
      rw [hbs0] at h; simpa using h
    · have h : (bs.constr F ![a, w, v + w]) (bs 1) = ![a, w, v + w] 1 := bs.constr_basis F _ 1
      rw [hbs1] at h; simpa using h
    · have h : (bs.constr F ![a, w, v + w]) (bs 2) = ![a, w, v + w] 2 := bs.constr_basis F _ 2
      rw [hbs2] at h; simpa using h
  have hgw1 : fg (w + v) = w := by
    rw [map_add, hfgw, hfgv, add_comm w v, ← add_assoc, hdbl, zero_add]
  have hbw1 : fb (v + w) = v := by
    rw [map_add, hfbv, hfbw, add_assoc, hdbl, add_zero]
  have hfg3 : ∀ x, fg (fg (fg x)) = x := by
    intro x
    have : fg ∘ₗ fg ∘ₗ fg = LinearMap.id := by
      apply bs.ext
      intro i
      fin_cases i
      · simp [hbs0, hfga]
      · simp [hbs1, hfgw, hfgv, hgw1]
      · simp [hbs2, hfgv, hgw1, hfgw]
    exact LinearMap.congr_fun this x
  have hfb2 : ∀ x, fb (fb x) = x := by
    intro x
    have : fb ∘ₗ fb = LinearMap.id := by
      apply bs.ext
      intro i
      fin_cases i
      · simp [hbs0, hfba]
      · simp [hbs1, hfbw]
      · simp [hbs2, hfbv, hbw1]
    exact LinearMap.congr_fun this x
  have hrel : ∀ x, fb x = fg (fb (fg x)) := by
    intro x
    have : fb = fg ∘ₗ fb ∘ₗ fg := by
      apply bs.ext
      intro i
      fin_cases i
      · simp [hbs0, hfga, hfba]
      · simp [hbs1, hfgw, hfbv, hfbw, hfgv]
        rw [add_assoc, hdbl, add_zero]
      · simp [hbs2, hfgw, hfbv, hfbw, hfgv]
        rw [add_assoc, hdbl, add_zero]
    exact LinearMap.congr_fun this x
  obtain ⟨g, hg⟩ := exists_gl_of_linear fg (fg ∘ₗ fg) (fun x => hfg3 x) (fun x => hfg3 x)
  obtain ⟨b, hb⟩ := exists_gl_of_linear fb fb hfb2 hfb2
  have hg3 : g ^ 3 = 1 := by
    apply gl_ext
    intro x
    rw [pow_three', glAct_mul, glAct_mul, hg, hg, hg, glAct_one]
    exact hfg3 x
  have hg1 : g ≠ 1 := by
    intro h
    have := hg w
    rw [h, glAct_one, hfgw] at this
    exact hv (this ▸ hwW)
  have hbb : b * b = 1 := by
    apply gl_ext
    intro x
    rw [glAct_mul, hb, hb, glAct_one]
    exact hfb2 x
  have hbgbg : b * g * b * g = 1 := by
    apply gl_ext
    intro x
    rw [glAct_mul, glAct_mul, glAct_mul, hg, hb, hg, hb, ← hrel, hfb2, glAct_one]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hrelgl : b * g * b⁻¹ = g⁻¹ := by
    rw [hbi]; exact eq_inv_of_mul_eq_one_left hbgbg
  have hbW : ∀ x ∈ W, glAct b x ∈ W := by
    intro x hx
    have hx' : x ∈ ({0, a, w, w + a} : Set (Fin 3 → F)) := hWeq ▸ hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rw [hb]
    rcases hx' with rfl | rfl | rfl | rfl
    · rw [map_zero]; exact W.zero_mem
    · rw [hfba]; exact haW
    · rw [hfbw]; exact hwW
    · rw [map_add, hfbw, hfba]; exact W.add_mem hwW haW
  refine ⟨g, b, orderOf_eq_prime hg3 hg1, ?_, ⟨w, hwW, ?_⟩, ?_, hbW, hrelgl, ?_⟩
  · rw [hg, hfga]
  · rw [hg, hfgw]; exact hv
  · rw [hb, hfba]
  · intro D hD8 hD
    let T : Set (GL (Fin 3) F) := {h | glAct h a = a ∧ ∀ x ∈ W, glAct h x ∈ W}
    have hTmaps : ∀ h ∈ T, glAct h w ∈ ({w, w + a} : Set (Fin 3 → F)) ∧
        glAct h v ∈ ((W : Set (Fin 3 → F))ᶜ) := by
      intro h ⟨hha, hhW⟩
      refine ⟨?_, ?_⟩
      · have h1 : glAct h w ∈ (W : Set (Fin 3 → F)) := hhW w hwW
        rw [hWeq] at h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
        rcases h1 with h1 | h1 | h1 | h1
        · exfalso
          apply hw0
          apply glAct_injective h
          rw [h1]
          have : glAct h 0 = 0 := by simp [glAct]
          rw [this]
        · exfalso
          apply hwa
          apply glAct_injective h
          rw [h1, hha]
        · exact Or.inl h1
        · exact Or.inr h1
      · intro hvW
        have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite (W : Set (Fin 3 → F)))
          (f := glAct h) (fun x hx => hhW x hx)).mp (fun x _ y _ hxy => glAct_injective h hxy)
        obtain ⟨x, hxW, hxv⟩ := hbij.surjOn hvW
        have : x = v := glAct_injective h hxv
        exact hv (this ▸ hxW)
    have hTinj : Set.InjOn (fun h : GL (Fin 3) F => (glAct h w, glAct h v)) T := by
      intro h₁ h₁T h₂ h₂T heq
      simp only [Prod.mk.injEq] at heq
      apply gl_ext
      intro x
      have hlin : (Matrix.mulVecLin (h₁ : Matrix (Fin 3) (Fin 3) F)) =
          Matrix.mulVecLin (h₂ : Matrix (Fin 3) (Fin 3) F) := by
        apply bs.ext
        intro i
        fin_cases i
        · simp only [Matrix.mulVecLin_apply]
          have := hbs0
          simp only [Fin.zero_eta] at this ⊢
          rw [this]
          exact h₁T.1.trans h₂T.1.symm
        · simp only [Matrix.mulVecLin_apply]
          simp only [Fin.mk_one] at *
          rw [hbs1]
          exact heq.1
        · simp only [Matrix.mulVecLin_apply]
          rw [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl, hbs2]
          exact heq.2
      exact LinearMap.congr_fun hlin x
    have hTle : T.ncard ≤ 8 := by
      have hmaps : Set.MapsTo (fun h : GL (Fin 3) F => (glAct h w, glAct h v)) T
          (({w, w + a} : Set (Fin 3 → F)) ×ˢ ((W : Set (Fin 3 → F))ᶜ)) :=
        fun h hh => ⟨(hTmaps h hh).1, (hTmaps h hh).2⟩
      have h1 := Set.ncard_le_ncard_of_injOn _ hmaps hTinj (Set.toFinite _)
      rw [Set.ncard_prod] at h1
      have h2 : ({w, w + a} : Set (Fin 3 → F)).ncard ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by simp)
      have h3 : ((W : Set (Fin 3 → F))ᶜ).ncard = 4 := by
        have := Set.ncard_add_ncard_compl (W : Set (Fin 3 → F)) (Set.toFinite _) (Set.toFinite _)
        rw [hall] at this
        omega
      rw [h3] at h1
      omega
    have hDT : (D : Set (GL (Fin 3) F)) ⊆ T := fun h hh => hD h hh
    have hDcard : (D : Set (GL (Fin 3) F)).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]; exact hD8
    have hDeq : (D : Set (GL (Fin 3) F)) = T :=
      Set.eq_of_subset_of_ncard_le hDT (by rw [hDcard]; exact hTle) (Set.toFinite _)
    have hbT : b ∈ T := ⟨by rw [hb, hfba], hbW⟩
    rw [← hDeq] at hbT
    exact hbT

end Linear

end Stellmacher.L3YC

end CFSG.Quasithin
