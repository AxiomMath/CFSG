module

public import CFSG.Quasithin.H13.A5W1618a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Matrix commutatorElement

local notation "StSL" => Assembly.LowTwoRank.StatedSL

section SL2

variable {K : Type} [Field K]

@[expose] def unip (x : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lunip (x : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def tor (μ : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![(μ : K), 0; 0, ((μ⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem coe_unip (x : K) :
    ((unip x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] :=
  rfl

theorem coe_lunip (x : K) :
    ((lunip x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; x, 1] :=
  rfl

theorem coe_tor (μ : Kˣ) :
    ((tor μ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(μ : K), 0; 0, ((μ⁻¹ : Kˣ) : K)] :=
  rfl

theorem tor_inv (μ : Kˣ) : tor μ⁻¹ = (tor μ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tor, coe_tor, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def slOf : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(StSL 2 K) where
  toFun s := ⟨Matrix.SpecialLinearGroup.toGL s, Subgroup.subset_closure (by
    show ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact s.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' s t := Subtype.ext (map_mul _ s t)

theorem sl2Mat_slOf (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    sl2Mat (slOf s) = (s : Matrix (Fin 2) (Fin 2) K) :=
  Matrix.SpecialLinearGroup.coe_GL_coe_matrix s

theorem slOf_surjective : Function.Surjective (slOf (K := K)) := by
  intro γ
  let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨sl2Mat γ, det_of_mem_statedSL γ⟩
  refine ⟨s, sl2Mat_injective ?_⟩
  rw [sl2Mat_slOf]

variable [CharP K 2]

@[expose] def wel : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two]; exact CharTwo.neg_eq 1⟩

theorem coe_wel :
    ((wel : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem wel_mul_unip_mul_wel (x : K) : wel * unip x * wel = lunip x := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_wel, coe_unip,
    coe_lunip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wel_mul_tor (μ : Kˣ) : wel * tor μ = tor μ⁻¹ * wel := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_wel, coe_tor,
    coe_tor]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem closure_unip_wel :
    Subgroup.closure (Set.range (unip (K := K)) ∪ {wel}) = ⊤ := by
  set S := Subgroup.closure (Set.range (unip (K := K)) ∪ {wel}) with hS
  have hu : ∀ x : K, unip x ∈ S := fun x => Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
  have hw : (wel : Matrix.SpecialLinearGroup (Fin 2) K) ∈ S :=
    Subgroup.subset_closure (Or.inr rfl)
  have hl : ∀ x : K, lunip x ∈ S := fun x => by
    rw [← wel_mul_unip_mul_wel]
    exact S.mul_mem (S.mul_mem hw (hu x)) hw
  have key : ∀ s : Matrix.SpecialLinearGroup (Fin 2) K,
      (s : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → s ∈ S := by
    intro s hc
    have hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1 := s.2
    rw [Matrix.det_fin_two] at hdet
    have e : s = unip (((s : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
          (s : Matrix (Fin 2) (Fin 2) K) 1 0) * lunip ((s : Matrix (Fin 2) (Fin 2) K) 1 0) *
        unip (((s : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (s : Matrix (Fin 2) (Fin 2) K) 1 0) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_unip,
        coe_unip, coe_lunip]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals (try field_simp)
      all_goals (first | linear_combination hdet | linear_combination -hdet | ring1)
    rw [e]
    exact S.mul_mem (S.mul_mem (hu _) (hl _)) (hu _)
  refine eq_top_iff.mpr fun s _ => ?_
  by_cases hc : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  ·
    have hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1 := s.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have hd : (s : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := fun h => by
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    have h1 : s * lunip 1 ∈ S := key _ (by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_lunip]
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc] using hd)
    have := S.mul_mem h1 (S.inv_mem (hl 1))
    rwa [mul_inv_cancel_right] at this
  · exact key s hc

end SL2

section Natural

variable {K : Type} [Field K] [CharP K 2]
variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {W C : Subgroup V}
  {π : ↥(StSL 2 K) →* ↥H}

omit [CharP K 2] in
theorem mem_of_fix_tor (hπ : (FFModel.nat (StSL 2 K)).RealizesVia H W C π) {ν : Kˣ}
    (hν : (ν : K) ≠ 1) {d : V} (hd : d ∈ W)
    (hfix : ((π (slOf (tor ν)) : ↥H) : MulAut V) d = d) : d ∈ C := by
  obtain ⟨-, -, -, hHW, -, -, -, β, -, hβk, hβe⟩ := hπ
  obtain ⟨⟨m, hmsec⟩, hm⟩ := QuotientGroup.mk_surjective (β ⟨d, hd⟩)
  have hgd : ((π (slOf (tor ν)) : ↥H) : MulAut V) d ∈ W := hHW _ d hd
  have h1 : β ⟨((π (slOf (tor ν)) : ↥H) : MulAut V) d, hgd⟩ = _ :=
    hβe (slOf (tor ν)) ⟨d, hd⟩ ⟨m, hmsec⟩ hgd trivial hm.symm
  have e : (⟨((π (slOf (tor ν)) : ↥H) : MulAut V) d, hgd⟩ : ↥W) = ⟨d, hd⟩ := Subtype.ext hfix
  rw [e, ← hm] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 := Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp h3)
  change Multiplicative (Fin 2 → K) at m
  have hact : natAct (StSL 2 K) (slOf (tor ν)) m = m := by
    have h5 : m⁻¹ * natAct (StSL 2 K) (slOf (tor ν)) m = 1 := by
      have := h4
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact this
    exact (inv_mul_eq_one.mp h5).symm
  have hmv : sl2Mat (slOf (tor ν)) *ᵥ Multiplicative.toAdd m = Multiplicative.toAdd m :=
    congrArg Multiplicative.toAdd hact
  rw [sl2Mat_slOf] at hmv
  have hν' : ((ν⁻¹ : Kˣ) : K) ≠ 1 := fun h => hν (by
    have := congrArg (fun u : Kˣ => ((u⁻¹ : Kˣ) : K)) (Units.ext (h.trans Units.val_one.symm))
    simpa using this)
  have hv0 : Multiplicative.toAdd m = 0 := by
    funext i
    have e1 := congrFun hmv i
    fin_cases i
    · simp [tor, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1
      have : ((ν : K) - 1) * Multiplicative.toAdd m 0 = 0 := by linear_combination e1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hν
      · simpa using h
    · simp [tor, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1
      have : (((ν⁻¹ : Kˣ) : K) - 1) * Multiplicative.toAdd m 1 = 0 := by
        simp only [Units.val_inv_eq_inv_val]
        linear_combination e1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hν'
      · simpa using h
  have hm1' : m = 1 := Multiplicative.toAdd.injective (by rw [hv0]; rfl)
  have hm1 : (⟨m, hmsec⟩ : ↥(FFModel.nat (StSL 2 K)).sec) = 1 := Subtype.ext hm1'
  exact (hβk ⟨d, hd⟩).1 (by rw [← hm, hm1, QuotientGroup.mk_one])

theorem fix_of_fix_borel (hπ : (FFModel.nat (StSL 2 K)).RealizesVia H W C π)
    (hC : ∀ g ∈ H, ∀ c ∈ C, g c = c) (hHp : ⁅H, H⁆ = H) {z : V}
    (hzW : ∀ g ∈ H, g z * z⁻¹ ∈ W)
    (hU : ∀ x : K, ((π (slOf (unip x)) : ↥H) : MulAut V) z = z) {μ : Kˣ} (hμ : (μ : K) ≠ 1)
    (hT : ((π (slOf (tor μ)) : ↥H) : MulAut V) z = z) : ∀ g ∈ H, g z = z := by
  have hsurj : Function.Surjective π := hπ.1
  have hinvC : ∀ g ∈ H, g z * z⁻¹ ∈ C → g⁻¹ z = (g z * z⁻¹)⁻¹ * z := by
    intro g hg hgC
    set c := g z * z⁻¹ with hc
    have e1 : g z = c * z := by rw [hc, inv_mul_cancel_right]
    have e2 : z = g⁻¹ (c * z) := by rw [← e1]; exact (MulAut.inv_apply_self _ g z).symm
    rw [map_mul, hC _ (H.inv_mem hg) c hgC] at e2
    calc g⁻¹ z = c⁻¹ * (c * g⁻¹ z) := by rw [inv_mul_cancel_left]
      _ = c⁻¹ * z := by rw [← e2]
  let D : Subgroup ↥(StSL 2 K) :=
    { carrier := {γ | ((π γ : ↥H) : MulAut V) z * z⁻¹ ∈ C}
      one_mem' := by
        show ((π 1 : ↥H) : MulAut V) z * z⁻¹ ∈ C
        rw [map_one, Subgroup.coe_one, MulAut.one_apply, mul_inv_cancel]
        exact C.one_mem
      mul_mem' := fun {γ δ} hγ hδ => by
        have hγ' : ((π γ : ↥H) : MulAut V) z * z⁻¹ ∈ C := hγ
        have hδ' : ((π δ : ↥H) : MulAut V) z * z⁻¹ ∈ C := hδ
        show ((π (γ * δ) : ↥H) : MulAut V) z * z⁻¹ ∈ C
        rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
        set c := ((π δ : ↥H) : MulAut V) z * z⁻¹ with hc
        have e : ((π δ : ↥H) : MulAut V) z = c * z := by rw [hc, inv_mul_cancel_right]
        rw [e, map_mul, hC _ (π γ).2 c hδ', mul_assoc]
        exact C.mul_mem hδ' hγ'
      inv_mem' := fun {γ} hγ => by
        have hγ' : ((π γ : ↥H) : MulAut V) z * z⁻¹ ∈ C := hγ
        show ((π γ⁻¹ : ↥H) : MulAut V) z * z⁻¹ ∈ C
        rw [map_inv, Subgroup.coe_inv, hinvC _ (π γ).2 hγ', mul_inv_cancel_right]
        exact C.inv_mem hγ' }
  have hwD : slOf wel ∈ D := by
    show ((π (slOf wel) : ↥H) : MulAut V) z * z⁻¹ ∈ C
    set d := ((π (slOf wel) : ↥H) : MulAut V) z * z⁻¹ with hd
    have hdW : d ∈ W := hzW _ (π (slOf wel)).2
    have hrel : π (slOf wel) * π (slOf (tor μ)) = π (slOf (tor μ⁻¹)) * π (slOf wel) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, wel_mul_tor]
    have hT' : ((π (slOf (tor μ⁻¹)) : ↥H) : MulAut V) z = z := by
      rw [tor_inv, map_inv, map_inv, Subgroup.coe_inv]
      conv_lhs => rw [← hT]
      exact MulAut.inv_apply_self _ _ z
    have e1 : ((π (slOf wel) : ↥H) : MulAut V) (((π (slOf (tor μ)) : ↥H) : MulAut V) z) =
        ((π (slOf (tor μ⁻¹)) : ↥H) : MulAut V) (((π (slOf wel) : ↥H) : MulAut V) z) := by
      have := congrArg (fun g : ↥H => ((g : ↥H) : MulAut V) z) hrel
      simpa only [Subgroup.coe_mul, MulAut.mul_apply] using this
    rw [hT] at e1
    have ez : ((π (slOf wel) : ↥H) : MulAut V) z = d * z := by rw [hd, inv_mul_cancel_right]
    rw [ez, map_mul, hT'] at e1
    have hfix : ((π (slOf (tor μ⁻¹)) : ↥H) : MulAut V) d = d := (mul_right_cancel e1).symm
    refine mem_of_fix_tor hπ (ν := μ⁻¹) ?_ hdW hfix
    intro h
    apply hμ
    have := congrArg (fun u : Kˣ => ((u⁻¹ : Kˣ) : K)) (Units.ext (h.trans Units.val_one.symm))
    simpa using this
  have hD : ∀ γ, γ ∈ D := by
    have hle : Subgroup.closure (Set.range (unip (K := K)) ∪ {wel}) ≤ D.comap slOf := by
      rw [Subgroup.closure_le]
      rintro s (⟨x, rfl⟩ | rfl)
      · show ((π (slOf (unip x)) : ↥H) : MulAut V) z * z⁻¹ ∈ C
        rw [hU x, mul_inv_cancel]
        exact C.one_mem
      · exact hwD
    rw [closure_unip_wel] at hle
    intro γ
    obtain ⟨s, rfl⟩ := slOf_surjective γ
    exact hle (Subgroup.mem_top s)
  have hHC : ∀ g ∈ H, g z * z⁻¹ ∈ C := by
    intro g hg
    obtain ⟨γ, hγ⟩ := hsurj ⟨g, hg⟩
    have h' : ((π γ : ↥H) : MulAut V) z * z⁻¹ ∈ C := hD γ
    rwa [hγ] at h'
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ MulAction.stabilizer (MulAut V) z := by
    intro a ha b hb
    rw [MulAction.mem_stabilizer_iff]
    set ca := a z * z⁻¹ with hca'
    set cb := b z * z⁻¹ with hcb'
    have hca : ca ∈ C := hHC a ha
    have hcb : cb ∈ C := hHC b hb
    have ea : a z = ca * z := by rw [hca', inv_mul_cancel_right]
    have eb : b z = cb * z := by rw [hcb', inv_mul_cancel_right]
    have ea' : a⁻¹ z = ca⁻¹ * z := hinvC a ha hca
    have eb' : b⁻¹ z = cb⁻¹ * z := hinvC b hb hcb
    show (a * b * a⁻¹ * b⁻¹) z = z
    simp only [MulAut.mul_apply]
    have s1 : a⁻¹ (b⁻¹ z) = cb⁻¹ * (ca⁻¹ * z) := by
      rw [eb', map_mul, hC _ (H.inv_mem ha) _ (C.inv_mem hcb), ea']
    have s2 : b (a⁻¹ (b⁻¹ z)) = cb⁻¹ * (ca⁻¹ * (cb * z)) := by
      rw [s1, map_mul, map_mul, hC _ hb _ (C.inv_mem hcb), hC _ hb _ (C.inv_mem hca), eb]
    have s3 : a (b (a⁻¹ (b⁻¹ z))) = cb⁻¹ * (ca⁻¹ * (cb * (ca * z))) := by
      rw [s2, map_mul, map_mul, map_mul, hC _ ha _ (C.inv_mem hcb), hC _ ha _ (C.inv_mem hca),
        hC _ ha _ hcb, ea]
    rw [s3, mul_left_comm ca⁻¹ cb, inv_mul_cancel_left, inv_mul_cancel_left]
  have hle : ⁅H, H⁆ ≤ MulAction.stabilizer (MulAut V) z := Subgroup.commutator_le.mpr hcomm
  intro g hg
  rw [← hHp] at hg
  exact MulAction.mem_stabilizer_iff.mp (hle hg)

end Natural

end CFSG.Quasithin.H13.A5
