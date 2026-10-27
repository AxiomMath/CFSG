module

public import CFSG.Quasithin.Background.JonesParshallHermitian
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.SteinbergCBI16Alt5

public noncomputable section

namespace CFSG.Quasithin.SteinbergCB.I16.Orth4

open Matrix Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [CharP F 2]

structure F4Data (F : Type) [Field F] where
  ω : F
  sq : ω ^ 2 = ω + 1
  cases : ∀ x : F, x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1
  pow4 : ∀ x : F, x ^ 4 = x

theorem exists_f4Data [Fintype F] (hF : Fintype.card F = 4) : Nonempty (F4Data F) := by
  classical
  have pow4 : ∀ x : F, x ^ 4 = x := fun x => by
    rw [← hF]
    exact FiniteField.pow_card x
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ∉ ({0, 1} : Finset F) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card (fun x (_ : x ∈ (Finset.univ : Finset F)) => h x)
    rw [Finset.card_univ, hF] at h1
    have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨hω0, hω1⟩ := hω
  have h3 : ω ^ 3 = 1 := by
    have h : ω * (ω ^ 3 - 1) = 0 := by
      rw [mul_sub, ← pow_succ', pow4, mul_one, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hω0)
  have hsq : ω ^ 2 = ω + 1 := by
    have h : (ω - 1) * (ω ^ 2 - ω - 1) = 0 := by grind
    have h' := (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hω1)
    grind
  refine ⟨⟨ω, hsq, fun x => ?_, pow4⟩⟩
  have h : x * (x - 1) * ((x - ω) * (x - ω - 1)) = 0 := by
    have := pow4 x
    grind
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
    · exact Or.inr (Or.inr (Or.inr (by grind)))

namespace F4Data

omit [CharP F 2] in
theorem ω_ne_zero (D : F4Data F) : D.ω ≠ 0 := fun h => by
  have := D.sq
  rw [h] at this
  grind

theorem ω_ne_one (D : F4Data F) : D.ω ≠ 1 := fun h => by
  have := D.sq
  rw [h] at this
  grind

omit [CharP F 2] in
theorem cube (D : F4Data F) {c : F} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h : c * (c ^ 3 - 1) = 0 := by
    rw [mul_sub, ← pow_succ', D.pow4, mul_one, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc)

theorem sig_one (x : F) : sig 1 x = x ^ 2 := by
  rw [sig_apply, pow_one]

theorem hσ (D : F4Data F) : ∀ x : F, sig 1 (sig 1 x) = x := fun x => by
  rw [sig_one, sig_one, ← pow_mul]
  exact D.pow4 x

@[expose] def pt (D : F4Data F) : Fin 5 → Fin 2 → F :=
  ![![1, 0], ![0, 1], ![1, 1], ![D.ω, 1], ![D.ω + 1, 1]]

@[expose] def rk (u : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => u i * u j ^ 2

theorem rk_mem (D : F4Data F) (u : Fin 2 → F) : rk u ∈ hermA 1 F :=
  mem_hermA_of fun i j => by
    simp only [rk, of_apply, sig_one]
    rw [mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, D.pow4, mul_comm]

theorem rk_smul (D : F4Data F) {c : F} (hc : c ≠ 0) (u : Fin 2 → F) : rk (c • u) = rk u := by
  ext i j
  simp only [rk, of_apply, Pi.smul_apply, smul_eq_mul]
  have := D.cube hc
  grind

theorem hermAct_rk (D : F4Data F) (g : SL2 F) (u : Fin 2 → F) :
    ((hermAct 1 D.hσ g ⟨rk u, D.rk_mem u⟩ : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) =
      rk ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) := by
  rw [hermAct_coe]
  ext i j
  simp only [rk, triple_apply, of_apply, frobPow, map_apply, mulVec, dotProduct,
    Fin.sum_univ_two, pow_one]
  grind

@[expose] def X (D : F4Data F) (p : Fin 5) : ↥(hermA 1 F) := ⟨rk (D.pt p), D.rk_mem _⟩

theorem X_coe (D : F4Data F) (p : Fin 5) :
    ((D.X p : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) = rk (D.pt p) :=
  rfl

theorem X_injective (D : F4Data F) : Function.Injective D.X := by
  have h0 := D.ω_ne_zero
  have h1 := D.ω_ne_one
  have h3 := D.cube (show D.ω + 1 ≠ 0 by grind)
  have h3' := D.cube h0
  intro i j h
  have e00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  have e01 := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  have e11 := congrFun (congrFun (congrArg Subtype.val h) 1) 1
  simp only [X, rk, pt, of_apply] at e00 e01 e11
  fin_cases i <;> fin_cases j <;> simp at e00 e01 e11 ⊢ <;> grind

omit [CharP F 2] in
theorem exists_pt (D : F4Data F) {u : Fin 2 → F} (hu : u ≠ 0) :
    ∃ j : Fin 5, ∃ c : F, c ≠ 0 ∧ u = c • D.pt j := by
  by_cases h1 : u 1 = 0
  · have h0 : u 0 ≠ 0 := fun h0 => hu (funext fun i => by fin_cases i <;> assumption)
    refine ⟨0, u 0, h0, funext fun i => ?_⟩
    fin_cases i <;> simp [pt, h1]
  · set t := u 0 / u 1
    have hu0 : u 0 = u 1 * t := by
      rw [mul_div_cancel₀ _ h1]
    have hv : ∀ j : Fin 5, D.pt j = ![t, 1] → u = u 1 • D.pt j := fun j hj => by
      rw [hj]
      funext i
      fin_cases i <;> simp [hu0]
    rcases D.cases t with ht | ht | ht | ht
    · exact ⟨1, u 1, h1, hv 1 (by rw [ht]; rfl)⟩
    · exact ⟨2, u 1, h1, hv 2 (by rw [ht]; rfl)⟩
    · exact ⟨3, u 1, h1, hv 3 (by rw [ht]; rfl)⟩
    · exact ⟨4, u 1, h1, hv 4 (by rw [ht]; rfl)⟩

omit [CharP F 2] in
theorem pt_ne_zero (D : F4Data F) (p : Fin 5) : D.pt p ≠ 0 := fun h => by
  have h1 := congrFun h 1
  have h0 := congrFun h 0
  fin_cases p <;> simp [pt] at h0 h1

theorem hermAct_X_eq (D : F4Data F) {g : SL2 F} {i j : Fin 5} {c : F} (hc : c ≠ 0)
    (h : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ D.pt i = c • D.pt j) :
    hermAct 1 D.hσ g (D.X i) = D.X j :=
  Subtype.ext ((D.hermAct_rk g _).trans (by rw [h, D.rk_smul hc]; rfl))

theorem hermAct_X (D : F4Data F) (g : SL2 F) (i : Fin 5) :
    ∃ j, hermAct 1 D.hσ g (D.X i) = D.X j := by
  have hne : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ D.pt i ≠ 0 := fun h => by
    apply D.pt_ne_zero i
    have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) F).det := by
      rw [g.2]
      exact isUnit_one
    calc D.pt i =
          ((g : Matrix (Fin 2) (Fin 2) F)⁻¹ * (g : Matrix (Fin 2) (Fin 2) F)) *ᵥ D.pt i := by
          rw [nonsing_inv_mul _ hdet, one_mulVec]
      _ = (g : Matrix (Fin 2) (Fin 2) F)⁻¹ *ᵥ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ D.pt i) :=
          (mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h, mulVec_zero]
  obtain ⟨j, c, hc, h⟩ := D.exists_pt hne
  exact ⟨j, D.hermAct_X_eq hc h⟩

@[expose] def idx (D : F4Data F) (g : SL2 F) (i : Fin 5) : Fin 5 :=
  Classical.choose (D.hermAct_X g i)

theorem idx_spec (D : F4Data F) (g : SL2 F) (i : Fin 5) :
    hermAct 1 D.hσ g (D.X i) = D.X (D.idx g i) :=
  Classical.choose_spec (D.hermAct_X g i)

theorem idx_eq_iff (D : F4Data F) {g : SL2 F} {i j : Fin 5} :
    D.idx g i = j ↔ hermAct 1 D.hσ g (D.X i) = D.X j :=
  ⟨fun h => h ▸ D.idx_spec g i, fun h => D.X_injective ((D.idx_spec g i).symm.trans h)⟩

theorem hermAct_mul_apply (D : F4Data F) (g h : SL2 F) (Y : ↥(hermA 1 F)) :
    hermAct 1 D.hσ (g * h) Y = hermAct 1 D.hσ g (hermAct 1 D.hσ h Y) := by
  rw [map_mul]
  rfl

theorem idx_inv (D : F4Data F) (g : SL2 F) (i : Fin 5) : D.idx g⁻¹ (D.idx g i) = i :=
  D.idx_eq_iff.2 (by rw [← D.idx_spec, ← D.hermAct_mul_apply, inv_mul_cancel, map_one]; rfl)

@[expose] def perm (D : F4Data F) (g : SL2 F) : Perm (Fin 5) where
  toFun := D.idx g
  invFun := D.idx g⁻¹
  left_inv := D.idx_inv g
  right_inv i := by
    simpa using D.idx_inv g⁻¹ i

@[expose] def phi (D : F4Data F) : SL2 F →* Perm (Fin 5) :=
  MonoidHom.mk' D.perm fun g h => Equiv.ext fun i => D.idx_eq_iff.2 (by
    change hermAct 1 D.hσ (g * h) (D.X i) = D.X (D.idx g (D.idx h i))
    rw [D.hermAct_mul_apply, D.idx_spec h, D.idx_spec g])

theorem phi_spec (D : F4Data F) (g : SL2 F) (i : Fin 5) :
    hermAct 1 D.hσ g (D.X i) = D.X (D.phi g i) :=
  D.idx_spec g i

theorem phi_injective (D : F4Data F) : Function.Injective D.phi := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ i, rk ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ D.pt i) = rk (D.pt i) := fun i => by
    have h := D.phi_spec g i
    rw [hg] at h
    exact (D.hermAct_rk g _).symm.trans (congrArg Subtype.val h)
  have e0 := congrFun (congrFun (hfix 0) 1) 1
  have e1 := congrFun (congrFun (hfix 1) 0) 0
  have e2 := congrFun (congrFun (hfix 2) 0) 1
  have hdet := g.2
  rw [det_fin_two] at hdet
  simp only [rk, pt, of_apply, mulVec, dotProduct, Fin.sum_univ_two] at e0 e1 e2
  simp at e0 e1 e2
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e0
  have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := e1
  rw [h10, h01] at e2 hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01] <;> grind

@[expose] def gA (D : F4Data F) : SL2 F :=
  ⟨!![0, 1; 1, 1], by
    rw [det_fin_two_of]
    have := D.sq
    grind⟩

@[expose] def gB (D : F4Data F) : SL2 F :=
  ⟨!![0, D.ω; D.ω + 1, D.ω], by
    rw [det_fin_two_of]
    have := D.sq
    grind⟩

theorem a5_vals : a5 0 = 1 ∧ a5 1 = 2 ∧ a5 2 = 0 ∧ a5 3 = 3 ∧ a5 4 = 4 := by
  decide +kernel

theorem b5_vals : b5 0 = 1 ∧ b5 1 = 2 ∧ b5 2 = 3 ∧ b5 3 = 4 ∧ b5 4 = 0 := by
  decide +kernel

theorem phi_gA (D : F4Data F) : D.phi D.gA = a5 := by
  have hs := D.sq
  have h0 := D.ω_ne_zero
  have h1 : D.ω + 1 ≠ 0 := fun h => D.ω_ne_one (by grind)
  obtain ⟨v0, v1, v2, v3, v4⟩ := a5_vals
  refine Equiv.ext fun i => ?_
  change D.idx D.gA i = a5 i
  refine D.idx_eq_iff.2 ?_
  fin_cases i
  · refine D.hermAct_X_eq (c := 1) one_ne_zero ?_
    rw [show (⟨0, by norm_num⟩ : Fin 5) = 0 from rfl, v0]
    funext j
    fin_cases j <;> simp [gA, pt, mulVec, dotProduct, Fin.sum_univ_two]
  · refine D.hermAct_X_eq (c := 1) one_ne_zero ?_
    rw [show (⟨1, by norm_num⟩ : Fin 5) = 1 from rfl, v1]
    funext j
    fin_cases j <;> simp [gA, pt, mulVec, dotProduct, Fin.sum_univ_two]
  · refine D.hermAct_X_eq (c := 1) one_ne_zero ?_
    rw [show (⟨2, by norm_num⟩ : Fin 5) = 2 from rfl, v2]
    funext j
    fin_cases j <;> simp [gA, pt, mulVec, dotProduct, Fin.sum_univ_two]
    grind
  · refine D.hermAct_X_eq (c := D.ω + 1) h1 ?_
    rw [show (⟨3, by norm_num⟩ : Fin 5) = 3 from rfl, v3]
    funext j
    fin_cases j <;> simp [gA, pt, mulVec, dotProduct, Fin.sum_univ_two]
    grind
  · refine D.hermAct_X_eq (c := D.ω) h0 ?_
    rw [show (⟨4, by norm_num⟩ : Fin 5) = 4 from rfl, v4]
    funext j
    fin_cases j <;> simp [gA, pt, mulVec, dotProduct, Fin.sum_univ_two] <;> grind

theorem phi_gB (D : F4Data F) : D.phi D.gB = b5 := by
  have hs := D.sq
  have h0 := D.ω_ne_zero
  have h1 : D.ω + 1 ≠ 0 := fun h => D.ω_ne_one (by grind)
  obtain ⟨v0, v1, v2, v3, v4⟩ := b5_vals
  refine Equiv.ext fun i => ?_
  change D.idx D.gB i = b5 i
  refine D.idx_eq_iff.2 ?_
  fin_cases i
  · refine D.hermAct_X_eq (c := D.ω + 1) h1 ?_
    rw [show (⟨0, by norm_num⟩ : Fin 5) = 0 from rfl, v0]
    funext j
    fin_cases j <;> simp [gB, pt, mulVec, dotProduct, Fin.sum_univ_two]
  · refine D.hermAct_X_eq (c := D.ω) h0 ?_
    rw [show (⟨1, by norm_num⟩ : Fin 5) = 1 from rfl, v1]
    funext j
    fin_cases j <;> simp [gB, pt, mulVec, dotProduct, Fin.sum_univ_two]
  · refine D.hermAct_X_eq (c := 1) one_ne_zero ?_
    rw [show (⟨2, by norm_num⟩ : Fin 5) = 2 from rfl, v2]
    funext j
    fin_cases j <;> simp [gB, pt, mulVec, dotProduct, Fin.sum_univ_two]
    grind
  · refine D.hermAct_X_eq (c := D.ω + 1) h1 ?_
    rw [show (⟨3, by norm_num⟩ : Fin 5) = 3 from rfl, v3]
    funext j
    fin_cases j <;> simp [gB, pt, mulVec, dotProduct, Fin.sum_univ_two] <;> grind
  · refine D.hermAct_X_eq (c := D.ω) h0 ?_
    rw [show (⟨4, by norm_num⟩ : Fin 5) = 4 from rfl, v4]
    funext j
    fin_cases j <;> simp [gB, pt, mulVec, dotProduct, Fin.sum_univ_two]
    grind

theorem closure_ab :
    Subgroup.closure (Set.range fun i => (gens5 i : Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  have h := congrArg (Subgroup.map (alternatingGroup (Fin 5)).subtype) closure_gens5
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    ← Set.range_comp] at h
  exact h

theorem phi_range (D : F4Data F) [Finite F] (hF : Nat.card F = 4) :
    D.phi.range = alternatingGroup (Fin 5) := by
  have hle : alternatingGroup (Fin 5) ≤ D.phi.range := by
    rw [← closure_ab, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨D.gA, D.phi_gA⟩
    · exact ⟨D.gB, D.phi_gB⟩
  have hcard : Nat.card D.phi.range ≤ Nat.card (alternatingGroup (Fin 5)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective D.phi_injective).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    have := card_alternatingGroup_fin_mul_two 5 (by norm_num)
    rw [show Nat.factorial 5 = 120 from rfl] at this
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

@[expose] def slEquiv (D : F4Data F) [Finite F] (hF : Nat.card F = 4) :
    SL2 F ≃* ↥(alternatingGroup (Fin 5)) :=
  (MonoidHom.ofInjective D.phi_injective).trans (MulEquiv.subgroupCongr (D.phi_range hF))

theorem val_nsmul_add {A : Type*} [AddCommMonoid A] (a b : ZMod 2) (Y : A) (hY : Y + Y = 0) :
    (a + b).val • Y = a.val • Y + b.val • Y := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 from rfl, ZMod.val_zero, zero_smul, ZMod.val_one, one_smul, hY]

@[expose] def lam (D : F4Data F) : (Fin 5 → ZMod 2) →+ ↥(hermA 1 F) where
  toFun x := ∑ p, (x p).val • D.X p
  map_zero' := by simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => val_nsmul_add _ _ _ (hermA_add_self _)

theorem hermAct_lam (D : F4Data F) (g : SL2 F) (x : Fin 5 → ZMod 2) :
    hermAct 1 D.hσ g (D.lam x) = D.lam (pv (D.phi g) x) := by
  change hermAct 1 D.hσ g (∑ p, (x p).val • D.X p) = ∑ q, ((pv (D.phi g) x) q).val • D.X q
  rw [map_sum, ← Equiv.sum_comp (D.phi g) fun q => ((pv (D.phi g) x) q).val • D.X q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_nsmul, D.phi_spec, pv_apply, Perm.inv_def, Equiv.symm_apply_apply]

theorem incl_proj5 (x : Fin 5 → ZMod 2) (hx : ∑ i, x i = 0) :
    coords5.incl (coords5.proj x) = x := by
  have hs : ∑ i, (x - coords5.incl (coords5.proj x)) i = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hx, coords5.sum_incl, sub_self]
  rcases coords5.ker_proj _ hs (by rw [map_sub, coords5.proj_incl, sub_self]) with h | h
  · exact (sub_eq_zero.1 h).symm
  · rw [h] at hs
    exact absurd hs (by decide)

@[expose] def M (D : F4Data F) : (Fin 4 → ZMod 2) →+ ↥(hermA 1 F) := D.lam.comp coords5.incl

theorem M_equivariant (D : F4Data F) [Finite F] (hF : Nat.card F = 4) (g : SL2 F)
    (y : Fin 4 → ZMod 2) :
    D.M (coords5.actA (D.slEquiv hF g) y) = hermAct 1 D.hσ g (D.M y) := by
  change D.lam (coords5.incl (coords5.proj (pv (D.phi g) (coords5.incl y)))) =
    hermAct 1 D.hσ g (D.lam (coords5.incl y))
  rw [incl_proj5 _ (by rw [sum_pv]; exact coords5.sum_incl y), D.hermAct_lam]

abbrev kap : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

theorem val_cast (z : ZMod 2) : ((z.val : ℕ) : F) = kap z := by
  rw [ZMod.natCast_val, ZMod.castHom_apply]

theorem lam_apply (D : F4Data F) (x : Fin 5 → ZMod 2) (i j : Fin 2) :
    ((D.lam x : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) i j =
      ∑ p, kap (x p) * rk (D.pt p) i j := by
  change ((∑ p, (x p).val • D.X p : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) i j = _
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [AddSubmonoidClass.coe_nsmul, Matrix.smul_apply, nsmul_eq_mul, val_cast, X_coe]

theorem M_apply (D : F4Data F) (y : Fin 4 → ZMod 2) (i j : Fin 2) :
    ((D.M y : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) i j =
      kap (y 0) * rk (D.pt 0) i j + kap (y 1) * rk (D.pt 1) i j +
        kap (y 2) * rk (D.pt 2) i j + kap (y 3) * rk (D.pt 3) i j +
          kap (y 0 + y 1 + y 2 + y 3) * rk (D.pt 4) i j := by
  change ((D.lam (inclOdd 4 y) : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) i j = _
  rw [lam_apply, Fin.sum_univ_five]
  simp [inclOdd, Fin.sum_univ_four]

theorem M_00 (D : F4Data F) (y : Fin 4 → ZMod 2) :
    ((D.M y : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = kap (y 1) := by
  have h3 := D.cube D.ω_ne_zero
  have h3' := D.cube (show D.ω + 1 ≠ 0 from fun h => D.ω_ne_one (by grind))
  rw [M_apply]
  simp only [rk, pt, of_apply, map_add]
  simp
  grind

theorem M_11 (D : F4Data F) (y : Fin 4 → ZMod 2) :
    ((D.M y : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = kap (y 0) := by
  rw [M_apply]
  simp only [rk, pt, of_apply, map_add]
  simp
  grind

theorem M_01 (D : F4Data F) (y : Fin 4 → ZMod 2) :
    ((D.M y : ↥(hermA 1 F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      kap (y 0 + y 1 + y 3) + kap (y 0 + y 1 + y 2) * D.ω := by
  rw [M_apply]
  simp only [rk, pt, of_apply, map_add]
  simp
  grind

theorem M_injective (D : F4Data F) : Function.Injective D.M := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have e00 := D.M_00 y
  have e11 := D.M_11 y
  have e01 := D.M_01 y
  rw [hy] at e00 e11 e01
  have hk : Function.Injective (kap : ZMod 2 →+* F) := (kap : ZMod 2 →+* F).injective
  have y1 : y 1 = 0 := hk (by rw [← e00, map_zero]; rfl)
  have y0 : y 0 = 0 := hk (by rw [← e11, map_zero]; rfl)
  rw [y0, y1] at e01
  have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have h0 := D.ω_ne_zero
  have h1 := D.ω_ne_one
  have hz : y 2 = 0 ∧ y 3 = 0 := by
    rcases h2 (y 2) with e2 | e2 <;> rcases h2 (y 3) with e3 | e3 <;> rw [e2, e3] at e01 <;>
      simp at e01 <;> first | exact ⟨e2, e3⟩ | grind
  funext i
  fin_cases i
  · exact y0
  · exact y1
  · exact hz.1
  · exact hz.2

theorem M_surjective (D : F4Data F) : Function.Surjective D.M := by
  intro Y
  have hsq : ∀ x : F, sig 1 x = x → ∃ z : ZMod 2, kap z = x := fun x hx => by
    rw [sig_one] at hx
    have h : x * (x - 1) = 0 := by grind
    rcases mul_eq_zero.1 h with h | h
    · exact ⟨0, by rw [map_zero, h]⟩
    · exact ⟨1, by rw [map_one, sub_eq_zero.1 h]⟩
  obtain ⟨za, ha⟩ := hsq _ (hermA_00 Y)
  obtain ⟨zd, hd⟩ := hsq _ (hermA_11 Y)
  obtain ⟨c0, c1, hb⟩ : ∃ c0 c1 : ZMod 2,
      kap c0 + kap c1 * D.ω = (Y : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    rcases D.cases ((Y : Matrix (Fin 2) (Fin 2) F) 0 1) with h | h | h | h
    · exact ⟨0, 0, by rw [h]; simp⟩
    · exact ⟨1, 0, by rw [h]; simp⟩
    · exact ⟨0, 1, by rw [h]; simp⟩
    · exact ⟨1, 1, by rw [h]; simp; ring⟩
  refine ⟨![zd, za, c1 + zd + za, c0 + zd + za], hermA_ext ?_ ?_ ?_⟩
  · rw [M_00]
    exact ha
  · rw [M_01, ← hb]
    simp only [Matrix.cons_val]
    congr 2 <;> grind
  · rw [M_11]
    exact hd

end F4Data

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem alternatingNatural_of_binaryOrthogonalFour [Fintype F] (hF : Fintype.card F = 2 ^ (2 * 1))
    {ρ : Representation (ZMod 2) Γ W} (h : Explicit.BinaryOrthogonalFour ρ F 1) :
    Explicit.AlternatingNatural ρ 5 .alternating := by
  obtain ⟨D⟩ := exists_f4Data (F := F) (by rw [hF]; rfl)
  have hN : Nat.card F = 4 := by
    rw [Nat.card_eq_fintype_card, hF]
    rfl
  obtain ⟨θ, β, hβ⟩ := BinaryOrthogonalFour.intertwiner D.hσ h
  let Me : (Fin 4 → ZMod 2) ≃+ ↥(hermA 1 F) :=
    AddEquiv.ofBijective D.M ⟨D.M_injective, D.M_surjective⟩
  refine coords5.alternatingNatural_of_intertwiner (θ := θ.trans (D.slEquiv hN))
    (e := β.trans Me.symm) fun γ w => ?_
  apply Me.injective
  rw [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, hβ, MulEquiv.trans_apply]
  change _ = D.M (coords5.actA (D.slEquiv hN (θ γ)) (Me.symm (β w)))
  rw [D.M_equivariant]
  exact congrArg _ (Me.apply_symm_apply (β w)).symm

end CFSG.Quasithin.SteinbergCB.I16.Orth4
