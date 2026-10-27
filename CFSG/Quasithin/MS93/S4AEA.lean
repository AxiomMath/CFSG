module

public import CFSG.Quasithin.MS93.ML3Facts

public section

namespace CFSG.Quasithin.MS93

open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem mul_eq_zero_of_mul_self_eq_zero {A B : Matrix (Fin 3) (Fin 3) F} (hA : A * A = 0)
    (hB : B * B = 0) (hAB : A * B = B * A) : A * B = 0 := by
  by_contra h
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → F, (A * B) *ᵥ x ≠ 0 := by
    by_contra! h'
    exact h (Matrix.ext_of_mulVec_single fun i => by rw [h', Matrix.zero_mulVec])
  have e1 : A *ᵥ (A *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec, hA, Matrix.zero_mulVec]
  have e2 : B *ᵥ (B *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  have e3 : A *ᵥ (B *ᵥ x) = (A * B) *ᵥ x := Matrix.mulVec_mulVec _ _ _
  have e4 : B *ᵥ (A *ᵥ x) = (A * B) *ᵥ x := by rw [Matrix.mulVec_mulVec, hAB]
  have e5 : A *ᵥ ((A * B) *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, ← mul_assoc, hA, zero_mul, Matrix.zero_mulVec]
  have e6 : B *ᵥ ((A * B) *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, ← mul_assoc, ← hAB, mul_assoc, hB, mul_zero, Matrix.zero_mulVec]
  have hli : LinearIndependent F ![x, A *ᵥ x, B *ᵥ x, (A * B) *ᵥ x] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_four] at hc
    have hc' : c 0 • x + c 1 • (A *ᵥ x) + c 2 • (B *ᵥ x) + c 3 • ((A * B) *ᵥ x) = 0 := hc
    have hA' : c 0 • (A *ᵥ x) + c 2 • ((A * B) *ᵥ x) = 0 := by
      simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, e1, e3, e5, smul_zero, add_zero,
        Matrix.mulVec_zero] using congrArg (A *ᵥ ·) hc'
    have hB' : c 0 • (B *ᵥ x) + c 1 • ((A * B) *ᵥ x) = 0 := by
      simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, e2, e4, e6, smul_zero, add_zero,
        Matrix.mulVec_zero] using congrArg (B *ᵥ ·) hc'
    have hAB' : c 0 • ((A * B) *ᵥ x) = 0 := by
      simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, e4, e6, smul_zero, add_zero,
        Matrix.mulVec_zero] using congrArg (B *ᵥ ·) hA'
    have h0 : c 0 = 0 := (smul_eq_zero.mp hAB').resolve_right hx
    rw [h0, zero_smul, zero_add] at hA' hB'
    have h2 : c 2 = 0 := (smul_eq_zero.mp hA').resolve_right hx
    have h1 : c 1 = 0 := (smul_eq_zero.mp hB').resolve_right hx
    rw [h0, h1, h2] at hc'
    simp only [zero_smul, zero_add] at hc'
    have h3 : c 3 = 0 := (smul_eq_zero.mp hc').resolve_right hx
    intro i
    fin_cases i
    exacts [h0, h1, h2, h3]
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fin_fun] at this
  omega

theorem sub_one_mul_self_eq_zero [CharP F 2] {g : SL3 F} (hg : g * g = 1) :
    ((g : Matrix (Fin 3) (Fin 3) F) - 1) * ((g : Matrix (Fin 3) (Fin 3) F) - 1) = 0 := by
  have hg' : (g : Matrix (Fin 3) (Fin 3) F) * g = 1 := by
    rw [← coe_mul_SL3, hg, coe_one_SL3]
  have h := CharTwo.add_self_eq_zero (g : Matrix (Fin 3) (Fin 3) F)
  have h1 := CharTwo.add_self_eq_zero (1 : Matrix (Fin 3) (Fin 3) F)
  calc _ = (g : Matrix (Fin 3) (Fin 3) F) * g - ((g : Matrix (Fin 3) (Fin 3) F) + g) + 1 := by
        noncomm_ring
    _ = 0 := by rw [hg', h, sub_zero, h1]

theorem commN_le_fixN_of_elemAb [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) :
    commN E ≤ fixN E := by
  rw [commN, Submodule.span_le]
  rintro _ ⟨h, hh, x, rfl⟩ g hg
  have hcomm : ((g : Matrix (Fin 3) (Fin 3) F) - 1) * ((h : Matrix (Fin 3) (Fin 3) F) - 1) =
      ((h : Matrix (Fin 3) (Fin 3) F) - 1) * ((g : Matrix (Fin 3) (Fin 3) F) - 1) := by
    have e : (g : Matrix (Fin 3) (Fin 3) F) * h = h * g := by
      rw [← coe_mul_SL3, ← coe_mul_SL3, hc g hg h hh]
    simp only [sub_mul, mul_sub, one_mul, mul_one, e]
    abel
  have key := congrArg (· *ᵥ x) (mul_eq_zero_of_mul_self_eq_zero
    (sub_one_mul_self_eq_zero (h2 g hg)) (sub_one_mul_self_eq_zero (h2 h hh)) hcomm)
  simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec] at key
  exact sub_eq_zero.mp key

theorem finrank_commN_le_finrank_fixN_of_elemAb [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) :
    Module.finrank F (commN E) ≤ Module.finrank F (fixN E) :=
  Submodule.finrank_mono (commN_le_fixN_of_elemAb h2 hc)

theorem card_le_pow_finrank [Finite F] (E : Subgroup (SL3 F)) :
    Nat.card E ≤
      Nat.card F ^ ((3 - Module.finrank F (fixN E)) * Module.finrank F (commN E)) := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (fixN E)
  have hdim : Module.finrank F W = 3 - Module.finrank F (fixN E) := by
    have h := Submodule.finrank_add_eq_of_isCompl hW
    rw [Module.finrank_fin_fun] at h
    omega
  let f : E → (W →ₗ[F] commN E) := fun g =>
    { toFun := fun w => ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F) - w,
        sub_mem_commN g.2 _⟩
      map_add' := fun w w' => by
        apply Subtype.ext
        simp only [Submodule.coe_add, Matrix.mulVec_add]
        abel
      map_smul' := fun c w => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, Matrix.mulVec_smul, RingHom.id_apply, smul_sub] }
  have hf : Function.Injective f := by
    intro g h hgh
    have hW' : ∀ w ∈ W, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
        ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
      intro w hw
      have := congrArg (fun φ : W →ₗ[F] commN E => ((φ ⟨w, hw⟩ : commN E) : Fin 3 → F)) hgh
      simpa [f] using this
    have hall : ∀ v : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
      intro v
      have hv : v ∈ fixN E ⊔ W := by rw [hW.sup_eq_top]; trivial
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hy g g.2, hy h h.2, hW' w hw]
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.ext_of_mulVec_single fun i => hall _
  have : Finite (W →ₗ[F] commN E) := Module.finite_of_finite F
  calc Nat.card E ≤ Nat.card (W →ₗ[F] commN E) := Nat.card_le_card_of_injective f hf
    _ = Nat.card F ^ Module.finrank F (W →ₗ[F] commN E) :=
        Module.natCard_eq_pow_finrank (K := F) (V := W →ₗ[F] commN E)
    _ = _ := by rw [Module.finrank_linearMap, hdim]

theorem card_le_of_elemAb [Finite F] [CharP F 2] {E : Subgroup (SL3 F)}
    (_h2 : ∀ g ∈ E, g * g = 1) (_hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) :
    Nat.card E ≤
      Nat.card F ^ ((3 - Module.finrank F (fixN E)) * Module.finrank F (commN E)) :=
  card_le_pow_finrank E

theorem card_fixN [Finite F] (E : Subgroup (SL3 F)) :
    Nat.card (fixN E) = Nat.card F ^ Module.finrank F (fixN E) :=
  Module.natCard_eq_pow_finrank

private theorem mulVec_conj (x g : SL3 F) (v : Fin 3 → F) :
    (((MulAut.conj x).toMonoidHom g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      (x : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_mul_SL3, coe_mul_SL3,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem mulVec_inv_mulVec (x : SL3 F) (v : Fin 3 → F) :
    ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]

private theorem mulVec_mulVec_inv (x : SL3 F) (v : Fin 3 → F) :
    (x : Matrix (Fin 3) (Fin 3) F) *ᵥ (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem fixN_map_conj (x : SL3 F) (E : Subgroup (SL3 F)) :
    fixN (E.map (MulAut.conj x).toMonoidHom) =
      (fixN E).map (Matrix.SpecialLinearGroup.toLin' x : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) := by
  ext y
  rw [Submodule.mem_map_equiv]
  change (∀ g ∈ E.map (MulAut.conj x).toMonoidHom, _) ↔
    ∀ g ∈ E, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
      ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y
  constructor
  · intro hy g hg
    have := congrArg (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ·)
      (hy _ (Subgroup.mem_map_of_mem _ hg))
    simpa only [mulVec_conj, mulVec_inv_mulVec] using this
  · rintro hy _ ⟨g, hg, rfl⟩
    rw [mulVec_conj, hy g hg, mulVec_mulVec_inv]

theorem commN_map_conj (x : SL3 F) (E : Subgroup (SL3 F)) :
    commN (E.map (MulAut.conj x).toMonoidHom) =
      (commN E).map (Matrix.SpecialLinearGroup.toLin' x : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) := by
  rw [commN, commN, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, v, rfl⟩
    refine ⟨_, ⟨g, hg, ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_sub, mulVec_conj, mulVec_mulVec_inv]
  · rintro ⟨_, ⟨g, hg, v, rfl⟩, rfl⟩
    refine ⟨_, ⟨g, hg, rfl⟩, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ v, ?_⟩
    rw [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_sub, mulVec_conj, mulVec_inv_mulVec]

theorem finrank_fixN_map_conj (x : SL3 F) (E : Subgroup (SL3 F)) :
    Module.finrank F (fixN (E.map (MulAut.conj x).toMonoidHom)) =
      Module.finrank F (fixN E) := by
  rw [fixN_map_conj, LinearEquiv.finrank_map_eq]

theorem finrank_commN_map_conj (x : SL3 F) (E : Subgroup (SL3 F)) :
    Module.finrank F (commN (E.map (MulAut.conj x).toMonoidHom)) =
      Module.finrank F (commN E) := by
  rw [commN_map_conj, LinearEquiv.finrank_map_eq]

private theorem exists_natCard_eq_two_pow [Finite F] [CharP F 2] :
    ∃ n : ℕ, Nat.card F = 2 ^ n := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem exists_conj_le_sStar [Finite F] [CharP F 2] {S : Subgroup (SL3 F)}
    (hS : IsPGroup 2 S) : ∃ x : SL3 F, S.map (MulAut.conj x).toMonoidHom ≤ sStar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hF⟩ := exists_natCard_eq_two_pow (F := F)
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SL3 F) Q
    ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF))
  refine ⟨x, ?_⟩
  have := congrArg (fun P : Sylow 2 (SL3 F) => (P : Subgroup (SL3 F))) hx
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  rw [Subgroup.pointwise_smul_def] at this
  rw [← this]
  exact Subgroup.map_mono hQ

theorem uniTri_eq_uniTri_iff {a b c a' b' c' : F} :
    uniTri a b c = uniTri a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have := @uniTri_injective F _ (a, b, c) (a', b', c') h
    simp only [Prod.mk.injEq] at this
    exact this
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem uniTri_mulVec (a b c : F) (x : Fin 3 → F) :
    ((uniTri a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      ![x 0 + a * x 1 + b * x 2, x 1 + c * x 2, x 2] := by
  rw [coe_uniTri]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem uniTri_commutator (a b c a' b' c' : F) :
    ⁅uniTri a b c, uniTri a' b' c'⁆ = uniTri 0 (a * c' - a' * c) 0 := by
  rw [commutatorElement_def, uniTri_inv, uniTri_inv, uniTri_mul, uniTri_mul, uniTri_mul]
  congr 1 <;> ring

theorem uniTri_mul_self [CharP F 2] (a b c : F) :
    uniTri a b c * uniTri a b c = uniTri 0 (a * c) 0 := by
  rw [uniTri_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_right_comm,
    CharTwo.add_self_eq_zero, zero_add]

theorem uniTri_mul_self_eq_one_iff [CharP F 2] (a b c : F) :
    uniTri a b c * uniTri a b c = 1 ↔ a * c = 0 := by
  rw [uniTri_mul_self, ← uniTri_zero, uniTri_eq_uniTri_iff]
  simp

theorem mem_qPt_iff_uniTri {g : SL3 F} : g ∈ qPt ↔ ∃ a b : F, uniTri a b 0 = g := by
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ∃ a b : F, uniTri a b 0 = g}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        exact ⟨a + a', b + a * 0 + b', by rw [uniTri_mul, add_zero]⟩
      one_mem' := ⟨0, 0, uniTri_zero⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨-a, a * 0 - b, by rw [uniTri_inv, neg_zero]⟩ }
  constructor
  · intro hg
    have hle : (qPt : Subgroup (SL3 F)) ≤ P := by
      rw [qPt]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨a, 0, (rootElt01_eq_uniTri a).symm⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨0, b, (rootElt02_eq_uniTri b).symm⟩
    exact hle hg
  · rintro ⟨a, b, rfl⟩
    have e : uniTri a b 0 = rootElt 0 1 a * rootElt 0 2 b := by
      rw [rootElt01_eq_uniTri, rootElt02_eq_uniTri, uniTri_mul]
      congr 1 <;> ring
    rw [e, qPt]
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup _ _ _) (rootElt_mem_rootGroup _ _ _)

theorem mem_qLn_iff_uniTri {g : SL3 F} : g ∈ qLn ↔ ∃ b c : F, uniTri 0 b c = g := by
  rw [mem_qLn_iff]
  have e : ∀ b c : F, rootElt 0 2 b * rootElt 1 2 c = uniTri 0 b c := fun b c => by
    rw [rootElt02_eq_uniTri, rootElt12_eq_uniTri, uniTri_mul]
    congr 1 <;> ring
  simp only [e]

theorem card_rootGroup [Finite F] {i j : Fin 3} (h : i ≠ j) :
    Nat.card (rootGroup i j : Subgroup (SL3 F)) = Nat.card F :=
  (Nat.card_congr (Equiv.ofInjective _ (rootElt_injective h))).symm

theorem card_qPt [Finite F] : Nat.card (qPt : Subgroup (SL3 F)) = Nat.card F ^ 2 := by
  have e : F × F ≃ (qPt : Subgroup (SL3 F)) :=
    Equiv.ofBijective (fun p => ⟨uniTri p.1 p.2 0, mem_qPt_iff_uniTri.mpr ⟨_, _, rfl⟩⟩)
      ⟨fun p p' h => by
        obtain ⟨h1, h2, -⟩ := uniTri_eq_uniTri_iff.mp (congrArg Subtype.val h)
        exact Prod.ext h1 h2, by
        rintro ⟨g, hg⟩
        obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hg
        exact ⟨(a, b), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, sq]

theorem card_qLn [Finite F] : Nat.card (qLn : Subgroup (SL3 F)) = Nat.card F ^ 2 := by
  have e : F × F ≃ (qLn : Subgroup (SL3 F)) :=
    Equiv.ofBijective (fun p => ⟨uniTri 0 p.1 p.2, mem_qLn_iff_uniTri.mpr ⟨_, _, rfl⟩⟩)
      ⟨fun p p' h => by
        obtain ⟨-, h1, h2⟩ := uniTri_eq_uniTri_iff.mp (congrArg Subtype.val h)
        exact Prod.ext h1 h2, by
        rintro ⟨g, hg⟩
        obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hg
        exact ⟨(b, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, sq]

theorem qPt_inf_qLn : (qPt : Subgroup (SL3 F)) ⊓ qLn = rootGroup 0 2 := by
  refine le_antisymm ?_ (le_inf rootGroup_le_qPt rootGroup_le_qLn)
  rintro g ⟨hP, hL⟩
  obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hP
  obtain ⟨b', c', e⟩ := mem_qLn_iff_uniTri.mp hL
  obtain ⟨ha, -, -⟩ := uniTri_eq_uniTri_iff.mp e
  rw [← ha]
  exact ⟨b, rootElt02_eq_uniTri b⟩

theorem finrank_pt0 [Finite F] : Module.finrank F (pt0 : Submodule F (Fin 3 → F)) = 1 := by
  have hc : Nat.card (pt0 : Submodule F (Fin 3 → F)) = Nat.card F := by
    let e : F ≃ (pt0 : Submodule F (Fin 3 → F)) :=
      { toFun := fun c => ⟨![c, 0, 0], ⟨rfl, rfl⟩⟩
        invFun := fun x => (x : Fin 3 → F) 0
        left_inv := fun c => rfl
        right_inv := fun x => by
          apply Subtype.ext
          funext k
          fin_cases k
          · rfl
          · exact x.2.1.symm
          · exact x.2.2.symm }
    rw [← Nat.card_congr e]
  have h := Module.natCard_eq_pow_finrank (K := F) (V := (pt0 : Submodule F (Fin 3 → F)))
  rw [hc] at h
  exact (Nat.pow_right_injective (Finite.one_lt_card (α := F)) (h.symm.trans (pow_one _).symm))

theorem le_qPt_or_le_qLn_of_mul_self_eq_one [CharP F 2] {E : Subgroup (SL3 F)}
    (hE : E ≤ sStar) (h2 : ∀ g ∈ E, g * g = 1) : E ≤ qPt ∨ E ≤ qLn := by
  by_contra! h
  obtain ⟨hP, hL⟩ := h
  obtain ⟨g, hg, hgP⟩ := IsConcreteLE.not_le_iff_exists.mp hP
  obtain ⟨g', hg', hgL⟩ := IsConcreteLE.not_le_iff_exists.mp hL
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hE hg)
  obtain ⟨a', b', c', rfl⟩ := mem_sStar_iff.mp (hE hg')
  have hc : c ≠ 0 := fun h => hgP (mem_qPt_iff_uniTri.mpr ⟨a, b, by rw [h]⟩)
  have ha' : a' ≠ 0 := fun h => hgL (mem_qLn_iff_uniTri.mpr ⟨b', c', by rw [h]⟩)
  have e1 := (uniTri_mul_self_eq_one_iff a b c).mp (h2 _ hg)
  have e2 := (uniTri_mul_self_eq_one_iff a' b' c').mp (h2 _ hg')
  have e3 := h2 _ (E.mul_mem hg hg')
  rw [uniTri_mul, uniTri_mul_self_eq_one_iff] at e3
  have ha : a = 0 := (mul_eq_zero.mp e1).resolve_right hc
  have hc' : c' = 0 := (mul_eq_zero.mp e2).resolve_left ha'
  rw [ha, hc', zero_add, add_zero] at e3
  exact mul_ne_zero ha' hc e3

theorem le_qPt_or_le_qLn_of_elemAb [CharP F 2] {E : Subgroup (SL3 F)} (hE : E ≤ sStar)
    (h2 : ∀ g ∈ E, g * g = 1) (_hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) :
    E ≤ qPt ∨ E ≤ qLn :=
  le_qPt_or_le_qLn_of_mul_self_eq_one hE h2

private theorem false_of_noncommuting_aux [Finite F] [CharP F 2] {Ea Eb : Subgroup (SL3 F)}
    (hEa : Ea ≤ sStar) (hEb : Eb ≤ sStar)
    (h2a : ∀ g ∈ Ea, g * g = 1) (h2b : ∀ g ∈ Eb, g * g = 1)
    {a b b' c : F} (ha : a ≠ 0) (hc : c ≠ 0) (hga : uniTri a b 0 ∈ Ea)
    (hgb : uniTri 0 b' c ∈ Eb) (hcomm : ⁅Ea, Eb⁆ ≤ Ea ⊓ Eb)
    (hcarda : Nat.card Ea = Nat.card F ^ (3 - Module.finrank F (fixN Ea)))
    (hcardb : Nat.card Eb = Nat.card F ^ (3 - Module.finrank F (fixN Eb))) : False := by
  have hEaP : Ea ≤ qPt := by
    rcases le_qPt_or_le_qLn_of_mul_self_eq_one hEa h2a with h | h
    · exact h
    · obtain ⟨b₁, c₁, e⟩ := mem_qLn_iff_uniTri.mp (h hga)
      exact (ha (uniTri_eq_uniTri_iff.mp e).1.symm).elim
  have hEbL : Eb ≤ qLn := by
    rcases le_qPt_or_le_qLn_of_mul_self_eq_one hEb h2b with h | h
    · obtain ⟨a₁, b₁, e⟩ := mem_qPt_iff_uniTri.mp (h hgb)
      exact (hc (uniTri_eq_uniTri_iff.mp e).2.2.symm).elim
    · exact h
  have hz : uniTri 0 (a * c) 0 ∈ Ea ⊓ Eb := by
    have := hcomm (Subgroup.commutator_mem_commutator hga hgb)
    rwa [uniTri_commutator, zero_mul, sub_zero] at this
  have hfix : fixN Ea ≤ pt0 := by
    intro x hx
    have h1 := congrFun (hx _ hga) 0
    have h2 := congrFun (hx _ hz.1) 0
    rw [uniTri_mulVec] at h1 h2
    simp only [Matrix.cons_val_zero] at h1 h2
    have hx2 : x 2 = 0 := by
      have : a * c * x 2 = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero ha hc)
      · exact h
    have hx1 : x 1 = 0 := by
      have : a * x 1 = 0 := by linear_combination h1 - b * hx2
      exact (mul_eq_zero.mp this).resolve_left ha
    exact ⟨hx1, hx2⟩
  have hfa : Module.finrank F (fixN Ea) ≤ 1 :=
    (Submodule.finrank_mono hfix).trans finrank_pt0.le
  have hEaq : Ea = qPt := by
    apply Subgroup.eq_of_le_of_card_ge hEaP
    rw [card_qPt, hcarda]
    exact Nat.pow_le_pow_right Nat.card_pos (by omega)
  have hZ : rootGroup 0 2 ≤ Eb := by
    rintro _ ⟨t, rfl⟩
    have hs : uniTri (t / c) 0 0 ∈ Ea := by
      rw [hEaq]
      exact mem_qPt_iff_uniTri.mpr ⟨t / c, 0, rfl⟩
    have := (hcomm (Subgroup.commutator_mem_commutator hs hgb)).2
    rw [uniTri_commutator, zero_mul, sub_zero, div_mul_cancel₀ t hc] at this
    rwa [rootElt02_eq_uniTri]
  have hfb : 2 ≤ Module.finrank F (fixN Eb) := by
    rw [← finrank_ln01 (F := F)]
    exact Submodule.finrank_mono (fixN_qLn.symm.le.trans (fixN_anti hEbL))
  have hEbZ : rootGroup 0 2 = Eb := by
    apply Subgroup.eq_of_le_of_card_ge hZ
    rw [card_rootGroup (by decide), hcardb]
    calc Nat.card F ^ (3 - Module.finrank F (fixN Eb)) ≤ Nat.card F ^ 1 :=
          Nat.pow_le_pow_right Nat.card_pos (by omega)
      _ = Nat.card F := pow_one _
  rw [← hEbZ] at hgb
  obtain ⟨t, ht⟩ := hgb
  rw [rootElt02_eq_uniTri] at ht
  exact hc (uniTri_eq_uniTri_iff.mp ht).2.2.symm

theorem false_of_noncommuting_elemAb [Finite F] [CharP F 2] {E₁ E₂ : Subgroup (SL3 F)}
    (hE₁ : E₁ ≤ sStar) (hE₂ : E₂ ≤ sStar)
    (h2₁ : ∀ g ∈ E₁, g * g = 1) (_hc₁ : ∀ g ∈ E₁, ∀ g' ∈ E₁, g * g' = g' * g)
    (h2₂ : ∀ g ∈ E₂, g * g = 1) (_hc₂ : ∀ g ∈ E₂, ∀ g' ∈ E₂, g * g' = g' * g)
    (hnc : ∃ g₁ ∈ E₁, ∃ g₂ ∈ E₂, g₁ * g₂ ≠ g₂ * g₁) (hcomm : ⁅E₁, E₂⁆ ≤ E₁ ⊓ E₂)
    (hcard₁ : Nat.card E₁ = Nat.card F ^ (3 - Module.finrank F (fixN E₁)))
    (hcard₂ : Nat.card E₂ = Nat.card F ^ (3 - Module.finrank F (fixN E₂))) : False := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ := hnc
  obtain ⟨a₁, b₁, c₁, rfl⟩ := mem_sStar_iff.mp (hE₁ hg₁)
  obtain ⟨a₂, b₂, c₂, rfl⟩ := mem_sStar_iff.mp (hE₂ hg₂)
  have e₁ := (uniTri_mul_self_eq_one_iff a₁ b₁ c₁).mp (h2₁ _ hg₁)
  have e₂ := (uniTri_mul_self_eq_one_iff a₂ b₂ c₂).mp (h2₂ _ hg₂)
  have hne' : a₁ * c₂ ≠ a₂ * c₁ := by
    intro h
    apply hne
    rw [uniTri_mul, uniTri_mul, h]
    congr 1 <;> ring
  by_cases h : a₁ * c₂ = 0
  · have h' : a₂ * c₁ ≠ 0 := fun h' => hne' (h.trans h'.symm)
    have ha₂ := left_ne_zero_of_mul h'
    have hc₁ := right_ne_zero_of_mul h'
    have ha₁ : a₁ = 0 := (mul_eq_zero.mp e₁).resolve_right hc₁
    have hc₂ : c₂ = 0 := (mul_eq_zero.mp e₂).resolve_left ha₂
    subst ha₁ hc₂
    exact false_of_noncommuting_aux hE₂ hE₁ h2₂ h2₁ ha₂ hc₁ hg₂ hg₁
      (by rwa [Subgroup.commutator_comm, inf_comm]) hcard₂ hcard₁
  · have ha₁ := left_ne_zero_of_mul h
    have hc₂ := right_ne_zero_of_mul h
    have hc₁ : c₁ = 0 := (mul_eq_zero.mp e₁).resolve_left ha₁
    have ha₂ : a₂ = 0 := (mul_eq_zero.mp e₂).resolve_right hc₂
    subst hc₁ ha₂
    exact false_of_noncommuting_aux hE₁ hE₂ h2₁ h2₂ ha₁ hc₂ hg₁ hg₂ hcomm hcard₁ hcard₂

theorem le_ln01_of_invariant {S : Subgroup (SL3 F)} (hS : S ≤ sStar) (hC : commN S = ln01)
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ S, ∀ x ∈ W, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W)
    (hWV : W ≠ ⊤) : W ≤ ln01 := by
  by_contra hle
  obtain ⟨w, hw, hw2⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hw2' : w 2 ≠ 0 := hw2
  have hdec : ∀ v : Fin 3 → F, v - (v 2 / w 2) • w ∈ ln01 := fun v => by
    show (v - (v 2 / w 2) • w) 2 = 0
    simp [div_mul_cancel₀ _ hw2']
  have hWc : ∀ g ∈ S, ∀ x ∈ W, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ W :=
    fun g hg x hx => W.sub_mem (hW g hg x hx) hx
  have hlp : ∀ g ∈ S, ∀ l ∈ ln01, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ l - l ∈ pt0 := by
    intro g hg l hl
    have hl2 : l 2 = 0 := hl
    obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hS hg)
    rw [uniTri_mulVec]
    exact ⟨by simp [hl2], by simp⟩
  have hpf : ∀ g ∈ S, ∀ p ∈ pt0, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p :=
    fun g hg p hp => pt0_le_fixN_of_le_sStar hS hp g hg
  have hsplit : ∀ g ∈ S, ∀ v : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v =
      (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((v 2 / w 2) • w) - (v 2 / w 2) • w) +
      (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (v - (v 2 / w 2) • w) -
        (v - (v 2 / w 2) • w)) := fun g _ v => by
    rw [Matrix.mulVec_sub]
    abel
  have h1 : ln01 ≤ W ⊔ pt0 := by
    rw [← hC, commN, Submodule.span_le]
    rintro _ ⟨g, hg, v, rfl⟩
    rw [hsplit g hg v]
    exact Submodule.add_mem_sup (hWc g hg _ (W.smul_mem _ hw)) (hlp g hg _ (hdec v))
  have h2 : ∀ g ∈ S, ∀ l ∈ ln01, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ l - l ∈ W := by
    intro g hg l hl
    obtain ⟨w', hw', p, hp, rfl⟩ := Submodule.mem_sup.mp (h1 hl)
    rw [Matrix.mulVec_add, hpf g hg p hp, add_sub_add_right_eq_sub]
    exact hWc g hg w' hw'
  have h3 : ln01 ≤ W := by
    rw [← hC, commN, Submodule.span_le]
    rintro _ ⟨g, hg, v, rfl⟩
    rw [hsplit g hg v]
    exact W.add_mem (hWc g hg _ (W.smul_mem _ hw)) (h2 g hg _ (hdec v))
  apply hWV
  rw [eq_top_iff]
  intro v _
  have := W.add_mem (W.smul_mem (v 2 / w 2) hw) (h3 (hdec v))
  rwa [add_sub_cancel] at this

theorem le_commN_of_invariant [Finite F] [CharP F 2] {S : Subgroup (SL3 F)} (hS : IsPGroup 2 S)
    (hC : Module.finrank F (commN S) = 2) {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ S, ∀ x ∈ W, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) (hWV : W ≠ ⊤) :
    W ≤ commN S := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hS
  set e := Matrix.SpecialLinearGroup.toLin' x with he
  have hC' : commN (S.map (MulAut.conj x).toMonoidHom) = ln01 := by
    apply Submodule.eq_of_le_of_finrank_eq (commN_le_ln01_of_le_sStar hx)
    rw [finrank_commN_map_conj, hC, finrank_ln01]
  set W' := W.map (e : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) with hW'def
  have hW' : ∀ g ∈ S.map (MulAut.conj x).toMonoidHom, ∀ y ∈ W',
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ W' := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨w, hw, rfl⟩
    refine ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w, hW g hg w hw, ?_⟩
    simp only [he, LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply]
    rw [mulVec_conj, mulVec_inv_mulVec]
  have hWV' : W' ≠ ⊤ := by
    intro htop
    apply hWV
    rw [eq_top_iff]
    intro v _
    have hv : e v ∈ W' := by rw [htop]; trivial
    rw [hW'def, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hv
    exact hv
  have := le_ln01_of_invariant hx hC' hW' hWV'
  rw [← hC', commN_map_conj] at this
  exact (Submodule.map_le_map_iff_of_injective e.injective _ _).mp this

end CFSG.Quasithin.MS93
