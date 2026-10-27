module

public import CFSG.RankThree.PartOne.KF.QuadTorus
public import CFSG.RankThree.PartOne.KF.SpSylow

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG.GroupTheory.WeirSylow Module
open CFSG.Assembly.LowTwoRank (StatedSp)

section Trace

variable {K : Type} [Field K] [Finite K] [CharP K 2]

instance : CharP (Qext K) 2 := charP_of_injective_algebraMap (algebraMap K (Qext K)).injective 2

theorem two_eq_zero_qext : (2 : Qext K) = 0 := CharP.cast_eq_zero (Qext K) 2

theorem frobQ_ne_one : frobQ K ≠ 1 := by
  intro h
  have hc : Nat.card (Qext K ≃ₐ[K] Qext K) = 2 := FiniteField.natCard_algEquiv_extension K 2 2
  have hall : ∀ τ : Qext K ≃ₐ[K] Qext K, τ = 1 := fun τ => by
    rcases gal_cases τ with h1 | h1
    · exact h1
    · rw [h1, h]
  have hone : Nat.card (Qext K ≃ₐ[K] Qext K) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
  omega

@[expose] noncomputable def trQ : Qext K →ₗ[K] K := Algebra.trace K (Qext K)

theorem algebraMap_trQ (x : Qext K) : algebraMap K (Qext K) (trQ x) = x + frobQ K x := by
  have h := trace_eq_sum_automorphisms (K := K) (L := Qext K) x
  rw [Fintype.sum_eq_add (1 : Qext K ≃ₐ[K] Qext K) (frobQ K) (Ne.symm frobQ_ne_one)
    (fun τ hτ => absurd (gal_cases τ) (by tauto))] at h
  have h' : algebraMap K (Qext K) (Algebra.trace K (Qext K) x) = x + frobQ K x := by simpa using h
  exact h'

theorem trQ_frobQ (x : Qext K) : trQ (frobQ K x) = trQ x := by
  apply (algebraMap K (Qext K)).injective
  rw [algebraMap_trQ, algebraMap_trQ, frobQ_frobQ, add_comm]

theorem trQ_eq_zero_of_frob {z : Qext K} (hz : frobQ K z = z) : trQ z = 0 := by
  apply (algebraMap K (Qext K)).injective
  rw [algebraMap_trQ, hz, map_zero]
  calc z + z = 2 * z := by ring
    _ = 0 := by rw [two_eq_zero_qext, zero_mul]

theorem trQ_ne_zero : (trQ : Qext K →ₗ[K] K) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ : ∃ x : Qext K, frobQ K x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact frobQ_ne_one (AlgEquiv.ext hcon)
  have h0 : trQ x = 0 := by rw [h]; rfl
  have h2 := algebraMap_trQ x
  rw [h0, map_zero] at h2
  apply hx
  have h3 : frobQ K x = -x := eq_neg_of_add_eq_zero_right h2.symm
  rw [h3]
  exact (CharTwo.neg_eq x)

@[expose] noncomputable def qForm : LinearMap.BilinForm K (Qext K) :=
  twistSympForm trQ (frobQ K)

theorem qForm_apply (x y : Qext K) : qForm x y = trQ (x * frobQ K y) := rfl

theorem qForm_isAlt : (qForm (K := K)).IsAlt :=
  twistSympForm_isAlt frobQ_frobQ (fun _ hz => trQ_eq_zero_of_frob hz)

theorem qForm_nondegenerate : (qForm (K := K)).Nondegenerate :=
  twistSympForm_nondegenerate trQ_ne_zero frobQ_frobQ qForm_isAlt

theorem qForm_frobQ (x y : Qext K) : qForm (frobQ K x) (frobQ K y) = qForm x y := by
  have h1 : frobQ K x * frobQ K (frobQ K y) = frobQ K (x * frobQ K y) := by rw [map_mul]
  rw [qForm_apply, qForm_apply, h1, trQ_frobQ]

theorem qForm_mul_unit {u : (Qext K)ˣ} (hu : (u : Qext K) * frobQ K u = 1) (x y : Qext K) :
    qForm ((u : Qext K) * x) ((u : Qext K) * y) = qForm x y := by
  have := toModuleAut_mem_twist (trQ (K := K)) (frobQ K) hu x y
  simpa [qForm, Units.smul_def] using this

end Trace

section Space

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def formQ (K : Type) [Field K] [Finite K] [CharP K 2] :
    QV K (Fin 3) → QV K (Fin 3) → K :=
  fun x y => ∑ i, qForm (x i) (y i)

@[expose] noncomputable def M10 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) :=
  formIsometryGroup K (formQ K)

theorem mem_M10_iff (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) :
    g ∈ M10 K ↔ ∀ x y, ∑ i, qForm (g x i) (g y i) = ∑ i, qForm (x i) (y i) :=
  Iff.rfl

noncomputable abbrev sp3Space (K : Type) [Field K] [Finite K] [CharP K 2] :
    FormSpace K K :=
  FormSpace.pi (fun _ : Fin 3 => (⟨Qext K, fun x y => qForm x y⟩ : FormSpace K K))

theorem isSymplecticSpace_sp3 : IsSymplecticSpace (sp3Space K) :=
  isSymplecticSpace_pi _ (fun _ => ⟨qForm, fun _ _ => rfl, qForm_isAlt, qForm_nondegenerate⟩)

theorem finrank_sp3 : finrank K (sp3Space K).V = 2 * 3 := by
  rw [FormSpace.finrank_pi]
  simp [finrank_qext]

theorem nonempty_m10Equiv : Nonempty (↥(M10 K) ≃* ↥(StatedSp 3 K)) := by
  obtain ⟨B, hBF, hBa, hBn⟩ := isSymplecticSpace_sp3 (K := K)
  obtain ⟨ι⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry B
    (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K 3) hBa hBn
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [finrank_sp3, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard])
  let e₁ : (sp3Space K).isom ≃* (stdSympSpace K 3).isom :=
    formIsometryGroupCongr ι.toLinearEquiv fun x y => by
      rw [hBF]
      exact ι.map_app y x
  let M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun K (Fin 3 ⊕ Fin 3))
  have hmem : ∀ g : (stdSympSpace K 3).isom, M g.1 ∈ StatedSp 3 K := fun g => by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp]
    exact Subgroup.mem_map_of_mem _ (TauCeti.BilinForm.mem_isometryGroup_iff.2 g.2)
  let ψ₀ : (stdSympSpace K 3).isom →* StatedSp 3 K :=
    { toFun := fun g => ⟨M g.1, hmem g⟩
      map_one' := Subtype.ext (map_one M)
      map_mul' := fun g h => Subtype.ext (map_mul M g.1 h.1) }
  have hinj : Function.Injective ψ₀ := fun g h hgh =>
    Subtype.ext (M.injective (congrArg Subtype.val hgh))
  have hsurj : Function.Surjective ψ₀ := by
    rintro ⟨A, hA⟩
    have hA' := hA
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp] at hA'
    obtain ⟨g, hg, hgA⟩ := hA'
    refine ⟨⟨g, ?_⟩, Subtype.ext hgA⟩
    intro x y
    exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y
  have hbij : Function.Bijective (ψ₀.comp e₁.toMonoidHom) :=
    ⟨hinj.comp e₁.injective, hsurj.comp e₁.surjective⟩
  exact ⟨MulEquiv.ofBijective _ hbij⟩

instance : Finite (M10 K) := by
  obtain ⟨e⟩ := nonempty_m10Equiv (K := K)
  exact Finite.of_equiv _ e.symm.toEquiv

end Space

section Torus10

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem unit_mul_frob_eq_one_of_pow {x : (Qext K)ˣ} (hx : x ^ (Nat.card K + 1) = 1) :
    (x : Qext K) * frobQ K x = 1 := by
  have hq : (x : Qext K) ^ (Nat.card K + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  rw [frobQ_eq_inv hq]
  exact mul_inv_cancel₀ x.ne_zero

theorem unit_mul_frob_eq_one (hpq : p ∣ Nat.card K + 1) {x : (Qext K)ˣ} (hx : x ^ p = 1) :
    (x : Qext K) * frobQ K x = 1 := by
  apply unit_mul_frob_eq_one_of_pow
  obtain ⟨c, hc⟩ := hpq
  rw [hc, pow_mul, hx, one_pow]

theorem torusEquiv_mem_M10_of_norm {x : Fin 3 → (Qext K)ˣ}
    (hx : ∀ i, (x i : Qext K) * frobQ K (x i) = 1) : torusEquiv x ∈ M10 K := by
  rw [mem_M10_iff]
  intro v w
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torusEquiv_apply, torusEquiv_apply]
  exact qForm_mul_unit (hx i) _ _

theorem torusEquiv_mem_M10 (hpq : p ∣ Nat.card K + 1) {x : Fin 3 → (Qext K)ˣ}
    (hx : ∀ i, x i ^ p = 1) : torusEquiv x ∈ M10 K :=
  torusEquiv_mem_M10_of_norm fun i => unit_mul_frob_eq_one hpq (hx i)

@[expose] noncomputable def permEquiv (π : Equiv.Perm (Fin 3)) :
    QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  LinearEquiv.funCongrLeft K (Qext K) π.symm

theorem permEquiv_apply (π : Equiv.Perm (Fin 3)) (v : QV K (Fin 3)) (i : Fin 3) :
    permEquiv π v i = v (π.symm i) := rfl

@[expose] noncomputable def frobAt (s : Fin 3 → Bool) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  LinearEquiv.piCongrRight fun i =>
    if s i then (frobQ K).toLinearEquiv else LinearEquiv.refl K (Qext K)

theorem frobAt_apply (s : Fin 3 → Bool) (v : QV K (Fin 3)) (i : Fin 3) :
    frobAt s v i = if s i then frobQ K (v i) else v i := by
  by_cases h : s i <;> simp [frobAt, h]

theorem permEquiv_mem_M10 (π : Equiv.Perm (Fin 3)) : permEquiv (K := K) π ∈ M10 K := by
  rw [mem_M10_iff]
  intro x y
  simp only [permEquiv_apply]
  exact Equiv.sum_comp π.symm (fun i => qForm (x i) (y i))

theorem frobAt_mem_M10 (s : Fin 3 → Bool) : frobAt (K := K) s ∈ M10 K := by
  rw [mem_M10_iff]
  intro x y
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frobAt_apply, frobAt_apply]
  by_cases h : s i
  · simp only [h, ite_true]
    exact qForm_frobQ _ _
  · simp [h]

@[expose] noncomputable def sgnPerm (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  permEquiv π * frobAt s

theorem sgnPerm_mem_M10 (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    sgnPerm (K := K) π s ∈ M10 K :=
  (M10 K).mul_mem (permEquiv_mem_M10 π) (frobAt_mem_M10 s)

theorem sgnPerm_apply (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : QV K (Fin 3)) (i : Fin 3) :
    sgnPerm π s v i = if s (π.symm i) then frobQ K (v (π.symm i)) else v (π.symm i) := by
  show frobAt s v (π.symm i) = _
  rw [frobAt_apply]

theorem conj_eq_of_intertwine_aux {ι : Type} (g : QV K ι ≃ₗ[K] QV K ι) (x y : ι → (Qext K)ˣ)
    (h : ∀ w, g (torusEquiv x w) = torusEquiv y (g w)) : g * torusEquiv x * g⁻¹ = torusEquiv y := by
  refine LinearEquiv.ext fun w => ?_
  have : g (torusEquiv x (g⁻¹ w)) = torusEquiv y w := by
    rw [h]
    simp
  simpa using this

theorem sgnPerm_conj (hpq : p ∣ Nat.card K + 1) (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (x y : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1)
    (hy : ∀ i, y i = if s (π.symm i) then (x (π.symm i))⁻¹ else x (π.symm i)) :
    sgnPerm π s * torusEquiv x * (sgnPerm π s)⁻¹ = torusEquiv y := by
  refine conj_eq_of_intertwine_aux _ _ _ fun w => ?_
  have hσ : ∀ j, frobQ K (x j : Qext K) = (((x j)⁻¹ : (Qext K)ˣ) : Qext K) := fun j => by
    have h1 := unit_mul_frob_eq_one hpq (hx j)
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right h1
  funext i
  rw [sgnPerm_apply, torusEquiv_apply, torusEquiv_apply, sgnPerm_apply]
  by_cases h : s (π.symm i)
  · simp only [h, ite_true, map_mul, hσ, hy i]
  · simp [h, hy i]

end Torus10

section Emb10

open CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def sqVec (d : Fin 4 → (Qext K)ˣ) : Fin 3 → (Qext K)ˣ :=
  ![d 0 * d 1, d 0 * d 2, d 0 * d 3]

@[expose] noncomputable def sqCoords : torusVec p 4 (Qext K) →* (Fin 3 → (Qext K)ˣ) where
  toFun d := sqVec (d : Fin 4 → (Qext K)ˣ)
  map_one' := by
    funext i
    fin_cases i <;> simp [sqVec]
  map_mul' a b := by
    funext i
    fin_cases i <;> simp [sqVec, mul_mul_mul_comm]

omit [Finite K] in
theorem sqCoords_apply (d : torusVec p 4 (Qext K)) :
    sqCoords d = ![(d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 1,
      (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 2,
      (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 3] := rfl

omit [Finite K] in
theorem sqCoords_pow (d : torusVec p 4 (Qext K)) (i : Fin 3) : sqCoords d i ^ p = 1 := by
  have h := d.2.1
  fin_cases i <;> simp [sqCoords_apply, mul_pow, h 0, h 1, h 2, h 3]

omit [Finite K] in
theorem torusVec_prod_four (d : torusVec p 4 (Qext K)) :
    (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 1 * (d : Fin 4 → (Qext K)ˣ) 2 *
      (d : Fin 4 → (Qext K)ˣ) 3 = 1 := by
  have := d.2.2
  simpa [Fin.prod_univ_four] using this

omit [Finite K] in
theorem eq_one_of_mul_self_of_pow {u : (Qext K)ˣ} (hp : Odd p) (h2 : u * u = 1)
    (hp1 : u ^ p = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := hp
  have : u ^ p = u := by
    rw [hk, pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  rw [← this]
  exact hp1

omit [Finite K] in
theorem sqCoords_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (sqCoords (p := p) (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have h0 : (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 1 = 1 := by
    simpa [sqCoords_apply] using congrFun hd 0
  have h1 : (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 2 = 1 := by
    simpa [sqCoords_apply] using congrFun hd 1
  have h2 : (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 3 = 1 := by
    simpa [sqCoords_apply] using congrFun hd 2
  have hprod := torusVec_prod_four d
  have e1 := eq_inv_of_mul_eq_one_right h0
  have e2 := eq_inv_of_mul_eq_one_right h1
  have e3 := eq_inv_of_mul_eq_one_right h2
  rw [e1, e2, e3] at hprod
  have hsq : (d : Fin 4 → (Qext K)ˣ) 0 * (d : Fin 4 → (Qext K)ˣ) 0 = 1 := by
    have : ((d : Fin 4 → (Qext K)ˣ) 0)⁻¹ * ((d : Fin 4 → (Qext K)ˣ) 0)⁻¹ = 1 := by
      calc _ = (d : Fin 4 → (Qext K)ˣ) 0 * ((d : Fin 4 → (Qext K)ˣ) 0)⁻¹ *
            ((d : Fin 4 → (Qext K)ˣ) 0)⁻¹ * ((d : Fin 4 → (Qext K)ˣ) 0)⁻¹ := by
            rw [mul_inv_cancel, one_mul]
        _ = 1 := hprod
    simpa [mul_inv_rev] using congrArg (fun u => u⁻¹) this
  have hd0 : (d : Fin 4 → (Qext K)ˣ) 0 = 1 :=
    eq_one_of_mul_self_of_pow (hp.odd_of_ne_two hp2) hsq (d.2.1 0)
  apply Subtype.ext
  funext i
  fin_cases i
  · exact hd0
  · simpa [hd0] using e1
  · simpa [hd0] using e2
  · simpa [hd0] using e3

omit [Finite K] in
theorem sqCoords_surjective (hp : p.Prime) (hp2 : p ≠ 2) (x : Fin 3 → (Qext K)ˣ)
    (hx : ∀ i, x i ^ p = 1) : ∃ d : torusVec p 4 (Qext K), sqCoords d = x := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  set m := x 0 * x 1 * x 2 with hm
  have hmp : m ^ p = 1 := by simp [hm, mul_pow, hx]
  set d0 := m ^ (k + 1) with hd0
  have hd00 : d0 * d0 = m := by
    rw [hd0, ← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, hmp, one_mul]
  have hd0p : d0 ^ p = 1 := by
    rw [hd0, ← pow_mul, mul_comm, pow_mul, hmp, one_pow]
  refine ⟨⟨![d0, x 0 * d0⁻¹, x 1 * d0⁻¹, x 2 * d0⁻¹], ⟨fun i => ?_, ?_⟩⟩, ?_⟩
  · fin_cases i <;> simp [mul_pow, inv_pow, hd0p, hx]
  · simp only [Fin.prod_univ_four]
    show d0 * (x 0 * d0⁻¹) * (x 1 * d0⁻¹) * (x 2 * d0⁻¹) = 1
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    have h0 : ((d0 : (Qext K)ˣ) : Qext K) ≠ 0 := d0.ne_zero
    have h := congrArg Units.val hd00
    simp only [hm, Units.val_mul] at h
    field_simp
    linear_combination -h
  · funext i
    fin_cases i <;> simp [sqCoords_apply]

@[expose] noncomputable def emb10 :
    torusVec p 4 (Qext K) →* (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) :=
  torusHom.comp sqCoords

theorem emb10_apply (d : torusVec p 4 (Qext K)) (w : QV K (Fin 3)) (i : Fin 3) :
    emb10 d w i = (sqCoords d i : Qext K) * w i := rfl

theorem emb10_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (emb10 (p := p) (K := K)) := by
  intro a b h
  apply sqCoords_injective hp hp2
  funext i
  have := congrArg (fun g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) => g (fun _ => 1) i) h
  simp only [emb10_apply, mul_one] at this
  exact Units.ext this

theorem emb10_pow (d : torusVec p 4 (Qext K)) : emb10 d ^ p = 1 := by
  rw [← map_pow]
  have : d ^ p = 1 := Subtype.ext (funext fun i => d.2.1 i)
  rw [this, map_one]

theorem emb10_comm (v w : torusVec p 4 (Qext K)) : emb10 v * emb10 w = emb10 w * emb10 v := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem emb10_mem_M10 (hpq : p ∣ Nat.card K + 1) (d : torusVec p 4 (Qext K)) :
    emb10 d ∈ M10 K :=
  torusEquiv_mem_M10 hpq (sqCoords_pow d)

end Emb10

section Sylow10

open CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem factorization_card_m10 (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (M10 K)).factorization p = 3 * (Nat.card (Qext K)ˣ).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := nonempty_m10Equiv (K := K)
  rw [Nat.card_congr e.toEquiv]
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hpK : ¬ p ∣ Fintype.card K := by
    intro h
    rw [← hcard] at h
    have h1 : p ∣ 1 := (Nat.dvd_add_right h).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hq : ((Fintype.card K : ℕ) : ZMod p) = -1 := by
    have h1 : (((Nat.card K + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    rw [Nat.cast_add, Nat.cast_one, hcard] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = 2 := by
    rw [hq]
    refine orderOf_neg_one.trans ?_
    have : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
    rw [this]
    simp [hp2]
  rw [factorization_card_statedSp (hp.odd_of_ne_two hp2) K hpK 3, hord]
  have h2 : padicValNat p ((2 * 3 / 2).factorial) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h6 : p ∣ 2 * 3 := by simpa [Nat.factorial] using h
    rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
    · have := Nat.le_of_dvd (by norm_num) h6
      omega
    · have := Nat.le_of_dvd (by norm_num) h6
      omega
  have hev : Even 2 := even_two
  simp only [hev, ite_true] at h2 ⊢
  rw [h2, add_zero, Nat.card_units, FiniteField.natCard_extension K 2 2,
    Nat.factorization_def _ hp, hcard]
  norm_num [mul_comm]

@[expose] noncomputable def sylowHom3 (S : Subgroup (Qext K)ˣ) :
    (Fin 3 → ↥S) →* (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) :=
  torusHom.comp (MonoidHom.pi fun i => S.subtype.comp (Pi.evalMonoidHom (fun _ : Fin 3 => ↥S) i))

theorem sylowHom3_apply (S : Subgroup (Qext K)ˣ) (x : Fin 3 → ↥S) (w : QV K (Fin 3)) (i : Fin 3) :
    sylowHom3 S x w i = ((x i : (Qext K)ˣ) : Qext K) * w i := rfl

theorem sylowHom3_eq_torusEquiv (S : Subgroup (Qext K)ˣ) (x : Fin 3 → ↥S) :
    sylowHom3 S x = torusEquiv (fun i => (x i : (Qext K)ˣ)) := rfl

theorem sylowHom3_injective (S : Subgroup (Qext K)ˣ) :
    Function.Injective (sylowHom3 (K := K) S) := by
  intro x y h
  funext i
  have := congrArg (fun g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) => g (fun _ => 1) i) h
  simp only [sylowHom3_apply, mul_one] at this
  exact Subtype.ext (Units.ext this)

theorem pow_card_succ_eq_one_of_mem_sylow (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (S : Sylow p (Qext K)ˣ) {u : (Qext K)ˣ}
    (hu : u ∈ (S : Subgroup (Qext K)ˣ)) : u ^ (Nat.card K + 1) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') (⟨u, hu⟩ : ↥(S : Subgroup (Qext K)ˣ))
  have hk' : orderOf u = p ^ k := by rwa [← Subgroup.orderOf_coe] at hk
  have h1 : orderOf u ∣ Nat.card K ^ 2 - 1 := by
    have := orderOf_dvd_natCard u
    rwa [Nat.card_units, FiniteField.natCard_extension K 2 2] at this
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    cases h : Nat.card K with
    | zero => omega
    | succ n => simp [sq]; ring_nf; omega
  have hcop : Nat.Coprime (orderOf u) (Nat.card K - 1) := by
    rw [hk']
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_pred hp hp2 hpq))
  rw [h2] at h1
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h1)

theorem sylowHom3_range_le (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (S : Sylow p (Qext K)ˣ) : (sylowHom3 (K := K) (S : Subgroup (Qext K)ˣ)).range ≤ M10 K := by
  rintro _ ⟨x, rfl⟩
  rw [sylowHom3_eq_torusEquiv]
  exact torusEquiv_mem_M10_of_norm fun i =>
    unit_mul_frob_eq_one_of_pow (pow_card_succ_eq_one_of_mem_sylow hp hp2 hpq S (x i).2)

theorem card_sylowHom3_range (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (S : Sylow p (Qext K)ˣ) :
    Nat.card (sylowHom3 (K := K) (S : Subgroup (Qext K)ˣ)).range =
      p ^ (Nat.card (M10 K)).factorization p := by
  have hinj := sylowHom3_injective (K := K) (S : Subgroup (Qext K)ˣ)
  rw [factorization_card_m10 hp hp5 hpq,
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have : Fact p.Prime := ⟨hp⟩
  rw [Sylow.card_eq_multiplicity S, ← pow_mul, mul_comm]

theorem exists_conj_into_T10 (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (X : Subgroup ↥(M10 K)) (hX : ∀ x ∈ X, x ^ p = 1) :
    ∃ g : ↥(M10 K), ∀ x ∈ X, g * x * g⁻¹ ∈
      (emb10 : torusVec p 4 (Qext K) →* (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf
        (M10 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let S : Sylow p (Qext K)ˣ := default
  let P : Subgroup ↥(M10 K) :=
    (sylowHom3 (K := K) (S : Subgroup (Qext K)ˣ)).range.subgroupOf (M10 K)
  have hPcard : Nat.card P = p ^ (Nat.card (M10 K)).factorization p := by
    rw [← card_sylowHom3_range hp hp5 hpq S]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sylowHom3_range_le hp hp2 hpq S)).toEquiv
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P hPcard X hX
  refine ⟨g, fun x hx => ?_⟩
  have hmem : ((g * x * g⁻¹ : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ∈
      (sylowHom3 (K := K) (S : Subgroup (Qext K)ˣ)).range := hg x hx
  obtain ⟨y, hy⟩ := hmem
  have hxp : ((g * x * g⁻¹ : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ^ p = 1 := by
    have : (g * x * g⁻¹) ^ p = 1 := by
      rw [conj_pow, hX x hx, mul_one, mul_inv_cancel]
    simpa using congrArg Subtype.val this
  have hyp : y ^ p = 1 := by
    apply sylowHom3_injective (K := K) (S : Subgroup (Qext K)ˣ)
    rw [map_pow, hy, hxp, map_one]
  have hyi : ∀ i, ((y i : (Qext K)ˣ)) ^ p = 1 := fun i => by
    have := congrArg (fun z : Fin 3 → ↥(S : Subgroup (Qext K)ˣ) =>
      ((z i : ↥(S : Subgroup (Qext K)ˣ)) : (Qext K)ˣ)) hyp
    simpa using this
  obtain ⟨d, hd⟩ := sqCoords_surjective hp hp2 (fun i => (y i : (Qext K)ˣ)) hyi
  rw [Subgroup.mem_subgroupOf]
  refine ⟨d, ?_⟩
  rw [← hy, sylowHom3_eq_torusEquiv]
  show torusEquiv (sqCoords d) = torusEquiv _
  rw [hd]

end Sylow10

end CFSG.RankThree.PartOne.KFQ
