module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsComp
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp

public section

open Polynomial Module Multiplicative
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spLin_injective spEnd spForm_isAlt
  spForm_nondegenerate)
open CFSG.RankThree.PartOne.KCPrimary (primaryComponent mem_primaryComponent)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial
  aeval_reciprocalPolynomial_of_unit)

namespace CFSG.StandardType

namespace SpNsCont

open CoordSpNs

section Aeval

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

theorem apply_aeval_of_intertwine {A : Module.End K V} {B : Module.End K W} (P : V →ₗ[K] W)
    (h : ∀ v, P (A v) = B (P v)) (f : K[X]) (v : V) : P (aeval A f v) = aeval B f (P v) := by
  have hpow : ∀ (m : ℕ) (v : V), P ((A ^ m) v) = (B ^ m) (P v) := by
    intro m
    induction m with
    | zero => intro v; rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
    | succ m ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, h₁, h₂]
  | monomial m r =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, hpow]

theorem apply_aeval_of_mul {L : Type*} [CommRing L] [Algebra K L] {a : Module.End K V}
    (e : V →ₗ[K] L) {z : L} (h : ∀ v, e (a v) = z * e v) (f : K[X]) (v : V) :
    e (aeval a f v) = aeval z f * e v := by
  have hpow : ∀ (m : ℕ) (v : V), e ((a ^ m) v) = z ^ m * e v := by
    intro m
    induction m with
    | zero => intro v; rw [pow_zero, pow_zero, Module.End.one_apply, one_mul]
    | succ m ih => intro v; rw [pow_succ, pow_succ, Module.End.mul_apply, ih, h, mul_assoc]
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, map_add, h₁, h₂, add_mul]
  | monomial m r =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow, Algebra.smul_def, mul_assoc]

end Aeval

section Split

variable {F : Type} [Field F] {g : F[X]} [Fact (Irreducible g)] {p : ℕ} {D : Type}
  [AddCommGroup D] [Module F D] {c : D ≃ₗ[F] D}

omit [Fact (Irreducible g)] in
theorem pow_mul_pred_pow {M : Type*} [CommMonoid M] {z : M} (hp : 1 ≤ p) (hz : z ^ p = 1)
    (m : ℕ) : z ^ m * (z ^ (p - 1)) ^ m = 1 := by
  rw [← mul_pow, ← pow_succ', Nat.sub_add_cancel hp, hz, one_pow]

omit [Fact (Irreducible g)] in
theorem aeval_reciprocal_eq_zero {L : Type*} [Field L] [Algebra F L] {u v : L} (huv : u * v = 1)
    {f : F[X]} (hf : aeval v f = 0) : aeval u (reciprocalPolynomial f) = 0 := by
  have hu : u ≠ 0 := left_ne_zero_of_mul_eq_one huv
  have h := aeval_reciprocalPolynomial_of_unit (Units.mk0 u hu) f
  have hv : (((Units.mk0 u hu)⁻¹ : Lˣ) : L) = v := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    exact inv_eq_of_mul_eq_one_right huv
  rw [Units.val_mk0, hv, hf, mul_zero, smul_zero] at h
  exact h

theorem block_split (hbt : NsBlockType g p D c) (hp : 1 ≤ p) (hζ : AdjoinRoot.root g ^ p = 1)
    {m : ℕ} {f : F[X]} {y₀ : D} (hy₀ : y₀ ≠ 0)
    (h0 : aeval ((c ^ m : D ≃ₗ[F] D) : Module.End F D) f y₀ = 0) (y : D) :
    ∃ y₁ y₂ : D, y = y₁ + y₂ ∧ aeval ((c ^ m : D ≃ₗ[F] D) : Module.End F D) f y₁ = 0 ∧
      aeval ((c ^ m : D ≃ₗ[F] D) : Module.End F D) (reciprocalPolynomial f) y₂ = 0 := by
  have hinv := pow_mul_pred_pow hp hζ m
  rcases hbt with ⟨-, e, he⟩ | ⟨-, e, he⟩
  ·
    have hfa : ∀ (f' : F[X]) (v : D), e (aeval ((c ^ m : D ≃ₗ[F] D) : Module.End F D) f' v) =
        aeval (AdjoinRoot.root g ^ m) f' * e v :=
      apply_aeval_of_mul e.toLinearMap (fun v => sd_e_pow he m v)
    have hz : aeval (AdjoinRoot.root g ^ m) f = 0 := by
      have h1 := hfa f y₀
      rw [h0, map_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (e.map_ne_zero_iff.mpr hy₀)
    refine ⟨y, 0, (add_zero y).symm, ?_, map_zero _⟩
    apply e.injective
    rw [hfa, hz, zero_mul, map_zero]
  ·
    have h1 : ∀ (f' : F[X]) (v : D),
        (e (aeval ((c ^ m : D ≃ₗ[F] D) : Module.End F D) f' v)).1 =
          aeval (AdjoinRoot.root g ^ m) f' * (e v).1 :=
      apply_aeval_of_mul ((LinearMap.fst F _ _).comp e.toLinearMap)
        (fun v => congrArg Prod.fst (pr_e_pow he m v))
    have h2 : ∀ (f' : F[X]) (v : D),
        (e (aeval ((c ^ m : D ≃ₗ[F] D) : Module.End F D) f' v)).2 =
          aeval ((AdjoinRoot.root g ^ (p - 1)) ^ m) f' * (e v).2 :=
      apply_aeval_of_mul ((LinearMap.snd F _ _).comp e.toLinearMap)
        (fun v => congrArg Prod.snd (pr_e_pow he m v))
    have hy0 : e y₀ ≠ 0 := e.map_ne_zero_iff.mpr hy₀
    have h01 := h1 f y₀
    have h02 := h2 f y₀
    rw [h0, map_zero, Prod.fst_zero] at h01
    rw [h0, map_zero, Prod.snd_zero] at h02
    have hcase : aeval (AdjoinRoot.root g ^ m) f = 0 ∨
        aeval ((AdjoinRoot.root g ^ (p - 1)) ^ m) f = 0 := by
      by_contra hne
      push Not at hne
      exact hy0 (Prod.ext ((mul_eq_zero.mp h01.symm).resolve_left hne.1)
        ((mul_eq_zero.mp h02.symm).resolve_left hne.2))
    have hsplit : ∀ v : D, v = e.symm ((e v).1, 0) + e.symm (0, (e v).2) := fun v => by
      apply e.injective
      rw [map_add, e.apply_symm_apply, e.apply_symm_apply, Prod.mk_add_mk, add_zero, zero_add]
    rcases hcase with hz | hz
    · have hz' : aeval ((AdjoinRoot.root g ^ (p - 1)) ^ m) (reciprocalPolynomial f) = 0 :=
        aeval_reciprocal_eq_zero (by rw [mul_comm]; exact hinv) hz
      refine ⟨e.symm ((e y).1, 0), e.symm (0, (e y).2), hsplit y, ?_, ?_⟩
      · apply e.injective
        refine Prod.ext ?_ ?_
        · rw [h1, hz, zero_mul, map_zero, Prod.fst_zero]
        · rw [h2, e.apply_symm_apply, mul_zero, map_zero, Prod.snd_zero]
      · apply e.injective
        refine Prod.ext ?_ ?_
        · rw [h1, e.apply_symm_apply, mul_zero, map_zero, Prod.fst_zero]
        · rw [h2, hz', zero_mul, map_zero, Prod.snd_zero]
    · have hz' : aeval (AdjoinRoot.root g ^ m) (reciprocalPolynomial f) = 0 :=
        aeval_reciprocal_eq_zero hinv hz
      refine ⟨e.symm (0, (e y).2), e.symm ((e y).1, 0), ?_, ?_, ?_⟩
      · rw [add_comm]
        exact hsplit y
      · apply e.injective
        refine Prod.ext ?_ ?_
        · rw [h1, e.apply_symm_apply, mul_zero, map_zero, Prod.fst_zero]
        · rw [h2, hz, zero_mul, map_zero, Prod.snd_zero]
      · apply e.injective
        refine Prod.ext ?_ ?_
        · rw [h1, hz', zero_mul, map_zero, Prod.fst_zero]
        · rw [h2, e.apply_symm_apply, mul_zero, map_zero, Prod.snd_zero]


theorem galSigns_le_twistGroup [Finite F] [CharP F 2] [Fact p.Prime] (hbt : NsBlockType g p D c)
    (hζ : AdjoinRoot.root g ^ p = 1) (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hc : c ^ p = 1) {ω : LinearMap.BilinForm F D} (hωa : ω.IsAlt) (hωnd : ω.Nondegenerate)
    (hcω : ∀ x y, ω (c x) (c y) = ω x y) : galSigns p (Nat.card F) ≤ twistGroup ω c hc := by
  have hp : p.Prime := Fact.out
  have hζ0 : AdjoinRoot.root g ≠ 0 := hprim.ne_zero hp.ne_zero
  intro u hu
  rcases hbt with ⟨hσ, e, he⟩ | ⟨hσ, e, he⟩
  · have h1 : ∀ a, e.symm (sdC hζ0 a) = c (e.symm a) := fun a => by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply, sdC_apply]
    have hc' : ∀ a b, LinearMap.BilinForm.congr e ω (sdC hζ0 a) (sdC hζ0 b) =
        LinearMap.BilinForm.congr e ω a b := fun a b => by
      rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply, h1, h1, hcω]
    obtain ⟨T', hT'⟩ := mem_twistGroup.mp (galSigns_le_twistGroup_sd hζ hprim hσ hζ0
      (fun a => hωa (e.symm a)) (hωnd.congr e) hc' hu)
    refine mem_twistGroup.mpr ⟨e.trans (T'.trans e.symm), fun x y => ?_, fun x => ?_⟩
    · have h2 := hT'.1 (e x) (e y)
      simp only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply] at h2
      simpa only [LinearEquiv.trans_apply] using h2
    · have h2 : e ((c ^ (u : ZMod p).val) x) = (sdC hζ0 ^ (u : ZMod p).val) (e x) := by
        rw [sd_e_pow he, sdC_pow_apply]
      simp only [LinearEquiv.trans_apply]
      rw [h2, hT'.2, h1]
  · have hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0 := pow_ne_zero _ hζ0
    have h1 : ∀ a, e.symm (prC hζ0 hζ0' a) = c (e.symm a) := fun a => by
      apply e.injective
      obtain ⟨a₁, a₂⟩ := a
      rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply, prC_apply]
    have hc' : ∀ a b, LinearMap.BilinForm.congr e ω (prC hζ0 hζ0' a) (prC hζ0 hζ0' b) =
        LinearMap.BilinForm.congr e ω a b := fun a b => by
      rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply, h1, h1, hcω]
    obtain ⟨T', hT'⟩ := mem_twistGroup.mp (galSigns_le_twistGroup_pr hζ0 hζ0' hζ hprim hσ
      (fun a => hωa (e.symm a)) (hωnd.congr e) hc' hu)
    refine mem_twistGroup.mpr ⟨e.trans (T'.trans e.symm), fun x y => ?_, fun x => ?_⟩
    · have h2 := hT'.1 (e x) (e y)
      simp only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply] at h2
      simpa only [LinearEquiv.trans_apply] using h2
    · have h2 : e ((c ^ (u : ZMod p).val) x) = (prC hζ0 hζ0' ^ (u : ZMod p).val) (e x) := by
        rw [pr_e_pow he, ← prC_pow_apply hζ0 hζ0']
      simp only [LinearEquiv.trans_apply]
      rw [h2, hT'.2, h1]

end Split

section Form

variable {F : Type} [Field F] {n : ℕ} {D : Type} [AddCommGroup D] [Module F D] {s : ℕ}
  {κ : Type} {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
  {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
include hdec

theorem form_single_left (i : Fin s) (a : D) (d : Fin s → D) (w : κ → F) :
    spForm n F (Φ (Pi.single i a, 0)) (Φ (d, w)) = ω a (d i) := by
  rw [hdec, Prod.mk_zero_zero, map_zero, map_zero, LinearMap.zero_apply, add_zero,
    Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero,
      LinearMap.zero_apply]) (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem form_single_right (i : Fin s) (a : D) (d : Fin s → D) (w : κ → F) :
    spForm n F (Φ (d, w)) (Φ (Pi.single i a, 0)) = ω (d i) a := by
  rw [hdec, Prod.mk_zero_zero, map_zero, map_zero, add_zero,
    Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem isAlt_of_dec (i : Fin s) : ω.IsAlt := fun a => by
  have h := form_single_left hdec i a (Pi.single i a) 0
  rw [Pi.single_eq_same] at h
  rw [← h]
  exact spForm_isAlt _

theorem nondegenerate_of_dec (i : Fin s) : ω.Nondegenerate := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h0 : Φ (Pi.single i a, 0) = 0 := spForm_nondegenerate.1 _ fun v => by
      obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
      rw [form_single_left hdec]
      exact ha _
    have h1 : ((Pi.single i a : Fin s → D), (0 : κ → F)) = 0 := Φ.map_eq_zero_iff.mp h0
    have h2 := congrArg (fun z : (Fin s → D) × (κ → F) => z.1 i) h1
    simpa using h2
  · have h0 : Φ (Pi.single i a, 0) = 0 := spForm_nondegenerate.2 _ fun v => by
      obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
      rw [form_single_right hdec]
      exact ha _
    have h1 : ((Pi.single i a : Fin s → D), (0 : κ → F)) = 0 := Φ.map_eq_zero_iff.mp h0
    have h2 := congrArg (fun z : (Fin s → D) × (κ → F) => z.1 i) h1
    simpa using h2

end Form

section Frame

variable {F : Type} [Field F] {n p : ℕ} [NeZero p] {D : Type} [AddCommGroup D] [Module F D]
  {s : ℕ} {κ : Type} {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
  {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
  (hcω : ∀ x y, ω (c x) (c y) = ω x y)

theorem spEnd_torElt (t : Fin s → ZMod p) (y : (Fin s → D) × (κ → F)) :
    spEnd (torElt hc hdec hcω t) (Φ y) = Φ (torD c t y) := by
  have h := frameEnd_torElt hc hdec hcω t y
  rw [frameEnd_apply] at h
  rw [← h, LinearEquiv.apply_symm_apply]

theorem torElt_add (t t' : Fin s → ZMod p) :
    torElt hc hdec hcω (t + t') = torElt hc hdec hcω t * torElt hc hdec hcω t' := by
  rw [torElt, torElt, torElt, ofAdd_add, map_mul, map_mul]

theorem torElt_zero : torElt hc hdec hcω (0 : Fin s → ZMod p) = 1 := by
  rw [torElt, ofAdd_zero, map_one, map_one]

theorem torElt_neg (t : Fin s → ZMod p) :
    torElt hc hdec hcω (-t) = (torElt hc hdec hcω t)⁻¹ := by
  rw [torElt, torElt, ofAdd_neg, map_inv, map_inv]

theorem torElt_sub (t t' : Fin s → ZMod p) :
    torElt hc hdec hcω (t - t') = torElt hc hdec hcω t * (torElt hc hdec hcω t')⁻¹ := by
  rw [sub_eq_add_neg, torElt_add, torElt_neg]

theorem torElt_smul (a : ℕ) (t : Fin s → ZMod p) :
    torElt hc hdec hcω (a • t) = torElt hc hdec hcω t ^ a := by
  rw [torElt, torElt, ofAdd_nsmul, map_pow, map_pow]

theorem torElt_pow_p (t : Fin s → ZMod p) : torElt hc hdec hcω t ^ p = 1 := by
  rw [← torElt_smul]
  have h : p • t = 0 := by
    funext i
    simp
  rw [h, torElt_zero]

theorem torElt_comm (t t' : Fin s → ZMod p) :
    torElt hc hdec hcω t * torElt hc hdec hcω t' =
      torElt hc hdec hcω t' * torElt hc hdec hcω t := by
  rw [← torElt_add, ← torElt_add, add_comm]

theorem aeval_block_eq_zero {β : Fin s → ZMod p} {f : F[X]} {v : Fin n ⊕ Fin n → F}
    (hv : v ∈ primaryComponent (spEnd (torElt hc hdec hcω β)) f) (j : Fin s) :
    aeval ((c ^ (β j).val : D ≃ₗ[F] D) : Module.End F D) f ((Φ.symm v).1 j) = 0 := by
  have h2 : ∀ v' : Fin n ⊕ Fin n → F, Φ.symm.toLinearMap (spEnd (torElt hc hdec hcω β) v') =
      (torD c β : ((Fin s → D) × (κ → F)) ≃ₗ[F] _).toLinearMap (Φ.symm.toLinearMap v') := by
    intro v'
    obtain ⟨y, rfl⟩ := Φ.surjective v'
    simp only [LinearEquiv.coe_coe]
    rw [spEnd_torElt, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have h3 := apply_aeval_of_intertwine Φ.symm.toLinearMap h2 f v
  rw [mem_primaryComponent.mp hv, map_zero] at h3
  simp only [LinearEquiv.coe_coe] at h3
  have h4 := apply_aeval_of_intertwine ((LinearMap.proj j).comp (LinearMap.fst F _ _))
    (A := (torD c β : ((Fin s → D) × (κ → F)) ≃ₗ[F] _).toLinearMap)
    (B := ((c ^ (β j).val : D ≃ₗ[F] D) : Module.End F D)) (fun y => by
      obtain ⟨d, w⟩ := y
      rfl) f (Φ.symm v)
  rw [← h3] at h4
  simpa using h4.symm

theorem single_mem_primaryComponent {β : Fin s → ZMod p} {f : F[X]} {j : Fin s} {z : D}
    (hz : aeval ((c ^ (β j).val : D ≃ₗ[F] D) : Module.End F D) f z = 0) :
    Φ (Pi.single j z, 0) ∈ primaryComponent (spEnd (torElt hc hdec hcω β)) f := by
  rw [mem_primaryComponent]
  have h1 := apply_aeval_of_intertwine (A := ((c ^ (β j).val : D ≃ₗ[F] D) : Module.End F D))
    (B := spEnd (torElt hc hdec hcω β))
    (Φ.toLinearMap.comp ((LinearMap.inl F _ (κ → F)).comp (LinearMap.single F (fun _ => D) j)))
    (fun y => by
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
        LinearMap.single_apply]
      rw [spEnd_torElt, torD_single]) f z
  rw [hz, map_zero] at h1
  simpa using h1.symm

@[expose] noncomputable def frameSp
    (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F))
    (M : ((Fin s → D) × (κ → F)) ≃ₗ[F] ((Fin s → D) × (κ → F)))
    (hM : ∀ x y, spForm n F (Φ (M x)) (Φ (M y)) = spForm n F (Φ x) (Φ y)) : StatedSp n F :=
  (spIso n F).symm ⟨SpNS.frameUnit Φ M, SpNS.frameUnit_mem Φ hM⟩

omit [NeZero p] in
theorem frameEnd_frameSp (M : ((Fin s → D) × (κ → F)) ≃ₗ[F] ((Fin s → D) × (κ → F)))
    (hM : ∀ x y, spForm n F (Φ (M x)) (Φ (M y)) = spForm n F (Φ x) (Φ y))
    (y : (Fin s → D) × (κ → F)) : frameEnd Φ (frameSp Φ M hM) y = M y := by
  rw [frameEnd_apply, ← coe_spIso, frameSp, MulEquiv.apply_symm_apply]
  change Φ.symm (((SpNS.frameUnit Φ M : LinearMap.GeneralLinearGroup F _) :
    (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) (Φ y)) = M y
  rw [SpNS.frameUnit_apply, LinearEquiv.symm_apply_apply]

omit [NeZero p] in
theorem eq_of_frameEnd {Y Z : StatedSp n F} (h : ∀ y, frameEnd Φ Y y = frameEnd Φ Z y) :
    Y = Z := by
  have h1 : Y * Z⁻¹ = 1 := eq_one_of_frameEnd Φ _ fun y => by
    rw [frameEnd_mul, h, frameEnd_apply_inv]
  exact mul_inv_eq_one.mp h1

end Frame

section Setup

variable {F : Type} [Field F] {g : F[X]} [Fact (Irreducible g)] {n p : ℕ} [Fact p.Prime]
  {D : Type} [AddCommGroup D] [Module F D] {s : ℕ} {κ : Type} {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
  {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
  (hcω : ∀ x y, ω (c x) (c y) = ω x y)

omit [Fact p.Prime] in
theorem nontrivial_of_blockType (hbt : NsBlockType g p D c) : Nontrivial D := by
  rcases hbt with ⟨-, e, -⟩ | ⟨-, e, -⟩
  · exact e.toEquiv.nontrivial
  · exact e.toEquiv.nontrivial

omit [Fact (Irreducible g)] [Fact p.Prime] in
theorem neZero_of_frame [Nontrivial D] (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F))
    (i : Fin s) : NeZero n := by
  refine ⟨fun hn => ?_⟩
  subst hn
  obtain ⟨d, hd⟩ := exists_ne (0 : D)
  have h1 : Φ (Pi.single i d, 0) = Φ 0 := funext fun k => by rcases k with k | k <;> exact k.elim0
  have h2 := congrArg (fun y : (Fin s → D) × (κ → F) => y.1 i) (Φ.injective h1)
  simp only [Pi.single_eq_same, Prod.fst_zero, Pi.zero_apply] at h2
  exact hd h2

theorem torElt_ne_one (hbt : NsBlockType g p D c) (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {β : Fin s → ZMod p} {i : Fin s}
    (hi : β i ≠ 0) : torElt hc hdec hcω β ≠ 1 := by
  have : Nontrivial D := nontrivial_of_blockType hbt
  intro h
  obtain ⟨d, hd⟩ := exists_ne (0 : D)
  have h1 := frameEnd_torElt hc hdec hcω β (Pi.single i d, 0)
  rw [h, frameEnd_one, torD_single] at h1
  have h2 := congrArg (fun y : (Fin s → D) × (κ → F) => y.1 i) h1
  simp only [Pi.single_eq_same] at h2
  exact hd (block_pow_fix hbt hζ hprim hi h2.symm)

omit [Fact (Irreducible g)] [Fact p.Prime] in
theorem exists_card_eq_two_pow [Finite F] [CharP F 2] : ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hf]⟩

theorem spPrimaryBlocks_torElt [Finite F] [CharP F 2] (hp2 : p ≠ 2) (hbt : NsBlockType g p D c)
    (hζ : AdjoinRoot.root g ^ p = 1) (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    {β : Fin s → ZMod p} {i : Fin s} (hi : β i ≠ 0) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card F = 2 ^ f) :
    CFSG.RankThree.Classical.SpPrimaryBlocks 2 f p (torElt hc hdec hcω β)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n F (torElt hc hdec hcω β)) := by
  have : Nontrivial D := nontrivial_of_blockType hbt
  have : NeZero n := neZero_of_frame Φ i
  have hp : p.Prime := Fact.out
  have hxo : orderOf (torElt hc hdec hcω β) = p :=
    orderOf_eq_prime (torElt_pow_p hc hdec hcω β) (torElt_ne_one hc hdec hcω hbt hζ hprim hi)
  have hinj : Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n F) := by
    rw [← MonoidHom.ker_eq_bot_iff,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact le_antisymm
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center.trans
        AutPSp.center_eq_bot.le) bot_le
  have hxop : orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n F
      (torElt hc hdec hcω β)) = p := by rw [orderOf_injective _ hinj, hxo]
  exact ((CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
    Nat.prime_two hf hK hp hp2 hp2 (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) _ hxop).2) _ rfl hxo

end Setup

section Pull

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}

theorem isComponentOf_comap {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ)
    {x : StatedSp n F} {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {ψ x})) :
    IsComponentOf (L₁.comap ψ) (Subgroup.centralizer {x}) ∧ (L₁.comap ψ).map ψ = L₁ := by
  have hmapC : (Subgroup.centralizer ({x} : Set (StatedSp n F))).map ψ =
      ψ.range ⊓ Subgroup.centralizer {ψ x} := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hψ (by rw [map_mul, map_mul]; exact hy), rfl⟩
  rw [← hmapC] at hL₁
  exact CFSG.StandardType.isComponentOf_comap_of_injective ψ hψ hL₁

theorem false_of_forall_fix {L K : Subgroup (StatedSp n F)} (hL : IsComponentOf L K)
    (h : ∀ y ∈ L, ∀ v, spEnd y v = v) : False := by
  have hone : ∀ y ∈ L, y = 1 := fun y hy => by
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun v => ?_)
    rw [map_one]
    exact h y hy v
  exact LinSemisimple.false_of_isQuasisimple_of_commute hL.2.2 fun a ha b hb => by
    rw [hone a ha, hone b hb]

end Pull

end SpNsCont

end CFSG.StandardType
