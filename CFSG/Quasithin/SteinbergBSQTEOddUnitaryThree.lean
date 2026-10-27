module

public import CFSG.Quasithin.SteinbergBSQTEInvolutionSylow
public import CFSG.CharacterTheory.Wreathed.OddUnitaryThreeCentralizerCore
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup Module CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.Wreathed.OddUnitaryThreeCentralizerCore CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial QTEInvolutionSylow

namespace QTEOddUnitaryThree

variable {p f : ℕ} {K : Type} [Field K]

theorem card_eq_sq (h : UnitaryFieldData p f K) : Nat.card K = (p ^ f) ^ 2 := by
  rw [h.card, ← pow_mul, mul_comm]

variable [Fact p.Prime] [Finite K]

noncomputable abbrev frob (h : UnitaryFieldData p f K) : K ≃+* K :=
  CatalogueBUnitaryTwo.unitaryFieldConjugation p f (card_eq_sq h)

theorem frob_apply (h : UnitaryFieldData p f K) (c : K) : frob h c = h.bar c := by
  rw [frob, CatalogueBUnitaryTwo.unitaryFieldConjugation_apply, UnitaryFieldData.bar_apply]

@[expose] noncomputable def frobForm (h : UnitaryFieldData p f K) (n : ℕ) :
    (Fin n → K) →ₛₗ[(frob h).toRingHom] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (frob h).toRingHom (RingHom.id K) (fun x y => ∑ i, frob h (x i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
      rfl)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_left_comm])

theorem frobForm_apply (h : UnitaryFieldData p f K) (n : ℕ) (x y : Fin n → K) :
    frobForm h n x y = stdHermForm h n x y := by
  change ∑ i, frob h (x i) * y i = _
  rw [stdHermForm_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [frob_apply]

theorem frobForm_isSymm (h : UnitaryFieldData p f K) (n : ℕ) : (frobForm h n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  change frob h (frobForm h n x y) = frobForm h n y x
  rw [frobForm_apply, frobForm_apply, frob_apply]
  exact (stdHermForm_isSymm h n).eq x y

theorem frobForm_nondegenerate (h : UnitaryFieldData p f K) (n : ℕ) :
    (frobForm h n).Nondegenerate := by
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · have h1 := hx (Pi.single i 1)
    rw [frobForm_apply, stdHermForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (by simp)] at h1
    simp only [Pi.single_eq_same, mul_one] at h1
    have h2 : h.bar (h.bar (x i)) = h.bar 0 := by rw [h1]
    rw [h.bar_bar, map_zero] at h2
    exact h2
  · have h1 := hy (Pi.single i 1)
    rw [frobForm_apply, stdHermForm_single] at h1
    exact h1

variable (K) in
@[expose] noncomputable def glEquiv (n : ℕ) : GL (Fin n) K ≃* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)

omit [Fact p.Prime] [Finite K] in
theorem glEquiv_apply (n : ℕ) (g : GL (Fin n) K) (v : Fin n → K) :
    glEquiv K n g v = Matrix.mulVec (g : Matrix (Fin n) (Fin n) K) v :=
  rfl

omit [Fact p.Prime] [Finite K] in
theorem glEquiv_toLinearMap (n : ℕ) (g : GL (Fin n) K) :
    (glEquiv K n g).toLinearMap = Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) :=
  rfl

@[expose] noncomputable def unitaryHom (h : UnitaryFieldData p f K) :
    unitarySU p f K 3 →* specialIsometry (frobForm h 3) where
  toFun g := ⟨⟨glEquiv K 3 (g : GL (Fin 3) K), fun x y => by
      rw [glEquiv_apply, glEquiv_apply, frobForm_apply, frobForm_apply]
      exact ((mem_unitarySU_iff_isometry h).1 g.2).2 x y⟩, by
    rw [mem_specialIsometry_iff]
    change LinearMap.det (glEquiv K 3 (g : GL (Fin 3) K)).toLinearMap = 1
    rw [glEquiv_toLinearMap, LinearMap.det_toLin']
    exact ((mem_unitarySU_iff_isometry h).1 g.2).1⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (glEquiv K 3)))
  map_mul' g g' := Subtype.ext (Subtype.ext (map_mul (glEquiv K 3) (g : GL (Fin 3) K) g'))

theorem unitaryHom_bijective (h : UnitaryFieldData p f K) :
    Function.Bijective (unitaryHom h) := by
  refine ⟨fun g g' hgg' => ?_, fun e => ?_⟩
  · have h1 : glEquiv K 3 (g : GL (Fin 3) K) = glEquiv K 3 g' :=
      congrArg (fun x : specialIsometry (frobForm h 3) => x.val.val) hgg'
    exact Subtype.ext ((glEquiv K 3).injective h1)
  · set g₀ : GL (Fin 3) K := (glEquiv K 3).symm e.val.val with hg₀
    have hg₀e : glEquiv K 3 g₀ = e.val.val := (glEquiv K 3).apply_symm_apply _
    have hmem : g₀ ∈ unitarySU p f K 3 := by
      rw [mem_unitarySU_iff_isometry h]
      refine ⟨?_, fun x y => ?_⟩
      · rw [← LinearMap.det_toLin', ← glEquiv_toLinearMap, hg₀e]
        exact (mem_specialIsometry_iff (frobForm h 3) e.val).1 e.2
      · rw [← glEquiv_apply, ← glEquiv_apply, hg₀e, ← frobForm_apply, ← frobForm_apply]
        exact e.val.2 x y
    exact ⟨⟨g₀, hmem⟩, Subtype.ext (Subtype.ext hg₀e)⟩

@[expose] noncomputable def unitaryEquiv (h : UnitaryFieldData p f K) :
    unitarySU p f K 3 ≃* specialIsometry (frobForm h 3) :=
  MulEquiv.ofBijective (unitaryHom h) (unitaryHom_bijective h)

omit [Fact p.Prime] [Finite K] in
theorem finrank_three : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K

theorem map_le_scalarCenter (h : UnitaryFieldData p f K) {D : Subgroup (unitarySU p f K 3)}
    (hD : D ≤ unitaryScalars h 3) :
    D.map (unitaryEquiv h).toMonoidHom ≤ scalarCenter (frobForm h 3) finrank_three := by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨c, hcn, hc3, hdc⟩ := mem_unitaryScalars.1 (hD hd)
  have hc1 : frob h (c : K) * (c : K) = 1 := by
    rw [frob_apply, mul_comm]
    exact hcn
  let a : normOneUnits (sigma := frob h) := ⟨c, hc1⟩
  have ha3 : a ∈ cubicUnits (sigma := frob h) := by
    change a ^ 3 = 1
    exact Subtype.ext (by simpa using hc3)
  refine ⟨⟨a, ha3⟩, Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))⟩
  rw [scalarSpecial_apply]
  change (c : K) • v = Matrix.mulVec ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) v
  rw [hdc, Matrix.GeneralLinearGroup.coe_scalar]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

section Plane

variable {W : Type*} [AddCommGroup W] [Module K W]

omit [Fact p.Prime] [Finite K] in
theorem generalLinearEquiv_symm_apply (a : W ≃ₗ[K] W) (x : W) :
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm a :
      LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) x = a x := by
  rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap, MulEquiv.apply_symm_apply]
  rfl

omit [Fact p.Prime] [Finite K] in
@[expose] noncomputable def isometryToSesq {σ₁ : K ≃+* K} {σ₂ : K →+* K}
    (B₁ : W →ₛₗ[σ₁.toRingHom] W →ₗ[K] K) (B₂ : W →ₛₗ[σ₂] W →ₗ[K] K)
    (hB : ∀ x y, B₁ x y = B₂ x y) : isometryGroup B₁ ≃* sesqUnitaryGroup B₂ where
  toFun a := ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm a.val, fun x y => by
    rw [generalLinearEquiv_symm_apply, generalLinearEquiv_symm_apply, ← hB, ← hB]
    exact a.2 x y⟩
  invFun g := ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv K W
      (g : LinearMap.GeneralLinearGroup K W), fun x y => by
    rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, hB, hB]
    exact g.2 x y⟩
  left_inv a :=
    Subtype.ext ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).apply_symm_apply _)
  right_inv g :=
    Subtype.ext ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm_apply_apply _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

omit [Fact p.Prime] [Finite K] in
theorem map_specialIsometry_isometryToSesq [FiniteDimensional K W] {σ₁ : K ≃+* K}
    {σ₂ : K →+* K} (B₁ : W →ₛₗ[σ₁.toRingHom] W →ₗ[K] K) (B₂ : W →ₛₗ[σ₂] W →ₗ[K] K)
    (hB : ∀ x y, B₁ x y = B₂ x y) :
    (specialIsometry B₁).map (isometryToSesq B₁ B₂ hB).toMonoidHom =
      (sesqSpecialUnitaryGroup B₂).subgroupOf (sesqUnitaryGroup B₂) := by
  have hdet : ∀ a : isometryGroup B₁,
      LinearMap.det ((isometryToSesq B₁ B₂ hB a : LinearMap.GeneralLinearGroup K W) :
        W →ₗ[K] W) = LinearMap.det a.val.toLinearMap := by
    intro a
    congr 1
  ext g
  rw [mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(isometryToSesq B₁ B₂ hB a).2, ?_⟩
    change LinearMap.det ((isometryToSesq B₁ B₂ hB a : LinearMap.GeneralLinearGroup K W) :
      W →ₗ[K] W) = 1
    rw [hdet]
    exact (mem_specialIsometry_iff B₁ a).1 ha
  · rintro ⟨-, hdetg⟩
    refine ⟨(isometryToSesq B₁ B₂ hB).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    refine (mem_specialIsometry_iff B₁ _).2 ?_
    rw [← hdet, MulEquiv.apply_symm_apply]
    exact hdetg

end Plane

section PlaneTwoLocal

variable (h : UnitaryFieldData p f K) {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] (B : W →ₛₗ[(frob h).toRingHom] W →ₗ[K] K)

theorem eigenScalar_mem_normOne (h2 : (2 : K) ≠ 0) (hW : Module.finrank K W = 2)
    (hsym : B.IsSymm) (hnd : B.Nondegenerate) {a : W ≃ₗ[K] W} (haB : a ∈ isometryGroup B)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (han : a ≠ LinearEquiv.neg K) {g : W ≃ₗ[K] W}
    (hgB : g ∈ isometryGroup B) (hg : g ∈ centralizer ({a} : Set (W ≃ₗ[K] W))) :
    (eigenScalarHom a ⟨g, hg⟩).1 ∈ normOneUnits (sigma := frob h) ∧
      (eigenScalarHom a ⟨g, hg⟩).2 ∈ normOneUnits (sigma := frob h) := by
  obtain ⟨hm, hp⟩ := finrank_eigenspaces_eq_one h2 hW ha2 ha1 han
  have hinv : Function.Involutive (a : Module.End K W) := fun v => by
    have h' := congrArg (fun e : W ≃ₗ[K] W => e v) ha2
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, LinearEquiv.coe_coe] using h'
  have hcompl := involution_spaces_isCompl h2 (a : Module.End K W) hinv
  have horth : ∀ x ∈ minusSpace (a : Module.End K W), ∀ y ∈ plusSpace (a : Module.End K W),
      B x y = 0 := fun x hx y hy => involution_eigenspaces_orthogonal B h2 a haB x y hx hy
  have hndm := orthogonal_restriction_nondegenerate B hsym hnd _ _ hcompl horth
  have hndp := orthogonal_restriction_nondegenerate B hsym hnd _ _ hcompl.symm
    fun y hy x hx => hsym.eq_iff.mpr (horth x hx y hy)
  have key : ∀ μ : K, Module.finrank K (Module.End.eigenspace (a : Module.End K W) μ) = 1 →
      (B.domRestrict₁₂ (Module.End.eigenspace (a : Module.End K W) μ)
        (Module.End.eigenspace (a : Module.End K W) μ)).Nondegenerate →
      (eigenspaceRestriction (a : Module.End K W) μ g (comm_of_mem_centralizer hg)).det ∈
        normOneUnits (sigma := frob h) := by
    intro μ hμ hndμ
    have : Nontrivial (Module.End.eigenspace (a : Module.End K W) μ) :=
      Module.nontrivial_of_finrank_pos (by rw [hμ]; norm_num)
    set r := eigenspaceRestriction (a : Module.End K W) μ g (comm_of_mem_centralizer hg)
    have hr : r = LinearEquiv.smulOfUnit r.det := line_equiv_eq_smul_det hμ r
    refine scalar_norm_one_of_isometry _ hndμ r.det ?_
    change LinearEquiv.smulOfUnit r.det ∈ isometryGroup _
    rw [← hr]
    intro x y
    change B (r x : W) (r y : W) = B x y
    rw [eigenspaceRestriction_apply, eigenspaceRestriction_apply]
    exact hgB x y
  exact ⟨key (-1) hm hndm, key 1 hp hndp⟩

theorem card_isometryGroup_plane (hW : Module.finrank K W = 2) (B₂ : W →ₛₗ[h.bar] W →ₗ[K] K)
    (hB : ∀ x y, B x y = B₂ x y) (hsym₂ : B₂.IsSymm) (hl₂ : B₂.SeparatingLeft) :
    Nat.card (isometryGroup B) = p ^ f * ((p ^ f + 1) * ((p ^ f) ^ 2 - 1)) := by
  rw [Nat.card_congr (isometryToSesq B B₂ hB).toEquiv]
  have hord := (unitary_full_group_order h hsym₂ hl₂ hW (by norm_num)).1
  have hq1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos (Fact.out : p.Prime).pos f)
  have e : (((p ^ f * ((p ^ f + 1) * ((p ^ f) ^ 2 - 1)) : ℕ)) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 2, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    push_cast [Nat.cast_sub hq1]
    ring
  exact_mod_cast hord.trans e.symm

omit [FiniteDimensional K W] in
@[expose] def centralizerInclusion (a : isometryGroup B) :
    centralizer ({a} : Set (isometryGroup B)) →*
      centralizer ({a.val} : Set (W ≃ₗ[K] W)) where
  toFun g := ⟨g.val.val, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 g.2))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [FiniteDimensional K W] in
theorem centralizerInclusion_injective (a : isometryGroup B) :
    Function.Injective (centralizerInclusion h B a) := fun _ _ hgg' =>
  Subtype.ext (Subtype.ext
    (congrArg (fun x : centralizer ({a.val} : Set (W ≃ₗ[K] W)) => (x : W ≃ₗ[K] W)) hgg'))

theorem unitary_two_twoLocal (hp : p ≠ 2) (hW : Module.finrank K W = 2)
    (B₂ : W →ₛₗ[h.bar] W →ₗ[K] K) (hB : ∀ x y, B x y = B₂ x y) (hsym : B.IsSymm)
    (hnd : B.Nondegenerate) (hsym₂ : B₂.IsSymm) :
    (∀ S : Subgroup (isometryGroup B), IsPGroup 2 S →
      Nat.card S = 2 ^ (Nat.card (isometryGroup B)).factorization 2 → IsCyclic (center S)) ∧
    ∀ Q : Subgroup (isometryGroup B), (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) →
      (∀ x ∈ Q, x * x = 1) → Nat.card Q ≤ 4 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have h2 : (2 : K) ≠ 0 := unitaryField_two_ne_zero p f hpodd (card_eq_sq h)
  have : Finite (isometryGroup B) := isometryGroup_finite B
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hW]; norm_num)
  have hl₂ : B₂.SeparatingLeft := fun x hx => hnd.1 x fun y => by rw [hB]; exact hx y
  have hneg : (-1 : Kˣ) ∈ normOneUnits (sigma := frob h) := by
    change frob h ((-1 : Kˣ) : K) * ((-1 : Kˣ) : K) = 1
    simp
  set c : isometryGroup B := scalarIsometry B ⟨-1, hneg⟩ with hc
  have hcval : c.val = LinearEquiv.neg K := LinearEquiv.ext fun v => by
    rw [hc, scalarIsometry_apply, LinearEquiv.neg_apply]
    simp
  have hcC : c ∈ center (isometryGroup B) := scalarIsometry_mem_center B _
  have hc2 : orderOf c = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hcval]
      exact LinearEquiv.ext fun v => by
        simp only [sq, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_neg, Subgroup.coe_one,
          LinearEquiv.coe_one, id_eq]
    · intro h1
      obtain ⟨v, hv⟩ := exists_ne (0 : W)
      have h' := congrArg (fun e : isometryGroup B => e.val v) h1
      simp only [hcval, LinearEquiv.neg_apply, Subgroup.coe_one, LinearEquiv.coe_one,
        id_eq] at h'
      apply hv
      have h2v : (2 : K) • v = 0 := by rw [two_smul]; nth_rewrite 1 [← h']; exact neg_add_cancel v
      exact (smul_eq_zero.1 h2v).resolve_left h2
  refine twoLocal_of_small_centralizers hcC hc2 fun a ha2 ha1 hac => ?_
  have ha₀2 : a.val * a.val = 1 := congrArg Subtype.val ha2
  have ha₀1 : a.val ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have ha₀n : a.val ≠ LinearEquiv.neg K := fun h' => hac (Subtype.ext (h'.trans hcval.symm))
  let ψ : centralizer ({a} : Set (isometryGroup B)) →* Kˣ × Kˣ :=
    (eigenScalarHom a.val).comp (centralizerInclusion h B a)
  have hψ : Function.Injective ψ :=
    (eigenScalarHom_injective h2 hW ha₀2 ha₀1 ha₀n).comp (centralizerInclusion_injective h B a)
  have hψN : ∀ g, ψ g ∈ (normOneUnits (sigma := frob h)).prod (normOneUnits (sigma := frob h)) :=
    fun g => mem_prod.2 (eigenScalar_mem_normOne h B h2 hW hsym hnd a.2 ha₀2 ha₀1 ha₀n g.val.2 _)
  have hdvd := card_dvd_of_injective (ψ.codRestrict _ hψN) fun x y hxy =>
    hψ (congrArg Subtype.val hxy)
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    normOneUnits_card p f (card_eq_sq h)] at hdvd
  refine ⟨?_, fun E hE hexp => ?_⟩
  ·
    set q := p ^ f with hq
    have hqodd : Odd q := hpodd.pow
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hqodd.pos; omega⟩
    have hr0 : r ≠ 0 := by
      have h3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
      have hf1 : 1 ≤ f := h.one_le
      have hpq : p ≤ q := Nat.le_self_pow (by omega) p
      omega
    have hU : Nat.card (isometryGroup B) = ((r + 2) * (r + 2)) * ((r + 1) * r) := by
      rw [card_isometryGroup_plane h B hW B₂ hB hsym₂ hl₂, ← hq, hr,
        Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = r * (r + 2) + 1 by ring)]
      ring
    rw [hr, show r + 1 + 1 = r + 2 by ring] at hdvd
    have hrr : (r + 2) * (r + 2) ≠ 0 := by positivity
    have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hrr).2 hdvd 2
    have heven : 2 ∣ r := by
      rw [hr] at hqodd
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k, by omega⟩
    have hone := (Nat.prime_two.dvd_iff_one_le_factorization hr0).1 heven
    have e1 : ((r + 2) * (r + 2) * ((r + 1) * r)).factorization 2 =
        ((r + 2) * (r + 2)).factorization 2 + ((r + 1).factorization 2 + r.factorization 2) := by
      rw [Nat.factorization_mul (a := (r + 2) * (r + 2)) hrr (Nat.mul_ne_zero (by omega) hr0),
        Finsupp.add_apply, Nat.factorization_mul (a := r + 1) (b := r) (by omega) hr0,
        Finsupp.add_apply]
    rw [hU, e1]
    omega
  ·
    have hle : E.map (isometryGroup B).subtype ≤ centralizer ({a.val} : Set (W ≃ₗ[K] W)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hE hx)))
    have hexp' : ∀ x ∈ E.map (isometryGroup B).subtype, x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hexp x hx)
    have := card_le_four_of_le_centralizer h2 hW ha₀2 ha₀1 ha₀n hle hexp'
    rwa [card_map_of_injective (isometryGroup B).subtype_injective] at this

end PlaneTwoLocal

section Block

omit [Fact p.Prime] [Finite K]

noncomputable abbrev act (g : unitarySU p f K 3) (v : Fin 3 → K) : Fin 3 → K :=
  Matrix.mulVec ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) v

theorem act_mul (g g' : unitarySU p f K 3) (v : Fin 3 → K) :
    act (g * g') v = act g (act g' v) := by
  simp only [act, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 3 → K) : act (1 : unitarySU p f K 3) v = v := by
  simp only [act, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

theorem act_inv_act (g : unitarySU p f K 3) (v : Fin 3 → K) : act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : unitarySU p f K 3) (v : Fin 3 → K) : act g (act g⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

variable (p f) in
@[expose] def unitaryPreservingFixing (P Q : Submodule K (Fin 3 → K)) :
    Subgroup (unitarySU p f K 3) where
  carrier := {g | (∀ v, act g v ∈ P ↔ v ∈ P) ∧ ∀ v ∈ Q, act g v = v}
  one_mem' := ⟨fun v => by rw [act_one], fun v _ => act_one v⟩
  mul_mem' := by
    rintro g g' ⟨hgP, hgQ⟩ ⟨hg'P, hg'Q⟩
    exact ⟨fun v => by rw [act_mul, hgP, hg'P],
      fun v hv => by rw [act_mul, hg'Q v hv, hgQ v hv]⟩
  inv_mem' := by
    rintro g ⟨hgP, hgQ⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [← hgP, act_act_inv]
    · calc act g⁻¹ v = act g⁻¹ (act g v) := by rw [hgQ v hv]
        _ = v := act_inv_act g v

end Block

omit [Fact p.Prime] in
theorem frob_two_ne_zero (h : UnitaryFieldData p f K) (hp : p ≠ 2) : (2 : K) ≠ 0 :=
  unitaryField_two_ne_zero p f (h.prime.odd_of_ne_two hp) (card_eq_sq h)

theorem frob_sq (h : UnitaryFieldData p f K) : frob h ^ 2 = 1 :=
  (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f (card_eq_sq h)).1

theorem frob_ne_one (h : UnitaryFieldData p f K) : frob h ≠ 1 :=
  (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f (card_eq_sq h)).2.1

omit [Fact p.Prime] [Finite K] in
@[expose] noncomputable def quotCentralizerIso {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (t : G) : centralizer ({e t} : Set H) ≃* centralizer ({t} : Set G) :=
  (centralizerTransport e.symm (e t)).trans
    (MulEquiv.subgroupCongr (by rw [MulEquiv.symm_apply_apply]))

omit [Fact p.Prime] [Finite K] in
theorem perfectResidual_map_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) : (perfectResidual G).map e.toMonoidHom = perfectResidual H := by
  have : Group.IsPerfect (perfectResidual G) := CFSG.perfect_residual_characterization.2.2.1
  have : Group.IsPerfect (perfectResidual H) := CFSG.perfect_residual_characterization.2.2.1
  apply le_antisymm
  · exact (CFSG.perfect_residual_transport (MonoidHom.id H)).2.2 _
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom.subgroupMap (perfectResidual G))
        (e.toMonoidHom.subgroupMap_surjective _))
  · have h1 : (perfectResidual H).map e.symm.toMonoidHom ≤ perfectResidual G :=
      (CFSG.perfect_residual_transport (MonoidHom.id G)).2.2 _
        (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom.subgroupMap (perfectResidual H))
          (e.symm.toMonoidHom.subgroupMap_surjective _))
    intro x hx
    exact ⟨e.symm x, h1 ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

omit [Fact p.Prime] [Finite K] in
theorem perfectResidual_centralizer_transport {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] (e : G ≃* H) (t : G) :
    (perfectResidual (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
      ((perfectResidual (centralizer ({e t} : Set H))).map
        (centralizer ({e t} : Set H)).subtype).map e.symm.toMonoidHom := by
  rw [← perfectResidual_map_mulEquiv (quotCentralizerIso e t), Subgroup.map_map,
    Subgroup.map_map]
  rfl

omit [Fact p.Prime] [Finite K] in
theorem perfectResidual_eq_map_ker {C H A : Type*} [Group C] [Group H] [CommGroup A]
    [Finite C] (φ : H →* C) (hφ : Function.Surjective φ) (δ : H →* A)
    [Group.IsPerfect δ.ker] : perfectResidual C = δ.ker.map φ := by
  have hJn : (δ.ker.map φ).Normal := (MonoidHom.normal_ker δ).map φ hφ
  have hJperf : Group.IsPerfect (δ.ker.map φ) :=
    Group.IsPerfect.ofSurjective (f := φ.subgroupMap δ.ker) (φ.subgroupMap_surjective δ.ker)
  have hquot : Group.IsSolvable (C ⧸ δ.ker.map φ) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨a, rfl⟩ := hφ x
        obtain ⟨c, rfl⟩ := hφ y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        refine ⟨(a * c)⁻¹ * (c * a), ?_, by rw [map_mul, map_inv, map_mul, map_mul]⟩
        change δ ((a * c)⁻¹ * (c * a)) = 1
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (δ c), inv_mul_cancel]
  exact le_antisymm ((CFSG.perfect_residual_characterization.2.2.2.2.1 _).1 hquot)
    ((CFSG.perfect_residual_transport (MonoidHom.id C)).2.2 _ hJperf)

omit [Fact p.Prime] [Finite K] in
theorem map_subtype_map_eq {G H : Type*} [Group G] [Group H] (D : Subgroup G) [D.Normal]
    {t : G ⧸ D} (φ : H →* centralizer ({t} : Set (G ⧸ D))) (β : H →* G)
    (hφβ : ∀ a, (φ a : G ⧸ D) = QuotientGroup.mk' D (β a)) (S : Subgroup H) :
    (S.map φ).map (centralizer ({t} : Set (G ⧸ D))).subtype =
      (S.map β).map (QuotientGroup.mk' D) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext hφβ

omit [Fact p.Prime] [Finite K] in
theorem sylow_twoLocal_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] (e : G ≃* H)
    (hS : ∀ T : Sylow 2 H, IsCyclic (center (T : Subgroup H)) ∧
      ∀ E : Subgroup H, E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 4)
    (T : Sylow 2 G) : IsCyclic (center (T : Subgroup G)) ∧
      ∀ E : Subgroup G, E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := hS (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨?_, fun E hET hc he => ?_⟩
  · have : IsCyclic (center ((T : Subgroup G).map e.toMonoidHom)) := h1
    let eT := (T : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
    exact isCyclic_of_surjective (centerCongr eT.symm) (centerCongr eT.symm).surjective
  · have := h2 (E.map e.toMonoidHom) (Subgroup.map_mono hET)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        change e x * e y = e y * e x
        rw [← map_mul e, ← map_mul e, hc x hx y hy])
      (by
        rintro _ ⟨x, hx, rfl⟩
        change e x * e x = 1
        rw [← map_mul e, he x hx, map_one e])
    rwa [card_map_of_injective e.injective] at this

section AbstractForm

variable {σ : K ≃+* K} {V : Type*} [AddCommGroup V] [Module K V]
  (B : V →ₛₗ[σ.toRingHom] V →ₗ[K] K)

omit [Fact p.Prime] [Finite K] in
theorem specialIsometry_mul_apply (g g' : specialIsometry B) (v : V) :
    (g * g').val.val v = g.val.val (g'.val.val v) :=
  rfl

omit [Fact p.Prime] [Finite K] in
theorem specialIsometry_one_apply (v : V) : (1 : specialIsometry B).val.val v = v :=
  rfl

omit [Fact p.Prime] [Finite K] in
theorem mem_minusSpace_iff (z : specialIsometry B) (v : V) :
    v ∈ minusSpace z.val.val.toLinearMap ↔ z.val.val v = -v := by
  change v ∈ Module.End.eigenspace _ (-1) ↔ _
  rw [Module.End.mem_eigenspace_iff, neg_one_smul]
  rfl

omit [Fact p.Prime] [Finite K] in
theorem mem_plusSpace_iff (z : specialIsometry B) (v : V) :
    v ∈ plusSpace z.val.val.toLinearMap ↔ z.val.val v = v := by
  change v ∈ Module.End.eigenspace _ 1 ↔ _
  rw [Module.End.mem_eigenspace_iff, one_smul]
  rfl

omit [Fact p.Prime] [Finite K] in
theorem apply_mem_minusSpace_iff {z g : specialIsometry B} (hg : g * z = z * g) (v : V) :
    g.val.val v ∈ minusSpace z.val.val.toLinearMap ↔ v ∈ minusSpace z.val.val.toLinearMap := by
  have key : ∀ g : specialIsometry B, g * z = z * g → ∀ v,
      v ∈ minusSpace z.val.val.toLinearMap → g.val.val v ∈ minusSpace z.val.val.toLinearMap := by
    intro g hg v hv
    rw [mem_minusSpace_iff] at hv ⊢
    have e := congrArg (fun x : specialIsometry B => x.val.val v) hg
    change g.val.val (z.val.val v) = z.val.val (g.val.val v) at e
    rw [← e, hv, map_neg g.val.val v]
  refine ⟨fun hv => ?_, key g hg v⟩
  have := key g⁻¹ (show Commute g z from hg).inv_left _ hv
  rwa [← specialIsometry_mul_apply, inv_mul_cancel g, specialIsometry_one_apply] at this

@[expose] def preservingFixingIso (P Q : Submodule K V) : Subgroup (specialIsometry B) where
  carrier := {g | (∀ v, g.val.val v ∈ P ↔ v ∈ P) ∧ ∀ v ∈ Q, g.val.val v = v}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g g' ⟨hgP, hgQ⟩ ⟨hg'P, hg'Q⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [specialIsometry_mul_apply, hgP, hg'P]
    · rw [specialIsometry_mul_apply, hg'Q v hv, hgQ v hv]
  inv_mem' := by
    rintro g ⟨hgP, hgQ⟩
    have e : ∀ v, g.val.val ((g⁻¹).val.val v) = v := fun v => by
      rw [← specialIsometry_mul_apply, mul_inv_cancel g, specialIsometry_one_apply]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [← hgP, e]
    · calc (g⁻¹).val.val v = (g⁻¹).val.val (g.val.val v) := by rw [hgQ v hv]
        _ = v := by
          rw [← specialIsometry_mul_apply, inv_mul_cancel g, specialIsometry_one_apply]

omit [Fact p.Prime] [Finite K] in
theorem comm_of_mem_preservingFixingIso (h2 : (2 : K) ≠ 0) {z g : specialIsometry B}
    (hz : orderOf z = 2)
    (hg : g ∈ preservingFixingIso B (minusSpace z.val.val.toLinearMap)
      (plusSpace z.val.val.toLinearMap)) : g * z = z * g := by
  obtain ⟨hgP, hgQ⟩ := hg
  have hc := involution_complement B h2 z hz
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
  change g.val.val (z.val.val v) = z.val.val (g.val.val v)
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hzx := (mem_minusSpace_iff B z x).1 hx
  have hzy := (mem_plusSpace_iff B z y).1 hy
  have hzgx := (mem_minusSpace_iff B z _).1 ((hgP x).2 hx)
  have lhs : g.val.val (z.val.val (x + y)) = -g.val.val x + y := by
    rw [map_add z.val.val, hzx, hzy, map_add g.val.val, map_neg g.val.val, hgQ y hy]
  have rhs : z.val.val (g.val.val (x + y)) = -g.val.val x + y := by
    rw [map_add g.val.val, hgQ y hy, map_add z.val.val, hzgx, hzy]
  rw [lhs, rhs]

omit [Fact p.Prime] [Finite K] in
theorem exists_plusSpace_ne_zero [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hdim : Module.finrank K V = 3) (z : specialIsometry B) (hz : orderOf z = 2) :
    ∃ y ∈ plusSpace z.val.val.toLinearMap, y ≠ 0 := by
  have hfr := (involution_finrank B h2 hdim z hz).2
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun hb => ?_
  rw [hb, finrank_bot] at hfr
  exact absurd hfr (by norm_num)

variable [FiniteDimensional K V]

@[expose] noncomputable def isoBlock (h2 : (2 : K) ≠ 0) (hsym : B.IsSymm)
    (hnd : B.Nondegenerate) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) (hdim : Module.finrank K V = 3)
    (z : specialIsometry B) (hz : orderOf z = 2) :
    isometryGroup (B.domRestrict₁₂ (minusSpace z.val.val.toLinearMap)
      (minusSpace z.val.val.toLinearMap)) →* specialIsometry B :=
  (centralizer ({z} : Set (specialIsometry B))).subtype.comp
    (unitaryCentralizerBlock B h2 hsym hnd hσ hne hdim z hz)

omit [Fact p.Prime] in
theorem map_isoBlock_specialIsometry (h2 : (2 : K) ≠ 0) (hsym : B.IsSymm)
    (hnd : B.Nondegenerate) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) (hdim : Module.finrank K V = 3)
    (z : specialIsometry B) (hz : orderOf z = 2) :
    (specialIsometry (B.domRestrict₁₂ (minusSpace z.val.val.toLinearMap)
        (minusSpace z.val.val.toLinearMap))).map (isoBlock B h2 hsym hnd hσ hne hdim z hz) =
      preservingFixingIso B (minusSpace z.val.val.toLinearMap)
        (plusSpace z.val.val.toLinearMap) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    have hdet : ((a.val.det⁻¹ : Kˣ) : K) = 1 := by
      have ha' : a.val.det = 1 := ha
      rw [ha', inv_one, Units.val_one]
    refine ⟨fun v => apply_mem_minusSpace_iff B (mem_centralizer_singleton_iff.1
      (unitaryCentralizerBlock B h2 hsym hnd hσ hne hdim z hz a).2) v, fun v hv => ?_⟩
    have := unitaryCentralizerBlock_plus B h2 hsym hnd hσ hne hdim z hz a ⟨v, hv⟩
    rw [hdet, one_smul] at this
    exact this
  · intro g hg
    have hgC : g ∈ centralizer ({z} : Set (specialIsometry B)) :=
      mem_centralizer_singleton_iff.2 (comm_of_mem_preservingFixingIso B h2 hz hg)
    have hblock := unitaryCentralizerBlock_restriction B h2 hsym hnd hσ hne hdim z hz ⟨g, hgC⟩
    refine ⟨unitaryCentralizerRestriction B z ⟨g, hgC⟩, ?_,
      congrArg Subtype.val hblock⟩
    obtain ⟨y₀, hy₀, hy₀0⟩ := exists_plusSpace_ne_zero B h2 hdim z hz
    have hplus := unitaryCentralizerBlock_plus B h2 hsym hnd hσ hne hdim z hz
      (unitaryCentralizerRestriction B z ⟨g, hgC⟩) ⟨y₀, hy₀⟩
    rw [hblock] at hplus
    change g.val.val y₀ = _ at hplus
    rw [hg.2 y₀ hy₀] at hplus
    have h1 : (((unitaryCentralizerRestriction B z ⟨g, hgC⟩).val.det⁻¹ : Kˣ) : K) = 1 := by
      have h' : (1 : K) • y₀ =
          (((unitaryCentralizerRestriction B z ⟨g, hgC⟩).val.det⁻¹ : Kˣ) : K) • y₀ := by
        rw [one_smul]
        exact hplus
      exact (smul_left_injective K hy₀0 h').symm
    change (unitaryCentralizerRestriction B z ⟨g, hgC⟩).val.det = 1
    have h1' : ((unitaryCentralizerRestriction B z ⟨g, hgC⟩).val.det⁻¹ : Kˣ) = 1 := Units.ext h1
    rwa [inv_eq_one] at h1'

end AbstractForm

section AbstractUnitary

variable (h : UnitaryFieldData p f K) {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem nonempty_specialIsometry_plane_equiv (B : V →ₛₗ[(frob h).toRingHom] V →ₗ[K] K)
    (B₂ : V →ₛₗ[h.bar] V →ₗ[K] K) (hB : ∀ x y, B x y = B₂ x y) (hsym₂ : B₂.IsSymm)
    (P : Submodule K V) (hP : Module.finrank K P = 2)
    (hnd : (B.domRestrict₁₂ P P).Nondegenerate) :
    Nonempty (specialIsometry (B.domRestrict₁₂ P P) ≃*
      Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  have hB' : ∀ x y, B.domRestrict₁₂ P P x y = B₂.domRestrict₁₂ P P x y := fun x y => hB x y
  have hl : (B₂.domRestrict₁₂ P P).SeparatingLeft := fun x hx =>
    hnd.1 x fun y => by rw [hB']; exact hx y
  obtain ⟨e⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 h
    (hsym₂.domRestrict P) hl hP
  exact ⟨((((isometryToSesq _ _ hB').subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_specialIsometry_isometryToSesq _ _ hB'))).trans
      (Subgroup.subgroupOfEquivOfLe fun _ hg => (mem_sesqSpecialUnitaryGroup.1 hg).1)).trans e⟩

theorem abstract_sylow_structure (hp : p ≠ 2) (B : V →ₛₗ[(frob h).toRingHom] V →ₗ[K] K)
    (hsym : B.IsSymm) (hnd : B.Nondegenerate) (hdim : Module.finrank K V = 3)
    (B₂ : V →ₛₗ[h.bar] V →ₗ[K] K) (hB : ∀ x y, B x y = B₂ x y) (hsym₂ : B₂.IsSymm)
    (D : Subgroup (specialIsometry B)) [D.Normal] (hD : D ≤ scalarCenter B hdim)
    (T : Sylow 2 (specialIsometry B ⧸ D)) :
    IsCyclic (center (T : Subgroup (specialIsometry B ⧸ D))) ∧
      ∀ E : Subgroup (specialIsometry B ⧸ D), E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
        (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := frob_two_ne_zero h hp
  have := isometryGroup_finite B
  by_cases hT1 : Nat.card (T : Subgroup (specialIsometry B ⧸ D)) = 1
  · have : Subsingleton (T : Subgroup (specialIsometry B ⧸ D)) :=
      (Nat.card_eq_one_iff_unique.1 hT1).1
    refine ⟨isCyclic_of_subsingleton, fun E hET _ _ => ?_⟩
    have := card_le_of_le hET
    omega
  have hnt : Nontrivial (T : Subgroup (specialIsometry B ⧸ D)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by have := Nat.card_pos (α := T); omega)
  have hZ2 : IsPGroup 2 (center (T : Subgroup (specialIsometry B ⧸ D))) :=
    T.isPGroup'.to_subgroup (center _)
  have hZnt := T.isPGroup'.center_nontrivial
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hk
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := center (T : Subgroup (specialIsometry B ⧸ D))) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have ht : orderOf ((x : T) : specialIsometry B ⧸ D) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hTt : (T : Subgroup (specialIsometry B ⧸ D)) ≤
      centralizer ({((x : T) : specialIsometry B ⧸ D)} : Set _) :=
    fun s hs => mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_center_iff.1 x.2 ⟨s, hs⟩))
  refine Exists.elim (unique_involution_lift B hdim D hD _ ht).exists fun z hz => ?_
  have hfr := involution_finrank B h2 hdim z hz.1
  obtain ⟨hPnd, -, -⟩ := involution_restrictions B h2 hsym hnd z hz.1
  have := isometryGroup_finite (B.domRestrict₁₂ (minusSpace z.val.val.toLinearMap)
    (minusSpace z.val.val.toLinearMap))
  obtain ⟨hH1, hH2⟩ := unitary_two_twoLocal h _ hp hfr.1 (B₂.domRestrict₁₂ _ _)
    (fun x y => hB x y) (hsym.domRestrict _) hPnd (hsym₂.domRestrict _)
  have hker := unitaryTargetQuotientCentralizer_ker B h2 hsym hnd (frob_sq h) (frob_ne_one h)
    hdim D z hz.1 _ hz.2
  refine sylow_transfer (unitaryTargetQuotientCentralizer B h2 hsym hnd (frob_sq h)
    (frob_ne_one h) hdim D z hz.1 _ hz.2) (unitaryTargetQuotientCentralizer_surjective B h2
      hsym hnd (frob_sq h) (frob_ne_one h) hdim D hD z hz.1 _ hz.2) ?_ ?_ hH1 hH2 T hTt
  · rw [hker]
    intro a ha
    refine Exists.elim ((unitaryQuotientCentralizer_mem_ker_iff h2 hsym hnd (frob_sq h)
      (frob_ne_one h) hD hz.1).1 ha) fun c hc => ?_
    rw [hc.2]
    exact scalarIsometry_mem_center _ _
  · rw [hker, unitaryQuotientCentralizer_ker_card B h2 hsym hnd (frob_sq h) (frob_ne_one h)
      hdim D hD z hz.1]
    exact scalar_kernel_odd B hdim D hD

theorem abstract_centralizer_structure (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (B : V →ₛₗ[(frob h).toRingHom] V →ₗ[K] K) (hsym : B.IsSymm) (hnd : B.Nondegenerate)
    (hdim : Module.finrank K V = 3) (B₂ : V →ₛₗ[h.bar] V →ₗ[K] K) (hB : ∀ x y, B x y = B₂ x y)
    (hsym₂ : B₂.IsSymm) (D : Subgroup (specialIsometry B)) [D.Normal]
    (hD : D ≤ scalarCenter B hdim) (t : specialIsometry B ⧸ D) (z : specialIsometry B)
    (hz : orderOf z = 2) (hzt : QuotientGroup.mk' D z = t) :
    (perfectResidual (centralizer ({t} : Set (specialIsometry B ⧸ D)))).map
        (centralizer ({t} : Set (specialIsometry B ⧸ D))).subtype =
      (preservingFixingIso B (minusSpace z.val.val.toLinearMap)
        (plusSpace z.val.val.toLinearMap)).map (QuotientGroup.mk' D) ∧
    Nonempty (↥((preservingFixingIso B (minusSpace z.val.val.toLinearMap)
        (plusSpace z.val.val.toLinearMap)).map (QuotientGroup.mk' D)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  have h2 := frob_two_ne_zero h hp
  have := isometryGroup_finite B
  have hfr := involution_finrank B h2 hdim z hz
  obtain ⟨hPnd, -, -⟩ := involution_restrictions B h2 hsym hnd z hz
  obtain ⟨eS⟩ := nonempty_specialIsometry_plane_equiv h B B₂ hB hsym₂ _ hfr.1 hPnd
  have h4 : ∃ s : Finset h.fixedField, s.card = 4 := by
    have := Fintype.ofFinite h.fixedField
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset h.fixedField)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card_fixedField]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
    special_linear_dimension_two_perfect h4
  have : Group.IsPerfect (specialIsometry (B.domRestrict₁₂ (minusSpace z.val.val.toLinearMap)
      (minusSpace z.val.val.toLinearMap))) :=
    Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
  have hDinf := perfectResidual_eq_map_ker (unitaryTargetQuotientCentralizer B h2 hsym hnd
    (frob_sq h) (frob_ne_one h) hdim D z hz t hzt) (unitaryTargetQuotientCentralizer_surjective
      B h2 hsym hnd (frob_sq h) (frob_ne_one h) hdim D hD z hz t hzt) (isometryDeterminant _)
  have hL := map_subtype_map_eq D (unitaryTargetQuotientCentralizer B h2 hsym hnd (frob_sq h)
    (frob_ne_one h) hdim D z hz t hzt) (isoBlock B h2 hsym hnd (frob_sq h) (frob_ne_one h) hdim
      z hz) (unitaryTargetQuotientCentralizer_coe B h2 hsym hnd (frob_sq h) (frob_ne_one h) hdim
        D z hz t hzt) (specialIsometry _)
  rw [map_isoBlock_specialIsometry] at hL
  have hinj : Function.Injective ((unitaryTargetQuotientCentralizer B h2 hsym hnd (frob_sq h)
      (frob_ne_one h) hdim D z hz t hzt).comp (specialIsometry (B.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, ha⟩ h1
    have hk : a ∈ (unitaryQuotientCentralizer B h2 hsym hnd (frob_sq h) (frob_ne_one h) hdim D z
        hz).ker := by
      rw [← unitaryTargetQuotientCentralizer_ker B h2 hsym hnd (frob_sq h) (frob_ne_one h) hdim
        D z hz t hzt]
      exact h1
    obtain ⟨c, -, rfl⟩ := (unitaryQuotientCentralizer_mem_ker_iff h2 hsym hnd (frob_sq h)
      (frob_ne_one h) hD hz).1 hk
    have hc2 : c.val.val ^ 2 = 1 := by
      have hdet : LinearEquiv.det (scalarAction (V := minusSpace z.val.val.toLinearMap)
          c.val.val) = 1 := ha
      rwa [scalarAction_determinant, hfr.1] at hdet
    have hc3 : c.val.val ^ 3 = 1 := congrArg Subtype.val (c.2 : c.val ^ 3 = 1)
    have hc1 : c.val.val = 1 := by
      calc c.val.val = c.val.val ^ 3 * (c.val.val ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, hc2, inv_one, one_mul]
    refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
    change ((c.val.val : Kˣ) : K) • x = x
    rw [hc1, Units.val_one, one_smul]
  have hJr : ((unitaryTargetQuotientCentralizer B h2 hsym hnd (frob_sq h) (frob_ne_one h) hdim D
      z hz t hzt).comp (specialIsometry (B.domRestrict₁₂ (minusSpace z.val.val.toLinearMap)
        (minusSpace z.val.val.toLinearMap))).subtype).range =
      (specialIsometry _).map (unitaryTargetQuotientCentralizer B h2 hsym hnd (frob_sq h)
        (frob_ne_one h) hdim D z hz t hzt) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨by rw [hDinf, hL], ⟨(MulEquiv.subgroupCongr hL.symm).trans
    ((equivMapOfInjective _ _ (centralizer ({t} : Set (specialIsometry B ⧸ D))).subtype_injective
      ).symm.trans (((MulEquiv.subgroupCongr hJr).symm.trans
        (MonoidHom.ofInjective hinj).symm).trans eS))⟩⟩

end AbstractUnitary

@[expose] noncomputable def imageD (h : UnitaryFieldData p f K)
    (D : Subgroup (unitarySU p f K 3)) : Subgroup (specialIsometry (frobForm h 3)) :=
  D.map ((unitaryEquiv h) : unitarySU p f K 3 →* specialIsometry (frobForm h 3))

instance imageD_normal (h : UnitaryFieldData p f K) (D : Subgroup (unitarySU p f K 3))
    [D.Normal] : (imageD h D).Normal :=
  Subgroup.Normal.map inferInstance _ (unitaryEquiv h).surjective

theorem imageD_le (h : UnitaryFieldData p f K) {D : Subgroup (unitarySU p f K 3)}
    (hD : D ≤ unitaryScalars h 3) : imageD h D ≤ scalarCenter (frobForm h 3) finrank_three :=
  map_le_scalarCenter h hD

@[expose] noncomputable def quotEquiv (h : UnitaryFieldData p f K)
    (D : Subgroup (unitarySU p f K 3)) [D.Normal] :
    (unitarySU p f K 3 ⧸ D) ≃* (specialIsometry (frobForm h 3) ⧸ imageD h D) :=
  QuotientGroup.congr D (imageD h D) (unitaryEquiv h) rfl

theorem quotEquiv_mk (h : UnitaryFieldData p f K) (D : Subgroup (unitarySU p f K 3)) [D.Normal]
    (x : unitarySU p f K 3) :
    quotEquiv h D (QuotientGroup.mk' D x) = QuotientGroup.mk' (imageD h D) (unitaryEquiv h x) :=
  QuotientGroup.congr_mk' D (imageD h D) (unitaryEquiv h) rfl x

theorem involution_lift (h : UnitaryFieldData p f K) (D : Subgroup (unitarySU p f K 3))
    [D.Normal] (hD : D ≤ unitaryScalars h 3) (t : unitarySU p f K 3 ⧸ D) (ht : orderOf t = 2) :
    ∃ z : unitarySU p f K 3, (orderOf z = 2 ∧ QuotientGroup.mk' D z = t) ∧
      ∀ w : unitarySU p f K 3, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z := by
  have ht' : orderOf (quotEquiv h D t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  have hu := unique_involution_lift (frobForm h 3) finrank_three (imageD h D)
    (imageD_le h hD) _ ht'
  refine Exists.elim hu.exists fun z' hz' => ?_
  refine Exists.elim ((unitaryEquiv h).surjective z') fun z hzz =>
    ⟨z, ⟨?_, ?_⟩, fun w hw hwt => ?_⟩
  · rw [← MulEquiv.orderOf_eq (unitaryEquiv h), hzz]
    exact hz'.1
  · apply (quotEquiv h D).injective
    rw [quotEquiv_mk, hzz]
    exact hz'.2
  · apply (unitaryEquiv h).injective
    rw [hzz]
    exact hu.unique ⟨by rw [MulEquiv.orderOf_eq, hw], by rw [← quotEquiv_mk, hwt]⟩ hz'

theorem unitaryPreservingFixing_eq_map (h : UnitaryFieldData p f K)
    (P Q : Submodule K (Fin 3 → K)) :
    unitaryPreservingFixing p f P Q =
      (preservingFixingIso (frobForm h 3) P Q).map (unitaryEquiv h).symm.toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  rfl

theorem map_mk_unitaryPreservingFixing (h : UnitaryFieldData p f K)
    (D : Subgroup (unitarySU p f K 3)) [D.Normal] (P Q : Submodule K (Fin 3 → K)) :
    (unitaryPreservingFixing p f P Q).map (QuotientGroup.mk' D) =
      ((preservingFixingIso (frobForm h 3) P Q).map (QuotientGroup.mk' (imageD h D))).map
        (quotEquiv h D).symm.toMonoidHom := by
  rw [unitaryPreservingFixing_eq_map h, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_unitaryPreservingFixing_self (h : UnitaryFieldData p f K) (z : unitarySU p f K 3) :
    z ∈ unitaryPreservingFixing p f (minusSpace (unitaryEquiv h z).val.val.toLinearMap)
      (plusSpace (unitaryEquiv h z).val.val.toLinearMap) := by
  rw [unitaryPreservingFixing_eq_map h, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  exact ⟨fun v => apply_mem_minusSpace_iff _ rfl v,
    fun v hv => (mem_plusSpace_iff _ (unitaryEquiv h z) v).1 hv⟩

theorem mk_comp_unitaryPreservingFixing_injective (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {D : Subgroup (unitarySU p f K 3)} [D.Normal] (hD : D ≤ unitaryScalars h 3)
    (z : unitarySU p f K 3) (hz : orderOf (unitaryEquiv h z) = 2) :
    Function.Injective ((QuotientGroup.mk' D).comp
      (unitaryPreservingFixing p f (minusSpace (unitaryEquiv h z).val.val.toLinearMap)
        (plusSpace (unitaryEquiv h z).val.val.toLinearMap)).subtype) := by
  obtain ⟨y₀, hy₀, hy₀0⟩ :=
    exists_plusSpace_ne_zero (frobForm h 3) (frob_two_ne_zero h hp) finrank_three _ hz
  rw [injective_iff_map_eq_one]
  rintro ⟨g, hg⟩ h1
  have hgD : g ∈ D := (QuotientGroup.eq_one_iff g).1 h1
  obtain ⟨c, -, -, hcg⟩ := mem_unitaryScalars.1 (hD hgD)
  have hgy : act g y₀ = (c : K) • y₀ := by
    change Matrix.mulVec ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) y₀ = _
    rw [hcg, Matrix.GeneralLinearGroup.coe_scalar]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hc1 : c = 1 := by
    have h' : (c : K) • y₀ = (1 : K) • y₀ := by rw [one_smul, ← hgy]; exact hg.2 y₀ hy₀
    exact Units.ext (smul_left_injective K hy₀0 h')
  subst hc1
  refine Subtype.ext (Subtype.ext ?_)
  rw [hcg, map_one]
  rfl

theorem stdHermForm_nondegenerate_of (h : UnitaryFieldData p f K) {P : Submodule K (Fin 3 → K)}
    (hP : ((frobForm h 3).domRestrict₁₂ P P).Nondegenerate) :
    ((stdHermForm h 3).domRestrict₁₂ P P).Nondegenerate :=
  ⟨fun x hx => hP.1 x fun y => (frobForm_apply h 3 x y).trans (hx y),
    fun y hy => hP.2 y fun x => (frobForm_apply h 3 x y).trans (hy x)⟩

end QTEOddUnitaryThree

open QTEOddUnitaryThree

variable {p f : ℕ} {K : Type} [Field K]

theorem odd_unitary_three_involution_and_Sylow_structure (h : UnitaryFieldData p f K)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (D : Subgroup (unitarySU p f K 3)) [D.Normal]
    (hD : D ≤ unitaryScalars h 3) :
    (∀ T : Sylow 2 (unitarySU p f K 3 ⧸ D),
      IsCyclic (center (T : Subgroup (unitarySU p f K 3 ⧸ D))) ∧
      ∀ E : Subgroup (unitarySU p f K 3 ⧸ D), E ≤ T → IsElementaryAbelian 2 E →
        Nat.card E ≤ 4) ∧
    ∀ t : unitarySU p f K 3 ⧸ D, orderOf t = 2 →
      ∃ z : unitarySU p f K 3, (orderOf z = 2 ∧ QuotientGroup.mk' D z = t) ∧
        (∀ w : unitarySU p f K 3, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
        Module.finrank K
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) = 2 ∧
        Module.finrank K
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) = 1 ∧
        ((stdHermForm h 3).domRestrict₁₂
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
          ).Nondegenerate ∧
        ((stdHermForm h 3).domRestrict₁₂
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
          ).Nondegenerate ∧
        (∀ x ∈ minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
          ∀ y ∈ plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
            stdHermForm h 3 x y = 0) ∧
        (perfectResidual (centralizer ({t} : Set (unitarySU p f K 3 ⧸ D)))).map
            (centralizer ({t} : Set (unitarySU p f K 3 ⧸ D))).subtype =
          (unitaryPreservingFixing p f
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))).map
              (QuotientGroup.mk' D) ∧
        Function.Injective ((QuotientGroup.mk' D).comp
          (unitaryPreservingFixing p f
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))).subtype) ∧
        Nonempty (↥((unitaryPreservingFixing p f
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))).map
              (QuotientGroup.mk' D)) ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField) ∧
        t ∈ (unitaryPreservingFixing p f
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))).map
              (QuotientGroup.mk' D) ∧
        ∀ l ∈ (unitaryPreservingFixing p f
            (minusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
            (plusSpace (Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))).map
              (QuotientGroup.mk' D), l * t = t * l := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have := isometryGroup_finite (frobForm h 3)
  have hS := sylow_twoLocal_of_mulEquiv (quotEquiv h D) (abstract_sylow_structure h hp
    (frobForm h 3) (frobForm_isSymm h 3) (frobForm_nondegenerate h 3) finrank_three
    (stdHermForm h 3) (frobForm_apply h 3) (stdHermForm_isSymm h 3) (imageD h D)
    (imageD_le h hD))
  have hSyl : ∀ T : Sylow 2 (unitarySU p f K 3 ⧸ D),
      IsCyclic (center (T : Subgroup (unitarySU p f K 3 ⧸ D))) ∧
      ∀ E : Subgroup (unitarySU p f K 3 ⧸ D), E ≤ T → IsElementaryAbelian 2 E →
        Nat.card E ≤ 4 := by
    refine fun T => ⟨(hS T).1, fun E hET hE => (hS T).2 E hET (fun a ha b hb => ?_)
      fun a ha => ?_⟩
    · exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  refine ⟨hSyl, fun t ht => ?_⟩
  obtain ⟨z, ⟨hz, hzt⟩, huniq⟩ := involution_lift h D hD t ht
  have hz' : orderOf (unitaryEquiv h z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
  have hzt' : QuotientGroup.mk' (imageD h D) (unitaryEquiv h z) = quotEquiv h D t := by
    rw [← quotEquiv_mk, hzt]
  have h2 := frob_two_ne_zero h hp
  have hfr := involution_finrank (frobForm h 3) h2 finrank_three _ hz'
  obtain ⟨hPnd, hQnd, horth⟩ := involution_restrictions (frobForm h 3) h2
    (frobForm_isSymm h 3) (frobForm_nondegenerate h 3) _ hz'
  obtain ⟨hL', ⟨eL⟩⟩ := abstract_centralizer_structure h hp hq (frobForm h 3)
    (frobForm_isSymm h 3) (frobForm_nondegenerate h 3) finrank_three (stdHermForm h 3)
    (frobForm_apply h 3) (stdHermForm_isSymm h 3) (imageD h D) (imageD_le h hD) _ _ hz' hzt'
  have hL : (perfectResidual (centralizer ({t} : Set (unitarySU p f K 3 ⧸ D)))).map
      (centralizer ({t} : Set (unitarySU p f K 3 ⧸ D))).subtype =
      (unitaryPreservingFixing p f (minusSpace (unitaryEquiv h z).val.val.toLinearMap)
        (plusSpace (unitaryEquiv h z).val.val.toLinearMap)).map (QuotientGroup.mk' D) := by
    rw [perfectResidual_centralizer_transport (quotEquiv h D) t, hL',
      map_mk_unitaryPreservingFixing h D]
  have hiso : Nonempty (↥((unitaryPreservingFixing p f
      (minusSpace (unitaryEquiv h z).val.val.toLinearMap)
      (plusSpace (unitaryEquiv h z).val.val.toLinearMap)).map (QuotientGroup.mk' D)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    rw [map_mk_unitaryPreservingFixing h D]
    exact ⟨(equivMapOfInjective _ _ (quotEquiv h D).symm.injective).symm.trans eL⟩
  have hinj := mk_comp_unitaryPreservingFixing_injective h hp hD z hz'
  have hzmem := mem_unitaryPreservingFixing_self h z
  have hM : (unitaryEquiv h z).val.val.toLinearMap =
      Matrix.toLin' ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl
  rw [hM] at hfr hPnd hQnd horth hL hiso hinj hzmem
  refine ⟨z, ⟨hz, hzt⟩, huniq, hfr.1, hfr.2, stdHermForm_nondegenerate_of h hPnd,
    stdHermForm_nondegenerate_of h hQnd,
    fun x hx y hy => (frobForm_apply h 3 x y).symm.trans (horth x hx y hy), hL, hinj, hiso,
    ⟨z, hzmem, hzt⟩, fun l hl => ?_⟩
  rw [← hL] at hl
  exact mem_centralizer_singleton_iff.1 (map_subtype_le _ hl)

end CFSG.Quasithin.SteinbergBS
