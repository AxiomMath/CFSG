module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddChar
import CFSG.RankThree.Classical.SteinbergBJCentralCoprimeLift
import CFSG.Open.PGLModelStated
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Module Matrix CFSG.RankThree.Classical
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Open (StatedProj StatedSU StatedScalars)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Rep

variable {n : ℕ} {K L : Type*} [Field K] [Field L]

@[expose] noncomputable def matRep (f : K →+* L) {G : Subgroup (GL (Fin n) K)}
    {Ã : Subgroup ↥G} {B : Type*} [Group B] (e : Ã ≃* B) : B →* Module.End L (Fin n → L) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) L ≃ₐ[L] _).toRingEquiv.toMonoidHom.comp
    (f.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp
      (G.subtype.comp (Ã.subtype.comp e.symm.toMonoidHom))))

theorem matRep_apply (f : K →+* L) {G : Subgroup (GL (Fin n) K)} {Ã : Subgroup ↥G}
    {B : Type*} [Group B] (e : Ã ≃* B) (b : B) (v : Fin n → L) :
    matRep f e b v =
      ((((e.symm b : Ã) : ↥G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map f *ᵥ v :=
  rfl

theorem matRep_injective (f : K →+* L) {G : Subgroup (GL (Fin n) K)} {Ã : Subgroup ↥G}
    {B : Type*} [Group B] (e : Ã ≃* B) {b : B} (hb : matRep f e b = 1) : b = 1 := by
  have h1 : ((((e.symm b : Ã) : ↥G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map f = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hb v
    rw [matRep_apply, Module.End.one_apply] at this
    rw [Matrix.toLin'_apply, LinearMap.id_apply, this]
  have h2 : ((((e.symm b : Ã) : ↥G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Matrix.map_injective f.injective (h1.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  have h3 : e.symm b = 1 := Subtype.ext (Subtype.ext (Units.ext h2))
  rw [← e.apply_symm_apply b, h3, map_one]

end Rep

theorem unitary_det_of_mem_statedSU {K : Type} [Field K] (fb : K →+* K) {n q : ℕ}
    (hfbq : ∀ x : K, fb x = x ^ q) {A : GL (Fin n) K} (hA : A ∈ StatedSU n q K) :
    (((A : Matrix (Fin n) (Fin n) K).map fb)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1) ∧
      (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  have e : (fun x : K => x ^ q) = ⇑fb := funext fun x => (hfbq x).symm
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, h2⟩ := hx
    rw [e] at h2
    exact ⟨h2, h1⟩
  | one => simp
  | mul x y _ _ hx hy =>
    refine ⟨?_, by simp [Matrix.det_mul, hx.2, hy.2]⟩
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((y : Matrix (Fin n) (Fin n) K).map fb)ᵀ * ((x : Matrix (Fin n) (Fin n) K).map fb)ᵀ *
        (↑x * ↑y) = ((y : Matrix (Fin n) (Fin n) K).map fb)ᵀ *
          (((x : Matrix (Fin n) (Fin n) K).map fb)ᵀ * ↑x) * ↑y := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hx.1, Matrix.mul_one, hy.1]
  | inv x _ hx =>
    refine ⟨?_, by simp [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hx.2]⟩
    set B : Matrix (Fin n) (Fin n) K := ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hB
    have h1 : (↑x : Matrix (Fin n) (Fin n) K) * B = 1 := Units.mul_inv x
    calc (B.map fb)ᵀ * B = (B.map fb)ᵀ * (((x : Matrix (Fin n) (Fin n) K).map fb)ᵀ * ↑x) * B := by
          rw [hx.1, Matrix.mul_one]
      _ = (((x : Matrix (Fin n) (Fin n) K) * B).map fb)ᵀ * (↑x * B) := by
          simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp

theorem five_le_sum_of_orderOf_eq_four {p : ℕ} [hp : Fact p.Prime] {D : Type*} [AddCommGroup D]
    [Module (ZMod p) D] [Fintype D] (hD : Nat.card D = p ^ 2) {u : ZMod p} (hu : orderOf u = 4)
    (m : D → ℕ) (hm : ∀ χ, m χ ≤ m (u • χ))
    (hS : AddSubgroup.closure {χ | χ ≠ 0 ∧ m χ ≠ 0} = ⊤) : 5 ≤ ∑ χ, m χ := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set S : Set D := {χ | χ ≠ 0 ∧ m χ ≠ 0} with hSdef
  have hline : ∀ χ : D, AddSubgroup.zmultiples χ ≠ ⊤ := by
    intro χ htop
    have h1 : Nat.card (AddSubgroup.zmultiples χ) ≤ p := by
      rw [Nat.card_zmultiples]
      apply Nat.le_of_dvd hp.out.pos
      apply addOrderOf_dvd_of_nsmul_eq_zero
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
    rw [htop, AddSubgroup.card_top, hD] at h1
    have h2 := hp.out.two_le
    have : p < p ^ 2 := by nlinarith
    omega
  obtain ⟨χ₁, hχ₁⟩ : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, AddSubgroup.closure_empty] at hS
    exact hline 0 (by rw [AddSubgroup.zmultiples_zero_eq_bot, hS])
  obtain ⟨χ₂, hχ₂S, hχ₂⟩ : ∃ χ₂ ∈ S, χ₂ ∉ AddSubgroup.zmultiples χ₁ := by
    by_contra hcon
    push Not at hcon
    apply hline χ₁
    rw [eq_top_iff, ← hS, AddSubgroup.closure_le]
    exact hcon
  have hpow : ∀ k : ℕ, 1 ≤ m (u ^ k • χ₁) := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul]; exact Nat.one_le_iff_ne_zero.mpr hχ₁.2
    | succ k ih => rw [pow_succ', mul_smul]; exact ih.trans (hm _)
  have hinj : Set.InjOn (fun k : ℕ => u ^ k • χ₁) (Finset.range 4 : Set ℕ) := by
    intro i hi j hj hij
    have h0 : (u ^ i - u ^ j) • χ₁ = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr hij
    have h1 : u ^ i = u ^ j := sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hχ₁.1)
    have hi' : i < orderOf u := by rw [hu]; exact Finset.mem_range.mp hi
    have hj' : j < orderOf u := by rw [hu]; exact Finset.mem_range.mp hj
    exact pow_injOn_Iio_orderOf hi' hj' h1
  have hmem : ∀ k : ℕ, u ^ k • χ₁ ∈ AddSubgroup.zmultiples χ₁ := by
    intro k
    rw [← ZMod.natCast_zmod_val (u ^ k), Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem_zmultiples _ _
  set T : Finset D := insert χ₂ ((Finset.range 4).image fun k : ℕ => u ^ k • χ₁) with hT
  have hTcard : T.card = 5 := by
    rw [hT, Finset.card_insert_of_notMem, Finset.card_image_of_injOn hinj, Finset.card_range]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro k _ hk
    exact hχ₂ (hk ▸ hmem k)
  calc 5 = ∑ χ ∈ T, 1 := by rw [Finset.sum_const, hTcard, smul_eq_mul, mul_one]
    _ ≤ ∑ χ ∈ T, m χ := by
        refine Finset.sum_le_sum fun χ hχ => ?_
        rw [hT, Finset.mem_insert, Finset.mem_image] at hχ
        rcases hχ with rfl | ⟨k, -, rfl⟩
        · exact Nat.one_le_iff_ne_zero.mpr hχ₂S.2
        · exact hpow k
    _ ≤ ∑ χ, m χ := Finset.sum_le_sum_of_subset (Finset.subset_univ T)

theorem false_of_unitary_lift {r p : ℕ} [Fact r.Prime] [hpf : Fact p.Prime] (hp7 : 7 ≤ p)
    (hpr : p ∣ r ^ 2 + 1) {K : Type*} [Field K] [CharP K r] {G : Subgroup (GL (Fin 4) K)}
    (hU : ∀ g ∈ G, ((g : Matrix (Fin 4) (Fin 4) K).map (frobenius K r))ᵀ *
      (g : Matrix (Fin 4) (Fin 4) K) = 1)
    {Ã : Subgroup ↥G} {Γ : Type*} [CommGroup Γ] [Fintype Γ] (e : Ã ≃* Γ)
    (hexp : ∀ g : Γ, g ^ p = 1) (hcard : Fintype.card Γ = p ^ 2) : False := by
  have hrp : r.Prime := Fact.out
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hpr' : p ≠ r := by
    rintro rfl
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p two_ne_zero)).mp hpr
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (Additive Γ →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Fintype (Additive Γ →+ ZMod p) := Fintype.ofFinite _
  have hDcard : Nat.card (Additive Γ →+ ZMod p) = p ^ 2 := by
    rw [natCard_char hp hexp, Nat.card_eq_fintype_card, hcard]
  set L := AlgebraicClosure K with hL
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K r] at h
    exact hpr' ((Nat.prime_dvd_prime_iff_eq hrp hp).mp h).symm
  haveI : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero _).mpr hpK
  have hΓL : (Fintype.card Γ : L) ≠ 0 := by
    rw [hcard, Nat.cast_pow]
    exact pow_ne_zero 2 hpL
  haveI : CharP L r := charP_of_injective_algebraMap (algebraMap K L).injective r
  let σ : L ≃+* L := iterateFrobeniusEquiv L r 1
  have hσ : ∀ x : L, σ x = x ^ r := fun x => by
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def, pow_one]
  set Mk : Γ → Matrix (Fin 4) (Fin 4) K := fun a =>
    ((((e.symm a : Ã) : ↥G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMk
  set f : K →+* L := algebraMap K L with hf
  set ρ := matRep f e with hρ
  set ρ' := matRep (σ.toRingHom.comp f) e with hρ'
  have hρa : ∀ (a : Γ) (v : Fin 4 → L), ρ a v = (Mk a).map f *ᵥ v := fun a v => rfl
  have hρ'a : ∀ (a : Γ) (v : Fin 4 → L), ρ' a v = (Mk a).map (σ.toRingHom.comp f) *ᵥ v :=
    fun a v => rfl
  let Φ : (Fin 4 → L) ≃+ (Fin 4 → L) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hΦ : ∀ (c : L) (v : Fin 4 → L), Φ (c • v) = σ c • Φ v := fun c v => by
    funext i
    simp [Φ, map_mul]
  have hρΦ : ∀ (a : Γ) (v : Fin 4 → L), Φ (ρ a v) = ρ' a (Φ v) := by
    intro a v
    funext i
    have hmap : ((Mk a).map f).map σ.toRingHom = (Mk a).map (σ.toRingHom.comp f) := by
      rw [Matrix.map_map]
      rfl
    rw [hρa, hρ'a]
    change σ.toRingHom (((Mk a).map f *ᵥ v) i) =
      ((Mk a).map (σ.toRingHom.comp f) *ᵥ fun j => σ.toRingHom (v j)) i
    rw [RingHom.map_mulVec σ.toRingHom, hmap]
    rfl
  set B : LinearMap.BilinForm L (Fin 4 → L) := Matrix.toBilin' (1 : Matrix (Fin 4) (Fin 4) L)
    with hB
  have hunit : ∀ a : Γ, ((Mk a).map (σ.toRingHom.comp f))ᵀ * (Mk a).map f = 1 := by
    intro a
    have hUa := hU _ ((e.symm a : Ã) : ↥G).2
    have hmapσ : (Mk a).map (σ.toRingHom.comp f) = ((Mk a).map (frobenius K r)).map f := by
      rw [Matrix.map_map]
      congr 1
      funext x
      simp only [Function.comp_apply, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, hσ, frobenius_def, map_pow]
    rw [hmapσ, ← Matrix.transpose_map, ← Matrix.map_mul, hUa,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hBinv : ∀ (a : Γ) (u w : Fin 4 → L), B (ρ' a u) (ρ a w) = B u w := by
    intro a u w
    rw [hρa, hρ'a, hB, Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.one_mulVec,
      Matrix.one_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hunit a, Matrix.one_mulVec]
  have hBnd : ∀ u : Fin 4 → L, (∀ w, B u w = 0) → u = 0 := by
    intro u hu
    funext i
    have := hu (Pi.single i 1)
    rw [hB, Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct_single, mul_one] at this
    exact this
  set m : (Additive Γ →+ ZMod p) → ℕ := fun χ => finrank L (charSpace ρ ζ χ) with hm
  have hsum : ∑ χ, m χ = 4 := by
    simp only [hm]
    rw [sum_finrank_charSpace hp hζ hexp hΓL, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hstep : ∀ χ, m χ ≤ m ((-(r : ZMod p)) • χ) := by
    intro χ
    have h1 := finrank_charSpace_nsmul₂ (ρ := ρ) (ρ' := ρ') hζ.pow_eq_one σ Φ hΦ hρΦ r (hσ ζ) χ
    have h2 := finrank_charSpace_le_neg₂ (ρ := ρ) (ρ' := ρ') hp hζ hexp hΓL B hBinv hBnd (r • χ)
    have h3 : -(r • χ) = (-(r : ZMod p)) • χ := by rw [neg_smul, Nat.cast_smul_eq_nsmul]
    simp only [hm]
    rw [← h3]
    omega
  have hcl := closure_support_charSpace_eq_top (ρ := ρ) hp hζ hexp hΓL
    (fun a ha => matRep_injective f e ha)
  have hS : AddSubgroup.closure {χ : Additive Γ →+ ZMod p | χ ≠ 0 ∧ m χ ≠ 0} = ⊤ := by
    have hset : {χ : Additive Γ →+ ZMod p | χ ≠ 0 ∧ m χ ≠ 0} =
        {χ | χ ≠ 0 ∧ charSpace ρ ζ χ ≠ ⊥} := by
      ext χ
      simp only [hm, Set.mem_setOf_eq, ne_eq, Submodule.finrank_eq_zero]
    rw [hset]
    exact hcl
  have hr2 : (r : ZMod p) ^ 2 = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (r ^ 2 + 1) p).mpr hpr
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hu : orderOf (-(r : ZMod p)) = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ¬ (-(r : ZMod p)) ^ 2 ^ 1 = 1 := by
      rw [pow_one, neg_sq, hr2]
      haveI : Fact (2 < p) := ⟨by omega⟩
      exact ZMod.neg_one_ne_one
    have h2 : (-(r : ZMod p)) ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, neg_sq, hr2]
      norm_num
    rw [orderOf_eq_prime_pow h1 h2]
    norm_num
  have h5 := five_le_sum_of_orderOf_eq_four hDcard hu m hstep hS
  omega

theorem false_of_elemAbelian_psu4 {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : 3 < r)
    (hp7 : 7 ≤ p) (hpr : p ∣ r ^ 2 + 1) (A : Subgroup (projSU 4 r 1))
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set K := GaloisField r (2 * 1) with hKdef
  have hfrob : ∀ x : K, frobenius K r x = x ^ (r ^ 1) := fun x => by
    rw [pow_one, frobenius_def]
  set G : Subgroup (GL (Fin 4) K) := StatedSU 4 (r ^ 1) K with hG
  set ψ := CFSG.PGLModel.projSUEquivStatedProj 4 r 1 with hψ
  set A₁ : Subgroup (StatedProj G) := A.map ψ.toMonoidHom with hA₁
  have hA₁e : CFSG.Open.IsElemAbelian p A₁ := hA.map _
  have hA₁c : Nat.card A₁ = p ^ 2 := by
    rw [hA₁, Subgroup.card_map_of_injective ψ.injective, hAc]
  set π : ↥G →* StatedProj G := QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf G)
    with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = (StatedScalars (Fin 4) K).subgroupOf G := QuotientGroup.ker_mk' _
  have hc : π.ker ≤ Subgroup.center ↥G := by
    intro k hk
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have hk' : ((k : ↥G) : GL (Fin 4) K) ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hk
    rw [Subgroup.mem_center_iff] at hk' ⊢
    intro g
    exact Subtype.ext (hk' g)
  have hcop : Nat.Coprime (Nat.card π.ker) p := by
    have h2 : IsPGroup 2 π.ker := by
      intro k
      refine ⟨2, ?_⟩
      have hk1 : π (k : ↥G) = 1 := MonoidHom.mem_ker.mp k.2
      have hkS : (k : ↥G) ∈ (StatedScalars (Fin 4) K).subgroupOf G :=
        (QuotientGroup.eq_one_iff (k : ↥G)).mp hk1
      rw [Subgroup.mem_subgroupOf] at hkS
      obtain ⟨c, hcK⟩ := hkS
      have hdet := (unitary_det_of_mem_statedSU (frobenius K r) hfrob ((k : ↥G).2)).2
      rw [← hcK, Matrix.GeneralLinearGroup.coe_scalar] at hdet
      have hc4 : c ^ 4 = 1 := by
        apply Units.ext
        simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow, ← hcK, ← map_pow,
        show (2 : ℕ) ^ 2 = 4 by norm_num, hc4, map_one]
      rfl
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨Ã, -, -, e, -⟩ := exists_sylow_lift_of_ker_le_center hp π hπs hc hcop A₁
    hA₁e.isPGroup
  letI : CommGroup A₁ := { (inferInstance : Group A₁) with mul_comm := hA₁e.1.is_comm.comm }
  haveI : Fintype A₁ := Fintype.ofFinite A₁
  have hU : ∀ g ∈ G, ((g : Matrix (Fin 4) (Fin 4) K).map (frobenius K r))ᵀ *
      (g : Matrix (Fin 4) (Fin 4) K) = 1 := fun g hg =>
    (unitary_det_of_mem_statedSU (frobenius K r) hfrob hg).1
  exact false_of_unitary_lift hp7 hpr hU e (fun a => Subtype.ext (hA₁e.2 a a.2))
    (by rw [Fintype.card_eq_nat_card, hA₁c])
end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
