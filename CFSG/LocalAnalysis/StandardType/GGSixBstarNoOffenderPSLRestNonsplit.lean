module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSL
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSL
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial

namespace NoOffPSLRest

section Frame

variable {G : Type} [Group G] {F : Type} [Field F] {n e s r p : ℕ}

theorem mod_eq_of_map_nsSL_eq (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1) (he : e ≠ 0) (hp0 : 0 < p)
    (hCp : C ^ p = 1) (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    {φ : SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) {k k' : Fin s → ℕ}
    (h : φ (SLNS.nsSL ε hC k) = φ (SLNS.nsSL ε hC k')) (i : Fin s) : k i % p = k' i % p := by
  classical
  set z := (SLNS.nsSL ε hC k')⁻¹ * SLNS.nsSL ε hC k with hz
  have hzk : z ∈ φ.ker := by rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hzk)
  have hkk : SLNS.nsSL ε hC k = SLNS.nsSL ε hC k' * z := by rw [hz, mul_inv_cancel_left]
  have hmat : SLNS.nsMat ε C k = SLNS.nsMat ε C k' * Matrix.scalar (Fin n) c := by
    have h1 := congrArg (fun t : SpecialLinearGroup (Fin n) F => (t : Matrix (Fin n) (Fin n) F))
      hkk
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
    rw [hc]
    exact h1
  have hblock : C ^ k i = c • C ^ k' i := by
    ext a b
    have h1 := congrFun (congrFun hmat (ε.symm (Sum.inl (a, i)))) (ε.symm (Sum.inl (b, i)))
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, SLNS.nsMat_block, SLNS.nsMat_block] at h1
    rw [h1, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have hzero : C ^ (k i + (p - 1) * k' i) - c • 1 = 0 := by
    have h1 : k' i + (p - 1) * k' i = p * k' i := by
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [pow_add, hblock, smul_mul_assoc, ← pow_add, h1, pow_mul, hCp, one_pow, sub_self]
  have hdvd : p ∣ k i + (p - 1) * k' i := by
    by_contra hnd
    have : Nonempty (Fin e) := ⟨⟨0, Nat.pos_of_ne_zero he⟩⟩
    have hu := hunit _ hnd c
    rw [hzero] at hu
    exact not_isUnit_zero hu
  have h2 : k i + (p - 1) * k' i + k' i = k i + p * k' i := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  calc k i % p = (k i + p * k' i) % p := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (k i + (p - 1) * k' i + k' i) % p := by rw [h2]
    _ = k' i % p := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod]

theorem eq_of_map_eq_of_pow {φ : SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hnsplit : ∀ c : F, c ^ p = 1 → c = 1) {X Y : SpecialLinearGroup (Fin n) F}
    (hX : X ^ p = 1) (hY : Y ^ p = 1) (h : φ X = φ Y) : X = Y := by
  set z := Y⁻¹ * X with hz
  have hzk : z ∈ φ.ker := by rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h, inv_mul_cancel]
  have hzc := hker hzk
  have hXYz : X = Y * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : X ^ p = Y ^ p * z ^ p := by
      rw [hXYz]
      exact Commute.mul_pow (Subgroup.mem_center_iff.mp hzc Y) p
    rw [hX, hY, one_mul] at h1
    exact h1.symm
  have hz1 : z = 1 := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · exact Subsingleton.elim _ _
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzc
    have hcp : c ^ p = 1 := by
      have h1 := congrArg (fun t : SpecialLinearGroup (Fin n) F =>
        (t : Matrix (Fin n) (Fin n) F) i i) hzp
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, one_apply_eq,
        ← hc] at h1
      rwa [Matrix.scalar_apply, diagonal_pow, diagonal_apply_eq] at h1
    apply Subtype.ext
    rw [← hc, hnsplit c hcp, map_one]
    rfl
  rw [hXYz, hz1, mul_one]

end Frame

section Coords

variable {G : Type} [Group G] {F : Type} [Field F] {n e s r p : ℕ}

@[expose] noncomputable def nsExp (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1) (φ : SpecialLinearGroup (Fin n) F →* G)
    (b : G) : Fin s → ℕ :=
  open Classical in
  if h : ∃ k : Fin s → ℕ, b = φ (SLNS.nsSL ε hC k) then Classical.choose h else 0

theorem nsExp_spec (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F}
    (hC : C.det = 1) (φ : SpecialLinearGroup (Fin n) F →* G) {b : G}
    (h : ∃ k : Fin s → ℕ, b = φ (SLNS.nsSL ε hC k)) : b = φ (SLNS.nsSL ε hC (nsExp ε hC φ b)) := by
  rw [nsExp, dite_eq_left h]
  exact Classical.choose_spec h

@[expose] noncomputable def nsCoord (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1) (φ : SpecialLinearGroup (Fin n) F →* G)
    (ζ : ℂˣ) (b : G) : Fin s → ℂˣ :=
  fun i => ζ ^ nsExp ε hC φ b i

theorem nsCoord_eq (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F}
    (hC : C.det = 1) (he : e ≠ 0) (hp0 : 0 < p) (hCp : C ^ p = 1)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    {φ : SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) {ζ : ℂˣ}
    (hord : orderOf ζ = p) (k : Fin s → ℕ) :
    nsCoord ε hC φ ζ (φ (SLNS.nsSL ε hC k)) = fun i => ζ ^ k i := by
  funext i
  have h1 := nsExp_spec ε hC φ ⟨k, rfl⟩
  have h2 := mod_eq_of_map_nsSL_eq ε hC he hp0 hCp hunit hker h1.symm i
  change ζ ^ nsExp ε hC φ (φ (SLNS.nsSL ε hC k)) i = ζ ^ k i
  rw [pow_eq_pow_iff_modEq, hord]
  exact h2

theorem coords [Finite F] {B Bs G₀ : Subgroup G} {ψ : SpecialLinearGroup (Fin n) F →* G}
    {A₀ : SpecialLinearGroup (Fin n) F} {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
    {C : Matrix (Fin e) (Fin e) F} {hC : C.det = 1} (hc : SLNS.NSCtx ε hC p B Bs G₀ ψ A₀)
    (he : e ≠ 0) {ζ : ℂˣ} (hord : orderOf ζ = p) :
    NoOffenderClassical.Coords p Bs (nsCoord ε hC (SLRep.ggFrame ψ A₀) ζ) := by
  have hp0 := hc.prime.pos
  have : NeZero p := ⟨hc.prime.ne_zero⟩
  have hker := hc.ker_frame
  have heq := nsCoord_eq ε hC he hp0 hc.cp hc.cunit hker hord
  have hprim : IsPrimitiveRoot (ζ : ℂ) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord)
  refine ⟨fun a ha b hb => ?_, fun a ha b hb hab => ?_, fun t ht => ?_⟩
  · obtain ⟨ka, rfl⟩ := hc.frame a ha
    obtain ⟨kb, rfl⟩ := hc.frame b hb
    rw [← map_mul, SLNS.nsSL_mul, heq, heq, heq]
    funext i
    simp only [Pi.add_apply, Pi.mul_apply, pow_add]
  · obtain ⟨ka, rfl⟩ := hc.frame a ha
    obtain ⟨kb, rfl⟩ := hc.frame b hb
    rw [heq, heq] at hab
    refine congrArg _ (SLNS.nsSL_congr ε hC hc.cp fun i => ?_)
    have h1 := congrFun hab i
    rw [pow_eq_pow_iff_modEq, hord] at h1
    exact h1
  · have hpow : ∀ i, ∃ c, ζ ^ c = t i := fun i => by
      obtain ⟨c, -, hc'⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (t i : ℂ))
        (by rw [← Units.val_pow_eq_pow_val, ht i, Units.val_one])
      exact ⟨c, Units.ext (by rw [Units.val_pow_eq_pow_val, hc'])⟩
    choose c hc' using hpow
    refine ⟨SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC c), hc.mem_bstar c, ?_⟩
    rw [heq]
    exact funext hc'

end Coords

end NoOffPSLRest

section Family

theorem ggSixBstarNoOffenderOn_PSLNonsplit : GGSixBstarNoOffenderOn GGPSLNonsplit := by
  classical
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hns⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hpp hp2
  have hnsplit : ∀ c : GaloisField 2 f, c ^ p = 1 → c = 1 := fun c hc =>
    OrdPNS.eq_one_of_pow_eq_one hpp hpF hc
  have hX : ∀ b : Bs, ∃ X : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
      X ^ p = 1 ∧ (b : G) = ψ X := fun b =>
    SLNSRest.exists_sl_of_innerDiag hm hker hCψ hpp hpF (hctx.2.1.2.1.2 b b.2)
      (hctx.2.2.2.2.2.2.1.2 _ (Bs.inv_mem b.2))
  choose X hXp hXb using hX
  have hXc : ∀ b c : Bs, X b * X c = X c * X b := fun b c =>
    SLNSRest.commute_of_map_eq hker hpp hpF (hXp b) (by
      have h := TableB.IsElemAbelian.comm hctx.2.1.2.1 b.2 c.2
      rw [hXb b, hXb c] at h
      exact h)
  obtain ⟨d, s, r, C, hCdet, ε, A₀, hCp, hcunit, hframe⟩ :=
    NSFrame.exists_nsFrame hpp hpF hpK
      (Set.range fun b : Bs => (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
      (by
        rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
        change (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X c : _) =
          (X c : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X b : _)
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hXc])
      (by
        rintro _ ⟨b, rfl⟩
        rw [← Matrix.SpecialLinearGroup.coe_pow, hXp, Matrix.SpecialLinearGroup.coe_one])
  have hframe' : ∀ b ∈ Bs, ∃ k : Fin s → ℕ, b = SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hCdet k) := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : X ⟨b, hb⟩ * A₀ = A₀ * SLNS.nsSL ε hCdet k := Subtype.ext hk
    have h2 : X ⟨b, hb⟩ = A₀ * SLNS.nsSL ε hCdet k * A₀⁻¹ := by
      rw [← h1, mul_inv_cancel_right]
    exact (hXb ⟨b, hb⟩).trans (congrArg ψ h2)
  have hNS : SLNS.NSCtx ε hCdet p B Bs (ggG0 p B x L D J) ψ A₀ :=
    ⟨hctx.2.1, hker, hctx.range_eq, hC, hpp, hnsplit, hCp, hcunit, hframe'⟩
  set φ := SLRep.ggFrame ψ A₀ with hφ
  intro E hEM hEN hE
  by_cases hEC : E ≤ Subgroup.centralizer (Bs : Set G)
  · exact Or.inl hEC
  right
  have hd : d ≠ 0 := by
    intro hd0
    apply hEC
    intro y _
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, rfl⟩ := hframe' b hb
    rw [SLNS.nsSL_eq_one_of_e_zero ε hCdet hd0 k, map_one, one_mul, mul_one]
  have hunit1 : ∀ j : ℕ, ¬ p ∣ j → IsUnit (C ^ j - 1) := fun j hj => by
    simpa using hcunit j hj 1
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hpp.ne_zero
  set ζu : ℂˣ := (hζ.isUnit hpp.ne_zero).unit with hζudef
  have hζu : (ζu : ℂ) = Complex.exp (2 * Real.pi * Complex.I / p) := IsUnit.unit_spec _
  have hord : orderOf ζu = p :=
    ((IsPrimitiveRoot.coe_units_iff.mp (hζu ▸ hζ)).eq_orderOf).symm
  set κ := NoOffPSLRest.nsCoord ε hCdet φ ζu with hκdef
  have hκ : NoOffenderClassical.Coords p Bs κ := NoOffPSLRest.coords hNS hd hord
  have hκ1 : ∀ b (j : Fin s), κ b j = 1 ↔ p ∣ NoOffPSLRest.nsExp ε hCdet φ b j := fun b j => by
    change ζu ^ _ = 1 ↔ _
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.symm
  refine NoOffenderClassical.card_mul_lt_of_coords hpp hp2 hζ hκ hctx.bstar.2.1 hE hEN
    (fun y hy => ?_) hEC
  have hyM : y ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]
    exact hEM hy
  have hyB : y ∈ Subgroup.normalizer (Bs : Set G) := hEN hy
  obtain ⟨A, σ, hAσ⟩ :=
    NoOffenderClassical.SL.exists_semilinear hm hpp hp2 hker hCψ hyM (hE.2 y hy)
  refine NoOffPSLRest.exists_supp_perm_of_single hpp hζ hκ hctx.bstar.2.1.2 hyB
    (fun b hb i hbi => ?_)
  have hyb : y * b * y⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hyB b).mp hb
  set k := NoOffPSLRest.nsExp ε hCdet φ b with hk
  set k' := NoOffPSLRest.nsExp ε hCdet φ (y * b * y⁻¹) with hk'
  have hbk : b = φ (SLNS.nsSL ε hCdet k) := NoOffPSLRest.nsExp_spec ε hCdet φ (hframe' b hb)
  have hbk' : y * b * y⁻¹ = φ (SLNS.nsSL ε hCdet k') :=
    NoOffPSLRest.nsExp_spec ε hCdet φ (hframe' _ hyb)
  set Xb := A₀ * SLNS.nsSL ε hCdet k * A₀⁻¹ with hXbdef
  set Xb' := A₀ * SLNS.nsSL ε hCdet k' * A₀⁻¹ with hXb'def
  have hXbp : Xb ^ p = 1 := by
    rw [hXbdef, conj_pow, SLNS.nsSL_pow_p ε hCdet hCp, mul_one, mul_inv_cancel]
  have hXb'p : Xb' ^ p = 1 := by
    rw [hXb'def, conj_pow, SLNS.nsSL_pow_p ε hCdet hCp, mul_one, mul_inv_cancel]
  set X₁ := InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom Xb) with hX₁
  have hX₁p : X₁ ^ p = 1 := by rw [hX₁, ← map_pow, ← map_pow, hXbp, map_one, map_one]
  have hbX : b = ψ Xb := hbk.trans (SLRep.ggFrame_apply ψ A₀ _)
  have hψ : ψ Xb' = ψ X₁ :=
    calc ψ Xb' = y * b * y⁻¹ := (hbk'.trans (SLRep.ggFrame_apply ψ A₀ _)).symm
      _ = y * ψ Xb * y⁻¹ := by rw [← hbX]
      _ = ψ X₁ := hAσ Xb
  have hXX : Xb' = X₁ := NoOffPSLRest.eq_of_map_eq_of_pow hker hnsplit hXb'p hX₁p hψ
  have hA₀ : (A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
      ((A₀⁻¹ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hA₀' : ((A₀⁻¹ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
      (A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hA : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
      ((A⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : ((A⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM : ((Xb : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
      (A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * SLNS.nsMat ε C k *
        ((A₀⁻¹ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := by
    rw [hXbdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rfl
  have hM' : ((Xb' : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
      (A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * SLNS.nsMat ε C k' *
        ((A₀⁻¹ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := by
    rw [hXb'def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rfl
  have hM₁ : ((X₁ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
        ((Xb : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).map σ *
        ((A⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := by
    rw [hX₁, InnerDiagA.coe_conjSL]
    rfl
  have hfix : Nat.card {v : Fin (m + 1) → GaloisField 2 f // SLNS.nsMat ε C k' *ᵥ v = v} =
      Nat.card {v : Fin (m + 1) → GaloisField 2 f // SLNS.nsMat ε C k *ᵥ v = v} := by
    rw [← NoOffPSLRest.card_fix_conj _ _ (SLNS.nsMat ε C k') hA₀ hA₀', ← hM', hXX, hM₁,
      NoOffPSLRest.card_fix_conj _ _ _ hA hA', NoOffPSLRest.card_fix_map, hM,
      NoOffPSLRest.card_fix_conj _ _ _ hA₀ hA₀']
  have hfilt := NoOffPSLRest.card_filter_eq_of_card_fix_eq ε hCp hunit1 hd hfix
  have hone : (Finset.univ.filter fun j => ¬ p ∣ k j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [← hbi j, ne_eq, hκ1]
  have hcount : (Finset.univ.filter fun j => ¬ p ∣ k' j).card = 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => p ∣ k j)
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => p ∣ k' j)
    rw [hone, Finset.card_singleton] at h1
    omega
  obtain ⟨i', hi'⟩ := Finset.card_eq_one.mp hcount
  refine ⟨i', fun j => ?_⟩
  have h1 := Finset.ext_iff.mp hi' j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at h1
  rw [ne_eq, hκ1]
  exact h1

end Family

end CFSG.StandardType
