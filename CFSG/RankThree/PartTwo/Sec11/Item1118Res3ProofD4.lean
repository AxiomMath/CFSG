module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofLattice
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofD4
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofRep

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1118Res3Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
open scoped Matrix


theorem eq_scalar_of_smul_eq_scalar {Ω : Type} [Field Ω] {u : Ωˣ}
    {A : Matrix (Fin 3) (Fin 3) Ω} {r : Ω} (h : (u : Ω) • A = Matrix.scalar (Fin 3) r) :
    A = Matrix.scalar (Fin 3) (((u⁻¹ : Ωˣ) : Ω) * r) := by
  have h1 := congrArg (fun B => ((u⁻¹ : Ωˣ) : Ω) • B) h
  simp only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h1
  rw [h1, Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal]

section Model

open scoped Pointwise

variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]

abbrev nvT (Ω : Type) [Field Ω] : ModGL TwistTag.D4.tag Ω :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) Ω vTt

theorem exists_decomp {g : ModGL TwistTag.D4.tag Ω} {a : Fin TwistTag.D4.tag.rank → Ωˣ}
    (hMset : (toralCentralizer Tag.D4 Ω a : Set (ModGL Tag.D4 Ω)) =
      (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) * (d4A2Qv Ω vT : Set (ModGL Tag.D4 Ω)))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hD : Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      (toralCentralizer TwistTag.D4.tag Ω a).comap (threeSixEmb' Ω K σ g))
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hy : y ∈ Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ (b : Fin TwistTag.D4.tag.rank → Ωˣ) (u : ModGL TwistTag.D4.tag Ω), u ∈ d4A2Qv Ω vT ∧
      threeSixEmb' Ω K σ g y = rootDiagUnit TwistTag.D4.tag b * u := by
  rw [hD, Subgroup.mem_comap] at hy
  have hy' : threeSixEmb' Ω K σ g y ∈
      (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) * (d4A2Qv Ω vT : Set (ModGL Tag.D4 Ω)) := by
    rw [← hMset]
    exact hy
  obtain ⟨t, ht, u, hu, htu⟩ := hy'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact ⟨b, u, hu, htu.symm⟩

theorem conj_mem_subsystemGroup' {u : ModGL Tag.D4 Ω} (hu : u ∈ d4A2Qv Ω vT) :
    (canonicalRep (coxeterSystem Tag.D4) Ω vT)⁻¹ * u * canonicalRep (coxeterSystem Tag.D4) Ω vT ∈
      subsystemGroup Tag.D4 Ω d4SuppA2 := by
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
  have e : (canonicalRep (coxeterSystem Tag.D4) Ω vT)⁻¹ *
      (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) Ω vT)).toMonoidHom u₀ *
        canonicalRep (coxeterSystem Tag.D4) Ω vT = u₀ := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hu₀

theorem conj_mem_subsystemGroup {u : ModGL TwistTag.D4.tag Ω} (hu : u ∈ d4A2Qv Ω vT) :
    (nvT Ω)⁻¹ * u * nvT Ω ∈ subsystemGroup Tag.D4 Ω d4SuppA2 :=
  conj_mem_subsystemGroup' hu

theorem conj_decomp (b : Fin TwistTag.D4.tag.rank → Ωˣ) (u : ModGL TwistTag.D4.tag Ω) :
    (nvT Ω)⁻¹ * (rootDiagUnit TwistTag.D4.tag b * u) * nvT Ω =
      rootDiagUnit TwistTag.D4.tag
          (fun j => rootChar b (vTt • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ))) *
        ((nvT Ω)⁻¹ * u * nvT Ω) := by
  rw [← canonicalRep_inv_conj_rootDiagUnit' vTt b]
  group

theorem conj_decomp_mem_v0Stab (b : Fin TwistTag.D4.tag.rank → Ωˣ) {u : ModGL TwistTag.D4.tag Ω}
    (hu : u ∈ d4A2Qv Ω vT) :
    (nvT Ω)⁻¹ * (rootDiagUnit TwistTag.D4.tag b * u) * nvT Ω ∈ v0Stab Ω := by
  rw [conj_decomp]
  exact mul_mem (rootDiagUnit_mem_v0Stab _) (subsystemGroup_le_v0Stab (conj_mem_subsystemGroup hu))

@[expose] def pullTuple (b : Fin TwistTag.D4.tag.rank → Ωˣ) : Fin TwistTag.D4.tag.rank → Ωˣ :=
  fun j => rootChar b (vTt • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ))

theorem rootChar_pullTuple (b : Fin TwistTag.D4.tag.rank → Ωˣ)
    (l : Fin TwistTag.D4.tag.rank → ℤ) : rootChar (pullTuple b) l = rootChar b (vTt • l) :=
  (rootChar_smul_eq_rootChar b vTt l).symm

theorem rootChar_pullTuple_d4A2Weight (b : Fin TwistTag.D4.tag.rank → Ωˣ) :
    rootChar (pullTuple b) (d4A2Weight 0) = rootChar b vBeta0 ∧
      rootChar (pullTuple b) (d4A2Weight 1) = rootChar b vBeta1 ∧
        rootChar (pullTuple b) (d4A2Weight 2) = rootChar b vBeta2 := by
  obtain ⟨h0, h1, h2⟩ := vT_smul_d4A2Weight
  exact ⟨(rootChar_pullTuple b _).trans (congrArg (rootChar b) h0),
    (rootChar_pullTuple b _).trans (congrArg (rootChar b) h1),
    (rootChar_pullTuple b _).trans (congrArg (rootChar b) h2)⟩

theorem conj_rootDiagUnit_pullTuple (b : Fin TwistTag.D4.tag.rank → Ωˣ) :
    (nvT Ω)⁻¹ * rootDiagUnit TwistTag.D4.tag b * nvT Ω =
      rootDiagUnit TwistTag.D4.tag (pullTuple b) :=
  canonicalRep_inv_conj_rootDiagUnit' vTt b

theorem d4A2Mat_rootDiagUnit' (b : Fin TwistTag.D4.tag.rank → Ωˣ) :
    d4A2Mat (rootDiagUnit TwistTag.D4.tag b) =
      Matrix.diagonal fun k => ((rootChar b (d4A2Weight k) : Ωˣ) : Ω) :=
  d4A2Mat_rootDiagUnit b

theorem det_d4A2Mat_pullTuple (b : Fin TwistTag.D4.tag.rank → Ωˣ) :
    (d4A2Mat (rootDiagUnit TwistTag.D4.tag (pullTuple b))).det =
      ((rootChar b (latE + 2 • latF) : Ωˣ) : Ω) := by
  obtain ⟨h0, h1, h2⟩ := rootChar_pullTuple_d4A2Weight b
  rw [d4A2Mat_rootDiagUnit', Matrix.det_diagonal, Fin.prod_univ_three, h0, h1, h2, ← vBeta_sum,
    rootChar_add, rootChar_add, Units.val_mul, Units.val_mul]

theorem d4A2Mat_mul_of_mem' {g h : ModGL TwistTag.D4.tag Ω} (hh : h ∈ v0Stab Ω) :
    d4A2Mat (g * h) = d4A2Mat g * d4A2Mat h :=
  d4A2Mat_mul_of_mem hh

theorem rootChar_single_t (b : Fin TwistTag.D4.tag.rank → Ωˣ) (i : Fin TwistTag.D4.tag.rank) :
    rootChar b (Pi.single i 1) = b i := by
  have h := rootChar_nsmul_single b i 1
  rwa [one_smul, pow_one] at h

end Model

theorem natCast_eq_eps {q j : ℕ} {ε : ℤ}
    (hqj : (ε = 1 ∧ q = 3 * j + 1) ∨ (ε = -1 ∧ q = 3 * j + 2)) : ((q : ℕ) : ZMod 3) = ε := by
  rcases hqj with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [h]
    push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_add]
  · rw [h]
    push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_add]
    rfl

section SL3

open scoped Pointwise

theorem exists_isSL3Model_model {ℓ f j : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ}
    (hqj : (ε = 1 ∧ ℓ ^ f = 3 * j + 1) ∨ (ε = -1 ∧ ℓ ^ f = 3 * j + 2))
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) {ζ : Ωˣ} (hζ : orderOf ζ = 3)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * g⁻¹) :
    ∃ ρ : Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →*
      Matrix.SpecialLinearGroup (Fin 3) Ω, Item1118Res2Proof.IsSL3Model ρ := by
  classical
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hqj with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = ε := natCast_eq_eps hqj
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube hℓ hf hK
  have hpK : ringChar Ω ≠ 3 := by
    rw [ringChar.eq Ω ℓ]
    exact hℓ3
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hζ3 := pow_three_of_orderOf hζ
  have ha := mem_threeSixTorus_tup_gT (L := Ω) hFr hε hqε hζ3
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  have hstab := threeSix_stab hFr hε ha hv
  obtain ⟨-, hMset, -, -, -, -, -, hinf, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK (tup ζ gT)
      hord vT hv.symm
  have hD := centralizer_eq_comap hrange hgG hFg hx
  set ι := threeSixEmb' Ω K σ g with hιdef
  have hιinj : Function.Injective ι := threeSixEmb'_injective g
  have hfix : ∀ y, threeSixFrob Ω Fr ε (ι y) = ι y := fun y =>
    ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  have hιx : ι x = rootDiagUnit TwistTag.D4.tag (tup ζ gT) := by
    rw [hιdef, threeSixEmb'_apply, hx]
    group
  set C := Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    with hCdef
  have hconj : ∀ y : C, (MulAut.conj (nvT Ω)⁻¹).toMonoidHom (ι y) = (nvT Ω)⁻¹ * ι y * nvT Ω :=
    fun y => by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hmemS : ∀ y : C, (MulAut.conj (nvT Ω)⁻¹).toMonoidHom (ι y) ∈ v0Stab Ω := fun y => by
    obtain ⟨b, u, hu, hbu⟩ := exists_decomp hMset hD y.2
    rw [hconj, hbu]
    exact conj_decomp_mem_v0Stab b hu
  let φ : C →* v0Stab Ω := ((((MulAut.conj (nvT Ω)⁻¹).toMonoidHom.comp ι).comp
    C.subtype).codRestrict (v0Stab Ω) hmemS)
  let ρ₀ : C →* GL (Fin 3) Ω := (v0Rep Ω).comp φ
  have hρ₀ : ∀ y : C, ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      d4A2Mat ((nvT Ω)⁻¹ * ι y * nvT Ω) := fun y => by
    rw [← hconj]
    rfl
  have hdet : ∀ y : C,
      Matrix.GeneralLinearGroup.det (ρ₀ y) ^ (3 * j ^ 2 + 3 * j + 1) = 1 := fun y => by
    obtain ⟨b, u, hu, hbu⟩ := exists_decomp hMset hD y.2
    have hu' := conj_mem_subsystemGroup hu
    have h1 : ((Matrix.GeneralLinearGroup.det (ρ₀ y) : Ωˣ) : Ω) =
        ((rootChar b (latE + 2 • latF) : Ωˣ) : Ω) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hρ₀, hbu, conj_decomp,
        d4A2Mat_mul_of_mem' (subsystemGroup_le_v0Stab hu'), Matrix.det_mul, det_d4A2Mat hu',
        mul_one]
      exact det_d4A2Mat_pullTuple b
    have hs : (rootDiagUnit TwistTag.D4.tag b)⁻¹ *
        threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag b) ∈ d4A2Tv Ω vT := by
      rw [← hinf]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h2 : threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag b) *
            threeSixFrob Ω Fr ε u = rootDiagUnit TwistTag.D4.tag b * u := by
          rw [← map_mul, ← hbu, hfix]
        have h3 : (rootDiagUnit TwistTag.D4.tag b)⁻¹ *
            threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag b) =
              u * (threeSixFrob Ω Fr ε u)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h2, mul_inv_cancel_right]
        rw [h3]
        have hFu : threeSixFrob Ω Fr ε u ∈ d4A2Qv Ω vT :=
          (map_threeSixFrob_d4A2Qv Fr hFrs hε vT hstab).le ⟨u, hu, rfl⟩
        exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hFu)
      · obtain ⟨b', hb', -⟩ := rootChar_threeSixFrob_rootDiagUnit Fr hFr ε b
        rw [hb', rootDiagUnit_inv, ← rootDiagUnit_mul]
        exact rootDiagUnit_mem_torusGroup _
    have hpow := rootChar_detVec_pow_eq_one Fr hFr hqj b hs
    exact Units.ext (by
      rw [Units.val_pow_eq_pow_val, h1, ← Units.val_pow_eq_pow_val, hpow, Units.val_one])
  set x' : C := ⟨x, Item1118Res2Proof.self_mem_centralizer x⟩ with hx'
  have hρ₀x : ((ρ₀ x' : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      Matrix.scalar (Fin 3) ((ζ : Ω) ^ 2) := by
    rw [hρ₀]
    change d4A2Mat ((nvT Ω)⁻¹ * ι x * nvT Ω) = _
    rw [hιx, conj_rootDiagUnit_pullTuple, d4A2Mat_rootDiagUnit', Matrix.scalar_apply]
    congr 1
    obtain ⟨h0, h1, h2⟩ := rootChar_pullTuple_d4A2Weight (tup ζ gT)
    obtain ⟨p0, p1, p2⟩ := gT_pairing_vBeta
    have hv2 : (2 : ZMod 3).val = 2 := rfl
    have e0 : ((rootChar (pullTuple (tup ζ gT)) (d4A2Weight 0) : Ωˣ) : Ω) = (ζ : Ω) ^ 2 := by
      rw [h0, rootChar_tup hζ3, p0, hv2, Units.val_pow_eq_pow_val]
    have e1 : ((rootChar (pullTuple (tup ζ gT)) (d4A2Weight 1) : Ωˣ) : Ω) = (ζ : Ω) ^ 2 := by
      rw [h1, rootChar_tup hζ3, p1, hv2, Units.val_pow_eq_pow_val]
    have e2 : ((rootChar (pullTuple (tup ζ gT)) (d4A2Weight 2) : Ωˣ) : Ω) = (ζ : Ω) ^ 2 := by
      rw [h2, rootChar_tup hζ3, p2, hv2, Units.val_pow_eq_pow_val]
    funext k
    fin_cases k
    · exact e0
    · exact e1
    · exact e2
  have hδx : Matrix.GeneralLinearGroup.det (ρ₀ x') = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hρ₀x, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
      show 2 * 3 = 3 * 2 by rfl, pow_mul, ← Units.val_pow_eq_pow_val, hζ3, Units.val_one,
      one_pow]
  have hscalar : ∀ y : C, ∀ r : Ω,
      ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) r →
      ∃ c : Fin TwistTag.D4.tag.rank → Ωˣ, c 0 = 1 ∧ c 2 = 1 ∧
        (nvT Ω)⁻¹ * ι y * nvT Ω = rootDiagUnit TwistTag.D4.tag c := fun y r hr => by
    obtain ⟨b, u, hu, hbu⟩ := exists_decomp hMset hD y.2
    have hu' := conj_mem_subsystemGroup hu
    rw [hρ₀, hbu, conj_decomp] at hr
    obtain ⟨c, hc, hc0, hc2⟩ := exists_rootDiagUnit_of_d4A2Mat_scalar (pullTuple b) hu' hr
    exact ⟨c, hc0, hc2, by rw [hbu, conj_decomp]; exact hc⟩
  have hcentral : ∀ y : C, ∀ r : Ω,
      ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) r →
      ∀ z : C, y * z = z * y := fun y r hr z => by
    obtain ⟨c, hc0, hc2, hc⟩ := hscalar y r hr
    obtain ⟨b₂, u₂, hu₂, hbu₂⟩ := exists_decomp hMset hD z.2
    have hu₂' := conj_mem_subsystemGroup hu₂
    have hz : (nvT Ω)⁻¹ * ι z * nvT Ω = rootDiagUnit TwistTag.D4.tag (pullTuple b₂) *
        ((nvT Ω)⁻¹ * u₂ * nvT Ω) := by
      rw [hbu₂, conj_decomp]
      rfl
    have hcomm : rootDiagUnit TwistTag.D4.tag c * ((nvT Ω)⁻¹ * ι z * nvT Ω) =
        ((nvT Ω)⁻¹ * ι z * nvT Ω) * rootDiagUnit TwistTag.D4.tag c := by
      rw [hz]
      exact rootDiagUnit_commute_of_mem hc0 hc2 (rootDiagUnit_mem_torusGroup _) hu₂'
    have hιy : ι y = nvT Ω * rootDiagUnit TwistTag.D4.tag c * (nvT Ω)⁻¹ := by
      rw [← hc]
      group
    have h2 := congrArg (fun w => nvT Ω * w * (nvT Ω)⁻¹) hcomm
    have hyz : ι y * ι z = ι z * ι y := by
      rw [hιy]
      calc nvT Ω * rootDiagUnit TwistTag.D4.tag c * (nvT Ω)⁻¹ * ι z
          = nvT Ω * (rootDiagUnit TwistTag.D4.tag c * ((nvT Ω)⁻¹ * ι z * nvT Ω)) *
              (nvT Ω)⁻¹ := by group
        _ = nvT Ω * (((nvT Ω)⁻¹ * ι z * nvT Ω) * rootDiagUnit TwistTag.D4.tag c) *
              (nvT Ω)⁻¹ := h2
        _ = ι z * (nvT Ω * rootDiagUnit TwistTag.D4.tag c * (nvT Ω)⁻¹) := by group
    apply Subtype.ext
    apply hιinj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hyz
  have hthree : ∀ y : C, (∃ k : ℕ, y ^ 3 ^ k = 1) → ∀ r : Ω,
      ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) r →
      (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈ Subgroup.zpowers x :=
      fun y hy3 r hr => by
    obtain ⟨c, hc0, hc2, hc⟩ := hscalar y r hr
    have hιy : ι y = nvT Ω * rootDiagUnit TwistTag.D4.tag c * (nvT Ω)⁻¹ := by
      rw [← hc]
      group
    have hH : ι y ∈ torusGroup TwistTag.D4.tag Ω := by
      rw [hιy]
      exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer vTt) _).1
        (rootDiagUnit_mem_torusGroup c)
    obtain ⟨c', hc'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
    have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff c' c vTt).1 (hc'.symm.trans hιy)
    have hc'1 : c' 1 = 1 := by
      have h := hchar (Pi.single 2 1)
      rw [vTt_smul_single_two, rootChar_single_t, rootChar_single_t, hc2] at h
      exact h
    have hc'2 : c' 2 = 1 := by
      have h := hchar (Pi.single 0 1)
      rw [vTt_smul_single_zero, rootChar_single_t, rootChar_single_t, hc0] at h
      exact h
    have hF : threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag c') =
        rootDiagUnit TwistTag.D4.tag c' := by
      rw [← hc']
      exact hfix y
    have h3' : ∃ k : ℕ, rootDiagUnit TwistTag.D4.tag c' ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hy3
      refine ⟨k, ?_⟩
      rw [← hc', ← map_pow]
      have : (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ^ 3 ^ k = 1 := by
        rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
      rw [this, map_one]
    have hz := rootDiagUnit_mem_zpowers_of_fixed Fr hFr hqj hζ hc'1 hc'2 hF h3'
    rw [← hc', ← hιx] at hz
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Subgroup.mem_zpowers_iff.2 ⟨i, hιinj ?_⟩
    rw [map_zpow, hi]
  let δ : C →* Ωˣ := Matrix.GeneralLinearGroup.det.comp ρ₀
  have hδ : ∀ y : C, ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det = (δ y : Ω) :=
    fun y => (Matrix.GeneralLinearGroup.val_det_apply _).symm
  have hdetρ : ∀ y : C, (((δ y ^ (j * (j + 1)) : Ωˣ) : Ω) •
      ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)).det = 1 := fun y => by
    rw [Matrix.det_smul, Fintype.card_fin, hδ, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← pow_mul, ← pow_succ, show j * (j + 1) * 3 + 1 = 3 * j ^ 2 + 3 * j + 1 by ring]
    exact congrArg Units.val (hdet y) |>.trans Units.val_one
  let ρ : C →* Matrix.SpecialLinearGroup (Fin 3) Ω :=
    { toFun := fun y => ⟨((δ y ^ (j * (j + 1)) : Ωˣ) : Ω) •
        ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω), hdetρ y⟩
      map_one' := by
        apply Subtype.ext
        simp only [map_one, one_pow, Units.val_one, one_smul]
        rfl
      map_mul' := fun y z => by
        apply Subtype.ext
        simp only [map_mul, mul_pow, Units.val_mul]
        change _ = (((δ y ^ (j * (j + 1)) : Ωˣ) : Ω) •
            ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)) *
          (((δ z ^ (j * (j + 1)) : Ωˣ) : Ω) • ((ρ₀ z : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω))
        rw [smul_mul_smul_comm] }
  have hρ : ∀ y : C, ((ρ y : Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      ((δ y ^ (j * (j + 1)) : Ωˣ) : Ω) • ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) :=
    fun _ => rfl
  have hδx : δ x' = 1 := hδx
  have hρx : ((ρ x' : Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      Matrix.scalar (Fin 3) ((ζ : Ω) ^ 2) := by
    rw [hρ, hδx, one_pow, Units.val_one, one_smul, hρ₀x]
  refine ⟨ρ, ?_, ?_, fun y hy3 hyc => ?_, fun y z hy => ?_⟩
  ·
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨(ζ : Ω) ^ 2, ?_, ?_⟩
    · rw [Fintype.card_fin, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul,
        ← Units.val_pow_eq_pow_val, hζ3, Units.val_one, one_pow]
    · exact hρx.symm
  ·
    intro h1
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) Ω =>
      (A : Matrix (Fin 3) (Fin 3) Ω) 0 0) h1
    rw [hρx, Matrix.SpecialLinearGroup.coe_one, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h
    have hζ2 : ζ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have hdvd := orderOf_dvd_of_pow_eq_one hζ2
    rw [hζ] at hdvd
    omega
  ·
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hyc
    have hr' : ((δ y ^ (j * (j + 1)) : Ωˣ) : Ω) •
        ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) r := by
      rw [← hρ, ← hr]
    exact hthree y hy3 _ (eq_scalar_of_smul_eq_scalar hr')
  ·
    have hr' : ((δ y ^ (j * (j + 1)) : Ωˣ) : Ω) •
        ((ρ₀ y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) 1 := by
      rw [← hρ, hy, Matrix.SpecialLinearGroup.coe_one, Matrix.scalar_apply, Matrix.diagonal_one]
    exact hcentral y _ (eq_scalar_of_smul_eq_scalar hr') z

end SL3


end Item1118Res3Proof

section KFacts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  Item1118Res3Proof


theorem d4ThreeASL3Model_holds : D4ThreeASL3Model := by
  intro K _ _ q σ hK hσ h3 z hzS hz3 hz1
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := exists_prime_pow_of_card_eq_cube hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact h3 (dvd_pow_self 3 (by omega))
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  have hζ3 := pow_three_of_orderOf hζ
  obtain ⟨ε, j, hqj⟩ : ∃ (ε : ℤ) (j : ℕ),
      (ε = 1 ∧ ℓ ^ f = 3 * j + 1) ∨ (ε = -1 ∧ ℓ ^ f = 3 * j + 2) := by
    have h31 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by omega
    rcases h31 with h | h
    · exact ⟨1, ℓ ^ f / 3, Or.inl ⟨rfl, by omega⟩⟩
    · exact ⟨-1, ℓ ^ f / 3, Or.inr ⟨rfl, by omega⟩⟩
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hqj with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = ε := natCast_eq_eps hqj
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (threeSixN L ε)
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L ε := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓ hf hK hσ hFr hgG hFg' ha
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  have hk : g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ ∈
        adjointGroup TwistTag.D4.tag L :=
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _))
  have hxk : triEmb K σ L x = (g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹) *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          (g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹)⁻¹ := by
    change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  obtain ⟨ρ₀, hρ₀⟩ := exists_isSL3Model_model hℓ hℓ3 hf hK hσ hFr hqj hgG hFg' hζ hx
  subst hc
  obtain ⟨ρ, hρ⟩ := Item1118Res2Proof.isSL3Model_comap (MulAut.conj c) (v := z) hρ₀
  exact ⟨L, inferInstance, ρ, hρ⟩

end KFacts

end CFSG.RankThree.PartTwo.Sec11
