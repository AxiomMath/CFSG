module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
public import CFSG.LieType.SeitzGeneration.Basic
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadicalNode
import CFSG.LieType.SeitzGeneration.Coprime
import CFSG.LieType.SeitzGeneration.UnitaryHyperCenters

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private noncomputable def semiT (A : GL (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) : Fin n → K :=
  (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i)

private theorem semiT_injective (A : GL (Fin n) K) (φ : K ≃+* K) :
    Function.Injective (semiT A φ) :=
  mulVec_map_injective A φ

private theorem semiT_add (A : GL (Fin n) K) (φ : K ≃+* K) (x y : Fin n → K) :
    semiT A φ (x + y) = semiT A φ x + semiT A φ y := by
  simp only [semiT, Pi.add_apply, map_add]
  exact mulVec_add _ _ _

private theorem semiT_sub (A : GL (Fin n) K) (φ : K ≃+* K) (x y : Fin n → K) :
    semiT A φ (x - y) = semiT A φ x - semiT A φ y := by
  simp only [semiT, Pi.sub_apply, map_sub]
  exact mulVec_sub _ _ _

private theorem semiT_smul (A : GL (Fin n) K) (φ : K ≃+* K) (c : K) (v : Fin n → K) :
    semiT A φ (c • v) = φ c • semiT A φ v := by
  have h : (fun i => φ ((c • v) i)) = φ c • (fun i => φ (v i)) := by
    funext i
    simp [map_mul]
  rw [semiT, semiT, h, mulVec_smul]

private noncomputable def semiTinv (A : GL (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) :
    Fin n → K :=
  fun i => φ.symm ((((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) i)

private theorem semiT_semiTinv (A : GL (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) :
    semiT A φ (semiTinv A φ v) = v := by
  funext i
  simp only [semiT, semiTinv]
  have h : (fun j => φ (φ.symm ((((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) j))) =
      (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) :=
    funext fun j => φ.apply_symm_apply _
  rw [h, mulVec_mulVec, ← Units.val_mul, show A * A⁻¹ = 1 from mul_inv_cancel A, Units.val_one,
    one_mulVec]

private theorem semiTinv_semiT (A : GL (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) :
    semiTinv A φ (semiT A φ v) = v := by
  funext i
  simp only [semiT, semiTinv]
  have h : (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i))) =
      fun i => φ (v i) := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [h]
  exact φ.symm_apply_apply _

private theorem map_mulVec_eq (M : Matrix (Fin n) (Fin n) K) (φ : K ≃+* K)
    (v : Fin n → K) :
    (M.map φ) *ᵥ v = fun i => φ ((M *ᵥ fun j => φ.symm (v j)) i) := by
  funext i
  have h := RingHom.map_mulVec (φ : K →+* K) M (fun j => φ.symm (v j)) i
  have h2 : (⇑(φ : K →+* K) ∘ fun j => φ.symm (v j)) = v := by
    funext j
    exact φ.apply_symm_apply _
  rw [h2] at h
  exact h.symm

private theorem gramForm_map_ringEquiv' (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (φ : K ≃+* K) (x y : Fin n → K) :
    φ (gramForm h (C : Matrix (Fin n) (Fin n) K) x y) =
      gramForm h (C : Matrix (Fin n) (Fin n) K) (fun i => φ (x i)) (fun i => φ (y i)) := by
  rw [gramForm_apply, gramForm_apply]
  simp only [dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_bar_comm, show φ (((C : Matrix (Fin n) (Fin n) K) *ᵥ y) a) =
    (φ : K →+* K) (((C : Matrix (Fin n) (Fin n) K) *ᵥ y) a) from rfl, RingHom.map_mulVec,
    hC.map_eq (φ : K →+* K)]
  rfl

private theorem semiT_form (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K) (x y : Fin n → K) :
    gramForm h (C : Matrix (Fin n) (Fin n) K) (semiT (A : GL (Fin n) K) φ x)
        (semiT (A : GL (Fin n) K) φ y) = φ (gramForm h (C : Matrix (Fin n) (Fin n) K) x y) := by
  have hA : (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (C : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (C : Matrix (Fin n) (Fin n) K) := mem_primeFormUnitary.mp A.2
  rw [semiT, semiT, gramForm_mulVec, hA]
  exact (gramForm_map_ringEquiv' h hC φ x y).symm

private theorem isRadicalMatrix_conj' (h : UnitaryFieldData p f K) {G : Matrix (Fin n) (Fin n) K}
    {W : Submodule K (Fin n → K)} {Am Ai gm : Matrix (Fin n) (Fin n) K}
    (hAA : Am * Ai = 1) (φ : K ≃+* K) (hg : IsRadicalMatrix h G W gm)
    (hTW : ∀ v, Am *ᵥ (fun i => φ (v i)) ∈ W ↔ v ∈ W)
    (hTL : ∀ v, Am *ᵥ (fun i => φ (v i)) ∈ W.orthogonalBilin (gramForm h G) ↔
      v ∈ W.orthogonalBilin (gramForm h G)) :
    IsRadicalMatrix h G W (Am * gm.map φ * Ai) := by
  set T : (Fin n → K) → Fin n → K := fun v => Am *ᵥ fun i => φ (v i) with hT
  set T' : (Fin n → K) → Fin n → K := fun v => fun i => φ.symm ((Ai *ᵥ v) i) with hT'
  have hTT' : ∀ v, T (T' v) = v := fun v => by
    simp only [hT, hT', RingEquiv.apply_symm_apply]
    rw [mulVec_mulVec, hAA, one_mulVec]
  have hTsub : ∀ u u', T (u - u') = T u - T u' := fun u u' => by
    simp only [hT, Pi.sub_apply, map_sub]
    rw [← mulVec_sub]
    rfl
  have hX : ∀ v, (Am * gm.map φ * Ai) *ᵥ v = T (gm *ᵥ T' v) := fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    simp only [hT, hT']
    congr 1
    funext i
    rw [show φ ((gm *ᵥ fun i => φ.symm ((Ai *ᵥ v) i)) i) =
      (φ : K →+* K) ((gm *ᵥ fun i => φ.symm ((Ai *ᵥ v) i)) i) from rfl, RingHom.map_mulVec]
    congr 1
    funext j
    exact (φ.apply_symm_apply _).symm
  obtain ⟨g1, g2, g3⟩ := hg
  have hT'W : ∀ v, T' v ∈ W ↔ v ∈ W := fun v => by
    have := hTW (T' v)
    change T (T' v) ∈ W ↔ T' v ∈ W at this
    rw [hTT'] at this
    exact this.symm
  have hT'L : ∀ v, T' v ∈ W.orthogonalBilin (gramForm h G) ↔
      v ∈ W.orthogonalBilin (gramForm h G) := fun v => by
    have := hTL (T' v)
    change T (T' v) ∈ W.orthogonalBilin (gramForm h G) ↔
      T' v ∈ W.orthogonalBilin (gramForm h G) at this
    rw [hTT'] at this
    exact this.symm
  have hsub : ∀ v, T (gm *ᵥ T' v) - v = T (gm *ᵥ T' v - T' v) := fun v => by
    rw [hTsub, hTT']
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [hX, g1 _ ((hT'W w).mpr hw), hTT']
  · rw [hX, hsub]
    exact (hTW _).mpr (g2 _ ((hT'L v).mpr hv))
  · rw [hX, hsub]
    exact (hTL _).mpr (g3 (T' v))

private theorem pow_char_eq_one_of_mem_isotropicRadical (h : UnitaryFieldData p f K)
    (hp : p.Prime) (hp2 : p ≠ 2) {C : Matrix (Fin n) (Fin n) K}
    {W : Submodule K (Fin n → K)} {g : gramSU h C} (hg : g ∈ isotropicRadical h C W) :
    g ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  have : Finite K := h.finite
  have hN : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
    simpa only [pow_three, mul_assoc] using sub_one_pow_three_of_mem_radical hg
  have hchoose : (p.choose 2 : K) = (p : K) * (((p - 1) / 2 : ℕ) : K) := by
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (even_iff_two_dvd.1 (hp.even_sub_one hp2))]
    push_cast
    rfl
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hpow : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    conv_lhs => rw [show ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) by abel]
    rw [unip_pow_of_cube_eq_zero (K := K) hN p, hchoose, hpK, zero_mul, zero_smul, zero_smul,
      add_zero, add_zero]
  refine Subtype.ext (Units.ext ?_)
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  exact hpow

private theorem not_two_dvd_card_isotropicRadical (h : UnitaryFieldData p f K) (hp : p.Prime)
    (hp2 : p ≠ 2) {C : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)} :
    ¬ 2 ∣ Nat.card (isotropicRadical h C W) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  have hP : IsPGroup p (isotropicRadical h C W) := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    refine ⟨1, fun g => ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using pow_char_eq_one_of_mem_isotropicRadical h hp hp2 g.2)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  rw [hm]
  intro hd
  have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm

theorem planeGen_of_stable_isotropic (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W,
      gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0)
    (hWs : ∀ e ∈ E, ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (φ : K ≃+* K), primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
        ⟨A, φ⟩ = e ∧
        ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W) :
    PlaneGen E := by
  classical
  let C : GL (Fin n) K := 1
  have hC : IsPrimeFormGram C := CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hcard : Nat.card K = (p ^ f) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by omega, pow_mul]
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h2
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).1 hdvd |>.resolve_left h.prime.ne_one
    exact hp hp2
  set σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K p f with hσdef
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hcard
  have hform : ∀ x y : Fin n → K, gramForm h (C : Matrix (Fin n) (Fin n) K) x y =
      CFSG.ClassicalGroups.Unitary.herm σ x y := by
    intro x y
    rw [gramForm_apply, CFSG.ClassicalGroups.Unitary.herm]
    simp only [show (C : Matrix (Fin n) (Fin n) K) = 1 from rfl, Matrix.one_mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show h.bar (x i) = σ (x i) from
      (CFSG.LieType.BorelTits.unitaryInvolution_apply (K := K) (p := p) (f := f) (x i)).trans
        (h.bar_apply (x i)).symm]
  have horth : W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) =
      CFSG.RankThree.PartOne.CTP.hermOrth σ W := by
    ext v
    rw [Submodule.mem_orthogonalBilin, CFSG.RankThree.PartOne.CTP.mem_hermOrth]
    exact ⟨fun hv x hx => by rw [← hform x v]; exact hv x hx,
      fun hv x hx => by rw [hform x v]; exact hv x hx⟩
  have hWherm : ∀ x ∈ W, ∀ y ∈ W, CFSG.ClassicalGroups.Unitary.herm σ x y = 0 :=
    fun x hx y hy => by rw [← hform x y]; exact hW x hx y hy
  let A : E → primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) :=
    fun e => Classical.choose (hWs e e.2)
  let φ : E → K ≃+* K := fun e =>
    Classical.choose (Classical.choose_spec (hWs e e.2))
  have hpsi : ∀ e : E, primeFormPsi h hC ⟨A e, φ e⟩ =
      (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) := fun e =>
    (Classical.choose_spec (Classical.choose_spec (hWs e e.2))).1
  have hTW : ∀ e : E, ∀ w ∈ W,
      semiT (A e : GL (Fin n) K) (φ e) w ∈ W := fun e =>
    (Classical.choose_spec (Classical.choose_spec (hWs e e.2))).2
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have : Fintype E := Fintype.ofFinite E
  have hTWiff : ∀ e : E, ∀ v : Fin n → K,
      semiT (A e : GL (Fin n) K) (φ e) v ∈ W ↔ v ∈ W := fun e =>
    mem_iff_of_mapsTo_of_finite (semiT_injective _ _) (hTW e)
  have hTformHerm : ∀ e : E, ∀ x y : Fin n → K,
      CFSG.ClassicalGroups.Unitary.herm σ (semiT (A e : GL (Fin n) K) (φ e) x)
        (semiT (A e : GL (Fin n) K) (φ e) y) = φ e (CFSG.ClassicalGroups.Unitary.herm σ x y) := by
    intro e x y
    rw [← hform (semiT (A e : GL (Fin n) K) (φ e) x)
        (semiT (A e : GL (Fin n) K) (φ e) y),
      semiT_form h hC (A e) (φ e) x y, hform x y]
  have hsurjW : ∀ e : E, ∀ w ∈ W, ∃ x ∈ W, semiT (A e : GL (Fin n) K) (φ e) x = w := by
    intro e w hw
    have hm : Set.MapsTo (semiT (A e : GL (Fin n) K) (φ e)) (W : Set (Fin n → K))
        (W : Set (Fin n → K)) := fun x hx => hTW e x hx
    have hbij := ((Set.toFinite (W : Set (Fin n → K))).injOn_iff_bijOn_of_mapsTo hm).mp
      (semiT_injective _ _).injOn
    exact hbij.surjOn hw
  have hTLmem : ∀ e : E, ∀ v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W,
      semiT (A e : GL (Fin n) K) (φ e) v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W := by
    intro e v hv w hw
    obtain ⟨x, hxW, hxw⟩ := hsurjW e w hw
    rw [← hxw, hTformHerm e x v, hv x hxW, map_zero]
  have hTLiff : ∀ e : E, ∀ v : Fin n → K,
      semiT (A e : GL (Fin n) K) (φ e) v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W ↔
        v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W := fun e =>
    mem_iff_of_mapsTo_of_finite (semiT_injective _ _) (hTLmem e)
  have hcomp : ∀ e f : E, ∃ c : Kˣ, h.norm (c : K) = 1 ∧ φ (e * f) = φ e * φ f ∧
      (A e : GL (Fin n) K) * glAut (φ e) (A f : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c * (A (e * f) : GL (Fin n) K) := by
    intro e f
    let x : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
        (K ≃+* K) := ⟨A e, φ e⟩
    let y : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
        (K ≃+* K) := ⟨A f, φ f⟩
    let z : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
        (K ≃+* K) := ⟨A (e * f), φ (e * f)⟩
    have hx : primeFormPsi h hC x = (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :=
      hpsi e
    have hy : primeFormPsi h hC y = (f : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :=
      hpsi f
    have hz : primeFormPsi h hC z =
        (e * f : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) := hpsi (e * f)
    have h1 : primeFormPsi h hC (x * y * z⁻¹) = 1 := by
      simp only [map_mul, map_inv, hx, hy, hz]
      group
    obtain ⟨hright, c, hc, hcleft⟩ :=
      (primeFormPsi_eq_one_iff h hC hn (x * y * z⁻¹)).mp h1
    have hmemc : GeneralLinearGroup.scalar (Fin n) c ∈
        primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := by
      rw [← hcleft]
      exact (x * y * z⁻¹).left.2
    have hone : (1 : K ≃+* K) = RingEquiv.refl K := by
      ext u
      rfl
    have hpair : x * y * z⁻¹ = (⟨⟨GeneralLinearGroup.scalar (Fin n) c, hmemc⟩,
        (1 : K ≃+* K)⟩ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
          (K ≃+* K)) := by
      refine SemidirectProduct.ext ?_ ?_
      · exact Subtype.ext hcleft
      · rw [hone]
        exact hright
    have hxy : x * y = (⟨⟨GeneralLinearGroup.scalar (Fin n) c, hmemc⟩, (1 : K ≃+* K)⟩ :
        primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
          (K ≃+* K)) * z := by
      rw [← hpair]
      group
    refine ⟨c, hc, ?_, ?_⟩
    · have hr : φ e * φ f * (φ (e * f))⁻¹ = 1 := by
        rw [hone]
        simpa [x, y, z] using hright
      exact (mul_inv_eq_one.mp hr).symm
    · have hleft := congrArg (fun q : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[
          primeFormFieldU h hC] (K ≃+* K) => (q.left : GL (Fin n) K)) hxy
      simpa only [SemidirectProduct.mul_left, Subgroup.coe_mul, coe_primeFormFieldU, map_one,
        MulAut.one_apply, x, y, z] using hleft
  let ρ : E → Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K := fun e M =>
    ((A e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map (φ e) *
      (((A e : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hρ_add : ∀ (e : E) (M M' : Matrix (Fin n) (Fin n) K),
      ρ e (M + M') = ρ e M + ρ e M' := by
    intro e M M'
    simp only [ρ]
    rw [Matrix.map_add (⇑(φ e)) (map_add (φ e)) (M := M) (N := M'), Matrix.mul_add,
      Matrix.add_mul]
  have hρ_smul : ∀ (e : E) (a : K) (M : Matrix (Fin n) (Fin n) K),
      ρ e (a • M) = φ e a • ρ e M := by
    intro e a M
    simp only [ρ]
    rw [Matrix.map_smulₛₗ (⇑(φ e)) (⇑(φ e)) a (fun x => map_mul (φ e) a x) (M := M)]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  have hρ_comp : ∀ (e f : E) (M : Matrix (Fin n) (Fin n) K), ρ e (ρ f M) = ρ (e * f) M := by
    intro e f M
    obtain ⟨c, hc, hφ, hAA⟩ := hcomp e f
    set Ae : Matrix (Fin n) (Fin n) K := ((A e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      with hAedef
    set Af : Matrix (Fin n) (Fin n) K := ((A f : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      with hAfdef
    set Aef : Matrix (Fin n) (Fin n) K := ((A (e * f) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) with hAefdef
    set Aei : Matrix (Fin n) (Fin n) K :=
      (((A e : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAeidef
    set Afi : Matrix (Fin n) (Fin n) K :=
      (((A f : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAfidef
    set Aefi : Matrix (Fin n) (Fin n) K :=
      (((A (e * f) : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAefidef
    set Afe : Matrix (Fin n) (Fin n) K := Af.map (φ e) with hAfedef
    set Afie : Matrix (Fin n) (Fin n) K := Afi.map (φ e) with hAfiedef
    set X : Matrix (Fin n) (Fin n) K := Ae * Afe with hXdef
    set Y : Matrix (Fin n) (Fin n) K := Afie * Aei with hYdef
    set Z : Matrix (Fin n) (Fin n) K := (c : K)⁻¹ • Aefi with hZdef
    have hAeAei : Ae * Aei = 1 := by
      rw [hAedef, hAeidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hAeiAe : Aei * Ae = 1 := by
      rw [hAedef, hAeidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hAfeAfie : Afe * Afie = 1 := by
      rw [hAfedef, hAfiedef, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact Matrix.map_one (⇑(φ e)) (map_zero (φ e)) (map_one (φ e))
    have hAfieAfe : Afie * Afe = 1 := by
      rw [hAfedef, hAfiedef, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      exact Matrix.map_one (⇑(φ e)) (map_zero (φ e)) (map_one (φ e))
    have hX : X = (c : K) • Aef := by
      rw [hXdef, hAfedef, hAedef, hAfdef, hAefdef]
      have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hAA
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h
      rw [show Matrix.scalar (Fin n) (c : K) =
        (c : K) • (1 : Matrix (Fin n) (Fin n) K) from
        (Matrix.smul_one_eq_diagonal (c : K)).symm, Matrix.smul_mul, Matrix.one_mul] at h
      simpa only [Units.val_mul, coe_glAut] using h
    have hYX : Y * X = 1 := by
      rw [hYdef, hXdef]
      calc Afie * Aei * (Ae * Afe) = Afie * (Aei * Ae) * Afe := by noncomm_ring
        _ = Afie * 1 * Afe := by rw [hAeiAe]
        _ = Afie * Afe := by noncomm_ring
        _ = 1 := hAfieAfe
    have hXZ : X * Z = 1 := by
      rw [hX, hZdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [show ((c : K) * (c : K)⁻¹) = 1 from mul_inv_cancel₀ (Units.ne_zero c), one_smul]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hYeqZ : Y = Z := by
      calc Y = Y * 1 := (mul_one Y).symm
        _ = Y * (X * Z) := by rw [hXZ]
        _ = (Y * X) * Z := by rw [← mul_assoc]
        _ = 1 * Z := by rw [hYX]
        _ = Z := one_mul Z
    have hmapmap : (M.map (φ f)).map (φ e) = M.map (φ (e * f)) := by
      rw [show φ (e * f) = φ e * φ f from hφ]
      ext i j
      rfl
    simp only [ρ, Matrix.map_mul]
    rw [hmapmap]
    have hL : ((A e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((((A f : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (φ e)) *
          M.map (φ (e * f)) *
          ((((A f : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map
            (φ e)))) *
        (((A e : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        X * M.map (φ (e * f)) * Y := by
      rw [← hAedef, ← hAfdef, ← hAeidef, ← hAfidef, ← hAfedef, ← hAfiedef, hXdef, hYdef]
      noncomm_ring
    rw [hL, hYeqZ, hX, hZdef]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show ((c : K)⁻¹ * (c : K)) = 1 from inv_mul_cancel₀ (Units.ne_zero c), one_smul]
  let Wp : Submodule K (Fin n → K) := CFSG.RankThree.PartOne.CTP.hermOrth σ W
  obtain ⟨D, hD⟩ : ∃ D : Submodule K (Fin n → K), IsCompl Wp D := exists_isCompl Wp
  let π₀ : (Fin n → K) →ₗ[K] (Fin n → K) := Wp.projection D hD
  let M₀ : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' π₀
  have hM₀ : ∀ v : Fin n → K, M₀ *ᵥ v = π₀ v := fun v => LinearMap.toMatrix'_mulVec π₀ v
  have hπ₀ : ∀ v : Fin n → K, π₀ v ∈ Wp := fun v => Submodule.projection_apply_mem hD v
  have hπ₀id : ∀ v ∈ Wp, π₀ v = v := fun v hv => Submodule.projection_apply_of_mem_left hD hv
  let N : Matrix (Fin n) (Fin n) K := (4 : K)⁻¹ • ∑ e : E, ρ e M₀
  have hρN : ∀ e : E, ρ e N = N := by
    intro e
    have hsum : ∑ f : E, ρ (e * f) M₀ = ∑ f : E, ρ f M₀ :=
      Fintype.sum_bijective (fun f : E => e * f) (Equiv.mulLeft e).bijective
        (fun f => ρ (e * f) M₀) (fun f => ρ f M₀) (fun f => rfl)
    have hsum' : ∀ s : Finset E, ρ e (s.sum (fun f => ρ f M₀)) =
        s.sum (fun f => ρ (e * f) M₀) := by
      intro s
      induction s using Finset.induction with
      | empty => simp [ρ]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hρ_add, hρ_comp, ih]
    have hsum'' : ρ e (∑ f : E, ρ f M₀) = ∑ f : E, ρ f M₀ := by
      rw [show (∑ f : E, ρ f M₀) = (Finset.univ : Finset E).sum (fun f => ρ f M₀) from rfl,
        hsum', hsum]
    have h4 : φ e ((4 : K)⁻¹) = (4 : K)⁻¹ := by
      rw [map_inv₀, show φ e (4 : K) = 4 from map_ofNat (φ e) 4]
    simp only [N]
    rw [hρ_smul, hsum'', h4]
  have hρ_apply : ∀ (e : E) (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
      (ρ e M) *ᵥ v = semiT (A e : GL (Fin n) K) (φ e)
        (M *ᵥ semiTinv (A e : GL (Fin n) K) (φ e) v) := by
    intro e M v
    simp only [ρ, semiT]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    congr 1
    exact map_mulVec_eq M (φ e) ((((A e : GL (Fin n) K)⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v)
  have h4K : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2K h2K
  have hN_apply : ∀ v : Fin n → K,
      N *ᵥ v = (4 : K)⁻¹ • ∑ e : E, (ρ e M₀) *ᵥ v := by
    intro v
    simp only [N]
    rw [Matrix.smul_mulVec]
    congr 1
    exact Matrix.sum_mulVec Finset.univ (fun e => ρ e M₀) v
  have hTinv_mem : ∀ (e : E) {v : Fin n → K}, v ∈ Wp →
      semiTinv (A e : GL (Fin n) K) (φ e) v ∈ Wp := by
    intro e v hv
    exact (hTLiff e (semiTinv (A e : GL (Fin n) K) (φ e) v)).mp (by
      rw [semiT_semiTinv]
      exact hv)
  have hρ_mem : ∀ (e : E) (v : Fin n → K), (ρ e M₀) *ᵥ v ∈ Wp := by
    intro e v
    rw [hρ_apply]
    exact hTLmem e _ (by rw [hM₀]; exact hπ₀ _)
  have hρ_fix : ∀ (e : E) {v : Fin n → K}, v ∈ Wp → (ρ e M₀) *ᵥ v = v := by
    intro e v hv
    rw [hρ_apply]
    have h1 : semiTinv (A e : GL (Fin n) K) (φ e) v ∈ Wp := hTinv_mem e hv
    rw [hM₀, hπ₀id _ h1, semiT_semiTinv]
  have hNfix : ∀ v ∈ Wp, N *ᵥ v = v := by
    intro v hv
    rw [hN_apply]
    have hsum : ∑ e : E, (ρ e M₀) *ᵥ v = (4 : K) • v := by
      rw [Finset.sum_congr rfl (fun e _ => hρ_fix e hv), Finset.sum_const,
        Finset.card_univ, ← Nat.card_eq_fintype_card, h4]
      ext i
      simp
    rw [hsum, smul_smul, show (4 : K)⁻¹ * 4 = 1 from inv_mul_cancel₀ h4K, one_smul]
  have hNmem : ∀ v : Fin n → K, N *ᵥ v ∈ Wp := by
    intro v
    rw [hN_apply]
    exact Wp.smul_mem _ (Wp.sum_mem fun e _ => hρ_mem e v)
  let C₀ : Submodule K (Fin n → K) := LinearMap.ker (Matrix.toLin' N)
  have hC₀mem : ∀ v : Fin n → K, v ∈ C₀ ↔ N *ᵥ v = 0 := by
    intro v
    simp only [C₀, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hC₀compl : IsCompl Wp C₀ := by
    have hdisj : Disjoint Wp C₀ := by
      rw [disjoint_iff, Submodule.eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      have h1 : N *ᵥ v = v := hNfix v hv.1
      rw [(hC₀mem v).mp hv.2] at h1
      exact h1.symm
    refine ⟨hdisj, ?_⟩
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hmem : N *ᵥ v ∈ Wp := hNmem v
    have hker : v - N *ᵥ v ∈ C₀ := by
      rw [hC₀mem, Matrix.mulVec_sub, hNfix _ hmem, sub_self]
    have hv : N *ᵥ v + (v - N *ᵥ v) = v := by abel
    rw [← hv]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right hker)
  have hC₀stab : ∀ (e : E) {v : Fin n → K}, v ∈ C₀ →
      semiT (A e : GL (Fin n) K) (φ e) v ∈ C₀ := by
    intro e v hv
    rw [hC₀mem] at hv ⊢
    have hρ : (ρ e N) *ᵥ semiT (A e : GL (Fin n) K) (φ e) v =
        semiT (A e : GL (Fin n) K) (φ e) (N *ᵥ v) := by
      rw [hρ_apply, semiTinv_semiT]
    rw [hρN e, hv] at hρ
    rw [hρ]
    simp only [semiT, Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero ((A e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hWP : ∀ w ∈ W, w ∈ Wp := fun w hw x hx => by rw [← hform x w]; exact hW x hx w hw
  let C₀p : Submodule K (Fin n → K) := CFSG.RankThree.PartOne.CTP.hermOrth σ C₀
  have hTC₀p : ∀ (e : E) {z : Fin n → K}, z ∈ C₀p → semiT (A e : GL (Fin n) K) (φ e) z ∈ C₀p := by
    intro e z hz c hc
    obtain ⟨c', hc', rfl⟩ : ∃ c' ∈ C₀, semiT (A e : GL (Fin n) K) (φ e) c' = c := by
      have hm : Set.MapsTo (semiT (A e : GL (Fin n) K) (φ e)) (C₀ : Set (Fin n → K))
          (C₀ : Set (Fin n → K)) := fun x hx => hC₀stab e hx
      have hbij := ((Set.toFinite (C₀ : Set (Fin n → K))).injOn_iff_bijOn_of_mapsTo hm).mp
        (semiT_injective _ _).injOn
      exact hbij.surjOn hc
    rw [hTformHerm e c' z, hz c' hc', map_zero]
  have hsurjC₀ : ∀ (e : E) (c : Fin n → K), c ∈ C₀ →
      ∃ c' ∈ C₀, semiT (A e : GL (Fin n) K) (φ e) c' = c := by
    intro e c hc
    have hm : Set.MapsTo (semiT (A e : GL (Fin n) K) (φ e)) (C₀ : Set (Fin n → K))
        (C₀ : Set (Fin n → K)) := fun x hx => hC₀stab e hx
    have hbij := ((Set.toFinite (C₀ : Set (Fin n → K))).injOn_iff_bijOn_of_mapsTo hm).mp
      (semiT_injective _ _).injOn
    exact hbij.surjOn hc
  have hWC : IsCompl W C₀p := by
    have hfin1 := CFSG.RankThree.PartOne.CTP.finrank_hermOrth_add σ hσ.invol W
    have hfin2 := CFSG.RankThree.PartOne.CTP.finrank_hermOrth_add σ hσ.invol C₀
    have hfin3 : Module.finrank K Wp + Module.finrank K C₀ = n := by
      simpa [Wp] using Submodule.finrank_add_eq_of_isCompl hC₀compl
    have hdisj : Disjoint W C₀p := by
      rw [Submodule.disjoint_def]
      intro w hw hwC
      refine CFSG.ClassicalGroups.Unitary.eq_zero_of_herm σ fun y => ?_
      have hy : y ∈ Wp ⊔ C₀ := by rw [hC₀compl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
      rw [CFSG.ClassicalGroups.Unitary.herm_add_right, hu w hw,
        CFSG.ClassicalGroups.Unitary.herm_eq_zero_comm σ hσ.invol (hwC c hc), add_zero]
    have hfin3' : Module.finrank K (CFSG.RankThree.PartOne.CTP.hermOrth σ W) +
        Module.finrank K C₀ = n := by simpa [Wp] using hfin3
    refine (Submodule.isCompl_iff_disjoint W C₀p ?_).2 hdisj
    simp only [Module.finrank_fin_fun, C₀p]
    omega
  let P : (Fin n → K) →ₗ[K] (Fin n → K) := W.projection C₀p hWC
  have hP1 : ∀ v, P v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hP2 : ∀ v, v - P v ∈ C₀p := fun v => Submodule.sub_projection_mem hWC v
  have hPW : ∀ w ∈ W, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  have hPC : ∀ z ∈ C₀p, P z = 0 := fun z hz =>
    Submodule.projection_apply_of_mem_right hWC hz
  have hPg : ∀ (e : E) (v : Fin n → K),
      P (semiT (A e : GL (Fin n) K) (φ e) v) =
        semiT (A e : GL (Fin n) K) (φ e) (P v) := by
    intro e v
    have hv : semiT (A e : GL (Fin n) K) (φ e) v =
        semiT (A e : GL (Fin n) K) (φ e) (P v) +
          semiT (A e : GL (Fin n) K) (φ e) (v - P v) := by
      rw [← semiT_add, add_sub_cancel]
    rw [hv, map_add, hPW _ (hTW e _ (hP1 v)), hPC _ (hTC₀p e (hP2 v)), add_zero]
  have hcc : ∀ c₁ ∈ C₀, ∀ c₂ ∈ C₀,
      CFSG.ClassicalGroups.Unitary.herm σ c₁ (P c₂) =
        CFSG.ClassicalGroups.Unitary.herm σ c₁ c₂ := by
    intro c₁ hc₁ c₂ _
    have := hP2 c₂ c₁ hc₁
    rw [CFSG.ClassicalGroups.Unitary.herm_sub_right, sub_eq_zero] at this
    exact this.symm
  let κ : K := (2 : K)⁻¹
  have hσκ : σ κ = κ := by
    simp only [κ, map_inv₀, show σ (2 : K) = 2 from map_ofNat σ 2]
  have hκ : κ + σ κ = 1 := by
    rw [hσκ]
    show (2 : K)⁻¹ + (2 : K)⁻¹ = 1
    rw [← two_mul, mul_inv_cancel₀ h2K]
  have hφκ : ∀ e : E, φ e κ = κ := by
    intro e
    simp only [κ, map_inv₀, show φ e (2 : K) = 2 from map_ofNat (φ e) 2]
  let W' : Submodule K (Fin n → K) := C₀.map (LinearMap.id - κ • P)
  have hW'iso : ∀ x ∈ W', ∀ y ∈ W', CFSG.ClassicalGroups.Unitary.herm σ x y = 0 := by
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    have e1 := hcc c₁ hc₁ c₂ hc₂
    have e2 : CFSG.ClassicalGroups.Unitary.herm σ (P c₁) c₂ =
        CFSG.ClassicalGroups.Unitary.herm σ c₁ c₂ := by
      rw [CFSG.ClassicalGroups.Unitary.herm_conj σ hσ.invol c₂ (P c₁),
        hcc c₂ hc₂ c₁ hc₁, ← CFSG.ClassicalGroups.Unitary.herm_conj σ hσ.invol c₂ c₁]
    have e3 := hWherm _ (hP1 c₁) _ (hP1 c₂)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      CFSG.ClassicalGroups.Unitary.herm_sub_left,
      CFSG.ClassicalGroups.Unitary.herm_sub_right,
      CFSG.ClassicalGroups.Unitary.herm_smul_left,
      CFSG.ClassicalGroups.Unitary.herm_smul_right, e1, e2, e3]
    linear_combination (-(CFSG.ClassicalGroups.Unitary.herm σ c₁ c₂)) * hκ
  have hW'compl : IsCompl Wp W' := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      rintro x ⟨hx, c, hc, rfl⟩
      have hcP : c ∈ Wp := by
        have h1 : c = (c - κ • P c) + κ • P c := by abel
        rw [h1]
        exact Wp.add_mem (by simpa using hx) (Wp.smul_mem _ (hWP _ (hP1 c)))
      have hc0 : c = 0 := Submodule.disjoint_def.1 hC₀compl.disjoint c hcP hc
      simp [hc0]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ Wp ⊔ C₀ := by rw [hC₀compl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
      refine Submodule.mem_sup.2 ⟨u + κ • P c, ?_, c - κ • P c, ⟨c, hc, rfl⟩, by abel⟩
      exact Wp.add_mem hu (Wp.smul_mem _ (hWP _ (hP1 c)))
  have hW'stab : ∀ e : E, ∀ w ∈ W', semiT (A e : GL (Fin n) K) (φ e) w ∈ W' := by
    rintro e _ ⟨c, hc, rfl⟩
    refine ⟨semiT (A e : GL (Fin n) K) (φ e) c, hC₀stab e hc, ?_⟩
    change semiT (A e : GL (Fin n) K) (φ e) c - κ • P (semiT (A e : GL (Fin n) K) (φ e) c) =
      semiT (A e : GL (Fin n) K) (φ e) (c - κ • P c)
    rw [semiT_sub, semiT_smul, hφκ e, ← hPg e c]
  let π : gramSU h (C : Matrix (Fin n) (Fin n) K) →*
      primeFormP h (C : Matrix (Fin n) (Fin n) K) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let QW : Subgroup (primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
    (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W).map π
  let QW' : Subgroup (primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
    (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W').map π
  have hW'surj : ∀ (e : E) (w : Fin n → K), w ∈ W' →
      ∃ x ∈ W', semiT (A e : GL (Fin n) K) (φ e) x = w := by
    intro e w hw
    have hm : Set.MapsTo (semiT (A e : GL (Fin n) K) (φ e)) (W' : Set (Fin n → K))
        (W' : Set (Fin n → K)) := fun x hx => hW'stab e x hx
    have hbij := ((Set.toFinite (W' : Set (Fin n → K))).injOn_iff_bijOn_of_mapsTo hm).mp
      (semiT_injective _ _).injOn
    exact hbij.surjOn hw
  have hW'po : W'.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) =
      CFSG.RankThree.PartOne.CTP.hermOrth σ W' := by
    ext v
    rw [Submodule.mem_orthogonalBilin, CFSG.RankThree.PartOne.CTP.mem_hermOrth]
    exact ⟨fun hv x hx => by rw [← hform x v]; exact hv x hx,
      fun hv x hx => by rw [hform x v]; exact hv x hx⟩
  have hW'TLmem : ∀ (e : E) (v : Fin n → K),
      v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W' →
        semiT (A e : GL (Fin n) K) (φ e) v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W' := by
    intro e v hv w hw
    obtain ⟨x, hxW, hxw⟩ := hW'surj e w hw
    rw [← hxw, hTformHerm e x v, hv x hxW, map_zero]
  have hW'TLiff : ∀ (e : E) (v : Fin n → K),
      semiT (A e : GL (Fin n) K) (φ e) v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W' ↔
        v ∈ CFSG.RankThree.PartOne.CTP.hermOrth σ W' := fun e =>
    mem_iff_of_mapsTo_of_finite (semiT_injective _ _) (hW'TLmem e)
  have hWiff' : ∀ (e : E) (v : Fin n → K),
      semiT (A e : GL (Fin n) K) (φ e) v ∈ W ↔ v ∈ W := fun e =>
    mem_iff_of_mapsTo_of_finite (semiT_injective _ _) (hTW e)
  have hWLiff' : ∀ (e : E) (v : Fin n → K),
      semiT (A e : GL (Fin n) K) (φ e) v ∈
        W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) ↔
        v ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) := by
    intro e v
    rw [horth]
    exact hTLiff e v
  have hW'Liff' : ∀ (e : E) (v : Fin n → K),
      semiT (A e : GL (Fin n) K) (φ e) v ∈
        W'.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) ↔
        v ∈ W'.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) := by
    intro e v
    rw [hW'po]
    exact hW'TLiff e v
  have hQle : ∀ {X : Submodule K (Fin n → K)}
      (hXiff : ∀ e : E, ∀ v : Fin n → K,
        semiT (A e : GL (Fin n) K) (φ e) v ∈ X ↔ v ∈ X)
      (hXLiff : ∀ e : E, ∀ v : Fin n → K,
        semiT (A e : GL (Fin n) K) (φ e) v ∈
          X.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) ↔
          v ∈ X.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))),
      ∀ e : E,
        ((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π).map
            (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom ≤
          (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π := by
    intro X hXiff hXLiff e
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hq
    have hAA : ((A e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((A e : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hSU : ((A e : GL (Fin n) K) * glAut (φ e) (g : GL (Fin n) K) *
        (A e : GL (Fin n) K)⁻¹) ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) :=
      conj_mem_gramSU h (C : Matrix (Fin n) (Fin n) K) (A e).2
        (glAut_mem_gramSU h hC (φ e) g.2)
    have hrad : IsRadicalMatrix h (C : Matrix (Fin n) (Fin n) K) X
        (((A e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (φ e)) *
          (((A e : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      isRadicalMatrix_conj' h hAA (φ e) (mem_isotropicRadical.mp hg) (hXiff e) (hXLiff e)
    have hx : (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (π g) =
        π (⟨(A e : GL (Fin n) K) * glAut (φ e) (g : GL (Fin n) K) *
          (A e : GL (Fin n) K)⁻¹, hSU⟩ : gramSU h (C : Matrix (Fin n) (Fin n) K)) := by
      rw [← hpsi e, primeFormPsi_apply]
      change (primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) (A e))
        ((primeFormFieldHom h hC (φ e)) (π g)) = _
      have h1 : primeFormFieldHom h hC (φ e) (π g) =
          ((⟨glAut (φ e) (g : GL (Fin n) K),
            glAut_mem_gramSU h hC (φ e) g.2⟩ : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
              primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
        primeFormFieldAut_mk h hC (φ e) g
      rw [h1, primeFormConjHom_mk]
      rfl
    change ((e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (π g)) ∈
      (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π
    rw [hx]
    exact Subgroup.mem_map_of_mem π (mem_isotropicRadical.mpr hrad)
  have hQinv : ∀ {X : Submodule K (Fin n → K)}
      (hXiff : ∀ e : E, ∀ v : Fin n → K,
        semiT (A e : GL (Fin n) K) (φ e) v ∈ X ↔ v ∈ X)
      (hXLiff : ∀ e : E, ∀ v : Fin n → K,
        semiT (A e : GL (Fin n) K) (φ e) v ∈
          X.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) ↔
          v ∈ X.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))),
      ∀ e : E,
        ((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π).map
            (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom =
          (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π := by
    intro X hXiff hXLiff e
    refine le_antisymm (hQle hXiff hXLiff e) ?_
    have h1 := hQle hXiff hXLiff (e⁻¹ : E)
    have hcomp : ((e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom).comp
        ((e⁻¹ : E) : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    have hmap : (((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π).map
        ((e⁻¹ : E) : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom).map
          (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom =
        (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π := by
      rw [Subgroup.map_map, hcomp]
      simp
    calc (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π
        = (((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π).map
            ((e⁻¹ : E) : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom).map
              (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom :=
          hmap.symm
      _ ≤ ((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π).map
            (e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).toMonoidHom :=
          Subgroup.map_mono h1
  have hQodd : ∀ X : Submodule K (Fin n → K),
      ¬ 2 ∣ Nat.card ((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) X).map π) := by
    intro X hd
    exact not_two_dvd_card_isotropicRadical h h.prime hp (C := (C : Matrix (Fin n) (Fin n) K))
      (W := X) (hd.trans (Subgroup.card_map_dvd _ π))
  have hW'iff : ∀ e : E, ∀ v : Fin n → K,
      semiT (A e : GL (Fin n) K) (φ e) v ∈ W' ↔ v ∈ W' := fun e =>
    mem_iff_of_mapsTo_of_finite (semiT_injective _ _) (hW'stab e)
  have hQWeq : ∀ e ∈ E, QW.map e.toMonoidHom = QW := by
    intro e he
    simpa [QW] using hQinv hWiff' hWLiff' (⟨e, he⟩ : E)
  have hQW'eq : ∀ e ∈ E, QW'.map e.toMonoidHom = QW' := by
    intro e he
    simpa [QW'] using hQinv hW'iff hW'Liff' (⟨e, he⟩ : E)
  have hcardE : 2 ^ 2 ≤ Nat.card E := by rw [h4]; norm_num
  have hQWle : QW ≤ planeClosure E :=
    le_planeClosure_of_invariant_coprime (p := 2) hE hcardE hQWeq (hQodd W)
  have hQW'le : QW' ≤ planeClosure E :=
    le_planeClosure_of_invariant_coprime (p := 2) hE hcardE hQW'eq (hQodd W')
  have hq2 : p ^ f ≠ 2 := by
    intro h2
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have hpf : p ≤ p ^ f := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) h.one_le
    omega
  have hSUeq : CFSG.LieType.Universal.Unitary.SUid σ n =
      gramSU h (C : Matrix (Fin n) (Fin n) K) := by
    have hCmat : ((C : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := rfl
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hcard n, hCmat,
      ← unitarySU_eq_gramSU h n]
  let eSU : CFSG.LieType.Universal.Unitary.SUid σ n ≃*
      gramSU h (C : Matrix (Fin n) (Fin n) K) := MulEquiv.subgroupCongr hSUeq
  let πc : CFSG.LieType.Universal.Unitary.SUid σ n →*
      primeFormP h (C : Matrix (Fin n) (Fin n) K) := π.comp eSU.toMonoidHom
  let H : Subgroup (CFSG.LieType.Universal.Unitary.SUid σ n) := (planeClosure E).comap πc
  have hgW : ∀ g : CFSG.LieType.Universal.Unitary.SUid σ n,
      g ∈ uRad σ W hWherm → πc g ∈ planeClosure E := by
    intro g hg
    have hcoe : ((eSU g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [show (eSU g : GL (Fin n) K) = (g : GL (Fin n) K) from
        MulEquiv.subgroupCongr_apply hSUeq g]
    have hR : eSU g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W := by
      rw [mem_isotropicRadical]
      obtain ⟨h1, h2, h3⟩ := hg
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        simpa only [hcoe, CFSG.ClassicalGroups.Unitary.smul_def] using h3 w hw
      · intro v hv
        rw [horth] at hv
        simpa only [hcoe, CFSG.ClassicalGroups.Unitary.smul_def] using h2 v hv
      · intro v
        rw [horth]
        simpa only [hcoe, CFSG.ClassicalGroups.Unitary.smul_def] using h1 v
    have := hQWle (Subgroup.mem_map_of_mem π hR)
    simpa [πc, H] using this
  have hgW' : ∀ g : CFSG.LieType.Universal.Unitary.SUid σ n,
      g ∈ uRad σ W' hW'iso → πc g ∈ planeClosure E := by
    intro g hg
    have hcoe : ((eSU g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [show (eSU g : GL (Fin n) K) = (g : GL (Fin n) K) from
        MulEquiv.subgroupCongr_apply hSUeq g]
    have hR : eSU g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W' := by
      rw [mem_isotropicRadical]
      obtain ⟨h1, h2, h3⟩ := hg
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        simpa only [hcoe, CFSG.ClassicalGroups.Unitary.smul_def] using h3 w hw
      · intro v hv
        rw [hW'po] at hv
        simpa only [hcoe, CFSG.ClassicalGroups.Unitary.smul_def] using h2 v hv
      · intro v
        rw [hW'po]
        simpa only [hcoe, CFSG.ClassicalGroups.Unitary.smul_def] using h1 v
    have := hQW'le (Subgroup.mem_map_of_mem π hR)
    simpa [πc, H] using this
  have hH : H = ⊤ := by
    refine eq_top_of_uRad_of_opposite hσ (by omega) ?_ hW0 hWherm hW'iso hW'compl ?_ ?_
    · intro _
      obtain ⟨s, hs0, hs⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hcard hq2
      exact ⟨s, hs0, hs⟩
    · intro g hg
      rw [Subgroup.mem_comap]
      exact hgW g hg
    · intro g hg
      rw [Subgroup.mem_comap]
      exact hgW' g hg
  have hplane : planeClosure E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxH : ∀ g : CFSG.LieType.Universal.Unitary.SUid σ n, g ∈ H := fun g => by
      rw [hH]
      exact Subgroup.mem_top g
    obtain ⟨g₀, rfl⟩ := hπsurj x
    obtain ⟨g, rfl⟩ := eSU.surjective g₀
    exact Subgroup.mem_comap.mp (hxH g)
  exact hplane

end CFSG.LocalAnalysis.WeakClosure81.UOuter
