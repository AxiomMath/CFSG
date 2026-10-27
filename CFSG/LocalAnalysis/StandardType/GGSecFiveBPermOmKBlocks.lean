module


public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.KLinearOmega
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
public import CFSG.Assembly.ComponentFreeOddCores
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Timmesfeld.ClassicalOrders

variable {G : Type} [Group G] {p n m f : ℕ} [Fact p.Prime] {F K : Type} [Field F] [Field K]
  [Algebra F K] [Finite K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 f))
variable {Bs X : Subgroup G} {y : G}
variable {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
variable {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}

private theorem normQuad_mul (x y : K) :
    normQuad E (x * y) = normQuad E x * normQuad E y := by
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad,
    map_mul (algebraMap F K) (normQuad E x) (normQuad E y),
    algebraMap_normQuad, algebraMap_normQuad, map_mul (unitaryInvolution K 2 f) x y]
  ring

private noncomputable def diagF (c : Fin m → Kˣ) : (Fin m → K) ≃ₗ[F] (Fin m → K) where
  toFun x i := (c i : K) * x i
  invFun x i := ((c i : K))⁻¹ * x i
  left_inv x := by
    funext i
    change ((c i : K))⁻¹ * ((c i : K) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero (c i)), one_mul]
  right_inv x := by
    funext i
    change (c i : K) * (((c i : K))⁻¹ * x i) = x i
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (c i)), one_mul]
  map_add' x y := by
    funext i
    change (c i : K) * (x i + y i) = (c i : K) * x i + (c i : K) * y i
    rw [mul_add]
  map_smul' a x := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, RingHom.id_apply]
    simp only [Algebra.smul_def]
    ring

omit [Finite K] [CharP K 2] in
private theorem diagF_apply (c : Fin m → Kˣ) (x : Fin m → K) :
    diagF (F := F) c x = fun i => (c i : K) * x i := rfl

omit [Finite K] [CharP K 2] in
private theorem diagF_kLinear (c : Fin m → Kˣ) (a : K) (x : Fin m → K) :
    diagF (F := F) c (a • x) = a • diagF (F := F) c x := by
  funext i
  simp only [diagF_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem diagF_mem_orthogonalGroup (c : Fin m → Kˣ)
    (hc : ∀ i, normQuad E (c i : K) = 1) :
    diagF (F := F) c ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E m) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [Qn_apply, Qn_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagF_apply, normQuad_mul, hc i, one_mul]

private noncomputable def diagV (c : Fin m → Kˣ) :
    ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) :=
  hypExt (K := F) (W := Fin m → K) (diagF (F := F) c)

omit [Finite K] [CharP K 2] in
private theorem diagV_apply (c : Fin m → Kˣ) (p : (F × F) × (Fin m → K)) :
    diagV (F := F) (K := K) c p = (p.1, fun i => (c i : K) * p.2 i) := by
  rw [diagV, hypExt_apply, diagF_apply]

private theorem diagV_mem_normOmega (hm : 2 ≤ m) (c : Fin m → Kˣ)
    (hc : ∀ i, normQuad E (c i : K) = 1) : diagV (F := F) (K := K) c ∈ normOmega E m :=
  hypExt_mem_orthDerived_of_kLinear E hm
    (diagF_mem_orthogonalGroup E c hc) (diagF_kLinear (F := F) c)

private noncomputable def omDiag (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v : Fin m → Multiplicative (ZMod p)) : normOmega E m :=
  ⟨diagV (F := F) (K := K) (fun i => χ (v i)),
    diagV_mem_normOmega (E := E) hm _ (fun i => hχ (v i))⟩

private noncomputable def omFrameT
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (b : ↥Bs) : normOmega E m :=
  Classical.choose (hκ.2.2.2 b)

private theorem omFrameT_apply
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (b : ↥Bs)
    (v : (F × F) × (Fin m → K)) :
    ((omFrameT E hκ b : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
      (v.1, fun i => (χ (eta b (π i.castSucc)) : K) * v.2 i) :=
  (Classical.choose_spec (hκ.2.2.2 b)).1 v

private theorem omFrameT_conj
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (b : ↥Bs) (s : normOmega E m) :
    (b : G) * κ s * (b : G)⁻¹ =
      κ (omFrameT E hκ b * s * (omFrameT E hκ b)⁻¹) :=
  (Classical.choose_spec (hκ.2.2.2 b)).2 s

private theorem omDiag_apply (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v : Fin m → Multiplicative (ZMod p)) (p : (F × F) × (Fin m → K)) :
    ((omDiag (E := E) (χ := χ) hm hχ v : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) p =
      (p.1, fun i => (χ (v i) : K) * p.2 i) := by
  change diagV (F := F) (K := K) (fun i => χ (v i)) p = _
  rw [diagV_apply]

private theorem omFrameT_eq_omDiag (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (b : ↥Bs) :
    omFrameT E hκ b = omDiag (E := E) (χ := χ) hm hχ
      (fun i => eta b (π i.castSucc)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [omFrameT_apply, omDiag_apply]

private theorem omDiag_commute (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v w : Fin m → Multiplicative (ZMod p)) :
    omDiag (E := E) (χ := χ) hm hχ v * omDiag (E := E) (χ := χ) hm hχ w =
      omDiag (E := E) (χ := χ) hm hχ w * omDiag (E := E) (χ := χ) hm hχ v := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro q
  rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [omDiag_apply]
  congr 1
  funext i
  ring

omit [Finite K] [CharP K 2] in
private theorem diagV_pow_apply (c : Fin m → Kˣ) (n : ℕ)
    (p : (F × F) × (Fin m → K)) :
    ((diagV (F := F) (K := K) c ^ n) p) =
      (p.1, fun i => ((c i : K) ^ n) * p.2 i) := by
  induction n generalizing p with
  | zero =>
      simp only [pow_zero]
      ext <;> simp
  | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, ih, diagV_apply]
      refine Prod.ext rfl ?_
      funext i
      change ↑(c i) ^ n * (↑(c i) * p.2 i) = ↑(c i) ^ (n + 1) * p.2 i
      rw [pow_succ]
      ring

private theorem omDiag_pow_eq_one (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v : Fin m → Multiplicative (ZMod p)) :
    (omDiag (E := E) (χ := χ) hm hχ v) ^ p = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro q
  change ((diagV (F := F) (K := K) (fun i => χ (v i))) ^ p) q = q
  rw [diagV_pow_apply]
  have hv : ∀ i, (χ (v i) : K) ^ p = 1 := by
    intro i
    have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by
      rw [Fintype.card_multiplicative, ZMod.card]
    have hvp : v i ^ p = 1 := by
      simpa [hcard] using pow_card_eq_one (x := v i)
    have h1 : χ (v i) ^ p = 1 := by rw [← map_pow, hvp, map_one]
    simpa using congrArg (fun u : Kˣ => (u : K)) h1
  ext <;> simp [hv]

private theorem normQuad_chi
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (i : Fin m)
    (a : Multiplicative (ZMod p)) : normQuad E (χ a : K) = 1 := by
  classical
  let b : ↥Bs := eta.symm (Pi.mulSingle (π i.castSucc) a)
  let T : normOmega E m := omFrameT E hκ b
  obtain ⟨y, hy⟩ := normQuad_surjective E (1 : F)
  let p : (F × F) × (Fin m → K) := ((0, 0), Pi.single i y)
  have hT : (T : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
    Subgroup.commutator_le_self _ T.2
  have hcoord : ∀ j : Fin m, eta b (π j.castSucc) = if j = i then a else 1 := by
    intro j
    dsimp only [b]
    rw [MulEquiv.apply_symm_apply]
    by_cases hji : j = i
    · subst hji; simp
    · rw [Pi.mulSingle_eq_of_ne]
      · simp [hji]
      · intro h
        exact hji (Fin.castSucc_injective m (π.injective h))
  have hQp : normHypForm E m p = 1 := by
    simp only [p, normHypForm, hypSum_apply, Qn_apply,
      zero_mul, zero_add]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, hy]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      exact QuadraticMap.map_zero (normQuad E)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hTp : (T : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) p = ((0, 0), Pi.single i ((χ a : K) * y)) := by
    rw [omFrameT_apply]
    refine Prod.ext rfl ?_
    funext j
    change (χ (eta b (π j.castSucc)) : K) * p.2 j =
      (Pi.single i ((χ a : K) * y) : Fin m → K) j
    rw [hcoord j]
    by_cases hji : j = i <;> simp [p, hji]
  have hQtp : normHypForm E m ((T : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) p) = normQuad E ((χ a : K) * y) := by
    rw [hTp]
    simp only [normHypForm, hypSum_apply, Qn_apply,
      zero_mul, zero_add]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      exact QuadraticMap.map_zero (normQuad E)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hiso := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hT) p
  have h1 : normQuad E ((χ a : K) * y) = 1 := by
    rw [← hQtp, hiso, hQp]
  rw [normQuad_mul, hy, mul_one] at h1
  exact h1

private theorem omDiag_kappa_mem_Bs (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (v : Fin m → Multiplicative (ZMod p)) :
    κ (omDiag (E := E) (χ := χ) hm hχ v) ∈ Bs := by
  apply hBs
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    let D : normOmega E m := omDiag (E := E) (χ := χ) hm hχ v
    let b' : ↥Bs := ⟨b, hb⟩
    let T' : normOmega E m := omFrameT E hκ b'
    have hfr := omFrameT_conj E hκ b' D
    have hTb := omFrameT_eq_omDiag (E := E) (χ := χ) hm hχ hκ b'
    have hcomm := omDiag_commute (E := E) (χ := χ) hm hχ
      (fun i => eta b' (π i.castSucc)) v
    have harg : T' * D * T'⁻¹ = D := by
      change omFrameT E hκ b' * D * (omFrameT E hκ b')⁻¹ = D
      rw [hTb, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hfr' : b * κ D * b⁻¹ = κ D := by
      rw [hfr, harg]
    change b * κ D = κ D * b
    calc b * κ D = (b * κ D * b⁻¹) * b := by group
      _ = κ D * b := by rw [hfr']
  · rw [← map_pow, omDiag_pow_eq_one, map_one]

private theorem omDiag_coord (hm : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (v : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    eta ⟨κ (omDiag (E := E) (χ := χ) hm hχ v),
      omDiag_kappa_mem_Bs (E := E) (χ := χ) hm hχ hκ hBs v⟩ (π i.castSucc) = v i := by
  classical
  let D : normOmega E m := omDiag (E := E) (χ := χ) hm hχ v
  let b : ↥Bs := ⟨κ D, omDiag_kappa_mem_Bs (E := E) (χ := χ) hm hχ hκ hBs v⟩
  let T' : normOmega E m := omFrameT E hκ b
  have hcenter : D⁻¹ * T' ∈ Subgroup.center ↥(normOmega E m) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 := omFrameT_conj E hκ b s
    have h2 : (b : G) = κ D := rfl
    rw [h2] at h1
    have h1' : κ (D * s * D⁻¹) = κ (T' * s * T'⁻¹) := by
      simpa only [map_mul, map_inv] using h1
    have hEq : D * s * D⁻¹ = T' * s * T'⁻¹ := hκ.1 h1'
    calc s * (D⁻¹ * T') = D⁻¹ * (D * s * D⁻¹) * T' := by group
      _ = D⁻¹ * (T' * s * T'⁻¹) * T' := by rw [hEq]
      _ = (D⁻¹ * T') * s := by group
  have hD : D⁻¹ * T' = 1 := by
    have hbot := center_normOmega_eq_bot (E := E) hm
    exact Subgroup.mem_bot.mp (hbot ▸ hcenter)
  have hT' : T' = D := by
    calc T' = D * (D⁻¹ * T') := by group
      _ = D := by rw [hD, mul_one]
  let q : (F × F) × (Fin m → K) := ((0, 0), Pi.single i (1 : K))
  have h1 := congrArg (fun e : normOmega E m =>
    (e : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q) hT'
  rw [omFrameT_apply, omDiag_apply] at h1
  have h2 := congrFun (congrArg Prod.snd h1) i
  simp only [q, Pi.single_eq_same, mul_one] at h2
  exact hκ.2.2.1 (Units.ext h2)

private theorem omk_coe_mem_ggBsCoordZeroOn {S : Set (Fin n)} {b : ↥Bs} :
    (b : G) ∈ ggBsCoordZeroOn Bs eta S ↔ ∀ c ∈ S, eta b c = 1 :=
  mem_ggBsCoordZeroOn.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨b.2, h⟩⟩

private theorem omDiag_apply_of_fixes (hm2 : 2 ≤ m) {k : ℕ} (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v : Fin m → Multiplicative (ZMod p))
    (hv : ∀ i : Fin k, v (Fin.castLE hkm.le i) = 1)
    (q : (F × F) × (Fin m → K)) :
    ((omDiag (E := E) (χ := χ) hm2 hχ v : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q =
      (q.1, fun j : Fin m =>
        if _hj : (j : ℕ) < k then q.2 j else (χ (v j) : K) * q.2 j) := by
  rw [omDiag_apply]
  refine Prod.ext rfl ?_
  funext j
  by_cases hj : (j : ℕ) < k
  · have hvj : v j = 1 := by
      have h : Fin.castLE hkm.le ⟨(j : ℕ), hj⟩ = j := Fin.ext rfl
      rw [← h]
      exact hv ⟨(j : ℕ), hj⟩
    simp only [dif_pos hj, hvj, map_one, Units.val_one, one_mul]
  · simp only [dif_neg hj]

private theorem normOmegaCast_apply_of {k : ℕ} (hkm : k < m) (a : normOmega E k)
    (q : (F × F) × (Fin m → K)) :
    ((normOmegaCast E hkm.le a : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q =
      (((a : ((F × F) × (Fin k → K)) ≃ₗ[F]
          ((F × F) × (Fin k → K))) (castRestr hkm.le q)).1,
        fun j : Fin m => if hj : (j : ℕ) < k then
          ((a : ((F × F) × (Fin k → K)) ≃ₗ[F]
            ((F × F) × (Fin k → K))) (castRestr hkm.le q)).2 ⟨(j : ℕ), hj⟩
          else q.2 j) := by
  rw [normOmegaCast_apply, castEquiv_apply, castLin_apply]
  rfl

private theorem castRestr_omDiag_eq (hm2 : 2 ≤ m) {k : ℕ} (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v : Fin m → Multiplicative (ZMod p))
    (hv : ∀ i : Fin k, v (Fin.castLE hkm.le i) = 1)
    (q : (F × F) × (Fin m → K)) :
    castRestr hkm.le
      (((omDiag (E := E) (χ := χ) hm2 hχ v : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q) =
      castRestr hkm.le q := by
  apply Prod.ext
  · rfl
  · funext i
    change (((omDiag (E := E) (χ := χ) hm2 hχ v : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q).2
        (Fin.castLE hkm.le i) = q.2 (Fin.castLE hkm.le i)
    have h := congrFun (congrArg Prod.snd
      (omDiag_apply_of_fixes (E := E) (χ := χ) hm2 hkm hχ v hv q))
      (Fin.castLE hkm.le i)
    rw [h]
    have hi : ((Fin.castLE hkm.le i).val) < k := by simp
    simp only [dif_pos hi]

private theorem omDiag_mul_normOmegaCast_comm (hm2 : 2 ≤ m) {k : ℕ} (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (v : Fin m → Multiplicative (ZMod p))
    (hv : ∀ i : Fin k, v (Fin.castLE hkm.le i) = 1) (a : normOmega E k) :
    omDiag (E := E) (χ := χ) hm2 hχ v * normOmegaCast E hkm.le a =
      normOmegaCast E hkm.le a * omDiag (E := E) (χ := χ) hm2 hχ v := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro q
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, omDiag_apply, normOmegaCast_apply,
    castEquiv_apply, castLin_apply]
  have hcast : castRestr hkm.le (q.1, fun i => (χ (v i) : K) * q.2 i) =
      castRestr hkm.le q := by
    apply Prod.ext
    · rfl
    · funext i
      change (χ (v (Fin.castLE hkm.le i)) : K) * q.2 (Fin.castLE hkm.le i) =
        q.2 (Fin.castLE hkm.le i)
      rw [hv i, map_one, Units.val_one, one_mul]
  rw [hcast]
  refine Prod.ext rfl ?_
  funext i
  by_cases hi : (i : ℕ) < k
  · have hv_i : v i = 1 := by
      have h : Fin.castLE hkm.le ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
      rw [← h]
      exact hv ⟨(i : ℕ), hi⟩
    simp only [dif_pos hi, hv_i, map_one, Units.val_one, one_mul]
  · simp only [dif_neg hi]

private theorem omDiag_eq_normOmegaCast (hm2 : 2 ≤ m) {k : ℕ} (hk2 : 2 ≤ k)
    (hkm : k < m) (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    {v : Fin m → Multiplicative (ZMod p)}
    (hv : ∀ j : Fin m, k ≤ (j : ℕ) → v j = 1) :
    omDiag (E := E) (χ := χ) hm2 hχ v =
      normOmegaCast E hkm.le
        (omDiag (m := k) (E := E) (χ := χ) hk2 hχ
          (fun i => v (Fin.castLE hkm.le i))) := by
  let a0 : normOmega E k := omDiag (m := k) (E := E) (χ := χ) hk2 hχ
    (fun i => v (Fin.castLE hkm.le i))
  change omDiag (E := E) (χ := χ) hm2 hχ v = normOmegaCast E hkm.le a0
  apply Subtype.ext
  apply LinearEquiv.ext
  intro q
  rw [omDiag_apply, normOmegaCast_apply, castEquiv_apply, castLin_apply]
  refine Prod.ext rfl ?_
  funext j
  by_cases hj : (j : ℕ) < k
  · change (χ (v j) : K) * q.2 j =
      (if hj : (j : ℕ) < k then
        ((a0 : ((F × F) × (Fin k → K)) ≃ₗ[F]
          ((F × F) × (Fin k → K))) (castRestr hkm.le q)).2 ⟨(j : ℕ), hj⟩
       else q.2 j)
    rw [dif_pos hj]
    change (χ (v j) : K) * q.2 j =
      (χ (v (Fin.castLE hkm.le ⟨(j : ℕ), hj⟩)) : K) *
        (castRestr hkm.le q).2 ⟨(j : ℕ), hj⟩
    have hck : v (Fin.castLE hkm.le ⟨(j : ℕ), hj⟩) = v j := by
      congr 1
    rw [hck]
    have hrestr : (castRestr hkm.le q).2 ⟨(j : ℕ), hj⟩ = q.2 j := by
      congr 1
    rw [hrestr]
  · change (χ (v j) : K) * q.2 j =
      (if hj : (j : ℕ) < k then
        ((a0 : ((F × F) × (Fin k → K)) ≃ₗ[F]
          ((F × F) × (Fin k → K))) (castRestr hkm.le q)).2 ⟨(j : ℕ), hj⟩
       else q.2 j)
    rw [dif_neg hj]
    have hvj : v j = 1 := hv j (by omega)
    simp only [hvj, map_one, Units.val_one, one_mul]

private theorem omK_gen {k : ℕ} (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    ∀ b : ↥Bs, ∃ h ∈ ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)),
      ∃ w ∈ Bs ⊓ ((normOmegaCast E hkm.le).range.map κ), (b : G) = h * w := by
  classical
  intro b
  let v : Fin m → Multiplicative (ZMod p) :=
    fun j => if hj : (j : ℕ) < k then eta b (π j.castSucc) else 1
  let D : normOmega E m := omDiag (E := E) (χ := χ) hm2 hχ v
  let w : G := κ D
  have hwB : w ∈ Bs := omDiag_kappa_mem_Bs (E := E) (χ := χ) hm2 hχ hκ hBs v
  let ck : Fin k → Multiplicative (ZMod p) := fun i => v (Fin.castLE hkm.le i)
  let a0 : normOmega E k := omDiag (m := k) (E := E) (χ := χ) hk2 hχ ck
  have hD : D = normOmegaCast E hkm.le a0 :=
    omDiag_eq_normOmegaCast (E := E) (χ := χ) hm2 hk2 hkm hχ
      (v := v) (fun j hj => by
        have hjk : ¬ (j : ℕ) < k := by omega
        simp only [v, dif_neg hjk])
  have hwR : w ∈ (normOmegaCast E hkm.le).range.map κ := by
    refine Subgroup.mem_map.mpr ⟨normOmegaCast E hkm.le a0, ?_, ?_⟩
    · exact ⟨a0, rfl⟩
    · rw [← hD]
  refine ⟨(b : G) * w⁻¹, ?_, w, ⟨hwB, hwR⟩, by group⟩
  have hhB : (b : G) * w⁻¹ ∈ Bs := Bs.mul_mem b.2 (Bs.inv_mem hwB)
  change ((⟨(b : G) * w⁻¹, hhB⟩ : ↥Bs) : G) ∈
    ggBsCoordZeroOn Bs eta
      (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))
  rw [omk_coe_mem_ggBsCoordZeroOn]
  intro c hc
  obtain ⟨i, rfl⟩ := hc
  have hidx : (Fin.castLE hkm.le i).castSucc =
      (Fin.castLE (by omega : k ≤ m + 1) i : Fin (m + 1)) := Fin.ext rfl
  have hwcoord : eta ⟨w, hwB⟩ (π (Fin.castLE (by omega : k ≤ m + 1) i)) =
      v (Fin.castLE hkm.le i) := by
    rw [← hidx]
    exact omDiag_coord (E := E) (χ := χ) hm2 hχ hκ hBs v (Fin.castLE hkm.le i)
  have hv : v (Fin.castLE hkm.le i) =
      eta b (π (Fin.castLE (by omega : k ≤ m + 1) i)) := by
    have hi : ((Fin.castLE hkm.le i).val) < k := by simp
    simp only [v, dif_pos hi]
    rw [hidx]
  have hh_eq : (⟨(b : G) * w⁻¹, hhB⟩ : ↥Bs) = b * ⟨w, hwB⟩⁻¹ := Subtype.ext rfl
  calc eta ⟨(b : G) * w⁻¹, hhB⟩ (π (Fin.castLE (by omega : k ≤ m + 1) i))
      = eta (b * ⟨w, hwB⟩⁻¹) (π (Fin.castLE (by omega : k ≤ m + 1) i)) := by
        rw [hh_eq]
    _ = eta b (π (Fin.castLE (by omega : k ≤ m + 1) i)) *
          (eta ⟨w, hwB⟩ (π (Fin.castLE (by omega : k ≤ m + 1) i)))⁻¹ := by
        rw [map_mul, map_inv]
        rfl
    _ = eta b (π (Fin.castLE (by omega : k ≤ m + 1) i)) *
          (v (Fin.castLE hkm.le i))⁻¹ := by rw [hwcoord]
    _ = eta b (π (Fin.castLE (by omega : k ≤ m + 1) i)) *
          (eta b (π (Fin.castLE (by omega : k ≤ m + 1) i)))⁻¹ := by rw [hv]
    _ = 1 := mul_inv_cancel _

private theorem range_normOmegaCast_le_centralizer (hm2 : 2 ≤ m) {k : ℕ} (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) :
    (normOmegaCast E hkm.le).range.map κ ≤
      Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G) := by
  rintro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨a, ⟨a0, ha0⟩, hax⟩ := Subgroup.mem_map.mp hx
  rw [← ha0] at hax
  rw [← hax]
  have hhB : h ∈ Bs := ggBsCoordZeroOn_le Bs eta _ hh
  let b' : ↥Bs := ⟨h, hhB⟩
  let v : Fin m → Multiplicative (ZMod p) := fun j => eta b' (π j.castSucc)
  have hhS : ∀ i : Fin k,
      eta b' (π (Fin.castLE (by omega : k ≤ m + 1) i)) = 1 := by
    intro i
    exact (omk_coe_mem_ggBsCoordZeroOn (S := Set.range fun i : Fin k =>
      π (Fin.castLE (by omega : k ≤ m + 1) i)) (b := b')).mp hh _ ⟨i, rfl⟩
  have hv : ∀ i : Fin k, v (Fin.castLE hkm.le i) = 1 := by
    intro i
    have hidx : (Fin.castLE hkm.le i).castSucc =
        (Fin.castLE (by omega : k ≤ m + 1) i : Fin (m + 1)) := Fin.ext rfl
    change eta b' (π (Fin.castLE hkm.le i).castSucc) = 1
    rw [hidx]
    exact hhS i
  let D : normOmega E m := omDiag (E := E) (χ := χ) hm2 hχ v
  let C : normOmega E m := normOmegaCast E hkm.le a0
  have hTb : omFrameT E hκ b' = D := omFrameT_eq_omDiag (E := E) (χ := χ) hm2 hχ hκ b'
  have hcomm : D * C = C * D :=
    omDiag_mul_normOmegaCast_comm (E := E) (χ := χ) hm2 hkm hχ v hv a0
  have hfr := omFrameT_conj E hκ b' C
  have harg : D * C * D⁻¹ = C := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfr' : (b' : G) * κ C * (b' : G)⁻¹ = κ C := by
    rw [hfr]
    rw [hTb, harg]
  change h * κ C = κ C * h
  calc h * κ C = (h * κ C * h⁻¹) * h := by group
    _ = κ C * h := by rw [hfr']

private theorem range_perfect {k : ℕ} (hk2 : 2 ≤ k) (hkm : k < m)
    (_hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hsimp : IsSimpleGroup ↥(normOmega E k)) :
    (normOmegaCast E hkm.le).range.map κ =
      ⁅(normOmegaCast E hkm.le).range.map κ, (normOmegaCast E hkm.le).range.map κ⁆ := by
  let φ : normOmega E k →* G := κ.comp (normOmegaCast E hkm.le)
  have hR : (normOmegaCast E hkm.le).range.map κ = φ.range :=
    (MonoidHom.range_comp κ (normOmegaCast E hkm.le)).symm
  have hinj : Function.Injective φ := hκ.1.comp (normOmegaCast_injective E hkm.le)
  let e : ↥(normOmega E k) ≃* ↥φ.range := MonoidHom.ofInjective hinj
  have hsR : IsSimpleGroup ↥φ.range := MulEquiv.isSimpleGroup e.symm
  have hcenterR : Subgroup.center ↥φ.range = ⊥ := by
    have hZ : Subgroup.center ↥(normOmega E k) = ⊥ := center_normOmega_eq_bot E hk2
    have he := Subgroup.map_center_eq e
    rw [hZ, Subgroup.map_bot] at he
    exact he.symm
  have hnonab : ∃ a b : ↥φ.range, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥φ.range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact (h x y).symm
    rw [hcenterR] at htop
    have hall : ∀ x : ↥φ.range, x = 1 := by
      intro x
      exact (Subgroup.eq_bot_iff_forall (⊤ : Subgroup ↥φ.range)).mp htop.symm x
        (Subgroup.mem_top x)
    have : Subsingleton ↥φ.range := ⟨fun x y => by rw [hall x, hall y]⟩
    exact not_subsingleton ↥φ.range inferInstance
  have hperfR : Group.IsPerfect ↥φ.range :=
    Group.isPerfect_def.mpr (CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hnonab)
  have hperf : φ.range = ⁅φ.range, φ.range⁆ := Subgroup.commutator_eq_self.symm
  rw [hR]
  exact hperf

private theorem omk_normalizer_commutator_of_normalizer {A : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (A : Set G)) :
    c ∈ Subgroup.normalizer (⁅A, A⁆ : Subgroup G) := by
  have hmap : (⁅A, A⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom = ⁅A, A⁆ := by
    rw [Subgroup.map_commutator,
      CFSG.LocalAnalysis.ComponentInitial.map_conj_eq_of_mem_normalizer hc]
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  have hh := Subgroup.mem_map_equiv (f := MulAut.conj c) (K := (⁅A, A⁆ : Subgroup G)) (x := h)
  rw [hmap] at hh
  simpa [MulAut.conj_symm_apply] using hh

private theorem omFrameT_coord_eq_one (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hyB : y ∈ Bs)
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    (i : Fin m) :
    eta ⟨y, hyB⟩ (π i.castSucc) = 1 := by
  classical
  let b : ↥Bs := ⟨y, hyB⟩
  let T : normOmega E m := omFrameT E hκ b
  have hyX : ∀ s : normOmega E m, (y : G) * κ s * y⁻¹ = κ s := by
    intro s
    have hs : κ s ∈ X := by rw [← hκ.2.1]; exact ⟨s, rfl⟩
    have hyc : κ s * y = y * κ s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hX.1 hs)
    calc y * κ s * y⁻¹ = (κ s * y) * y⁻¹ := by rw [hyc]
      _ = κ s := mul_inv_cancel_right _ _
  have hcent : T ∈ Subgroup.center ↥(normOmega E m) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 := omFrameT_conj E hκ b s
    rw [hyX s] at h1
    have h2 : T * s * T⁻¹ = s := (hκ.1 h1).symm
    calc s * T = (T * s * T⁻¹) * T := by rw [h2]
      _ = T * s := by group
  have hT1 : T = 1 := by
    have hbot := center_normOmega_eq_bot (E := E) hm2
    exact Subgroup.mem_bot.mp (hbot ▸ hcent)
  have hTd : omDiag (E := E) (χ := χ) hm2 hχ
      (fun j => eta b (π j.castSucc)) = 1 := by
    rw [← omFrameT_eq_omDiag (E := E) (χ := χ) hm2 hχ hκ b]
    exact hT1
  let q : (F × F) × (Fin m → K) := ((0, 0), Pi.single i (1 : K))
  have h := congrArg (fun e : normOmega E m =>
    (e : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) q) hTd
  have hone : ((1 : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q = q := by simp
  rw [hone] at h
  rw [omDiag_apply] at h
  have h2 := congrFun (congrArg Prod.snd h) i
  change (χ (eta b (π i.castSucc)) : K) * q.2 i = q.2 i at h2
  simp only [q, Pi.single_eq_same, mul_one] at h2
  have h2' : (χ (eta b (π i.castSucc)) : K) = 1 := h2
  exact hκ.2.2.1 (by simpa [b] using h2')

private theorem y_mem_H (hm2 : 2 ≤ m) {k : ℕ} (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hyB : y ∈ Bs)
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G))) :
    y ∈ ggBsCoordZeroOn Bs eta
      (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) := by
  change ((⟨y, hyB⟩ : ↥Bs) : G) ∈ ggBsCoordZeroOn Bs eta
    (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))
  rw [omk_coe_mem_ggBsCoordZeroOn]
  intro c hc
  obtain ⟨i, rfl⟩ := hc
  change eta ⟨y, hyB⟩ (π (Fin.castLE (by omega : k ≤ m + 1) i)) = 1
  have hidx : (Fin.castLE hkm.le i).castSucc =
      (Fin.castLE (by omega : k ≤ m + 1) i : Fin (m + 1)) := Fin.ext rfl
  rw [← hidx]
  exact omFrameT_coord_eq_one (E := E) (χ := χ) hm2 hχ hκ hyB hX (Fin.castLE hkm.le i)

private theorem omDiag_single_ne_one (hm2 : 2 ≤ m) {i : Fin m}
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hinj : Function.Injective χ)
    (a : Multiplicative (ZMod p)) (ha : a ≠ 1) :
    omDiag (E := E) (χ := χ) hm2 hχ
      (Pi.mulSingle i a) ≠ 1 := by
  intro hD1
  let q : (F × F) × (Fin m → K) := ((0, 0), Pi.single i (1 : K))
  have h := congrArg (fun e : normOmega E m =>
    (e : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) q) hD1
  have hone : ((1 : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q = q := by simp
  rw [hone] at h
  rw [omDiag_apply] at h
  have h2 := congrFun (congrArg Prod.snd h) i
  change (χ (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod p)) i a i) : K) *
    q.2 i = q.2 i at h2
  rw [Pi.mulSingle_eq_same] at h2
  simp only [q, Pi.single_eq_same, mul_one] at h2
  exact ha (hinj (Units.ext (by simpa using h2)))

private theorem centralizer_le_normalizer_commutator [Finite G] (hm2 : 2 ≤ m) {k : ℕ} (_hk2 : 2 ≤ k)
    (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs)
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G))) :
    Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G) ≤
      Subgroup.normalizer (⁅X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
          (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G),
        X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
          (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G)⁆ :
            Subgroup G) := by
  classical
  let H : Subgroup G := ggBsCoordZeroOn Bs eta
    (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let M : Subgroup G := X ⊓ C
  let N : Subgroup G := ⁅M, M⁆
  have hyH : y ∈ H :=
    y_mem_H (E := E) (χ := χ) hm2 hkm hχ hκ hyB hX
  let i0 : Fin m := ⟨k, hkm⟩
  let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have ha_ne : a ≠ 1 := by
    intro ha
    have h0 : Multiplicative.ofAdd (0 : ZMod p) = 1 := rfl
    have h10 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (ha.trans h0.symm)
    exact one_ne_zero h10
  let v : Fin m → Multiplicative (ZMod p) := Pi.mulSingle i0 a
  let D : normOmega E m := omDiag (E := E) (χ := χ) hm2 hχ v
  have hDne : D ≠ 1 :=
    omDiag_single_ne_one (E := E) (χ := χ) hm2 hχ hκ.2.2.1 a ha_ne
  have hDnc : D ∉ Subgroup.center ↥(normOmega E m) := by
    intro hc
    exact hDne (Subgroup.mem_bot.mp (center_normOmega_eq_bot (E := E) hm2 ▸ hc))
  have hex : ∃ s : normOmega E m, s * D ≠ D * s := by
    by_contra h
    push Not at h
    exact hDnc (by rw [Subgroup.mem_center_iff]; intro s; exact h s)
  obtain ⟨s, hs⟩ := hex
  have hrB : κ D ∈ Bs :=
    omDiag_kappa_mem_Bs (E := E) (χ := χ) hm2 hχ hκ hBs v
  have hrH : κ D ∈ H := by
    change ((⟨κ D, hrB⟩ : ↥Bs) : G) ∈ H
    rw [omk_coe_mem_ggBsCoordZeroOn]
    intro c hc
    obtain ⟨i, rfl⟩ := hc
    change eta ⟨κ D, hrB⟩ (π (Fin.castLE (by omega : k ≤ m + 1) i)) = 1
    have hidx : (Fin.castLE hkm.le i).castSucc =
        (Fin.castLE (by omega : k ≤ m + 1) i : Fin (m + 1)) := Fin.ext rfl
    rw [← hidx]
    have hp : (⟨κ D, hrB⟩ : ↥Bs) =
        ⟨κ D, omDiag_kappa_mem_Bs (E := E) (χ := χ) hm2 hχ hκ hBs v⟩ :=
      Subtype.ext rfl
    rw [hp]
    rw [omDiag_coord (E := E) (χ := χ) hm2 hχ hκ hBs v (Fin.castLE hkm.le i)]
    have hne : Fin.castLE hkm.le i ≠ i0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [i0, Fin.val_castLE] at hv
      omega
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Multiplicative (ZMod p)) hne a
  have hrC : κ D ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhB : h ∈ Bs := ggBsCoordZeroOn_le Bs eta _ hh
    let b' : ↥Bs := ⟨h, hhB⟩
    let vh : Fin m → Multiplicative (ZMod p) := fun i => eta b' (π i.castSucc)
    let T : normOmega E m := omFrameT E hκ b'
    have hTb : T = omDiag (E := E) (χ := χ) hm2 hχ vh :=
      omFrameT_eq_omDiag (E := E) (χ := χ) hm2 hχ hκ b'
    have hcomm : T * D = D * T := by
      rw [hTb]
      exact omDiag_commute (E := E) (χ := χ) hm2 hχ vh v
    have hfr := omFrameT_conj E hκ b' D
    have harg : T * D * T⁻¹ = D := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hfr' : h * κ D * h⁻¹ = κ D := by
      rw [hfr]
      change κ (T * D * T⁻¹) = κ D
      rw [harg]
    calc h * κ D = (h * κ D * h⁻¹) * h := by group
      _ = κ D * h := by rw [hfr']
  have hrX : κ D ∈ X := by
    rw [← hκ.2.1]
    exact ⟨D, rfl⟩
  have hrnotcent : κ D ∉ Subgroup.centralizer (X : Set G) := by
    intro hcent
    have hsX : κ s ∈ X := by rw [← hκ.2.1]; exact ⟨s, rfl⟩
    have hcomm : κ s * κ D = κ D * κ s :=
      Subgroup.mem_centralizer_iff.mp hcent (κ s) hsX
    apply hs
    apply hκ.1
    rw [map_mul, map_mul]
    exact hcomm
  have hrM : κ D ∈ M := ⟨hrX, hrC⟩
  have hCy : C ≤ Subgroup.centralizer ({y} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc y hyH).symm
  have hCnormX : C ≤ Subgroup.normalizer (X : Set G) := by
    intro c hc
    exact ggMem_normalizer_of_component (CFSG.Assembly.isComponentOf_iff_open.mpr hX)
      hrX hrnotcent (Subgroup.le_normalizer (hCy hc))
      (Subgroup.mem_centralizer_iff.mp hc (κ D) hrH).symm
  have hCnormM : C ≤ Subgroup.normalizer (M : Set G) :=
    (le_inf hCnormX Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  intro c hc
  exact omk_normalizer_commutator_of_normalizer (hCnormM hc)

private theorem W_ne_bot (hm2 : 2 ≤ m) {k : ℕ} (hk2 : 2 ≤ k) (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    Bs ⊓ ((normOmegaCast E hkm.le).range.map κ) ≠ ⊥ := by
  classical
  let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have ha_ne : a ≠ 1 := by
    intro ha
    have h0 : Multiplicative.ofAdd (0 : ZMod p) = 1 := rfl
    have h10 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (ha.trans h0.symm)
    exact one_ne_zero h10
  let j0 : Fin m := ⟨0, by omega⟩
  let v : Fin m → Multiplicative (ZMod p) := Pi.mulSingle j0 a
  have hv : ∀ j : Fin m, k ≤ (j : ℕ) → v j = 1 := by
    intro j hj
    have hj0 : j ≠ j0 := by
      intro h
      subst h
      simp only [j0] at hj
      omega
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Multiplicative (ZMod p)) hj0 a
  let D : normOmega E m := omDiag (E := E) (χ := χ) hm2 hχ v
  let a0 : normOmega E k := omDiag (m := k) (E := E) (χ := χ) hk2 hχ
    (fun i => v (Fin.castLE hkm.le i))
  have hD : D = normOmegaCast E hkm.le a0 :=
    omDiag_eq_normOmegaCast (E := E) (χ := χ) hm2 hk2 hkm hχ (v := v) hv
  let w : G := κ D
  have hwB : w ∈ Bs := omDiag_kappa_mem_Bs (E := E) (χ := χ) hm2 hχ hκ hBs v
  have hwR : w ∈ (normOmegaCast E hkm.le).range.map κ := by
    refine Subgroup.mem_map.mpr ⟨normOmegaCast E hkm.le a0, ?_, ?_⟩
    · exact ⟨a0, rfl⟩
    · rw [← hD]
  have hw1 : w ≠ 1 := by
    intro hw
    have hD1 : D = 1 := by
      apply hκ.1
      change w = κ 1
      rw [hw, map_one]
    let q : (F × F) × (Fin m → K) := ((0, 0), Pi.single j0 (1 : K))
    have h := congrArg (fun e : normOmega E m =>
      (e : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) q) hD1
    rw [omDiag_apply] at h
    have h2 := congrFun (congrArg Prod.snd h) j0
    simp only [q, Pi.single_eq_same, mul_one] at h2
    have hva : v j0 = a := by
      simp only [v, Pi.mulSingle_eq_same]
    have hχ1 : χ a = 1 := by
      rw [← hva]
      exact Units.ext h2
    exact ha_ne (hκ.2.2.1 (by simpa using hχ1))
  intro hbot
  have hwbot : w ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hwB, hwR⟩
  exact hw1 (Subgroup.mem_bot.mp hwbot)

set_option linter.unusedSectionVars false in
private theorem range_map_isSimpleGroup {k : ℕ} (hkm : k < m)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hsimp : IsSimpleGroup ↥(normOmega E k)) :
    IsSimpleGroup ↥((normOmegaCast E hkm.le).range.map κ) := by
  let φ : normOmega E k →* G := κ.comp (normOmegaCast E hkm.le)
  have hR : (normOmegaCast E hkm.le).range.map κ = φ.range :=
    (MonoidHom.range_comp κ (normOmegaCast E hkm.le)).symm
  rw [hR]
  let e : ↥(normOmega E k) ≃* ↥φ.range :=
    MonoidHom.ofInjective (hκ.1.comp (normOmegaCast_injective E hkm.le))
  exact MulEquiv.isSimpleGroup e.symm

set_option linter.unusedSectionVars false in
private theorem range_map_center_eq_bot {k : ℕ} (hk2 : 2 ≤ k) (hkm : k < m)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) :
    Subgroup.center ↥((normOmegaCast E hkm.le).range.map κ) = ⊥ := by
  let φ : normOmega E k →* G := κ.comp (normOmegaCast E hkm.le)
  have hR : (normOmegaCast E hkm.le).range.map κ = φ.range :=
    (MonoidHom.range_comp κ (normOmegaCast E hkm.le)).symm
  rw [hR]
  let e : ↥(normOmega E k) ≃* ↥φ.range :=
    MonoidHom.ofInjective (hκ.1.comp (normOmegaCast_injective E hkm.le))
  have hZ : Subgroup.center ↥(normOmega E k) = ⊥ := center_normOmega_eq_bot E hk2
  have he := Subgroup.map_center_eq e
  rw [hZ, Subgroup.map_bot] at he
  exact he.symm

private theorem range_le_commutator_W (hm2 : 2 ≤ m) {k : ℕ} (hk2 : 2 ≤ k) (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hsimp : IsSimpleGroup ↥(normOmega E k)) :
    (normOmegaCast E hkm.le).range.map κ ≤
      ⁅(normOmegaCast E hkm.le).range.map κ,
        Bs ⊓ ((normOmegaCast E hkm.le).range.map κ)⁆ := by
  let R : Subgroup G := (normOmegaCast E hkm.le).range.map κ
  let W : Subgroup G := Bs ⊓ R
  have hWR : W ≤ R := inf_le_right
  have : IsSimpleGroup ↥R := range_map_isSimpleGroup (E := E) (χ := χ) hkm hκ hsimp
  have hcenter : Subgroup.center ↥R = ⊥ :=
    range_map_center_eq_bot (E := E) (χ := χ) hk2 hkm hκ
  have hWne : W ≠ ⊥ := W_ne_bot (E := E) (χ := χ) hm2 hk2 hkm hχ hκ hBs
  exact le_commutator_of_isSimpleGroup_of_ne_bot hWR hcenter hWne

private theorem W_le_commutator (hm2 : 2 ≤ m) {k : ℕ} (hk2 : 2 ≤ k) (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hsimp : IsSimpleGroup ↥(normOmega E k)) :
    Bs ⊓ ((normOmegaCast E hkm.le).range.map κ) ≤
      ⁅X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
          (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G),
        X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
          (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G)⁆ := by
  let H : Subgroup G := ggBsCoordZeroOn Bs eta
    (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let M : Subgroup G := X ⊓ C
  let R : Subgroup G := (normOmegaCast E hkm.le).range.map κ
  have hRX : R ≤ X := by
    rw [← hκ.2.1]
    exact Subgroup.map_le_range κ _
  have hRC : R ≤ C := range_normOmegaCast_le_centralizer (E := E) (χ := χ) hm2 hkm hχ hκ
  have hRM : R ≤ M := le_inf hRX hRC
  have hRperf : R = ⁅R, R⁆ := range_perfect (E := E) (χ := χ) hk2 hkm hχ hκ hsimp
  intro x hx
  have hxR : x ∈ R := hx.2
  have hxRR : x ∈ ⁅R, R⁆ := by rw [← hRperf]; exact hxR
  exact Subgroup.commutator_mono hRM hRM hxRR

private theorem exists_add_algebraMap_mul_of_notMem (E : QuadExt F K (unitaryInvolution K 2 f))
    (ω : K) (hω : ω ∉ Set.range (algebraMap F K)) :
    ∀ c : K, ∃ a b : F, c = algebraMap F K a + algebraMap F K b * ω := by
  have hli : LinearIndependent F ![algebraMap F K (1 : F), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : algebraMap F K s + algebraMap F K t * ω = 0 := by
      simpa only [Algebra.smul_def, map_one, mul_one] using hst
    have ht : t = 0 := by
      by_contra ht
      apply hω
      refine ⟨-s * t⁻¹, ?_⟩
      have ht' : algebraMap F K t ≠ 0 := fun h0 =>
        ht ((algebraMap F K).injective (by simpa using h0))
      have h2 : algebraMap F K t * ω = -algebraMap F K s := by
        linear_combination h1
      calc algebraMap F K (-s * t⁻¹) = algebraMap F K (-s) * algebraMap F K t⁻¹ := by
            rw [map_mul]
        _ = (-algebraMap F K s) * (algebraMap F K t)⁻¹ := by rw [map_neg, map_inv₀]
        _ = ω := by
            rw [← h2]
            field_simp [ht']
    refine ⟨?_, ht⟩
    have h1' : algebraMap F K s = 0 := by simpa [ht] using h1
    exact (algebraMap F K).injective (by simpa using h1')
  have hspan : Submodule.span F ({ω, algebraMap F K (1 : F)} : Set K) = ⊤ := by
    have h := LinearIndependent.span_eq_top_of_card_eq_finrank hli (by simp [E.finrank_eq])
    simpa using h
  intro c
  have hc : c ∈ Submodule.span F ({ω, algebraMap F K (1 : F)} : Set K) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hc
  refine ⟨b, a, ?_⟩
  rw [← hab]
  simp only [Algebra.smul_def, map_one, mul_one]
  ring

private theorem eq_mul_of_commute_mul (E : QuadExt F K (unitaryInvolution K 2 f))
    (ω : K) (hω : ω ∉ Set.range (algebraMap F K)) (g : K →ₗ[F] K)
    (hg : ∀ x : K, g (ω * x) = ω * g x) :
    ∃ d : K, ∀ x : K, g x = d * x := by
  have hmap : ∀ (a : F) (y : K),
      g (algebraMap F K a * y) = algebraMap F K a * g y := by
    intro a y
    rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
  have hlin : ∀ lam y : K, g (lam * y) = lam * g y := by
    intro lam y
    obtain ⟨a, b, hlam⟩ :=
      exists_add_algebraMap_mul_of_notMem (E := E) ω hω lam
    rw [hlam]
    calc g ((algebraMap F K a + algebraMap F K b * ω) * y)
        = g (algebraMap F K a * y + algebraMap F K b * (ω * y)) := by
            congr 1
            rw [add_mul, mul_assoc]
        _ = g (algebraMap F K a * y) + g (algebraMap F K b * (ω * y)) := by
            rw [map_add]
        _ = algebraMap F K a * g y + algebraMap F K b * g (ω * y) := by
            rw [hmap a y, hmap b (ω * y)]
        _ = algebraMap F K a * g y + algebraMap F K b * (ω * g y) := by rw [hg]
        _ = (algebraMap F K a + algebraMap F K b * ω) * g y := by ring
  refine ⟨g 1, fun x => ?_⟩
  calc g x = g (x * 1) := by rw [mul_one]
    _ = x * g 1 := hlin x 1
    _ = g 1 * x := by ring

private noncomputable def castIncl {k m : ℕ} (_h : k ≤ m)
    (v : (F × F) × (Fin k → K)) : (F × F) × (Fin m → K) :=
  (v.1, fun j => if hj : (j : ℕ) < k then v.2 ⟨(j : ℕ), hj⟩ else 0)

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_castIncl {k m : ℕ} (h : k ≤ m)
    (v : (F × F) × (Fin k → K)) :
    castRestr h (castIncl h v) = v := by
  refine Prod.ext rfl (funext fun i => ?_)
  simp only [castIncl, castRestr]
  rw [dif_pos (by rw [Fin.val_castLE]; exact i.2)]
  congr 1

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem castIncl_castRestr_of_tail {k m : ℕ} (h : k ≤ m)
    {v : (F × F) × (Fin m → K)}
    (hv : ∀ j : Fin m, k ≤ (j : ℕ) → v.2 j = 0) :
    castIncl h (castRestr h v) = v := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp only [castIncl, castRestr]
    rw [dif_pos hj]
    congr 1
  · simp only [castIncl, castRestr]
    rw [dif_neg hj]
    exact (hv j (by omega)).symm

private theorem castLin_castIncl {k m : ℕ} (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin k → K)) :
    castLin h g (castIncl h v) = castIncl h (g v) := by
  refine Prod.ext ?_ (funext fun j => ?_)
  · rw [castLin_fst, castRestr_castIncl]
    rfl
  · by_cases hj : (j : ℕ) < k
    · rw [castLin_snd_of_lt h g (castIncl h v) hj, castRestr_castIncl]
      simp only [castIncl, dif_pos hj]
    · rw [castLin_snd_of_not_lt h g (castIncl h v) hj]
      simp only [castIncl, dif_neg hj]

private theorem castEquiv_castIncl {k m : ℕ} (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin k → K)) :
    castEquiv h g (castIncl h v) = castIncl h (g v) := by
  rw [castEquiv_apply]
  exact castLin_castIncl h g.toLinearMap v


open scoped commutatorElement

private noncomputable def eLin {m : ℕ} (j : Fin m) :
    K →ₗ[F] (F × F) × (Fin m → K) where
  toFun x := ((0, 0), Pi.single j x)
  map_add' x y := by
    ext <;> simp [Pi.single_add]
  map_smul' c x := by
    ext <;> simp [Pi.single_smul]

omit [Finite K] [CharP K 2] in
private theorem eLin_injective {m : ℕ} (j : Fin m) :
    Function.Injective (eLin (F := F) (K := K) j) := by
  intro x y h
  have := congrFun (congrArg Prod.snd h) j
  simpa [eLin] using this

omit [Finite K] [CharP K 2] in
private theorem eq_eLin_of_mem {m : ℕ} {j : Fin m}
    {q : (F × F) × (Fin m → K)}
    (h1 : q.1 = 0) (h2 : ∀ l : Fin m, l ≠ j → q.2 l = 0) :
    q = eLin (F := F) (K := K) j (q.2 j) := by
  refine Prod.ext ?_ (funext fun l => ?_)
  · rw [h1]; rfl
  · by_cases hl : l = j
    · subst hl; simp [eLin]
    · rw [h2 l hl]; simp [eLin, hl]

omit [Finite K] [CharP K 2] in
private theorem chi_val_ne_one {a : Multiplicative (ZMod p)}
    (hχinj : Function.Injective χ) (ha : a ≠ 1) : (χ a : K) ≠ 1 := by
  intro h
  exact ha (hχinj (Units.ext (by simpa using h)))

private theorem chi_ofAdd_one_ne_one :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := by
  intro h
  have h0 : (Multiplicative.ofAdd (0 : ZMod p) : Multiplicative (ZMod p)) = 1 := rfl
  have h10 : (1 : ZMod p) = 0 :=
    Multiplicative.ofAdd.injective (h.trans h0.symm)
  exact one_ne_zero h10

private theorem chi_ofAdd_one_notMem_range
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hχinj : Function.Injective χ) :
    (χ (Multiplicative.ofAdd (1 : ZMod p)) : K) ∉ Set.range (algebraMap F K) := by
  rintro ⟨c, hc⟩
  have h1 : normQuad E (algebraMap F K c) = 1 := by rw [hc]; exact hχ _
  have h2 : algebraMap F K (normQuad E (algebraMap F K c)) =
      (algebraMap F K c) ^ 2 := by
    rw [algebraMap_normQuad, E.fix c, pow_two]
  rw [h1, map_one] at h2
  have hc2 : c ^ 2 = 1 := by
    apply (algebraMap F K).injective
    rw [map_pow, map_one]
    exact h2.symm
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have hc1 : c = 1 := by
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hzero : (c - 1) * (c - 1) = 0 := by
      have hsum : c + c = 0 := by rw [← two_mul, htwo, zero_mul]
      have h1c : c * c = 1 := by simpa [pow_two] using hc2
      calc (c - 1) * (c - 1) = c * c - (c + c) + 1 := by ring
        _ = 0 := by rw [h1c, hsum, sub_zero, ← two_mul, htwo, zero_mul]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hzero)
  have hcχ : χ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := by
    apply Units.ext
    rw [← hc, hc1, map_one]
    rfl
  have h : (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) = 1 :=
    hχinj (hcχ.trans (map_one χ).symm)
  exact (chi_ofAdd_one_ne_one (p := p)) h

private theorem exists_coord_b {k : ℕ} (hkm : k < m)
    (v : Fin m → Multiplicative (ZMod p))
    (hv : ∀ i : Fin k, v (Fin.castLE hkm.le i) = 1) :
    ∃ b : ↥Bs, ((b : G) ∈ ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))) ∧
      ∀ i : Fin m, eta b (π i.castSucc) = v i := by
  classical
  let w : Fin (m + 1) → Multiplicative (ZMod p) :=
    fun j => if hj : (j : ℕ) < m then v ⟨(j : ℕ), hj⟩ else 1
  let b : ↥Bs := eta.symm (fun c => w (π.symm c))
  have heta : ∀ c : Fin n, eta b c = w (π.symm c) := by
    intro c
    dsimp only [b]
    rw [MulEquiv.apply_symm_apply]
  refine ⟨b, ?_, ?_⟩
  · rw [omk_coe_mem_ggBsCoordZeroOn]
    intro c hc
    obtain ⟨i, rfl⟩ := hc
    rw [heta, Equiv.symm_apply_apply]
    have hval : (((Fin.castLE (by omega : k ≤ m + 1) i : Fin (m + 1))) : ℕ) < m := by
      rw [Fin.val_castLE]; omega
    simp only [w, dif_pos hval]
    have hidx : (⟨(((Fin.castLE (by omega : k ≤ m + 1) i : Fin (m + 1))) : ℕ), hval⟩ :
        Fin m) = Fin.castLE hkm.le i := Fin.ext rfl
    rw [hidx]
    exact hv i
  · intro i
    rw [heta, Equiv.symm_apply_apply]
    have hi : (((i.castSucc : Fin (m + 1))) : ℕ) < m := by
      rw [Fin.val_castSucc]; exact i.isLt
    simp only [w, dif_pos hi]
    have hidx : (⟨(((i.castSucc : Fin (m + 1))) : ℕ), hi⟩ : Fin m) = i := Fin.ext rfl
    rw [hidx]

private theorem commute_omDiag_of_mem_comap
    (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {H : Subgroup G} {s : normOmega E m}
    (hs : κ s ∈ Subgroup.centralizer (H : Set G))
    {b : ↥Bs} (hb : (b : G) ∈ H)
    (v : Fin m → Multiplicative (ZMod p))
    (hcoord : ∀ i : Fin m, eta b (π i.castSucc) = v i) :
    s * omDiag (E := E) (χ := χ) hm2 hχ v =
      omDiag (E := E) (χ := χ) hm2 hχ v * s := by
  have hbc : (b : G) * κ s = κ s * (b : G) :=
    Subgroup.mem_centralizer_iff.mp hs (b : G) hb
  have hfr := omFrameT_conj E hκ b s
  have hleft : (b : G) * κ s * (b : G)⁻¹ = κ s := by
    rw [hbc, mul_assoc, mul_inv_cancel, mul_one]
  rw [hleft] at hfr
  have hEq : s = omFrameT E hκ b * s * (omFrameT E hκ b)⁻¹ := hκ.1 hfr
  have hD : omFrameT E hκ b = omDiag (E := E) (χ := χ) hm2 hχ v := by
    rw [omFrameT_eq_omDiag (E := E) (χ := χ) hm2 hχ hκ b]
    congr 1
    funext i
    exact hcoord i
  rw [hD] at hEq
  conv_lhs => rw [hEq]
  group

private theorem commute_omDiag_of_mem {k : ℕ} (hkm : k < m)
    (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {s : normOmega E m}
    (hs : s ∈ (X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G)).comap κ)
    (v : Fin m → Multiplicative (ZMod p))
    (hv : ∀ i : Fin k, v (Fin.castLE hkm.le i) = 1) :
    s * omDiag (E := E) (χ := χ) hm2 hχ v =
      omDiag (E := E) (χ := χ) hm2 hχ v * s := by
  obtain ⟨b, hbH, hcoord⟩ :=
    exists_coord_b (Bs := Bs) (eta := eta) (π := π) (p := p) hkm v hv
  have hsM : κ s ∈ X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
      (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G) :=
    Subgroup.mem_comap.mp hs
  exact commute_omDiag_of_mem_comap (E := E) (χ := χ) hm2 hχ hκ hsM.2 hbH v hcoord

private theorem omDiag_mulSingle_eLin
    (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    (j : Fin m) (a : Multiplicative (ZMod p)) (x : K) :
    ((omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j ((χ a : K) * x) := by
  rw [omDiag_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  by_cases hi : i = j
  · subst hi
    simp [eLin, Pi.mulSingle_eq_same]
  · simp [eLin, hi]

private theorem maps_Vk
    (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    {k : ℕ} {a : Multiplicative (ZMod p)}
    (hχa : (χ a : K) ≠ 1)
    {s : normOmega E m} {v : Fin m → Multiplicative (ZMod p)}
    (hvhead : ∀ i : Fin m, (i : ℕ) < k → v i = 1)
    (hvtail : ∀ i : Fin m, k ≤ (i : ℕ) → v i = a)
    (hcomm : s * omDiag (E := E) (χ := χ) hm2 hχ v =
      omDiag (E := E) (χ := χ) hm2 hχ v * s) :
    ∀ q : (F × F) × (Fin m → K),
      (∀ j : Fin m, k ≤ (j : ℕ) → q.2 j = 0) →
      ∀ j : Fin m, k ≤ (j : ℕ) → ((s : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) q).2 j = 0 := by
  intro q hq j hj
  let S : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) := s
  let Dv : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) :=
    (omDiag (E := E) (χ := χ) hm2 hχ v : normOmega E m)
  have hDq : Dv q = q := by
    change ((omDiag (E := E) (χ := χ) hm2 hχ v : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q = q
    rw [omDiag_apply]
    refine Prod.ext rfl (funext fun i => ?_)
    change (χ (v i) : K) * q.2 i = q.2 i
    by_cases hi : (i : ℕ) < k
    · rw [hvhead i hi, map_one, Units.val_one, one_mul]
    · rw [hvtail i (by omega), hq i (by omega), mul_zero]
  have hcomm' : S * Dv = Dv * S := by
    have h := congrArg (fun x : normOmega E m =>
      (x : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) hcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    simpa only [S, Dv] using h
  have hDsq : Dv (S q) = S q := by
    calc Dv (S q) = (Dv * S) q := by rw [LinearEquiv.mul_apply]
      _ = (S * Dv) q := by rw [hcomm']
      _ = S (Dv q) := by rw [LinearEquiv.mul_apply]
      _ = S q := by rw [hDq]
  have h2 := congrFun (congrArg Prod.snd hDsq) j
  have h3 : (χ (v j) : K) * (S q).2 j = (S q).2 j := by
    simpa only [Dv, omDiag_apply] using h2
  rw [hvtail j (by omega)] at h3
  have hne : (χ a : K) - 1 ≠ 0 := sub_ne_zero.mpr hχa
  have hzero : ((χ a : K) - 1) * (S q).2 j = 0 := by
    rw [sub_mul, one_mul, h3, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

private theorem maps_Uj
    (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    {a : Multiplicative (ZMod p)} (hχa : (χ a : K) ≠ 1)
    {j : Fin m} {s : normOmega E m}
    (hcomm : s * omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) =
      omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) * s) :
    ∀ q : (F × F) × (Fin m → K), q.1 = 0 →
      (∀ l : Fin m, l ≠ j → q.2 l = 0) →
      (((s : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) q).1 = 0 ∧
      ∀ l : Fin m, l ≠ j → (((s : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) q).2 l = 0 := by
  intro q hq1 hq2
  let S : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) := s
  let Dv : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) :=
    (omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) : normOmega E m)
  let y : (F × F) × (Fin m → K) :=
    eLin (F := F) (K := K) j (((χ a : K) - 1)⁻¹ * q.2 j)
  have hane : (χ a : K) - 1 ≠ 0 := sub_ne_zero.mpr hχa
  have hqeq : q = eLin (F := F) (K := K) j (q.2 j) := eq_eLin_of_mem hq1 hq2
  have hDy : Dv y = eLin (F := F) (K := K) j
      ((χ a : K) * (((χ a : K) - 1)⁻¹ * q.2 j)) := by
    exact omDiag_mulSingle_eLin (E := E) (χ := χ) hm2 hχ j a _
  have hval : (χ a : K) * (((χ a : K) - 1)⁻¹ * q.2 j) -
      ((χ a : K) - 1)⁻¹ * q.2 j = q.2 j := by
    rw [show (χ a : K) * (((χ a : K) - 1)⁻¹ * q.2 j) -
        ((χ a : K) - 1)⁻¹ * q.2 j
        = ((χ a : K) - 1) * (((χ a : K) - 1)⁻¹ * q.2 j) from by ring]
    rw [← mul_assoc, mul_inv_cancel₀ hane, one_mul]
  have hkey : Dv y - y = q := by
    rw [hDy, ← (eLin (F := F) (K := K) j).map_sub, hval]
    exact hqeq.symm
  have hcomm' : S * Dv = Dv * S := by
    have h := congrArg (fun x : normOmega E m =>
      (x : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) hcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    simpa only [S, Dv] using h
  have hstep : S q = Dv (S y) - S y := by
    rw [← hkey, map_sub]
    congr 1
    change (S * Dv) y = (Dv * S) y
    rw [hcomm']
  have hmem1 : (Dv (S y)).1 = (S y).1 := by
    simp only [Dv, omDiag_apply]
  have hmem2 : ∀ l : Fin m, l ≠ j → (Dv (S y)).2 l = (S y).2 l := by
    intro l hl
    simp only [Dv, omDiag_apply,
      Pi.mulSingle_eq_of_ne (M := fun _ : Fin m =>
        Multiplicative (ZMod p)) hl a, map_one, Units.val_one, one_mul]
  refine ⟨?_, ?_⟩
  · rw [hstep, Prod.fst_sub, hmem1, sub_self]
  · intro l hl
    rw [hstep, Prod.snd_sub, Pi.sub_apply, hmem2 l hl, sub_self]

private theorem scalar_on_Uj
    (hm2 : 2 ≤ m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1)
    {a : Multiplicative (ZMod p)} (hχa : (χ a : K) ≠ 1)
    (haF : (χ a : K) ∉ Set.range (algebraMap F K))
    {j : Fin m} {s : normOmega E m}
    (hcomm : s * omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) =
      omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) * s) :
    ∃ d : K, ∀ x : K, ((s : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
      (eLin (F := F) (K := K) j x) = eLin (F := F) (K := K) j (d * x) := by
  let S : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) := s
  let Dv : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) :=
    (omDiag (E := E) (χ := χ) hm2 hχ (Pi.mulSingle j a) : normOmega E m)
  have hmaps := maps_Uj (E := E) (χ := χ) hm2 hχ (a := a) hχa
    (j := j) (s := s) (by simpa only [Dv] using hcomm)
  let g : K →ₗ[F] K :=
    { toFun := fun x => (S (eLin (F := F) (K := K) j x)).2 j
      map_add' := by
        intro x y
        rw [map_add (eLin (F := F) (K := K) j), map_add S]
        rfl
      map_smul' := by
        intro c x
        rw [map_smul (eLin (F := F) (K := K) j), map_smul S]
        rfl }
  have hg : ∀ x : K, g ((χ a : K) * x) = (χ a : K) * g x := by
    intro x
    have hmem := hmaps (eLin (F := F) (K := K) j x) rfl
      (fun l hl => by simp [eLin, hl])
    have hmem2 := hmaps (eLin (F := F) (K := K) j ((χ a : K) * x)) rfl
      (fun l hl => by simp [eLin, hl])
    have hSx : S (eLin (F := F) (K := K) j x) = eLin (F := F) (K := K) j (g x) :=
      eq_eLin_of_mem hmem.1 hmem.2
    have hSx2 : S (eLin (F := F) (K := K) j ((χ a : K) * x)) =
        eLin (F := F) (K := K) j (g ((χ a : K) * x)) :=
      eq_eLin_of_mem hmem2.1 hmem2.2
    have hcomm' : S * Dv = Dv * S := by
      have h := congrArg (fun x : normOmega E m =>
        (x : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
      simpa only [S, Dv] using h
    have hDx : Dv (eLin (F := F) (K := K) j x) =
        eLin (F := F) (K := K) j ((χ a : K) * x) :=
      omDiag_mulSingle_eLin (E := E) (χ := χ) hm2 hχ j a x
    have hDgx : Dv (eLin (F := F) (K := K) j (g x)) =
        eLin (F := F) (K := K) j ((χ a : K) * (g x)) :=
      omDiag_mulSingle_eLin (E := E) (χ := χ) hm2 hχ j a (g x)
    have h1 := congrArg (fun f : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K)) => f (eLin (F := F) (K := K) j x)) hcomm'
    simp only [LinearEquiv.mul_apply] at h1
    rw [hDx, hSx2, hSx, hDgx] at h1
    exact eLin_injective j h1
  obtain ⟨d, hd⟩ := eq_mul_of_commute_mul (E := E) (ω := (χ a : K))
    (hω := haF) (g := g) (hg := hg)
  refine ⟨d, fun x => ?_⟩
  have hmem := hmaps (eLin (F := F) (K := K) j x) rfl
    (fun l hl => by simp [eLin, hl])
  change S (eLin (F := F) (K := K) j x) = eLin (F := F) (K := K) j (d * x)
  rw [eq_eLin_of_mem hmem.1 hmem.2]
  change eLin (F := F) (K := K) j (g x) = eLin (F := F) (K := K) j (d * x)
  rw [hd x]
private def VkSet {k : ℕ} (v : (F × F) × (Fin m → K)) : Prop :=
  ∀ j : Fin m, k ≤ (j : ℕ) → v.2 j = 0

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem VkSet_castIncl {k : ℕ} (hkm : k < m) (v : (F × F) × (Fin k → K)) :
    VkSet (m := m) (k := k) (castIncl hkm.le v) := by
  intro j hj
  simp only [castIncl, dif_neg (by omega : ¬ (j : ℕ) < k)]

omit [Finite K] [CharP K 2] in
private theorem sum_tail_eLin {k : ℕ} (_hkm : k < m)
    (v : (F × F) × (Fin m → K)) (i : Fin m) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin m => k ≤ (j : ℕ)),
      eLin (F := F) (K := K) j (v.2 j)).2 i =
      if k ≤ (i : ℕ) then v.2 i else 0 := by
  rw [Prod.snd_sum, Finset.sum_apply]
  by_cases hi : k ≤ (i : ℕ)
  · rw [if_pos hi]
    rw [Finset.sum_eq_single i]
    · simp [eLin]
    · intro j _ hji
      have hji' : i ≠ j := fun h => hji h.symm
      simp [eLin, hji']
    · intro hi'
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) hi'
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : i ≠ j := by
      intro h
      subst h
      exact hi (Finset.mem_filter.mp hj).2
    simp [eLin, hne]

omit [Finite K] [CharP K 2] in
private theorem castIncl_castRestr_add_tail {k : ℕ} (hkm : k < m)
    (v : (F × F) × (Fin m → K)) :
    castIncl hkm.le (castRestr hkm.le v) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin m => k ≤ (j : ℕ)),
        eLin (F := F) (K := K) j (v.2 j)) = v := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [Prod.fst_add, Prod.fst_sum]
    have hsum0 : (∑ c ∈ Finset.univ.filter (fun j : Fin m => k ≤ (j : ℕ)),
        ((eLin (F := F) (K := K) c) (v.2 c)).1) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rfl
    rw [hsum0, add_zero]
    rfl
  · rw [Prod.snd_add, Pi.add_apply, sum_tail_eLin (F := F) (K := K) hkm v i]
    by_cases hi : (i : ℕ) < k
    · rw [if_neg (by omega)]
      simp only [castIncl, dif_pos hi, add_zero]
      exact congrArg v.2 (Fin.ext rfl)
    · rw [if_pos (by omega)]
      simp only [castIncl, dif_neg hi, zero_add]

omit [Finite K] [CharP K 2] in
private theorem eq_of_eq_on_castIncl_tail {k : ℕ} (hkm : k < m)
    {f g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hVk : ∀ v : (F × F) × (Fin k → K), f (castIncl hkm.le v) =
      g (castIncl hkm.le v))
    (hTf : ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      f (eLin (F := F) (K := K) j x) = eLin (F := F) (K := K) j x)
    (hTg : ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      g (eLin (F := F) (K := K) j x) = eLin (F := F) (K := K) j x) :
    f = g := by
  apply LinearEquiv.ext
  intro v
  conv_lhs => rw [← castIncl_castRestr_add_tail hkm v]
  conv_rhs => rw [← castIncl_castRestr_add_tail hkm v]
  rw [map_add, map_sum, map_add, map_sum, hVk]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hTf j (Finset.mem_filter.mp hj).2 (v.2 j),
    hTg j (Finset.mem_filter.mp hj).2 (v.2 j)]

private theorem normOmegaCast_eLin_tail {k : ℕ} (hkm : k < m)
    (a : normOmega E k) {j : Fin m} (hj : k ≤ (j : ℕ)) (x : K) :
    ((normOmegaCast E hkm.le a : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (eLin (F := F) (K := K) j x) = eLin (F := F) (K := K) j x := by
  rw [normOmegaCast_apply_of (E := E) hkm a]
  have hzero : castRestr hkm.le (eLin (F := F) (K := K) j x) = 0 := by
    refine Prod.ext rfl (funext fun i => ?_)
    have hne : (Fin.castLE hkm.le i) ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castLE] at hv
      omega
    simp [castRestr, eLin, hne]
  rw [hzero, map_zero]
  refine Prod.ext rfl (funext fun i => ?_)
  change (if hi : (i : ℕ) < k then (0 : K) else
    ((eLin (F := F) (K := K) j x).2 i)) = ((eLin (F := F) (K := K) j x).2 i)
  by_cases hi : (i : ℕ) < k
  · rw [dif_pos hi]
    have hne : i ≠ j := by omega
    simp [eLin, hne]
  · rw [dif_neg hi]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem vkSet_zero {k : ℕ} : VkSet (m := m) (k := k) (0 : (F × F) × (Fin m → K)) := by
  intro j hj
  rfl

private theorem normOmega_inv_mul_cancel (u : normOmega E m) :
    ((u⁻¹ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) *
    ((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) = 1 := by
  have h := congrArg (fun z : normOmega E m =>
    (z : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
    (inv_mul_cancel u)
  rwa [Subgroup.coe_mul, Subgroup.coe_one] at h

private theorem normOmega_mul_inv_cancel (u : normOmega E m) :
    ((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) *
    ((u⁻¹ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) = 1 := by
  have h := congrArg (fun z : normOmega E m =>
    (z : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
    (mul_inv_cancel u)
  rwa [Subgroup.coe_mul, Subgroup.coe_one] at h

private theorem commutator_eLin_fix {s t : normOmega E m} {j : Fin m}
    {ds dt : K}
    (hs : ∀ x : K, ((s : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j (ds * x))
    (ht : ∀ x : K, ((t : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j (dt * x))
    (hds : ds ≠ 0) (hdt : dt ≠ 0) (x : K) :
    ((⁅s, t⁆ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j x := by
  have hsinv : ∀ y : K, ((s⁻¹ : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
      (eLin (F := F) (K := K) j y) = eLin (F := F) (K := K) j (ds⁻¹ * y) := by
    intro y
    have h := hs (ds⁻¹ * y)
    rw [show ds * (ds⁻¹ * y) = y from by
      rw [← mul_assoc, mul_inv_cancel₀ hds, one_mul]] at h
    have h' := congrArg (fun w => ((s⁻¹ : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w) h
    rw [← LinearEquiv.mul_apply, normOmega_inv_mul_cancel] at h'
    exact h'.symm
  have htin : ∀ y : K, ((t⁻¹ : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
      (eLin (F := F) (K := K) j y) = eLin (F := F) (K := K) j (dt⁻¹ * y) := by
    intro y
    have h := ht (dt⁻¹ * y)
    rw [show dt * (dt⁻¹ * y) = y from by
      rw [← mul_assoc, mul_inv_cancel₀ hdt, one_mul]] at h
    have h' := congrArg (fun w => ((t⁻¹ : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w) h
    rw [← LinearEquiv.mul_apply, normOmega_inv_mul_cancel] at h'
    exact h'.symm
  have hcoe : ((⁅s, t⁆ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) =
      ((s : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) *
      ((t : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) *
      ((s⁻¹ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) *
      ((t⁻¹ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) := by
    rw [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv]
  rw [hcoe]
  simp only [LinearEquiv.mul_apply]
  rw [htin, hsinv, ht, hs]
  congr 1
  field_simp [hds, hdt]

omit [Finite K] [CharP K 2] in
private theorem eLin_ne_zero {j : Fin m} : eLin (F := F) (K := K) j (1 : K) ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg Prod.snd h) j
  simp [eLin] at h2

private theorem scalar_ne_zero_of_scalar {j : Fin m} {s : normOmega E m} {d : K}
    (hs : ∀ x : K, ((s : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j (d * x)) : d ≠ 0 := by
  intro hd
  have h := hs 1
  rw [hd, zero_mul, map_zero (eLin (F := F) (K := K) j)] at h
  have h0 : ((s : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) 0 = 0 := map_zero _
  have : eLin (F := F) (K := K) j (1 : K) = 0 := by
    apply ((s : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))).injective
    rw [h, h0]
  exact eLin_ne_zero this

private theorem fixTail_mul {k : ℕ} {u v : normOmega E m}
    (hu : ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      ((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
        eLin (F := F) (K := K) j x)
    (hv : ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      ((v : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
        eLin (F := F) (K := K) j x) :
    ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      ((u * v : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
        eLin (F := F) (K := K) j x := by
  intro j hj x
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hv j hj x, hu j hj x]

private theorem fixTail_inv {k : ℕ} {u : normOmega E m}
    (hu : ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      ((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
        eLin (F := F) (K := K) j x) :
    ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
      ((u⁻¹ : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
        eLin (F := F) (K := K) j x := by
  intro j hj x
  have h1 : ((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j x := hu j hj x
  have h2 := congrArg (fun w => ((u⁻¹ : normOmega E m) :
    ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w) h1
  rw [← LinearEquiv.mul_apply, normOmega_inv_mul_cancel] at h2
  simpa using h2.symm

omit [Finite K] [CharP K 2] in
private theorem eLin_congr {j : Fin m} {x y : K} (h : x = y) :
    eLin (F := F) (K := K) j x = eLin (F := F) (K := K) j y := by
  rw [h]

private def FixTail {k : ℕ} : Subgroup (normOmega E m) where
  carrier := {u | ∀ (j : Fin m), k ≤ (j : ℕ) → ∀ x : K,
    ((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x) =
      eLin (F := F) (K := K) j x}
  one_mem' := by
    intro j hj x
    rw [Subgroup.coe_one]
    rfl
  mul_mem' := fun hu hv => fixTail_mul (E := E) hu hv
  inv_mem' := fun hu => fixTail_inv (E := E) hu

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem castIncl_add {k m : ℕ} (h : k ≤ m)
    (v w : (F × F) × (Fin k → K)) :
    castIncl (F := F) (K := K) h (v + w) =
      castIncl (F := F) (K := K) h v + castIncl (F := F) (K := K) h w := by
  refine Prod.ext ?_ (funext fun j => ?_)
  · rfl
  · by_cases hj : (j : ℕ) < k
    · simp [castIncl, hj, Pi.add_apply]
    · simp [castIncl, hj]

omit [Finite K] [CharP K 2] in
private theorem castIncl_smul {k m : ℕ} (h : k ≤ m) (c : F)
    (v : (F × F) × (Fin k → K)) :
    castIncl (F := F) (K := K) h (c • v) =
      c • castIncl (F := F) (K := K) h v := by
  refine Prod.ext ?_ (funext fun j => ?_)
  · rfl
  · by_cases hj : (j : ℕ) < k
    · simp [castIncl, hj, Pi.smul_apply]
    · simp [castIncl, hj]

private noncomputable def restrLin {k : ℕ} (hkm : k < m)
    {J : Subgroup (normOmega E m)}
    (hV : ∀ u ∈ J, ∀ v : (F × F) × (Fin m → K),
      VkSet (m := m) (k := k) v → VkSet (m := m) (k := k)
        (((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) v))
    (u : J) : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K)) where
  toFun v := castRestr hkm.le (((u.1 : normOmega E m) :
    ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
    (castIncl hkm.le v))
  invFun v := castRestr hkm.le ((((u⁻¹ : J).1 : normOmega E m) :
    ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
    (castIncl hkm.le v))
  left_inv v := by
    have hVu : VkSet (m := m) (k := k)
        (((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (castIncl hkm.le v)) :=
      hV u u.2 _ (VkSet_castIncl hkm v)
    have h1 := castIncl_castRestr_of_tail hkm.le hVu
    dsimp only
    rw [h1]
    have hc : (((u⁻¹ : J).1 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        ((u.1 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) = 1 := by
      rw [Subgroup.coe_inv]
      have h := congrArg (fun z : normOmega E m =>
        (z : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
        (inv_mul_cancel u.1)
      rwa [Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inv] at h
    have h3 : (((u⁻¹ : J).1 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (castIncl hkm.le v)) = castIncl hkm.le v := by
      calc (((u⁻¹ : J).1 : normOmega E m) :
            ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            (((u.1 : normOmega E m) :
              ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
              (castIncl hkm.le v))
          = ((((u⁻¹ : J).1 : normOmega E m) :
              ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
              ((u.1 : normOmega E m) :
                ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
              (castIncl hkm.le v) := by rw [LinearEquiv.mul_apply]
        _ = (1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K))) (castIncl hkm.le v) := by rw [hc]
        _ = castIncl hkm.le v := rfl
    rw [h3, castRestr_castIncl]
  right_inv v := by
    have hVinv : VkSet (m := m) (k := k)
        ((((u⁻¹ : J).1 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (castIncl hkm.le v)) :=
      hV (u⁻¹) (Subgroup.inv_mem J u.2) _ (VkSet_castIncl hkm v)
    have h1 := castIncl_castRestr_of_tail hkm.le hVinv
    dsimp only
    rw [h1]
    have hc : ((u.1 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        (((u⁻¹ : J).1 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) = 1 := by
      rw [Subgroup.coe_inv]
      have h := congrArg (fun z : normOmega E m =>
        (z : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
        (mul_inv_cancel u.1)
      rwa [Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inv] at h
    have h3 : ((u.1 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        ((((u⁻¹ : J).1 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (castIncl hkm.le v)) = castIncl hkm.le v := by
      calc ((u.1 : normOmega E m) :
            ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            ((((u⁻¹ : J).1 : normOmega E m) :
              ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
              (castIncl hkm.le v))
          = (((u.1 : normOmega E m) :
              ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
              (((u⁻¹ : J).1 : normOmega E m) :
                ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
              (castIncl hkm.le v) := by rw [LinearEquiv.mul_apply]
        _ = (1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K))) (castIncl hkm.le v) := by rw [hc]
        _ = castIncl hkm.le v := rfl
    rw [h3, castRestr_castIncl]
  map_add' x y := by
    rw [castIncl_add, map_add]
    rfl
  map_smul' c x := by
    rw [castIncl_smul, map_smul]
    rfl

private theorem normHypForm_castIncl {k : ℕ} (hkm : k < m)
    (v : (F × F) × (Fin k → K)) :
    normHypForm E m (castIncl hkm.le v) = normHypForm E k v := by
  rw [normHypForm_eq_castRestr_add (E := E) hkm.le]
  have hzero : (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
      normQuad E ((castIncl hkm.le v).2 j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : ¬ (j : ℕ) < k := (Finset.mem_filter.mp hj).2
    rw [show (castIncl hkm.le v).2 j = 0 from by simp [castIncl, hj'], map_zero]
  rw [castRestr_castIncl, hzero, add_zero]

private theorem restrLin_mem_orthogonal {k : ℕ} (hkm : k < m)
    {J : Subgroup (normOmega E m)}
    (hV : ∀ u ∈ J, ∀ v : (F × F) × (Fin m → K),
      VkSet (m := m) (k := k) v → VkSet (m := m) (k := k)
        (((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) v))
    (u : J) : restrLin (E := E) hkm hV u ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  change normHypForm E k (castRestr hkm.le
    (((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) (castIncl hkm.le v))) = normHypForm E k v
  have hVu : VkSet (m := m) (k := k)
      (((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (castIncl hkm.le v)) :=
    hV u u.2 _ (VkSet_castIncl hkm v)
  have h1 : normHypForm E m
      (((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (castIncl hkm.le v)) =
      normHypForm E k (castRestr hkm.le
        (((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (castIncl hkm.le v))) := by
    rw [normHypForm_eq_castRestr_add (E := E) hkm.le]
    have hzero : (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
        normQuad E ((((u.1 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (castIncl hkm.le v)).2 j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' : k ≤ (j : ℕ) := by
        have := (Finset.mem_filter.mp hj).2
        omega
      rw [hVu j hj', map_zero]
    rw [hzero, add_zero]
  rw [← h1]
  rw [show normHypForm E k v = normHypForm E m (castIncl hkm.le v) from
    (normHypForm_castIncl (E := E) hkm v).symm]
  have huO : ((u.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
    Subgroup.commutator_le_self _ u.1.2
  exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp huO) (castIncl hkm.le v)

private noncomputable def restrHom {k : ℕ} (hkm : k < m)
    (J : Subgroup (normOmega E m))
    (hV : ∀ u ∈ J, ∀ v : (F × F) × (Fin m → K),
      VkSet (m := m) (k := k) v → VkSet (m := m) (k := k)
        (((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) v)) :
    J →* TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k) where
  toFun u := ⟨restrLin (E := E) hkm hV u,
    restrLin_mem_orthogonal (E := E) hkm hV u⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (restrLin (E := E) hkm hV 1) v = v
    rw [show (restrLin (E := E) hkm hV 1) v = castRestr hkm.le
      (((1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (castIncl hkm.le v)) from rfl]
    rw [Subgroup.coe_one]
    exact castRestr_castIncl hkm.le v
  map_mul' u v := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change (restrLin (E := E) hkm hV (u * v)) w =
      (restrLin (E := E) hkm hV u) ((restrLin (E := E) hkm hV v) w)
    rw [show (restrLin (E := E) hkm hV (u * v)) w = castRestr hkm.le
      ((((u * v : J).1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (castIncl hkm.le w)) from rfl]
    rw [show (restrLin (E := E) hkm hV v) w = castRestr hkm.le
      (((v.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (castIncl hkm.le w)) from rfl]
    have hVv : VkSet (m := m) (k := k)
        (((v.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (castIncl hkm.le w)) :=
      hV v v.2 _ (VkSet_castIncl hkm w)
    have hJmul : ((u * v : J).1 : normOmega E m) =
        (u.1 : normOmega E m) * (v.1 : normOmega E m) := by
      rw [Subgroup.coe_mul]
    rw [hJmul, Subgroup.coe_mul, LinearEquiv.mul_apply]
    change castRestr hkm.le (((u.1 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((v.1 : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (castIncl hkm.le w))) =
      castRestr hkm.le (((u.1 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (castIncl hkm.le (castRestr hkm.le (((v.1 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (castIncl hkm.le w)))))
    rw [castIncl_castRestr_of_tail hkm.le hVv]

private theorem hNR [Finite G] {k : ℕ}
    {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hm2 : 2 ≤ m) (hkm : k < m)
    (hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1) :
    ⁅X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G),
      X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i)) : Set G)⁆ ≤
      (normOmegaCast E hkm.le).range.map κ := by
  classical
  let H : Subgroup G := ggBsCoordZeroOn Bs eta
    (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let M : Subgroup G := X ⊓ C
  let R : Subgroup G := (normOmegaCast E hkm.le).range.map κ
  let J : Subgroup (normOmega E m) := M.comap κ
  have hMle : M ≤ κ.range := fun z hz => by rw [hκ.2.1]; exact hz.1
  have hJM : J.map κ = M := Subgroup.map_comap_eq_self hMle
  have hMM : ⁅M, M⁆ = (⁅J, J⁆).map κ := by
    rw [← hJM, Subgroup.map_commutator]
  rw [hMM]
  let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have ha : a ≠ 1 := by
    intro h
    have h0 : (Multiplicative.ofAdd (0 : ZMod p) : Multiplicative (ZMod p)) = 1 := rfl
    have h10 : (1 : ZMod p) = 0 :=
      Multiplicative.ofAdd.injective (h.trans h0.symm)
    exact one_ne_zero h10
  have hχa : (χ a : K) ≠ 1 := chi_val_ne_one (χ := χ) hκ.2.2.1 ha
  have haF : (χ a : K) ∉ Set.range (algebraMap F K) :=
    chi_ofAdd_one_notMem_range (E := E) (χ := χ) hχ hκ.2.2.1
  let vfix : Fin m → Multiplicative (ZMod p) :=
    fun i => if (i : ℕ) < k then 1 else a
  have hvfix : ∀ i : Fin k, vfix (Fin.castLE hkm.le i) = 1 := by
    intro i
    change (if ((Fin.castLE hkm.le i : Fin m) : ℕ) < k then 1 else a) = 1
    rw [Fin.val_castLE, if_pos i.2]
  have hvfix_head : ∀ i : Fin m, (i : ℕ) < k → vfix i = 1 := by
    intro i hi
    change (if (i : ℕ) < k then 1 else a) = 1
    rw [if_pos hi]
  have hvfix_tail : ∀ i : Fin m, k ≤ (i : ℕ) → vfix i = a := by
    intro i hi
    change (if (i : ℕ) < k then 1 else a) = a
    rw [if_neg (by omega : ¬ (i : ℕ) < k)]
  have hV : ∀ u ∈ J, ∀ v : (F × F) × (Fin m → K),
      VkSet (m := m) (k := k) v → VkSet (m := m) (k := k)
        (((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) v) := by
    intro u hu v hv j hj
    have hcomm := commute_omDiag_of_mem (E := E) (χ := χ) (Bs := Bs) (X := X)
      (eta := eta) (π := π) (κ := κ) hkm hm2 hχ hκ hu vfix hvfix
    exact maps_Vk (E := E) (χ := χ) hm2 hχ hχa hvfix_head hvfix_tail hcomm v hv j hj
  have hscal : ∀ u ∈ J, ∀ (j : Fin m), k ≤ (j : ℕ) → ∃ d : K,
      ∀ x : K, (((u : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (eLin (F := F) (K := K) j x)) =
        eLin (F := F) (K := K) j (d * x) := by
    intro u hu j hj
    have hv : ∀ i : Fin k, (Pi.mulSingle (M := fun _ : Fin m =>
        Multiplicative (ZMod p)) j a) (Fin.castLE hkm.le i) = 1 := by
      intro i
      have hne : Fin.castLE hkm.le i ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castLE] at hv
        omega
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin m =>
        Multiplicative (ZMod p)) hne a
    have hcomm := commute_omDiag_of_mem (E := E) (χ := χ) (Bs := Bs) (X := X)
      (eta := eta) (π := π) (κ := κ) hkm hm2 hχ hκ hu (Pi.mulSingle j a) hv
    exact scalar_on_Uj (E := E) (χ := χ) hm2 hχ hχa haF hcomm
  have hFix : ⁅J, J⁆ ≤ FixTail (E := E) (m := m) (k := k) := by
    rw [Subgroup.commutator_le]
    intro s hs t ht j hj x
    obtain ⟨ds, hds⟩ := hscal s hs j hj
    obtain ⟨dt, hdt⟩ := hscal t ht j hj
    exact commutator_eLin_fix (E := E) hds hdt
      (scalar_ne_zero_of_scalar (E := E) hds)
      (scalar_ne_zero_of_scalar (E := E) hdt) x
  have hrange : ∀ q ∈ ⁅J, J⁆, q ∈ (normOmegaCast E hkm.le).range := by
    intro q hq
    have hqJ : q ∈ J := Subgroup.commutator_le_self J hq
    have hqFix : q ∈ FixTail (E := E) (m := m) (k := k) := hFix hq
    let qJ : J := ⟨q, hqJ⟩
    let ρ := restrHom (E := E) (m := m) hkm J hV
    let qk : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K)) :=
      restrLin (E := E) hkm hV qJ
    have hq' : qJ ∈ ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ := by
      have htop : (⊤ : Subgroup J).map (Subgroup.subtype J) = J := by
        ext x
        constructor
        · rintro ⟨z, -, rfl⟩
          exact z.2
        · intro hx
          exact ⟨⟨x, hx⟩, trivial, rfl⟩
      have hmap : (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆).map
          (Subgroup.subtype J) = ⁅J, J⁆ := by
        rw [Subgroup.map_commutator]
        congr 1
      have hqmap : q ∈ (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆).map
          (Subgroup.subtype J) := by
        rw [hmap]; exact hq
      obtain ⟨q', hq'mem, hq'eq⟩ := Subgroup.mem_map.mp hqmap
      have hqq' : q' = qJ := Subtype.ext hq'eq
      rwa [hqq'] at hq'mem
    let O : Subgroup (((F × F) × (Fin k → K)) ≃ₗ[F]
        ((F × F) × (Fin k → K))) :=
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k)
    let ρ' : J →* (((F × F) × (Fin k → K)) ≃ₗ[F]
        ((F × F) × (Fin k → K))) := (Subgroup.subtype O).comp ρ
    have hρle : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ ≤
        (⁅O, O⁆).comap ρ' := by
      rw [Subgroup.commutator_le]
      intro s _ t _
      rw [Subgroup.mem_comap]
      have hcomm : ρ' ⁅s, t⁆ = ⁅ρ' s, ρ' t⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp only [map_mul, map_inv]
      rw [hcomm]
      exact Subgroup.commutator_mem_commutator (ρ s).2 (ρ t).2
    have hqkO : qk ∈ normOmega E k := by
      show restrLin (E := E) hkm hV qJ ∈ normOmega E k
      exact hρle hq'
    have hqeq : q = normOmegaCast E hkm.le ⟨qk, hqkO⟩ := by
      apply Subtype.ext
      apply eq_of_eq_on_castIncl_tail (k := k) hkm
        (f := ((q : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))))
        (g := ((normOmegaCast E hkm.le ⟨qk, hqkO⟩ : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))))
      · intro v
        have hmemVk : VkSet (m := m) (k := k)
            (((q : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K))) (castIncl hkm.le v)) :=
          hV q hqJ _ (VkSet_castIncl hkm v)
        rw [normOmegaCast_apply, castEquiv_castIncl,
          ← castIncl_castRestr_of_tail hkm.le hmemVk]
        rfl
      · intro j hj x
        exact hqFix j hj x
      · intro j hj x
        exact normOmegaCast_eLin_tail (E := E) hkm ⟨qk, hqkO⟩ hj x
    exact ⟨⟨qk, hqkO⟩, hqeq.symm⟩
  intro z hz
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
  exact Subgroup.mem_map_of_mem κ (hrange q hq)

theorem ggSecFiveBPermOmK_ggBlockComm_eq [Finite G] {k : ℕ}
    {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hk : 2 ≤ k) (hkm : k < m)
    (hsimp : IsSimpleGroup ↥(normOmega E k)) :
    ggBlockComm Bs eta (Set.range fun i : Fin k => π (Fin.castLE (by omega) i)) =
      (normOmegaCast E hkm.le).range.map κ := by
  classical
  let H : Subgroup G := ggBsCoordZeroOn Bs eta
    (Set.range fun i : Fin k => π (Fin.castLE (by omega : k ≤ m + 1) i))
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let M : Subgroup G := X ⊓ C
  let R : Subgroup G := (normOmegaCast E hkm.le).range.map κ
  let W : Subgroup G := Bs ⊓ R
  let N : Subgroup G := ⁅M, M⁆
  have hm2 : 2 ≤ m := by omega
  have hχ : ∀ a : Multiplicative (ZMod p), normQuad E (χ a : K) = 1 :=
    fun a => normQuad_chi (E := E) hκ ⟨0, by omega⟩ a
  show ⁅C, Bs⁆ = R
  refine ggCommutator_centralizer_eq_of_mul (E := Bs) (H := H) (W := W) (N := N) (R := R)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨h, hhH, w, hwW, heq⟩ :=
      omK_gen (E := E) (χ := χ) hm2 hk hkm hχ hκ hBs ⟨e, he⟩
    exact ⟨h, hhH, w, hwW, by simpa using heq⟩
  · intro x hx
    exact hx.1
  · exact centralizer_le_normalizer_commutator (E := E) (χ := χ) hm2 hk hkm hχ hκ hBs hyB hX
  · exact W_le_commutator (E := E) (χ := χ) hm2 hk hkm hχ hκ hsimp
  · exact hNR (E := E) (χ := χ) hκ hm2 hkm hχ
  · exact range_normOmegaCast_le_centralizer (E := E) (χ := χ) hm2 hkm hχ hκ
  · exact range_le_commutator_W (E := E) (χ := χ) hm2 hk hkm hχ hκ hBs hsimp

end CFSG.StandardType

end
