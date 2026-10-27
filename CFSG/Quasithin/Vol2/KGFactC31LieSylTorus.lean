module


public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

@[expose] def torusChar (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (t : Kˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* Kˣ where
  toFun x := t ^ (∑ j, τ.cartan i j * Multiplicative.toAdd x j)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib, zpow_add]

theorem units_inv_apply_of_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (x : (Module.End K V)ˣ) {v w : V} (h : (x : Module.End K V) v = w) :
    ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) w = v := by
  rw [← h, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem units_pow_apply_of_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (x : (Module.End K V)ˣ) (v : V) (c : K) (h : (x : Module.End K V) v = c • v) (n : ℕ) :
    ((x ^ n : (Module.End K V)ˣ) : Module.End K V) v = (c ^ n) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Module.End.mul_apply, h, map_smul, ih, smul_smul, pow_succ,
      mul_comm]

theorem units_list_prod_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    ∀ (n : ℕ) (F : Fin n → (Module.End K V)ˣ) (c : Fin n → K) (v : V),
      (∀ i, (F i : Module.End K V) v = c i • v) →
      ((List.ofFn F).prod : Module.End K V) v = (∏ i, c i) • v
  | 0, F, c, v, _ => by simp
  | n + 1, F, c, v, h => by
    rw [List.ofFn_succ, List.prod_cons, Units.val_mul, Module.End.mul_apply,
      units_list_prod_apply n (fun i => F i.succ) (fun i => c i.succ) _ (fun i => h i.succ),
      map_smul, h 0, smul_smul, Fin.prod_univ_succ, mul_comm]

theorem torus_mem_char {τ : Tag}
    {K : Type} [Field K] {g : ModGL τ K} (hg : g ∈ torusGroup τ K) :
    ∃ θ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ,
      (∀ i, (g : Module.End K (RootModule τ K)) (hVec τ K i) = hVec τ K i) ∧
      ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
        (g : Module.End K (RootModule τ K)) (rootVec τ K β) =
          ((θ (Multiplicative.ofAdd β) : Kˣ) : K) • rootVec τ K β := by
  unfold torusGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hx
    refine ⟨torusChar τ K i t, fun j => torusElt_hVec i j t, fun β hβ => ?_⟩
    exact torusElt_rootVec i t hβ
  | one =>
    exact ⟨1, fun j => by simp, fun β hβ => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨θx, hxf, hxr⟩ := hx
    obtain ⟨θy, hyf, hyr⟩ := hy
    refine ⟨θx * θy, fun j => ?_, fun β hβ => ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply, hyf j, hxf j]
    · rw [Units.val_mul, Module.End.mul_apply, hyr β hβ, map_smul, hxr β hβ, smul_smul,
        MonoidHom.mul_apply, Units.val_mul, mul_comm]
  | inv x _ hx =>
    obtain ⟨θx, hxf, hxr⟩ := hx
    refine ⟨MonoidHom.mk' (fun y => (θx y)⁻¹) (fun a b => by simp [mul_inv, mul_comm]), fun j => ?_,
      fun β hβ => ?_⟩
    · exact units_inv_apply_of_apply x (hxf j)
    · have hc : ((θx (Multiplicative.ofAdd β) : Kˣ) : K) ≠ 0 :=
        Units.ne_zero _
      have h1 := units_inv_apply_of_apply x (hxr β hβ)
      have h2 : ((x⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
          (rootVec τ K β) = ((θx (Multiplicative.ofAdd β) : Kˣ) : K)⁻¹ • rootVec τ K β := by
        calc ((x⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
              (rootVec τ K β)
            = ((x⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
                (((θx (Multiplicative.ofAdd β) : Kˣ) : K)⁻¹ •
                  ((θx (Multiplicative.ofAdd β) : Kˣ) : K) • rootVec τ K β) := by
              rw [inv_smul_smul₀ hc]
          _ = ((θx (Multiplicative.ofAdd β) : Kˣ) : K)⁻¹ •
                ((x⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
                  (((θx (Multiplicative.ofAdd β) : Kˣ) : K) • rootVec τ K β) := by
              rw [map_smul]
          _ = ((θx (Multiplicative.ofAdd β) : Kˣ) : K)⁻¹ • rootVec τ K β := by
              rw [h1]
      rw [h2]
      simp only [MonoidHom.mk'_apply, Units.val_inv_eq_inv_val]

theorem char_eq_one_of_basis {τ : Tag} {K : Type} [Field K]
    (θ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ)
    (h : ∀ j : Fin τ.rank, θ (Multiplicative.ofAdd (Pi.single j 1)) = 1) : θ = 1 := by
  refine MonoidHom.ext fun x => ?_
  have ha : Multiplicative.toAdd x =
      ∑ j, (Multiplicative.toAdd x j) • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hx : x = ∏ j, Multiplicative.ofAdd (Pi.single j 1 : Fin τ.rank → ℤ) ^
      (Multiplicative.toAdd x j) := by
    calc x = Multiplicative.ofAdd (Multiplicative.toAdd x) := (ofAdd_toAdd x).symm
      _ = Multiplicative.ofAdd (∑ j, (Multiplicative.toAdd x j) •
            (Pi.single j 1 : Fin τ.rank → ℤ)) := by rw [← ha]
      _ = _ := by
        rw [ofAdd_sum]
        exact Finset.prod_congr rfl fun j _ => ofAdd_zsmul _ _
  rw [hx, map_prod]
  simp [map_zpow, h]

theorem zpow_sum_eq_prod' {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι] (a : G)
    (f : ι → ℤ) : a ^ (∑ i, f i) = ∏ i, a ^ f i := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem prod_zpow_pow_coe {K : Type} [Field K] {ι : Type} [Fintype ι] (ζ : Kˣ) (a : ι → ℤ)
    (n : ι → ℕ) :
    ∏ i, (((ζ ^ a i : Kˣ) : K)) ^ n i = ((ζ ^ (∑ i, a i * (n i : ℤ)) : Kˣ) : K) := by
  have h1 : ∀ i, (((ζ ^ a i : Kˣ) : K)) ^ n i = ((ζ ^ (a i * (n i : ℤ)) : Kˣ) : K) := by
    intro i
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  simp only [h1]
  rw [← Units.coe_prod, ← zpow_sum_eq_prod']

theorem isUnit_det_cartan_map11 (τ : Tag) :
    IsUnit ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).det) := by
  have key : ∀ d : ℤ, τ.cartan.det = d → IsUnit (d : ZMod 11) →
      IsUnit ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).det) := by
    intro d hd hu
    have h := RingHom.map_det (Int.castRingHom (ZMod 11)) τ.cartan
    rw [RingHom.mapMatrix_apply, hd] at h
    have h' : (τ.cartan.map (Int.cast : ℤ → ZMod 11)).det = (d : ZMod 11) := h.symm
    rw [h']
    exact hu
  have u1 : IsUnit ((1 : ℤ) : ZMod 11) := by simp
  have u2 : IsUnit ((2 : ℤ) : ZMod 11) := isUnit_iff_exists_inv.2 ⟨((6 : ℤ) : ZMod 11), by decide⟩
  have u3 : IsUnit ((3 : ℤ) : ZMod 11) := isUnit_iff_exists_inv.2 ⟨((4 : ℤ) : ZMod 11), by decide⟩
  have u4 : IsUnit ((4 : ℤ) : ZMod 11) := isUnit_iff_exists_inv.2 ⟨((3 : ℤ) : ZMod 11), by decide⟩
  cases τ
  · exact key 1 det_cartan_G2 u1
  · exact key 1 det_cartan_F4 u1
  · exact key 4 det_cartan_D4 u4
  · exact key 3 det_cartan_E6 u3
  · exact key 2 det_cartan_E7 u2
  · exact key 1 det_cartan_E8 u1

section Chev

theorem omega_one_torusGroup_eq {τ : Tag} {K : Type} [Field K] [Finite K] {ζ : Kˣ}
    (hζ : orderOf ζ = 11) {g : ModGL τ K} (hg : g ∈ torusGroup τ K) (hg11 : g ^ 11 = 1) :
    ∃ k : Fin τ.rank → ZMod 11, g = (List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod := by
  obtain ⟨θ, hfix, hroot⟩ := torus_mem_char hg
  have hsimple : ∀ j : Fin τ.rank,
      ((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K) ^ 11 = 1 := by
    intro j
    have hr : IsRoot τ (Pi.single j 1) := isRoot_single τ j
    have h1 := units_pow_apply_of_eigen (g : (Module.End K (RootModule τ K))ˣ)
      (rootVec τ K (Pi.single j 1)) _ (hroot _ hr) 11
    have h2 : ((g : (Module.End K (RootModule τ K))ˣ) ^ 11 :
        (Module.End K (RootModule τ K))ˣ) = 1 := hg11
    rw [h2, Units.val_one, Module.End.one_apply, rootVec_eq_single_of_isRoot hr] at h1
    have h3 := congrArg (fun w => w (Sum.inr ⟨Pi.single j 1, hr⟩)) h1
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h3
    exact h3.symm
  have hprim : IsPrimitiveRoot (ζ : K) 11 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  choose m _hm_lt hm using fun j : Fin τ.rank => hprim.eq_pow_of_pow_eq_one (hsimple j)
  have hM : IsUnit ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).transpose).det := by
    rw [Matrix.det_transpose]
    exact isUnit_det_cartan_map11 τ
  obtain ⟨k, hk⟩ : ∃ k : Fin τ.rank → ZMod 11, ∀ j : Fin τ.rank,
      ∑ i, ((τ.cartan i j : ℤ) : ZMod 11) * k i = ((m j : ℕ) : ZMod 11) := by
    refine ⟨((τ.cartan.map (Int.cast : ℤ → ZMod 11)).transpose)⁻¹.mulVec
      (fun j => ((m j : ℕ) : ZMod 11)), fun j => ?_⟩
    have h := congrFun (show ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).transpose).mulVec
        (((τ.cartan.map (Int.cast : ℤ → ZMod 11)).transpose)⁻¹.mulVec
          (fun j => ((m j : ℕ) : ZMod 11))) = fun j => ((m j : ℕ) : ZMod 11) from by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]) j
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using h
  have hact_root : ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
      ((((List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod :
        (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) (rootVec τ K β) =
        (∏ i, (((ζ ^ (∑ l, τ.cartan i l * β l) : Kˣ) : K)) ^ (k i).val) • rootVec τ K β) := by
    intro β hβ
    exact units_list_prod_apply _ (fun i => torusElt τ K i ζ ^ (k i).val)
      (fun i => (((ζ ^ (∑ l, τ.cartan i l * β l) : Kˣ) : K)) ^ (k i).val) (rootVec τ K β)
      (fun i => units_pow_apply_of_eigen (torusElt τ K i ζ) (rootVec τ K β) _
        (torusElt_rootVec i ζ hβ) _)
  have hact_e : ∀ j : Fin τ.rank,
      ((((List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod :
        (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
          (rootVec τ K (Pi.single j 1)) =
        ((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K) • rootVec τ K (Pi.single j 1)) := by
    intro j
    rw [hact_root _ (isRoot_single τ j)]
    congr 1
    have hsum : ∀ i, (∑ l, τ.cartan i l * (Pi.single j 1 : Fin τ.rank → ℤ) l) =
        τ.cartan i j := by
      intro i
      simp [Pi.single_apply]
    simp only [hsum]
    rw [prod_zpow_pow_coe ζ (fun i => τ.cartan i j) (fun i => (k i).val)]
    have hN : ((∑ i, τ.cartan i j * ((k i).val : ℤ) : ℤ) : ZMod 11) = ((m j : ℕ) : ZMod 11) := by
      rw [Int.cast_sum]
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hk j
    have hmod : (∑ i, τ.cartan i j * ((k i).val : ℤ)) ≡ ((m j : ℕ) : ℤ) [ZMOD 11] :=
      (ZMod.intCast_eq_intCast_iff _ _ 11).1 (by rw [Int.cast_natCast]; exact hN)
    have hzpow : ζ ^ (∑ i, τ.cartan i j * ((k i).val : ℤ)) = ζ ^ ((m j : ℕ) : ℤ) :=
      zpow_eq_zpow_iff_modEq.2 (by rw [hζ]; exact hmod)
    rw [hzpow, zpow_natCast, Units.val_pow_eq_pow_val, hm j]
  have hact_h : ∀ l : Fin τ.rank,
      ((((List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod :
        (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) (hVec τ K l) =
        hVec τ K l) := by
    intro l
    have h := units_list_prod_apply _ (fun i => torusElt τ K i ζ ^ (k i).val) (fun _ => (1 : K))
      (hVec τ K l) (fun i => by
        rw [units_pow_apply_of_eigen (torusElt τ K i ζ) (hVec τ K l) 1
          (by rw [torusElt_hVec, one_smul]), one_pow])
    rw [h]
    simp
  have hmemh : (List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod ∈ torusGroup τ K := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact pow_mem (torusElt_mem_torusGroup i ζ) _
  set h : (Module.End K (RootModule τ K))ˣ :=
    (List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod with hh
  have hy : g * h⁻¹ ∈ torusGroup τ K :=
    (torusGroup τ K).mul_mem hg ((torusGroup τ K).inv_mem hmemh)
  obtain ⟨θy, _hyfix, hyroot⟩ := torus_mem_char hy
  have hy_root : ∀ j : Fin τ.rank,
      ((g * h⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        (rootVec τ K (Pi.single j 1)) = rootVec τ K (Pi.single j 1) := by
    intro j
    have hr := isRoot_single τ j
    have hc0 : ((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have hinv : ((h⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        (rootVec τ K (Pi.single j 1)) =
        ((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K)⁻¹ • rootVec τ K (Pi.single j 1) := by
      have h1 := units_inv_apply_of_apply h (hact_e j)
      calc ((h⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
            (rootVec τ K (Pi.single j 1))
          = ((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K)⁻¹ •
              ((h⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
                (((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K) •
                  rootVec τ K (Pi.single j 1)) := by
            rw [map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = ((θ (Multiplicative.ofAdd (Pi.single j 1)) : Kˣ) : K)⁻¹ •
              rootVec τ K (Pi.single j 1) := by
            rw [h1]
    rw [Units.val_mul, Module.End.mul_apply, hinv, map_smul, hroot _ hr, smul_smul,
      inv_mul_cancel₀ hc0, one_smul]
  have hy_hVec : ∀ l : Fin τ.rank,
      ((g * h⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        (hVec τ K l) = hVec τ K l := by
    intro l
    rw [Units.val_mul, Module.End.mul_apply, units_inv_apply_of_apply h (hact_h l), hfix l]
  have hθy_e : ∀ j : Fin τ.rank, θy (Multiplicative.ofAdd (Pi.single j 1)) = 1 := by
    intro j
    have hr := isRoot_single τ j
    have h1 := hyroot _ hr
    rw [hy_root j, rootVec_eq_single_of_isRoot hr] at h1
    have h3 := congrArg (fun w => w (Sum.inr ⟨Pi.single j 1, hr⟩)) h1
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h3
    exact Units.ext (by rw [Units.val_one]; exact h3.symm)
  have hθy : θy = 1 := char_eq_one_of_basis θy hθy_e
  have hy1 : ((g * h⁻¹ : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) = 1 := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    rcases a with i | ⟨β, hβ⟩
    · exact hy_hVec i
    · show ((g * h⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
          (Finsupp.single (Sum.inr ⟨β, hβ⟩) 1) = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1
      rw [← rootVec_eq_single_of_isRoot hβ, hyroot β hβ, hθy]
      simp
  refine ⟨k, ?_⟩
  have hy_one : g * h⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact hy1)
  exact mul_inv_eq_one.1 hy_one

end Chev

end CFSG.Quasithin.KGC31
