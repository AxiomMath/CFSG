module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UKl1
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UF16
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UGlue2
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UTh

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Polynomial
open scoped IsMulCommutative
open CFSG.Quasithin.H13.L828T

section Gen

variable {K M : Type} [Group K] [AddCommGroup M] [Module (ZMod 2) M]

theorem ob5_comm_sigma_of_scalar [Module (GaloisField 2 4) M] [Finite M]
    (σ : AddMonoid.End M) (hσL : aeval (ob5L σ) (cyclotomic 5 (ZMod 2)) = 0)
    (hF : ∀ (a : GaloisField 2 4) (m : M), a • m = ob5_f16Hom (ob5L σ) hσL a m)
    (b : Module.Basis (Fin 2) (GaloisField 2 4) M)
    (φ : K →* (M →ₗ[GaloisField 2 4] M)ˣ)
    (θ : K →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))
    (hθ : ∀ κ : K, ((θ κ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 4)) = ob5mat b (φ κ))
    (hsurj : Function.Surjective θ) (ρv : AddMonoid.End M)
    (hcomm : ∀ (κ : K) (m : M), ((φ κ : (M →ₗ[GaloisField 2 4] M)ˣ) : M →ₗ[GaloisField 2 4] M)
      (ρv m) = ρv (((φ κ : (M →ₗ[GaloisField 2 4] M)ˣ) : M →ₗ[GaloisField 2 4] M) m)) :
    σ * ρv = ρv * σ := by
  obtain ⟨α, hα⟩ := ob5_scalar_of_surj b φ θ hθ hsurj ρv hcomm
  have hρ : ∀ w : M, ρv w = ob5_f16Hom (ob5L σ) hσL α w := fun w => (hα w).trans (hF α w)
  have hc := ob5_f16Hom_commute (ob5L σ) hσL (ob5L σ) (Commute.refl _) α
  ext w
  show σ (ρv w) = ρv (σ w)
  rw [hρ w, hρ (σ w)]
  exact congrArg (fun g : Module.End (ZMod 2) M => g w) hc.eq

end Gen

theorem ob5_dih5_noncomm (x w : DihedralGroup 5) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : x * w ≠ w * x := by
  revert x w
  decide

section Main

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

abbrev ob5MM (T I : Subgroup G) (h : G) [IsMulCommutative ↥(fsuV T I)] : Type :=
  QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
    QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)

theorem ob5rho_mul' (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    {a b : G} (ha : a ∈ ob5N0 T I h) (hb : b ∈ ob5N0 T I h)
    (hab : a * b ∈ ob5N0 T I h := Subgroup.mul_mem _ ha hb) :
    ob5rho c ⟨a * b, hab⟩ = ob5rho c ⟨a, ha⟩ * ob5rho c ⟨b, hb⟩ :=
  (congrArg (ob5rho c) (Subtype.ext (Subgroup.coe_mul _ ⟨a, ha⟩ ⟨b, hb⟩).symm)).trans
    (map_mul _ _ _)

theorem ob5dd_of_mem' {I : Subgroup G} (f : ↥I →* DihedralGroup 5) {g : G} (hg : g ∈ I) :
    ob5dd f g = f ⟨g, hg⟩ := by
  unfold ob5dd
  exact dif_pos hg

theorem ob5_not_4080 (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    [Module (ZMod 2) (ob5MM T I h)] [Module (GaloisField 2 4) (ob5MM T I h)]
    [Finite (ob5MM T I h)]
    {K : Subgroup G} (hKN0 : K ≤ ob5N0 T I h)
    (hKC : ∀ κ ∈ K, ∀ x ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G),
      κ * x * κ⁻¹ * x⁻¹ ∈ pCoreOf 2 K)
    {y : G} (hyN : y ∈ ob5N0 T I h) (hyI : y ∈ ch82I (fsuV T I) h)
    {v : G} (hvN : v ∈ ob5N0 T I h) (hvI : v ∈ ch82I (fsuV T I) h) (hv2 : v * v = 1)
    (f : ↥(ch82I (fsuV T I) h) →* DihedralGroup 5)
    (hf : ∀ g : ↥(ch82I (fsuV T I) h), f g = 1 ↔ (g : G) ∈ pCoreOf 2 (ch82I (fsuV T I) h))
    (hyf : ob5dd f y = DihedralGroup.r 1) (hvf : ob5dd f v ≠ 1)
    (hσL : aeval (ob5L (ob5rho c ⟨y, hyN⟩)) (cyclotomic 5 (ZMod 2)) = 0)
    (hF : ∀ (a : GaloisField 2 4) (m : ob5MM T I h),
      a • m = ob5_f16Hom (ob5L (ob5rho c ⟨y, hyN⟩)) hσL a m)
    (b : Module.Basis (Fin 2) (GaloisField 2 4) (ob5MM T I h))
    (φ : K →* ((ob5MM T I h) →ₗ[GaloisField 2 4] (ob5MM T I h))ˣ)
    (θ : K →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))
    (hθ : ∀ κ : K, ((θ κ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 4)) = ob5mat b (φ κ))
    (hsurj : Function.Surjective θ)
    (hφR : ∀ (κ : K) (m : ob5MM T I h),
      ((φ κ : ((ob5MM T I h) →ₗ[GaloisField 2 4] (ob5MM T I h))ˣ) :
        (ob5MM T I h) →ₗ[GaloisField 2 4] (ob5MM T I h)) m = ob5rho c ⟨(κ : G), hKN0 κ.2⟩ m) :
    False := by
  classical
  have hQ1 : ∀ q : ↥K, q ∈ CFSG.pCore 2 ↥K → θ q = 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hN0 : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal (p := 2) (G := ↥K)
    have hN : ((CFSG.pCore 2 ↥K).map θ).Normal := Subgroup.Normal.map hN0 θ hsurj
    have hP : IsPGroup 2 ((CFSG.pCore 2 ↥K).map θ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map θ
    haveI := hN
    have hbot := ob5_normal_two_SL ((CFSG.pCore 2 ↥K).map θ) hP
    intro q hq
    have hmem : θ q ∈ (CFSG.pCore 2 ↥K).map θ := Subgroup.mem_map_of_mem θ hq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hρQ : ∀ q : ↥K, q ∈ CFSG.pCore 2 ↥K → ob5rho c ⟨(q : G), hKN0 q.2⟩ = 1 := by
    intro q hq
    have hφq : φ q = 1 := by
      have h1 := hθ q
      rw [hQ1 q hq] at h1
      apply Units.ext
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [Units.val_one, map_one]
      exact h1.symm.trans Matrix.SpecialLinearGroup.coe_one
    refine AddMonoidHom.ext fun m => ?_
    have h2 := hφR q m
    rw [hφq, Units.val_one, Module.End.one_apply] at h2
    exact h2.symm
  have hvC : v ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hvu := c.hcen u hu v hvI
    calc u * v = v * u * v⁻¹ * v := by rw [hvu]
      _ = v * u := by group
  have hcv : ∀ κ : K, ob5rho c ⟨(κ : G), hKN0 κ.2⟩ * ob5rho c ⟨v, hvN⟩ =
      ob5rho c ⟨v, hvN⟩ * ob5rho c ⟨(κ : G), hKN0 κ.2⟩ := by
    intro κ
    have hc' : (κ : G) * v * (κ : G)⁻¹ * v⁻¹ ∈ pCoreOf 2 K := hKC κ κ.2 v hvC
    have hcN : (κ : G) * v * (κ : G)⁻¹ * v⁻¹ ∈ ob5N0 T I h :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKN0 κ.2) hvN)
        (inv_mem (hKN0 κ.2))) (inv_mem hvN)
    have hvk : v * (κ : G) ∈ ob5N0 T I h := Subgroup.mul_mem _ hvN (hKN0 κ.2)
    have hκv : (κ : G) * v ∈ ob5N0 T I h := Subgroup.mul_mem _ (hKN0 κ.2) hvN
    obtain ⟨q, hq, hqc⟩ := Subgroup.mem_map.mp hc'
    have hqeq : (⟨(κ : G) * v * (κ : G)⁻¹ * v⁻¹, hcN⟩ : ↥(ob5N0 T I h)) =
        ⟨(q : G), hKN0 q.2⟩ := Subtype.ext hqc.symm
    have hr : ob5rho c ⟨(κ : G) * v * (κ : G)⁻¹ * v⁻¹, hcN⟩ = 1 := by
      rw [hqeq]
      exact hρQ q hq
    have hsplit : (κ : G) * v = ((κ : G) * v * (κ : G)⁻¹ * v⁻¹) * (v * (κ : G)) := by group
    have hsplitN : (⟨(κ : G) * v, hκv⟩ : ↥(ob5N0 T I h)) =
        ⟨(κ : G) * v * (κ : G)⁻¹ * v⁻¹, hcN⟩ * ⟨v * (κ : G), hvk⟩ :=
      Subtype.ext (hsplit.trans (Subgroup.coe_mul _ ⟨_, hcN⟩ ⟨_, hvk⟩).symm)
    calc ob5rho c ⟨(κ : G), hKN0 κ.2⟩ * ob5rho c ⟨v, hvN⟩
        = ob5rho c ⟨(κ : G) * v, hκv⟩ := (ob5rho_mul' c (hKN0 κ.2) hvN).symm
      _ = ob5rho c ⟨(κ : G) * v * (κ : G)⁻¹ * v⁻¹, hcN⟩ * ob5rho c ⟨v * (κ : G), hvk⟩ := by
          rw [hsplitN, map_mul]
      _ = ob5rho c ⟨v * (κ : G), hvk⟩ := by rw [hr, one_mul]
      _ = ob5rho c ⟨v, hvN⟩ * ob5rho c ⟨(κ : G), hKN0 κ.2⟩ := ob5rho_mul' c hvN (hKN0 κ.2)
  have hσρ : ob5rho c ⟨y, hyN⟩ * ob5rho c ⟨v, hvN⟩ = ob5rho c ⟨v, hvN⟩ * ob5rho c ⟨y, hyN⟩ := by
    apply ob5_comm_sigma_of_scalar (ob5rho c ⟨y, hyN⟩) hσL hF b φ θ hθ hsurj
      (ob5rho c ⟨v, hvN⟩)
    intro κ m
    calc _ = ob5rho c ⟨(κ : G), hKN0 κ.2⟩ (ob5rho c ⟨v, hvN⟩ m) := hφR κ _
      _ = (ob5rho c ⟨(κ : G), hKN0 κ.2⟩ * ob5rho c ⟨v, hvN⟩) m := rfl
      _ = (ob5rho c ⟨v, hvN⟩ * ob5rho c ⟨(κ : G), hKN0 κ.2⟩) m := by rw [hcv κ]
      _ = ob5rho c ⟨v, hvN⟩ (ob5rho c ⟨(κ : G), hKN0 κ.2⟩ m) := rfl
      _ = _ := by rw [hφR κ m]
  have hdI : y * v * y⁻¹ * v⁻¹ ∈ ch82I (fsuV T I) h :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyI hvI) (inv_mem hyI))
      (inv_mem hvI)
  have hdN : y * v * y⁻¹ * v⁻¹ ∈ ob5N0 T I h :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hvN) (inv_mem hyN))
      (inv_mem hvN)
  have hvy : v * y ∈ ob5N0 T I h := Subgroup.mul_mem _ hvN hyN
  have hyv : y * v ∈ ob5N0 T I h := Subgroup.mul_mem _ hyN hvN
  have hvyinv : (v * y)⁻¹ ∈ ob5N0 T I h := inv_mem hvy
  have e1 : ob5rho c ⟨y * v, hyv⟩ = ob5rho c ⟨v * y, hvy⟩ := by
    rw [ob5rho_mul' c hyN hvN, ob5rho_mul' c hvN hyN]
    exact hσρ
  have e2 : ob5rho c ⟨y * v * y⁻¹ * v⁻¹, hdN⟩ * ob5rho c ⟨v * y, hvy⟩ =
      ob5rho c ⟨y * v, hyv⟩ := by
    rw [← ob5rho_mul' c hdN hvy]
    congr 1
    exact Subtype.ext (by group)
  have e3 : ob5rho c ⟨v * y, hvy⟩ * ob5rho c ⟨(v * y)⁻¹, hvyinv⟩ = 1 := by
    rw [← ob5rho_mul' c hvy hvyinv]
    have hone : (⟨v * y * (v * y)⁻¹, Subgroup.mul_mem _ hvy hvyinv⟩ : ↥(ob5N0 T I h)) = 1 :=
      Subtype.ext (mul_inv_cancel _)
    rw [hone, map_one]
  have hd1 : ob5rho c ⟨y * v * y⁻¹ * v⁻¹, hdN⟩ = 1 := by
    calc ob5rho c ⟨y * v * y⁻¹ * v⁻¹, hdN⟩
        = ob5rho c ⟨y * v * y⁻¹ * v⁻¹, hdN⟩ * (ob5rho c ⟨v * y, hvy⟩ *
            ob5rho c ⟨(v * y)⁻¹, hvyinv⟩) := by rw [e3, mul_one]
      _ = (ob5rho c ⟨y * v * y⁻¹ * v⁻¹, hdN⟩ * ob5rho c ⟨v * y, hvy⟩) *
            ob5rho c ⟨(v * y)⁻¹, hvyinv⟩ := (mul_assoc _ _ _).symm
      _ = ob5rho c ⟨v * y, hvy⟩ * ob5rho c ⟨(v * y)⁻¹, hvyinv⟩ := by rw [e2, e1]
      _ = 1 := e3
  have hdP : y * v * y⁻¹ * v⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h) :=
    c.hfaith _ hdI ((ob5_rho_one_iff c _ hdN).mp hd1)
  have hdf : ob5dd f (y * v * y⁻¹ * v⁻¹) = 1 := by
    rw [ob5dd_of_mem' f hdI]
    exact (hf ⟨_, hdI⟩).mpr hdP
  have hsplitf : ob5dd f (y * v * y⁻¹ * v⁻¹) =
      ob5dd f y * ob5dd f v * (ob5dd f y)⁻¹ * (ob5dd f v)⁻¹ := by
    rw [ob5dd_mul f (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyI hvI) (inv_mem hyI)) (inv_mem hvI),
      ob5dd_mul f (Subgroup.mul_mem _ hyI hvI) (inv_mem hyI),
      ob5dd_mul f hyI hvI, ob5dd_inv f hyI, ob5dd_inv f hvI]
  rw [hsplitf] at hdf
  have hcomm_dih : ob5dd f y * ob5dd f v = ob5dd f v * ob5dd f y := by
    calc ob5dd f y * ob5dd f v
        = (ob5dd f y * ob5dd f v * (ob5dd f y)⁻¹ * (ob5dd f v)⁻¹) * (ob5dd f v * ob5dd f y) := by
          group
      _ = ob5dd f v * ob5dd f y := by rw [hdf, one_mul]
  have hw2 : (ob5dd f v) ^ 2 = 1 := by
    rw [pow_two, ← ob5dd_mul f hvI hvI, hv2, ob5dd_one]
  have hx5 : (ob5dd f y) ^ 5 = 1 := by
    rw [hyf]
    decide
  have hx1 : ob5dd f y ≠ 1 := by
    rw [hyf]
    decide
  exact ob5_dih5_noncomm _ _ hx5 hx1 hw2 hvf hcomm_dih

end Main

end CFSG.Quasithin.H13
