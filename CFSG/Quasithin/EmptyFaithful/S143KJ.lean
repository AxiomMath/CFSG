module

public import CFSG.Quasithin.EmptyFaithful.S143KI
public import CFSG.Quasithin.EmptyFaithful.S143KH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

set_option synthInstance.maxHeartbeats 400000 in
theorem perm3_sq_cases : ∀ σ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ ^ 3 = 1 →
    σ ^ 2 = 1 ∨ σ ^ 2 = τ ∨ σ ^ 2 = τ ^ 2 := by decide

section Generators

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.phiI_eq_one_iff_mem_rOf {γ : G} (hγ : γ ∈ yOfL22 T M ⊔ uOfL22 T M) :
    phiI c.h1281 ⟨γ, hγ⟩ = 1 ↔ γ ∈ rOf T M := by
  rw [← MonoidHom.mem_ker, ker_phiI c.h1281 c.nonab c.goodElt, mem_pCore_iff,
    ← rOf_eq_pCoreOf_sup c]

theorem Counter.yOfL22_le_rOf_sup_zpowers {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3) :
    yOfL22 T M ≤ rOf T M ⊔ Subgroup.zpowers x := by
  calc yOfL22 T M = oTwoUpper (yOfL22 T M) := (oTwoUpper_yOfL22 T M).symm
    _ ≤ rOf T M ⊔ Subgroup.zpowers x := by
      apply oTwoUpper_le_of_pow_mem
      intro l hl
      refine ⟨1, ?_⟩
      have hR2 : IsPGroup 2 ↥(rOf T M) := c.hyp.sylow.1.to_le (rOf_le_T_of_hyp c.h1281)
      have hlI : l ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.mem_sup_left hl
      have hxI : x ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.mem_sup_left hxL
      set φ := phiI c.h1281 with hφ
      set τ := φ ⟨x, hxI⟩ with hτ
      have hx3' : x ^ 3 = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx3] at this
      have hτ3 : τ ^ 3 = 1 := by
        rw [hτ, ← map_pow]
        have : (⟨x, hxI⟩ : ↥(yOfL22 T M ⊔ uOfL22 T M)) ^ 3 = 1 := Subtype.ext (by simpa using hx3')
        rw [this, map_one]
      have hτ1 : τ ≠ 1 := by
        intro h
        have hxR : x ∈ rOf T M := (c.phiI_eq_one_iff_mem_rOf hxI).mp h
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨x, hxR⟩
        rw [Subgroup.orderOf_mk, hx3] at hk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · norm_num at hk
        · have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0.ne'
          rw [← hk] at this
          norm_num at this
      have step : ∀ j : ℕ, φ ⟨l * l, (yOfL22 T M ⊔ uOfL22 T M).mul_mem hlI hlI⟩ = τ ^ j →
          l * l ∈ rOf T M ⊔ Subgroup.zpowers x := by
        intro j hj
        have hxj : x ^ j ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.pow_mem _ hxI j
        have hm : l * l * (x ^ j)⁻¹ ∈ yOfL22 T M ⊔ uOfL22 T M :=
          Subgroup.mul_mem _ ((yOfL22 T M ⊔ uOfL22 T M).mul_mem hlI hlI)
            (Subgroup.inv_mem _ hxj)
        have h1 : φ ⟨l * l * (x ^ j)⁻¹, hm⟩ = 1 := by
          have e : (⟨l * l * (x ^ j)⁻¹, hm⟩ : ↥(yOfL22 T M ⊔ uOfL22 T M)) =
              ⟨l * l, (yOfL22 T M ⊔ uOfL22 T M).mul_mem hlI hlI⟩ *
                ((⟨x, hxI⟩ : ↥(yOfL22 T M ⊔ uOfL22 T M)) ^ j)⁻¹ := by
            apply Subtype.ext; simp
          rw [e, map_mul, map_inv, map_pow, hj, mul_inv_cancel]
        have hmR := (c.phiI_eq_one_iff_mem_rOf hm).mp h1
        have e : l * l = (l * l * (x ^ j)⁻¹) * x ^ j := by group
        rw [e]
        exact Subgroup.mul_mem_sup hmR (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j)
      have hsq : φ ⟨l * l, (yOfL22 T M ⊔ uOfL22 T M).mul_mem hlI hlI⟩ = (φ ⟨l, hlI⟩) ^ 2 := by
        rw [pow_two, ← map_mul]; rfl
      have hll : l * l ∈ rOf T M ⊔ Subgroup.zpowers x := by
        rcases perm3_sq_cases (φ ⟨l, hlI⟩) τ hτ1 hτ3 with h | h | h
        · exact step 0 (by rw [hsq, h, pow_zero])
        · exact step 1 (by rw [hsq, h, pow_one])
        · exact step 2 (by rw [hsq, h])
      simpa [pow_two] using hll

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.oTwoUpper_inf_normalizer_le_sup {y : G} (hyH : y ∈ mcOf T) (hy3 : y * y * y = 1)
    (hodd : ∀ n : ↥(mcOf T), (n : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) →
      Odd (orderOf n) → ∃ i : ℕ, c.actK n = c.actK ⟨y, hyH⟩ ^ i) :
    oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) ≤
      uOfL22 T M ⊔ Subgroup.zpowers y := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro n ⟨⟨hnH, hnN⟩, hnodd⟩
  have hyodd : Odd (orderOf y) := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact hy3)
    exact Odd.of_dvd_nat (by decide) hdvd
  obtain ⟨i, hi⟩ := hodd ⟨n, hnH⟩ hnN (by rw [Subgroup.orderOf_mk]; exact hnodd)
  have hyiH : y ^ i ∈ mcOf T := Subgroup.pow_mem _ hyH i
  have hqH : n * (y ^ i)⁻¹ ∈ mcOf T := Subgroup.mul_mem _ hnH (Subgroup.inv_mem _ hyiH)
  have hqQ : n * (y ^ i)⁻¹ ∈ qOf T := by
    apply c.mem_qOf_of_actK_eq_one (x := ⟨n * (y ^ i)⁻¹, hqH⟩)
    have e : (⟨n * (y ^ i)⁻¹, hqH⟩ : ↥(mcOf T)) = ⟨n, hnH⟩ * (⟨y, hyH⟩ ^ i)⁻¹ := by
      apply Subtype.ext; simp
    rw [e, map_mul, map_inv, map_pow, hi, mul_inv_cancel]
  have hnO : n ∈ oTwoUpper (mcOf T) := mem_oTwoUpper_of_odd hnH hnodd
  have hyO : y ^ i ∈ oTwoUpper (mcOf T) :=
    Subgroup.pow_mem _ (mem_oTwoUpper_of_odd hyH hyodd) i
  have hqU : n * (y ^ i)⁻¹ ∈ uOfL22 T M := inf_qOf_le_uOfL22 c
    ⟨(oTwoUpper (mcOf T)).mul_mem hnO ((oTwoUpper (mcOf T)).inv_mem hyO), hqQ⟩
  have e : n = (n * (y ^ i)⁻¹) * y ^ i := by group
  rw [e]
  exact Subgroup.mul_mem_sup hqU (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i)

end Generators

section KModelSection

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1)

structure KModel (cm : Mat4) (y : G) : Prop where
  inj : ∀ v w : V4, vm v cm = vm w cm → v = w
  K_le : kOf T M (c.Ac hrW hrV hr2) ≤ GoodSub hS.basis cm
  x_K : x ∈ kOf T M (c.Ac hrW hrV hr2)
  y_K : y ∈ kOf T M (c.Ac hrW hrV hr2)
  y_N : y ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)
  count : (closureCodes [cmat z a r r1 x, cmat z a r r1 y]).length = 360
  inter : ∀ γ₁ ∈ rOf T M, ∀ u₁ ∈ uOfL22 T M, ∀ γ₂ ∈ rOf T M, ∀ u₂ ∈ uOfL22 T M,
    cmat z a r r1 γ₁ = cmat z a r r1 u₁ → cmat z a r r1 γ₁ ≠ I4 →
      cmat z a r r1 γ₂ = cmat z a r r1 u₂ → cmat z a r r1 γ₂ ≠ I4 →
        cmat z a r r1 γ₁ = cmat z a r r1 γ₂

variable {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ

theorem Setup.exists_KModel : ∃ (y : G) (cm : Mat4), KModel hS cm y := by
  obtain ⟨y, hyH, cm, hyN, hy3, hcm, hRok, hUok, hxok, hyok, hcl, hinter, hodd⟩ :=
    hS.exists_model htT htRQ
  have hB := hS.basis
  have hRN := c.rOf_le_normalizer_Ac hrW hrV hr2
  have hUN : ∀ u ∈ uOfL22 T M, u ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    fun u hu => c.iTwo_le_normalizer_Ac hrW hrV hr2 (le_conjClosure _ _ hu)
  have hRG : rOf T M ≤ GoodSub hB cm := fun γ hγ => mem_GoodSub_of_A6ok hB (hRN hγ) (hRok γ hγ)
  have hUG : uOfL22 T M ≤ GoodSub hB cm := fun u hu => mem_GoodSub_of_A6ok hB (hUN u hu) (hUok u hu)
  have hxG : x ∈ GoodSub hB cm :=
    mem_GoodSub_of_A6ok hB (c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo) hxok
  have hyG : y ∈ GoodSub hB cm := mem_GoodSub_of_A6ok hB hyN hyok
  have hLG : yOfL22 T M ≤ GoodSub hB cm :=
    (c.yOfL22_le_rOf_sup_zpowers hS.x_mem hS.x_ord).trans
      (sup_le hRG (Subgroup.zpowers_le.mpr hxG))
  have hOG : oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) ≤
      GoodSub hB cm :=
    (c.oTwoUpper_inf_normalizer_le_sup hrW hrV hr2 hyH hy3 hodd).trans
      (sup_le hUG (Subgroup.zpowers_le.mpr hyG))
  have hyodd : Odd (orderOf y) := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact hy3)
    exact Odd.of_dvd_nat (by decide) hdvd
  refine ⟨y, cm, ⟨hcm, sup_le hOG hLG, (le_sup_right : yOfL22 T M ≤ _) hS.x_mem, ?_, hyN, hcl,
    hinter⟩⟩
  exact (le_sup_left : oTwoUpper _ ≤ _) (mem_oTwoUpper_of_odd ⟨hyH, hyN⟩ hyodd)

end KModelSection

end S143

end CFSG.Quasithin
