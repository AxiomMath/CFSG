module

public import CFSG.Quasithin.EmptyFaithful.S143KE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem Z2S3_cases : ∀ p q : Multiplicative (ZMod 2) × Equiv.Perm (Fin 3), p ^ 3 = 1 → q ^ 3 = 1 →
    q ≠ 1 → p = 1 ∨ p = q ∨ p = q ^ 2 := by decide

theorem Z2S3_pow_six : ∀ p : Multiplicative (ZMod 2) × Equiv.Perm (Fin 3), p ^ 6 = 1 := by decide

theorem odd_mem_zpowers_of_Z2S3 {Γ : Type*} [Group Γ]
    (e : Γ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) {y n : Γ} (hy : orderOf y = 3)
    (hn : Odd (orderOf n)) : ∃ i : ℕ, n = y ^ i := by
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have hq3 : (e y) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hq1 : e y ≠ 1 := by
    intro h
    have : y = 1 := e.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hy
    omega
  have hp6 : n ^ 6 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact Z2S3_pow_six _
  have hdvd : orderOf n ∣ 3 := by
    have h6 : orderOf n ∣ 3 * 2 := by simpa using orderOf_dvd_of_pow_eq_one hp6
    exact (Nat.coprime_two_right.mpr hn).dvd_of_dvd_mul_right h6
  have hp3 : (e n) ^ 3 = 1 := by
    rw [← map_pow, orderOf_dvd_iff_pow_eq_one.mp hdvd, map_one]
  rcases Z2S3_cases (e n) (e y) hp3 hq3 hq1 with h | h | h
  · exact ⟨0, by apply e.injective; rw [h, pow_zero, map_one]⟩
  · exact ⟨1, by apply e.injective; rw [h, pow_one]⟩
  · exact ⟨2, by apply e.injective; rw [h, map_pow]⟩

section YPart

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.exists_y :
    ∃ (y : G) (hyH : y ∈ mcOf T), y ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) ∧
      y * y * y = 1 ∧ (∀ w : UT T M, c.actK ⟨y, hyH⟩ w = w → w = 1) ∧
      ∀ n : ↥(mcOf T), (n : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) →
        Odd (orderOf n) → ∃ i : ℕ, c.actK n = c.actK ⟨y, hyH⟩ ^ i := by
  have hαT := c.alphaOf_mem_T hrW hrV hr2
  have hα1 := c.alphaOf_ne_one hrW hrV hr2
  have hα2 := c.alphaOf_sq hrW hrV hr2
  have hαx := c.alphaOf_tclsE hrW hrV hr2
  obtain ⟨y₀, hy₀C, hy₀3, hffp⟩ := c.exists_ffp_centralizer hrW hrV hr2 hαT hα1 hα2 hαx
  obtain ⟨-, ⟨e⟩⟩ := c.swap_facts hrW hrV hr2 hαT hα1 hα2 hαx
  obtain ⟨ω, hωodd, hω⟩ := exists_odd_lift c.actK hy₀C.2 (by rw [hy₀3]; decide)
  have hωN : (ω : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (c.mem_normalizer_Ac_iff hrW hrV hr2 ω).mpr
      (by rw [hω]; exact Subgroup.mem_centralizer_singleton_iff.mp hy₀C.1)
  have hy₀cube : y₀ * y₀ * y₀ = 1 := by
    have := pow_orderOf_eq_one y₀
    rw [hy₀3, pow_three'] at this
    exact this
  have hω3 : (ω : G) * ω * ω = 1 := by
    have h1 : c.actK (ω * ω * ω) = 1 := by
      rw [map_mul, map_mul, hω]; exact hy₀cube
    have hq : ((ω * ω * ω : ↥(mcOf T)) : G) ∈ qOf T := c.mem_qOf_of_actK_eq_one h1
    have hodd3 : Odd (orderOf (ω * ω * ω)) := by
      rw [← pow_three']
      exact Odd.of_dvd_nat hωodd (orderOf_pow_dvd 3)
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨((ω * ω * ω : ↥(mcOf T)) : G), hq⟩
    have hxk : ((ω * ω * ω : ↥(mcOf T)) : G) ^ (2 ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hdvd : orderOf ((ω * ω * ω : ↥(mcOf T)) : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hodd3' : Odd (orderOf ((ω * ω * ω : ↥(mcOf T)) : G)) := by
      rw [Subgroup.orderOf_coe]; exact hodd3
    have : orderOf ((ω * ω * ω : ↥(mcOf T)) : G) = 1 :=
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd3')).eq_one_of_dvd hdvd
    exact orderOf_eq_one_iff.mp this
  refine ⟨ω, ω.2, hωN, hω3, ?_, ?_⟩
  · intro w hw
    exact hffp w (by rw [← hω]; exact hw)
  · intro n hnN hnodd
    have hnC : c.actK n ∈ Subgroup.centralizer ({c.alphaOf hrW hrV hr2} : Set (MulAut (UT T M))) ⊓
        c.actK.range :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr ((c.mem_normalizer_Ac_iff hrW hrV hr2 n).mp hnN),
        ⟨n, rfl⟩⟩
    have hoddn : Odd (orderOf (c.actK n)) := Odd.of_dvd_nat hnodd (orderOf_map_dvd _ _)
    have hy₀ord : orderOf (⟨y₀, hy₀C⟩ : ↥(Subgroup.centralizer
        ({c.alphaOf hrW hrV hr2} : Set (MulAut (UT T M))) ⊓ c.actK.range)) = 3 := by
      rw [Subgroup.orderOf_mk]; exact hy₀3
    obtain ⟨i, hi⟩ := odd_mem_zpowers_of_Z2S3 e hy₀ord
      (n := ⟨c.actK n, hnC⟩) (by rw [Subgroup.orderOf_mk]; exact hoddn)
    refine ⟨i, ?_⟩
    have := congrArg Subtype.val hi
    rw [hω]
    simpa using this

end YPart

section YHyp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {N1 N2 : Mat4}
  (hN : ∀ P, P ∈ [I4, N1, N2, mm N1 N2] ↔ ∃ u ∈ uOfL22 T M, cmat z a r r1 u = P)

include hS hN

theorem Setup.exists_YHyp :
    ∃ (y : G) (hyH : y ∈ mcOf T), y ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) ∧
      y * y * y = 1 ∧ IsYMat (cmat z a r r1 y) ∧ YHypM N1 N2 (cmat z a r r1 y) ∧
      ∀ n : ↥(mcOf T), (n : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) →
        Odd (orderOf n) → ∃ i : ℕ, c.actK n = c.actK ⟨y, hyH⟩ ^ i := by
  obtain ⟨y, hyH, hyN, hy3, hffp, hodd⟩ := c.exists_y hrW hrV hr2
  have hB := hS.basis
  have hUN : ∀ u ∈ uOfL22 T M, u ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    fun u hu => c.iTwo_le_normalizer_Ac hrW hrV hr2 (le_conjClosure _ _ hu)
  refine ⟨y, hyH, hyN, hy3, hS.isYMat_cmat hyH hyN, ⟨?_, ?_, ?_⟩, hodd⟩
  ·
    have h1 : cmat z a r r1 (y * (y * y)) =
        mm (mm (cmat z a r r1 y) (cmat z a r r1 y)) (cmat z a r r1 y) := by
      rw [hB.cmat_mul hyN (Subgroup.mul_mem _ hyN hyN), hB.cmat_mul hyN hyN]
    have h2 : y * (y * y) = 1 := by rw [← mul_assoc]; exact hy3
    rw [h2, hB.cmat_one] at h1
    exact (h1.trans (mm_assoc _ _ _)).symm
  ·
    intro x0 x1 x2 h
    set v : V4 := ⟨x0, x1, x2, false⟩ with hv
    have heA : embV z a r r1 v ∈ c.Ac hrW hrV hr2 := hB.embV_mem v
    have hcoords : coordsOf z a r r1 (embV z a r r1 v) = v := hB.coordsOf_embV v
    have hye : y * embV z a r r1 v * y⁻¹ = embV z a r r1 v := by
      apply hB.coordsOf_inj (conj_mem_of_mem_normalizer hyN heA) heA
      rw [hB.cmat_spec hyN heA, hcoords]
      exact h
    have hzQ : z ∈ qOf T := c.wOfU_le_qOf (Hyp1281Two.VZ_le_wOfU c.h1281 hS.z_V)
    have haQ : a ∈ qOf T := c.wOfU_le_qOf (Hyp1281Two.VZ_le_wOfU c.h1281 hS.a_V)
    have hrQ : r ∈ qOf T := c.wOfU_le_qOf hrW
    have hite : ∀ (b : Bool) (e' : G), e' ∈ qOf T → (if b = true then e' else 1) ∈ qOf T := by
      intro b e' he'; cases b <;> simp [he']
    have heQ : embV z a r r1 v ∈ qOf T := by
      have e1 : embV z a r r1 v = (if x0 = true then z else 1) * (if x1 = true then a else 1) *
          (if x2 = true then r else 1) := by
        simp [embV, hv]
      rw [e1]
      exact (qOf T).mul_mem ((qOf T).mul_mem (hite x0 z hzQ) (hite x1 a haQ)) (hite x2 r hrQ)
    have heU : embV z a r r1 v ∈ uOfL22 T M := c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2 ⟨heA, heQ⟩
    have hye' : y * embV z a r r1 v * y⁻¹ ∈ uOfL22 T M := by rw [hye]; exact heU
    have hyw : c.actK ⟨y, hyH⟩ (tclsE c.hUN heU) = tclsE c.hUN heU :=
      (actTilde_tclsE c.hUN (hHN_of T) c.hHU ⟨y, hyH⟩ heU hye').trans
        (tclsE_congr c.hUN hye' heU hye)
    have h1 := hffp _ hyw
    have heZ := (tclsE_eq_one_iff c.hUN heU).mp h1
    rcases c.mem_Z_cases hS.z_mem hS.z_ne heZ with h0 | h0
    · have : v = V4.zero := by rw [← hcoords, h0, hB.coordsOf_one]
      simp only [hv, V4.zero, V4.mk.injEq] at this
      exact ⟨this.2.1, this.2.2.1⟩
    · have : v = ⟨true, false, false, false⟩ := by rw [← hcoords, h0, hB.coordsOf_e0]
      simp only [hv, V4.mk.injEq] at this
      exact ⟨this.2.1, this.2.2.1⟩
  ·
    intro N hN'
    have hNmem : N ∈ [I4, N1, N2, mm N1 N2] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN' ⊢
      tauto
    obtain ⟨u, hu, rfl⟩ := (hN N).mp hNmem
    have huy : y * u * y⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp (c.hHU hyH) u).mp hu
    refine ⟨cmat z a r r1 (y * u * y⁻¹), (hN _).mpr ⟨_, huy, rfl⟩, ?_⟩
    rw [← hB.cmat_mul hyN (hUN u hu), ← hB.cmat_mul (hUN _ huy) hyN]
    congr 1
    group

end YHyp

end S143

end CFSG.Quasithin
