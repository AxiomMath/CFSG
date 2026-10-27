module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.Norm
public import CFSG.Walter.Ree.Thompson2.BaseFin.Nine
public import CFSG.Walter.Ree.Thompson2.BaseFin.Tuple
public import CFSG.Walter.Ree.Thompson2.BaseGrp.K
public import CFSG.Walter.Ree.Thompson2.BaseGrp.U

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward BaseFin

@[expose] def TYOfNine : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [CharP k 3] (σ : k ≃+* k) (n : ℕ),
    Fintype.card k = 3 ^ (2 * n + 1) → ∀ x : ThompsonN k σ, x ^ 9 = 1 → x ^ 3 ≠ 1 →
      (tT σ)⁻¹ * x * tT σ ∈ Subgroup.zpowers x →
      (ThompsonN.J σ)⁻¹ * x * ThompsonN.J σ = x⁻¹ → ∃ d : k, x = tY σ d ∨ x⁻¹ = tY σ d

section NComp

variable {k : Type} [Field k] [CharP k 3] (σ : k ≃+* k) (d : k)

theorem tY_pow_four' : tY σ d ^ 4 = tY σ (d + 1) := by
  rw [pow_succ, tY_cube, tY, tY, pp_mul, pp_eq_iff]
  simp only [map_zero, map_one]
  refine ⟨by ring, by ring, by ring⟩

theorem tY_pow_seven' : tY σ d ^ 7 = tY σ (d - 1) := by
  have h : tY σ d ^ 7 = (tY σ d ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact tY_pow_nine σ d)
  rw [h, tY_sq, pp_inv, tY, pp_eq_iff]
  refine ⟨by ring, by ring, by ring⟩

theorem tT_zpow (m : ℤ) : tT σ ^ m = pp σ 0 (m : k) 0 := by
  have h : tT σ = uHom σ (Multiplicative.ofAdd 1) := rfl
  rw [h, ← map_zpow]
  change pp σ 0 (Multiplicative.toAdd (Multiplicative.ofAdd (1 : k) ^ m)) 0 = _
  rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one]

end NComp

section Transport

variable {H G : Type*} [Group H] [Group G] {φ : H →* G} (hφ : Function.Injective φ)
include hφ

theorem inj_comm {x y : H} {X Y : G} (hx : φ x = X) (hy : φ y = Y) (h : X * Y = Y * X) :
    x * y = y * x := hφ (by rw [map_mul, map_mul, hx, hy, h])

theorem inj_pow {x : H} {X : G} (hx : φ x = X) {n : ℕ} (h : X ^ n = 1) : x ^ n = 1 :=
  hφ (by rw [map_pow, hx, h, map_one])

theorem inj_mul_pow {x y : H} {X Y : G} (hx : φ x = X) (hy : φ y = Y) {n : ℕ}
    (h : (X * Y) ^ n = 1) : (x * y) ^ n = 1 :=
  hφ (by rw [map_pow, map_mul, hx, hy, h, map_one])

theorem inj_conj {a x : H} {A X : G} (ha : φ a = A) (hx : φ x = X) (h : A * X * A = X⁻¹) :
    a * x * a = x⁻¹ := hφ (by rw [map_mul, map_mul, map_inv, ha, hx, h])

theorem inj_conj_sq {c e : H} {C E : G} (hc : φ c = C) (he : φ e = E)
    (h : C⁻¹ * E * C = (E ^ 2)⁻¹) : c⁻¹ * e * c = (e ^ 2)⁻¹ :=
  hφ (by rw [map_mul, map_mul, map_inv, map_inv, map_pow, hc, he, h])

omit hφ in
theorem inj_ne {x y : H} {X Y : G} (hx : φ x = X) (hy : φ y = Y) (h : X ≠ Y) : x ≠ y :=
  fun hxy => h (by rw [← hx, ← hy, hxy])

omit hφ in
theorem inj_ne_one {x : H} {X : G} (hx : φ x = X) (h : X ≠ 1) : x ≠ 1 :=
  inj_ne hx (map_one φ) h

end Transport

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ) [Fintype k]

include C in
theorem exists_rType
    (hY : TYOfNine) : ∃ d : k, Nonempty (RType G k σ d) := by
  obtain ⟨n, hn, hk⟩ := C.card_k_eq
  obtain ⟨K, hK2, hKN, hKinv, hKT⟩ := C.exists_K
  obtain ⟨S, hJS, hKS, hTS⟩ := C.exists_S hK2 hKN hKinv hKT
  obtain ⟨c, hc7, hcN, hTc⟩ := C.exists_c S hTS
  obtain ⟨γ, hγ, huc⟩ := C.exists_u S hJS hc7 hcN hTc
  obtain ⟨i, T', hi, hT', hrels⟩ := C.exists_hatRels S hJS hc7 hcN hTc huc
  set φ := liftHat hrels with hφdef
  have hφ : Function.Injective φ := liftHat_injective hrels C.J_ne_one
  set w := C.ι (pp σ 0 0 γ) with hw
  have hφj : φ PGammaL28.j = C.J := liftHat_j hrels
  have hφu : φ hatW = C.J * w := liftHat_w hrels
  obtain ⟨tt, htt⟩ : ∃ tt, φ tt = C.T := by
    rcases hT' with rfl | rfl
    · exact ⟨_, liftHat_t hrels⟩
    · exact ⟨PGammaL28.t⁻¹, by rw [map_inv, liftHat_t hrels, inv_inv]⟩
  have h7 : c ^ 7 = 1 := by rw [← hc7]; exact pow_orderOf_eq_one c
  obtain ⟨cc, hcc⟩ : ∃ cc, φ cc = c := by
    rcases hi with rfl | rfl
    · exact ⟨hatC, by rw [liftHat_c hrels, pow_one]⟩
    · refine ⟨hatC ^ 5, ?_⟩
      rw [map_pow, liftHat_c hrels, ← pow_mul,
        show 3 * 5 = 7 * 2 + 1 by norm_num, pow_succ, pow_mul, h7, one_pow, one_mul]
  have hww : φ (PGammaL28.j * hatW) = w := by
    rw [map_mul, hφj, hφu, ← mul_assoc, C.J_mul_J, one_mul]
  have hK1 : K ≠ 1 := fun h => hKN (h ▸ C.N.one_mem)
  obtain ⟨m, -, hKm⟩ := C.exists_sJ_eq S hJS hcN hc7 hKS hK1
  have hkk : φ ((cc ^ m)⁻¹ * PGammaL28.j * cc ^ m) = K := by
    rw [map_mul, map_mul, map_inv, map_pow, hcc, hφj, hKm]
    rfl
  set kk := (cc ^ m)⁻¹ * PGammaL28.j * cc ^ m with hkkdef
  have hinj : ∀ {x y : PGammaL28}, φ x = φ y → x = y := fun h => hφ h
  have hJ2 : C.J ^ 2 = 1 := by rw [sq, C.J_mul_J]
  have hT3 := C.T_pow_three
  have hw3 : w ^ 3 = 1 := C.w_pow_three γ
  have hw1 : w ≠ 1 := by
    intro h
    apply hγ
    have := (pp_eq_iff.mp (C.ι_eq_one.mp h))
    exact this.2.2
  have hwP : w ∈ (C.P : Subgroup G) := C.ι_pp_mem_P 0 0 γ
  have hJw : C.J * w * C.J = w⁻¹ := by
    have := C.J_conj_w γ
    rwa [C.J_inv] at this
  have hTw : C.T * w = w * C.T := (C.w_comm_T γ).symm
  obtain ⟨e₀, he9, he3, he3w, heT, heJ⟩ := nine_lemma (a := PGammaL28.j) (t := tt)
    (w := PGammaL28.j * hatW)
    (inj_pow hφ hφj hJ2) (inj_ne_one hφj C.J_ne_one)
    (inj_pow hφ htt hT3) (inj_ne_one htt C.T_ne_one)
    (inj_comm hφ hφj htt C.J_mul_T) (inj_pow hφ hww hw3) (inj_ne_one hww hw1)
    (inj_comm hφ htt hww hTw) (inj_conj hφ hφj hww hJw)
    (by
      rintro hmem
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have := congrArg φ hj
      rw [map_zpow, htt, hww, T, ← map_zpow, tT_zpow] at this
      have h2 := (pp_eq_iff.mp (C.ι_injective this)).2.2
      exact hγ h2.symm)
  set Y₀ := φ e₀ with hY₀
  have hY₀9 : Y₀ ^ 9 = 1 := by rw [hY₀, ← map_pow, he9, map_one]
  have hY₀3 : Y₀ ^ 3 ≠ 1 := fun h => he3 (hinj (by rw [map_pow, ← hY₀, h, map_one]))
  have hY₀w : Y₀ * w = w * Y₀ := by
    have hc3 : Y₀ * Y₀ ^ 3 = Y₀ ^ 3 * Y₀ := (Commute.self_pow Y₀ 3).eq
    rcases he3w with h | h
    · have e : Y₀ ^ 3 = w := by rw [hY₀, ← map_pow, h, hww]
      rwa [e] at hc3
    · have e : Y₀ ^ 3 = w⁻¹ := by rw [hY₀, ← map_pow, h, map_inv, hww]
      rw [e] at hc3
      calc Y₀ * w = w * (w⁻¹ * Y₀) * w := by group
        _ = w * (Y₀ * w⁻¹) * w := by rw [hc3]
        _ = w * Y₀ := by group
  have hY₀N : Y₀ ∈ C.N := C.mem_N_of_commute hwP hw1 hY₀w
  obtain ⟨x, hx⟩ := C.exists_ι hY₀N
  have hx9 : x ^ 9 = 1 := C.ι_injective (by rw [map_pow, ← hx, hY₀9, map_one])
  have hx3 : x ^ 3 ≠ 1 := fun h => hY₀3 (by rw [hx, ← map_pow, h, map_one])
  have hxT : (tT σ)⁻¹ * x * tT σ ∈ Subgroup.zpowers x := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp heT
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, C.ι_injective ?_⟩
    rw [map_zpow, map_mul, map_mul, map_inv, ← hx]
    have := congrArg φ hj
    rwa [map_zpow, map_mul, map_mul, map_inv, htt, ← hY₀] at this
  have hxJ : (ThompsonN.J σ)⁻¹ * x * ThompsonN.J σ = x⁻¹ := by
    apply C.ι_injective
    rw [map_mul, map_mul, map_inv, map_inv, ← hx]
    have := congrArg φ heJ
    rw [map_mul, map_mul, map_inv, hφj, ← hY₀] at this
    change C.J⁻¹ * Y₀ * C.J = Y₀⁻¹
    rw [C.J_inv]
    exact this
  obtain ⟨d, hd⟩ := hY k σ n hk x hx9 hx3 hxT hxJ
  set Y := C.ι (tY σ d) with hYdef
  obtain ⟨ee, hee⟩ : ∃ ee, φ ee = Y := by
    rcases hd with h | h
    · exact ⟨e₀, by rw [← hY₀, hx, h]⟩
    · exact ⟨e₀⁻¹, by rw [map_inv, ← hY₀, hx, ← map_inv, h]⟩
  have hJK : C.J * K = K * C.J := (C.commute_J_of_inv hKinv).symm
  have hJK' : C.J ≠ K := fun h => hKN (h ▸ C.J_mem_N)
  have hY9 : Y ^ 9 = 1 := by rw [hYdef, ← map_pow, tY_pow_nine, map_one]
  have hY3 : Y ^ 3 ≠ 1 := by
    rw [hYdef, ← map_pow, tY_cube]
    intro h
    have := (pp_eq_iff.mp ((C.ι_eq_one.mp h).trans pp_zero.symm)).2.2
    exact one_ne_zero this
  have hJY : C.J * Y * C.J = Y⁻¹ := by
    have := congrArg C.ι (thompsonJ_conj_tY σ d)
    rw [map_mul, map_mul, map_inv, map_inv] at this
    change C.J⁻¹ * C.ι (tY σ d) * C.J = (C.ι (tY σ d))⁻¹ at this
    rwa [C.J_inv] at this
  have hTY : C.T⁻¹ * Y * C.T = (Y ^ 2)⁻¹ := by
    have := congrArg C.ι (tT_conj_tY σ d)
    rwa [map_mul, map_mul, map_inv, map_inv, map_pow] at this
  obtain ⟨g, k₀, hk₀, ha, hb, hc, he⟩ := tuple_lemma (a := PGammaL28.j) (b := kk) (c := tt)
    (e := ee)
    (inj_pow hφ hφj hJ2) (inj_pow hφ hkk (by rw [sq, hK2])) (inj_ne_one hφj C.J_ne_one)
    (inj_ne_one hkk hK1) (inj_ne hφj hkk hJK') (inj_comm hφ hφj hkk hJK)
    (inj_pow hφ htt hT3) (inj_ne_one htt C.T_ne_one) (inj_comm hφ hφj htt C.J_mul_T)
    (inj_mul_pow hφ hkk htt hKT) (inj_pow hφ hee hY9)
    (fun h => hY3 (by rw [← hee, ← map_pow, h, map_one]))
    (inj_conj hφ hφj hee hJY) (inj_conj_sq hφ htt hee hTY)
  set β : PGammaL28 →* G := φ.comp (MulAut.conj g⁻¹).toMonoidHom with hβ
  have hβx : ∀ x, β x = φ (g⁻¹ * x * g) := by
    intro x
    simp [hβ]
  have hβinj : Function.Injective β := hφ.comp (MulAut.conj g⁻¹).injective
  have hβy : ∃ d' : k, β PGammaL28.y = C.ι (tY σ d') := by
    rw [hβx, ← he, map_pow, hee, hYdef, ← map_pow]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk₀
    rcases hk₀ with rfl | rfl | rfl
    · exact ⟨d, by rw [pow_one]⟩
    · exact ⟨d + 1, by rw [tY_pow_four']⟩
    · exact ⟨d - 1, by rw [tY_pow_seven']⟩
  obtain ⟨d', hd'⟩ := hβy
  refine ⟨d', ⟨⟨C.h, C.P, C.e, K, hKN, hKinv, β, hβinj, ?_, ?_, ?_, hd'⟩⟩⟩
  · rw [hβx, ← ha, hφj]; rfl
  · rw [hβx, ← hb, hkk]
  · rw [hβx, ← hc, htt]; rfl

end Ctx

theorem baseExists_of
    (hY : TYOfNine) : BaseExists := by
  intro k _ _ _ G _ _ h σ hP
  obtain ⟨P, ⟨e⟩⟩ := hP
  exact (⟨h, P, e⟩ : Ctx G k σ).exists_rType hY

end CFSG.Walter.Ree.T2.BaseGrp
