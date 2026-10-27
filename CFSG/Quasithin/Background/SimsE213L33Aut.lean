module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB9
public import CFSG.Quasithin.Vol2.Ch3E213MOLB2
public import CFSG.Quasithin.Vol2.Ch3E213MOL3

public section

namespace CFSG.Quasithin.SimsE2.E213L33

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K CFSG.Quasithin.Ch3E213M
open scoped MatrixGroups

theorem rootInv_mul_self :
    Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) *
      Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) = 1 := by
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) OLB.two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  have h1 := pow_orderOf_eq_one (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num))
  rw [hcl.orderOf_eq_two, pow_two] at h1
  exact h1

theorem rootInv_ne_one : Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) ≠ 1 := by
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) OLB.two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  intro h
  have h1 : orderOf (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) = 2 :=
    hcl.orderOf_eq_two
  rw [h, orderOf_one] at h1
  omega

theorem conj_mem_zOf_of_mem_normalizer {Y : Type} [Group Y] {S : Subgroup Y} {s w : Y}
    (hs : s ∈ Subgroup.normalizer (S : Set Y)) (hw : w ∈ E2P.zOf S) :
    s * w * s⁻¹ ∈ E2P.zOf S := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hs w).mp hw.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have hx' : s⁻¹ * x * s ∈ S := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) x).mp hx
    simpa using h1
  have h := (Subgroup.mem_centralizer_iff.mp hw.2) _ hx'
  calc x * (s * w * s⁻¹) = s * ((s⁻¹ * x * s) * w) * s⁻¹ := by group
    _ = s * (w * (s⁻¹ * x * s)) * s⁻¹ := by rw [h]
    _ = s * w * s⁻¹ * x := by group

section Inv


theorem false_of_inv_of_commute {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    (ι : SL(3, GaloisField 3 1) ≃* K) (hC : Subgroup.centralizer (K : Set X) = ⊥)
    {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPz : P ≤ Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X))
    (hPn : Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X) ≤
      Subgroup.normalizer (P : Set X))
    {t : X} (htP : t ∈ P) (htK : t ∉ K) (ht2 : t * t = 1) (htc : ∀ y ∈ P, t * y = y * t) :
    False := by
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) OLB.two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  have hιmul : ∀ x y : SL(3, GaloisField 3 1), ((ι (x * y) : K) : X) = (ι x : X) * (ι y : X) :=
    fun x y => by rw [map_mul, Subgroup.coe_mul]
  have hιinj : ∀ x y : SL(3, GaloisField 3 1), ((ι x : K) : X) = (ι y : X) → x = y :=
    fun x y h => ι.injective (Subtype.ext h)
  have hz₀2 : z₀ * z₀ = 1 := rootInv_mul_self
  have hz₀1 : z₀ ≠ 1 := rootInv_ne_one
  set z : X := (ι z₀ : X) with hzdef
  have hz2 : z * z = 1 := by
    rw [hzdef, ← hιmul, hz₀2, map_one, Subgroup.coe_one]
  have hz1 : z ≠ 1 := fun h =>
    hz₀1 (hιinj _ _ (by rw [← hzdef, h, map_one, Subgroup.coe_one]))
  have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hPz htP)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hyA : ∀ A : SL(2, GaloisField 3 1), A * A * A = 1 →
      t * (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A) : X) =
        (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A) : X) * t := by
    intro A hA3
    set h₀ := WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A with hh₀
    have hh₀z : h₀ * z₀ = z₀ * h₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcl.le_centralizer ⟨A, rfl⟩)
    have hzh : z * (ι h₀ : X) = (ι h₀ : X) * z := by
      rw [hzdef, ← hιmul, ← hιmul, hh₀z]
    have hh3 : (ι h₀ : X) * (ι h₀ : X) * (ι h₀ : X) = 1 := by
      rw [← hιmul, ← hιmul, hh₀, ← map_mul, ← map_mul, hA3, map_one, map_one,
        Subgroup.coe_one]
    have hhK : (ι h₀ : X) ∈ K := (ι h₀).2
    have hhC : (ι h₀ : X) ∈ Subgroup.centralizer ({z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzh.symm
    have huP : (ι h₀ : X) * t * (ι h₀ : X)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPn hhC) t).mp htP
    have hyK : (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ ∈ K := by
      have h1 : t * (ι h₀ : X)⁻¹ * t⁻¹ ∈ K :=
        (inferInstance : K.Normal).conj_mem _ (K.inv_mem hhK) t
      have h2 := K.mul_mem hhK h1
      simpa [mul_assoc] using h2
    have hyP : (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ ∈ P := P.mul_mem huP (P.inv_mem htP)
    have htu : t * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) = ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * t :=
      htc _ huP
    have huu : ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) = 1 := by
      calc ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) =
          (ι h₀ : X) * (t * t) * (ι h₀ : X)⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hy2 : ((ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹) * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹) =
        1 := by
      rw [htinv]
      calc ((ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t) * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t) =
          ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * (t * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹)) * t := by
            group
        _ = ((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * (((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * t) * t := by
            rw [htu]
        _ = (((ι h₀ : X) * t * (ι h₀ : X)⁻¹) * ((ι h₀ : X) * t * (ι h₀ : X)⁻¹)) * (t * t) := by
            group
        _ = 1 := by rw [huu, ht2, one_mul]
    have hy : (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ = 1 ∨
        (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ = z := by
      have hιx : ((ι (ι.symm ⟨_, hyK⟩) : K) : X) = (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ := by
        rw [MulEquiv.apply_symm_apply]
      have hx2 : ι.symm ⟨_, hyK⟩ * ι.symm ⟨_, hyK⟩ = 1 :=
        hιinj _ _ (by rw [hιmul, hιx, hy2, map_one, Subgroup.coe_one])
      rcases OLB.eq_one_or_eq_rootInv ι hP hPz hPn (by rw [hιx]; exact hyP) hx2 with h | h
      · left
        rw [← hιx, h, map_one, Subgroup.coe_one]
      · right
        rw [← hιx, h]
    exact OLB.commute_of_comm_mem hz1 hz2 hzh hh3 hy
  set A₁ : SL(2, GaloisField 3 1) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hA₁
  set A₂ : SL(2, GaloisField 3 1) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ with hA₂
  have cA₁ : (A₁ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 1; 0, 1] := rfl
  have cA₂ : (A₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 0; 1, 1] := rfl
  have hA₁3 : A₁ * A₁ * A₁ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cA₁]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination OLB.three_eq_zero_gf3
  have hA₂3 : A₂ * A₂ * A₂ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cA₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination OLB.three_eq_zero_gf3
  exact OLB.false_of_fix ι hC htK ht2 htz cA₁ cA₂ (hyA _ hA₁3) (hyA _ hA₂3)

end Inv

variable {X : Type} [Group X] [Finite X] {K T M V : Subgroup X} [K.Normal]

theorem exists_iota (hL : IsPSL 3 3 1 ↥K) (hT : IsSylowTwoOf T ⊤) :
    ∃ ι : SL(3, GaloisField 3 1) ≃* K, E2P.zOf (T ⊓ K) =
      Subgroup.zpowers ((ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : K) : X) := by
  obtain ⟨ι⟩ := OLB.exists_equiv_sl3 hL
  have hS : IsSylowTwoOf (T ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hT le_top
      (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : K.Normal)).ge
  obtain ⟨g, hg⟩ := OLB.exists_zOf_sl3 ι (B6.toSylow2 hS)
  rw [B6.toSylow2_coe] at hg
  refine ⟨(MulAut.conj g).trans ι, ?_⟩
  rw [← OL.map_zOf_subgroupOf inf_le_right, hg, MonoidHom.map_zpowers]
  rfl

theorem le_pCoreOf_and_pCoreOf_le (hmp : MinParabolic (⊤ : Subgroup X) T M)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (ι : SL(3, GaloisField 3 1) ≃* K)
    (hz : E2P.zOf (T ⊓ K) =
      Subgroup.zpowers ((ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : K) : X))
    (hVT : V ≤ T) (hVM : V ≤ pCoreOf 2 M) :
    V ≤ pCoreOf 2 (Subgroup.centralizer
      ({((ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : K) : X)} : Set X)) ∧
    pCoreOf 2 (Subgroup.centralizer
      ({((ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : K) : X)} : Set X)) ≤
      T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  have hz₀2 : z₀ * z₀ = 1 := rootInv_mul_self
  have hz₀1 : z₀ ≠ 1 := rootInv_ne_one
  set z : X := ((ι z₀ : K) : X) with hzdef
  have hz2 : z * z = 1 := by
    rw [hzdef, ← Subgroup.coe_mul, ← map_mul, hz₀2, map_one, Subgroup.coe_one]
  have hz1 : z ≠ 1 := fun h => hz₀1 (ι.injective (Subtype.ext (by
    rw [map_one, Subgroup.coe_one]; exact h)))
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzZ : z ∈ E2P.zOf (T ⊓ K) := hz ▸ Subgroup.mem_zpowers _
  have hTz : T ≤ Subgroup.centralizer ({z} : Set X) := by
    intro s hs
    have hsn : s ∈ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxT, hxK⟩
        exact ⟨T.mul_mem (T.mul_mem hs hxT) (T.inv_mem hs),
          (inferInstance : K.Normal).conj_mem x hxK s⟩
      · rintro ⟨hxT, hxK⟩
        refine ⟨?_, ?_⟩
        · have h1 := T.mul_mem (T.mul_mem (T.inv_mem hs) hxT) hs
          simpa [mul_assoc] using h1
        · have h1 := (inferInstance : K.Normal).conj_mem _ hxK s⁻¹
          simpa [mul_assoc] using h1
    have h1 := conj_mem_zOf_of_mem_normalizer hsn hzZ
    rw [hz] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat] at hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hk
      exfalso
      apply hz1
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [← hk]; group
    · rw [h, zpow_one] at hk
      calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [← hk]
  have hzM : Subgroup.centralizer ({z} : Set X) ≤ M := by
    refine hmp.le_of_lt hTz (lt_top_iff_ne_top.mpr fun htop => hz1 ?_)
    have hzC : z ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      have hk : k ∈ Subgroup.centralizer ({z} : Set X) := htop ▸ Subgroup.mem_top k
      exact Subgroup.mem_centralizer_singleton_iff.mp hk
    rw [hC] at hzC
    exact Subgroup.mem_bot.mp hzC
  refine ⟨?_, ?_⟩
  ·
    have hA2 : IsPGroup 2 ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set X)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
    have hAn : Subgroup.centralizer ({z} : Set X) ≤
        Subgroup.normalizer ((pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set X) :
          Subgroup X) : Set X) := by
      intro c hc
      have hcM := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hzM hc)
      have hcC : c ∈ Subgroup.normalizer
          ((Subgroup.centralizer ({z} : Set X) : Subgroup X) : Set X) :=
        Subgroup.le_normalizer hc
      rw [Subgroup.mem_normalizer_iff] at hcM hcC ⊢
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hcM x, hcC x]
    have hAP := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hAn hA2
    exact fun v hv => hAP ⟨hVM hv, hTz (hVT hv)⟩
  ·
    have hP2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer ({z} : Set X))
    have hTn : T ≤ Subgroup.normalizer
        (pCoreOf 2 (Subgroup.centralizer ({z} : Set X)) : Set X) :=
      hTz.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hsup2 : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set X)) ⊔ T) :=
      IsPGroup.to_sup_of_normal_left' hP2 hmp.isSylow.2.1 hTn
    have heq := E2P.eq_of_isSylowTwoOf_le hmp.isSylow hsup2 le_sup_right le_top
    exact le_sup_left.trans heq.le


theorem four_le_card (hmp : MinParabolic (⊤ : Subgroup X) T M) (hL : IsPSL 3 3 1 ↥K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set X)) (hVe : IsElemAbelian 2 V)
    (hVM : V ≤ pCoreOf 2 M) (hVK : ¬ V ≤ K) : 4 ≤ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hz⟩ := exists_iota hL hmp.isSylow
  obtain ⟨hVP, hPT⟩ := le_pCoreOf_and_pCoreOf_le hmp hC ι hz hVT hVM
  by_contra h4
  push Not at h4
  obtain ⟨t, htV, htK⟩ := SetLike.not_le_iff_exists.mp hVK
  have ht1 : t ≠ 1 := fun h => htK (h ▸ K.one_mem)
  have ht2 : t * t = 1 := by rw [← pow_two]; exact hVe.2 t htV
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian hVe)
  have hn1 : n ≤ 1 := by
    by_contra hn1
    push Not at hn1
    have h1 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    have h2 := h1.trans_lt (hn ▸ h4)
    norm_num at h2
  have hle2 : Nat.card V ≤ Nat.card (Subgroup.zpowers t) := by
    rw [Nat.card_zpowers, hord, hn]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  have hVeq : Subgroup.zpowers t = V :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htV) hle2
  have hVt : ∀ v ∈ V, v = 1 ∨ v = t := by
    intro v hv
    rw [← hVeq] at hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have htT : ∀ s ∈ T, s * t = t * s := by
    intro s hs
    have h1 : s * t * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV hs) t).mp htV
    rcases hVt _ h1 with h | h
    · exfalso
      apply ht1
      calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    · calc s * t = s * t * s⁻¹ * s := by group
        _ = t * s := by rw [h]
  exact false_of_inv_of_commute ι hC (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    (hVP htV) htK ht2 fun y hy => (htT y (hPT hy)).symm

theorem false_of_quadratic (hmp : MinParabolic (⊤ : Subgroup X) T M) (hL : IsPSL 3 3 1 ↥K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (hVT : V ≤ T) (hVe : IsElemAbelian 2 V)
    (hVM : V ≤ pCoreOf 2 M) (hV4 : 4 ≤ Nat.card V)
    {W : Type} [Group W] (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    (ρ : X →* MulAut W) (hnt : ∃ k ∈ K, ρ k ≠ 1)
    (hquad : ∀ v ∈ V, ∀ v' ∈ V, ∀ w : W, ρ v (ρ v' w * w⁻¹) * (ρ v' w * w⁻¹)⁻¹ = 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hz⟩ := exists_iota hL hmp.isSylow
  obtain ⟨hVP, -⟩ := le_pCoreOf_and_pCoreOf_le hmp hC ι hz hVT hVM
  have hKs : IsSimpleGroup ↥K := OL.isSimpleGroup_of_L3U3 Nat.prime_three le_rfl (Or.inr hL)
  obtain ⟨k, hk, hk1⟩ := hnt
  exact hk1 (OLB.trivial_of_quadratic ι hC hKs (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    hVe hV4 hVP hcomm hexp ρ hquad k hk)

end CFSG.Quasithin.SimsE2.E213L33
