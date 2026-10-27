module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB3
public import CFSG.Quasithin.Vol2.Ch3E213MOLB7
public import CFSG.Quasithin.Vol2.Ch3E213MOLB8

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

theorem card_le_two_of_forall {X : Type} [Group X] {V : Subgroup X} {a : X}
    (h : ∀ v ∈ V, v = 1 ∨ v = a) : Nat.card V ≤ 2 := by
  have hsub : (V : Set X) ⊆ {1, a} := fun v hv => by
    rcases h v hv with h | h <;> simp [h]
  calc Nat.card V = (V : Set X).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, a} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({a} : Set X).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

theorem commute_of_comm_mem {X : Type} [Group X] {t h z : X} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzh : z * h = h * z) (hh3 : h * h * h = 1)
    (hy : h * t * h⁻¹ * t⁻¹ = 1 ∨ h * t * h⁻¹ * t⁻¹ = z) : t * h = h * t := by
  rcases hy with hy | hy
  · have h1 : h * t * h⁻¹ = t := mul_inv_eq_one.mp hy
    calc t * h = h * t * h⁻¹ * h := by rw [h1]
      _ = h * t := by group
  · exfalso
    apply hz1
    have e1 : t * h * t⁻¹ = z * h := by
      calc t * h * t⁻¹ = (h * t * h⁻¹ * t⁻¹)⁻¹ * h := by group
        _ = z * h := by rw [hy, inv_eq_of_mul_eq_one_right hz2]
    have e2 : (z * h) * (z * h) * (z * h) = 1 := by
      rw [← e1]
      calc t * h * t⁻¹ * (t * h * t⁻¹) * (t * h * t⁻¹) = t * (h * h * h) * t⁻¹ := by group
        _ = 1 := by rw [hh3, mul_one, mul_inv_cancel]
    have hc : Commute z h := hzh
    calc z = z * z * z * (h * h * h) := by rw [hz2, one_mul, hh3, mul_one]
      _ = (z * h) * (z * h) * (z * h) := by
        rw [← pow_three', ← pow_three', ← pow_three', hc.mul_pow]
      _ = 1 := e2

theorem trivial_of_quadratic {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    (ι : SL(3, GaloisField 3 1) ≃* K) (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (hKs : IsSimpleGroup K) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPz : P ≤ Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X))
    (hPn : Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X) ≤
      Subgroup.normalizer (P : Set X))
    {V : Subgroup X} (hVe : IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V) (hVP : V ≤ P)
    {W : Type} [Group W] (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    (ρ : X →* MulAut W)
    (hquad : ∀ v ∈ V, ∀ v' ∈ V, ∀ w : W, ρ v (ρ v' w * w⁻¹) * (ρ v' w * w⁻¹)⁻¹ = 1) :
    ∀ k ∈ K, ρ k = 1 := by
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  have hz₀2 : z₀ * z₀ = 1 := by
    have h1 := pow_orderOf_eq_one z₀
    rw [hcl.orderOf_eq_two, pow_two] at h1
    exact h1
  have hz₀1 : z₀ ≠ 1 := fun h => by
    have h1 : orderOf z₀ = 2 := hcl.orderOf_eq_two
    rw [h, orderOf_one] at h1
    omega
  have hιmul : ∀ x y : SL(3, GaloisField 3 1), ((ι (x * y) : K) : X) = (ι x : X) * (ι y : X) :=
    fun x y => by rw [map_mul, Subgroup.coe_mul]
  have hιinj : ∀ x y : SL(3, GaloisField 3 1), ((ι x : K) : X) = (ι y : X) → x = y :=
    fun x y h => ι.injective (Subtype.ext h)
  have hιinv : ∀ x : SL(3, GaloisField 3 1), ((ι x⁻¹ : K) : X) = (ι x : X)⁻¹ :=
    fun x => by rw [map_inv, Subgroup.coe_inv]
  set z : X := (ι z₀ : X) with hzdef
  have hz2 : z * z = 1 := by rw [hzdef, ← hιmul, hz₀2, map_one, Subgroup.coe_one]
  have hz1 : z ≠ 1 := fun h => hz₀1 (hιinj _ _ (by rw [← hzdef, h, map_one, Subgroup.coe_one]))
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact hVe.2 v hv
  have hPK : ∀ x : SL(3, GaloisField 3 1), (ι x : X) ∈ P → x * x = 1 → x = 1 ∨ x = z₀ :=
    fun x hx hx2 => eq_one_or_eq_rootInv ι hP hPz hPn hx hx2
  have hVK : ∀ v ∈ V, v ∈ K → v = 1 ∨ v = z := by
    intro v hv hvK
    have hιx : ((ι (ι.symm ⟨v, hvK⟩) : K) : X) = v := by rw [MulEquiv.apply_symm_apply]
    have hx2 : ι.symm ⟨v, hvK⟩ * ι.symm ⟨v, hvK⟩ = 1 :=
      hιinj _ _ (by rw [hιmul, hιx, hV2 v hv, map_one, Subgroup.coe_one])
    rcases hPK _ (by rw [hιx]; exact hVP hv) hx2 with h | h
    · left
      rw [← hιx, h, map_one, Subgroup.coe_one]
    · right
      rw [← hιx, h]
  obtain ⟨t, htV, htK⟩ : ∃ t ∈ V, t ∉ K := by
    by_contra hcon
    push Not at hcon
    have := card_le_two_of_forall (fun v hv => hVK v hv (hcon v hv))
    omega
  have ht2 := hV2 t htV
  have hzV : z ∈ V := by
    by_contra hz
    obtain ⟨v, hvV, hv1, hvt⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ t := by
      by_contra hcon
      push Not at hcon
      have := card_le_two_of_forall (a := t) (fun v hv => by
        by_cases h1 : v = 1
        · exact Or.inl h1
        · exact Or.inr (hcon v hv h1))
      omega
    have hvK : v ∉ K := fun hvK => by
      rcases hVK v hvV hvK with h | h
      · exact hv1 h
      · exact hz (h ▸ hvV)
    rcases hVK _ (V.mul_mem htV hvV) (mul_mem_of_not_mem ι hC htK hvK) with h | h
    · apply hvt
      calc v = t⁻¹ * (t * v) := by group
        _ = t := by rw [h, mul_one]; exact inv_eq_of_mul_eq_one_right ht2
    · exact hz (h ▸ V.mul_mem htV hvV)
  have htz : t * z = z * t := congrArg Subtype.val (hVe.1.is_comm.comm ⟨t, htV⟩ ⟨z, hzV⟩)
  have hqzt : QuadPair ρ z t := quadPair_of_quad hcomm (hquad z hzV t htV)
  have main : ∀ y ∈ P, y ∈ K → QuadPair ρ z y → y ≠ 1 → y ≠ z → ∀ k ∈ K, ρ k = 1 := by
    intro y hyP hyK hyQ hy1 hyz
    obtain ⟨n, hn⟩ := hP ⟨y, hyP⟩
    have hyn : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hinv : ∀ m : ℕ, y ^ m * y ^ m = 1 → y ^ m ≠ 1 → y ^ m = z := by
      intro m hm2 hm1
      have hιx : ((ι (ι.symm ⟨y ^ m, K.pow_mem hyK m⟩) : K) : X) = y ^ m := by
        rw [MulEquiv.apply_symm_apply]
      have hx2 : ι.symm ⟨y ^ m, K.pow_mem hyK m⟩ * ι.symm ⟨y ^ m, K.pow_mem hyK m⟩ = 1 :=
        hιinj _ _ (by rw [hιmul, hιx, hm2, map_one, Subgroup.coe_one])
      rcases hPK _ (by rw [hιx]; exact P.pow_mem hyP m) hx2 with h | h
      · exact absurd (by rw [← hιx, h, map_one, Subgroup.coe_one]) hm1
      · rw [← hιx, h]
    obtain ⟨m, hm⟩ := exists_sq_eq ⟨n, hyn⟩ hy1 hyz hinv
    have hcK : y ^ m ∈ K := K.pow_mem hyK m
    have hcQ : QuadPair ρ (y ^ m * y ^ m) (y ^ m) := by rw [hm]; exact quadPair_pow hyQ m
    have hN := norm_eq_one_of_quadPair hcomm hexp hcQ
    set c' := ι.symm ⟨y ^ m, hcK⟩ with hc'
    have hιc : ((ι c' : K) : X) = y ^ m := by rw [hc', MulEquiv.apply_symm_apply]
    have hc'2 : c' * c' = z₀ := hιinj _ _ (by rw [hιmul, hιc, hm])
    have hc'z : c' * z₀ = z₀ * c' := by rw [← hc'2, mul_assoc]
    have hb3 : c' * u₁ * c'⁻¹ * (c' * u₁ * c'⁻¹) * (c' * u₁ * c'⁻¹) = 1 := by
      calc c' * u₁ * c'⁻¹ * (c' * u₁ * c'⁻¹) * (c' * u₁ * c'⁻¹) =
          c' * (u₁ * u₁ * u₁) * c'⁻¹ := by group
        _ = 1 := by rw [u₁_cube, mul_one, mul_inv_cancel]
    have hcb : c' * (c' * u₁ * c'⁻¹) * c'⁻¹ = u₁⁻¹ := by
      have hz₀i : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz₀2
      calc c' * (c' * u₁ * c'⁻¹) * c'⁻¹ = (c' * c') * u₁ * (c' * c')⁻¹ := by group
        _ = z₀ * u₁ * z₀ := by rw [hc'2, hz₀i]
        _ = u₁⁻¹ := rootInv_conj_u₁
    have hfix := fix_of_norm hcomm hexp (ρ := ρ) (a := (ι u₁ : X))
      (b := (ι (c' * u₁ * c'⁻¹) : X)) (c := y ^ m)
      (by rw [← hιmul, ← hιmul, commute_u₁_conj hc'z])
      (by rw [← hιmul, ← hιmul, u₁_cube, map_one, Subgroup.coe_one])
      (by rw [← hιmul, ← hιmul, hb3, map_one, Subgroup.coe_one])
      (by rw [← hιc, ← hιinv, ← hιmul, ← hιmul])
      (by rw [← hιc, ← hιinv, ← hιmul, ← hιmul, hcb, hιinv]) hN
    have hρu : ρ (ι u₁ : X) = 1 := MulEquiv.ext fun w => by rw [hfix w, MulAut.one_apply]
    have := hKs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.comp K.subtype).ker with h | h
    · exfalso
      apply u₁_ne_one
      have h1 : ι u₁ ∈ (ρ.comp K.subtype).ker := MonoidHom.mem_ker.mpr hρu
      rw [h, Subgroup.mem_bot] at h1
      exact ι.injective (by rw [h1, map_one])
    · intro k hk
      have h1 : (⟨k, hk⟩ : K) ∈ (ρ.comp K.subtype).ker := by rw [h]; trivial
      exact MonoidHom.mem_ker.mp h1
  by_contra hne
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
    have hyK : (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ ∈ K := by
      have h1 : t * (ι h₀ : X)⁻¹ * t⁻¹ ∈ K :=
        (inferInstance : K.Normal).conj_mem _ (K.inv_mem hhK) t
      have h2 := K.mul_mem hhK h1
      simpa [mul_assoc] using h2
    have hyP : (ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPn hhC) t).mp (hVP htV))
        (P.inv_mem (hVP htV))
    have hyQ : QuadPair ρ z ((ι h₀ : X) * t * (ι h₀ : X)⁻¹ * t⁻¹) :=
      quadPair_mul (quadPair_conj hqzt hzh.symm) (quadPair_inv hqzt)
    refine (commute_of_comm_mem hz1 hz2 hzh hh3 ?_)
    by_contra hy
    push Not at hy
    exact hne (main _ hyP hyK hyQ hy.1 hy.2)
  set A₁ : SL(2, GaloisField 3 1) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hA₁
  set A₂ : SL(2, GaloisField 3 1) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ with hA₂
  have cA₁ : (A₁ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 1; 0, 1] := rfl
  have cA₂ : (A₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 0; 1, 1] := rfl
  have hA₁3 : A₁ * A₁ * A₁ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cA₁]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination three_eq_zero_gf3
  have hA₂3 : A₂ * A₂ * A₂ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cA₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination three_eq_zero_gf3
  exact false_of_fix ι hC htK ht2 htz cA₁ cA₂ (hyA _ hA₁3) (hyA _ hA₂3)

end CFSG.Quasithin.Ch3E213M.OLB
