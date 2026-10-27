module

public import CFSG.LieType.SteinbergBRPrimeLinearTwoSylow

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open scoped commutatorElement

theorem exists_finset_card_four_of_le {F : Type*} [Finite F] (h : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  exact ⟨s, hs⟩

theorem isQuasisimple_SL2_of_four {F : Type*} [Field F] (h4 : ∃ s : Finset F, s.card = 4) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  have hab' : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) F ⧸
      center (Matrix.SpecialLinearGroup (Fin 2) F), a * b = b * a :=
    fun a b => by_contra fun h => hab ⟨a, b, h⟩
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) F) ≤
      center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab' (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (Matrix.SpecialLinearGroup (Fin 2) F ⧸ center (Matrix.SpecialLinearGroup (Fin 2) F))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem exists_SL2_mul_col_eq {F : Type*} [Field F] {X : Matrix (Fin 2) (Fin 1) F}
    (hX : X ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      A.val * (!![1; 0] : Matrix (Fin 2) (Fin 1) F) = X := by
  by_cases h0 : X 0 0 = 0
  · have h1 : X 1 0 ≠ 0 := fun h1 => hX (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1])
    refine ⟨⟨!![0, -(X 1 0)⁻¹; X 1 0, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two_of, h1]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![X 0 0, 0; X 1 0, (X 0 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two_of, h0]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_SL2_mul_eq {F : Type*} [Field F] {X Y : Matrix (Fin 2) (Fin 1) F} (hX : X ≠ 0)
    (hY : Y ≠ 0) : ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, A.val * X = Y := by
  obtain ⟨P, hP⟩ := exists_SL2_mul_col_eq hX
  obtain ⟨R, hR⟩ := exists_SL2_mul_col_eq hY
  refine ⟨R * P⁻¹, ?_⟩
  calc (R * P⁻¹).val * X =
        R.val * ((P⁻¹).val * (P.val * (!![1; 0] : Matrix (Fin 2) (Fin 1) F))) := by
        rw [hP, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    _ = Y := by
        rw [← Matrix.mul_assoc (P⁻¹).val, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, hR]

theorem exists_SL2_row_mul_eq {F : Type*} [Field F] {X Y : Matrix (Fin 1) (Fin 2) F}
    (hX : X ≠ 0) (hY : Y ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, X * (A⁻¹).val = Y := by
  obtain ⟨B, hB⟩ := exists_SL2_mul_eq (X := X.transpose) (Y := Y.transpose)
    (fun h => hX (Matrix.transpose_eq_zero.mp h)) (fun h => hY (Matrix.transpose_eq_zero.mp h))
  let Bt : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨B.val.transpose, by rw [Matrix.det_transpose]; exact B.2⟩
  refine ⟨Bt⁻¹, ?_⟩
  rw [inv_inv]
  have h := congrArg Matrix.transpose hB
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose] at h
  exact h

theorem conj_inl_eq {N K : Type*} [CommGroup N] [Group K] {φ : K →* MulAut N}
    (c : N ⋊[φ] K) (n : N) :
    c * SemidirectProduct.inl n * c⁻¹ = SemidirectProduct.inl (φ c.right n) := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply, mul_comm c.left, mul_inv_cancel_right]
  · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.inv_right, SemidirectProduct.right_inl, mul_one, mul_inv_cancel]

theorem affine_image_projection {G N K : Type*} [Group G] [Group N] [Group K]
    {φ : K →* MulAut N} (θ : N ⋊[φ] K →* G) (hθ : Function.Injective θ) :
    (θ.comp SemidirectProduct.inl).range ≤ θ.range ∧
      ∃ ψ : ↥θ.range →* K, Function.Surjective ψ ∧
        ψ.ker = ((θ.comp SemidirectProduct.inl).range).subgroupOf θ.range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨SemidirectProduct.inl n, rfl⟩
  let e : N ⋊[φ] K ≃* ↥θ.range := MonoidHom.ofInjective hθ
  refine ⟨SemidirectProduct.rightHom.comp e.symm.toMonoidHom,
    SemidirectProduct.rightHom_surjective.comp e.symm.surjective, ?_⟩
  ext y
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hy
    have h1 : e.symm y = SemidirectProduct.inl (e.symm y).left :=
      SemidirectProduct.ext rfl hy
    refine ⟨(e.symm y).left, ?_⟩
    calc (θ.comp SemidirectProduct.inl) (e.symm y).left = θ (e.symm y) := by
          rw [MonoidHom.comp_apply, ← h1]
      _ = (y : G) := congrArg Subtype.val (e.apply_symm_apply y)
  · rintro ⟨n, hn⟩
    have h1 : e.symm y = SemidirectProduct.inl n := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext hn.symm
    change (e.symm y).right = 1
    rw [h1]
    rfl

theorem isElementaryAbelian_range_of_comm {G H : Type*} [Group G] [Group H] {p : ℕ}
    (f : G →* H) (hcomm : ∀ x y : G, x * y = y * x) (hp : ∀ x : G, x ^ p = 1) :
    IsElementaryAbelian p f.range where
  is_comm := ⟨fun a b => by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : H) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, hcomm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    obtain ⟨x, hx⟩ := a.2
    apply Subtype.ext
    change (a : H) ^ p = 1
    rw [← hx, ← map_pow, hp, map_one]

theorem eq_range_of_affine {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hFp : Nat.card F = p) (hp5 : 5 ≤ p)
    {Qt : Subgroup G} (ρ : ↥Qt →* GL (Fin 2) F) (hρ : Function.Surjective ρ) {N : Type*}
    [CommGroup N] {φ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut N}
    (htrans : ∀ n m : N, n ≠ 1 → m ≠ 1 → ∃ A, φ A n = m)
    (θ : N ⋊[φ] Matrix.SpecialLinearGroup (Fin 2) F →* G) (hθ : Function.Injective θ)
    (hθQ : θ.range ≤ Qt)
    (hρθ : ∀ x, ρ ⟨θ x, hθQ ⟨x, rfl⟩⟩ = Matrix.SpecialLinearGroup.toGL x.right)
    (hker : ∀ g : ↥Qt, ρ g = 1 → (g : G) ∈ (θ.comp SemidirectProduct.inl).range)
    {Mt : Subgroup G} (hMQ : Mt ≤ Qt) (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ Mt)
    {C : Subgroup G} (hCM : C ≤ Mt) (hCY : C ≤ θ.range) (hCperf : ⁅C, C⁆ = C) (hC1 : C ≠ ⊥)
    (hCsub : (C.subgroupOf Mt).IsSubnormal) (hCq : ¬ CFSG.IsQuasisimple ↥C) :
    C = θ.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GL (Fin 2) F) := Finite.of_injective _ Units.val_injective
  have hSQ : (S : Subgroup G) ≤ Qt := hSM.trans hMQ
  set H : Subgroup (GL (Fin 2) F) := (Mt.subgroupOf Qt).map ρ with hH
  set J : Subgroup (GL (Fin 2) F) := (C.subgroupOf Qt).map ρ with hJ
  have hSH : ∃ P : Sylow 2 (GL (Fin 2) F), (P : Subgroup (GL (Fin 2) F)) ≤ H := by
    refine ⟨(S.subtype hSQ).mapSurjective hρ, ?_⟩
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
    exact map_mono fun x hx => mem_subgroupOf.mpr (hSM (mem_subgroupOf.mp hx))
  have hJH : J ≤ H := map_mono fun x hx => mem_subgroupOf.mpr (hCM (mem_subgroupOf.mp hx))
  have hCQperf : ⁅C.subgroupOf Qt, C.subgroupOf Qt⁆ = C.subgroupOf Qt := by
    apply Subgroup.map_injective Qt.subtype_injective
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le (hCM.trans hMQ), hCperf]
  have hJperf : ⁅J, J⁆ = J := by rw [hJ, ← Subgroup.map_commutator, hCQperf]
  have hUcomm : ∀ x ∈ (θ.comp SemidirectProduct.inl).range,
      ∀ y ∈ (θ.comp SemidirectProduct.inl).range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h := congrArg (θ.comp SemidirectProduct.inl) (mul_comm a b)
    rwa [map_mul, map_mul] at h
  have hJ1 : J ≠ ⊥ := by
    intro hJbot
    apply hC1
    have hCU : ∀ c ∈ C, c ∈ (θ.comp SemidirectProduct.inl).range := fun c hc => by
      have h1 : ρ ⟨c, hMQ (hCM hc)⟩ ∈ J := ⟨⟨c, hMQ (hCM hc)⟩, mem_subgroupOf.mpr hc, rfl⟩
      rw [hJbot, mem_bot] at h1
      exact hker _ h1
    rw [← hCperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact hUcomm _ (hCU y hy) _ (hCU x hx)
  let f : ↥Mt →* ↥H := (ρ.comp (Subgroup.inclusion hMQ)).codRestrict H fun m =>
    ⟨Subgroup.inclusion hMQ m, mem_subgroupOf.mpr m.2, rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨_, q, hq, rfl⟩
    exact ⟨⟨q, mem_subgroupOf.mp hq⟩, rfl⟩
  have hmap : (C.subgroupOf Mt).map f = J.subgroupOf H := by
    ext y
    rw [mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨Subgroup.inclusion hMQ m, mem_subgroupOf.mpr (mem_subgroupOf.mp hm), rfl⟩
    · rintro ⟨q, hq, hqy⟩
      exact ⟨⟨q, hCM (mem_subgroupOf.mp hq)⟩, mem_subgroupOf.mpr (mem_subgroupOf.mp hq),
        Subtype.ext hqy⟩
  have hJsub : (J.subgroupOf H).IsSubnormal := hmap ▸ hCsub.map hfs
  have hSL := (CFSG.LieType.prime_linear_two_full_sylow_perfect_subnormal_equality hFp hp5 hSH
    hJH hJ1 hJperf hJsub).1
  have hlift : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x, θ x ∈ C ∧ x.right = A := by
    intro A
    have hA : Matrix.SpecialLinearGroup.toGL A ∈ J := by
      rw [hSL]
      exact ⟨A, rfl⟩
    obtain ⟨q, hq, hqA⟩ := hA
    have hqC : (q : G) ∈ C := mem_subgroupOf.mp hq
    obtain ⟨x, hx⟩ := hCY hqC
    refine ⟨x, by rw [hx]; exact hqC, ?_⟩
    have h1 : ρ ⟨θ x, hθQ ⟨x, rfl⟩⟩ = ρ q := congrArg ρ (Subtype.ext hx)
    rw [hρθ, hqA] at h1
    exact Matrix.SpecialLinearGroup.toGL_injective h1
  have hKinv : ∀ n, θ (SemidirectProduct.inl n) ∈ C →
      ∀ A, θ (SemidirectProduct.inl (φ A n)) ∈ C := by
    intro n hn A
    obtain ⟨x, hx, rfl⟩ := hlift A
    rw [← conj_inl_eq, map_mul, map_mul, map_inv]
    exact C.mul_mem (C.mul_mem hx hn) (C.inv_mem hx)
  have hK1 : ∃ n : N, n ≠ 1 ∧ θ (SemidirectProduct.inl n) ∈ C := by
    by_contra hK
    have hK' : ∀ n : N, θ (SemidirectProduct.inl n) ∈ C → n = 1 :=
      fun n hn => by_contra fun h => hK ⟨n, h, hn⟩
    apply hCq
    let e := MonoidHom.ofInjective hθ
    let ψ : ↥C →* Matrix.SpecialLinearGroup (Fin 2) F :=
      SemidirectProduct.rightHom.comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hCY))
    have he : ∀ c : ↥C, θ (e.symm (Subgroup.inclusion hCY c)) = c := fun c =>
      congrArg Subtype.val (e.apply_symm_apply (Subgroup.inclusion hCY c))
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have hx : e.symm (Subgroup.inclusion hCY c) =
          SemidirectProduct.inl (e.symm (Subgroup.inclusion hCY c)).left :=
        SemidirectProduct.ext rfl hc
      have h1 : (e.symm (Subgroup.inclusion hCY c)).left = 1 := by
        apply hK'
        rw [← hx, he]
        exact c.2
      apply Subtype.ext
      rw [← he c, hx, h1, map_one, map_one]
      rfl
    have hψs : Function.Surjective ψ := by
      intro A
      obtain ⟨x, hx, rfl⟩ := hlift A
      refine ⟨⟨θ x, hx⟩, ?_⟩
      have h2 : Subgroup.inclusion hCY ⟨θ x, hx⟩ = e x := Subtype.ext rfl
      change (e.symm (Subgroup.inclusion hCY ⟨θ x, hx⟩)).right = x.right
      rw [h2, MulEquiv.symm_apply_apply]
    have hq := isQuasisimple_SL2_of_four (exists_finset_card_four_of_le (F := F) (by omega))
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (MulEquiv.ofBijective ψ ⟨hψinj, hψs⟩)).2 hq
  obtain ⟨n₀, hn₀, hn₀C⟩ := hK1
  have hKall : ∀ m : N, θ (SemidirectProduct.inl m) ∈ C := by
    intro m
    by_cases hm : m = 1
    · rw [hm, map_one, map_one]
      exact C.one_mem
    · obtain ⟨A, hA⟩ := htrans n₀ m hn₀ hm
      rw [← hA]
      exact hKinv n₀ hn₀C A
  have hall : ∀ x, θ x ∈ C := by
    intro x
    obtain ⟨c, hc, hcr⟩ := hlift x.right
    have hx : x = SemidirectProduct.inl (x.left * c.left⁻¹) * c := by
      refine SemidirectProduct.ext ?_ ?_
      · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          map_one, MulAut.one_apply, inv_mul_cancel_right]
      · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul, hcr]
    rw [hx, map_mul]
    exact C.mul_mem (hKall _) hc
  refine le_antisymm hCY ?_
  rintro _ ⟨x, rfl⟩
  exact hall x

end CFSG.Quasithin.H13.NQCat
