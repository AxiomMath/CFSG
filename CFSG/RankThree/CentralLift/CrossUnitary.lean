module

public import CFSG.RankThree.CentralLift.CrossUnitaryThree
public import CFSG.RankThree.CentralLift.CrossSymplectic
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.CentralLiftU.UnitaryTriangular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherBruhat

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (fullPosEquiv fullPosEquiv_apply
  exists_mem_uBruhatCell uBruhatCell isLinePerm_weylMat weylPerm_one)
open CFSG.RankThree.CentralLiftU (UHyp TorusHyp liftWeylU sLift weylHomU isLinePerm_weylHomU
  weylHomU_surjective ker_weylHomU normal_subgroupOf_liftWeylU sLift_mul_self_mem
  weylPerm_injective heisUpper heisLower heisUMat heisLMat heisUMat_mul heisLMat_mul
  isPGroup_hypUnitriangular gramJ3 liftSubgroup_mono simpleKerU simpleKerU_le rhoLift iotaLift
  kappaLift ne_succ_of_lt xPlusEven xMinusEven xPlusOdd xMinusOdd xPlusEven_mem_liftU
  xPlusOdd_mem_liftU torusEven torusOdd torusHyp_even torusHyp_odd
  odd_unitary_higher_cross_characteristic_central_prime_triangular_factorization_even
  odd_unitary_higher_cross_characteristic_central_prime_triangular_factorization_odd)
open CFSG.LieType.CentralExt (liftSubgroup)
open scoped Pointwise

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem eq_one_of_isLinePerm_of_blockTriangular {r ε : ℕ} {σ : Equiv.Perm (HypIndex r ε)}
    {M : Matrix (HypIndex r ε) (HypIndex r ε) K} (hσ : IsLinePerm σ M)
    (hM : M.BlockTriangular fullPos) : σ = 1 := by
  have hle : ∀ x, fullPosEquiv (σ x) ≤ fullPosEquiv x := by
    intro x
    by_contra hlt
    apply hσ.apply_ne_zero x
    refine hM ?_
    rw [not_le, Fin.lt_def, fullPosEquiv_apply, fullPosEquiv_apply] at hlt
    exact hlt
  have h1 : (fullPosEquiv.symm.trans σ).trans fullPosEquiv = 1 :=
    LinearRoots.perm_eq_one_of_forall_le fun a => by
      have := hle (fullPosEquiv.symm a)
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using this
  ext x
  have h2 := congrArg (fun τ : Equiv.Perm (Fin (2 * r + ε)) => τ (fullPosEquiv x)) h1
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] at h2
  rw [Equiv.Perm.one_apply, fullPosEquiv.injective h2]

theorem blockTriangular_of_isLinePerm_one {r ε : ℕ} {M : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hM : IsLinePerm 1 M) : M.BlockTriangular fullPos := by
  intro i j hij
  refine hM.apply_eq_zero ?_
  rw [Equiv.Perm.one_apply]
  rintro rfl
  exact lt_irrefl _ hij

section Hyp

variable (h : UnitaryFieldData ℓ f K) {r ε : ℕ} {R : Type*} [Group R] [Finite R]
  {π : R →* hypSU h r ε} {c : K} {hc : c ∈ h.traceZero} {hc0 : c ≠ 0} {H : Subgroup R}

theorem weylHomU_eq_one_of_mem_hypBorel (hS : UHyp h π) (hT : TorusHyp h π hc hc0 H)
    (hε : ε ≤ 1) (n : liftWeylU h π hc hc0 H) (hn : π n ∈ hypBorel h r ε) :
    weylHomU h hS hc hc0 hT n = 1 := by
  have h1 := eq_one_of_isLinePerm_of_blockTriangular (isLinePerm_weylHomU h hS hc hc0 hT n)
    (blockTriangular_of_mem_hypBorel h hε hn)
  refine Subtype.ext (weylPerm_injective r ε ?_)
  rw [h1]
  exact weylPerm_one.symm

theorem sup_map_eq_top_hyp (hS : UHyp h π) (hT : TorusHyp h π hc hc0 H) (hε : ε ≤ 1)
    {B : Subgroup R} (hBmap : B.map π = hypBorel h r ε) :
    B.map π ⊔ (liftWeylU h π hc hc0 H).map π = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_uBruhatCell h hε hc hc0 g
  obtain ⟨n, hn⟩ := weylHomU_surjective h hS hc hc0 hT w
  have hσn := isLinePerm_weylHomU h hS hc hc0 hT n
  rw [hn] at hσn
  have hσw : IsLinePerm (CFSG.ClassicalGroups.UnitaryFlag.weylPerm (ε := ε)
      (w : Equiv.Perm (Fin r ⊕ Fin r)))
      (((weylElt (ε := ε) h hc hc0 w.2 : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [coe_weylElt]
    exact isLinePerm_weylMat h hc0 _
  have hd : (weylElt (ε := ε) h hc hc0 w.2)⁻¹ * π n ∈ hypBorel h r ε := by
    refine mem_hypBorel_of_blockTriangular h (blockTriangular_of_isLinePerm_one ?_)
    have hprod := (hσw.inv).mul hσn
    rw [inv_mul_cancel] at hprod
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    exact hprod
  have he : weylElt (ε := ε) h hc hc0 w.2 =
      π n * ((weylElt (ε := ε) h hc hc0 w.2)⁻¹ * π n)⁻¹ := by group
  refine mul_mem (mul_mem (Subgroup.mem_sup_left (hBmap ▸ hb₁)) ?_)
    (Subgroup.mem_sup_left (hBmap ▸ hb₂))
  rw [he]
  exact mul_mem (Subgroup.mem_sup_right ⟨n, n.2, rfl⟩)
    (inv_mem (Subgroup.mem_sup_left (hBmap ▸ hd)))

omit [Field K] in
theorem isPerfect_hypSU {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2)
    (hn : 3 ≤ 2 * r + ε) : Group.IsPerfect (hypSU h r ε) := by
  have : Group.IsPerfect (sesqSpecialUnitaryGroup (hypForm h r ε)) :=
    unitary_perfect h (hypForm_isSymm h) (hypForm_separatingLeft h) (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega) (fun h32 => by
        have h2 : ℓ ^ f = 2 := congrArg Prod.snd h32
        have hodd : Odd (ℓ ^ f) := (h.prime.odd_of_ne_two hℓ).pow
        rw [h2] at hodd
        exact absurd hodd (by decide))
  obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h (B := hypForm h r ε)
    (Pi.basisFun K (HypIndex r ε)) (G := hypGram r ε K) fun i j => by
      rw [Pi.basisFun_apply, Pi.basisFun_apply]
      exact gramForm_single h _ i j
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end Hyp

section Heis

variable (h : UnitaryFieldData ℓ f K)

theorem heisUMat_zero : heisUMat h 0 0 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisUMat]

theorem heisLMat_zero : heisLMat h 0 0 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisLMat]

theorem one_mem_heisUpper : (1 : gramSU h (gramJ3 K)) ∈ heisUpper h :=
  ⟨0, 0, by simp, by rw [heisUMat_zero]; rfl⟩

theorem one_mem_heisLower : (1 : gramSU h (gramJ3 K)) ∈ heisLower h :=
  ⟨0, 0, by simp, by rw [heisLMat_zero]; rfl⟩

theorem heisUpper_mul_mem {X Y : gramSU h (gramJ3 K)} (hX : X ∈ heisUpper h)
    (hY : Y ∈ heisUpper h) : X * Y ∈ heisUpper h := by
  obtain ⟨u, v, huv, hXm⟩ := hX
  obtain ⟨u', v', huv', hYm⟩ := hY
  refine ⟨u + u', v + v' - u * h.bar u', ?_, ?_⟩
  · rw [map_sub, map_add, map_add, map_mul, UnitaryFieldData.bar_bar]
    linear_combination huv + huv'
  · rw [Subgroup.coe_mul, Units.val_mul, hXm, hYm, heisUMat_mul]

theorem heisLower_mul_mem {X Y : gramSU h (gramJ3 K)} (hX : X ∈ heisLower h)
    (hY : Y ∈ heisLower h) : X * Y ∈ heisLower h := by
  obtain ⟨z, t, hzt, hXm⟩ := hX
  obtain ⟨z', t', hzt', hYm⟩ := hY
  refine ⟨z + z', t + t' - h.bar z * z', ?_, ?_⟩
  · rw [map_sub, map_add, map_add, map_mul, UnitaryFieldData.bar_bar]
    linear_combination hzt + hzt'
  · rw [Subgroup.coe_mul, Units.val_mul, hXm, hYm, heisLMat_mul]

theorem heisUpper_inv_mem {X : gramSU h (gramJ3 K)} (hX : X ∈ heisUpper h) :
    X⁻¹ ∈ heisUpper h := by
  obtain ⟨u, v, huv, hXm⟩ := hX
  refine ⟨-u, -v - u * h.bar u, ?_, ?_⟩
  · rw [map_sub, map_neg, map_neg, map_mul, UnitaryFieldData.bar_bar]
    linear_combination -huv
  · rw [Subgroup.coe_inv, Matrix.coe_units_inv, hXm]
    refine Matrix.inv_eq_right_inv ?_
    rw [heisUMat_mul, map_neg, mul_neg, sub_neg_eq_add, add_neg_cancel]
    rw [show v + (-v - u * h.bar u) + u * h.bar u = 0 by ring, heisUMat_zero]

theorem heisLower_inv_mem {X : gramSU h (gramJ3 K)} (hX : X ∈ heisLower h) :
    X⁻¹ ∈ heisLower h := by
  obtain ⟨z, t, hzt, hXm⟩ := hX
  refine ⟨-z, -t - z * h.bar z, ?_, ?_⟩
  · rw [map_sub, map_neg, map_neg, map_mul, UnitaryFieldData.bar_bar]
    linear_combination -hzt
  · rw [Subgroup.coe_inv, Matrix.coe_units_inv, hXm]
    refine Matrix.inv_eq_right_inv ?_
    rw [heisLMat_mul, mul_neg, sub_neg_eq_add, add_neg_cancel]
    rw [show t + (-t - z * h.bar z) + h.bar z * z = 0 by ring, heisLMat_zero]

end Heis

section Assembly

variable (h : UnitaryFieldData ℓ f K) {r ε : ℕ} {R : Type*} [Group R] [Finite R]
  {π : R →* hypSU h r ε} {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {H : Subgroup R}

theorem hyp_cross_splitting_of_triangular (hℓ : Odd ℓ) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center R) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpk : IsPGroup p π.ker) (hT : TorusHyp h π hc hc0 H)
    (hBmem : ∀ x : R, x ∈ liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H ↔
      ∃ u ∈ liftSubgroup ℓ π (hypUnitriangular h r ε), ∃ y ∈ H, x = u * y)
    (hBmap : (liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H).map π = hypBorel h r ε)
    (hBinj : Function.Injective
      (π.comp (liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H).subtype))
    (Xp Xm : Fin r → Subgroup R)
    (hXpU : ∀ i, Xp i ≤ liftSubgroup ℓ π (hypUnitriangular h r ε))
    (hfact : ∀ i (x : R), x ∈ liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H ↔
      ∃ x' ∈ Xp i, ∃ u ∈ liftSubgroup ℓ π (simpleKerU h r ε i), ∃ y ∈ H, x = x' * u * y)
    (hnorm : ∀ i, sLift h π hc hc0 i ∈
      Subgroup.normalizer (liftSubgroup ℓ π (simpleKerU h r ε i) : Set R))
    (hrew : ∀ i, ∀ x ∈ Xp i, x ≠ 1 →
      ∃ y ∈ Xm i, ∃ z ∈ H, ∃ x' ∈ Xp i, x * sLift h π hc hc0 i = y * z * x')
    (hsign : ∀ v ∈ liftWeylU h π hc hc0 H, ∀ i,
      (∀ x ∈ Xp i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r ε)) ∨
        ∀ x ∈ Xm i, v * x * v⁻¹ ∈ liftSubgroup ℓ π (hypUnitriangular h r ε)) :
    (∃! s : hypSU h r ε →* R, π.comp s = MonoidHom.id _) ∧
      ∀ s : hypSU h r ε →* R, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* R, ∀ c g, e (c, g) = (c : R) * g := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hBset : ((liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H : Subgroup R) : Set R) =
      (liftSubgroup ℓ π (hypUnitriangular h r ε) : Set R) * (H : Set R) := by
    ext x
    rw [SetLike.mem_coe, hBmem x]
    constructor
    · rintro ⟨u, hu, y, hy, rfl⟩
      exact ⟨u, hu, y, hy, rfl⟩
    · rintro ⟨u, hu, y, hy, rfl⟩
      exact ⟨u, hu, y, hy, rfl⟩
  have hInj : Set.InjOn π
      ((liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H : Subgroup R) : Set R) :=
    fun x hx y hy hxy => congrArg Subtype.val (hBinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfact' : ∀ i, ((liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H : Subgroup R) : Set R) =
      (Xp i : Set R) * (liftSubgroup ℓ π (simpleKerU h r ε i) : Set R) * (H : Set R) := by
    intro i
    ext x
    rw [SetLike.mem_coe, hfact i x]
    constructor
    · rintro ⟨x', hx', u, hu, y, hy, rfl⟩
      exact ⟨_, ⟨x', hx', u, hu, rfl⟩, y, hy, rfl⟩
    · rintro ⟨_, ⟨x', hx', u, hu, rfl⟩, y, hy, rfl⟩
      exact ⟨x', hx', u, hu, y, hy, rfl⟩
  have hconj : ∀ i, ∀ u ∈ liftSubgroup ℓ π (simpleKerU h r ε i),
      (sLift h π hc hc0 i)⁻¹ * u * sLift h π hc hc0 i ∈
        liftSubgroup ℓ π (hypUnitriangular h r ε) := by
    intro i u hu
    have hn' : (sLift h π hc hc0 i)⁻¹ ∈
        Subgroup.normalizer (liftSubgroup ℓ π (simpleKerU h r ε i) : Set R) := inv_mem (hnorm i)
    have h1 := (Subgroup.mem_normalizer_iff.1 hn' u).1 hu
    rw [inv_inv] at h1
    exact liftSubgroup_mono hcen (isPGroup_hypUnitriangular hε) (simpleKerU_le i) h1
  have hrew' : ∀ i, ∀ x ∈ Xp i, x ≠ 1 → x * sLift h π hc hc0 i ∈
      (Xm i : Set R) * (H : Set R) * (Xp i : Set R) := by
    intro i x hx hx1
    obtain ⟨y, hy, z, hz, x', hx', he⟩ := hrew i x hx hx1
    rw [he]
    exact ⟨_, ⟨y, hy, z, hz, rfl⟩, x', hx', rfl⟩
  have hBN : ∀ n ∈ liftWeylU h π hc hc0 H,
      π n ∈ (liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H).map π → n ∈ H := by
    intro n hn hnB
    rw [hBmap] at hnB
    have h1 := weylHomU_eq_one_of_mem_hypBorel h hS hT hε ⟨n, hn⟩ hnB
    have h2 : (⟨n, hn⟩ : liftWeylU h π hc hc0 H) ∈ (weylHomU h hS hc hc0 hT).ker := h1
    rw [ker_weylHomU h hS hc hc0 hT] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  obtain ⟨-, -, σ, hσ⟩ :=
    CFSG.RankThree.CentralExtension.central_extension_faithful_bruhat_lift_splitting π hcen
      hBset hInj (normal_subgroupOf_liftWeylU h hS hc hc0 hT) (sLift h π hc hc0) rfl
      (fun i => by rw [pow_two]; exact sLift_mul_self_mem h hc hc0 hT i) Xp Xm
      (fun i => liftSubgroup ℓ π (simpleKerU h r ε i)) hXpU hfact' hconj hrew' hsign hBN
      (sup_map_eq_top_hyp h hS hT hε hBmap)
  have : Group.IsPerfect (hypSU h r ε) := isPerfect_hypSU h hℓ2 hn
  exact ⟨⟨σ, hσ, fun σ' hσ' => section_eq_of_forall π hcen (fun δ hδ =>
    eq_one_of_isPerfect_of_mem_center δ fun x => hcen (hδ x)) hσ' hσ⟩,
    fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hcen hs⟩

end Assembly

section Parity

variable (h : UnitaryFieldData ℓ f K) {r : ℕ} {R : Type*} [Group R] [Finite R]

theorem hyp_even_cross_splitting (hℓ : Odd ℓ) (hr : 2 ≤ r) (π : R →* hypSU h r 0) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center R) (hpk : IsPGroup p π.ker) :
    (∃! s : hypSU h r 0 →* R, π.comp s = MonoidHom.id _) ∧
      ∀ s : hypSU h r 0 →* R, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* R, ∀ c g, e (c, g) = (c : R) * g := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.finite
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨-, -, hBmem, hBmap, hBinj, hi⟩ :=
    odd_unitary_higher_cross_characteristic_central_prime_triangular_factorization_even h hℓ hr
      hc hc0 π hp hp3 hpℓ hπ hcen hpk
  let Xp : Fin r → Subgroup R := fun i => if hi : i.val + 1 < r then
      ((rhoLift h π (ne_succ_of_lt hi)).comp LinearRoots.uSLHom).range
    else ((iotaLift h π hc hc0 i).comp LinearRoots.uSLHom).range
  let Xm : Fin r → Subgroup R := fun i => if hi : i.val + 1 < r then
      ((rhoLift h π (ne_succ_of_lt hi)).comp vSLHom).range
    else ((iotaLift h π hc hc0 i).comp vSLHom).range
  have hXp : ∀ i x, x ∈ Xp i ↔ x ∈ xPlusEven h hc hc0 π i := by
    intro i x
    simp only [Xp, xPlusEven]
    split_ifs with hi
    · exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
    · exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hXm : ∀ i x, x ∈ Xm i ↔ x ∈ xMinusEven h hc hc0 π i := by
    intro i x
    simp only [Xm, xMinusEven]
    split_ifs with hi
    · exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
    · exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  exact hyp_cross_splitting_of_triangular h hc hc0 hℓ (by norm_num) (by omega) hπ hcen hp hp3
    hpk (torusHyp_even h hS hc hc0) hBmem hBmap hBinj Xp Xm
    (fun i x hx => xPlusEven_mem_liftU hS hc hc0 ((hXp i x).1 hx))
    (fun i x => by simp only [hXp]; exact (hi i).2.2.1 x) (fun i => (hi i).2.2.2.1)
    (fun i x hx hx1 => by
      obtain ⟨y, hy, z, hz, x', hx', he⟩ := (hi i).2.2.2.2.2.1 x ((hXp i x).1 hx) hx1
      exact ⟨y, (hXm i y).2 hy, z, hz, x', (hXp i x').2 hx', he⟩)
    (fun v hv i => by
      rcases (hi i).2.2.2.2.2.2 v hv with hl | hl
      · exact Or.inl fun x hx => hl x ((hXp i x).1 hx)
      · exact Or.inr fun x hx => hl x ((hXm i x).1 hx))

theorem hyp_odd_cross_splitting (hℓ : Odd ℓ) (hr : 2 ≤ r) (π : R →* hypSU h r 1) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center R) (hpk : IsPGroup p π.ker) :
    (∃! s : hypSU h r 1 →* R, π.comp s = MonoidHom.id _) ∧
      ∀ s : hypSU h r 1 →* R, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* R, ∀ c g, e (c, g) = (c : R) * g := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.finite
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨-, -, hBmem, hBmap, hBinj, hi⟩ :=
    odd_unitary_higher_cross_characteristic_central_prime_triangular_factorization_odd h hℓ hr
      hc hc0 π hp hp3 hpℓ hπ hcen hpk
  let HU : Subgroup (gramSU h (gramJ3 K)) :=
    { carrier := heisUpper h
      mul_mem' := fun hx hy => heisUpper_mul_mem h hx hy
      one_mem' := one_mem_heisUpper h
      inv_mem' := fun hx => heisUpper_inv_mem h hx }
  let HL : Subgroup (gramSU h (gramJ3 K)) :=
    { carrier := heisLower h
      mul_mem' := fun hx hy => heisLower_mul_mem h hx hy
      one_mem' := one_mem_heisLower h
      inv_mem' := fun hx => heisLower_inv_mem h hx }
  let Xp : Fin r → Subgroup R := fun i => if hi : i.val + 1 < r then
      ((rhoLift h π (ne_succ_of_lt hi)).comp LinearRoots.uSLHom).range
    else HU.map (kappaLift h π i)
  let Xm : Fin r → Subgroup R := fun i => if hi : i.val + 1 < r then
      ((rhoLift h π (ne_succ_of_lt hi)).comp vSLHom).range
    else HL.map (kappaLift h π i)
  have hXp : ∀ i x, x ∈ Xp i ↔ x ∈ xPlusOdd h π i := by
    intro i x
    simp only [Xp, xPlusOdd]
    split_ifs with hi
    · exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
    · exact Iff.rfl
  have hXm : ∀ i x, x ∈ Xm i ↔ x ∈ xMinusOdd h π i := by
    intro i x
    simp only [Xm, xMinusOdd]
    split_ifs with hi
    · exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
    · exact Iff.rfl
  exact hyp_cross_splitting_of_triangular h hc hc0 hℓ le_rfl (by omega) hπ hcen hp hp3
    hpk (torusHyp_odd h hS hc hc0) hBmem hBmap hBinj Xp Xm
    (fun i x hx => xPlusOdd_mem_liftU hS ((hXp i x).1 hx))
    (fun i x => by simp only [hXp]; exact (hi i).2.2.1 x) (fun i => (hi i).2.2.2.1)
    (fun i x hx hx1 => by
      obtain ⟨y, hy, z, hz, x', hx', he⟩ := (hi i).2.2.2.2.2.1 x ((hXp i x).1 hx) hx1
      exact ⟨y, (hXm i y).2 hy, z, hz, x', (hXp i x').2 hx', he⟩)
    (fun v hv i => by
      rcases (hi i).2.2.2.2.2.2 v hv with hl | hl
      · exact Or.inl fun x hx => hl x ((hXp i x).1 hx)
      · exact Or.inr fun x hx => hl x ((hXm i x).1 hx))

end Parity

theorem splitting_of_mulEquiv {S S' E : Type*} [Group S] [Group S'] [Group E] (e : S ≃* S')
    {π : E →* S} (hC : π.ker ≤ Subgroup.center E)
    (h' : ∃! s' : S' →* E, (e.toMonoidHom.comp π).comp s' = MonoidHom.id _) :
    (∃! s : S →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : S →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  obtain ⟨s', hs', huniq⟩ := h'
  have hs'x : ∀ x, e (π (s' x)) = x := fun x => DFunLike.congr_fun hs' x
  refine ⟨⟨s'.comp e.toMonoidHom, MonoidHom.ext fun x => e.injective ?_, fun t ht => ?_⟩,
    fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hC hs⟩
  · change e (π (s' (e x))) = e x
    rw [hs'x]
  · have htx : ∀ x, π (t x) = x := fun x => DFunLike.congr_fun ht x
    have h1 := huniq (t.comp e.symm.toMonoidHom) (MonoidHom.ext fun y => by
      change e (π (t (e.symm y))) = y
      rw [htx, MulEquiv.apply_symm_apply])
    refine MonoidHom.ext fun x => ?_
    have h2 := DFunLike.congr_fun h1 (e x)
    change t (e.symm (e x)) = s' (e x) at h2
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2

theorem unitary_cross_splitting {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) {V : Type*} [AddCommGroup V]
    [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : 3 ≤ Module.finrank K V) {E : Type*} [Group E] [Finite E]
    (π : E →* sesqSpecialUnitaryGroup B) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∃! s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  by_cases h3 : Module.finrank K V = 3
  · exact unitary_three_cross_splitting hp hp3 h hℓodd hB hBl h3 π hπ hC hCp
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨r, ε, hε, hr, hn⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ 2 ≤ r ∧ Module.finrank K V = 2 * r + ε :=
    ⟨Module.finrank K V / 2, Module.finrank K V % 2, by omega, by omega, by omega⟩
  obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl hn
  obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h w hw
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  refine splitting_of_mulEquiv e hC ?_
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exact (hyp_even_cross_splitting h hℓodd hr (e.toMonoidHom.comp π) hp hp3 hpℓ
      (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ hCp)).1
  · exact (hyp_odd_cross_splitting h hℓodd hr (e.toMonoidHom.comp π) hp hp3 hpℓ
      (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ hCp)).1

end CFSG.RankThree.CentralLift
