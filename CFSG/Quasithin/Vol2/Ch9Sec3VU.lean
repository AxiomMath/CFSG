module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrL
public import CFSG.Quasithin.Vol2.Ch9Lem935

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem exists_eq_commutator_of_fpf {G : Type*} [Group G] {W : Subgroup G} [Finite W] {d : G}
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hfp : ∀ v ∈ W, d * v * d⁻¹ = v → v = 1) :
    ∀ w ∈ W, ∃ x ∈ W, w = x * d * x⁻¹ * d⁻¹ := by
  have hmem : ∀ x ∈ W, x * d * x⁻¹ * d⁻¹ ∈ W := fun x hx => by
    have h1 : d * x⁻¹ * d⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hdW _).mp (W.inv_mem hx)
    have e : x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) := by group
    rw [e]
    exact W.mul_mem hx h1
  let f : ↥W → ↥W := fun x => ⟨x * d * (x : G)⁻¹ * d⁻¹, hmem x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (x : G) * d * (x : G)⁻¹ * d⁻¹ = y * d * (y : G)⁻¹ * d⁻¹ := congrArg Subtype.val hxy
    have h1' : (x : G) * d * (x : G)⁻¹ = y * d * (y : G)⁻¹ := by
      have := congrArg (· * d) h1
      simpa using this
    have h2 : d * ((y : G)⁻¹ * x) * d⁻¹ = (y : G)⁻¹ * x := by
      calc d * ((y : G)⁻¹ * x) * d⁻¹ = (y : G)⁻¹ * (y * d * (y : G)⁻¹) * x * d⁻¹ := by group
        _ = (y : G)⁻¹ * (x * d * (x : G)⁻¹) * x * d⁻¹ := by rw [h1']
        _ = (y : G)⁻¹ * x := by group
    have h3 := hfp _ (W.mul_mem (W.inv_mem y.2) x.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  intro w hw
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
  exact ⟨x, x.2, (congrArg Subtype.val hx).symm⟩

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {D : Subgroup G}

theorem mem_L_of_mem_D (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    {y : G} (hy : y ∈ D)
    (hψy : ψ ⟨y, (hD.1.trans inf_le_left) hy⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ) : y ∈ L := by
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) :=
    le_sup_right.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c)
  obtain ⟨⟨l, hlL0⟩, hl, hψl⟩ := hψy
  have hq := hc.mem_Q_of_psi_eq_one h37c h38c (⟨l, hlL0⟩⁻¹ * ⟨y, hDL hy⟩) (by
    rw [map_mul, map_inv, hψl, inv_mul_cancel])
  have hle : Subgroup.zpowers y ≤ Q ⊔ L := by
    rw [Subgroup.zpowers_le]
    have e' : y = l * (l⁻¹ * y) := by group
    rw [e']
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hl))
      (Subgroup.mem_sup_left hq)
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    exact hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hy)
  exact Vol2.Ch10.SecB.C11AmS.le_of_odd hle hodd
    (B6.isTwoQuotient_of_sup_eq S.isPGroup_Q (sup_le hQL Subgroup.le_normalizer) rfl)
    (Subgroup.mem_zpowers y)

theorem exists_fpf (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) :
    ∃ d ∈ D, d ∈ L ∧ ∀ v ∈ fsuV T I, d * v * d⁻¹ = v → v = 1 := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have : Nontrivial Kˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  have hω' : (ω : K) ≠ 1 := fun h => hω (Units.ext h)
  have hωi : (ω : K)⁻¹ ≠ 1 := fun h => hω' (inv_eq_one.mp h)
  have key : ∀ c x : K, c ≠ 1 → c * x = x → x = 0 := fun c x hc h => by
    by_contra hx
    exact hc ((mul_eq_right₀ hx).mp h)
  have key' : ∀ c x : K, c ≠ 1 → x * c = x → x = 0 := fun c x hc h => by
    by_contra hx
    exact hc ((mul_eq_left₀ hx).mp h)
  have hd1 : diagOf (1 : Kˣ) = 1 := by rw [← diagHom_apply, map_one]
  have hfix : ∀ (d : G) (hdL : d ∈ fsuL0 T L) (v : G) (hv : v ∈ fsuV T I), d * v * d⁻¹ = v →
      Om4.rho (ψ ⟨d, hdL⟩) (e ⟨v, hv⟩) = e ⟨v, hv⟩ := by
    intro d hdL v hv hdv
    have hdv' : d * v * d⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V hdL) v).mp hv
    rw [← hc.e_conj ⟨d, hdL⟩ ⟨v, hv⟩ hdv']
    congr 1
    exact Subtype.ext hdv
  have hzero : ∀ (v : G) (hv : v ∈ fsuV T I),
      Multiplicative.toAdd (e ⟨v, hv⟩) = 0 → v = 1 := by
    intro v hv h0
    have h3 : e ⟨v, hv⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0]
      rfl
    exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h3)
  rcases hc.map_L h37c h38c with hL | hL
  · obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag ω 1
    refine ⟨d, hdD, hc.mem_L_of_mem_D h37 h38 h37c h38c hD hdD (by
      rw [hL, MonoidHom.mem_ker]
      show (ψ ⟨d, _⟩).2 = 1
      rw [hψd, hd1]), fun v hv hdv => ?_⟩
    have h1 := hfix d hdL v hv hdv
    rw [hψd, hd1] at h1
    apply hzero v hv
    ext i j
    have h3 := congrArg
      (fun X : Om4.VM K => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) i j) h1
    simp only [toAdd_rho, mul_mul_transpose_apply, coe_diagOf] at h3
    fin_cases i <;> fin_cases j <;> simp at h3 ⊢ <;>
      first | exact key _ _ hω' h3 | exact key _ _ hωi h3
  · obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag 1 ω
    refine ⟨d, hdD, hc.mem_L_of_mem_D h37 h38 h37c h38c hD hdD (by
      rw [hL, MonoidHom.mem_ker]
      show (ψ ⟨d, _⟩).1 = 1
      rw [hψd, hd1]), fun v hv hdv => ?_⟩
    have h1 := hfix d hdL v hv hdv
    rw [hψd, hd1] at h1
    apply hzero v hv
    ext i j
    have h3 := congrArg
      (fun X : Om4.VM K => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) i j) h1
    simp only [toAdd_rho, mul_mul_transpose_apply, coe_diagOf] at h3
    fin_cases i <;> fin_cases j <;> simp at h3 ⊢ <;>
      first | exact key' _ _ hω' h3 | exact key' _ _ hωi h3

theorem card_conjClosure_ge (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2) :
    2 ^ 4 ≤ Nat.card ↥(conjClosure (fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) L) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set V₂ := conjClosure V₁ L with hV₂
  let w : SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, mul_one, zero_sub]
    exact CharTwo.neg_eq 1⟩
  set E : Matrix (Fin 2) (Fin 2) K := !![(1 : K), 0; 0, 0] with hE
  have hl : ∃ (l : G) (hl : l ∈ L) (N : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2),
      (∀ c : K, Om4.rho (ψ ⟨l, S.L_le_L0 hl⟩) (Multiplicative.ofAdd (c • E)) =
        Multiplicative.ofAdd (c • N)) ∧ N 0 0 = 0 ∧ N i j = 1 ∧ E i j = 0 := by
    rcases hc.map_L h37c h38c with hL | hL
    · obtain ⟨⟨l, hlL0⟩, hl, hψl⟩ := (show ((w, 1) : SpecialLinearGroup (Fin 2) K × _) ∈
          (L.subgroupOf (fsuL0 T L)).map ψ by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
      refine ⟨l, Subgroup.mem_subgroupOf.mp hl, !![0, 0; 1, 0], 1, 0, fun c => ?_, rfl, rfl, rfl⟩
      have e1 : (⟨l, S.L_le_L0 (Subgroup.mem_subgroupOf.mp hl)⟩ : ↥(fsuL0 T L)) = ⟨l, hlL0⟩ := rfl
      rw [e1, hψl]
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
      ext a b
      rw [mul_mul_transpose_apply]
      fin_cases a <;> fin_cases b <;> simp [w, hE]
    · obtain ⟨⟨l, hlL0⟩, hl, hψl⟩ := (show ((1, w) : SpecialLinearGroup (Fin 2) K × _) ∈
          (L.subgroupOf (fsuL0 T L)).map ψ by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
      refine ⟨l, Subgroup.mem_subgroupOf.mp hl, !![0, 1; 0, 0], 0, 1, fun c => ?_, rfl, rfl, rfl⟩
      have e1 : (⟨l, S.L_le_L0 (Subgroup.mem_subgroupOf.mp hl)⟩ : ↥(fsuL0 T L)) = ⟨l, hlL0⟩ := rfl
      rw [e1, hψl]
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
      ext a b
      rw [mul_mul_transpose_apply]
      fin_cases a <;> fin_cases b <;> simp [w, hE]
  obtain ⟨l, hlL, N, i, j, hN, hN0, hNij, hEij⟩ := hl
  have hmem : ∀ c c' : K,
      ((e.symm (Multiplicative.ofAdd (c • E + c' • N)) : ↥(fsuV T I)) : G) ∈ V₂ := by
    intro c c'
    have h1 : e.symm (Multiplicative.ofAdd (c • E + c' • N)) =
        e.symm (Multiplicative.ofAdd (c • E)) * e.symm (Multiplicative.ofAdd (c' • N)) := by
      rw [← map_mul]
      rfl
    have hv := hc.symm_mem (e := e) c'
    set v := e.symm (Multiplicative.ofAdd (c' • E)) with hvdef
    have hlv : l * (v : G) * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V (S.L_le_L0 hlL)) v).mp v.2
    have h2 : e.symm (Multiplicative.ofAdd (c' • N)) = ⟨l * (v : G) * l⁻¹, hlv⟩ := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, hc.e_conj ⟨l, S.L_le_L0 hlL⟩ v hlv, hvdef,
        MulEquiv.apply_symm_apply, hN]
    rw [h1, Subgroup.coe_mul, h2]
    exact V₂.mul_mem (le_conjClosure V₁ L (hc.symm_mem (e := e) c)) (mem_conjClosure hlL hv)
  let f : K × K → ↥V₂ := fun p => ⟨_, hmem p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, c'⟩ ⟨d, d'⟩ hcd
    have h0 : ((e.symm (Multiplicative.ofAdd (c • E + c' • N)) : ↥(fsuV T I)) : G) =
        ((e.symm (Multiplicative.ofAdd (d • E + d' • N)) : ↥(fsuV T I)) : G) :=
      congrArg (fun x : ↥V₂ => (x : G)) hcd
    have h1 : e.symm (Multiplicative.ofAdd (c • E + c' • N)) =
        e.symm (Multiplicative.ofAdd (d • E + d' • N)) := Subtype.ext h0
    have h2 := congrArg Multiplicative.toAdd (e.symm.injective h1)
    rw [toAdd_ofAdd, toAdd_ofAdd] at h2
    have h00 := congrFun (congrFun h2 0) 0
    have hij := congrFun (congrFun h2 i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hN0, hNij, hEij, mul_zero,
      add_zero, zero_add, mul_one] at h00 hij
    simp only [hE, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_one] at h00
    exact Prod.ext h00 hij
  have h16 : Nat.card (K × K) = 2 ^ 4 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, hK4]
    norm_num
  rw [← h16]
  exact Nat.card_le_card_of_injective f hf

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
