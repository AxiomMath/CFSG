module

public import CFSG.Quasithin.Vol2.Ch9Sec3Red

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix
open scoped Pointwise

theorem le_centralizer_of_perfect_of_card_le_four {G : Type} [Group G] [Finite G]
    {V K : Subgroup G} (hV : Nat.card ↥V ≤ 4) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hK : ⁅K, K⁆ = K) : K ≤ Subgroup.centralizer (V : Set G) := by
  classical
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  let φ : ↥K →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hKN)
  have hsolv : Group.IsSolvable (MulAut ↥V) := by
    have h1 : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V)
      (fun a b h => MulEquiv.ext fun x => congrArg (fun p => p x) h)
  have h2 : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  have h3 : Group.IsSolvable ↥φ.range := inferInstance
  have h4 : ∀ k : ↥K, φ k = 1 := by
    intro k
    obtain ⟨m, hm⟩ := h3.solvable
    have h5 := Group.IsPerfect.derivedSeries_eq_top ↥φ.range m
    rw [hm] at h5
    have h6 : (⟨φ k, ⟨k, rfl⟩⟩ : ↥φ.range) ∈ (⊤ : Subgroup ↥φ.range) := Subgroup.mem_top _
    rw [← h5, Subgroup.mem_bot] at h6
    exact congrArg Subtype.val h6
  intro k hk
  have h5 : (⟨k, hKN hk⟩ : ↥(Subgroup.normalizer (V : Set G))) ∈ V.normalizerMonoidHom.ker :=
    MonoidHom.mem_ker.mpr (h4 ⟨k, hk⟩)
  rw [Subgroup.normalizerMonoidHom_ker] at h5
  exact Subgroup.mem_subgroupOf.mp h5

theorem mem_normalizer_centralizer {G : Type} [Group G] {B : Subgroup G} {x : G}
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := by
  have key : ∀ y ∈ Subgroup.normalizer (B : Set G), ∀ w ∈ Subgroup.centralizer (B : Set G),
      y * w * y⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
    intro y hy w hw
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    have hs' : y⁻¹ * s * y ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) s).mp hs
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hw _ hs'
    calc s * (y * w * y⁻¹) = y * ((y⁻¹ * s * y) * w) * y⁻¹ := by group
      _ = y * (w * (y⁻¹ * s * y)) * y⁻¹ := by rw [h2]
      _ = y * w * y⁻¹ * s := by group
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨key x hB w, fun hw => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hB) _ hw
  simpa [mul_assoc] using this

theorem eq_one_of_odd_of_mem {G : Type} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : Nat.Coprime (orderOf x) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

include S in
theorem T_le_normalizer_V1 :
    T ≤ Subgroup.normalizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨S.T_le_normalizer_V ht,
    mem_normalizer_centralizer (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, Setup.T_le_normalizer_L0 ht⟩)⟩

include S in
theorem mem_normalizer_V1_of_mem_N0 {x : G}
    (hx : x ∈ fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨S.L0_le_normalizer_V hx.1,
    mem_normalizer_centralizer hx.2⟩

omit [Finite G] in
theorem T_le_normalizer_N0 :
    T ≤ Subgroup.normalizer ((fsuL0 T L ⊓ Subgroup.normalizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Setup.T_le_normalizer_L0 ht,
    Subgroup.le_normalizer (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, Setup.T_le_normalizer_L0 ht⟩)⟩

include S in
theorem exists_mul_eq_mul_hall {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G))) :
    (∀ a ∈ D, ∀ c ∈ T, ∃ a' ∈ D, ∃ c' ∈ T, c * a = a' * c') ∧
      (∀ a ∈ D, ∀ c ∈ T, ∃ c' ∈ T, ∃ a' ∈ D, a * c = c' * a') := by
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hN₀eq : N₀ = P₀ ⊔ D :=
    le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall S.isSylowTwoOf_T_inf_L0_normalizer hD)
      (sup_le S.isSylowTwoOf_T_inf_L0_normalizer.1 hD.1)
  have hDN : D ≤ Subgroup.normalizer (P₀ : Set G) := hD.1.trans inf_le_right
  have hset1 : (N₀ : Set G) = (D : Set G) * (P₀ : Set G) := by
    rw [hN₀eq, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right D P₀ hDN
  have hset2 : (N₀ : Set G) = (P₀ : Set G) * (D : Set G) := by
    rw [hN₀eq]
    exact Subgroup.coe_mul_of_right_le_normalizer_left P₀ D hDN
  have hTN := T_le_normalizer_N0 (T := T) (L := L)
  refine ⟨fun a ha c hc => ?_, fun a ha c hc => ?_⟩
  · have hca : c * a * c⁻¹ ∈ (N₀ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hTN hc) a).mp (hD.1 ha)
    rw [hset1] at hca
    obtain ⟨a', ha', s, hs, hal⟩ := hca
    have hal' : a' * s = c * a * c⁻¹ := hal
    refine ⟨a', ha', s * c, T.mul_mem hs.1 hc, ?_⟩
    calc c * a = (c * a * c⁻¹) * c := by group
      _ = (a' * s) * c := by rw [← hal']
      _ = a' * (s * c) := by group
  · have hca : c⁻¹ * a * c⁻¹⁻¹ ∈ (N₀ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem hc)) a).mp (hD.1 ha)
    rw [hset2] at hca
    obtain ⟨s, hs, a', ha', hsa⟩ := hca
    have hsa' : s * a' = c⁻¹ * a * c⁻¹⁻¹ := hsa
    refine ⟨c * s, T.mul_mem hc hs.1, a', ha', ?_⟩
    calc a * c = c * (c⁻¹ * a * c⁻¹⁻¹) := by group
      _ = c * (s * a') := by rw [← hsa']
      _ = c * s * a' := by group

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem card_V1_le :
    Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) ≤
      Fintype.card K := by
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  let f : ↥V₁ → K := fun v => Multiplicative.toAdd (e ⟨v, v.2.1⟩) 0 0
  have hf : Function.Injective f := by
    intro v w hvw
    have hv := hc.toAdd_e_eq v.2
    have hw := hc.toAdd_e_eq w.2
    have h1 : e ⟨v, v.2.1⟩ = e ⟨w, w.2.1⟩ := by
      apply Multiplicative.toAdd.injective
      rw [hv, hw]
      exact congrArg (· • !![(1 : K), 0; 0, 0]) hvw
    have h2 := congrArg Subtype.val (e.injective h1)
    exact Subtype.ext h2
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective f hf

theorem V1_ne_bot :
    fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≠ ⊥ := by
  intro hbot
  have hw := hc.symm_mem (e := e) 1
  rw [hbot, Subgroup.mem_bot] at hw
  have h1 : e.symm (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) = 1 :=
    Subtype.ext hw
  have h2 : Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0]) = (1 : Om4.VM K) := by
    rw [← map_one e.symm] at h1
    exact e.symm.injective h1
  have h3 := congrArg (fun X : Om4.VM K => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) 0 0)
    h2
  simp at h3

theorem eq_one_of_odd (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (k : ↥(fsuL0 T L)) (hodd : Odd (orderOf (k : G)))
    (hk : ψ k = 1) : (k : G) = 1 := by
  have h := hc.bar_L0 k
  rw [hk, map_one] at h
  have hC := mem_centralizer_of_bar e _ h
  have hQ : (k : G) ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    S.sup_inf_centralizer_le h37c h38c ⟨Subgroup.mem_sup_left k.2, hC⟩
  exact eq_one_of_odd_of_mem S.isPGroup_Q hQ hodd

variable {D : Subgroup G}

theorem mul_comm_of_mem (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x := by
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  obtain ⟨a, b, hab⟩ := exists_diag_of_mem hdiag hx (hDL hx)
  obtain ⟨a', b', hab'⟩ := exists_diag_of_mem hdiag hy (hDL hy)
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ D :=
    D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)
  have hodd : Odd (orderOf (x * y * x⁻¹ * y⁻¹)) :=
    hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hmem)
  have hψ : ψ (⟨x, hDL hx⟩ * ⟨y, hDL hy⟩ * ⟨x, hDL hx⟩⁻¹ * ⟨y, hDL hy⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab, hab']
    simp only [Prod.mk_mul_mk, Prod.inv_mk, ← diagHom_apply, ← map_inv, ← map_mul]
    have h1 : a * a' * a⁻¹ * a'⁻¹ = 1 := by
      rw [mul_right_comm a a', mul_inv_cancel, one_mul, mul_inv_cancel]
    have h2 : b * b' * b⁻¹ * b'⁻¹ = 1 := by
      rw [mul_right_comm b b', mul_inv_cancel, one_mul, mul_inv_cancel]
    rw [h1, h2, map_one, Prod.mk_one_one]
  have h3 := hc.eq_one_of_odd h37c h38c _ hodd hψ
  have h4 : x * y * x⁻¹ * y⁻¹ = 1 := h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h4, one_mul]

theorem pow_three_eq_one (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    {x : G} (hx : x ∈ D) : x ^ 3 = 1 := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  obtain ⟨a, b, hab⟩ := exists_diag_of_mem hdiag hx (hDL hx)
  have hmem : x ^ 3 ∈ D := D.pow_mem hx 3
  have hodd : Odd (orderOf (x ^ 3)) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hmem)
  have hψ : ψ (⟨x, hDL hx⟩ ^ 3) = 1 := by
    rw [map_pow, hab, Prod.pow_mk, ← diagHom_apply, ← diagHom_apply, ← map_pow, ← map_pow,
      pow_three_eq_one_of_card_four hK4, pow_three_eq_one_of_card_four hK4, map_one,
      Prod.mk_one_one]
  exact hc.eq_one_of_odd h37c h38c _ hodd hψ

theorem isPGroup_three (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) : IsPGroup 3 D :=
  fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hc.pow_three_eq_one h37c h38c h2 hD hdiag x.2)⟩

theorem exists_not_mem_centralizer_V1 (h2 : n = 2)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) :
    ∃ d ∈ D, d ∉ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have : Nontrivial Kˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag ω ω
  refine ⟨d, hdD, fun hdC => hω ?_⟩
  have h1 := (hc.mem_centralizer_V1_iff_diag ⟨d, hdL⟩ ω ω hψd).mp hdC
  have h3 := pow_three_eq_one_of_card_four hK4 ω
  calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
    _ = 1 := by rw [h3, h1, inv_one, one_mul]

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
