module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenApi

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_of_card_seven {X Y : Type*} [Group X] [Finite X] [MulAction X Y] [Finite Y]
    (hY : Nat.card Y = 7) (P N : Subgroup X) (hP : Odd P.index) (hN : N.index = 12)
    (hPfix : ∀ p ∈ P, ∀ y : Y, p • y = y) (z : Y) (hNz : ∀ n ∈ N, n • z = z) :
    ∃ y : Y, ∀ x : X, x • y = y := by
  classical
  by_contra hno
  push Not at hno
  have hidx : ∀ y : Y, Odd (MulAction.stabilizer X y).index := fun y => by
    have hle : P ≤ MulAction.stabilizer X y := fun p hp =>
      (MulAction.mem_stabilizer_iff).mpr (hPfix p hp y)
    exact Odd.of_dvd_nat hP (Subgroup.index_dvd_of_le hle)
  have h3 : ∀ y : Y, 3 ≤ (MulAction.stabilizer X y).index := by
    intro y
    have hodd := hidx y
    have hne : (MulAction.stabilizer X y).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      obtain ⟨x, hx⟩ := hno y
      exact hx ((MulAction.mem_stabilizer_iff).mp (h1 ▸ Subgroup.mem_top x))
    rw [Nat.odd_iff] at hodd
    omega
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Fintype (MulAction.orbitRel.Quotient X Y) := Fintype.ofFinite _
  have hsum : Nat.card Y = ∑ ω : MulAction.orbitRel.Quotient X Y,
      (MulAction.stabilizer X (Quotient.out ω)).index := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer X Y), Nat.card_sigma]
    rfl
  have hle3 : 3 * Fintype.card (MulAction.orbitRel.Quotient X Y) ≤ 7 := by
    calc 3 * Fintype.card (MulAction.orbitRel.Quotient X Y)
        = ∑ _ω : MulAction.orbitRel.Quotient X Y, 3 := by simp [mul_comm]
      _ ≤ ∑ ω : MulAction.orbitRel.Quotient X Y,
          (MulAction.stabilizer X (Quotient.out ω)).index :=
        Finset.sum_le_sum fun ω _ => h3 _
      _ = 7 := by rw [← hsum, hY]
  have hcard_odd : Odd (Fintype.card (MulAction.orbitRel.Quotient X Y)) := by
    have h7 : Odd (∑ ω : MulAction.orbitRel.Quotient X Y,
        (MulAction.stabilizer X (Quotient.out ω)).index) := by
      rw [← hsum, hY]; decide
    rw [Finset.odd_sum_iff_odd_card_odd] at h7
    simpa [Finset.filter_true_of_mem fun ω _ => hidx (Quotient.out ω)] using h7
  have hcard1 : Fintype.card (MulAction.orbitRel.Quotient X Y) = 1 := by
    rw [Nat.odd_iff] at hcard_odd
    omega
  obtain ⟨ω₀, hω₀⟩ := Fintype.card_eq_one_iff.mp hcard1
  have horb : MulAction.orbit X z = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hy : (Quotient.mk'' y : MulAction.orbitRel.Quotient X Y) = Quotient.mk'' z :=
      (hω₀ _).trans (hω₀ _).symm
    exact MulAction.orbitRel_apply.mp (Quotient.exact' hy)
  have h7 : (MulAction.stabilizer X z).index = 7 := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, hY]
  have hdvd : (MulAction.stabilizer X z).index ∣ N.index :=
    Subgroup.index_dvd_of_le fun n hn => (MulAction.mem_stabilizer_iff).mpr (hNz n hn)
  rw [h7, hN] at hdvd
  omega

theorem Sit813.exists_ne_one_mem_centralizer_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    ∃ z ∈ V, z ≠ 1 ∧ ∀ n ∈ oTwoMod (cGrp H T) K, n * z = z * n := by
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hTp : IsPGroup 2 T := hyp.sylow.isPGroup
  have hVT : V ≤ T := le_of_isCalH hV h.calH0.1 hyp.sylow
  have hVbot : V ≠ ⊥ := by
    intro hb
    have h8 := h.card_V_eq_eight
    rw [hb, Subgroup.card_bot] at h8
    omega
  haveI : Group.IsNilpotent ↥T := hTp.isNilpotent
  haveI hnormal : (V.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr h.le_normalizer_T
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hVbot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, hb, Subgroup.map_bot]
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hcV, hcZ⟩ := Subgroup.mem_inf.mp hc
  have hzV : (c : G) ∈ V := hcV
  have hzT : (c : G) ∈ T := c.2
  have hzC : ∀ y ∈ T, y * (c : G) = (c : G) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨y, hy⟩)
  have hz1 : (c : G) ≠ 1 := fun hc' => hc1 (Subtype.ext (Subtype.ext hc'))
  have hzO : (c : G) ∈ omegaOneCenterOf T := mem_omegaOneCenterOf hzT hzC (hV.2 _ hzV)
  have hβ : IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K) :=
    h.isSylowIn_oTwoMod_of_isSylowIn_inf h.concl813.t_sylow
  refine ⟨(c : G), hzV, hz1, fun n hn => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (h.oTwoMod_le_centralizer_omegaOneCenter hβ hn) _
    hzO).symm

@[instance_reducible] private def conjActNonone (V K : Subgroup G) :
    MulAction ↥(K ⊓ normalizer (V : Set G)) {v : G // v ∈ V ∧ v ≠ 1} where
  smul k y :=
    ⟨(k : G) * (y : G) * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp k.2).2 (y : G)).mp y.2.1,
      fun h1 => y.2.2 (by
        have h2 := congrArg (fun x => (k : G)⁻¹ * x * (k : G)) h1
        simpa [mul_assoc] using h2)⟩
  one_smul y := Subtype.ext (by
    change ((1 : ↥(K ⊓ normalizer (V : Set G))) : G) * (y : G) *
        ((1 : ↥(K ⊓ normalizer (V : Set G))) : G)⁻¹ = (y : G)
    simp)
  mul_smul k₁ k₂ y := Subtype.ext (by
    change ((k₁ * k₂ : ↥(K ⊓ normalizer (V : Set G))) : G) * (y : G) *
        ((k₁ * k₂ : ↥(K ⊓ normalizer (V : Set G))) : G)⁻¹ =
      (k₁ : G) * ((k₂ : G) * (y : G) * (k₂ : G)⁻¹) * (k₁ : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem Sit813.exists_fixed_vector {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (P : Subgroup G) (hPK : P ≤ K) (hPodd : Odd (P.relIndex K))
    (hPV : ∀ p ∈ P, ∀ v ∈ V, p * v = v * p) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ k ∈ K ⊓ normalizer (V : Set G), k * v * k⁻¹ = v := by
  classical
  letI : MulAction ↥(K ⊓ normalizer (V : Set G)) {v : G // v ∈ V ∧ v ≠ 1} := conjActNonone V K
  have hPK₁ : P ≤ K ⊓ normalizer (V : Set G) := fun p hp =>
    Subgroup.mem_inf.mpr ⟨hPK hp, Subgroup.mem_normalizer_fintype fun n hn => by
      rw [hPV p hp n hn]
      simpa using hn⟩
  have hNK₁ : oTwoMod (cGrp H T) K ≤ K ⊓ normalizer (V : Set G) := h.oTwoMod_le_inf
  have hK₁K : K ⊓ normalizer (V : Set G) ≤ K := inf_le_left
  have hidx5 : (K ⊓ normalizer (V : Set G)).relIndex K = 5 := h.concl813.d_index
  have hN60 : (oTwoMod (cGrp H T) K).relIndex K = 60 := h.kn4
  have hN12 : (oTwoMod (cGrp H T) K).relIndex (K ⊓ normalizer (V : Set G)) = 12 := by
    have h1 := Subgroup.relIndex_mul_relIndex (H := oTwoMod (cGrp H T) K)
      (K := K ⊓ normalizer (V : Set G)) (L := K) hNK₁ hK₁K
    rw [hidx5, hN60] at h1
    omega
  have hPodd' : Odd (P.relIndex (K ⊓ normalizer (V : Set G))) := by
    have h1 := Subgroup.relIndex_mul_relIndex (H := P) (K := K ⊓ normalizer (V : Set G))
      (L := K) hPK₁ hK₁K
    exact Odd.of_dvd_nat hPodd (Dvd.intro _ h1)
  have hY : Nat.card {v : G // v ∈ V ∧ v ≠ 1} = 7 := by
    have h8 := h.card_V_eq_eight
    let e : {v : G // v ∈ V ∧ v ≠ 1} ≃ {v : ↥V // v ≠ 1} :=
      { toFun := fun y => ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
        invFun := fun y => ⟨y.1.1, y.1.2, fun h => y.2 (Subtype.ext h)⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    rw [Nat.card_congr e]
    haveI : Fintype ↥V := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at h8 ⊢
    have h9 : Fintype.card {v : ↥V // v ≠ 1} = Fintype.card ↥V - 1 := by simp
    omega
  obtain ⟨z, hzV, hz1, hzN⟩ := h.exists_ne_one_mem_centralizer_oTwoMod
  obtain ⟨y, hy⟩ := exists_fixed_of_card_seven (X := ↥(K ⊓ normalizer (V : Set G)))
    (Y := {v : G // v ∈ V ∧ v ≠ 1}) hY (P.subgroupOf (K ⊓ normalizer (V : Set G)))
    ((oTwoMod (cGrp H T) K).subgroupOf (K ⊓ normalizer (V : Set G))) hPodd'
    hN12 (fun p hp y => by
      refine Subtype.ext ?_
      change (p : G) * (y : G) * (p : G)⁻¹ = (y : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hPV p hp y y.2.1))
    ⟨z, hzV, hz1⟩ (fun n hn => by
      refine Subtype.ext ?_
      change (n : G) * z * (n : G)⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr (hzN n hn))
  refine ⟨y.1, y.2.1, y.2.2, fun k hk => ?_⟩
  exact congrArg Subtype.val (hy ⟨k, hk⟩)

end CFSG.LocalAnalysis.WeakClosure81

end
