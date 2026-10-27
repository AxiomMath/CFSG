module

public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.Walter.ReeOrder.JTMain

public noncomputable section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open scoped MatrixGroups Pointwise

theorem three_pow_odd_mod_sixteen (a : ℕ) :
    3 ^ (2 * a + 1) % 16 = 3 ∨ 3 ^ (2 * a + 1) % 16 = 11 := by
  induction a with
  | zero => left; rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem card_reeGamma_mod_sixteen (a : ℕ) :
    (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1) % 16 = 8 := by
  have hq1 : 1 ≤ 3 ^ (2 * a + 1) := Nat.one_le_pow _ _ (by norm_num)
  rcases three_pow_odd_mod_sixteen a with h | h
  · have h3 : (3 ^ (2 * a + 1)) ^ 3 % 16 = 11 := by rw [Nat.pow_mod, h]
    have h1 : (3 ^ (2 * a + 1) - 1) % 16 = 2 := by omega
    have h4 : ((3 ^ (2 * a + 1)) ^ 3 + 1) % 16 = 12 := by omega
    rw [Nat.mul_mod, Nat.mul_mod ((3 ^ (2 * a + 1)) ^ 3), h3, h1, h4]
  · have h3 : (3 ^ (2 * a + 1)) ^ 3 % 16 = 3 := by rw [Nat.pow_mod, h]
    have h1 : (3 ^ (2 * a + 1) - 1) % 16 = 10 := by omega
    have h4 : ((3 ^ (2 * a + 1)) ^ 3 + 1) % 16 = 4 := by omega
    rw [Nat.mul_mod, Nat.mul_mod ((3 ^ (2 * a + 1)) ^ 3), h3, h1, h4]

theorem isElementaryAbelian_closure_three {G : Type*} [Group G] {x y z : G}
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hx : x * x = 1)
    (hy : y * y = 1) (hz : z * z = 1) :
    IsElementaryAbelian 2 (Subgroup.closure ({x, y, z} : Set G)) := by
  set S := Subgroup.closure ({x, y, z} : Set G) with hSdef
  have hpair : ({x, y, z} : Set G).Pairwise Commute := by
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  have hcomm : IsMulCommutative S := Subgroup.isMulCommutative_closure hpair
  have hcomm' : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hsq : ∀ g ∈ S, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    | one => rw [one_mul]
    | mul u v hu hv ihu ihv =>
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [hcomm' v hv u hu]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [ihu, ihv, one_mul]
    | inv u _ ih => rw [← mul_inv_rev, ih, inv_one]
  exact { toIsMulCommutative := hcomm
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
            rw [sq]
            exact Subtype.ext (hsq g g.2) }

theorem closure_three_sylow {G : Type*} [Group G] [Finite G] {x y z : G}
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hx : x * x = 1)
    (hy : y * y = 1) (hz : z * z = 1) (h16 : ¬ 16 ∣ Nat.card G)
    (h5 : 5 ≤ Nat.card (Subgroup.closure ({x, y, z} : Set G))) :
    IsElementaryAbelian 2 (Subgroup.closure ({x, y, z} : Set G)) ∧
      Nat.card (Subgroup.closure ({x, y, z} : Set G)) = 8 ∧
      ∃ P : Sylow 2 G, (P : Subgroup G) = Subgroup.closure ({x, y, z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := Subgroup.closure ({x, y, z} : Set G) with hSdef
  have hE : IsElementaryAbelian 2 S := isElementaryAbelian_closure_three hxy hxz hyz hx hy hz
  have hsq' : ∀ g : S, g ^ 2 = 1 := fun g =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (@IsElementaryAbelian.exponent_dvd_p 2 S _ hE) g
  have hP2 : IsPGroup 2 S := fun g => ⟨1, by rw [pow_one]; exact hsq' g⟩
  obtain ⟨P, hSP⟩ := hP2.exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP2
  have hk3 : k ≤ 3 := by
    by_contra hk4
    apply h16
    have hdvd := Subgroup.card_subgroup_dvd_card (P : Subgroup G)
    rw [hk] at hdvd
    exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ k)).trans hdvd
  have hj3 : 3 ≤ j := by
    by_contra hj2
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hjk : j ≤ k := by
    have hdvd := Subgroup.card_dvd_of_le hSP
    rw [hj, hk] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hPS : S = P := Subgroup.eq_of_le_of_card_ge hSP (by rw [hk, hj]; rw [show j = k by omega])
  refine ⟨hE, ?_, P, hPS.symm⟩
  rw [hj, show j = 3 by omega]
  rfl

theorem hasAbelianSylowTwo_of_isMulCommutative {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    [IsMulCommutative (P : Subgroup G)] : CFSG.Walter.HasAbelianSylowTwo G := by
  intro P'
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P P'
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact Subgroup.map_isMulCommutative _ _

theorem five_le_card_of_nodup {G : Type*} [Group G] {S : Subgroup G} [Finite S]
    {e₁ e₂ e₃ e₄ e₅ : G} (h : [e₁, e₂, e₃, e₄, e₅].Nodup)
    (hmem : ∀ e ∈ [e₁, e₂, e₃, e₄, e₅], e ∈ S) : 5 ≤ Nat.card S := by
  classical
  have hsub : (([e₁, e₂, e₃, e₄, e₅].toFinset : Finset G) : Set G) ⊆ S := fun e he =>
    hmem e (List.mem_toFinset.1 (Finset.mem_coe.1 he))
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup h] at hle
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact hle

theorem index_ne_two_of_commutator_eq_top {X : Type*} [Group X] (hX : commutator X = ⊤)
    (H : Subgroup X) : H.index ≠ 2 := by
  intro hidx
  have : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (X ⧸ H) := isCyclic_of_prime_card (p := 2) (by
    rw [← Subgroup.index_eq_card, hidx])
  have hle : commutator X ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact hcyc.commGroup.mul_comm _ _
  rw [hX, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hidx
  omega

section SL2

variable {K : Type} [Field K]

variable (K) in
@[expose] def smallReeMSL : SL2 K := uSL 1 * uSL 1 * WSL * uSL 1

theorem coe_smallReeMSL : (smallReeMSL K : Matrix (Fin 2) (Fin 2) K) = !![-2, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smallReeMSL, coe_uSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem WSL_mul_self : (WSL : SL2 K) * WSL = -1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_WSL, Matrix.mul_apply, Fin.sum_univ_two]

variable (h3 : (3 : K) = 0)
include h3

theorem smallReeMSL_mul_self : smallReeMSL K * smallReeMSL K = -1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, coe_smallReeMSL, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.neg_apply, Matrix.one_apply] <;>
    simp <;> first | linear_combination | linear_combination h3 | linear_combination 2 * h3

theorem smallReeMSL_mul_WSL : smallReeMSL K * WSL = -(WSL * smallReeMSL K) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      coe_smallReeMSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;>
    simp <;> first | linear_combination | linear_combination h3 | linear_combination -h3

omit h3 in
theorem smallReeMSL_ne : smallReeMSL K ≠ 1 ∧ smallReeMSL K ≠ -1 := by
  constructor <;> intro h <;>
    have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h <;>
    simp [coe_smallReeMSL] at h'

omit h3 in
theorem WSL_ne : (WSL : SL2 K) ≠ 1 ∧ (WSL : SL2 K) ≠ -1 := by
  constructor <;> intro h <;>
    have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h <;>
    simp [coe_WSL] at h'

theorem WSL_ne_smallReeMSL : WSL ≠ smallReeMSL K ∧ WSL ≠ -smallReeMSL K := by
  constructor <;> intro h
  · have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [coe_smallReeMSL, coe_WSL] at h'
    have h1 : (1 : K) = 0 := by linear_combination h3 - h'
    exact one_ne_zero h1
  · have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) h
    simp [coe_smallReeMSL, coe_WSL] at h'
    have h1 : (1 : K) = 0 := by linear_combination h3 + h'
    exact one_ne_zero h1

end SL2

section Involutions

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
  (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
include hK hw₀

theorem smallReePsi_neg_one :
    smallReePsi K a (-1) = 1 :=
  (smallReePsi_eq_one_iff hK hw₀ (-1)).2 (Or.inr rfl)

theorem smallReePsi_neg
    (g : SL2 K) : smallReePsi K a (-g) = smallReePsi K a g := by
  rw [← neg_one_mul, map_mul, smallReePsi_neg_one hK hw₀, one_mul]

theorem smallReePsi_WSL_mul_self :
    smallReePsi K a WSL * smallReePsi K a WSL = 1 := by
  rw [← map_mul, WSL_mul_self, smallReePsi_neg_one hK hw₀]

theorem smallReePsi_MSL_mul_self :
    smallReePsi K a (smallReeMSL K) * smallReePsi K a (smallReeMSL K) = 1 := by
  rw [← map_mul, smallReeMSL_mul_self (smallRee_three_eq_zero (K := K)), smallReePsi_neg_one hK hw₀]

theorem smallReePsi_WSL_commute :
    Commute (smallReePsi K a WSL) (smallReePsi K a (smallReeMSL K)) := by
  show _ * _ = _ * _
  rw [← map_mul, ← map_mul, smallReeMSL_mul_WSL (smallRee_three_eq_zero (K := K)),
    smallReePsi_neg hK hw₀]

theorem smallReePsi_WSL_ne_one :
    smallReePsi K a WSL ≠ 1 := fun h => by
  rcases (smallReePsi_eq_one_iff hK hw₀ WSL).1 h with h' | h'
  exacts [WSL_ne.1 h', WSL_ne.2 h']

theorem smallReePsi_MSL_ne_one :
    smallReePsi K a (smallReeMSL K) ≠ 1 := fun h => by
  rcases (smallReePsi_eq_one_iff hK hw₀ _).1 h with h' | h'
  exacts [smallReeMSL_ne.1 h', smallReeMSL_ne.2 h']

theorem smallReePsi_WSL_ne_MSL :
    smallReePsi K a WSL ≠ smallReePsi K a (smallReeMSL K) :=
  fun h => by
  have h1 : smallReePsi K a (WSL * (smallReeMSL K)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rcases (smallReePsi_eq_one_iff hK hw₀ _).1 h1 with h' | h'
  · exact (WSL_ne_smallReeMSL (smallRee_three_eq_zero (K := K))).1 (mul_inv_eq_one.1 h')
  · apply (WSL_ne_smallReeMSL (smallRee_three_eq_zero (K := K))).2
    rw [← neg_one_mul, ← h', inv_mul_cancel_right]

end Involutions

section JT

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
  (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)

omit [Finite K] in
theorem smallReeH_neg_one_ne_one :
    smallReeH a K (-1) ≠ 1 := fun h => by
  rw [← smallReeH_one] at h
  exact neg_one_ne_one_of_charP (congrArg Units.val (smallReeH_injective h))

include hK hw₀

theorem smallReePsi_mem_reeGamma
    (g : SL2 K) : smallReePsi K a g ∈ G2.reeGamma K a :=
  (Subgroup.mem_inf.1 (smallReePsi_mem hK hw₀ g)).1

theorem smallReePsi_range_le_reeGamma :
    (smallReePsi K a).range ≤ G2.reeGamma K a := by
  rintro _ ⟨g, rfl⟩
  exact smallReePsi_mem_reeGamma hK hw₀ g

omit hw₀ in
theorem smallReeH_neg_one_mem_reeGamma :
    smallReeH a K (-1) ∈ G2.reeGamma K a :=
  (Subgroup.mem_inf.1 (smallReeH_mem hK (-1))).2

theorem smallRee_E8_sylow :
    IsElementaryAbelian 2 (Subgroup.closure ({⟨_, smallReeH_neg_one_mem_reeGamma hK⟩,
      ⟨_, smallReePsi_mem_reeGamma hK hw₀ WSL⟩,
        ⟨_, smallReePsi_mem_reeGamma hK hw₀ (smallReeMSL K)⟩} : Set (G2.reeGamma K a))) ∧
    Nat.card (Subgroup.closure ({⟨_, smallReeH_neg_one_mem_reeGamma hK⟩,
      ⟨_, smallReePsi_mem_reeGamma hK hw₀ WSL⟩,
        ⟨_, smallReePsi_mem_reeGamma hK hw₀ (smallReeMSL K)⟩} : Set (G2.reeGamma K a))) = 8 ∧
    ∃ P : Sylow 2 (G2.reeGamma K a), (P : Subgroup (G2.reeGamma K a)) =
      Subgroup.closure ({⟨_, smallReeH_neg_one_mem_reeGamma hK⟩,
        ⟨_, smallReePsi_mem_reeGamma hK hw₀ WSL⟩,
          ⟨_, smallReePsi_mem_reeGamma hK hw₀ (smallReeMSL K)⟩} : Set (G2.reeGamma K a)) := by
  set t : G2.reeGamma K a := ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩
  set n : G2.reeGamma K a := ⟨_, smallReePsi_mem_reeGamma hK hw₀ WSL⟩
  set m : G2.reeGamma K a := ⟨_, smallReePsi_mem_reeGamma hK hw₀ (smallReeMSL K)⟩
  have hcomm : ∀ g, Commute t ⟨_, smallReePsi_mem_reeGamma hK hw₀ g⟩ := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (smallReePsi_mem hK hw₀ g)).2).symm
  have htn := hcomm WSL
  have htm := hcomm (smallReeMSL K)
  have hnm : Commute n m := Subtype.ext (smallReePsi_WSL_commute hK hw₀)
  have htt : t * t = 1 := Subtype.ext smallReeH_neg_one_mul_self
  have hnn : n * n = 1 := Subtype.ext (smallReePsi_WSL_mul_self hK hw₀)
  have hmm : m * m = 1 := Subtype.ext (smallReePsi_MSL_mul_self hK hw₀)
  have hcard := (small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀).2.2.2.2.2.2.2.2.2.1
  have h16 : ¬ 16 ∣ Nat.card (G2.reeGamma K a) := by
    rw [hcard]
    intro h
    have := card_reeGamma_mod_sixteen a
    omega
  refine closure_three_sylow htn htm hnm htt hnn hmm h16 ?_
  have hL : ∀ g, (⟨_, smallReePsi_mem_reeGamma hK hw₀ g⟩ : G2.reeGamma K a) ≠ t := fun g h =>
    smallReeH_neg_one_not_mem_range hK hw₀ ⟨g, congrArg Subtype.val h⟩
  have hn1 : n ≠ 1 := fun h => smallReePsi_WSL_ne_one hK hw₀ (congrArg Subtype.val h)
  have hm1 : m ≠ 1 := fun h => smallReePsi_MSL_ne_one hK hw₀ (congrArg Subtype.val h)
  have hnm' : n ≠ m := fun h => smallReePsi_WSL_ne_MSL hK hw₀ (congrArg Subtype.val h)
  have hnm1 : n * m ≠ 1 := fun h => hnm' (by
    rw [mul_eq_one_iff_eq_inv.1 h, inv_eq_of_mul_eq_one_right hmm])
  have hnmn : n * m ≠ n := fun h => hm1 (mul_eq_left.1 h)
  have hnmm : n * m ≠ m := fun h => hn1 (mul_eq_right.1 h)
  have hnmt : n * m ≠ t := by
    have := hL (WSL * smallReeMSL K)
    rwa [show (⟨_, smallReePsi_mem_reeGamma hK hw₀ (WSL * smallReeMSL K)⟩ : G2.reeGamma K a) =
      n * m from Subtype.ext (map_mul _ _ _)] at this
  have ht1 : (1 : G2.reeGamma K a) ≠ t := by
    have := hL 1
    rwa [show (⟨_, smallReePsi_mem_reeGamma hK hw₀ 1⟩ : G2.reeGamma K a) = 1 from
      Subtype.ext (map_one _)] at this
  refine five_le_card_of_nodup (e₁ := 1) (e₂ := n) (e₃ := m) (e₄ := n * m) (e₅ := t) ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hn1.symm, hm1.symm, hnm1.symm, ht1⟩, ⟨hnm', hnmn.symm, hL WSL⟩, ⟨hnmm.symm,
      hL (smallReeMSL K)⟩, hnmt⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    have hx : t ∈ Subgroup.closure ({t, n, m} : Set (G2.reeGamma K a)) :=
      Subgroup.subset_closure (Or.inl rfl)
    have hy : n ∈ Subgroup.closure ({t, n, m} : Set (G2.reeGamma K a)) :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hz : m ∈ Subgroup.closure ({t, n, m} : Set (G2.reeGamma K a)) :=
      Subgroup.subset_closure (Or.inr (Or.inr rfl))
    rcases he with rfl | rfl | rfl | rfl | rfl
    exacts [one_mem _, hy, hz, mul_mem hy hz, hx]

theorem hasAbelianSylowTwo_reeGamma :
    CFSG.Walter.HasAbelianSylowTwo (G2.reeGamma K a) := by
  obtain ⟨hE, -, P, hPS⟩ := smallRee_E8_sylow hK hw₀
  have : IsMulCommutative (P : Subgroup (G2.reeGamma K a)) := hPS ▸ hE.toIsMulCommutative
  exact hasAbelianSylowTwo_of_isMulCommutative P

omit hw₀ in
theorem index_ne_two_reeGamma
    (ha : 1 ≤ a) (H : Subgroup (G2.reeGamma K a)) : H.index ≠ 2 :=
  index_ne_two_of_commutator_eq_top (ree_generic_fixed_group_perfect G2 a ha K hK).2.1 H

omit hw₀ in
theorem orderOf_smallReeH_neg_one :
    orderOf (⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : G2.reeGamma K a) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => smallReeH_neg_one_ne_one
    (congrArg Subtype.val h)
  rw [sq]
  exact smallReeH_neg_one_mul_self

theorem centralizer_eq_zpowers_sup :
    Subgroup.centralizer {(⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : G2.reeGamma K a)} =
      Subgroup.zpowers (⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : G2.reeGamma K a) ⊔
        (smallReePsi K a).range.subgroupOf (G2.reeGamma K a) := by
  apply Subgroup.map_injective (G2.reeGamma K a).subtype_injective
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (smallReePsi_range_le_reeGamma hK hw₀)]
  change _ = Subgroup.zpowers (smallReeH a K (-1)) ⊔ (smallReePsi K a).range
  rw [zpowers_sup_range_eq hK hw₀]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))⟩
  · intro hx
    obtain ⟨hxΓ, hxC⟩ := Subgroup.mem_inf.1 hx
    exact ⟨⟨x, hxΓ⟩, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hxC)), rfl⟩

theorem nonempty_subgroupOf_range_mulEquiv :
    Nonempty ((smallReePsi K a).range.subgroupOf (G2.reeGamma K a) ≃* PSL(2, K)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe (smallReePsi_range_le_reeGamma hK hw₀)).trans
    ((QuotientGroup.quotientMulEquivOfEq (smallReePsi_ker hK hw₀)).symm.trans
      (QuotientGroup.quotientKerEquivRange _)).symm⟩

end JT

@[expose] def smallReeJTHyp
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    CFSG.Walter.JT.JTHyp (ReeTag.G2.reeGamma K a) :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw₀ := (Finite.exists_max (coxeterSystem ReeTag.G2.tag).length).choose_spec
  have := Fintype.ofFinite K
  have : Fintype (GaloisField 3 (2 * a + 1)) := Fintype.ofFinite _
  { p := 3
    f := 2 * a + 1
    five_lt := by
      have : 3 ^ 3 ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    abelian_sylow := hasAbelianSylowTwo_reeGamma hK hw₀
    index_ne_two := index_ne_two_reeGamma hK ha
    t := ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩
    orderOf_t := orderOf_smallReeH_neg_one hK
    F := (smallReePsi K a).range.subgroupOf (ReeTag.G2.reeGamma K a)
    le_centralizer := by
      rintro x hx
      obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hx
      refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hg]
      exact Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (smallReePsi_mem hK hw₀ g)).2
    t_not_mem := fun h => smallReeH_neg_one_not_mem_range hK hw₀ (Subgroup.mem_subgroupOf.1 h)
    centralizer_eq := centralizer_eq_zpowers_sup hK hw₀
    iso := (nonempty_subgroupOf_range_mulEquiv hK hw₀).some.trans
      (CFSG.GorensteinWalter.psl2RingEquiv (FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK,
          GaloisField.card 3 (2 * a + 1) (by omega)]))) }

theorem small_Ree_jtHyp
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ h : CFSG.Walter.JT.JTHyp (ReeTag.G2.reeGamma K a), h.p = 3 ∧ h.f = 2 * a + 1 ∧
      (h.t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1) :=
  ⟨smallReeJTHyp ha hK, rfl, rfl, rfl⟩

theorem small_Ree_reeTypeHyp
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Walter.Ward.ReeTypeHyp (ReeTag.G2.reeGamma K a)) :=
  ((smallReeJTHyp ha hK).jt_theoremA_of_ne_two (by show (3 : ℕ) ≠ 2; decide)).2.2.2.2

end CFSG.Walter.Ree.Model
