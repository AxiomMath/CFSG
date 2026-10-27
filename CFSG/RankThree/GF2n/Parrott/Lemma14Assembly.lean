module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
public import CFSG.RankThree.GF2n.Parrott.Lemma14
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma14Pauli
import all CFSG.RankThree.GF2n.Parrott.Lemma14
import all CFSG.Quasithin.Recognition.U33Defs
public import CFSG.RankThree.GF2n.Parrott.Section2Cases

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_index_two_of_isConj (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z)
    (hxJ : x ∉ J z) {X : Subgroup G}
    (hX : IsSylowOf 2 X (H z ⊓ Subgroup.centralizer ({x} : Set G))) (hzx : IsConj z x) :
    ∃ Y : Subgroup G, X ≤ Y ∧ X.relIndex Y = 2 ∧ Y ≤ Subgroup.centralizer ({x} : Set G) ∧
      ∃ y ∈ Y, y ∉ H z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := H z ⊓ Subgroup.centralizer ({x} : Set G) with hM
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX.isPGroup
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer J_le_H).mp (J_subgroupOf_normal z)
  have hJx : ¬ J z ≤ Subgroup.centralizer ({x} : Set G) := by
    intro hle
    apply hxJ
    refine h.2.2.2.1 ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hj)
  have hdvd : 2 ∣ M.relIndex (H z) :=
    CFSG.GroupTheory.dvd_relIndex_inf_centralizer_of_normal_pGroup J_le_H hHN (isPGroup_J h) hJx
  have hHcard : Nat.card (H z) = M.relIndex (H z) * (X.relIndex M * 2 ^ k) := by
    have h1 := Subgroup.relIndex_mul_card M (H z)
    have h2 := Subgroup.relIndex_mul_card X M
    rw [inf_eq_left.mpr inf_le_left] at h1
    rw [inf_eq_left.mpr hX.le, hk] at h2
    rw [← h1, ← h2]
  have hpow : 2 ^ (k + 1) ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [← CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj hzx]
    change 2 ^ (k + 1) ∣ Nat.card (H z)
    rw [hHcard, pow_succ]
    obtain ⟨d, hd⟩ := hdvd
    rw [hd]
    exact ⟨d * X.relIndex M, by ring⟩
  obtain ⟨Y, hYcard, hXY, hYx⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (by rw [hk]; exact pow_dvd_pow 2 (Nat.le_succ k)) hpow (hX.le.trans inf_le_right)
  refine ⟨Y, hXY, ?_, hYx, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card X Y
    rw [inf_eq_left.mpr hXY, hk, hYcard, pow_succ] at h1
    have h2 : 0 < 2 ^ k := pow_pos two_pos k
    nlinarith
  · by_contra hall
    push Not at hall
    have hYM : Y ≤ M := fun y hy => ⟨hall y hy, hYx hy⟩
    have hY2 : IsPGroup 2 Y := IsPGroup.of_card hYcard
    obtain ⟨Q, hYQ⟩ := (hY2.comap_subtype : IsPGroup 2 (Y.subgroupOf M)).exists_le_sylow
    have hQcard : Nat.card (Q : Subgroup M) = 2 ^ k := by
      rw [Sylow.card_eq_multiplicity, ← hk, hX.card_eq]
    have hle : Nat.card (Y.subgroupOf M) ≤ Nat.card (Q : Subgroup M) := Subgroup.card_le_of_le hYQ
    have hYM' : Nat.card (Y.subgroupOf M) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv
    rw [hQcard, hYM', hYcard] at hle
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self k)
    omega

theorem conjMeetJBot_of_not_mem_H (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    {K : Subgroup (J z)} (hKiso : Nonempty (↥K ≃* CFSG.Quasithin.Z4StarQ8Model))
    {y : G} (hyH : y ∉ H z)
    (hKyH : (K.map (J z).subtype).map (MulAut.conj y).toMonoidHom ≤ H z) :
    ConjMeetJBot (z := z) K y := by
  obtain ⟨eK⟩ := hKiso
  unfold ConjMeetJBot
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer J_le_H).mp (J_subgroupOf_normal z)
  have hzK : (((eK.symm ⟨2, 0, 0⟩ : ↥K) : ↥(J z)) : G) = z := by
    set a : ↥K := eK.symm ⟨0, 0, 1⟩
    set b : ↥K := eK.symm ⟨0, 1, 0⟩
    have hab : eK.symm ⟨2, 0, 0⟩ = a * b * a⁻¹ * b⁻¹ := by
      apply eK.injective
      simp only [a, b, map_mul, map_inv, MulEquiv.apply_symm_apply]
      decide +kernel
    have hc := commutator_mem_zpowers_z h (a : ↥(J z)).2 (b : ↥(J z)).2
    rw [commutatorElement_def] at hc
    have hne : (((eK.symm ⟨2, 0, 0⟩ : ↥K) : ↥(J z)) : G) ≠ 1 := by
      intro h1
      have h2 : eK.symm ⟨2, 0, 0⟩ = 1 := Subtype.ext (Subtype.ext h1)
      have h3 := congrArg eK h2
      rw [MulEquiv.apply_symm_apply, map_one] at h3
      exact absurd h3 (by decide +kernel)
    rw [hab] at hne ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hne ⊢
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hc with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hyzJ : y * z * y⁻¹ ∉ J z := by
    intro hJy
    by_cases hyz : y * z * y⁻¹ = z
    · apply hyH
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz]
    · have hord : orderOf (y * z * y⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
      exact hJ _ hJy hord hyz y rfl
  rw [eq_bot_iff]
  rintro _ ⟨⟨_, ⟨κ, hκ, rfl⟩, rfl⟩, hwJ⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  change y * (κ : G) * y⁻¹ ∈ J z at hwJ
  have hκ1 : (⟨κ, hκ⟩ : ↥K) ≠ 1 := by
    intro h1
    apply hw1
    have : (κ : G) = 1 := congrArg (fun k : ↥K => ((k : ↥(J z)) : G)) h1
    simp [this]
  have hm1 : eK ⟨κ, hκ⟩ ≠ 1 := fun h1 => hκ1 (eK.injective (by rw [h1, map_one]))
  apply hyzJ
  rcases A1Section2Local.pauli_cases_of_ne_one _ hm1 with h1 | h1 | ⟨m', h1⟩
  · have h1' : (⟨κ, hκ⟩ : ↥K) = eK.symm ⟨2, 0, 0⟩ := by rw [← h1, MulEquiv.symm_apply_apply]
    have hκz : (κ : G) = z :=
      (congrArg (fun k : ↥K => ((k : ↥(J z)) : G)) h1').trans hzK
    rwa [hκz] at hwJ
  · have h1' : (⟨κ, hκ⟩ : ↥K) * ⟨κ, hκ⟩ = eK.symm ⟨2, 0, 0⟩ := by
      rw [← h1, map_mul, MulEquiv.symm_apply_apply]
    have hκz : (κ : G) * (κ : G) = z :=
      (congrArg (fun k : ↥K => ((k : ↥(J z)) : G)) h1').trans hzK
    have h2 := (J z).mul_mem hwJ hwJ
    rwa [show y * (κ : G) * y⁻¹ * (y * (κ : G) * y⁻¹) = y * ((κ : G) * (κ : G)) * y⁻¹ by group,
      hκz] at h2
  · set κ' : G := (((eK.symm m' : ↥K) : ↥(J z)) : G) with hκ'
    have h1' : (⟨κ, hκ⟩ : ↥K) * eK.symm m' * (⟨κ, hκ⟩ : ↥K)⁻¹ * (eK.symm m')⁻¹ =
        eK.symm ⟨2, 0, 0⟩ := by
      rw [← h1, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.symm_apply_apply]
    have hκz : (κ : G) * κ' * (κ : G)⁻¹ * κ'⁻¹ = z :=
      (congrArg (fun k : ↥K => ((k : ↥(J z)) : G)) h1').trans hzK
    have hκ'H : y * κ' * y⁻¹ ∈ H z :=
      hKyH ⟨κ', ⟨(eK.symm m' : ↥K), (eK.symm m').2, rfl⟩, rfl⟩
    have h2 : (y * κ' * y⁻¹) * (y * (κ : G) * y⁻¹)⁻¹ * (y * κ' * y⁻¹)⁻¹ ∈ J z :=
      (Subgroup.mem_normalizer_iff.mp (hHN hκ'H) _).mp ((J z).inv_mem hwJ)
    have h3 := (J z).mul_mem hwJ h2
    rwa [show y * (κ : G) * y⁻¹ * ((y * κ' * y⁻¹) * (y * (κ : G) * y⁻¹)⁻¹ * (y * κ' * y⁻¹)⁻¹) =
        y * ((κ : G) * κ' * (κ : G)⁻¹ * κ'⁻¹) * y⁻¹ by group, hκz] at h3

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem no_conj_z_eq_of_mem_tuJ_of_inputs (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    (hK : ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
      ∃ K : Subgroup (J z), K.map (J z).subtype ≤ Subgroup.centralizer ({x} : Set G) ∧
        Nonempty (↥K ≃* CFSG.Quasithin.Z4StarQ8Model))
    (hnoK : NoZ4Q8InCHutQuot (z := z) (D := D)) :
    ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x := by
  intro x hx hx2 g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKx, hKiso⟩ := hK x hx hx2
  obtain ⟨j, hj, hxj⟩ := hx
  have hxw : ((tH D * uH D : ↥(H z)) : G)⁻¹ * x ∈ J z := by
    rw [hxj, inv_mul_cancel_left]
    exact hj
  have hxH : x ∈ H z := by
    rw [hxj]
    exact (H z).mul_mem (tH D * uH D).2 (J_le_H hj)
  have hxJ : x ∉ J z := by
    intro hxJ
    have hw : ((tH D * uH D : ↥(H z)) : G) ∈ J z := by
      have e : ((tH D * uH D : ↥(H z)) : G) = x * (((tH D * uH D : ↥(H z)) : G)⁻¹ * x)⁻¹ := by
        group
      rw [e]
      exact (J z).mul_mem hxJ ((J z).inv_mem hxw)
    have hq := (J_mem_iff D (tH D * uH D)).mp (Subgroup.mem_subgroupOf.mpr hw)
    rw [map_mul, qH_tH, qH_uH] at hq
    apply beta_sq_ne_one
    rw [beta_sq, ← t_commute_u]
    have h' := congrArg Subtype.val hq
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h'
    exact h'
  obtain ⟨X, hX⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer ({x} : Set G))
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer J_le_H).mp (J_subgroupOf_normal z)
  have hCJX : J z ⊓ Subgroup.centralizer ({x} : Set G) ≤ X :=
    CFSG.GroupTheory.le_isSylowOf_of_isPGroup_of_le_normalizer hX (inf_le_inf_right _ J_le_H)
      (fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hHN hm.1, Subgroup.le_normalizer hm.2⟩) ((isPGroup_J h).to_le inf_le_left)
  have hKX : K.map (J z).subtype ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    exact hCJX ⟨k.2, hKx ⟨k, hk, rfl⟩⟩
  obtain ⟨Y, hXY, hYidx, -, y, hyY, hyH⟩ :=
    exists_index_two_of_isConj h hxH hxJ hX (isConj_iff.mpr ⟨g, hg⟩)
  have hYN : Y ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp (Subgroup.normal_of_index_eq_two hYidx)
  have hKyH : (K.map (J z).subtype).map (MulAut.conj y).toMonoidHom ≤ H z := by
    rintro _ ⟨k, hk, rfl⟩
    exact (hX.le.trans inf_le_left) ((Subgroup.mem_normalizer_iff.mp (hYN hyY) k).mp (hKX hk))
  have hKyJ := conjMeetJBot_of_not_mem_H h hJ hKiso hyH hKyH
  have hnoK' : ∀ L : Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z)),
      L ≤ Subgroup.centralizer
        ({QuotientGroup.mk' ((J z).subgroupOf (H z)) (tH D * uH D)} :
          Set (↥(H z) ⧸ (J z).subgroupOf (H z))) →
      ¬ Nonempty (↥L ≃* CFSG.Quasithin.Z4StarQ8Model) := by
    rw [mk_t_mul_u]
    exact hnoK
  exact no_conj_z_eq_of_mem_utJ_gen hxw hKiso hX hKX hXY hYidx hyY hKyJ hnoK' g hg

end CFSG.RankThree.GF2n.Parrott
