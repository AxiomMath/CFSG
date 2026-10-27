module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Data
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Setup

variable (h : Setup T M) {Y : Subgroup G}
include h

theorem inf_eq_pCoreOf (hY : IsYFamily T Y) (hYM : Y ≤ M) : Y ⊓ T = pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.pCoreOf_eq hY hYM]
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have hYN : Y ⊓ T ≤ Subgroup.normalizer (VZ T M : Set G) := inf_le_right.trans h.T_le_normalizer
    rw [← autI_eq_bot_iff h.elem hYN]
    have hp : IsPGroup 2 (autI h.elem (Y ⊓ T)) :=
      B2F.isPGroup_autI h.elem (h.isPGroup.to_le inf_le_right) hYN
    have hle : autI h.elem (Y ⊓ T) ≤ autI h.elem Y := autI_mono h.elem inf_le_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hn] at hdvd
    rcases n with _ | n
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
    · exfalso
      have h2' : 2 ∣ Nat.card (autI h.elem Y) := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr (h.odd_card_autI hY hYM)) (even_iff_two_dvd.mpr h2')
  · exact le_inf inf_le_left ((inf_le_inf_right _ hYM).trans h.inf_le_T)

theorem irreducible (hY : IsYFamily T Y) (hYM : Y ≤ M) {Y' : Subgroup G}
    (h1 : pCoreOf 2 Y ≤ Y') (h2 : Y' ≤ Y) (h3 : T ≤ Subgroup.normalizer (Y' : Set G)) :
    Y' = pCoreOf 2 Y ∨ Y' = Y := by
  rcases hY.1 with hXi | hxi
  · obtain ⟨-, -, -, -, -, -, -, -, hirr⟩ := hXi
    obtain ⟨s, -, -, hel, -⟩ := h.data hY hYM
    have hcomm : ⁅Y, Y⁆ ≤ pCoreOf 2 Y := by
      rw [h.pCoreOf_eq hY hYM]
      refine h.commutator_le_inf_centralizer hYM fun a ha b hb => ?_
      have := hel.1
      exact setLike_mul_comm ha hb
    have hsup : ⁅Y, Y⁆ ⊔ pCoreOf 2 Y = pCoreOf 2 Y := sup_eq_right.mpr hcomm
    rw [← hsup]
    exact hirr Y' (hsup.symm ▸ h1) h2 h3
  · obtain ⟨-, -, -, p, hp, -, hidx⟩ := hxi
    have e := Subgroup.relIndex_mul_relIndex (pCoreOf 2 Y) Y' Y h1 h2
    rw [hidx] at e
    rcases (Nat.dvd_prime hp).mp (Dvd.intro _ e) with h' | h'
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h') h1
    · right
      rw [h'] at e
      have e' : Y'.relIndex Y = 1 := by
        have hp0 := hp.pos
        have e2 : p * Y'.relIndex Y = p * 1 := by rw [e, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hp0 e2
      exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp e')

theorem isSylowTwoOf_sup : IsSylowTwoOf T (Y ⊔ T) := by
  obtain ⟨S, rfl⟩ := h.sylow
  exact isSylowTwoOf_of_sylow S le_sup_right

theorem minParabolic (hY : IsYFamily T Y) (hYM : Y ≤ M) : MinParabolic (Y ⊔ T) T T := by
  have hTY := (basic hY).2.1
  have hYT : ¬ Y ≤ T := not_le_of_isPGroup hY h.isPGroup
  refine minParabolic_of_isMaxSubgroupIn h.isSylowTwoOf_sup (fun hle => ?_)
    (isMaxSubgroupIn_sup hTY (h.inf_eq_pCoreOf hY hYM) hYT fun Y' h1 h2 h3 =>
      h.irreducible hY hYM h1 h2 h3)
  apply hYT
  rw [← hY.2]
  refine (Subgroup.commutator_mono le_rfl (thompsonJ_le_self T)).trans ?_
  rw [Subgroup.commutator_le]
  intro y hy t ht
  rw [commutatorElement_def]
  have hyN : y ∈ Subgroup.normalizer (T : Set G) := hle (Subgroup.mem_sup_left hy)
  exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN t).mp ht) (T.inv_mem ht)

theorem sup_le_M (hYM : Y ≤ M) : Y ⊔ T ≤ M := sup_le hYM h.T_le

theorem twoResidual_eq (hY : IsYFamily T Y) : twoResidual (Y ⊔ T) = Y :=
  twoResidual_sup_eq h.isPGroup (basic hY).2.1 (basic hY).1

theorem solv_sup (hYM : Y ≤ M) : Group.IsSolvable ↥(Y ⊔ T) := by
  have := h.solv
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (h.sup_le_M hYM))
    (Subgroup.inclusion_injective _)

theorem rank_sup (hYM : Y ≤ M) : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (Y ⊔ T) ≤ 2 :=
  fun p hp hp2 => (CFSG.SectionRank.pRank_mono hp.one_lt (h.sup_le_M hYM)).trans (h.rank p hp hp2)

theorem charTwo_sup (hYM : Y ≤ M) : CharTwo (Y ⊔ T) := by
  obtain ⟨S, rfl⟩ := h.sylow
  exact charTwo_of_le h.even S le_sup_right (h.sup_le_M hYM)
    ⟨h.T_le, h.pCoreOf_ne_bot⟩

theorem pow_mem_of_mem_centralizer (hY : IsYFamily T Y) (hYM : Y ≤ M) {x : G} (hx : x ∈ Y ⊔ T)
    (hxU : x ∈ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G)) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hTY := (basic hY).2.1
  obtain ⟨y, hy, t, ht, rfl⟩ := (mem_sup_iff_exists_mul hTY).mp hx
  obtain ⟨j, hj⟩ := h.isPGroup ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hTY ht) (2 ^ j)
  rw [hj', mul_one] at hpow
  refine ⟨j, ?_⟩
  rw [hpow]
  have hy'U : y' ∈ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) := by
    rw [← hpow]
    exact Subgroup.pow_mem _ hxU _
  exact h.centralizer_commutator_le hY hYM hy' hy'U

theorem le_normalizer_commutator (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    M ≤ Subgroup.normalizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) := fun _ hg =>
  A4.mem_normalizer_commutator (h.le_normalizer hg) (h.le_normalizer_of_mem hY hYM hg)

theorem isElemAbelian_commutator (hYM : Y ≤ M) : IsElemAbelian 2 (⁅VZ T M, Y⁆ : Subgroup G) :=
  isElemAbelian_mono (E2.commutator_le_self (hYM.trans h.le_normalizer)) h.elem

theorem commutator_le_T (hYM : Y ≤ M) : (⁅VZ T M, Y⁆ : Subgroup G) ≤ T :=
  (E2.commutator_le_self (hYM.trans h.le_normalizer)).trans h.V_le_T

theorem isTwoReducedIn_commutator (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    IsTwoReducedIn (Y ⊔ T) ⁅VZ T M, Y⁆ := by
  have hTY := (basic hY).2.1
  refine ⟨(h.commutator_le_T hYM).trans le_sup_right,
    (h.sup_le_M hYM).trans (h.le_normalizer_commutator hY hYM), h.isElemAbelian_commutator hYM,
    fun D hDH hHD hD => ?_⟩
  intro d hd
  have hdH := hDH hd
  have hdM := h.sup_le_M hYM hdH
  refine h.mem_centralizer_commutator hY hYM hdM ?_ ?_
  · obtain ⟨k, hk⟩ := hD d hd
    obtain ⟨j, hj⟩ := h.pow_mem_of_mem_centralizer hY hYM ((Y ⊔ T).pow_mem hdH _) hk
    exact ⟨k + j, by rw [pow_add, pow_mul]; exact hj⟩
  · intro y hy
    have hyH : y ∈ Y ⊔ T := Subgroup.mem_sup_left hy
    have hxD : d * y * d⁻¹ * y⁻¹ ∈ D := by
      have h0 : y * d⁻¹ * y⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hHD hyH) d⁻¹).mp (D.inv_mem hd)
      have := D.mul_mem hd h0
      simpa [mul_assoc] using this
    have hxY : d * y * d⁻¹ * y⁻¹ ∈ Y := by
      have hdN : d ∈ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_mem hY hYM hdM
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hdN y).mp hy) (Y.inv_mem hy)
    obtain ⟨k, hk⟩ := hD _ hxD
    have hkY : (d * y * d⁻¹ * y⁻¹) ^ 2 ^ k ∈ Subgroup.centralizer (VZ T M : Set G) :=
      h.centralizer_commutator_le hY hYM (Y.pow_mem hxY _) hk
    set x := d * y * d⁻¹ * y⁻¹
    have hxN := h.le_normalizer (hYM hxY)
    have hxD' := h.convI_mem_autI' hxY (hYM hxY)
    obtain ⟨s, -, -, hel, -⟩ := h.data hY hYM
    have h3 : (convI h.elem ⟨x, hxN⟩) ^ 3 = 1 := hel.2 _ hxD'
    have h2 : (convI h.elem ⟨x, hxN⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      exact (convI_eq_one_iff h.elem _).2 hkY
    have hord : orderOf (convI h.elem ⟨x, hxN⟩) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact (convI_eq_one_iff h.elem _).1 hord

theorem inf_centralizer_commutator_eq (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    (Y ⊔ T) ⊓ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) = pCoreOf 2 (Y ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left
      (B2F.le_normalizer_inf Subgroup.le_normalizer
        (B2F.le_normalizer_centralizer ((h.sup_le_M hYM).trans
          (h.le_normalizer_commutator hY hYM)))) ?_
    intro x
    obtain ⟨k, hk⟩ := h.pow_mem_of_mem_centralizer hY hYM x.2.1 x.2.2
    have hxM := h.sup_le_M hYM x.2.1
    obtain ⟨j, hj⟩ := h.isPGroup_inf ⟨_, ⟨M.pow_mem hxM (2 ^ k), hk⟩⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((x : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact hj'
  · exact le_inf (pCoreOf_le 2 _)
      (MinParabolic.pCoreOf_le_centralizer (h.isTwoReducedIn_commutator hY hYM))

omit h in
theorem _root_.CFSG.Quasithin.EmptyFaithfulMultiple.L15412.le_omegaOneCenterOf_of_isTwoReducedIn
    {H V' : Subgroup G} (hV' : IsTwoReducedIn H V') :
    V' ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  intro v hv
  have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (MinParabolic.pCoreOf_le_centralizer hV' hx) v hv).symm
  exact Subgroup.subset_closure ⟨⟨MinParabolic.le_pCoreOf_of_isTwoReduced hV' hv, hvC⟩,
    hV'.2.2.1.2 v hv⟩

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
