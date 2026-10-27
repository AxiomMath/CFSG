module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Zero
import CFSG.Quasithin.Background.B6Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem k105In_top_of_thompson {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) {z : X}
    (hz : z ∈ CFSG.Open.quasithinOmegaOneCenter T) (hC : K105In (centralizer {z}) T)
    (hJ : K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set X)) T)
    (hodd : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ A : Subgroup X, CFSG.Open.IsElemAbelian p A →
      A ≠ ⊥ → T ≤ normalizer (A : Set X) → A ⊓ centralizer {z} ≠ ⊥) :
    K105In ⊤ T := by
  intro R hTR _ hRs h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hRs
  have hsolv : ∀ Y : Subgroup X, Y ≤ R → Group.IsSolvable ↥Y := fun Y hY =>
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hY)
  have h3le : ∀ Y : Subgroup X, Y ≤ R → ¬ 3 ∣ Nat.card ↥Y := fun Y hY h =>
    h3 (h.trans (Subgroup.card_dvd_of_le hY))
  have hzT : T ≤ centralizer {z} := by
    have hle : CFSG.Open.quasithinOmegaOneCenter T ≤ centralizer (T : Set X) := by
      unfold CFSG.Open.quasithinOmegaOneCenter
      rw [Subgroup.closure_le]
      intro x hx
      exact (Subgroup.mem_inf.1 hx.1).2
    have hzc := hle hz
    exact fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzc t ht)
  have hnormR : ∀ N : Subgroup ↥R, N.Normal →
      R ≤ normalizer ((N.map R.subtype : Subgroup X) : Set X) := by
    intro N hN r hr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨r, hr⟩ * n * ⟨r, hr⟩⁻¹, hN.conj_mem n hn ⟨r, hr⟩, rfl⟩
    · rintro ⟨n, hn, hnh⟩
      refine ⟨⟨r, hr⟩⁻¹ * n * ⟨r, hr⟩, ?_, ?_⟩
      · simpa using hN.conj_mem n hn ⟨r, hr⟩⁻¹
      · have hnh' : (n : X) = r * h * r⁻¹ := hnh
        show r⁻¹ * (n : X) * r = h
        rw [hnh']
        group
  have hcore : CFSG.pPrimeCore 2 ↥R = ⊥ := by
    refine eq_bot_iff.2 (sSup_le fun K hK => ?_)
    obtain ⟨hKn, hKc⟩ := hK
    by_contra hK1
    have hKne : K ≠ ⊥ := fun h => hK1 h.le
    obtain ⟨M, ⟨hMn, hM1, hMK⟩, hmin⟩ :=
      (Set.toFinite {M : Subgroup ↥R | M.Normal ∧ M ≠ ⊥ ∧ M ≤ K}).exists_minimal
        ⟨K, hKn, hKne, le_rfl⟩
    have := hMn
    have : CFSG.IsMinimalNormal M := ⟨fun Y hY hYM => by
      by_cases hY1 : Y = ⊥
      · exact Or.inl hY1
      · exact Or.inr (le_antisymm hYM (hmin ⟨hY, hY1, hYM.trans hMK⟩ hYM))⟩
    obtain ⟨p, hp, hMe⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup p ↥M).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hM1 (Subgroup.card_eq_one.1 (by rw [hk, pow_zero]))
    have hpM : p ∣ Nat.card ↥M := hk ▸ dvd_pow_self p hk0
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hKc
        (hpM.trans (Subgroup.card_dvd_of_le hMK))
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact h3 (hpM.trans (Subgroup.card_subgroup_dvd_card M))
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have hlt' : p < 5 := by omega
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    have hAe : CFSG.Open.IsElemAbelian p (M.map R.subtype) :=
      CFSG.Open.IsElemAbelian.map ⟨hMe.toIsMulCommutative, fun y hy =>
        CFSG.elemPow_eq_one_of_isElementaryAbelian (A := M) y hy⟩ R.subtype
    have hA1 : M.map R.subtype ≠ ⊥ := fun h =>
      hM1 ((Subgroup.map_eq_bot_iff_of_injective M R.subtype_injective).1 h)
    have hTA : T ≤ normalizer ((M.map R.subtype : Subgroup X) : Set X) := fun t ht =>
      hnormR M hMn (hTR ht)
    apply hodd p hp hp5 _ hAe hA1 hTA
    have hsub : T ⊔ (M.map R.subtype ⊓ centralizer {z}) ≤ R :=
      sup_le hTR (inf_le_left.trans (Subgroup.map_subtype_le M))
    have hBT : M.map R.subtype ⊓ centralizer {z} ≤ T :=
      le_sup_right.trans
        (hC _ le_sup_left (sup_le hzT inf_le_right) (hsolv _ hsub) (h3le _ hsub))
    have hdisj := IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) T (M.map R.subtype) hT.2.1
      (CFSG.Open.IsElemAbelian.isPGroup hAe)
    exact le_bot_iff.1 ((le_inf hBT inf_le_left).trans (disjoint_iff.1 hdisj).le)
  have hS'2 : IsPGroup 2 (T.subgroupOf R) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTR).symm
  have hS'idx : ¬ 2 ∣ (T.subgroupOf R).index := fun h => hT.2.2 (by
    have h' := h.trans (Subgroup.relIndex_dvd_index_of_le hTR)
    rwa [← Subgroup.relIndex_top_right] at h')
  let T' : Sylow 2 ↥R := hS'2.toSylow hS'idx
  have hchar : CFSG.IsCharacteristicP 2 ↥R :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥R 2 hcore
      CFSG.HardMathSupport.Solomon.Coordinator.I28_8.layer_eq_bot_of_solvable'
  have hF := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥R 2).1 hchar
  obtain ⟨-, -, -, -, -, -, hNC, -⟩ :=
    CFSG.Quasithin.H13.NQTerm.solvable_characteristic_two_three_free_thompson_factorization
      (G := ↥R) hF h3 T' (Z := CFSG.Open.quasithinOmegaOneCenter (T' : Subgroup ↥R))
      (U := Subgroup.normalClosure
        ((CFSG.Open.quasithinOmegaOneCenter (T' : Subgroup ↥R) : Subgroup ↥R) : Set ↥R))
      (J := (CFSG.elemThompson (T' : Subgroup ↥R) 2).map (T' : Subgroup ↥R).subtype)
      rfl rfl rfl
  have hTS : (T' : Subgroup ↥R) = T.subgroupOf R := rfl
  have hJ' : ((CFSG.elemThompson (T' : Subgroup ↥R) 2).map (T' : Subgroup ↥R).subtype).map
      R.subtype = CFSG.Quasithin.thompsonJ T := by
    rw [CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ, hTS,
      CFSG.HardMathSupport.Solomon.Coordinator.I28_8.thompsonJ_map_subtype hTR]
  have hZ' : (CFSG.Open.quasithinOmegaOneCenter (T' : Subgroup ↥R)).map R.subtype =
      CFSG.Open.quasithinOmegaOneCenter T := by
    rw [hTS, CFSG.HardMathSupport.Solomon.Coordinator.I28_8.map_quasithinOmegaOneCenter hTR]
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥R) ∈ ((Subgroup.normalizer
      (((CFSG.elemThompson (T' : Subgroup ↥R) 2).map (T' : Subgroup ↥R).subtype : Subgroup ↥R) :
        Set ↥R) : Set ↥R)) *
      ((Subgroup.centralizer ((CFSG.Open.quasithinOmegaOneCenter (T' : Subgroup ↥R) :
        Subgroup ↥R) : Set ↥R) : Subgroup ↥R) : Set ↥R) := hNC ▸ Set.mem_univ _
  obtain ⟨n, hn, c, hc, hnc⟩ := hmem
  have hnT : (n : X) ∈ T := by
    have hnN : (n : X) ∈ normalizer (CFSG.Quasithin.thompsonJ T : Set X) := by
      have := CFSG.HardMathSupport.Solomon.Coordinator.I28_8.mem_normalizer_map_subtype hn
      rwa [hJ'] at this
    have hsub : normalizer (CFSG.Quasithin.thompsonJ T : Set X) ⊓ R ≤ R := inf_le_right
    exact hJ _ (le_inf (CFSG.Quasithin.B6.le_normalizer_thompsonJ T) hTR) inf_le_left
      (hsolv _ hsub) (h3le _ hsub) (Subgroup.mem_inf.2 ⟨hnN, n.2⟩)
  have hcT : (c : X) ∈ T := by
    have hc' : (c : X) ∈ centralizer
        (((CFSG.Open.quasithinOmegaOneCenter (T' : Subgroup ↥R)).map R.subtype : Subgroup X) :
          Set X) := by
      rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hc) w hw)
    rw [hZ'] at hc'
    have hcz : (c : X) ∈ centralizer {z} :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hc' z hz).symm
    have hsub : centralizer {z} ⊓ R ≤ R := inf_le_right
    exact hC _ (le_inf hzT hTR) inf_le_left (hsolv _ hsub) (h3le _ hsub)
      (Subgroup.mem_inf.2 ⟨hcz, c.2⟩)
  have hxnc : x = (n : X) * (c : X) := by
    rw [← Subgroup.coe_mul, show n * c = ⟨x, hx⟩ from hnc]
  rw [hxnc]
  exact T.mul_mem hnT hcT

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
