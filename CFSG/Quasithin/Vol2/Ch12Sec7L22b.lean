module

public import CFSG.Quasithin.Vol2.Ch12Sec7L22a
public import CFSG.Quasithin.Vol2.Ch12Sec7E3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem R2_le_normalizer (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    R2 T L V ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨-, -, hTV⟩ := card_eq_of_1222 h1222 h
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  intro r hr
  have hr1 : r ∈ L ⊔ pCoreOf 2 (L ⊔ T) := ((pCoreOf_le 2 _) hr).1
  exact sup_le hLV ((pCoreOf_le 2 _).trans (sup_le hLV hTV)) hr1

theorem offender_bound (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) (h3 : Lemma12_7_3)
    (h9 : Lemma12_7_9) (h11 : Lemma12_7_11) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) {k : ℕ} (hk : wParam T V = k) :
    rParam V ≤ ((k + 2 : ℕ) : ℕ∞) ∧ (rParam V = ((k + 2 : ℕ) : ℕ∞) →
      autOn (wClos V k T) V = autOn (R2 T L V) V ∧ V2 T L V ≤ cClos V k T) := by
  obtain ⟨hcomm, -, hTV⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hS.hyp.hyp hv⟩
  have hT := hypE322 h1222 hS.hyp
  have hw := (h11 G T L V t hS.toSetting1273).2.1
  obtain ⟨h3a, h3b⟩ := h3 G T L V hS.hyp
  have hTM : autOn T V ≤ hS.hyp.hyp.MVbar :=
    A4.autOn_mono (le_inf hS.hyp.hyp.normalizes hTV)
  obtain ⟨g, hg, hAT⟩ := exists_isWOffenderAt_le hVe hT hk
  have hdisj : ∀ h : G, IsWOffenderAt T V h → V ⊓ conjSubgroup V h = ⊥ := fun h hh => by
    by_contra hne
    exact hh.1 (lemma12_7_22_one h1222 h9 h11 hS h hne)
  have hbound : rParam V ≤ ((k + 2 : ℕ) : ℕ∞) := by
    by_contra hlt
    have hlt' : ((k + 2 : ℕ) : ℕ∞) < rParam V := lt_of_not_ge hlt
    have h3le : ((3 + k : ℕ) : ℕ∞) ≤ rParam V := by
      have := Order.add_one_le_of_lt hlt'
      rwa [show ((k + 2 : ℕ) : ℕ∞) + 1 = ((3 + k : ℕ) : ℕ∞) by push_cast; ring] at this
    have hmem := mem_aSet_autOn hVe hT hw hg hAT (hdisj g hg) hk h3le (by norm_num)
    have := le_aParam_of_mem_aSet (by norm_num : 0 < 3) (aSet_mono hTM hmem)
    rw [h3b] at this
    omega
  refine ⟨hbound, fun hr => ?_⟩
  have hR2 : ∀ h : G, IsWOffenderAt T V h →
      conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G) ≤ T →
        autOn (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) V = autOn (R2 T L V) V := by
    intro h hh hhT
    have hj : ((2 + k : ℕ) : ℕ∞) ≤ rParam V := by rw [hr, add_comm]
    have hmem := mem_aSet_autOn hVe hT hw hh hhT (hdisj h hh) hk hj (by norm_num)
    rw [h3a] at hmem
    exact hmem
  set K : Subgroup G := ((autOn (R2 T L V) V).comap (conjAct V)).map
    (Subgroup.normalizer (V : Set G)).subtype with hKdef
  have hΓK : ∀ A' ∈ gammaSet V k T, A' ≤ K := by
    rintro A' ⟨hA'T, h, hA'h, hA'k⟩ x hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hTV (hA'T hx)
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    show conjAct V ⟨x, hxN⟩ ∈ autOn (R2 T L V) V
    by_cases hA'C : A' ≤ Subgroup.centralizer (V : Set G)
    · rw [A4.conjAct_eq_one_iff.2 (hA'C hx)]
      exact Subgroup.one_mem _
    · obtain ⟨hA'eq, hh⟩ := eq_inf_normalizer_of_mem_gammaSet hVe hT hk hA'T hA'h hA'k hA'C
      have hhT : conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G) ≤ T := hA'eq ▸ hA'T
      rw [← hR2 h hh hhT, ← hA'eq]
      exact (A4.mem_autOn_iff (hA'T.trans hTV)).2 ⟨⟨x, hx⟩, rfl⟩
  have hWK : wClos V k T ≤ K := iSup₂_le hΓK
  have hWN : wClos V k T ≤ Subgroup.normalizer (V : Set G) := (wClos_le k T).trans hTV
  have hWR : autOn (wClos V k T) V ≤ autOn (R2 T L V) V := by
    intro a ha
    obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hWN).1 ha
    obtain ⟨y, hy, hyx⟩ := hWK x.2
    have e : y = ⟨x, hWN x.2⟩ := Subtype.ext hyx
    rw [e] at hy
    exact hy
  have hAΓ : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ∈ gammaSet V k T := by
    refine ⟨hAT, g, inf_le_left, ?_⟩
    have := hg.2
    rw [hk] at this
    exact_mod_cast this.symm
  refine ⟨le_antisymm hWR ?_, ?_⟩
  · rw [← hR2 g hg hAT]
    exact A4.autOn_mono (le_wClos hAΓ)
  ·
    obtain ⟨-, -, -, -, ⟨hV2line, -, -, -, hR2C, -⟩, -, -⟩ := h2 G T L V hS.hyp
    have hV2V : V2 T L V ≤ V := hV2line.1.1
    have hR2N := R2_le_normalizer h1222 hS.hyp
    refine le_inf (hV2V.trans (le_T_of_1222 h1222 hS.hyp)) ?_
    rw [← le_centralizer_iff_comm]
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    obtain ⟨y, hy, hyx⟩ := hWK hx
    obtain ⟨r, hr'⟩ := (A4.mem_autOn_iff hR2N).1 hy
    have h1 : ((conjAct V y ⟨v, hV2V hv⟩ : ↥V) : G) = (y : G) * v * (y : G)⁻¹ := rfl
    have h2' : ((A4.actionOn V (R2 T L V) hR2N r ⟨v, hV2V hv⟩ : ↥V) : G) =
        (r : G) * v * (r : G)⁻¹ := A4.actionOn_apply_coe hR2N r _
    rw [hr'] at h2'
    have hrv : (r : G) * v * (r : G)⁻¹ = v := by
      by_cases hrC : (r : G) ∈ Subgroup.centralizer (V : Set G)
      · rw [← Subgroup.mem_centralizer_iff.1 hrC v (hV2V hv), mul_inv_cancel_right]
      · have hvC : v ∈ V ⊓ Subgroup.centralizer ({(r : G)} : Set G) := by
          rw [hR2C r r.2 hrC]
          exact hv
        rw [(Subgroup.mem_centralizer_singleton_iff.1 hvC.2).symm, mul_inv_cancel_right]
    rw [← hyx]
    have h3' : (y : G) * v * (y : G)⁻¹ = v := by rw [← h1, h2', hrv]
    calc v * (y : G) = (y : G) * v * (y : G)⁻¹ * y := by rw [h3']
      _ = (y : G) * v := by group

theorem centralizer_V2_le (h4 : Lemma12_7_4) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) :
    Subgroup.centralizer (V2 T L V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, -, h4t, -⟩ := (h4 G T L V hS.hyp).2 t hS.t_mem hS.orbit_t
  obtain ⟨W, ⟨-, hWV2, l, hl, rfl⟩⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h4t]; norm_num)
  have ht : t ∈ Vt L t := le_conjClosure _ _ (Subgroup.mem_zpowers t)
  have hlt : l * t * l⁻¹ ∈ V2 T L V := hWV2 ⟨t, ht, rfl⟩
  refine (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hlt)).trans ?_
  exact centralizer_le_of_conj (L.inv_mem hl) (by group) hS.Gt_le

end S127

open S127 in
theorem lemma12_7_22_of (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight)
    (h2 : Lemma12_7_2) (h3 : Lemma12_7_3) (h4 : Lemma12_7_4) (h9 : Lemma12_7_9)
    (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) : Lemma12_7_22 := by
  intro G _ _ T L V t z hS
  obtain ⟨hcomm, hV64, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hS.hyp.hyp hv⟩
  have hT := hypE322 h1222 hS.hyp
  have hM := isUniqueM_centralizer h331 h3228 h1222 hS.hyp
  have hw := (h11 G T L V t hS.toSetting1273).2.1
  have hr2 := (h10 G T L V t hS.toSetting1273).2.1.1
  have hrk : rk ↥V = 6 := by rw [rk, hV64, padicValNat.prime_pow]
  have hV2M := centralizer_V2_le h4 hS
  suffices h234 : (wClos V 1 T ≤ Subgroup.centralizer (V : Set G) ∨
      (autOn (wClos V 1 T) V = autOn (R2 T L V) V ∧ rParam V = 3)) ∧
      Subgroup.centralizer (cClos V 1 T : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      (3 < rParam V →
        Subgroup.centralizer (cClos V 2 T : Set G) ≤ Subgroup.normalizer (L : Set G)) from
    ⟨lemma12_7_22_one h1222 h9 h11 hS, h234.1, h234.2.1, h234.2.2, lemma12_7_22_five h1222 h9 hS⟩
  by_cases hw1 : ((1 : ℕ) : ℕ∞) < wParam T V
  · have hW1 := wClos_le_of_lt_wParam hw1
    have hC1 := (e3_34_two hVe hT hM (by omega) hw1).2
    refine ⟨Or.inl (hW1.trans inf_le_right), hC1, fun hr3 => ?_⟩
    by_cases hw2 : ((2 : ℕ) : ℕ∞) < wParam T V
    · exact (e3_34_two hVe hT hM (by omega) hw2).2
    · have hk : wParam T V = ((2 : ℕ) : ℕ∞) := by
        refine le_antisymm (not_lt.1 hw2) ?_
        have := Order.add_one_le_of_lt hw1
        rwa [show ((1 : ℕ) : ℕ∞) + 1 = ((2 : ℕ) : ℕ∞) by norm_num] at this
      obtain ⟨hb, hpar⟩ := offender_bound h1222 h2 h3 h9 h11 hS hk
      have hr4 : rParam V = ((2 + 2 : ℕ) : ℕ∞) := by
        refine le_antisymm hb ?_
        have := Order.add_one_le_of_lt hr3
        rwa [show (3 : ℕ∞) + 1 = ((2 + 2 : ℕ) : ℕ∞) by norm_num] at this
      exact (Subgroup.centralizer_le (hpar hr4).2).trans hV2M
  · have hk : wParam T V = ((1 : ℕ) : ℕ∞) := by
      refine le_antisymm (not_lt.1 hw1) ?_
      have := Order.add_one_le_of_lt hw
      rwa [show (0 : ℕ∞) + 1 = ((1 : ℕ) : ℕ∞) by norm_num] at this
    obtain ⟨hb, hpar⟩ := offender_bound h1222 h2 h3 h9 h11 hS hk
    have hr3 : rParam V = ((1 + 2 : ℕ) : ℕ∞) := by
      refine le_antisymm hb ?_
      have := Order.add_one_le_of_lt hr2
      rwa [show (2 : ℕ∞) + 1 = ((1 + 2 : ℕ) : ℕ∞) by norm_num] at this
    obtain ⟨hW, hV2C⟩ := hpar hr3
    refine ⟨Or.inr ⟨hW, by rw [hr3]; norm_num⟩, (Subgroup.centralizer_le hV2C).trans hV2M,
      fun h => ?_⟩
    rw [hr3] at h
    exact absurd h (by norm_num)

end CFSG.Quasithin.H13
