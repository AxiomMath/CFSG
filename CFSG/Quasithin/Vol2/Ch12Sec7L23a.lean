module

public import CFSG.Quasithin.Vol2.Ch12Sec7L22a
public import CFSG.Quasithin.Vol2.Ch12Sec2StatementsPrime
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem one_lt_nParam (h1222 : Stmt12_2_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h22 : Lemma12_7_22) {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z)
    {H : Subgroup G} (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    1 < E1.nParam H := by
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hS.hyp.hyp hv⟩
  have hs : sParam hVe = 2 := (h10 G T L V t hS.toSetting1273).2.1.2 hVe
  have hW := (h11 G T L V t hS.toSetting1273).2.2
  have hC := (h22 G T L V t z hS).2.2.1
  have hT := hS.hyp.hyp.sylow
  have hS' : IsSylowIn 2 T H :=
    ⟨hHs.1.1, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hHs.1.1))⟩
  have h0 : ¬ E1.nParam H ≤ 0 := by
    intro h0
    have hodd := E1.odd_of_nParam_le_zero h0
    obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS.hyp.hyp.irrPlus.2.1
    have hv2 : orderOf (v : G) = 2 :=
      orderOf_eq_prime (sq_eq_one_of_mem hS.hyp.hyp v.2) fun h => hv1 (Subtype.ext h)
    have hdvd : orderOf (v : G) ∣ Nat.card H :=
      Subgroup.orderOf_dvd_natCard H (hHs.1.1 (le_T_of_1222 h1222 hS.hyp v.2))
    rw [hv2] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  by_contra hle
  push Not at hle
  have h1 : E1.nParam H = ((1 : ℕ) : ℕ∞) := by
    have hpos : 0 < E1.nParam H := lt_of_not_ge h0
    have h01 := Order.add_one_le_of_lt hpos
    rw [zero_add] at h01
    exact_mod_cast le_antisymm hle h01
  have hgen := e3_19 hVe hS' (i := 0) h1 (by rw [hs]; norm_num)
  apply hHs.2.1
  rw [← hgen, zero_add]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hW)

theorem nParam_le_two (h1222 : Stmt12_2_2) (h1211 : Stmt12_2_11') {T L V : Subgroup G}
    {t z : G} (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) :
    E1.nParam H ≤ 2 ∧ (E1.nParam H = 2 → ∀ C : Subgroup G,
      C ≤ H ⊓ Subgroup.normalizer (L : Set G) → Odd (Nat.card C) →
      (∃ k : ℕ, C.relIndex (H ⊓ Subgroup.normalizer (L : Set G)) = 2 ^ k) →
      C ≠ ⊥ ∧ IsPGroup 3 C) := by
  have hy := hS.hyp.hyp
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hy.irrPlus.2.2.1
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  obtain ⟨-, -, -, ⟨_, hmod⟩⟩ := hall V hy.irrPlus
  have hg : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6)) ∧ Nat.card V = 2 ^ 6 := by
    have hQ := card_quot_of_hatA6Quot hS.hyp.hatA6
    have hsl : ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) →
        ¬ 135 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
      intro n hn
      rcases hn with rfl | rfl | rfl <;> rw [Matrix.card_SL_field, ZMod.card] <;> decide
    rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
        ⟨m, hm5, hm8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, -⟩ | ⟨hq, hZ3, he6, -, hcard6, -⟩
    · exact absurd (dvd_card_quot_pCore hS.hyp.hatA6 e) (hsl n hn)
    · exact absurd (dvd_card_quot_pCore hS.hyp.hatA6 e) (hsl 3 (Or.inl rfl))
    · exact absurd (dvd_card_quot_pCore hS.hyp.hatA6 e) (hsl 5 (Or.inr (Or.inr rfl)))
    · exfalso
      apply card_alternating_ne hm5 hm8
      rw [← hQ, ← hker]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
    · exfalso
      apply card_alternating_ne (n := 7) (by norm_num) (by norm_num)
      rw [← hQ, ← hker]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
    · exfalso
      rcases hU with ⟨-, hU⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · have h135 := dvd_card_quot_pCore hS.hyp.hatA6 (MulEquiv.refl _)
        rw [F420.card_of_u33 hU] at h135
        exact absurd h135 (by decide)
      all_goals exact absurd h0 (by norm_num)
    · exact ⟨hq, hZ3, he6, hcard6⟩
  obtain ⟨hq, hZ3, he6, hcard6⟩ := hg
  have hVv : ∀ v ∈ V ⊓ Subgroup.centralizer (T : Set G), v ≠ 1 →
      V ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
    intro v hv hv1
    have hTv : T ≤ Subgroup.centralizer ({v} : Set G) := fun s hs => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hv).2 s hs
    have hodd := not_two_dvd_relIndex hy hTv
    rcases conj_z_or_t h1222 hS v (Subgroup.mem_inf.1 hv).1 hv1 with ⟨l, hl, hlv⟩ |
        ⟨l, hl, hlv⟩
    · have hl' : l⁻¹ * z * l⁻¹⁻¹ = v := by rw [← hlv]; group
      exact le_pCoreOf_centralizer_conj (hLV (L.inv_mem hl)) hl' hS.V_le
    · exfalso
      rw [← relIndex_centralizer_conj hl, hlv, hS.orbit_t] at hodd
      exact hodd ⟨9, rfl⟩
  have hU : Subgroup.zpowers z ≠ ⊥ := fun h => hS.z_ne_one (by
    have := Subgroup.mem_zpowers z
    rwa [h, Subgroup.mem_bot] at this)
  have hUV : Subgroup.zpowers z ≤ V := (Subgroup.zpowers_le).2 hzV
  have hHU : H ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro h hh
    have hc : Commute h z := Subgroup.mem_centralizer_singleton_iff.1 (hHz hh)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      have e : x = h⁻¹ * z ^ k * h := by rw [hk]; group
      rw [e, (hc.inv_left.zpow_right k).eq, inv_mul_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  exact h1211 G T L V H (Subgroup.zpowers z) hy hHs hU hUV hHU
    (Or.inr (Or.inl ⟨hq.1, hZ3, he6, hcard6, hVv⟩))

theorem nParam_eq_two (h1222 : Stmt12_2_2) (h1211 : Stmt12_2_11') (h10 : Lemma12_7_10)
    (h11 : Lemma12_7_11) (h22 : Lemma12_7_22) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) : E1.nParam H = 2 := by
  have h1 := one_lt_nParam h1222 h10 h11 h22 hS hHs
  have h2 := (nParam_le_two h1222 h1211 hS hHs hHz).1
  refine le_antisymm h2 ?_
  have := Order.add_one_le_of_lt h1
  rwa [show (1 : ℕ∞) + 1 = 2 by norm_num] at this

end S127

end CFSG.Quasithin.H13
