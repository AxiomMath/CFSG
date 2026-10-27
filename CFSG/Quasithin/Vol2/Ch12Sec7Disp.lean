module

public import CFSG.Quasithin.Vol2.Ch12Sec7Excl
public import CFSG.Quasithin.Vol2.Ch12Sec7Final
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem exists_isHStar_le {T M K : Subgroup G} (hK : InH T K) (hKM : ¬ K ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ K := by
  obtain ⟨H, ⟨hH1, hH2, hHK⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {H : Subgroup G | InH T H ∧ ¬ H ≤ M ∧ H ≤ K} ⟨K, hK, hKM, le_rfl⟩
  refine ⟨H, ⟨hH1, hH2, fun Y hY hYH hYM => ?_⟩, hHK⟩
  by_contra hne
  exact hmin Y ⟨hY, hYM, hYH.trans hHK⟩ (lt_of_le_of_ne hYH hne)

theorem not_two_dvd_relIndex {T L V : Subgroup G} (h : Hyp1223 G T L V) {v : G}
    (hv : T ≤ Subgroup.centralizer ({v} : Set G)) :
    ¬ 2 ∣ (Subgroup.centralizer ({v} : Set G)).relIndex L := by
  have hloc := h.maximal.1
  have hT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hT le_sup_left (sup_le Subgroup.le_normalizer h.normalizes)
  have hdvd : (Subgroup.centralizer ({v} : Set G)).relIndex L ∣ (T ⊓ L).relIndex L :=
    Subgroup.relIndex_dvd_of_le_left L (inf_le_left.trans hv)
  exact fun h2 => hTL.2.2 (h2.trans hdvd)

omit [Finite G] in
theorem centralizer_le_of_conj {L : Subgroup G} {l v w : G} (hl : l ∈ L)
    (hlv : l * v * l⁻¹ = w)
    (hw : Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : l * x * l⁻¹ ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hlv]
    calc l * x * l⁻¹ * (l * v * l⁻¹) = l * (x * v) * l⁻¹ := by group
      _ = l * (v * x) * l⁻¹ := by rw [hx]
      _ = l * v * l⁻¹ * (l * x * l⁻¹) := by group
  have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
  have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlN) (hw hx')) hlN
  rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h1

theorem card_sl_three_or_four {n : ℕ} (hn : n = 3 ∨ n = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 168 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 20160 := by
  rcases hn with rfl | rfl
  · left
    rw [Matrix.card_SL_field, ZMod.card]
    decide
  · right
    rw [Matrix.card_SL_field, ZMod.card]
    decide

theorem not_sl_of_hyp1271 {T L V : Subgroup G} (h : Hyp1271 G T L V) {n : ℕ} (hn : n = 3 ∨ n = 4) :
    ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1080 := dvd_card_of_hatA6Quot h.hatA6
  have hcard := (CFSG.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [Nat.card_congr e.toEquiv, hk] at hcard
  have h27 : 27 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) * 2 ^ k :=
    hcard ▸ (dvd_trans (by norm_num) h1080)
  have hcop : Nat.Coprime 27 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have h27' := hcop.dvd_of_dvd_mul_right h27
  rcases card_sl_three_or_four hn with h' | h' <;> rw [h'] at h27' <;> norm_num at h27'

end S127

open S127 in
theorem display12_7_22_of (h4 : Lemma12_7_4_one) (h1213 : Stmt12_2_13) : Display12_7_22 := by
  intro G _ _ T L V t z hS _
  have hH := hS.hyp
  obtain ⟨z₀, -, t₀, -, h45, h18₀, horb⟩ := h4 G T L V hH
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hzodd := not_two_dvd_relIndex hH.hyp hS.T_le_Gz
  have hzz₀ : ∃ l ∈ L, l * z * l⁻¹ = z₀ := by
    rcases horb z hzV hS.z_ne_one with hz | ⟨l, hl, hlz⟩
    · exact hz
    · rw [← hlz, relIndex_centralizer_conj hl] at h18₀
      exact absurd ⟨9, h18₀⟩ hzodd
  have htt₀ : ∃ l ∈ L, l * t * l⁻¹ = t₀ := by
    rcases horb t hS.t_mem (ne_one_of_relIndex hS.orbit_t (by decide)) with ⟨l, hl, hlt⟩ | ht
    · rw [← hlt, relIndex_centralizer_conj hl, hS.orbit_t] at h45
      exact absurd h45 (by decide)
    · exact ht
  have hGz : ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro hzM
    obtain ⟨l, hl, hlz⟩ := hzz₀
    obtain ⟨l', hl', hlt⟩ := htt₀
    have hz₀M : Subgroup.centralizer ({z₀} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      centralizer_le_of_conj (L.inv_mem hl) (by rw [← hlz]; group) hzM
    have ht₀M : Subgroup.centralizer ({t₀} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      centralizer_le_of_conj (L.inv_mem hl') (by rw [← hlt]; group) hS.Gt_le
    have hall : ∀ v ∈ V, v ≠ 1 →
        Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
      intro v hv hv1
      rcases horb v hv hv1 with ⟨m, hm, hmv⟩ | ⟨m, hm, hmv⟩
      · exact centralizer_le_of_conj hm hmv hz₀M
      · exact centralizer_le_of_conj hm hmv ht₀M
    have hy := hH.hyp
    rcases h1213 G T L V hy.simple hy.nonabelian hy.qtke hy.sylow hy.notAlt hy.maximal hy.faithful
        hy.quasisimple hy.normalizes hy.irrPlus with
      ⟨v, hv, hv1, hvM⟩ | ⟨n, hn, hSL, -⟩ | ⟨hSL, -⟩ | ⟨hSL, -⟩
    · exact hvM (hall v hv hv1)
    · exact not_sl_of_hyp1271 hH hn hSL
    · exact not_sl_of_hyp1271 hH (Or.inl rfl) hSL
    · exact not_sl_of_hyp1271 hH (Or.inr rfl) hSL
  have hInH : InH T (Subgroup.centralizer ({z} : Set G)) := by
    refine ⟨hS.T_le_Gz, fun hb => hS.z_ne_one ?_⟩
    have := hS.V_le hzV
    rwa [hb, Subgroup.mem_bot] at this
  exact exists_isHStar_le hInH hGz

end CFSG.Quasithin.H13
