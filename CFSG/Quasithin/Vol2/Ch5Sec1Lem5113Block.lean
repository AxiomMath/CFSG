module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Four
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113DMinus
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_1_13_four_be : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      2 < n ∧ D ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) ∧
        ∃ V' : Subgroup G, IsCh5Module T L V' ∧ IsNatQuotCh5 L V' n

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem false_of_block (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (ty : Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H)) (hn : 2 < n)
    (hDK : D ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G)) {V' : Subgroup G}
    (hV' : IsCh5Module T L V') (hnat : IsNatQuotCh5 L V' n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  have hD := m.nota.2.1
  obtain ⟨-, -, D₃, hD₃, hD₃3, -, hDKh, t, htTK, htinv⟩ := ty
  obtain ⟨d, hdD₃, hd1⟩ : ∃ d ∈ D₃, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have hb : D₃ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [hb, Subgroup.card_bot] at hD₃3
    omega
  have hd3 : d ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨d, hdD₃⟩ : ↥D₃)
    rw [hD₃3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdD : d ∈ D := (hD₃ hdD₃).1
  have h3 : 3 ∣ 2 ^ n - 1 := by
    rw [← (h.isCyclic_card_of_isHall l2TorusFact hD).2]
    have := orderOf_dvd_natCard (⟨d, hdD⟩ : ↥D)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd3 hd1] at this
  have hev : Even n := by
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exfalso
      obtain ⟨i, rfl⟩ := ho
      have h1 : 2 ^ (2 * i + 1) % 3 = 2 := by
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      have h2 := Nat.one_le_two_pow (n := 2 * i + 1)
      obtain ⟨x, hx⟩ : ∃ x, x = 2 ^ (2 * i + 1) := ⟨_, rfl⟩
      rw [← hx] at h1 h2 h3
      omega
  obtain ⟨k, hk⟩ := hev
  have hred := hV'.isTwoReducedIn
  have hTV : T ≤ Subgroup.normalizer (V' : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hred.2.1
  have hS := h.isSylowTwoOf_inf
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V' : Set G) ≤ T :=
    (h.setting516 hD hV').sup_inf_centralizer_le hred.2.1 fun hle => hV'.2.2
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle))
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hnat.exists_qcoord hS
  have hF' : Nat.card F = 2 ^ (2 * k) := by rw [hF, hk, two_mul]
  obtain ⟨Dm, hDmD, hDmc⟩ := exists_dMinus hLV ψ hc.sylow hF' hCV hS hD
  have hTK : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) := le_normalizer_conjClosure Kh₁ T
  have hle := le_one_of_dMinus hLV ψ hc.sylow hF' h.T_le_normalizer hTV hCV hS hD hDmD hDmc
    htTK.1 hdD hd1 hd3 (htinv d hdD₃) htTK.2 (hDmD.trans hDK) (inf_le_left.trans hTK) hDKh hD₃3
  omega

end Main513

theorem stmt5_1_13_four_star_of (hbe : Stmt5_1_13_four_be) : Stmt5_1_13_four_star := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax
  by_contra hZ
  obtain ⟨hn, hDK, V', hV', hnat⟩ := hbe G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  exact m.false_of_block ty hn hDK hV' hnat

end CFSG.Quasithin.H13
