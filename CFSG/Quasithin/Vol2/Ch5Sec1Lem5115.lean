module

public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section General

variable {G : Type} [Group G] [Finite G]

theorem le_of_pCoreOf_sup_ne_bot {H Mp X : Subgroup G} (hU : IsUniqueM H Mp)
    (hX : pCoreOf 2 (X ⊔ H) ≠ ⊥) : X ≤ Mp := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (X ⊔ H) : Set G)) :=
    ⟨pCoreOf 2 (X ⊔ H), hX, pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hsup : X ⊔ H ≤ M' := (le_normalizer_pCoreOf 2 (X ⊔ H)).trans hle
  have hM'eq : M' = Mp := hU.2 M' ⟨hM', le_sup_right.trans hsup⟩
  exact hM'eq ▸ (le_sup_left.trans hsup)

omit [Finite G] in
theorem pCoreOf_ne_bot_of_le_centerOf {X Z : Subgroup G} (hZ2 : IsPGroup 2 Z) (hZ : Z ≠ ⊥)
    (hZX : Z ≤ X) (hZC : Z ≤ Subgroup.centralizer (X : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  intro hbot
  apply hZ
  have hXC : X ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZC
  have hXN : X ≤ Subgroup.normalizer (Z : Set G) :=
    hXC.trans (Subgroup.centralizer_le_normalizer _)
  have := le_pCoreOf_of_le_normalizer 2 hZX hXN hZ2
  rw [hbot] at this
  exact le_bot_iff.mp this

omit [Finite G] in
theorem exists_le_sup_of_isCyclic {D : Subgroup G} (hcyc : IsCyclic ↥D) {a b : ℕ}
    (hab : Nat.Coprime a b) (hD : Nat.card D = a * b) (ha : 0 < a) (hb : 0 < b) :
    ∃ Da Db : Subgroup G, Da ≤ D ∧ Db ≤ D ∧ Nat.card Da = a ∧ Nat.card Db = b ∧
      D ≤ Da ⊔ Db := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf (g : G) = a * b := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hD]
  have hga : (g : G) ^ a ∈ D := D.pow_mem g.2 a
  have hgb : (g : G) ^ b ∈ D := D.pow_mem g.2 b
  refine ⟨Subgroup.zpowers ((g : G) ^ b), Subgroup.zpowers ((g : G) ^ a),
    Subgroup.zpowers_le.mpr hgb, Subgroup.zpowers_le.mpr hga, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, orderOf_pow_of_dvd hb.ne' (hord ▸ dvd_mul_left b a), hord,
      Nat.mul_div_cancel a hb]
  · rw [Nat.card_zpowers, orderOf_pow_of_dvd ha.ne' (hord ▸ dvd_mul_right a b), hord,
      Nat.mul_div_cancel_left b ha]
  · have h1 := Nat.gcd_eq_gcd_ab a b
    rw [hab.gcd_eq_one, Nat.cast_one] at h1
    have hg1 : (g : G) ∈ Subgroup.zpowers ((g : G) ^ b) ⊔ Subgroup.zpowers ((g : G) ^ a) := by
      have he : (g : G) = ((g : G) ^ a) ^ (Nat.gcdA a b) * ((g : G) ^ b) ^ (Nat.gcdB a b) := by
        calc (g : G) = (g : G) ^ (1 : ℤ) := (zpow_one _).symm
          _ = (g : G) ^ ((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b) := by rw [h1]
          _ = ((g : G) ^ a) ^ (Nat.gcdA a b) * ((g : G) ^ b) ^ (Nat.gcdB a b) := by
            rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      have hmem : ((g : G) ^ a) ^ (Nat.gcdA a b) * ((g : G) ^ b) ^ (Nat.gcdB a b) ∈
          Subgroup.zpowers ((g : G) ^ b) ⊔ Subgroup.zpowers ((g : G) ^ a) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
          (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ _))
      rw [← he] at hmem
      exact hmem
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hxk : x = (g : G) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hxk]
    exact Subgroup.zpow_mem _ hg1 k

theorem two_pow_sub_one_mul_add_one (m : ℕ) :
    (2 ^ m - 1) * (2 ^ m + 1) = 2 ^ (2 * m) - 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  zify [h1, h2]
  ring

theorem coprime_two_pow_sub_one_add_one {m : ℕ} (hm : m ≠ 0) :
    Nat.Coprime (2 ^ m - 1) (2 ^ m + 1) := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd h1 ((Nat.even_pow).mpr ⟨even_two, hm⟩) odd_one
  have he : 2 ^ m + 1 = (2 ^ m - 1) + 2 := by omega
  rw [he, Nat.coprime_self_add_right]
  exact Nat.coprime_two_right.mpr hodd

end General

theorem stmt5_1_15_of (h516 : Stmt5_1_6) (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    Stmt5_1_15 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨⟨-, hU, -⟩, ⟨hZH, -⟩, -⟩ := h5114 G T M L V H B D n hyp hN hV hK
  by_cases hDM : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  · exact Or.inl hDM
  right
  have hD := hN.2.1
  have hO : pCoreOf 2 (D ⊔ H) = ⊥ := by
    by_contra hne
    exact hDM (le_of_pCoreOf_sup_ne_bot hU hne)
  obtain ⟨hev, hcase⟩ := h516 G T M L V H D n h hV hH hD hO
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hT1 : T ≠ ⊥ := by
    intro hT
    apply hH.1.2
    have := F7.isSylowTwoOf_pCoreOf_le hTH
    rw [hT] at this
    exact le_bot_iff.mp this
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le hZT
  have hZ1 : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot h.sylow.1 hT1
  have hZHle : quasithinOmegaOneCenter T ≤ H := hZT.trans hH.1.1
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
  rcases hcase with ⟨h2, hsum, -⟩ | ⟨h24, hnat, -⟩ | ⟨-, -, -, hcen⟩ | ⟨-, horth, -, hDpm⟩
  · exact Or.inl ⟨h2, hsum⟩
  · exact Or.inr (Or.inl ⟨h24, hnat⟩)
  · exfalso
    apply hZ1
    have hle : quasithinOmegaOneCenter T ≤ centerOf H := le_inf hZHle hZC
    rw [hcen] at hle
    exact le_bot_iff.mp hle
  · right
    right
    obtain ⟨m, hm⟩ := hev
    have hn2 : n / 2 = m := by omega
    have hm0 : m ≠ 0 := by have := h.two_le; omega
    obtain ⟨hcyc, hcard⟩ := h.isCyclic_card_of_isHall hF hD
    have hcard' : Nat.card D = (2 ^ (n / 2) - 1) * (2 ^ (n / 2) + 1) := by
      rw [hcard, hn2, two_pow_sub_one_mul_add_one, hm, two_mul]
    have hpos1 : 0 < 2 ^ (n / 2) - 1 := by
      have : 2 ≤ 2 ^ (n / 2) := by
        rw [hn2]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm0)
      omega
    obtain ⟨Dp, Dm, hDp, hDm, hcDp, hcDm, hDle⟩ := exists_le_sup_of_isCyclic hcyc
      (hn2 ▸ coprime_two_pow_sub_one_add_one hm0) hcard' hpos1 (by positivity)
    have hminus : ∀ Dm' : Subgroup G, Dm' ≤ D → Nat.card Dm' = 2 ^ (n / 2) + 1 →
        Dm' ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
      intro Dm' hDm' hcDm'
      obtain ⟨hcen, -⟩ := hDpm Dp Dm' hDp hDm' hcDp hcDm'
      refine le_of_pCoreOf_sup_ne_bot hU ?_
      exact pCoreOf_ne_bot_of_le_centerOf hZ2 hZ1 (hcen.trans inf_le_left)
        (hcen.trans inf_le_right)
    refine ⟨?_, horth, hminus⟩
    have hDpM : ¬ Dp ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun hle =>
      hDM (hDle.trans (sup_le hle (hminus Dm hDm hcDm)))
    obtain ⟨-, hor⟩ := hDpm Dp Dm hDp hDm hcDp hcDm
    rcases hor with hne | h48
    · exact absurd (le_of_pCoreOf_sup_ne_bot hU hne) hDpM
    · exact h48

end CFSG.Quasithin.H13
