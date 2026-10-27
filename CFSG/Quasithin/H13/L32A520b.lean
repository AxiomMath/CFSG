module

public import CFSG.Quasithin.H13.L32A74
public import CFSG.Quasithin.H13.L32ASk5
public import CFSG.Quasithin.H13.U3S1349A

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_card_map {Y K : Subgroup G} (hKY : K ≤ Y) :
    (pCoreOf 2 Y).relIndex K =
      Nat.card ((K.subgroupOf Y).map (QuotientGroup.mk' ((pCoreOf 2 Y).subgroupOf Y))) := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hKY]

theorem oTwoUpper_sup_pCoreOf_eq {Y K : Subgroup G} (hQK : pCoreOf 2 Y ≤ K)
    (h3 : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 Y) : oTwoUpper K ⊔ pCoreOf 2 Y = K := by
  refine le_antisymm (sup_le (oTwoUpper_le K) hQK) fun k hk => ?_
  obtain ⟨j, hj⟩ := exists_pow_mem_oTwoUpper K hk
  have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : k = (k ^ 2 ^ j) ^ u * (k ^ 3) ^ v := by
    calc k = k ^ (u * ((2 ^ j : ℕ) : ℤ) + v * ((3 : ℕ) : ℤ)) := by rw [huv, zpow_one]
      _ = (k ^ 2 ^ j) ^ u * (k ^ 3) ^ v := by
        rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (zpow_mem hj u))
    (Subgroup.mem_sup_right (zpow_mem (h3 k hk) v))

theorem oTwoUpper_inf_pCoreOf {Y K : Subgroup G} (hKY : K ≤ Y)
    (h3 : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 Y) :
    oTwoUpper K ⊓ pCoreOf 2 Y = pCoreOf 2 (oTwoUpper K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKY' : oTwoUpper K ≤ Y := (oTwoUpper_le K).trans hKY
  refine le_antisymm (le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      le_normalizer_pCoreOf 2 Y (hKY' hx)⟩) ((pCoreOf_isPGroup 2 Y).to_le inf_le_right)) ?_
  refine le_inf (pCoreOf_le 2 _) fun x hx => ?_
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (oTwoUpper K) ⟨x, hx⟩
  have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime 3 (orderOf x) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hm')
    rw [hi]
    exact Nat.Coprime.pow_right i (by norm_num)
  exact (Subgroup.zpowers_le.mpr (h3 x ((oTwoUpper_le K) (pCoreOf_le 2 _ hx))))
    (A4.mem_zpowers_pow_of_coprime hcop)

theorem relIndex_oTwoUpper_eq {Y K : Subgroup G} (hQK : pCoreOf 2 Y ≤ K) (hKY : K ≤ Y)
    (h3 : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 Y) :
    (pCoreOf 2 (oTwoUpper K)).relIndex (oTwoUpper K) = (pCoreOf 2 Y).relIndex K := by
  have hQN : pCoreOf 2 Y ≤ Subgroup.normalizer (oTwoUpper K : Set G) :=
    hQK.trans (le_normalizer_oTwoUpper K)
  rw [← oTwoUpper_inf_pCoreOf hKY h3, ← U3.relIndex_sup_eq hQN, oTwoUpper_sup_pCoreOf_eq hQK h3]

theorem classLeTwo_of_card_le {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (hc : Nat.card P ≤ p ^ 3) : ClassLeTwo (⊤ : Subgroup P) := by
  rcases subsingleton_or_nontrivial P with hs | hnt
  · exact Subsingleton.elim _ _
  have hZ := hP.center_nontrivial
  have hZp : p ≤ Nat.card (Subgroup.center P) := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup (Subgroup.center P)).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
    rw [hk]
    exact Nat.le_self_pow hk0 p
  have hQ : Nat.card (P ⧸ Subgroup.center P) ≤ p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    by_contra hlt
    push Not at hlt
    have h2 : p ^ 2 * p < Nat.card (P ⧸ Subgroup.center P) * Nat.card (Subgroup.center P) := by
      calc p ^ 2 * p < Nat.card (P ⧸ Subgroup.center P) * p :=
            Nat.mul_lt_mul_of_pos_right hlt hp.out.pos
        _ ≤ _ := Nat.mul_le_mul_left _ hZp
    rw [← h1, ← pow_succ, show (2 : ℕ) + 1 = 3 from rfl] at h2
    omega
  have hcomm := commutative_of_card_le_prime_sq (hP.to_quotient (Subgroup.center P)) hQ
  have hle : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hcomm (x : P ⧸ Subgroup.center P) (y : P ⧸ Subgroup.center P)]
    group
  rw [ClassLeTwo, eq_bot_iff]
  calc ⁅⁅(⊤ : Subgroup P), ⊤⁆, ⊤⁆ ≤ ⁅Subgroup.center P, ⊤⁆ := Subgroup.commutator_mono hle le_rfl
    _ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro z hz w _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hz w).symm

theorem exp_three_cases {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hexp : ∀ x : P, x ^ 3 = 1) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup P) ≤ 2) :
    Nat.card P = 3 ∨ IsElemAbelianOfRank 3 2 P ∨ IsPOnePlusTwo 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 P := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  by_cases h1 : CFSG.Open.pRank 3 (⊤ : Subgroup P) ≤ 1
  · left
    obtain ⟨z, -, hz, hzo⟩ := exists_eq_zpowers_of_pRank_le_one hP (X := ⊤)
      (by simp) (fun x _ => hexp x) h1
    rw [← Subgroup.card_top (G := P), hz, Nat.card_zpowers, hzo]
  · right
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup P) = 2 := by omega
    obtain ⟨hc, -⟩ := CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hP hexp hr
    exact isElemAbelianOfRank_two_or_isPOnePlusTwo (by norm_num) hP
      (eq_top_iff.mpr fun x _ => Subgroup.subset_closure (hexp x)) h2 (classLeTwo_of_card_le hP hc)

section Setting

variable {T L V H : Subgroup G}

theorem normalizer_T_le (h331 : Stmt3_3_1) (h1332 : Stmt13_3_2) (S : Setting147 G T L V H) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hL13 := h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
  exact (h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).1 _ L
    hL13.2.1.2.2.1 hL13.2.1.1 S.hyp.fsu.maximal Subgroup.le_normalizer S.hyp.fsu.quasisimple

theorem le_M_of_index_three (h331 : Stmt3_3_1) (hThm : Thm14_5_3) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {Y₁ : Subgroup G}
    (hY₁H : Y₁ ≤ H) (hY₁o : oTwoUpper Y₁ = Y₁) (hTY₁ : T ≤ Subgroup.normalizer (Y₁ : Set G))
    (h3 : (pCoreOf 2 Y₁).relIndex Y₁ = 3)
    (hperm : (Y₁ : Set G) * (l1 T L V : Set G) = (l1 T L V : Set G) * (Y₁ : Set G)) :
    Y₁ ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO₂T : pCoreOf 2 Y₁ ≤ T := by
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y₁).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 Y₁)).trans (pCoreOf_le_of_le S.hyp le_sup_right)
    exact sup_le (le_normalizer_pCoreOf 2 Y₁) (F7.le_normalizer_pCoreOf_of_le_normalizer hTY₁)
  have hinf : (Y₁ ⊓ T).relIndex Y₁ = 3 := by
    have hle : pCoreOf 2 Y₁ ≤ Y₁ ⊓ T := le_inf (pCoreOf_le 2 Y₁) hO₂T
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
    rw [h3] at hmul
    have hd : (Y₁ ⊓ T).relIndex Y₁ ∣ 3 := ⟨_, by rw [mul_comm]; exact hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h
      have hY₁2 : IsPGroup 2 Y₁ := S.hyp.fsu.sylow.1.to_le (h.trans inf_le_right)
      have hY₁O : Y₁ ≤ pCoreOf 2 Y₁ :=
        le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hY₁2
      rw [Subgroup.relIndex_eq_one.mpr hY₁O] at h3
      exact absurd h3 (by norm_num)
    · exact h
  have hT3 : T.relIndex (Y₁ ⊔ T) = 3 := by rw [U3.relIndex_sup_eq hTY₁, hinf]
  by_cases hN : Y₁ ⊔ T ≤ Subgroup.normalizer (T : Set G)
  · exact (le_sup_left.trans hN).trans (normalizer_T_le h331 h1332 S)
  · have hsyl : IsSylowTwoOf T (Y₁ ⊔ T) :=
      isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow le_sup_right
    have hS3 := U3.quot_S3_of_index_three hsyl hT3 hN
    have hMod := stmtL32NModule_of_inputs h1332 h1334
    obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
    have hY₁G : Y₁ ≤ A6.g1 T V := hY₁H.trans S.hz.2.1
    exact (hThm G T L V S.hyp Y₁ V₂ hV2 hY₁o hY₁G hTY₁ hS3).2.1 hperm

end Setting

end CFSG.Quasithin.H13.L32A
