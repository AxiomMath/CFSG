module

public import CFSG.Quasithin.Vol2.Ch7S7Row
public import CFSG.Quasithin.Vol2.Ch8Sec1
public import CFSG.Quasithin.Background.HA7Cent
public import CFSG.Quasithin.Background.E6Gamma

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def Input7_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), ∀ U : Subgroup G,
      U ∈ E6.gammaE64 (fsuV T I) (fsuM T L) →
      (∀ W : Subgroup G, U ≤ W → W ≤ fsuV T I →
        ¬ Subgroup.centralizer (W : Set G) ≤ fsuM T L → W = U) →
      1 < mQuot (fsuV T I) U →
        ∃ y ∈ autI hV (fsuM T L ⊓ Subgroup.centralizer (U : Set G)),
          orderOf y = 2 ^ mQuot (fsuV T I) U - 1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_ti {V M U : Subgroup G} (hTI : IsTISetUnder V M) (hUV : U ≤ V)
    (hU : U ≠ ⊥) {g : G} (hgM : g ∈ M) (hgU : g ∈ Subgroup.centralizer (U : Set G)) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  by_contra hgN
  apply hU
  rw [eq_bot_iff, ← hTI g hgM hgN]
  intro u hu
  refine Subgroup.mem_inf.2 ⟨hUV hu, ?_⟩
  have hcomm : g * u = u * g := (Subgroup.mem_centralizer_iff.1 hgU u hu).symm
  refine ⟨u, hUV hu, ?_⟩
  change g⁻¹ * u * g⁻¹⁻¹ = u
  rw [inv_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem twoPrimeResidual_le_inf_centralizer {H V : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ y ∈ H, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ∈ Subgroup.centralizer (V : Set G)) :
    twoPrimeResidual H ≤ H ⊓ Subgroup.centralizer (V : Set G) := by
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two H
  have hSC : S ≤ Subgroup.centralizer (V : Set G) := fun s hs => by
    obtain ⟨k, hk⟩ := hS.2.1 ⟨s, hs⟩
    exact h s (hS.1 hs) ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine iInf₂_le (H ⊓ Subgroup.centralizer (V : Set G))
    ⟨inf_le_left, B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer hHN), fun h2 => ?_⟩
  exact hS.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left H (le_inf hS.1 hSC)))

omit [Finite G] in
theorem mem_centralizer_of_twoElement {V M U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : IsTISetUnder V M) (hUV : U ≤ V) (hU : U ≠ ⊥)
    (hinv : ∀ x ∈ autI hV ⊤, x * x = 1 → U.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers x) →
      x = 1)
    {g : G} (hgM : g ∈ M) (hgU : g ∈ Subgroup.centralizer (U : Set G))
    (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ∈ Subgroup.centralizer (V : Set G) := by
  have hgN := mem_normalizer_of_ti hTI hUV hU hgM hgU
  set x := convI hV ⟨g, hgN⟩ with hx
  have hxA : x ∈ autI hV ⊤ := convI_mem_autI hV (Subgroup.mem_top g) hgN
  have hxU : U.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers x) := by
    refine A7.le_fixV_zpowers fun v hv => IntMod.val_injective ?_
    have hvU : v.val ∈ U := hv
    have h1 : (x v).val = g * v.val * g⁻¹ := convI_apply_val hV ⟨g, hgN⟩ v
    rw [h1, ← Subgroup.mem_centralizer_iff.mp hgU _ hvU, mul_inv_cancel_right]
  obtain ⟨k, hk⟩ := hg2
  have hxk : x ^ 2 ^ k = 1 := by
    have h1 : (⟨g, hgN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact hk)
    rw [hx, ← map_pow, h1, map_one]
  have hx1 : x = 1 := by
    by_contra hx1
    obtain ⟨j, -, hxo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxk)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by rw [hxo, pow_zero]))
    have hlt : 2 ^ (j - 1) < orderOf x := by
      rw [hxo]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    apply pow_ne_one_of_lt_orderOf (by positivity) hlt
    refine hinv _ (Subgroup.pow_mem _ hxA _) ?_ fun v hv a ha =>
      hxU hv a (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) ha)
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0),
      ← hxo, pow_orderOf_eq_one]
  exact (convI_eq_one_iff hV ⟨g, hgN⟩).mp hx1

theorem mem_gammaE64_of {V M W : Subgroup G} (hTI : IsTISetUnder V M) (hWV : W ≤ V)
    (hW : W ≠ ⊥) (hCW : ¬ Subgroup.centralizer (W : Set G) ≤ M)
    (h2 : ∀ g ∈ M ⊓ Subgroup.centralizer (W : Set G), (∃ k : ℕ, g ^ 2 ^ k = 1) →
      g ∈ Subgroup.centralizer (V : Set G)) :
    W ∈ E6.gammaE64 V M := by
  refine ⟨hWV, hW, hCW, ?_⟩
  have hHN : M ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun g hg => mem_normalizer_of_ti hTI hWV hW hg.1 hg.2
  exact (twoPrimeResidual_le_inf_centralizer hHN h2).trans (inf_le_inf_right _ inf_le_left)

theorem exists_maximal_centralizer {V M U : Subgroup G} (hUV : U ≤ V)
    (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ M) :
    ∃ U₂ : Subgroup G, U ≤ U₂ ∧ U₂ ≤ V ∧ ¬ Subgroup.centralizer (U₂ : Set G) ≤ M ∧
      ∀ W : Subgroup G, U₂ ≤ W → W ≤ V → ¬ Subgroup.centralizer (W : Set G) ≤ M → W = U₂ := by
  classical
  let P : ℕ → Prop := fun n => ∃ W : Subgroup G, U ≤ W ∧ W ≤ V ∧
    ¬ Subgroup.centralizer (W : Set G) ≤ M ∧ Nat.card W = n
  obtain ⟨U₂, hUU₂, hU₂V, hCU₂, hc⟩ :=
    Nat.findGreatest_spec (P := P) (Subgroup.card_le_card_group U) ⟨U, le_rfl, hUV, hCU, rfl⟩
  refine ⟨U₂, hUU₂, hU₂V, hCU₂, fun W hW hWV hCW => ?_⟩
  have h1 : Nat.card W ≤ Nat.findGreatest P (Nat.card G) :=
    Nat.le_findGreatest (Subgroup.card_le_card_group W) ⟨W, hUU₂.trans hW, hWV, hCW, rfl⟩
  exact (Subgroup.eq_of_le_of_card_ge hW (by rw [hc]; exact h1)).symm

theorem stmt7_5_5_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h734 : Stmt7_3_4)
    (hin : Input8_1_2) (h755 : Input7_5_5) : Stmt7_5_5 := by
  intro G _ _ T L I hyp h731 hc hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h711 G T L I hyp hc
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hrow)))))))))))))
  have hLM := fsuM_le_normalizer_of_le_normalizer hTL
  have hTI : IsTISetUnder (fsuV T I) (fsuM T L) :=
    isTISetUnder_of_stmt3_2_5_of_le_normalizer h325 hyp.fsu hTL
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hA7 : A7Four (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥ := hnat
  have hMN := autI_top_le_normalizer hV hNM
  obtain ⟨hcard, hord, hcent⟩ := A7.H8_A7Pair_cent hA7 hφN hinf hsup hniso hMN
  have hF1 := (A7.H8_A7Pair_alpha hA7 hφN hinf hsup hniso hMN).1
  obtain ⟨-, -, hm2, -, -⟩ := stmt7_2_1_S7 G T L I hV hN hNM hc ⟨htw, hnat⟩
  obtain ⟨-, hwn, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hk : nPrime (autI hV ⊤) = 2 := (hn' hc).2.2.2.2.2.2.2.1 ⟨htw, hnat⟩
  have hr5 : rParam (fsuV T I) ≤ 5 := by
    have hfw := lemma_7_5_1 hyp hV hN hNM
    rw [hk] at hwn
    calc rParam (fsuV T I)
        ≤ ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T (fsuV T I) := hfw
      _ ≤ ((3 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) := add_le_add (by exact_mod_cast hm2) hwn
      _ = 5 := by norm_num
  have hodd : ∀ W : Subgroup G, W ≤ fsuV T I → W ≠ ⊥ →
      ¬ Subgroup.centralizer (W : Set G) ≤ fsuM T L →
      ∃ y ∈ autI hV ⊤, y ≠ 1 ∧ Odd (orderOf y) ∧
        W.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers y) := by
    intro W hWV hW hCW
    rcases hin G T L I hyp h731 hLM hV W hWV hW hCW with ⟨A, hA, -⟩ | ⟨y, hy, hy1, hyo, hfix⟩
    · exact (hF1 ⟨A, hA⟩).elim
    · exact ⟨y, hy, hy1, hyo, (leFixI_iff hV).1 hfix⟩
  have hr6 : (6 : ℕ∞) ≤ rParam (fsuV T I) := by
    unfold rParam
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hC⟩ := hU
    by_contra hlt
    have hU5 : mQuot (fsuV T I) U ≤ 5 := by
      push Not at hlt
      have : mQuot (fsuV T I) U < 6 := by exact_mod_cast hlt
      omega
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      have h1 := E3.card_eq_two_pow_mul (isPGroup_of_isElemAbelian_two hV)
        (bot_le : (⊥ : Subgroup G) ≤ fsuV T I)
      have h2 : Nat.card ↥(fsuV T I) = 2 ^ 8 := hcard
      rw [Subgroup.card_bot, mul_one, h2] at h1
      have := Nat.pow_right_injective (le_refl 2) h1
      omega
    have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun h =>
      hC fun g hg => mem_normalizer_of_ti hTI hUV hU1 (h hg) hg
    obtain ⟨y, hy, hy1, hyo, hfix⟩ := hodd U hUV hU1 hCM
    have hrkU := mQuot_eq_rkIdx_comap hV hUV
    have hinv := (hcent y hy hy1 hyo _ hfix).2 (by rw [← hrkU]; exact hU5)
    have h2 : ∀ W : Subgroup G, U ≤ W → ∀ g ∈ fsuM T L ⊓ Subgroup.centralizer (W : Set G),
        (∃ k : ℕ, g ^ 2 ^ k = 1) → g ∈ Subgroup.centralizer (fsuV T I : Set G) :=
      fun W hUW g hg hg2 => mem_centralizer_of_twoElement hV hTI hUV hU1 hinv hg.1
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUW) hg.2) hg2
    obtain ⟨U₂, hUU₂, hU₂V, hCU₂, hmax⟩ := exists_maximal_centralizer hUV hCM
    have hU₂1 : U₂ ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUU₂))
    have hΓ := mem_gammaE64_of hTI hU₂V hU₂1 hCU₂ (h2 U₂ hUU₂)
    have hle5 : mQuot (fsuV T I) U₂ ≤ 5 := (E3.mQuot_mono hUU₂).trans hU5
    obtain ⟨y₂, hy₂, hy₂1, hy₂o, hfix₂⟩ := hodd U₂ hU₂V hU₂1 hCU₂
    have hge4 : 4 ≤ mQuot (fsuV T I) U₂ := by
      rw [mQuot_eq_rkIdx_comap hV hU₂V]
      exact (hcent y₂ hy₂ hy₂1 hy₂o _ hfix₂).1
    obtain ⟨z, hz, hzo⟩ := h755 G T L I hyp hV U₂ hΓ hmax (by omega)
    have hzA : z ∈ autI hV ⊤ := autI_mono hV le_top hz
    rcases (show mQuot (fsuV T I) U₂ = 4 ∨ mQuot (fsuV T I) U₂ = 5 by omega) with h | h
    · rw [h] at hzo
      exact (hord z hzA).1 hzo
    · rw [h] at hzo
      exact (hord z hzA).2 hzo
  have h65 : (6 : ℕ∞) ≤ 5 := hr6.trans hr5
  have : (6 : ℕ) ≤ 5 := by exact_mod_cast h65
  omega

end CFSG.Quasithin.H13
