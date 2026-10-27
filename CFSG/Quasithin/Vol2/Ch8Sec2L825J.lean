module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825I

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L825J

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rk_comap_valHom_82 {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V) :
    rk ↥(U.comap (E3.valHom hV)) = rk ↥U := by
  unfold rk
  rw [← Subgroup.card_map_of_injective (E3.valHom_injective hV), map_comap_valHom hV hUV]

theorem exists_cartan_elt_82 {T M V : Subgroup G} {h : G} {k : ℕ} (hV : IsElemAbelian 2 V)
    (hk : 2 ≤ k) (hhI : h ∈ ch82I V h)
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ ch82I V h) (ch82I V h))
    (hMIeq : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G))
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hI : IsPSL 2 2 k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) ∨
      IsSz k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hVZ : E2.star (M ⊓ ch82I V h) (ch82I V h) V ≤
      E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h))
    (hBor : E2.star (M ⊓ ch82I V h) (ch82I V h) (M ⊓ ch82I V h) =
      Subgroup.normalizer (E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h) :
        Set (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))))
    (h9 : ∀ X : Subgroup G, X ≤ M ⊓ ch82I V h → Nat.card ↥X = 2 ^ k - 1 →
      V ⊓ Subgroup.centralizer (X : Set G) = ch82ZI V h) :
    ∃ x ∈ M ⊓ ch82I V h, ∃ hxN : x ∈ Subgroup.normalizer (V : Set G),
      orderOf x = 2 ^ k - 1 ∧
      V ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = ch82ZI V h ∧
      (IsPSL 2 2 k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) →
        orderOf (convI hV ⟨x, hxN⟩) = 2 ^ k - 1) := by
  have hK : IsPGroup 2 ↥(kerIn (M ⊓ ch82I V h) (ch82I V h)) := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (ch82I V h)
  obtain ⟨X, hXMI, hXcyc, hXc, hXK⟩ := exists_cartan_82 hK hSyl hBor hk hI
  obtain ⟨x, hxX, -, hxo⟩ := exists_zpowers_eq_82 hXcyc
  rw [hXc] at hxo
  have hNV : M ⊓ ch82I V h ≤ Subgroup.normalizer (V : Set G) := by
    rw [hMIeq]
    exact inf_le_right
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXMI.trans hNV
  refine ⟨x, hXMI hxX, hXN hxX, hxo, ?_, fun hPSL => ?_⟩
  · exact h9 (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr (hXMI hxX))
      (by rw [Nat.card_zpowers, hxo])
  · have hnt : Nontrivial (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 k hPSL).1
    have hV1 := star_ne_bot_82 hhI hker hnt
    have hodd : Odd (Nat.card ↥X) := by
      rw [hXc]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have hf : ∀ y ∈ X, y ∈ Subgroup.centralizer (V : Set G) → y = 1 := fun y hy hyc =>
      eq_one_of_cent_cartan_82 hk hPSL hSyl hBor hVZ hV1 hXMI hXK hodd hy hyc
    exact (orderOf_convI_82 hV hXN hf hxX).trans hxo

theorem false_of_l3_two_mul_82 (hE214 : AS_E_2_14) {H T M V : Subgroup G} {h : G} {n : ℕ}
    (hV : IsElemAbelian 2 V) (hn : 1 ≤ n)
    (hhI : h ∈ ch82I V h) (hIC : IsInIHTVC H T (H ⊓ M) V (ch82I V h)) (hZ1 : ch82ZI V h ≠ ⊥)
    (h28 : E2.Hyp28 H T (H ⊓ M) V) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn V (H ⊓ M))
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ ch82I V h) (ch82I V h))
    (hMIeq : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G))
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hPSL : IsPSL 2 2 (2 * n) (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hVZ : E2.star (M ⊓ ch82I V h) (ch82I V h) V ≤
      E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h))
    (hBor : E2.star (M ⊓ ch82I V h) (ch82I V h) (M ⊓ ch82I V h) =
      Subgroup.normalizer (E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h) :
        Set (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))))
    (hA7 : ch82A V h = B6.conjSub h V ⊓ Subgroup.normalizer (V : Set G))
    (hm2 : CFSG.Open.pRank 2 (autI hV ⊤) ≤ 4 * n) (hFF : ¬ IsFFModule (autI hV ⊤))
    (hcard : Nat.card ↥V = 2 ^ (9 * n)) {Lb : Subgroup (MulAut (IntMod V hV))}
    (hL6 : ∀ A : Subgroup (MulAut (IntMod V hV)), A ≤ autI hV ⊤ → IsElemAbelian2 A →
      2 * n + 1 < rk ↥A → A ≤ Lb)
    (hL4 : ∀ A : Subgroup (MulAut (IntMod V hV)), A ≤ Lb → IsElemAbelian2 A → rk ↥A = 4 * n →
      ∀ x ∈ autI hV ⊤ ⊓ Subgroup.normalizer (A : Set (MulAut (IntMod V hV))),
        orderOf x = 2 ^ (2 * n) - 1 → rk ↥(fixV (A ⊔ Subgroup.zpowers x)) ≠ 3 * n) : False := by
  obtain ⟨-, h6, h7, -, h9⟩ :=
    e214_82 hE214 hV hhI hIC hZ1 h28 hchar hTI (Or.inr (Or.inl ⟨2 * n, hPSL⟩))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : 2 ≤ 2 * n := by omega
  have hAle : Nat.card ↥(autI hV (ch82A V h)) ≤ 2 ^ (2 * (2 * n)) :=
    (card_autI_ch82A_le_82 hV hA7).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨hAc, hZc⟩ := h7 (2 * n) (Or.inl hPSL) hAle (one_lt_qOf_82 hV (ch82I V h) hFF)
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  have hrkA : rk ↥(autI hV (ch82A V h)) = 4 * n := by
    unfold rk
    rw [hAc, padicValNat.prime_pow]
    ring
  have hAL : autI hV (ch82A V h) ≤ Lb := hL6 _ (autI_mono hV le_top) hAel2 (by omega)
  obtain ⟨x, hxMI, hxN, -, hxV, hxo⟩ := exists_cartan_elt_82 hV hk hhI hSyl hMIeq hker
    (Or.inl hPSL) hVZ hBor (h9 (2 * n) (by omega) hPSL)
  have hxA := h6 (convI_mem_autI hV hxMI.2 hxN)
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := M) hIC.1] at hcl
  have hP := pair_82 hV h28.le_T h28.normal_T hSyl hMIeq hhI hcl
  have hfix : fixV (autI hV (ch82A V h) ⊔ Subgroup.zpowers (convI hV ⟨x, hxN⟩)) =
      (ch82ZI V h).comap (E3.valHom hV) := by
    rw [fixV_sup_82, ← autI_zpowers_82 hV hxN, fixV_autI_eq_comap hV hAN,
      fixV_autI_eq_comap hV (Subgroup.zpowers_le.mpr hxN), hxV, ← Subgroup.comap_inf]
    congr 1
    exact inf_eq_right.mpr (ch82ZI_le_ch82U_82 hP)
  have hrkZ : rk ↥(ch82ZI V h) = 3 * n := by
    have h1 := mQuot_add_rk (A := V) (B := ch82ZI V h) inf_le_left
    have h2 : mQuot V (ch82ZI V h) = 3 * (2 * n) := by
      unfold mQuot
      rw [hZc, padicValNat.prime_pow]
    have h3 : rk ↥V = 9 * n := by
      unfold rk
      rw [hcard, padicValNat.prime_pow]
    omega
  apply hL4 _ hAL hAel2 hrkA (convI hV ⟨x, hxN⟩)
    ⟨convI_mem_autI hV (Subgroup.mem_top x) hxN, hxA⟩ (hxo hPSL)
  rw [hfix, rk_comap_valHom_82 hV (U := ch82ZI V h) inf_le_left, hrkZ]

end L825J

end CFSG.Quasithin.H13
