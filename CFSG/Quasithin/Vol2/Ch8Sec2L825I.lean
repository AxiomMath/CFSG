module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825H
public import CFSG.Quasithin.Vol2.Ch7Lem756Two
public import CFSG.Quasithin.Vol2.Ch8Sec2L825F
public import CFSG.Quasithin.Vol2.Ch8Sec2L825G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L825I

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ch82ZI_le_ch82U_82 {T M V : Subgroup G} {h : G}
    (hP : E2.Pair (ch82I V h) T M V h) : ch82ZI V h ≤ ch82U V h := by
  intro z hz
  refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  exact hP.comm_conj ha.1 hz.2

omit [Finite G] in
theorem ch82A_facts_82 {V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hA7 : ch82A V h = B6.conjSub h V ⊓ Subgroup.normalizer (V : Set G)) :
    IsElemAbelian 2 (ch82A V h) ∧ ch82A V h ≤ Subgroup.normalizer (V : Set G) := by
  have hVh : IsElemAbelian 2 (B6.conjSub h V) := by
    rw [conjSub_eq_conjSubgroup_82]
    exact isElemAbelian_conjSubgroup hV _
  exact ⟨B2F.isElemAbelian_mono inf_le_left hVh, hA7 ▸ inf_le_right⟩

theorem false_of_code_two_82 (hE214 : AS_E_2_14) {H T M V : Subgroup G} {h : G}
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hhI : h ∈ ch82I V h) (hIC : IsInIHTVC H T (H ⊓ M) V (ch82I V h)) (hZ1 : ch82ZI V h ≠ ⊥)
    (h28 : E2.Hyp28 H T (H ⊓ M) V) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn V (H ⊓ M))
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ ch82I V h) (ch82I V h))
    (hMIeq : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G))
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hPSL : IsPSL 2 2 2 (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hVZ : E2.star (M ⊓ ch82I V h) (ch82I V h) V ≤
      E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h))
    (hBor : E2.star (M ⊓ ch82I V h) (ch82I V h) (M ⊓ ch82I V h) =
      Subgroup.normalizer (E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h) :
        Set (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))))
    (hA7 : ch82A V h = B6.conjSub h V ⊓ Subgroup.normalizer (V : Set G))
    (hm2 : CFSG.Open.pRank 2 (autI hV ⊤) ≤ 6) (hFF : ¬ IsFFModule (autI hV ⊤))
    (h167 : ∀ s : ℕ, (s = 2 ∨ s = 3) → ∀ A Y : Subgroup (MulAut (IntMod V hV)),
      A ≤ autI hV ⊤ → Y ≤ autI hV ⊤ → IsElemAbelian2 A → Nat.card ↥A = 2 ^ (2 * s) →
        Nat.card ↥Y = 3 → ⁅A, Y⁆ = A → rkIdx (fixV (A ⊔ Y)) ≠ 2 * (s + 1)) : False := by
  obtain ⟨h3, h6, -, h8, h9⟩ :=
    e214_82 hE214 hV hhI hIC hZ1 h28 hchar hTI (Or.inr (Or.inl ⟨2, hPSL⟩))
  have hAle : Nat.card ↥(autI hV (ch82A V h)) ≤ 2 ^ 6 :=
    (card_autI_ch82A_le_82 hV hA7).trans (Nat.pow_le_pow_right (by norm_num) hm2)
  obtain ⟨s, hs, hAs, hZs⟩ := h8 hPSL hAle (one_lt_qOf_82 hV (ch82I V h) hFF)
  have hK : IsPGroup 2 ↥(kerIn (M ⊓ ch82I V h) (ch82I V h)) := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (ch82I V h)
  obtain ⟨X, hXMI, hXcyc, hXc, hXK⟩ := exists_cartan_82 hK hSyl hBor le_rfl (Or.inl hPSL)
  have hXc3 : Nat.card ↥X = 3 := by rw [hXc]; norm_num
  obtain ⟨x, hxX, -, hxo⟩ := exists_zpowers_eq_82 hXcyc
  rw [hXc3] at hxo
  have hNV : M ⊓ ch82I V h ≤ Subgroup.normalizer (V : Set G) := by
    rw [hMIeq]
    exact inf_le_right
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXMI.trans hNV
  have hxN : x ∈ M ⊓ ch82I V h := hXMI hxX
  have hnt : Nontrivial (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 hPSL).1
  have hV1 := star_ne_bot_82 hhI hker hnt
  have hf : ∀ y ∈ X, y ∈ Subgroup.centralizer (V : Set G) → y = 1 := fun y hy hyc =>
    eq_one_of_cent_cartan_82 le_rfl hPSL hSyl hBor hVZ hV1 hXMI hXK
      (by rw [hXc3]; decide) hy hyc
  have hxo' : orderOf (convI hV ⟨x, hXN hxX⟩) = 3 :=
    (orderOf_convI_82 hV hXN hf hxX).trans hxo
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := M) hIC.1] at hcl
  have hP := pair_82 hV hVT hTV hSyl hMIeq hhI hcl
  have h3' : ∀ Y : Subgroup G, Y ≤ M ⊓ ch82I V h → Nat.card ↥Y = 3 →
      ∀ p ∈ e214P V (ch82I V h) h,
        (∀ y ∈ Y, y * p * y⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub h V) → p ∈ V ⊓ B6.conjSub h V :=
    fun Y hY hYc => h3 2 (by norm_num) hPSL Y hY (hYc.trans (by norm_num))
  have hxA := h6 (convI_mem_autI hV hxN.2 (hXN hxX))
  have hcomm := commutator_autI_eq_82 hV hP hNV h3' hxN hxo hxA
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hxV : V ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      ch82ZI V h :=
    h9 2 (by norm_num) hPSL (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxN)
      (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hfix : fixV (autI hV (ch82A V h) ⊔ Subgroup.zpowers (convI hV ⟨x, hXN hxX⟩)) =
      (ch82ZI V h).comap (E3.valHom hV) := by
    rw [fixV_sup_82, ← autI_zpowers_82 hV (hXN hxX), fixV_autI_eq_comap hV hAN,
      fixV_autI_eq_comap hV (Subgroup.zpowers_le.mpr (hXN hxX)), hxV, ← Subgroup.comap_inf]
    congr 1
    exact inf_eq_right.mpr (ch82ZI_le_ch82U_82 hP)
  have hrk : rkIdx (fixV (autI hV (ch82A V h) ⊔ Subgroup.zpowers (convI hV ⟨x, hXN hxX⟩))) =
      2 * (s + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hfix, ← mQuot_eq_rkIdx_comap hV (U := ch82ZI V h) inf_le_left]
    unfold mQuot
    rw [hZs, padicValNat.prime_pow]
  exact h167 s hs (autI hV (ch82A V h)) (Subgroup.zpowers (convI hV ⟨x, hXN hxX⟩))
    (autI_mono hV le_top)
    (Subgroup.zpowers_le.mpr (convI_mem_autI hV (Subgroup.mem_top x) (hXN hxX)))
    (isElemAbelian2_autI hV hAel hAN) hAs (by rw [Nat.card_zpowers, hxo']) hcomm hrk

end L825I

end CFSG.Quasithin.H13
