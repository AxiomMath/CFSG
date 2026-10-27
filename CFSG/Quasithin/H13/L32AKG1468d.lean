module

public import CFSG.Sporadic.Schreier.RuCentersMain
public import Certificates.Certificate7152

public noncomputable section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier

@[expose] def ruU1Basis (k : ℕ) : Equiv.Perm (Fin 4060) :=
  evalSigned [ruC0, ruC1] (ruU1Words.getD k [])

@[expose] def ruU1Elt (i : ℕ) : Equiv.Perm (Fin 4060) :=
  ruZ ^ (i % 2) * (ruU1Basis 0 ^ (i / 2 % 2) * (ruU1Basis 1 ^ (i / 4 % 2) *
    (ruU1Basis 2 ^ (i / 8 % 2) * ruU1Basis 3 ^ (i / 16 % 2))))

theorem ruU1Words_letters : ∀ k < 4, lettersOK 2 (ruU1Words.getD k []) = true := by decide

theorem rep_ruCW {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (ruCW w) (evalSigned [ruC0, ruC1] w) := by
  have hinv : ∀ h < 2, Rep 4060 #[ruInv ruC0A, ruInv ruC1A][h]! ([ruC0, ruC1].getD h 1)⁻¹ :=
    rep_pair_getD_inv (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1)
      (rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1)
  exact rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruC0 rep_ruC1) hinv w hw

theorem rep_ruU1Basis {k : ℕ} (hk : k < 4) :
    Rep 4060 (ruU1BasisA k) (ruU1Basis k) :=
  rep_ruCW (ruU1Words_letters k hk)

theorem rep_ruU1Prod (i : ℕ) :
    Rep 4060 (ruU1Prod i) (ruU1Elt i) :=
  rep_compA (rep_powA rep_ruZ _) (rep_compA (rep_powA (rep_ruU1Basis (by norm_num)) _)
    (rep_compA (rep_powA (rep_ruU1Basis (by norm_num)) _)
      (rep_compA (rep_powA (rep_ruU1Basis (by norm_num)) _)
        (rep_powA (rep_ruU1Basis (by norm_num)) _))))

theorem ruU1Arr_get {i : ℕ} (hi : i < 32) : ruU1Arr[i]! = ruU1Prod i := by
  rw [getElem!_pos ruU1Arr i (by simpa [ruU1Arr] using hi)]
  simp [ruU1Arr]

theorem rep_ruU1Arr {i : ℕ} (hi : i < 32) :
    Rep 4060 ruU1Arr[i]! (ruU1Elt i) := by
  rw [ruU1Arr_get hi]
  exact rep_ruU1Prod i

theorem ruU1Basis_memC (k : ℕ) : ruU1Basis k ∈ ruC :=
  evalSigned_mem (pair_mem ruC0_memC ruC1_memC) _

theorem ruU1Elt_memC (i : ℕ) : ruU1Elt i ∈ ruC :=
  mul_mem (pow_mem ruZ_memC _) (mul_mem (pow_mem (ruU1Basis_memC 0) _)
    (mul_mem (pow_mem (ruU1Basis_memC 1) _)
      (mul_mem (pow_mem (ruU1Basis_memC 2) _) (pow_mem (ruU1Basis_memC 3) _))))

theorem rep_ruU1FArr {i : ℕ}
    (hi : i < 32) : Rep 1920 ruU1FArr[i]! (ruResFPerm (ruU1Elt i)) := by
  have h : ruU1FArr[i]! = resA ruF ruFPos ruU1Arr[i]! := by
    rw [getElem!_pos ruU1FArr i (by simpa [ruU1FArr] using hi)]
    simp [ruU1FArr]
  rw [h]
  exact rep_ruResF (rep_ruU1Arr hi) (ruU1Elt_memC i)

theorem ruU1Elt_zero : ruU1Elt 0 = 1 := by simp [ruU1Elt]

theorem ruU1Elt_one : ruU1Elt 1 = ruZ := by simp [ruU1Elt]

theorem xor_lt_32 {i j : ℕ} (hi : i < 32) (hj : j < 32) : i ^^^ j < 32 :=
  Nat.xor_lt_two_pow (n := 5) hi hj

theorem eq_of_xor_eq_zero {i j : ℕ} (h : i ^^^ j = 0) : i = j := by
  calc i = i ^^^ (i ^^^ j) := by rw [h, Nat.xor_zero]
    _ = j := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem ruU1Elt_mul {i j : ℕ}
    (hi : i < 32) (hj : j < 32) : ruU1Elt i * ruU1Elt j = ruU1Elt (i ^^^ j) :=
  eq_of_eqA (rep_compA (rep_ruU1Arr hi) (rep_ruU1Arr hj)) (rep_ruU1Arr (xor_lt_32 hi hj))
    (Certificates.certificate7152.2.1 i hi j hj)

theorem ruU1Elt_ne_one {i : ℕ}
    (hi : i < 32) (h0 : 0 < i) : ruU1Elt i ≠ 1 := fun h => by
  have := Certificates.certificate7152.2.2.1 i hi h0
  rw [(eqA_iff (rep_ruU1Arr hi) rep_idA).2 h] at this
  exact Bool.noConfusion this

theorem ruU1Elt_inj {i j : ℕ}
    (hi : i < 32) (hj : j < 32) (h : ruU1Elt i = ruU1Elt j) : i = j := by
  by_contra hne
  have h0 : 0 < i ^^^ j := Nat.pos_of_ne_zero fun h' => hne (eq_of_xor_eq_zero h')
  apply ruU1Elt_ne_one (xor_lt_32 hi hj) h0
  rw [← ruU1Elt_mul hi hj, h, ruU1Elt_mul hj hj, Nat.xor_self, ruU1Elt_zero]

theorem ruU1Sig_lt : ∀ k < 4, ∀ i < 32, (ruU1Sig.getD k []).getD i 0 < 32 := by decide

theorem ruU1Tau_lt : ∀ m < 7, ruU1Tau.getD m 0 < 32 := by decide

theorem ruSGens_getD_mem' (k : ℕ) : ruSGens.getD k 1 ∈ ruS := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ruSGens[k]? with
  | none => exact ruS.one_mem
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem ruSGens_conj_ruU1Elt
    {k i : ℕ} (hk : k < 4) (hi : i < 32) :
    ruSGens.getD k 1 * ruU1Elt i * (ruSGens.getD k 1)⁻¹ =
      ruU1Elt ((ruU1Sig.getD k []).getD i 0) :=
  eq_of_eqA (rep_compA (rep_compA (rep_ruSGens k hk) (rep_ruU1Arr hi))
      (rep_ruInv (rep_ruSGens k hk) (ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk)))
    (rep_ruU1Arr (ruU1Sig_lt k hk i hi)) (Certificates.certificate7152.2.2.2.1 k hk i hi)

theorem ruEElt_eq_ruU1Elt
    {m : ℕ} (hm : m < 7) :
    ruEElt m = ruU1Elt (ruU1Tau.getD m 0) :=
  eq_of_eqA (rep_ruEElt hm) (rep_ruU1Arr (ruU1Tau_lt m hm))
    (Certificates.certificate7152.2.2.2.2.1 m hm)

theorem ruNs_conj_ruEElt
    {k m : ℕ} (hk : k < 2) (hm : m < 7) :
    [ruNs0, ruNs1].getD k 1 * ruEElt m * ([ruNs0, ruNs1].getD k 1)⁻¹ =
      ruEElt ((ruEPi.getD k []).getD m 0) := by
  have hπ : (ruEPi.getD k []).getD m 0 < 7 := by
    interval_cases k <;> interval_cases m <;> decide
  exact eq_of_eqA (rep_ruConjA hk (rep_ruEElt hm)) (rep_ruEElt hπ)
    (Certificates.certificate7152.2.2.2.2.2.2.1 k hk m hm)

theorem ruCommS_eq :
    ruSGens.getD 0 1 * ruEElt 2 * (ruSGens.getD 0 1)⁻¹ * (ruEElt 2)⁻¹ = ruZ := by
  have hs := rep_ruSGens 0 (by norm_num)
  have hsi := rep_ruInv hs (ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.2.1 0 (by norm_num))
  have he := rep_ruEElt (i := 2) (by norm_num)
  have hei := rep_ruInv he (ruE_check.2.2.2.2.1 2 (by norm_num))
  exact eq_of_eqA (rep_compA (rep_compA (rep_compA hs he) hsi) hei) rep_ruZ
    (Certificates.certificate7152.2.2.2.2.2.2.2.1)

theorem ruOdd_letters : ∀ k < 6, lettersOK 2 (ruOddA k) = true ∧ lettersOK 2 (ruOddB k) = true := by
  decide

theorem odd_orderOf_of_pow {x : Equiv.Perm (Fin 4060)} {m : ℕ} (hm : m % 2 = 1)
    (hx : x ^ m = 1) : Odd (orderOf x) :=
  (Nat.odd_iff.mpr hm).of_dvd_nat (orderOf_dvd_of_pow_eq_one hx)

theorem ruOdd_pow {k : ℕ}
    (hk : k < 6) :
    ruOddM k % 2 = 1 ∧ ruOddMA k % 2 = 1 ∧ ruOddMB k % 2 = 1 ∧
    (ruJGens.getD k 1 * evalSigned [ruC0, ruC1] (ruOddA k) *
        evalSigned [ruC0, ruC1] (ruOddB k)) ^ ruOddM k = 1 ∧
      evalSigned [ruC0, ruC1] (ruOddA k) ^ ruOddMA k = 1 ∧
      evalSigned [ruC0, ruC1] (ruOddB k) ^ ruOddMB k = 1 := by
  have h9 := Certificates.certificate7152.2.2.2.2.2.2.2.2 k hk
  have hrA := rep_ruCW (ruOdd_letters k hk).1
  have hrB := rep_ruCW (ruOdd_letters k hk).2
  have hrx := rep_compA (rep_compA (rep_ruJGens k hk) hrA) hrB
  have hx := h9.2.2.2.1
  have ha := h9.2.2.2.2.1
  have hb := h9.2.2.2.2.2
  have hpx := rep_powA hrx (ruOddM k)
  have hpa := rep_powA hrA (ruOddMA k)
  have hpb := rep_powA hrB (ruOddMB k)
  have e1 := eq_of_eqA hpx rep_idA hx
  have e2 := eq_of_eqA hpa rep_idA ha
  have e3 := eq_of_eqA hpb rep_idA hb
  exact ⟨h9.1, h9.2.1, h9.2.2.1, e1, e2, e3⟩

theorem mem_zpowers_ruZ
    {w : Equiv.Perm (Fin 4060)} (hw : w ∈ Subgroup.zpowers ruZ) : w = 1 ∨ w = ruZ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hz2 : ruZ ^ 2 = 1 := by rw [← orderOf_ruZ]; exact pow_orderOf_eq_one ruZ
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show (m + m : ℤ) = 2 * m by ring, zpow_mul, zpow_two, ← pow_two, hz2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ← pow_two, hz2, one_zpow, one_mul]

theorem u1_eq_of_comm
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruS)
    (hc : ∀ j ∈ ruJ, x * j * x⁻¹ * j⁻¹ ∈ Subgroup.zpowers ruZ) : ∃ i < 32, x = ruU1Elt i := by
  have hxC : x ∈ ruC := ruS_leC hx
  have hmem : ruResFPerm x ∈ ruChainS.originalSubgroup := by
    rw [ruChainS_sub]
    exact ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 hx, (ruResFPerm_of_mem hxC).symm⟩
  have hcomm : ∀ j < 6, ruResFPerm x * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm (ruJGens.getD j 1) * ruResFPerm x ∨ ruResFPerm x * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm ruZ * (ruResFPerm (ruJGens.getD j 1) * ruResFPerm x) := by
    intro j _
    have hjJ := ruJGens_getD_mem j
    have hjC := ruJ_leC hjJ
    rw [← ruResFPerm_mul hxC hjC, ← ruResFPerm_mul hjC hxC,
      ← ruResFPerm_mul ruZ_memC (mul_mem hjC hxC)]
    rcases mem_zpowers_ruZ (hc _ hjJ) with h | h
    · left
      congr 1
      calc x * ruJGens.getD j 1 = x * ruJGens.getD j 1 * x⁻¹ * (ruJGens.getD j 1)⁻¹ *
            (ruJGens.getD j 1 * x) := by group
        _ = ruJGens.getD j 1 * x := by rw [h, one_mul]
    · right
      congr 1
      calc x * ruJGens.getD j 1 = x * ruJGens.getD j 1 * x⁻¹ * (ruJGens.getD j 1)⁻¹ *
            (ruJGens.getD j 1 * x) := by group
        _ = ruZ * (ruJGens.getD j 1 * x) := by rw [h]
  have h := ruChainS_check.1
  have hb : ruChainS.baseCount = 2 := rfl
  have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
    (le_of_eq hb.symm) (fun i hi hi' => by
      have : i < 2 := lt_of_lt_of_eq hi' hb
      omega)
    (P := fun g => (∀ j < 6, g * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm (ruJGens.getD j 1) * g ∨ g * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm ruZ * (ruResFPerm (ruJGens.getD j 1) * g)) →
      ∃ i < 32, g = ruResFPerm (ruU1Elt i))
    (fun t g ht hp hc => by
      have hzF : Rep 1920 ruZF (ruResFPerm ruZ) := rep_ruResF rep_ruZ ruZ_memC
      have hcs : (allLt 6 fun j => ruCommZ1920 t (ruJF j)) = true := by
        rw [allLt_iff]
        intro j hj
        simp only [ruCommZ1920, Bool.or_eq_true]
        rcases hc j hj with h1 | h1
        · exact Or.inl ((eqA_iff (rep_compA ht (rep_ruJF hj)) (rep_compA (rep_ruJF hj) ht)).2 h1)
        · exact Or.inr ((eqA_iff (rep_compA ht (rep_ruJF hj))
            (rep_compA hzF (rep_compA (rep_ruJF hj) ht))).2 h1)
      simp only [hcs, Bool.not_true, Bool.false_or] at hp
      obtain ⟨i, hi, hie⟩ := nat_any_iff'.1 hp
      exact ⟨i, hi, (eqA_iff ht (rep_ruU1FArr hi)).1 hie⟩)
    Certificates.certificate7152.1 (ruResFPerm x) hmem hcomm
  obtain ⟨i, hi, he⟩ := key
  refine ⟨i, hi, ?_⟩
  rw [ruResFPerm_of_mem hxC, ruResFPerm_of_mem (ruU1Elt_memC i)] at he
  exact congrArg Subtype.val (ruResF_injective he)

theorem ruU1Span_lt {a b : ℕ} (ha : a < 32) (hb : b < 32) : ∀ w ∈ ruU1Span a b, w < 32 := by
  intro w hw
  simp only [ruU1Span, List.mem_cons, List.not_mem_nil, or_false] at hw
  have h1 : (1 : ℕ) < 32 := by norm_num
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact ha
  · exact xor_lt_32 ha h1
  · exact hb
  · exact xor_lt_32 hb h1
  · exact xor_lt_32 ha hb
  · exact xor_lt_32 (xor_lt_32 ha hb) h1

theorem ruZ_mem_ruESub :
    ruZ ∈ ruESub :=
  mem_ruESub.2 (Or.inr ⟨0, by norm_num, ruEElt_zero⟩)

theorem eq_ruESub_of_le
    {E₀ : Subgroup (Equiv.Perm (Fin 4060))} (hJ : E₀ ≤ ruS)
    (hc : ∀ x ∈ E₀, ∀ j ∈ ruJ, x * j * x⁻¹ * j⁻¹ ∈ Subgroup.zpowers ruZ)
    (hcard : Nat.card E₀ = 8) (hz : ruZ ∈ E₀)
    (hS : ruS ≤ Subgroup.normalizer (E₀ : Set (Equiv.Perm (Fin 4060)))) : E₀ = ruESub := by
  classical
  have hU : ∀ x ∈ E₀, ∃ i < 32, x = ruU1Elt i := fun x hx => u1_eq_of_comm (hJ hx) (hc x hx)
  have hle : E₀ ≤ ruESub := by
    intro g hg
    obtain ⟨c, hc32, rfl⟩ := hU g hg
    by_cases hc2 : c < 2
    · interval_cases c
      · rw [ruU1Elt_zero]
        exact ruESub.one_mem
      · rw [ruU1Elt_one]
        exact ruZ_mem_ruESub
    push Not at hc2
    obtain ⟨y, hy, hyn⟩ : ∃ y ∈ E₀, y ∉ ({1, ruZ, ruU1Elt c, ruU1Elt c * ruZ} :
        Finset (Equiv.Perm (Fin 4060))) := by
      by_contra hne
      push Not at hne
      have hsub : (E₀ : Set (Equiv.Perm (Fin 4060))) ⊆
          (({1, ruZ, ruU1Elt c, ruU1Elt c * ruZ} : Finset (Equiv.Perm (Fin 4060))) :
            Set (Equiv.Perm (Fin 4060))) := fun x hx => hne x hx
      have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at h1
      have h2 : ({1, ruZ, ruU1Elt c, ruU1Elt c * ruZ} : Finset (Equiv.Perm (Fin 4060))).card ≤ 4 :=
        (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
      omega
    obtain ⟨b, hb32, rfl⟩ := hU y hy
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyn
    obtain ⟨hb1, hbz, hbc, hbcz⟩ := hyn
    have h1 : (1 : ℕ) < 32 := by norm_num
    have hb2 : 2 ≤ b := by
      by_contra hb
      push Not at hb
      interval_cases b
      · exact hb1 ruU1Elt_zero
      · exact hbz ruU1Elt_one
    have hbc' : b ≠ c := fun h => hbc (by rw [h])
    have hbc1 : b ≠ c ^^^ 1 := fun h => hbcz (by rw [h, ← ruU1Elt_mul hc32 h1, ruU1Elt_one])
    have hpair := Certificates.certificate7152.2.2.2.2.2.1 c hc32 b hb32
    have hpre : (decide (2 ≤ c) && decide (2 ≤ b) && decide (b ≠ c) &&
        decide (b ≠ c ^^^ 1)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hc2, hb2⟩, hbc'⟩, hbc1⟩
    rw [ruU1PairOK, hpre, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hpair
    obtain ⟨hnd', himp'⟩ := hpair
    have hnd : (ruU1Span c b).Nodup := of_decide_eq_true hnd'
    have himp : (∀ k < 4, ∀ w ∈ ruU1Span c b, (ruU1Sig.getD k []).getD w 0 ∈ ruU1Span c b) →
        ∀ w ∈ ruU1Span c b, w = 0 ∨ w ∈ ruU1Tau := by
      intro hσ w hw
      have hall : (allLt 4 fun k => (ruU1Span c b).all fun w =>
          decide ((ruU1Sig.getD k []).getD w 0 ∈ ruU1Span c b)) = true := by
        rw [allLt_iff]
        intro k hk
        rw [List.all_eq_true]
        intro w hw
        exact decide_eq_true (hσ k hk w hw)
      rw [hall, Bool.not_true, Bool.false_or, List.all_eq_true] at himp'
      exact of_decide_eq_true (himp' w hw)
    have hWlt := ruU1Span_lt hc32 hb32
    have hcE : ruU1Elt c ∈ E₀ := hg
    have hbE : ruU1Elt b ∈ E₀ := hy
    have hz' : ruU1Elt 1 ∈ E₀ := by rw [ruU1Elt_one]; exact hz
    have hxor : ∀ i j, i < 32 → j < 32 → ruU1Elt i ∈ E₀ → ruU1Elt j ∈ E₀ →
        ruU1Elt (i ^^^ j) ∈ E₀ := fun i j hi hj hiE hjE => by
      rw [← ruU1Elt_mul hi hj]
      exact mul_mem hiE hjE
    have hWmem : ∀ w ∈ ruU1Span c b, ruU1Elt w ∈ E₀ := by
      intro w hw
      simp only [ruU1Span, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ruU1Elt_zero]; exact E₀.one_mem
      · exact hz'
      · exact hcE
      · exact hxor _ _ hc32 h1 hcE hz'
      · exact hbE
      · exact hxor _ _ hb32 h1 hbE hz'
      · exact hxor _ _ hc32 hb32 hcE hbE
      · exact hxor _ _ (xor_lt_32 hc32 hb32) h1 (hxor _ _ hc32 hb32 hcE hbE) hz'
    set F : Finset (Equiv.Perm (Fin 4060)) := (ruU1Span c b).toFinset.image ruU1Elt with hF
    have hFcard : F.card = 8 := by
      rw [hF, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
      · rfl
      · intro i hi j hj hij
        exact ruU1Elt_inj (hWlt i (List.mem_toFinset.mp hi)) (hWlt j (List.mem_toFinset.mp hj)) hij
    have hFsub : (F : Set (Equiv.Perm (Fin 4060))) ⊆ E₀ := by
      intro g hg'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hg'
      exact hWmem w (List.mem_toFinset.mp hw)
    have hFeq : (F : Set (Equiv.Perm (Fin 4060))) = E₀ := by
      refine Set.eq_of_subset_of_ncard_le hFsub ?_ (Set.toFinite _)
      rw [Set.ncard_coe_finset, hFcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard]
    have hEq : ∀ g ∈ E₀, ∃ w ∈ ruU1Span c b, g = ruU1Elt w := by
      intro g hg'
      have : g ∈ (F : Set (Equiv.Perm (Fin 4060))) := hFeq ▸ hg'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp this
      exact ⟨w, List.mem_toFinset.mp hw, rfl⟩
    have hσ : ∀ k < 4, ∀ w ∈ ruU1Span c b, (ruU1Sig.getD k []).getD w 0 ∈ ruU1Span c b := by
      intro k hk w hw
      have h2 := (Subgroup.mem_normalizer_iff.mp (hS (ruSGens_getD_mem' k)) _).mp (hWmem w hw)
      rw [ruSGens_conj_ruU1Elt hk (hWlt w hw)] at h2
      obtain ⟨w', hw', he⟩ := hEq _ h2
      rwa [ruU1Elt_inj (ruU1Sig_lt k hk w (hWlt w hw)) (hWlt w' hw') he]
    rcases himp hσ c (by simp [ruU1Span]) with h0 | hτ
    · omega
    · obtain ⟨m, hm, hmc⟩ : ∃ m < 7, ruU1Tau.getD m 0 = c := by
        obtain ⟨m, hm, he⟩ := List.getElem_of_mem hτ
        refine ⟨m, by simpa [ruU1Tau] using hm, ?_⟩
        rw [List.getD_eq_getElem _ _ hm, he]
      rw [← hmc, ← ruEElt_eq_ruU1Elt hm]
      exact mem_ruESub.2 (Or.inr ⟨m, hm, rfl⟩)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_ruESub, hcard])

end CFSG.Quasithin.H13.KGRu
