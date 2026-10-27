module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W4
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem eq_of_odd_mul_two_pow627 {x y i j : ℕ} (hx : Odd x) (hy : Odd y)
    (h : x * 2 ^ i = y * 2 ^ j) : x = y := by
  have hcx : Nat.Coprime x (2 ^ j) :=
    Nat.Coprime.pow_right j ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hx)))))
  have hcy : Nat.Coprime y (2 ^ i) :=
    Nat.Coprime.pow_right i ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hy)))))
  have h1 : x ∣ y * 2 ^ j := ⟨2 ^ i, h.symm⟩
  have h2 : y ∣ x * 2 ^ i := ⟨2 ^ j, h⟩
  exact Nat.dvd_antisymm (hcx.dvd_of_dvd_mul_right h1) (hcy.dvd_of_dvd_mul_right h2)

theorem not_card_mul_two_pow627 {N l k : ℕ} (hN : N = 720 ∨ N = 5040 ∨ N = 40320 ∨ N = 12096)
    (hlk : l * 2 ^ k = N)
    (hl : (∃ a, 1 ≤ a ∧ l = 2 ^ a * (4 ^ a - 1)) ∨
      (∃ a, 1 ≤ a ∧ l = (2 ^ a) ^ 3 * ((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 - 1)) ∨ l = 60) :
    False := by
  obtain ⟨m, v, hm, hNm⟩ : ∃ m v, (m = 45 ∨ m = 315 ∨ m = 189) ∧ N = m * 2 ^ v := by
    rcases hN with rfl | rfl | rfl | rfl
    · exact ⟨45, 4, by norm_num, by norm_num⟩
    · exact ⟨315, 4, by norm_num, by norm_num⟩
    · exact ⟨315, 7, by norm_num, by norm_num⟩
    · exact ⟨189, 6, by norm_num, by norm_num⟩
  have hmodd : Odd m := by rcases hm with rfl | rfl | rfl <;> decide
  rcases hl with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | rfl
  ·
    have h4 : 4 ≤ 4 ^ a := Nat.le_self_pow (by omega) 4
    have hodd : Odd (4 ^ a - 1) := by
      have : Even (4 ^ a) := (Nat.even_pow.mpr ⟨by decide, by omega⟩)
      exact Nat.Even.sub_odd (by omega) this odd_one
    have h1 : (4 ^ a - 1) * 2 ^ (a + k) = m * 2 ^ v := by
      rw [← hNm, ← hlk, pow_add]
      ring
    have h2 := eq_of_odd_mul_two_pow627 hodd hmodd h1
    have h3 : 4 ^ a < 4 ^ 5 := by rcases hm with rfl | rfl | rfl <;> omega
    have h5 : a < 5 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
    interval_cases a <;> rcases hm with rfl | rfl | rfl <;> omega
  ·
    set q := 2 ^ a with hq
    have hq2 : 2 ≤ q := by
      rw [hq]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have hqe : Even q := by
      rw [hq]
      exact Nat.even_pow.mpr ⟨by decide, by omega⟩
    have hodd2 : Odd (q ^ 2 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hqe.pow_of_ne_zero (by norm_num)) odd_one
    have hodd3 : Odd (q ^ 3 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hqe.pow_of_ne_zero (by norm_num)) odd_one
    have h1 : ((q ^ 2 - 1) * (q ^ 3 - 1)) * 2 ^ (3 * a + k) = m * 2 ^ v := by
      rw [← hNm, ← hlk, pow_add, show 2 ^ (3 * a) = q ^ 3 by rw [hq, ← pow_mul, mul_comm]]
      ring
    have h2 := eq_of_odd_mul_two_pow627 (hodd2.mul hodd3) hmodd h1
    have h3 : (q ^ 2 - 1) * (q ^ 3 - 1) ≤ 315 := by rcases hm with rfl | rfl | rfl <;> omega
    rcases Nat.lt_or_ge q 4 with hq4 | hq4
    · have hq2' : q = 2 ∨ q = 3 := by omega
      rcases hq2' with h | h <;> rw [h] at h2 <;> rcases hm with rfl | rfl | rfl <;> omega
    · have h6 : 15 ≤ q ^ 2 - 1 := by
        have : 16 ≤ q ^ 2 := by nlinarith
        omega
      have h7 : 63 ≤ q ^ 3 - 1 := by
        have : 64 ≤ q ^ 3 := by
          calc 64 = 4 ^ 3 := by norm_num
            _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
        omega
      have : 15 * 63 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul h6 h7
      omega
  ·
    have h1 : 15 * 2 ^ (k + 2) = m * 2 ^ v := by
      rw [← hNm, ← hlk, pow_add]
      ring
    have h2 := eq_of_odd_mul_two_pow627 (by decide) hmodd h1
    rcases hm with rfl | rfl | rfl <;> omega

theorem card_eq_mul_two_pow627 {Γ : Type*} [Group Γ] [Finite Γ] {J L T : Subgroup Γ}
    (hLJ : L ≤ J) (hn : J ≤ Subgroup.normalizer (L : Set Γ)) (hJ : J = L ⊔ T)
    (hT : IsPGroup 2 T) : ∃ k, Nat.card J = Nat.card L * 2 ^ k := by
  classical
  set N := L.subgroupOf J with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLJ).mpr hn
  have hTJ : T ≤ J := hJ ▸ le_sup_right
  set f : ↥(T.subgroupOf J) →* ↥J ⧸ N := (QuotientGroup.mk' N).comp (T.subgroupOf J).subtype
    with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hxJ⟩, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hxLT : x ∈ ((L ⊔ T : Subgroup Γ) : Set Γ) := hJ ▸ hxJ
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T (hTJ.trans hn)] at hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hxLT
    refine ⟨⟨⟨t, hTJ ht⟩, ht⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hN, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have := (Subgroup.mem_normalizer_iff.mp (hn (hTJ (T.inv_mem ht))) l).mp hl
    simpa [mul_assoc] using this
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT
  have hdvd : Nat.card (↥J ⧸ N) ∣ 2 ^ m := by
    rw [← hm, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv]
    exact Subgroup.card_dvd_of_surjective hfs
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨k, ?_⟩
  rw [← N.card_mul_index, Subgroup.index, hk, hN,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLJ).toEquiv]

variable {Q : Type} [CommGroup Q]

abbrev fstarJ627 (X : Subgroup (MulAut Q)) : Subgroup (MulAut Q) :=
  quasithinGenFitting (ffJ (cenOdd627 X))

theorem card_of_pair_types627 [Finite Q] {L : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    (h : (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ n, BinaryNaturalSL L U Z 3 n) ∨
      AlternatingNatural L U Z 5) :
    (∃ a, 1 ≤ a ∧ Nat.card L = 2 ^ a * (4 ^ a - 1)) ∨
      (∃ a, 1 ≤ a ∧ Nat.card L = (2 ^ a) ^ 3 * ((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 - 1)) ∨
        Nat.card L = 60 := by
  rcases h with ⟨n, K, _, _, hKn, π, hπ⟩ | ⟨n, K, _, _, hKn, π, hπ⟩ | ⟨π, hπ⟩
  · have e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    refine Or.inl ⟨n, one_le_of_card_eq_two_pow627 hKn, ?_⟩
    rw [← Nat.card_congr e.toEquiv]
    exact R3c.card_statedSL_two_pow hKn
  · have e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    refine Or.inr (Or.inl ⟨n, one_le_of_card_eq_two_pow627 hKn, ?_⟩)
    rw [← Nat.card_congr e.toEquiv, ← hKn]
    exact CFSG.SectionRank.OddCover.card_statedSL_three
  · have e := FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ
    refine Or.inr (Or.inr ?_)
    rw [← Nat.card_congr e.toEquiv]
    show Nat.card ↥(alternatingGroup (Fin 5)) = 60
    have := two_mul_card_alternatingGroup (α := Fin 5)
    rw [Fintype.card_perm, Fintype.card_fin] at this
    rw [Nat.card_eq_fintype_card]
    have h120 : Nat.factorial 5 = 120 := by decide
    omega

theorem ffJ_analysis627 [Finite Q] [Finite (MulAut Q)]
    (hK : KnownFacts15122Types)
    (hE : Vol2.Ch11.SecA.FactA318Excl) {X A : Subgroup (MulAut Q)}
    (hA : IsFFStarOffender (cenOdd627 X) A) (hA4 : Nat.card A = 4)
    (hfix : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A)
    (hcomm : Nat.card (commV A) ≤ 4) (hidx : (fixV A).index ≤ 4)
    (hexcl : ∀ L : Subgroup (MulAut Q), IsSubnormal L X → CFSG.IsQuasisimple ↥L →
      A318Exclusion ↥L → False)
    (hhat : ∀ L : Subgroup (MulAut Q), IsSubnormal L X → CFSG.IsQuasisimple ↥L →
      IsHat ↥L ↥(alternatingGroup (Fin 6)) → False)
    (h1 : B56Case1 (ffJ (cenOdd627 X))) :
    A ≤ fstarJ627 X ∧ IsSubnormal (fstarJ627 X) X ∧ CFSG.IsQuasisimple ↥(fstarJ627 X) ∧
      (BinaryNaturalSL (fstarJ627 X) (commV (fstarJ627 X))
          (fixV (fstarJ627 X) ⊓ commV (fstarJ627 X)) 2 2 ∨
        BinaryNaturalSL (fstarJ627 X) (commV (fstarJ627 X))
          (fixV (fstarJ627 X) ⊓ commV (fstarJ627 X)) 3 1 ∨
        BinaryNaturalSL (fstarJ627 X) (commV (fstarJ627 X))
          (fixV (fstarJ627 X) ⊓ commV (fstarJ627 X)) 3 2) := by
  classical
  set Y := cenOdd627 X with hY
  set J := ffJ Y with hJ
  set L := fstarJ627 X with hL
  have hAJ : A ≤ J := B6.le_ffJ hA
  have hA1 : A ≠ ⊥ := hA.2.1
  have hAab : IsElemAbelian2 A := hA.2.2.1
  have hJY : J ≤ Y := B6.ffJ_le Y
  have hJn : Y ≤ Subgroup.normalizer (J : Set (MulAut Q)) := B6.le_normalizer_ffJ Y
  have hYsn : IsSubnormal Y X := A3.subnormal_of_normal inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr (le_normalizer_cenOdd627 X))
  have hJsn : IsSubnormal J X := A3.subnormal_trans (A3.subnormal_of_normal hJY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mpr hJn)) hYsn
  have hLJ : L ≤ J := quasithinGenFitting_le J
  have hLn : J ≤ Subgroup.normalizer (L : Set (MulAut Q)) := le_normalizer_quasithinGenFitting J
  have hLsn : IsSubnormal L X := A3.subnormal_trans (A3.subnormal_of_normal hLJ
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hLJ).mpr hLn)) hJsn
  obtain ⟨hq, ⟨⟨-, hcases⟩, -⟩, -⟩ := h1
  have hexL := hexcl L hLsn hq
  have hhatL := hhat L hLsn hq
  have hfs : ∀ a ∈ A, Nat.card (commV (Subgroup.zpowers a)) ≤ 4 := fun a ha =>
    (Subgroup.card_le_of_le (commV_mono627 (Subgroup.zpowers_le.mpr ha))).trans hcomm
  have hidx' : (fixV A).index ≤ Nat.card A := hA4 ▸ hidx
  rcases hcases with ⟨-, hpair, hsyl⟩ | hii | ⟨n, -, hn45, π, U₁, U₂, -, hπ, -⟩ |
      ⟨-, n, hn45, k, hk1, -, I, π, -, -, -, hreal⟩
  · obtain ⟨T, hT⟩ := exists_isSylowTwoOf J
    rcases hsyl T hT with hJL | ⟨hJLT, hnat⟩
    ·
      have hAL : A ≤ L := hAJ.trans (le_of_eq hJL)
      exact ⟨hAL, hLsn, hq, pair_cases627 hK hE hq hpair hAL hA4 hfs
        (fun h5 => false_of_altD5_627 h5 hAL hA4 hAab hfix hcomm) hexL hhatL⟩
    ·
      exfalso
      obtain ⟨k, hk⟩ := card_eq_mul_two_pow627 hLJ hLn hJLT hT.2.1
      have hcL := card_of_pair_types627 (pair_types627 hK hE hq hpair hexL hhatL)
      rcases hnat with ⟨n, hn5, hn8, hsym⟩ | ⟨K, _, _, hK2, π, hπ⟩
      · rcases Nat.lt_or_ge 5 n with hn6 | hn5'
        · obtain ⟨π, hπ⟩ := hsym
          have e := FFC.equivOfRealizes (FFC.symDn_faithful (by omega)) hπ
          have hJn : Nat.card J = Nat.factorial n := by
            rw [← Nat.card_congr e.toEquiv]
            show Nat.card (Equiv.Perm (Fin n)) = _
            rw [Nat.card_perm, Nat.card_fin]
          have hN : Nat.factorial n = 720 ∨ Nat.factorial n = 5040 ∨ Nat.factorial n = 40320 ∨
              Nat.factorial n = 12096 := by
            interval_cases n <;> decide
          exact not_card_mul_two_pow627 (hJn ▸ hN) hk.symm hcL
        · obtain rfl : n = 5 := le_antisymm hn5' hn5
          exact false_of_symD5_627 hsym hAJ hA4 hAab hfix hcomm
      · have hK2' : Nat.card K = 2 := by simpa using hK2
        have := R3c.charP_two_of_natCard_eq_two_pow hK2
        have e := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
        have hJ12 : Nat.card J = 12096 := by
          rw [← Nat.card_congr e.toEquiv]
          show Nat.card ↥(CFSG.Open.quasithinG2 K) = 12096
          rw [card_quasithinG2_1527d hK2, hK2']
          norm_num
        exact not_card_mul_two_pow627 (hJ12 ▸ Or.inr (Or.inr (Or.inr rfl))) hk.symm hcL
  · exact (false_of_case1ii627 hii hAJ hA1 hAab hfix hidx' hcomm).elim
  ·
    exfalso
    have e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    rcases hn45 with rfl | rfl
    · exact hexL (hK.l42 _ (R3c2.isPSL_two_of_statedSL (by norm_num) e.symm))
    · exact hexL (hK.l52 _ (R3c2.isPSL_two_of_statedSL (by norm_num) e.symm))
  · exfalso
    have e := FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩)
    rcases hn45 with rfl | rfl
    · exact hexL (hK.l42 _ (R3c2.isPSL_two_of_statedSL (by norm_num) e.symm))
    · exact hexL (hK.l52 _ (R3c2.isPSL_two_of_statedSL (by norm_num) e.symm))

end CFSG.Quasithin.H13
