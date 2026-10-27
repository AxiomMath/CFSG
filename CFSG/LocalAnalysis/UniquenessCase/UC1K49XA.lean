module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Struct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open CFSG.ABGLocalTools CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cj_mul (g h a : G) : cj g (cj h a) = cj (h * g) a := by
  simp only [cj]
  group

theorem cj_pow_three (x a : G) (hx : x ^ 3 = 1) : cj x (cj x (cj x a)) = a := by
  rw [cj_mul, cj_mul, show x * (x * x) = x ^ 3 by rw [pow_three], hx]
  simp [cj]

theorem conjugate_cj (L : Subgroup G) (a y : G) (ha : a ∈ L) :
    cj y a ∈ CFSG.conjugate L y := by
  rw [CFSG.conjugate]
  exact ⟨a, ha, by simp [cj, MulAut.conj_apply]⟩

theorem orderOf_eq_three_of_zpowers {X : Subgroup G} {x : G}
    (hx : X = Subgroup.zpowers x) (hcard : Nat.card X = 3) : orderOf x = 3 := by
  have h : Nat.card (Subgroup.zpowers x) = 3 := by rw [← hx]; exact hcard
  simpa only [Nat.card_zpowers] using h

theorem x_mem_normalizer_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : x ∈ X) : x ∈ Subgroup.normalizer (I : Set G) :=
  le_normalizer_I h (h.X_le hx)

theorem conjugate_mem_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x t : G} (hx : x ∈ X) (ht : t ∈ I) : cj x t ∈ I := by
  have hxN : x ∈ Subgroup.normalizer (I : Set G) := x_mem_normalizer_I h hx
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (I : Set G) := (Subgroup.normalizer _).inv_mem hxN
  simpa only [cj, inv_inv] using (Subgroup.mem_normalizer_iff.mp hxN' t).mp ht

theorem eq_sup_Lc {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    I = L ⊔ Lc L x 1 ⊔ Lc L x 2 := by
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  refine le_antisymm ?_ ?_
  · rw [h.I_eq]
    refine iSup_le fun y => iSup_le fun hy => ?_
    have hy' : y ∈ Subgroup.zpowers x := hgen ▸ hy
    rcases mem_zpowers_of_orderOf_eq_three hord hy' with h1 | h2 | h3
    · rw [h1, conjugate_one]
      exact (le_sup_left : L ≤ L ⊔ Lc L x 1).trans le_sup_left
    · rw [h2]
      simpa only [Lc, pow_one] using
        (le_sup_right : Lc L x 1 ≤ L ⊔ Lc L x 1).trans le_sup_left
    · rw [h3]
      exact le_sup_right
  · refine sup_le (sup_le (le_I h) ?_) ?_
    · rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
      exact le_iSup (fun z : X => CFSG.conjugate L (z : G)) ⟨x ^ 1, X.pow_mem hxX 1⟩
    · rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
      exact le_iSup (fun z : X => CFSG.conjugate L (z : G)) ⟨x ^ 2, hx2X⟩


theorem map_conj_subtype_eq_of_mem {K : Subgroup G} {P : Subgroup K} {x : G} (hxK : x ∈ K)
    (hxP : (⟨x, hxK⟩ : K) ∈ P) :
    (P.map K.subtype).map (MulAut.conj x⁻¹).toMonoidHom = P.map K.subtype := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨q, hq, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
    refine ⟨(⟨x, hxK⟩ : K)⁻¹ * p * ⟨x, hxK⟩,
      P.mul_mem (P.mul_mem (P.inv_mem hxP) hp) hxP, ?_⟩
    simp [MulAut.conj_apply]
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨x * (p : G) * x⁻¹,
      Subgroup.mem_map.mpr ⟨(⟨x, hxK⟩ : K) * p * ⟨x, hxK⟩⁻¹,
        P.mul_mem (P.mul_mem hxP hp) (P.inv_mem hxP), by simp⟩, ?_⟩
    simp [MulAut.conj_apply]
    group

theorem exists_sylow_three_normalized {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) :
    ∃ T : Subgroup G, IsSylowOf 3 T I ∧ x ∈ Subgroup.normalizer (T : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := X ⊔ I
  have hXK : X ≤ K := le_sup_left
  have hIK : I ≤ K := le_sup_right
  have hKnormI : K ≤ Subgroup.normalizer (I : Set G) :=
    sup_le (fun y hy => x_mem_normalizer_I h hy) Subgroup.le_normalizer
  have hXcard : Nat.card (X.subgroupOf K) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv, h.card_X]
  have hX3 : IsPGroup 3 (X.subgroupOf K) := IsPGroup.of_card (n := 1) (by simpa using hXcard)
  obtain ⟨P, hXleP⟩ := hX3.exists_le_sylow
  have hPtop : IsSylowOf 3 (P : Subgroup K) ⊤ := by
    refine isSylowOf_iff.mpr ⟨le_top, P.isPGroup', ?_⟩
    simpa only [Subgroup.relIndex_top_right] using P.not_dvd_index
  have hPmap : IsSylowOf 3 ((P : Subgroup K).map K.subtype) K := by
    have := (isSylowOf_map_subtype_iff (p := 3) K (A := (P : Subgroup K)) (B := ⊤)).mpr hPtop
    simpa only [Subgroup.map_top, Subgroup.range_subtype] using this
  let T : Subgroup G := (P : Subgroup K).map K.subtype ⊓ I
  have hTP : T ≤ (P : Subgroup K).map K.subtype := inf_le_left
  have hT3 : IsPGroup 3 T := hPmap.isPGroup.to_le hTP
  have hTI : T ≤ I := inf_le_right
  have hTsyl : IsSylowOf 3 T I := hPmap.inf_of_le_normalizer hIK hKnormI
  have hxK : x ∈ K := hXK hxX
  have hxP : (⟨x, hxK⟩ : K) ∈ P :=
    hXleP (Subgroup.mem_subgroupOf.mpr hxX)
  have hPinv : (P.map K.subtype).map (MulAut.conj x⁻¹).toMonoidHom = P.map K.subtype :=
    map_conj_subtype_eq_of_mem hxK hxP
  have hIinv : I.map (MulAut.conj x⁻¹).toMonoidHom = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (x_mem_normalizer_I h (X.inv_mem hxX))
  have hTinv : T.map (MulAut.conj x⁻¹).toMonoidHom = T := by
    change (((P : Subgroup K).map K.subtype ⊓ I).map (MulAut.conj x⁻¹).toMonoidHom =
      (P : Subgroup K).map K.subtype ⊓ I)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective, hPinv, hIinv]
  refine ⟨T, hTsyl, ?_⟩
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hTinv
  simpa using (Subgroup.normalizer (T : Set G)).inv_mem hxinv


theorem card_bar2_L {L : Subgroup G} (halt : IsAlt (Bar2 L) 5) :
    Nat.card (Bar2 L) = 60 := by
  obtain ⟨e⟩ := halt
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

theorem factorization_three_card_L {L : Subgroup G} (halt : IsAlt (Bar2 L) 5) :
    (Nat.card L).factorization 3 = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have hcard : Nat.card L = 60 * 2 ^ k := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 (↥L))
    rw [hk] at h
    have hbar : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := card_bar2_L halt
    rw [hbar] at h
    exact h
  have h2k : (2 ^ k).factorization 3 = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have h60 : (60 : ℕ).factorization 3 = 1 := by
    rw [show (60 : ℕ) = 3 * 20 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 20)]
  rw [hcard, Nat.factorization_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    Finsupp.add_apply, h60, h2k]

theorem card_inf_sylow_L {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T I) :
    Nat.card ↥(T ⊓ L) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTL : CFSG.ABGLocalTools.IsSylowOf 3 (T ⊓ L) L :=
    hT.inf_of_le_normalizer (le_I h) (I_le_normalizer_L h)
  have hcard := hTL.card_eq (p := 3)
  rw [factorization_three_card_L h.L_alt] at hcard
  simpa using hcard


theorem H_le_normalizer_Q {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    H ≤ Subgroup.normalizer (Q : Set G) := by
  rw [h.Q_eq]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H

theorem isPGroup_Q {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    IsPGroup 2 ↥Q := by
  rw [h.Q_eq]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H

theorem Lc_le_H {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G} {i : ℕ}
    (hxi : x ^ i ∈ X) : Lc L x i ≤ H :=
  CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hxi))

theorem commutator_sup_Lc_le {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    {i j k : ℕ} (hi : x ^ i ∈ X) (hj : x ^ j ∈ X) (hk : x ^ k ∈ X)
    (hij : Lc L x i ≠ Lc L x j) (hik : Lc L x i ≠ Lc L x k)
    (hjk : Lc L x j ≠ Lc L x k) :
    ⁅Lc L x i ⊔ Lc L x j, Lc L x k⁆ ≤ Q := by
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := H_le_normalizer_Q h
  have hLiH : Lc L x i ≤ H := Lc_le_H h hi
  have hLjH : Lc L x j ≤ H := Lc_le_H h hj
  have hLiNLj : Lc L x i ≤ Subgroup.normalizer (Lc L x j : Set G) :=
    conjugate_normalize_of_ne h hi hj hij
  refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hLiNLj).mp hu
  have hbv : ⁅b, v⁆ ∈ Q :=
    (Subgroup.commutator_le.mp (commutator_conjugate_le h hj hk hjk)) b hb v hv
  have hav : ⁅a, v⁆ ∈ Q :=
    (Subgroup.commutator_le.mp (commutator_conjugate_le h hi hk hik)) a ha v hv
  have hconj : a * ⁅b, v⁆ * a⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn (hLiH ha)) ⁅b, v⁆).mp hbv
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact Q.mul_mem hconj hav

theorem inf_T_Q_eq_bot {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {T : Subgroup G} (hT3 : IsPGroup 3 T) : T ⊓ Q = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) T Q hT3 (isPGroup_Q h))


theorem conjugates_distinct {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    Lc L x 0 ≠ Lc L x 1 ∧ Lc L x 0 ≠ Lc L x 2 ∧ Lc L x 1 ≠ Lc L x 2 := by
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hxN : x ∉ Subgroup.normalizer (L : Set G) := by
    intro hx
    exact h.X_nle (hgen ▸ Subgroup.zpowers_le.mpr hx)
  have hx2N : x ^ 2 ∉ Subgroup.normalizer (L : Set G) := by
    intro hx2
    apply hxN
    have h4 : (x ^ 2) ^ 2 ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).pow_mem hx2 2
    rwa [show (x ^ 2) ^ 2 = x by
      rw [← pow_mul, show (2:ℕ) * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]] at h4
  have hL0 : Lc L x 0 = L := by
    rw [Lc, pow_zero, conjugate_one]
  have hne01 : Lc L x 0 ≠ Lc L x 1 := by
    rw [hL0]
    intro hc
    apply hxN
    have hx' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [CFSG.conjugate, Lc] using hc.symm)
    simpa using (Subgroup.normalizer (L : Set G)).inv_mem hx'
  have hne02 : Lc L x 0 ≠ Lc L x 2 := by
    rw [hL0]
    intro hc
    apply hx2N
    have hx' : (x ^ 2)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [CFSG.conjugate, Lc] using hc.symm)
    have hx2 : x ^ 2 ∈ Subgroup.normalizer (L : Set G) := by
      simpa using (Subgroup.normalizer (L : Set G)).inv_mem hx'
    exact hx2
  have hne12 : Lc L x 1 ≠ Lc L x 2 := by
    intro hc
    have h1 : CFSG.conjugate (Lc L x 1) x = CFSG.conjugate (Lc L x 2) x := by rw [hc]
    rw [conjugate_conjugate, conjugate_conjugate] at h1
    have hx2eq : x * x = x ^ 2 := by rw [pow_two]
    have hx3eq : x ^ 2 * x = 1 := by
      rw [show x ^ 2 * x = x ^ 3 by rw [pow_two, pow_three]; group, hx3]
    have hx1eq : x ^ 1 * x = x ^ 2 := by rw [pow_one]; exact hx2eq
    rw [hx1eq, hx3eq, conjugate_one] at h1
    exact hne02 (hL0.trans h1.symm)
  exact ⟨hne01, hne02, hne12⟩


theorem false_of_mul_pow_eq_one {H S K T Q : Subgroup G} {y c : G} {k : ℕ}
    (hyS : y ∈ S) (hcK : c ∈ K) (hc3 : orderOf c = 3)
    (hbound : ⁅S, K⁆ ≤ Q) (halt : IsAlt (Bar2 K) 5)
    (hKQ : K ⊓ Q = CFSG.Open.pCoreOf 2 K) (hKH : K ≤ H)
    (hTQ : T ⊓ Q = ⊥) (hcT : c ∈ T)
    (hrel : y * c ^ k = 1) (hk0 : k ≠ 0) (hk3 : k < 3) : False := by
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hck : c ^ k = y⁻¹ := by
    have := congrArg (fun t => y⁻¹ * t) hrel
    simpa [mul_assoc] using this
  have hk_cases : k = 1 ∨ k = 2 := by omega
  have hcS : c ∈ S := by
    rcases hk_cases with hk1 | hk2
    · rw [hk1, pow_one] at hck
      rw [hck]
      exact S.inv_mem hyS
    · rw [hk2] at hck
      have hc4 : c = (c ^ 2) ^ 2 := by
        rw [← pow_mul, show (2:ℕ) * 2 = 3 + 1 by norm_num, pow_add, hc3', one_mul, pow_one]
      rw [hc4, hck]
      exact S.pow_mem (S.inv_mem hyS) 2
  have hcent : ∀ m ∈ K, ⁅c, m⁆ ∈ Q := fun m hm =>
    (Subgroup.commutator_le.mp hbound) c hcS m hm
  have hcQ : c ∈ Q := mem_pCoreOf_of_centralizer_mod halt hKQ hKH hcK hcent
  have hcInf : c ∈ T ⊓ Q := ⟨hcT, hcQ⟩
  rw [hTQ, Subgroup.mem_bot] at hcInf
  have : orderOf c = 1 := by rw [hcInf]; exact orderOf_one
  omega


theorem independence {H X L Q I T : Subgroup G} (h : Setup49 H X L Q I) {x a b c : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    (haL : a ∈ L) (hbL : b ∈ Lc L x 1) (hcL : c ∈ Lc L x 2)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3)
    (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T) (hTQ : T ⊓ Q = ⊥)
    {i j k : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3)
    (hrel : a ^ i * b ^ j * c ^ k = 1) : i = 0 ∧ j = 0 ∧ k = 0 := by
  have hne := conjugates_distinct h hxX hgen hord
  have hx1X : x ^ 1 ∈ X := X.pow_mem hxX 1
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have ha0 : a ∈ Lc L x 0 := by simpa only [Lc, pow_zero, conjugate_one] using haL
  have hbound01 : ⁅Lc L x 0 ⊔ Lc L x 1, Lc L x 2⁆ ≤ Q :=
    commutator_sup_Lc_le h (X.pow_mem hxX 0) hx1X hx2X hne.1 hne.2.1 hne.2.2
  have hbound02 : ⁅Lc L x 0 ⊔ Lc L x 2, Lc L x 1⁆ ≤ Q := by
    have h := commutator_sup_Lc_le h (X.pow_mem hxX 0) hx2X hx1X hne.2.1 hne.1 (Ne.symm hne.2.2)
    simpa only [sup_comm] using h
  by_cases hk0 : k = 0
  · subst k
    by_cases hj0 : j = 0
    · subst j
      by_cases hi0 : i = 0
      · exact ⟨hi0, rfl, rfl⟩
      · exfalso
        have hai : a ^ i = 1 := by simpa using hrel
        have hdvd : 3 ∣ i := by
          rw [← ha3]
          exact orderOf_dvd_iff_pow_eq_one.mpr hai
        have h1 : i = 1 ∨ i = 2 := by omega
        rcases h1 with rfl | rfl <;> norm_num at hdvd
    · exfalso
      have hrel' : a ^ i * b ^ j = 1 := by simpa using hrel
      have hyS : a ^ i ∈ Lc L x 0 := Subgroup.pow_mem (K := Lc L x 0) ha0 i
      have hbound : ⁅Lc L x 0, Lc L x 1⁆ ≤ Q :=
        commutator_conjugate_le h (X.pow_mem hxX 0) hx1X hne.1
      exact false_of_mul_pow_eq_one hyS hbL hb3 hbound
        (isAlt_bar2_conjugate h.L_alt (x ^ 1)) (conjugate_inf_pCoreOf_eq h hx1X)
        (Lc_le_H h hx1X) hTQ hbT hrel' hj0 hj
  · exfalso
    have hyS : a ^ i * b ^ j ∈ Lc L x 0 ⊔ Lc L x 1 :=
      Subgroup.mul_mem_sup (Subgroup.pow_mem (K := Lc L x 0) ha0 i)
        (Subgroup.pow_mem (K := Lc L x 1) hbL j)
    exact false_of_mul_pow_eq_one hyS hcL hc3 hbound01
      (isAlt_bar2_conjugate h.L_alt (x ^ 2)) (conjugate_inf_pCoreOf_eq h hx2X)
      (Lc_le_H h hx2X) hTQ hcT hrel hk0 hk


theorem isElemAbelian_closure_three {S : Set G} (hcube : ∀ x ∈ S, x ^ 3 = 1)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    IsElemAbelian 3 (Subgroup.closure S) := by
  have hcX : ∀ x ∈ S, ∀ z ∈ Subgroup.closure S, x * z = z * x := by
    intro x hx z hz
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm x hx y hy
    exact Subgroup.mem_centralizer_iff.1 (hle hz) x (Set.mem_singleton x)
  have hcc : ∀ z ∈ Subgroup.closure S, ∀ w ∈ Subgroup.closure S, z * w = w * z := by
    intro z hz w hw
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcX y hy z hz).symm
    exact Subgroup.mem_centralizer_iff.1 (hle hw) z (Set.mem_singleton z)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcc a a.2 b b.2)⟩⟩, fun z hz => ?_⟩
  refine Subgroup.closure_induction (p := fun z _ => z ^ 3 = 1) (fun x hx => hcube x hx)
    (by simp) ?_ ?_ hz
  · intro x y hx hy hx3 hy3
    rw [(show Commute x y from hcc x hx y hy).mul_pow, hx3, hy3, one_mul]
  · intro x _ hx
    rw [inv_pow, hx, inv_one]

theorem closure_three_eq_sup (a b c : G) :
    Subgroup.closure ({a, b, c} : Set G) =
      (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro x (hx | hx | hx)
    · rw [hx]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    · rw [hx]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    · rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)


theorem commutes_zpowers {a b : G} (hab : Commute a b) :
    ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (hab.zpow_zpow i j).eq

theorem le_normalizer_of_commutes {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : y * x * y⁻¹ = x := by
      have := h x hx y hy
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [this]
        _ = x := by group
    rw [this]
    exact hx
  · intro hx
    have h2 := h _ hx y⁻¹ (B.inv_mem hy)
    have : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = (y * x * y⁻¹) * y⁻¹ * y := by rw [← h2]
        _ = y * x * y⁻¹ := by group
    rw [this]
    exact hx

theorem card_sup_mul_card_inf_normal {A L : Subgroup G} [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_normalizes {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_normal (A := B.subgroupOf N) (L := A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]


theorem exists_pow_lt_of_mem_zpowers {x y : G} (hy : y ∈ Subgroup.zpowers x) :
    ∃ i : ℕ, i < orderOf x ∧ y = x ^ i := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hi
  exact ⟨i, hi, hix.symm⟩

theorem normal_form_of_mem_closure {a b c m : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3)
    (hm : m ∈ Subgroup.closure ({a, b, c} : Set G)) :
    ∃ i j k : ℕ, i < 3 ∧ j < 3 ∧ k < 3 ∧ m = a ^ i * b ^ j * c ^ k := by
  have hZaNZb : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => (commutes_zpowers hab y hy x hx).symm
  have hZaNZc : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => (commutes_zpowers hac y hy x hx).symm
  have hZbNZc : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => (commutes_zpowers hbc y hy x hx).symm
  have hZabNZc : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := sup_le hZaNZc hZbNZc
  rw [closure_three_eq_sup] at hm
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_of_le_normalizer hZabNZc).mp hm
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sup_of_le_normalizer hZaNZb).mp hy
  obtain ⟨i, hi, hix⟩ := exists_pow_lt_of_mem_zpowers hx₁
  obtain ⟨j, hj, hjx⟩ := exists_pow_lt_of_mem_zpowers hx₂
  obtain ⟨k, hk, hkx⟩ := exists_pow_lt_of_mem_zpowers hz
  rw [hix, hjx, hkx]
  exact ⟨i, j, k, by simpa [ha3] using hi, by simpa [hb3] using hj,
    by simpa [hc3] using hk, rfl⟩


theorem inf_zpowers_pair_eq_bot {a b : G} (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hind : ∀ i j : ℕ, i < 3 → j < 3 → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxa, hxb⟩
  obtain ⟨i, hi, hix⟩ := exists_pow_lt_of_mem_zpowers hxa
  obtain ⟨j, hj, hjx⟩ := exists_pow_lt_of_mem_zpowers hxb
  rw [Subgroup.mem_bot]
  by_cases hi0 : i = 0
  · rw [hi0, pow_zero] at hix
    exact hix
  · exfalso
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero] at hjx
      rw [hjx] at hix
      have hdvd : 3 ∣ i := by
        rw [← ha3]
        exact orderOf_dvd_iff_pow_eq_one.mpr hix.symm
      have h1 : i = 1 ∨ i = 2 := by omega
      rcases h1 with rfl | rfl <;> norm_num at hdvd
    · have hj1 : j = 1 ∨ j = 2 := by omega
      have hrel : a ^ i * b ^ (3 - j) = 1 := by
        have hjinv : b ^ j * b ^ (3 - j) = 1 := by
          rcases hj1 with rfl | rfl
          · rw [show 3 - 1 = 2 by norm_num, ← pow_add, show 1 + 2 = 3 by norm_num,
              ← hb3, pow_orderOf_eq_one]
          · rw [show 3 - 2 = 1 by norm_num, ← pow_add, show 2 + 1 = 3 by norm_num,
              ← hb3, pow_orderOf_eq_one]
        calc a ^ i * b ^ (3 - j) = b ^ j * b ^ (3 - j) := by rw [← hix, hjx]
          _ = 1 := hjinv
      have h3j : 3 - j < 3 := by omega
      have := hind i (3 - j) (by simpa [ha3] using hi) h3j hrel
      exact hi0 this.1

theorem inf_zpowers_sup_eq_bot {a b c : G} (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hc3 : orderOf c = 3) (hab : Commute a b)
    (hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 →
      a ^ i * b ^ j * c ^ k = 1 → i = 0 ∧ j = 0 ∧ k = 0) :
    Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxc, hxab⟩
  obtain ⟨k, hk, hkx⟩ := exists_pow_lt_of_mem_zpowers hxc
  have hZaNZb : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => (commutes_zpowers hab y hy x hx).symm
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_of_le_normalizer hZaNZb).mp hxab
  obtain ⟨i, hi, hix⟩ := exists_pow_lt_of_mem_zpowers hy
  obtain ⟨j, hj, hjx⟩ := exists_pow_lt_of_mem_zpowers hz
  rw [Subgroup.mem_bot]
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero] at hkx
    exact hkx
  · exfalso
    have hk12 : k = 1 ∨ k = 2 := by omega
    have hrel : a ^ i * b ^ j * c ^ (3 - k) = 1 := by
      have hcinv : c ^ k * c ^ (3 - k) = 1 := by
        rcases hk12 with rfl | rfl
        · rw [show 3 - 1 = 2 by norm_num, ← pow_add, show 1 + 2 = 3 by norm_num,
            ← hc3, pow_orderOf_eq_one]
        · rw [show 3 - 2 = 1 by norm_num, ← pow_add, show 2 + 1 = 3 by norm_num,
            ← hc3, pow_orderOf_eq_one]
      calc a ^ i * b ^ j * c ^ (3 - k) = (a ^ i * b ^ j) * c ^ (3 - k) := rfl
        _ = c ^ k * c ^ (3 - k) := by rw [← hkx, hix, hjx]
        _ = 1 := hcinv
    have h3k : 3 - k < 3 := by omega
    have := hind i j (3 - k) (by simpa [ha3] using hi) (by simpa [hb3] using hj) h3k hrel
    omega

theorem card_sup_zpowers_pair {a b : G} (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hab : Commute a b) (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9 := by
  have hZbNZa : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    le_normalizer_of_commutes (commutes_zpowers hab)
  have h := card_sup_mul_card_inf_of_normalizes hZbNZa
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha3, hb3] at h
  simpa using h

theorem card_sup_zpowers_three {a b c : G} (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hc3 : orderOf c = 3) (hac : Commute a c) (hbc : Commute b c)
    (hpair : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9)
    (hinf : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥) :
    Nat.card ↥((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c) = 27 := by
  have hZcNZa : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    le_normalizer_of_commutes (commutes_zpowers hac)
  have hZcNZb : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    le_normalizer_of_commutes (commutes_zpowers hbc)
  have hZcNZab : Subgroup.zpowers c ≤
      Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
    (le_inf hZcNZa hZcNZb).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (Subgroup.zpowers a) (Subgroup.zpowers b))
  have h := card_sup_mul_card_inf_of_normalizes hZcNZab
  rw [inf_comm, hinf, Subgroup.card_bot, mul_one, hpair, Nat.card_zpowers, hc3] at h
  simpa using h


theorem pow_eq_of_lt_of_orderOf_eq_three {x : G} (hx : orderOf x = 3) {i j : ℕ}
    (hi : i < 3) (hj : j < 3) (h : x ^ i = x ^ j) : i = j := by
  have hmod := (pow_eq_pow_iff_modEq).mp h
  rw [hx] at hmod
  exact Nat.ModEq.eq_of_lt_of_lt hmod hi hj

private theorem inverting_a_pow_eq_of_normal_form_eq {a b c : G}
    (hpair : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    {i j k i' j' : ℕ}
    (heq : a ^ i * b ^ j * c ^ k = a ^ i' * b ^ j' * c ^ k) :
    a ^ i = a ^ i' := by
  have hZab : (a ^ i')⁻¹ * a ^ i ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
    have h1 : (a ^ i')⁻¹ * a ^ i = b ^ j' * (b ^ j)⁻¹ := by
      have h2 : a ^ i * b ^ j = a ^ i' * b ^ j' := by
        have := congrArg (fun t => t * (c ^ k)⁻¹) heq
        simpa [mul_assoc] using this
      calc (a ^ i')⁻¹ * a ^ i = (a ^ i')⁻¹ * (a ^ i * b ^ j) * (b ^ j)⁻¹ := by group
        _ = (a ^ i')⁻¹ * (a ^ i' * b ^ j') * (b ^ j)⁻¹ := by rw [h2]
        _ = b ^ j' * (b ^ j)⁻¹ := by group
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem (Subgroup.zpowers a)
        (Subgroup.inv_mem (Subgroup.zpowers a) (Subgroup.pow_mem (Subgroup.zpowers a)
          (Subgroup.mem_zpowers a) i'))
        (Subgroup.pow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) i)
    · rw [h1]
      exact Subgroup.mul_mem (Subgroup.zpowers b)
        (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) j')
        (Subgroup.inv_mem (Subgroup.zpowers b) (Subgroup.pow_mem (Subgroup.zpowers b)
          (Subgroup.mem_zpowers b) j))
  have hbot : (a ^ i')⁻¹ * a ^ i ∈ (⊥ : Subgroup G) := by
    rw [← hpair]; exact hZab
  rw [Subgroup.mem_bot] at hbot
  exact (inv_mul_eq_one.mp hbot).symm

private theorem inverting_c_pow_eq_of_normal_form_eq {a b c : G}
    (hsup : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥)
    {i j k i' j' k' : ℕ}
    (heq : a ^ i * b ^ j * c ^ k = a ^ i' * b ^ j' * c ^ k') :
    c ^ k = c ^ k' := by
  have hZcZab : c ^ k * (c ^ k')⁻¹ ∈
      Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    have h1 : c ^ k * (c ^ k')⁻¹ = (a ^ i * b ^ j)⁻¹ * (a ^ i' * b ^ j') := by
      have h2 : c ^ k = (a ^ i * b ^ j)⁻¹ * (a ^ i' * b ^ j') * c ^ k' := by
        have := congrArg (fun t => (a ^ i * b ^ j)⁻¹ * t) heq
        simpa [mul_assoc] using this
      rw [h2]
      group
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem (Subgroup.zpowers c)
        (Subgroup.pow_mem (Subgroup.zpowers c) (Subgroup.mem_zpowers c) k)
        (Subgroup.inv_mem (Subgroup.zpowers c) (Subgroup.pow_mem (Subgroup.zpowers c)
          (Subgroup.mem_zpowers c) k'))
    · rw [h1]
      exact Subgroup.mul_mem (Subgroup.zpowers a ⊔ Subgroup.zpowers b)
        (Subgroup.inv_mem (Subgroup.zpowers a ⊔ Subgroup.zpowers b)
          (Subgroup.mul_mem_sup
            (Subgroup.pow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) i)
            (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) j)))
        (Subgroup.mul_mem_sup
          (Subgroup.pow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) i')
          (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) j'))
  have hbot : c ^ k * (c ^ k')⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hsup]; exact hZcZab
  rw [Subgroup.mem_bot] at hbot
  exact mul_inv_eq_one.mp hbot

theorem normal_form_unique {a b c : G} (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hc3 : orderOf c = 3)
    (hpair : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    (hsup : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥)
    {i j k i' j' k' : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3)
    (hi' : i' < 3) (hj' : j' < 3) (hk' : k' < 3)
    (heq : a ^ i * b ^ j * c ^ k = a ^ i' * b ^ j' * c ^ k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hck : c ^ k = c ^ k' := inverting_c_pow_eq_of_normal_form_eq hsup heq
  have hkk' : k = k' := pow_eq_of_lt_of_orderOf_eq_three hc3 hk hk' hck
  subst k'
  have hai : a ^ i = a ^ i' := inverting_a_pow_eq_of_normal_form_eq hpair heq
  have hii' : i = i' := pow_eq_of_lt_of_orderOf_eq_three ha3 hi hi' hai
  subst i'
  have hjj' : j = j' := by
    have h2 : a ^ i * b ^ j = a ^ i * b ^ j' := by
      have := congrArg (fun t => t * (c ^ k)⁻¹) heq
      simpa [mul_assoc] using this
    exact pow_eq_of_lt_of_orderOf_eq_three hb3 hj hj' (mul_left_cancel h2)
  exact ⟨rfl, hjj', rfl⟩


theorem commute_of_commutator_mem {T Q : Subgroup G} {u v : G} (hu : u ∈ T) (hv : v ∈ T)
    (hQ : ⁅u, v⁆ ∈ Q) (hTQ : T ⊓ Q = ⊥) : u * v = v * u := by
  have hT : ⁅u, v⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hu hv) (T.inv_mem hu)) (T.inv_mem hv)
  have hbot : ⁅u, v⁆ = 1 := by
    have hmem : ⁅u, v⁆ ∈ T ⊓ Q := ⟨hT, hQ⟩
    rwa [hTQ, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hbot

theorem cj_mul_cj (x u v : G) : cj x (u * v) = cj x u * cj x v := by
  simp only [cj]
  group

theorem cj_pow (x u : G) (n : ℕ) : cj x (u ^ n) = (cj x u) ^ n := by
  have := MonoidHom.map_pow (MulAut.conj x⁻¹).toMonoidHom u n
  simpa [cj, MulAut.conj_apply, inv_inv] using this

theorem map_conj_closure_three (x a b c : G) :
    (Subgroup.closure ({a, b, c} : Set G)).map (MulAut.conj x⁻¹).toMonoidHom =
      Subgroup.closure ({cj x a, cj x b, cj x c} : Set G) := by
  rw [MonoidHom.map_closure]
  have himg : (MulAut.conj x⁻¹).toMonoidHom '' ({a, b, c} : Set G) =
      ({cj x a, cj x b, cj x c} : Set G) := by
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
      · exact Or.inl (by simp [cj, MulAut.conj_apply])
      · exact Or.inr (Or.inl (by simp [cj, MulAut.conj_apply]))
      · exact Or.inr (Or.inr (by simp [cj, MulAut.conj_apply]))
    · rintro (rfl | rfl | rfl)
      · exact ⟨a, Or.inl rfl, by simp [cj, MulAut.conj_apply]⟩
      · exact ⟨b, Or.inr (Or.inl rfl), by simp [cj, MulAut.conj_apply]⟩
      · exact ⟨c, Or.inr (Or.inr rfl), by simp [cj, MulAut.conj_apply]⟩
  rw [himg]


theorem cj_normal_form {x a b c : G} (hxa : cj x a = b) (hxb : cj x b = c)
    (hxc : cj x c = a) (i j k : ℕ) :
    cj x (a ^ i * b ^ j * c ^ k) = b ^ i * c ^ j * a ^ k := by
  rw [cj_mul_cj, cj_mul_cj, cj_pow, cj_pow, cj_pow, hxa, hxb, hxc]

private theorem xreg_mul_three_mem_closure (a b c : G) :
    a * b * c ∈ Subgroup.closure ({a, b, c} : Set G) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))

private theorem xreg_mul_three_mem_centralizer {X : Subgroup G} {x a b c : G}
    (hX : X = Subgroup.zpowers x) (hab : Commute a b) (hac : Commute a c)
    (hxa : cj x a = b) (hxb : cj x b = c) (hxc : cj x c = a) :
    a * b * c ∈ Subgroup.centralizer (X : Set G) := by
  have hcjz : cj x (a * b * c) = a * b * c := by
    rw [cj_mul_cj, cj_mul_cj, hxa, hxb, hxc]
    simpa only [mul_assoc] using ((hab.symm).mul_left hac.symm).eq
  have hczx : Commute (a * b * c) x := by
    refine mul_left_cancel (a := x⁻¹) ?_
    calc x⁻¹ * ((a * b * c) * x) = x⁻¹ * (a * b * c) * x := by group
      _ = a * b * c := hcjz
      _ = x⁻¹ * (x * (a * b * c)) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hX] at hy
  obtain ⟨n, hyn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hyn]
  exact (hczx.zpow_right n).eq.symm

private theorem xreg_cj_eq_self_of_mem_centralizer {X : Subgroup G} {x m : G}
    (hxX : x ∈ X) (hmC : m ∈ Subgroup.centralizer (X : Set G)) : cj x m = m := by
  have hmx : m * x = x * m := ((Subgroup.mem_centralizer_iff.mp hmC) x hxX).symm
  rw [cj]
  calc x⁻¹ * m * x = x⁻¹ * (m * x) := by group
    _ = x⁻¹ * (x * m) := by rw [hmx]
    _ = m := by group

private theorem xreg_mem_zpowers_mul_three_of_cj_eq_self {x a b c m : G}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3)
    (hpair : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    (hsup : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥)
    (hxa : cj x a = b) (hxb : cj x b = c) (hxc : cj x c = a)
    (hm : m ∈ Subgroup.closure ({a, b, c} : Set G)) (hcjm : cj x m = m) :
    m ∈ Subgroup.zpowers (a * b * c) := by
  obtain ⟨i, j, k, hi, hj, hk, hm'⟩ :=
    normal_form_of_mem_closure hab hac hbc ha3 hb3 hc3 hm
  have hcjform : cj x m = b ^ i * c ^ j * a ^ k := by
    rw [hm', cj_normal_form hxa hxb hxc]
  have heq : a ^ i * b ^ j * c ^ k = b ^ i * c ^ j * a ^ k := by
    rw [← hm', ← hcjform, hcjm]
  have heq' : a ^ i * b ^ j * c ^ k = a ^ k * b ^ i * c ^ j := by
    rw [heq]
    simpa only [mul_assoc] using
      ((hab.symm.pow_pow i k).mul_left (hac.symm.pow_pow j k)).eq
  have huniq := normal_form_unique ha3 hb3 hc3 hpair hsup hi hj hk hk hi hj heq'
  obtain ⟨_, hji, hkj⟩ := huniq
  rw [hm', hkj, hji]
  have hcalc : a ^ i * b ^ i * c ^ i = (a * b * c) ^ i := by
    calc a ^ i * b ^ i * c ^ i = (a * b) ^ i * c ^ i := by rw [hab.mul_pow]
      _ = ((a * b) * c) ^ i := by rw [(hac.mul_left hbc).mul_pow]
  rw [hcalc]
  exact Subgroup.pow_mem (Subgroup.zpowers (a * b * c))
    (Subgroup.mem_zpowers (a * b * c)) i

theorem inf_centralizer_eq_zpowers {A X : Subgroup G} {x a b c z : G}
    (hA : A = Subgroup.closure ({a, b, c} : Set G)) (hX : X = Subgroup.zpowers x)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3)
    (hpair : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    (hsup : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥)
    (hxa : cj x a = b) (hxb : cj x b = c) (hxc : cj x c = a) (hz : z = a * b * c) :
    A ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z := by
  have hzA : z ∈ A := by
    rw [hA, hz]
    exact xreg_mul_three_mem_closure a b c
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    rw [hz]
    exact xreg_mul_three_mem_centralizer hX hab hac hxa hxb hxc
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hzA, hzC⟩)
  rintro m ⟨hmA, hmC⟩
  have hxX : x ∈ X := hX ▸ Subgroup.mem_zpowers x
  have hcjm : cj x m = m := xreg_cj_eq_self_of_mem_centralizer hxX hmC
  have hm' : m ∈ Subgroup.closure ({a, b, c} : Set G) := by rw [← hA]; exact hmA
  have hmz : m ∈ Subgroup.zpowers (a * b * c) :=
    xreg_mem_zpowers_mul_three_of_cj_eq_self hab hac hbc ha3 hb3 hc3 hpair hsup
      hxa hxb hxc hm' hcjm
  rwa [hz]


theorem card_conjugate_eq (L : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate L g) = Nat.card L := by
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem card_I_dvd_card_L_cube {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    Nat.card I ∣ Nat.card L ^ 3 := by
  have hne := conjugates_distinct h hxX hgen hord
  have hx0X : x ^ 0 ∈ X := X.pow_mem hxX 0
  have hx1X : x ^ 1 ∈ X := X.pow_mem hxX 1
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hL0 : Lc L x 0 = L := by rw [Lc, pow_zero, conjugate_one]
  have hcardL0 : Nat.card (Lc L x 0) = Nat.card L := by rw [hL0]
  have hcardL1 : Nat.card (Lc L x 1) = Nat.card L := card_conjugate_eq L (x ^ 1)
  have hcardL2 : Nat.card (Lc L x 2) = Nat.card L := card_conjugate_eq L (x ^ 2)
  have h01 : Lc L x 0 ≤ Subgroup.normalizer (Lc L x 1 : Set G) :=
    conjugate_normalize_of_ne h hx0X hx1X hne.1
  have h02 : Lc L x 0 ≤ Subgroup.normalizer (Lc L x 2 : Set G) :=
    conjugate_normalize_of_ne h hx0X hx2X hne.2.1
  have h12 : Lc L x 1 ≤ Subgroup.normalizer (Lc L x 2 : Set G) :=
    conjugate_normalize_of_ne h hx1X hx2X hne.2.2
  have h10 : Lc L x 1 ≤ Subgroup.normalizer (Lc L x 0 : Set G) :=
    conjugate_normalize_of_ne h hx1X hx0X (Ne.symm hne.1)
  have hsupN : Lc L x 0 ⊔ Lc L x 1 ≤
      Subgroup.normalizer (Lc L x 2 : Set G) := sup_le h02 h12
  have hdvd1 : Nat.card ↥(Lc L x 0 ⊔ Lc L x 1) ∣ Nat.card L * Nat.card L := by
    have hprod := card_sup_mul_card_inf_of_normalizes (A := Lc L x 1) (B := Lc L x 0) h01
    rw [sup_comm (Lc L x 1) (Lc L x 0)] at hprod
    refine ⟨Nat.card ↥(Lc L x 1 ⊓ Lc L x 0), ?_⟩
    rw [hcardL1, hcardL0] at hprod
    rw [← hprod]
  have hI : I = (Lc L x 0 ⊔ Lc L x 1) ⊔ Lc L x 2 := by
    rw [hL0]
    exact eq_sup_Lc h hxX hgen hord
  have hdvd2 : Nat.card I ∣ Nat.card ↥(Lc L x 0 ⊔ Lc L x 1) * Nat.card L := by
    have hprod := card_sup_mul_card_inf_of_normalizes (A := Lc L x 2)
      (B := Lc L x 0 ⊔ Lc L x 1) hsupN
    rw [sup_comm (Lc L x 2), inf_comm (Lc L x 2)] at hprod
    rw [show Nat.card ↥I = Nat.card ↥((Lc L x 0 ⊔ Lc L x 1) ⊔ Lc L x 2) by rw [hI]]
    refine ⟨Nat.card ↥((Lc L x 0 ⊔ Lc L x 1) ⊓ Lc L x 2), ?_⟩
    rw [hprod, hcardL2, mul_comm]
  refine hdvd2.trans ?_
  have h1 : Nat.card ↥(Lc L x 0 ⊔ Lc L x 1) * Nat.card L ∣
      (Nat.card L * Nat.card L) * Nat.card L :=
    mul_dvd_mul_right hdvd1 (Nat.card L)
  have h2 : (Nat.card L * Nat.card L) * Nat.card L = Nat.card L ^ 3 := by ring
  rw [h2] at h1
  exact h1

theorem not_81_dvd_card_L_cube {L : Subgroup G} (halt : IsAlt (Bar2 L) 5) :
    ¬ 81 ∣ Nat.card L ^ 3 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have hcard : Nat.card L = 60 * 2 ^ k := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 (↥L))
    rw [hk] at h
    have hbar : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := card_bar2_L halt
    rw [hbar] at h
    exact h
  have h60 : (60 : ℕ).factorization 3 = 1 := by
    rw [show (60 : ℕ) = 3 * 20 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 20)]
  have h2k : (2 ^ k).factorization 3 = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hfac : ((Nat.card L) ^ 3).factorization 3 = 3 := by
    rw [hcard, Nat.factorization_pow, Nat.factorization_mul (by norm_num)
      (pow_ne_zero _ (by norm_num)), Finsupp.smul_apply, Finsupp.add_apply, h60, h2k]
    simp
  intro hdvd
  have h4 : 4 ≤ ((Nat.card L) ^ 3).factorization 3 := by
    have h81 : (3 : ℕ) ^ 4 ∣ (Nat.card L) ^ 3 := by
      simpa using hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (pow_ne_zero 3 (Nat.card_pos (α := ↥L)).ne')).mp h81
  omega


theorem not_81_dvd_card_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    ¬ 81 ∣ Nat.card I :=
  fun h81 => not_81_dvd_card_L_cube h.L_alt
    (h81.trans (card_I_dvd_card_L_cube h hxX hgen hord))


private theorem xreg_sylow_inf_L_gen {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : X = Subgroup.zpowers x) :
    ∃ (T : Subgroup G) (a : G), IsSylowOf 3 T I ∧ x ∈ Subgroup.normalizer (T : Set G) ∧
      a ∈ T ⊓ L ∧ orderOf a = 3 ∧ T ⊓ Q = ⊥ ∧ T ≤ I ∧ IsPGroup 3 T ∧
      Nat.card ↥(T ⊓ L) = 3 := by
  classical
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  obtain ⟨T, hTsyl, hxNT⟩ := exists_sylow_three_normalized h hxX
  have hT3 : IsPGroup 3 T := hTsyl.isPGroup
  have hTQ : T ⊓ Q = ⊥ := inf_T_Q_eq_bot h hT3
  have hTI : T ≤ I := hTsyl.le
  have hcardTL : Nat.card ↥(T ⊓ L) = 3 := card_inf_sylow_L h hTsyl
  haveI : Nontrivial ↥(T ⊓ L) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardTL
    norm_num at hcardTL
  obtain ⟨n0, hn0⟩ := exists_ne (1 : ↥(T ⊓ L))
  let a : G := (n0 : G)
  have haTL : a ∈ T ⊓ L := n0.2
  have ha3 : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := by
      rw [← hcardTL]
      exact Subgroup.orderOf_dvd_natCard (T ⊓ L) haTL
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      exact hn0 (Subtype.ext (by simpa [a] using orderOf_eq_one_iff.mp h1))
    · exact h3
  exact ⟨T, a, hTsyl, hxNT, haTL, ha3, hTQ, hTI, hT3, hcardTL⟩

private theorem xreg_cycle_mem {T L : Subgroup G} {x a : G} (haT : a ∈ T) (haL : a ∈ L)
    (hxNT : x ∈ Subgroup.normalizer (T : Set G)) :
    cj x a ∈ T ∧ cj x a ∈ Lc L x 1 ∧ cj (x ^ 2) a ∈ T ∧ cj (x ^ 2) a ∈ Lc L x 2 := by
  have hbL : cj x a ∈ Lc L x 1 := by
    simpa only [Lc, pow_one] using conjugate_cj L a x haL
  have hcL : cj (x ^ 2) a ∈ Lc L x 2 := by
    simpa only [Lc] using conjugate_cj L a (x ^ 2) haL
  have hbT : cj x a ∈ T := by
    have h := (Subgroup.mem_normalizer_iff''.mp hxNT) a
    exact h.mp haT
  have hcT : cj (x ^ 2) a ∈ T := by
    have hx2NT : x ^ 2 ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).pow_mem hxNT 2
    have h := (Subgroup.mem_normalizer_iff''.mp hx2NT) a
    exact h.mp haT
  exact ⟨hbT, hbL, hcT, hcL⟩

private theorem xreg_cycle_order_conj {x a : G} (ha3 : orderOf a = 3) (hx3 : x ^ 3 = 1) :
    orderOf (cj x a) = 3 ∧ orderOf (cj (x ^ 2) a) = 3 ∧
      cj x (cj x a) = cj (x ^ 2) a ∧ cj x (cj (x ^ 2) a) = a := by
  have hb3 : orderOf (cj x a) = 3 := by
    have hsem : SemiconjBy x⁻¹ a (cj x a) := by
      simp only [SemiconjBy, cj]
      group
    rw [← SemiconjBy.orderOf_eq x⁻¹ hsem]
    exact ha3
  have hc3 : orderOf (cj (x ^ 2) a) = 3 := by
    have hsem : SemiconjBy (x ^ 2)⁻¹ a (cj (x ^ 2) a) := by
      simp only [SemiconjBy, cj]
      group
    rw [← SemiconjBy.orderOf_eq (x ^ 2)⁻¹ hsem]
    exact ha3
  have hx_b : cj x (cj x a) = cj (x ^ 2) a := by
    rw [cj_mul, show x * x = x ^ 2 by rw [pow_two]]
  have hx_c : cj x (cj (x ^ 2) a) = a := by
    rw [cj_mul]
    rw [show x ^ 2 * x = x ^ 3 by rw [pow_two, pow_three]; group, hx3]
    simp [cj]
  exact ⟨hb3, hc3, hx_b, hx_c⟩

private theorem xreg_commute_cycle {H X L Q I T : Subgroup G} (h : Setup49 H X L Q I)
    {x a b c : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    (haL : a ∈ L) (hbL : b ∈ Lc L x 1) (hcL : c ∈ Lc L x 2)
    (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T) (hTQ : T ⊓ Q = ⊥) :
    Commute a b ∧ Commute a c ∧ Commute b c := by
  have hne := conjugates_distinct h hxX hgen hord
  have hx1X : x ^ 1 ∈ X := X.pow_mem hxX 1
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hQab : ⁅a, b⁆ ∈ Q := by
    have hle : ⁅Lc L x 0, Lc L x 1⁆ ≤ Q :=
      commutator_conjugate_le h (X.pow_mem hxX 0) hx1X hne.1
    exact (Subgroup.commutator_le.mp hle) a
      (by simpa only [Lc, pow_zero, conjugate_one] using haL) b hbL
  have hQac : ⁅a, c⁆ ∈ Q := by
    have hle : ⁅Lc L x 0, Lc L x 2⁆ ≤ Q :=
      commutator_conjugate_le h (X.pow_mem hxX 0) hx2X hne.2.1
    exact (Subgroup.commutator_le.mp hle) a
      (by simpa only [Lc, pow_zero, conjugate_one] using haL) c hcL
  have hQbc : ⁅b, c⁆ ∈ Q := by
    have hle : ⁅Lc L x 1, Lc L x 2⁆ ≤ Q :=
      commutator_conjugate_le h hx1X hx2X hne.2.2
    exact (Subgroup.commutator_le.mp hle) b hbL c hcL
  exact ⟨commute_of_commutator_mem haT hbT hQab hTQ,
    commute_of_commutator_mem haT hcT hQac hTQ,
    commute_of_commutator_mem hbT hcT hQbc hTQ⟩

private theorem xreg_independence_and_inf {H X L Q I T : Subgroup G} (h : Setup49 H X L Q I)
    {x a b c : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    (haL : a ∈ L) (hbL : b ∈ Lc L x 1) (hcL : c ∈ Lc L x 2)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3)
    (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T) (hTQ : T ⊓ Q = ⊥) (hab : Commute a b) :
    (∀ i j k : ℕ, i < 3 → j < 3 → k < 3 →
        a ^ i * b ^ j * c ^ k = 1 → i = 0 ∧ j = 0 ∧ k = 0) ∧
      (Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) ∧
      (Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥) := by
  have hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 →
      a ^ i * b ^ j * c ^ k = 1 → i = 0 ∧ j = 0 ∧ k = 0 := by
    intro i j k hi hj hk hrel
    exact independence h hxX hgen hord haL hbL hcL ha3 hb3 hc3 haT hbT hcT hTQ hi hj hk hrel
  have hpairinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    inf_zpowers_pair_eq_bot ha3 hb3 fun i j hi hj hrel => by
      have := hind i j 0 hi hj (by norm_num) (by simpa using hrel)
      exact ⟨this.1, this.2.1⟩
  have hsupinf : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥ :=
    inf_zpowers_sup_eq_bot ha3 hb3 hc3 hab hind
  exact ⟨hind, hpairinf, hsupinf⟩

private theorem xreg_closure_card_27 {a b c : G} (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hc3 : orderOf c = 3) (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hpairinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    (hsupinf : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥) :
    Nat.card (Subgroup.closure ({a, b, c} : Set G)) = 27 := by
  have hcardpair : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9 :=
    card_sup_zpowers_pair ha3 hb3 hab hpairinf
  have hcardsup : Nat.card ↥((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔
      Subgroup.zpowers c) = 27 :=
    card_sup_zpowers_three ha3 hb3 hc3 hac hbc hcardpair hsupinf
  rw [closure_three_eq_sup]
  exact hcardsup

private theorem xreg_isElemAbelian_closure {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3) :
    IsElemAbelian 3 (Subgroup.closure ({a, b, c} : Set G)) := by
  have ha3' : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcube : ∀ y ∈ ({a, b, c} : Set G), y ^ 3 = 1 := by
    intro y hy
    rcases hy with hy | hy | hy
    · rw [hy]; exact ha3'
    · rw [hy]; exact hb3'
    · rw [hy]; exact hc3'
  have hcommS : ∀ y ∈ ({a, b, c} : Set G), ∀ z ∈ ({a, b, c} : Set G), y * z = z * y := by
    intro y hy z hz
    rcases hy with hy | hy | hy <;> rcases hz with hz | hz | hz <;> rw [hy, hz] <;>
      first
        | rfl
        | exact hab.eq
        | exact hab.eq.symm
        | exact hac.eq
        | exact hac.eq.symm
        | exact hbc.eq
        | exact hbc.eq.symm
  exact isElemAbelian_closure_three hcube hcommS

private theorem xreg_normalizer_closure {X : Subgroup G} {x a b c : G}
    (hX : X = Subgroup.zpowers x) (hxa : cj x a = b) (hxb : cj x b = c)
    (hxc : cj x c = a) :
    X ≤ Subgroup.normalizer (Subgroup.closure ({a, b, c} : Set G) : Set G) := by
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer
      (Subgroup.closure ({a, b, c} : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.closure ({a, b, c} : Set G)).map
      (MulAut.conj x⁻¹).toMonoidHom = Subgroup.closure ({a, b, c} : Set G)
    rw [map_conj_closure_three]
    have hset : ({cj x a, cj x b, cj x c} : Set G) = {a, b, c} := by
      rw [hxa, hxb, hxc]
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
  have hxN : x ∈ Subgroup.normalizer
      (Subgroup.closure ({a, b, c} : Set G) : Set G) := by
    simpa using (Subgroup.normalizer
      (Subgroup.closure ({a, b, c} : Set G) : Set G)).inv_mem hxinvN
  rw [hX]
  exact Subgroup.zpowers_le.mpr hxN

private theorem xreg_centralizer_card {X : Subgroup G} {x a b c : G}
    (hX : X = Subgroup.zpowers x)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hc3 : orderOf c = 3)
    (hpair : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    (hsup : Subgroup.zpowers c ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥)
    (hxa : cj x a = b) (hxb : cj x b = c) (hxc : cj x c = a)
    (hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 →
      a ^ i * b ^ j * c ^ k = 1 → i = 0 ∧ j = 0 ∧ k = 0) :
    Nat.card ↥(Subgroup.closure ({a, b, c} : Set G) ⊓
      Subgroup.centralizer (X : Set G)) = 3 := by
  let z : G := a * b * c
  have ha3' : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hz3 : z ^ 3 = 1 := by
    dsimp only [z]
    rw [(hac.mul_left hbc).mul_pow, hab.mul_pow, ha3', hb3', hc3']
    simp
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hz1' : a * b * c = 1 := by simpa only [z] using hz1
    have hrel : a ^ 1 * b ^ 1 * c ^ 1 = 1 := by
      rw [pow_one, pow_one, pow_one]
      exact hz1'
    have hcontra := hind 1 1 1 (by norm_num) (by norm_num) (by norm_num) hrel
    omega
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz_ne
  rw [inf_centralizer_eq_zpowers (A := Subgroup.closure ({a, b, c} : Set G)) (X := X)
    (x := x) (a := a) (b := b) (c := c) (z := z) rfl hX hab hac hbc ha3 hb3 hc3
    hpair hsup hxa hxb hxc rfl]
  rw [Nat.card_zpowers, hzord]

private theorem xreg_closure_eq_sylow_and_index {H X L Q I T : Subgroup G}
    (h : Setup49 H X L Q I) {x a b c : G} (hxX : x ∈ X)
    (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T) (hTsyl : IsSylowOf 3 T I)
    (hAcard : Nat.card (Subgroup.closure ({a, b, c} : Set G)) = 27) :
    Subgroup.closure ({a, b, c} : Set G) = T ∧
      ¬ 3 ∣ ((Subgroup.closure ({a, b, c} : Set G)).subgroupOf I).index := by
  have hAleT : Subgroup.closure ({a, b, c} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy | hy
    · rw [hy]; exact haT
    · rw [hy]; exact hbT
    · rw [hy]; exact hcT
  have hnot81 : ¬ 81 ∣ Nat.card I := not_81_dvd_card_I h hxX hgen hord
  have hfac_le : (Nat.card I).factorization 3 ≤ 3 := by
    by_contra hlt
    have h4 : 4 ≤ (Nat.card I).factorization 3 := by omega
    have h81 : (3 : ℕ) ^ 4 ∣ Nat.card I :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Nat.card_pos (α := ↥I)).ne').mpr h4
    exact hnot81 (by simpa using h81)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTcard_le : Nat.card T ≤ 27 := by
    have hcard := hTsyl.card_eq (p := 3)
    rw [hcard]
    calc 3 ^ (Nat.card I).factorization 3 ≤ 3 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) hfac_le
      _ = 27 := by norm_num
  have hAT : Subgroup.closure ({a, b, c} : Set G) = T := by
    refine Subgroup.eq_of_le_of_card_ge hAleT ?_
    rw [hAcard]
    exact hTcard_le
  have hidx : ¬ 3 ∣ ((Subgroup.closure ({a, b, c} : Set G)).subgroupOf I).index := by
    have hTidx : ¬ 3 ∣ T.relIndex I := (isSylowOf_iff.mp hTsyl).2.2
    rw [hAT]
    have heqidx : (T.subgroupOf I).index = T.relIndex I := by
      calc (T.subgroupOf I).index = (T.subgroupOf I).relIndex (⊤ : Subgroup ↥I) := by
            rw [Subgroup.relIndex_top_right]
        _ = (T.subgroupOf I).relIndex (I.subgroupOf I) := by rw [Subgroup.subgroupOf_self]
        _ = T.relIndex I := Subgroup.relIndex_subgroupOf (H := T) (K := I) (L := I) le_rfl
    rw [heqidx]
    exact hTidx
  exact ⟨hAT, hidx⟩

theorem exists_XReg_sylow {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) :
    ∃ (A : Subgroup G) (a : G),
      A ≤ I ∧ XReg49 X A ∧ IsPGroup 3 A ∧ ¬ 3 ∣ (A.subgroupOf I).index ∧
      a ∈ L ∧ orderOf a = 3 ∧ A = Subgroup.closure {a, cj x a, cj (x ^ 2) a} := by
  classical
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hord : orderOf x = 3 := orderOf_eq_three_of_zpowers hx h.card_X
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  obtain ⟨T, a, hTsyl, hxNT, haTL, ha3, hTQ, hTI, _hT3, _hcardTL⟩ :=
    xreg_sylow_inf_L_gen h hx
  have haT : a ∈ T := haTL.1
  have haL : a ∈ L := haTL.2
  let b : G := cj x a
  let c : G := cj (x ^ 2) a
  have hxa : cj x a = b := rfl
  obtain ⟨hbT, hbL, hcT, hcL⟩ := xreg_cycle_mem haT haL hxNT
  obtain ⟨hb3, hc3, hxb, hxc⟩ := xreg_cycle_order_conj ha3 hx3
  obtain ⟨hab, hac, hbc⟩ := xreg_commute_cycle h hxX hx hord haL hbL hcL haT hbT hcT hTQ
  obtain ⟨hind, hpairinf, hsupinf⟩ :=
    xreg_independence_and_inf h hxX hx hord haL hbL hcL ha3 hb3 hc3 haT hbT hcT hTQ hab
  let A : Subgroup G := Subgroup.closure ({a, b, c} : Set G)
  have hAcard : Nat.card A = 27 := xreg_closure_card_27 ha3 hb3 hc3 hab hac hbc hpairinf hsupinf
  have hAelem : IsElemAbelian 3 A := xreg_isElemAbelian_closure hab hac hbc ha3 hb3 hc3
  have hAnorm : X ≤ Subgroup.normalizer (A : Set G) := xreg_normalizer_closure hx hxa hxb hxc
  have hcentral : Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set G)) = 3 :=
    xreg_centralizer_card hx hab hac hbc ha3 hb3 hc3 hpairinf hsupinf hxa hxb hxc hind
  have hXReg : XReg49 X A := ⟨h.card_X, hAelem, hAcard, hAnorm, hcentral⟩
  have hAI : A ≤ I := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy | hy
    · rw [hy]; exact le_I h haL
    · rw [hy]; exact hTI hbT
    · rw [hy]; exact hTI hcT
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by simpa using hAcard)
  obtain ⟨hAT, hidx⟩ := xreg_closure_eq_sylow_and_index h hxX hx hord haT hbT hcT hTsyl hAcard
  exact ⟨A, a, hAI, hXReg, hA3, hidx, haL, ha3, rfl⟩


theorem alternating_five_inversion_all :
    ∀ g : alternatingGroup (Fin 5), g ^ 3 = 1 →
      ∃ h : alternatingGroup (Fin 5), h * g * h⁻¹ = g⁻¹ := by
  decide +kernel

theorem alternating_five_inversion (g : alternatingGroup (Fin 5)) (hg : g ^ 3 = 1) :
    ∃ h : alternatingGroup (Fin 5), h * g * h⁻¹ = g⁻¹ :=
  alternating_five_inversion_all g hg


theorem exists_inverting_pCoreOf {L Q : Subgroup G} (halt : IsAlt (Bar2 L) 5)
    {a : G} (haL : a ∈ L) (ha3 : orderOf a = 3) :
    ∃ n₀ : G, n₀ ∈ L ∧ n₀ * a * n₀⁻¹ * a ∈ CFSG.Open.pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := halt
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let aL : ↥L := ⟨a, haL⟩
  let ā : Bar2 L := π aL
  have ha3' : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have hā3 : ā ^ 3 = 1 := by
    have h : aL ^ 3 = 1 := by
      apply Subtype.ext
      simpa [aL, ha3']
    simpa [ā, π] using congrArg π h
  obtain ⟨h, hh⟩ := alternating_five_inversion (e ā) (by rw [← map_pow, hā3, map_one])
  let g : Bar2 L := e.symm h
  have hg : g * ā * g⁻¹ = ā⁻¹ := by
    apply e.injective
    simpa [g, map_mul, map_inv] using hh
  obtain ⟨n₀L, hn₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
  let xL : ↥L := (n₀L * aL * n₀L⁻¹) * aL
  have hker : π xL = 1 := by
    simp only [xL, map_mul, map_inv, hn₀, ā, π, hg, inv_mul_cancel]
  have hmem : xL ∈ CFSG.pCore 2 (↥L) := (QuotientGroup.eq_one_iff xL).mp hker
  refine ⟨(n₀L : G), n₀L.2, ?_⟩
  have hmemP : (xL : G) ∈ CFSG.Open.pCoreOf 2 L :=
    (mem_pCoreOf_iff xL.2).mpr (by simpa using hmem)
  simpa [xL, aL, mul_assoc] using hmemP


theorem isPGroup_inf_I_Q {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    IsPGroup 2 ↥(I ⊓ Q) :=
  (isPGroup_Q h).to_le inf_le_right

theorem I_le_normalizer_inf_I_Q {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    I ≤ Subgroup.normalizer ((I ⊓ Q : Subgroup G) : Set G) := by
  have h1 : I ≤ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer
  have h2 : I ≤ Subgroup.normalizer (Q : Set G) := (I_le_H h).trans (H_le_normalizer_Q h)
  exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem inf_eq_bot_of_isPGroup_three_two {A R : Subgroup G} (hA : IsPGroup 3 A)
    (hR : IsPGroup 2 R) : A ⊓ R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) A R hA hR)

private theorem inverting_card_sup_eq_mul {A R : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hA_inf_R : A ⊓ R = ⊥) :
    Nat.card ↥(A ⊔ R) = Nat.card A * Nat.card R := by
  have hprod := card_sup_mul_card_inf_of_normalizes (A := R) (B := A) hAR
  rw [inf_comm, hA_inf_R, Subgroup.card_bot, mul_one] at hprod
  rw [sup_comm] at hprod
  rw [mul_comm] at hprod
  exact hprod

private theorem inverting_exists_conj_subgroupOf_eq {A A' R : Subgroup G} {k : ℕ}
    (hA'le : A' ≤ A ⊔ R) (hA3 : IsPGroup 3 A) (hA'3 : IsPGroup 3 A')
    (hAcard : Nat.card A = 27) (hA'card : Nat.card A' = Nat.card A)
    (hcard_sup : Nat.card ↥(A ⊔ R) = Nat.card A * Nat.card R)
    (hRcard : Nat.card R = 2 ^ k) :
    ∃ c₀ : ↥(A ⊔ R),
      MulAut.conj c₀ • (A.subgroupOf (A ⊔ R)) = A'.subgroupOf (A ⊔ R) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHA3 : IsPGroup 3 (A.subgroupOf (A ⊔ R)) := hA3.comap_subtype
  have hHA'3 : IsPGroup 3 (A'.subgroupOf (A ⊔ R)) := hA'3.comap_subtype
  have hHAidx : ¬ 3 ∣ (A.subgroupOf (A ⊔ R)).index := by
    have hmul := Subgroup.index_mul_card (A.subgroupOf (A ⊔ R))
    have hcard1 : Nat.card ↥(A.subgroupOf (A ⊔ R)) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [hcard1, hcard_sup, hAcard, hRcard] at hmul
    have h2 : ¬ 3 ∣ 2 ^ k := by
      intro h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    have : (A.subgroupOf (A ⊔ R)).index = 2 ^ k := by
      rw [mul_comm] at hmul
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥A)) (by simpa [hAcard] using hmul)
    rw [this]; exact h2
  have hHA'idx : ¬ 3 ∣ (A'.subgroupOf (A ⊔ R)).index := by
    have hmul := Subgroup.index_mul_card (A'.subgroupOf (A ⊔ R))
    have hcard1 : Nat.card ↥(A'.subgroupOf (A ⊔ R)) = Nat.card A' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv
    rw [hcard1, hA'card, hcard_sup, hAcard, hRcard] at hmul
    have h2 : ¬ 3 ∣ 2 ^ k := by
      intro h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    have : (A'.subgroupOf (A ⊔ R)).index = 2 ^ k := by
      rw [mul_comm] at hmul
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥A)) (by simpa [hAcard] using hmul)
    rw [this]; exact h2
  obtain ⟨c₀, hc₀⟩ := MulAction.exists_smul_eq ↥(A ⊔ R)
    (hHA3.toSylow hHAidx) (hHA'3.toSylow hHA'idx)
  refine ⟨c₀, ?_⟩
  have := congrArg (fun P : Sylow 3 ↥(A ⊔ R) => (P : Subgroup ↥(A ⊔ R))) hc₀
  simpa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this

private theorem inverting_conjugate_le_sup {A R : Subgroup G} {n₀ a b c : G}
    (hA : A = Subgroup.closure ({a, b, c} : Set G))
    (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hxpaR : n₀ * a * n₀⁻¹ * a ∈ R)
    (hxpbR : n₀ * b * n₀⁻¹ * b⁻¹ ∈ R)
    (hxpcR : n₀ * c * n₀⁻¹ * c⁻¹ ∈ R) :
    CFSG.conjugate A n₀⁻¹ ≤ A ⊔ R := by
  have hA'eq : CFSG.conjugate A n₀⁻¹ = A.map (MulAut.conj n₀).toMonoidHom := by
    rw [CFSG.conjugate]
    simp only [inv_inv]
  rw [hA'eq, hA, MonoidHom.map_closure, ← hA, Subgroup.closure_le]
  rintro y ⟨z, (hz | hz | hz), rfl⟩
  · rw [hz]
    have hdec : n₀ * a * n₀⁻¹ = (n₀ * a * n₀⁻¹ * a) * a⁻¹ := by group
    have hmem : (n₀ * a * n₀⁻¹ * a) * a⁻¹ ∈ A ⊔ R :=
      (A ⊔ R).mul_mem (Subgroup.mem_sup_right hxpaR) (Subgroup.mem_sup_left (A.inv_mem haA))
    convert hmem using 1
    rw [← hdec]
    rfl
  · rw [hz]
    have hdec : n₀ * b * n₀⁻¹ = (n₀ * b * n₀⁻¹ * b⁻¹) * b := by group
    have hmem : (n₀ * b * n₀⁻¹ * b⁻¹) * b ∈ A ⊔ R :=
      (A ⊔ R).mul_mem (Subgroup.mem_sup_right hxpbR) (Subgroup.mem_sup_left hbA)
    convert hmem using 1
    rw [← hdec]
    rfl
  · rw [hz]
    have hdec : n₀ * c * n₀⁻¹ = (n₀ * c * n₀⁻¹ * c⁻¹) * c := by group
    have hmem : (n₀ * c * n₀⁻¹ * c⁻¹) * c ∈ A ⊔ R :=
      (A ⊔ R).mul_mem (Subgroup.mem_sup_right hxpcR) (Subgroup.mem_sup_left hcA)
    convert hmem using 1
    rw [← hdec]
    rfl

private theorem inverting_map_conj_eq_and_inv {A A' : Subgroup G} {c₀ : G}
    (hle1' : ∀ y ∈ A, c₀ * y * c₀⁻¹ ∈ A')
    (hA'card : Nat.card A' = Nat.card A) :
    A.map (MulAut.conj c₀).toMonoidHom = A' ∧
      ∀ z ∈ A', c₀⁻¹ * z * c₀ ∈ A := by
  have heqmap : A.map (MulAut.conj c₀).toMonoidHom = A' := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using hle1' z hz
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj c₀).toMonoidHom
        (MulAut.conj c₀).injective).toEquiv, hA'card]
  refine ⟨heqmap, ?_⟩
  intro z hz
  have hz' : z ∈ A.map (MulAut.conj c₀).toMonoidHom := by rwa [heqmap]
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz'
  rw [← hyz]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group
  exact hy

private theorem inverting_conj_mem_of_eq_mul {A A' : Subgroup G} {bc r c₀ : G}
    (hbcA : bc ∈ A) (hbcrc : bc * r = c₀⁻¹)
    (hmem_inv : ∀ z ∈ A', c₀⁻¹ * z * c₀ ∈ A) :
    ∀ z ∈ A', r * z * r⁻¹ ∈ A := by
  intro z hz
  have h1 : c₀⁻¹ * z * c₀ ∈ A := hmem_inv z hz
  have h2 : bc * (r * z * r⁻¹) * bc⁻¹ ∈ A := by
    have heq : bc * (r * z * r⁻¹) * bc⁻¹ = c₀⁻¹ * z * c₀ := by
      calc bc * (r * z * r⁻¹) * bc⁻¹
          = (bc * r) * z * (bc * r)⁻¹ := by group
        _ = c₀⁻¹ * z * c₀ := by rw [hbcrc]; simp
    rw [heq]; exact h1
  have h3 : bc⁻¹ * (bc * (r * z * r⁻¹) * bc⁻¹) * bc ∈ A :=
    A.mul_mem (A.mul_mem (A.inv_mem hbcA) h2) hbcA
  simpa [mul_assoc] using h3

private theorem inverting_mul_conj_mul_mem {R I : Subgroup G} {r n₀ a : G}
    (hrR : r ∈ R) (hRnorm : I ≤ Subgroup.normalizer (R : Set G))
    (haI : a ∈ I) (hcomm : n₀ * a * n₀⁻¹ * a ∈ R) :
    r * n₀ * a * (r * n₀)⁻¹ * a ∈ R := by
  have hconjR : ∀ z ∈ R, a⁻¹ * z * (a⁻¹)⁻¹ ∈ R := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hRnorm (I.inv_mem haI)) z).mp hz
  have hcalc : r * n₀ * a * (r * n₀)⁻¹ * a =
      (r * (n₀ * a * n₀⁻¹ * a)) * (a⁻¹ * r⁻¹ * a) := by
    simp only [mul_assoc]; group
  rw [hcalc]
  exact R.mul_mem (R.mul_mem hrR hcomm) (by simpa using hconjR r⁻¹ (R.inv_mem hrR))

private theorem inverting_mul_conj_mul_inv_mem {R I : Subgroup G} {r n₀ b : G}
    (hrR : r ∈ R) (hRnorm : I ≤ Subgroup.normalizer (R : Set G))
    (hbI : b ∈ I) (hcomm : n₀ * b * n₀⁻¹ * b⁻¹ ∈ R) :
    r * n₀ * b * (r * n₀)⁻¹ * b⁻¹ ∈ R := by
  have hconjR : ∀ z ∈ R, b * z * b⁻¹ ∈ R := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hRnorm hbI) z).mp hz
  have hcalc : r * n₀ * b * (r * n₀)⁻¹ * b⁻¹ =
      (r * (n₀ * b * n₀⁻¹ * b⁻¹)) * (b * r⁻¹ * b⁻¹) := by
    simp only [mul_assoc]; group
  rw [hcalc]
  exact R.mul_mem (R.mul_mem hrR hcomm) (hconjR r⁻¹ (R.inv_mem hrR))

private theorem inverting_eq_inv_of_mul_mem {A R : Subgroup G} {m a : G}
    (haA : a ∈ A) (hA_inf_R : A ⊓ R = ⊥) (hmaA : m * a * m⁻¹ ∈ A)
    (hmaR : m * a * m⁻¹ * a ∈ R) : m * a * m⁻¹ = a⁻¹ := by
  have hmem : m * a * m⁻¹ * a ∈ A ⊓ R := ⟨A.mul_mem hmaA haA, hmaR⟩
  rw [hA_inf_R, Subgroup.mem_bot] at hmem
  have := congrArg (fun t => t * a⁻¹) hmem
  simpa [mul_assoc] using this

private theorem inverting_eq_self_of_mul_mem {A R : Subgroup G} {m a : G}
    (haA : a ∈ A) (hA_inf_R : A ⊓ R = ⊥) (hmaA : m * a * m⁻¹ ∈ A)
    (hmaR : m * a * m⁻¹ * a⁻¹ ∈ R) : m * a * m⁻¹ = a := by
  have hmem : m * a * m⁻¹ * a⁻¹ ∈ A ⊓ R := ⟨A.mul_mem hmaA (A.inv_mem haA), hmaR⟩
  rw [hA_inf_R, Subgroup.mem_bot] at hmem
  have := congrArg (fun t => t * a) hmem
  simpa [mul_assoc] using this

private theorem inverting_exists_c₀_conj {A R : Subgroup G} {n₀ a b c : G}
    (hA : A = Subgroup.closure ({a, b, c} : Set G))
    (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hA3 : IsPGroup 3 A) (hAcard : Nat.card A = 27)
    (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hA_inf_R : A ⊓ R = ⊥)
    (hxpaR : n₀ * a * n₀⁻¹ * a ∈ R)
    (hxpbR : n₀ * b * n₀⁻¹ * b⁻¹ ∈ R)
    (hxpcR : n₀ * c * n₀⁻¹ * c⁻¹ ∈ R) :
    ∃ c₀ : ↥(A ⊔ R),
      (∀ y ∈ A, (c₀ : G) * y * (c₀ : G)⁻¹ ∈ CFSG.conjugate A n₀⁻¹) ∧
      (∀ z ∈ CFSG.conjugate A n₀⁻¹, (c₀ : G)⁻¹ * z * (c₀ : G) ∈ A) := by
  have hcard_sup : Nat.card ↥(A ⊔ R) = Nat.card A * Nat.card R :=
    inverting_card_sup_eq_mul hAR hA_inf_R
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
  let A' : Subgroup G := CFSG.conjugate A n₀⁻¹
  have hA'eq : A' = A.map (MulAut.conj n₀).toMonoidHom := by
    change CFSG.conjugate A n₀⁻¹ = A.map (MulAut.conj n₀).toMonoidHom
    rw [CFSG.conjugate]
    simp only [inv_inv]
  have hA'card : Nat.card A' = Nat.card A := card_conjugate_eq A n₀⁻¹
  have hA'3 : IsPGroup 3 A' := by
    rw [hA'eq]
    exact hA3.map (MulAut.conj n₀).toMonoidHom
  have hA'le : A' ≤ A ⊔ R :=
    inverting_conjugate_le_sup hA haA hbA hcA hxpaR hxpbR hxpcR
  obtain ⟨c₀, hc₀'⟩ :=
    inverting_exists_conj_subgroupOf_eq hA'le hA3 hA'3 hAcard hA'card hcard_sup hk
  have hle1' : ∀ y ∈ A, (c₀ : G) * y * (c₀ : G)⁻¹ ∈ A' := by
    intro y hy
    have hyH : (⟨y, (le_sup_left : A ≤ A ⊔ R) hy⟩ : ↥(A ⊔ R)) ∈ A.subgroupOf (A ⊔ R) := hy
    have hmem := Subgroup.smul_mem_pointwise_smul (G := ↥(A ⊔ R))
      (⟨y, (le_sup_left : A ≤ A ⊔ R) hy⟩ : ↥(A ⊔ R)) (MulAut.conj (c₀ : ↥(A ⊔ R)))
      (A.subgroupOf (A ⊔ R)) hyH
    rw [hc₀'] at hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  obtain ⟨_, hmem_inv⟩ := inverting_map_conj_eq_and_inv hle1' hA'card
  exact ⟨c₀, hle1', hmem_inv⟩

private theorem inverting_exists_r_conj {A R : Subgroup G} {n₀ a b c : G}
    (hA : A = Subgroup.closure ({a, b, c} : Set G))
    (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hA3 : IsPGroup 3 A) (hAcard : Nat.card A = 27)
    (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hA_inf_R : A ⊓ R = ⊥)
    (hxpaR : n₀ * a * n₀⁻¹ * a ∈ R)
    (hxpbR : n₀ * b * n₀⁻¹ * b⁻¹ ∈ R)
    (hxpcR : n₀ * c * n₀⁻¹ * c⁻¹ ∈ R) :
    ∃ r ∈ R, ∀ z ∈ CFSG.conjugate A n₀⁻¹, r * z * r⁻¹ ∈ A := by
  obtain ⟨c₀, hle1', hmem_inv⟩ :=
    inverting_exists_c₀_conj hA haA hbA hcA hA3 hAcard hR2 hAR hA_inf_R hxpaR hxpbR hxpcR
  let c₁ : ↥(A ⊔ R) := c₀⁻¹
  obtain ⟨bc, hbcA, r, hrR, hbc_r⟩ := (mem_sup_of_le_normalizer hAR).mp c₁.2
  have hbcrc : bc * r = (c₀ : G)⁻¹ := by
    have hc₁ : (c₁ : G) = (bc : G) * r := by rw [hbc_r]
    rw [← hc₁]; rfl
  exact ⟨r, hrR, inverting_conj_mem_of_eq_mul hbcA hbcrc hmem_inv⟩

private theorem inverting_exists_conj_of_mod_R {A R I : Subgroup G} {n₀ a b c r : G}
    (hA : A = Subgroup.closure ({a, b, c} : Set G))
    (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hAI : A ≤ I) (hRnorm : I ≤ Subgroup.normalizer (R : Set G)) (hR_le_I : R ≤ I)
    (hA_inf_R : A ⊓ R = ⊥) (hn₀I : n₀ ∈ I)
    (hxpaR : n₀ * a * n₀⁻¹ * a ∈ R)
    (hxpbR : n₀ * b * n₀⁻¹ * b⁻¹ ∈ R)
    (hxpcR : n₀ * c * n₀⁻¹ * c⁻¹ ∈ R)
    (hrR : r ∈ R)
    (hr_conj : ∀ z ∈ CFSG.conjugate A n₀⁻¹, r * z * r⁻¹ ∈ A) :
    ∃ m ∈ I, m * a * m⁻¹ = a⁻¹ ∧ m * b * m⁻¹ = b ∧ m * c * m⁻¹ = c := by
  have hle1 : ∀ y ∈ A, n₀ * y * n₀⁻¹ ∈ CFSG.conjugate A n₀⁻¹ := by
    intro y hy
    rw [show CFSG.conjugate A n₀⁻¹ = A.map (MulAut.conj n₀).toMonoidHom from by
      rw [CFSG.conjugate]; simp only [inv_inv]]
    exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
  let m : G := r * n₀
  have hmI : m ∈ I := I.mul_mem (hR_le_I hrR) hn₀I
  have hmaA : m * a * m⁻¹ ∈ A := by
    have := hr_conj (n₀ * a * n₀⁻¹) (hle1 a haA)
    simpa [m, mul_assoc] using this
  have hmbA : m * b * m⁻¹ ∈ A := by
    have := hr_conj (n₀ * b * n₀⁻¹) (hle1 b hbA)
    simpa [m, mul_assoc] using this
  have hmcA : m * c * m⁻¹ ∈ A := by
    have := hr_conj (n₀ * c * n₀⁻¹) (hle1 c hcA)
    simpa [m, mul_assoc] using this
  have hmaR : m * a * m⁻¹ * a ∈ R := by
    have := inverting_mul_conj_mul_mem (R := R) (I := I) hrR hRnorm (hAI haA) hxpaR
    simpa [m] using this
  have hmbR : m * b * m⁻¹ * b⁻¹ ∈ R := by
    have := inverting_mul_conj_mul_inv_mem (R := R) (I := I) hrR hRnorm (hAI hbA) hxpbR
    simpa [m] using this
  have hmcR : m * c * m⁻¹ * c⁻¹ ∈ R := by
    have := inverting_mul_conj_mul_inv_mem (R := R) (I := I) hrR hRnorm (hAI hcA) hxpcR
    simpa [m] using this
  exact ⟨m, hmI, inverting_eq_inv_of_mul_mem haA hA_inf_R hmaA hmaR,
    inverting_eq_self_of_mul_mem hbA hA_inf_R hmbA hmbR,
    inverting_eq_self_of_mul_mem hcA hA_inf_R hmcA hmcR⟩

private theorem inverting_exists_inverting_mod_R {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x a : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    (haL : a ∈ L) (ha3 : orderOf a = 3) :
    ∃ n₀ ∈ L,
      n₀ * a * n₀⁻¹ * a ∈ I ⊓ Q ∧
      n₀ * cj x a * n₀⁻¹ * (cj x a)⁻¹ ∈ I ⊓ Q ∧
      n₀ * cj (x ^ 2) a * n₀⁻¹ * (cj (x ^ 2) a)⁻¹ ∈ I ⊓ Q := by
  have hne := conjugates_distinct h hxX hgen hord
  have hx0X : x ^ 0 ∈ X := X.pow_mem hxX 0
  have hx1X : x ^ 1 ∈ X := X.pow_mem hxX 1
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  let b : G := cj x a
  let c : G := cj (x ^ 2) a
  have hbL : b ∈ Lc L x 1 := by
    simpa only [b, Lc, pow_one] using conjugate_cj L a x haL
  have hcL : c ∈ Lc L x 2 := by
    simpa only [c, Lc] using conjugate_cj L a (x ^ 2) haL
  have hle11 : Lc L x 1 ≤ I := by
    rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
    exact le_iSup (fun z : X => CFSG.conjugate L (z : G)) ⟨x ^ 1, hx1X⟩
  have hle21 : Lc L x 2 ≤ I := by
    rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
    exact le_iSup (fun z : X => CFSG.conjugate L (z : G)) ⟨x ^ 2, hx2X⟩
  have hbI : b ∈ I := hle11 hbL
  have hcI : c ∈ I := hle21 hcL
  have hLQ : L ⊓ Q = CFSG.Open.pCoreOf 2 L := by
    simpa only [conjugate_one] using conjugate_inf_pCoreOf_eq h (X.one_mem : (1 : G) ∈ X)
  obtain ⟨n₀, hn₀L, hn₀inv⟩ := exists_inverting_pCoreOf (Q := Q) h.L_alt haL ha3
  have hn₀I : n₀ ∈ I := le_I h hn₀L
  have hpCore_le_Q : CFSG.Open.pCoreOf 2 L ≤ Q := by rw [← hLQ]; exact inf_le_right
  have hle01Q : ⁅Lc L x 0, Lc L x 1⁆ ≤ Q :=
    commutator_conjugate_le h hx0X hx1X hne.1
  have hle02Q : ⁅Lc L x 0, Lc L x 2⁆ ≤ Q :=
    commutator_conjugate_le h hx0X hx2X hne.2.1
  have hn₀L0 : n₀ ∈ Lc L x 0 := by simpa only [Lc, pow_zero, conjugate_one] using hn₀L
  have hxpaR : n₀ * a * n₀⁻¹ * a ∈ I ⊓ Q :=
    ⟨I.mul_mem (I.mul_mem (I.mul_mem hn₀I (le_I h haL)) (I.inv_mem hn₀I)) (le_I h haL),
      hpCore_le_Q hn₀inv⟩
  have hxpbR : n₀ * b * n₀⁻¹ * b⁻¹ ∈ I ⊓ Q :=
    ⟨I.mul_mem (I.mul_mem (I.mul_mem hn₀I hbI) (I.inv_mem hn₀I)) (I.inv_mem hbI),
      (Subgroup.commutator_le.mp hle01Q) n₀ hn₀L0 b hbL⟩
  have hxpcR : n₀ * c * n₀⁻¹ * c⁻¹ ∈ I ⊓ Q :=
    ⟨I.mul_mem (I.mul_mem (I.mul_mem hn₀I hcI) (I.inv_mem hn₀I)) (I.inv_mem hcI),
      (Subgroup.commutator_le.mp hle02Q) n₀ hn₀L0 c hcL⟩
  exact ⟨n₀, hn₀L, hxpaR, by simpa only [b] using hxpbR, by simpa only [c] using hxpcR⟩

theorem exists_inverting49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {A : Subgroup G} {a : G} (hAI : A ≤ I)
    (hA3 : IsPGroup 3 A) (hAcard : Nat.card A = 27) (haL : a ∈ L) (ha3 : orderOf a = 3)
    (hA : A = Subgroup.closure {a, cj x a, cj (x ^ 2) a}) :
    ∃ n ∈ I, cj n a = a⁻¹ ∧ cj n (cj x a) = cj x a ∧
      cj n (cj (x ^ 2) a) = cj (x ^ 2) a := by
  classical
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hord : orderOf x = 3 := orderOf_eq_three_of_zpowers hx h.card_X
  let b : G := cj x a
  let c : G := cj (x ^ 2) a
  let R : Subgroup G := I ⊓ Q
  have hR2 : IsPGroup 2 R := isPGroup_inf_I_Q h
  have hRnorm : I ≤ Subgroup.normalizer (R : Set G) := I_le_normalizer_inf_I_Q h
  have hA_inf_R : A ⊓ R = ⊥ := inf_eq_bot_of_isPGroup_three_two hA3 hR2
  have hR_le_I : R ≤ I := inf_le_left
  have haA : a ∈ A := by rw [hA]; exact Subgroup.subset_closure (Or.inl rfl)
  have hbA : b ∈ A := by rw [hA]; exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hcA : c ∈ A := by rw [hA]; exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hAI.trans hRnorm
  obtain ⟨n₀, hn₀L, hxpaR, hxpbR, hxpcR⟩ :=
    inverting_exists_inverting_mod_R h hxX hx hord haL ha3
  have hn₀I : n₀ ∈ I := le_I h hn₀L
  obtain ⟨r, hrR, hr_conj⟩ :=
    inverting_exists_r_conj (A := A) (R := R) (n₀ := n₀) (a := a) (b := b) (c := c)
      hA haA hbA hcA hA3 hAcard hR2 hAR hA_inf_R hxpaR hxpbR hxpcR
  obtain ⟨m, hmI, hma, hmb, hmc⟩ :=
    inverting_exists_conj_of_mod_R (A := A) (R := R) (I := I) (n₀ := n₀) (a := a)
      (b := b) (c := c) hA haA hbA hcA hAI hRnorm hR_le_I hA_inf_R hn₀I
      hxpaR hxpbR hxpcR hrR hr_conj
  refine ⟨m⁻¹, I.inv_mem hmI, ?_, ?_, ?_⟩
  · simpa only [cj, inv_inv] using hma
  · simpa only [cj, inv_inv, b] using hmb
  · simpa only [cj, inv_inv, c] using hmc


theorem xa49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) :
    ∃ (A : Subgroup G) (a n : G),
      A ≤ I ∧ XReg49 X A ∧ IsPGroup 3 A ∧ ¬ 3 ∣ (A.subgroupOf I).index ∧
      a ∈ L ∧ orderOf a = 3 ∧ A = Subgroup.closure {a, cj x a, cj (x ^ 2) a} ∧
      n ∈ I ∧ cj n a = a⁻¹ ∧ cj n (cj x a) = cj x a ∧ cj n (cj (x ^ 2) a) = cj (x ^ 2) a := by
  obtain ⟨A, a, hAI, hXreg, hA3, hidx, haL, ha3, hA⟩ := exists_XReg_sylow h hx
  obtain ⟨n, hnI, hna, hnb, hnc⟩ :=
    exists_inverting49 h hx hAI hA3 hXreg.2.2.1 haL ha3 hA
  exact ⟨A, a, n, hAI, hXreg, hA3, hidx, haL, ha3, hA, hnI, hna, hnb, hnc⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
