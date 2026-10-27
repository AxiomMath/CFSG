module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {V H E J : Subgroup G}

private theorem seven_eleven_bar_sq_eq_one (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ)
    {k : ↥(kSub V H E)} (hk : (k : G) ∈ dSet V H E) : (φ k) ^ 2 = 1 := by
  obtain ⟨U, hU, hkU, -⟩ := mem_dSet.mp hk
  have hUab : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
  have hkk : (k : ↥(kSub V H E)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [pow_two] using elemAbelian_mul_self hUab hkU
  rw [← map_pow, hkk, map_one]

private theorem seven_eleven_bar_mul_sq_eq_one {X : Type} [Group X] {a b : X}
    (hcomm : a * b = b * a) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) : (a * b) ^ 2 = 1 := by
  rw [pow_two]
  have h' : b * a = a * b := hcomm.symm
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [h']
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [← pow_two a, ← pow_two b, ha, hb, one_mul]

private theorem seven_eleven_bar_dvd_two {m : ℕ} (hm : m ∣ 2) : m = 2 ∨ Odd m := by
  have hm' : m ∣ 2 ^ 1 := by simpa using hm
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 1)).mp hm'
  interval_cases k
  · exact Or.inr (by norm_num)
  · exact Or.inl (by norm_num)

private theorem seven_eleven_bar_dvd_four {m : ℕ} (hm : m ∣ 4) : m = 2 ∨ m = 4 ∨ Odd m := by
  have hm' : m ∣ 2 ^ 2 := by simpa using hm
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 2)).mp hm'
  interval_cases k
  · exact Or.inr (Or.inr (by norm_num))
  · exact Or.inl (by norm_num)
  · exact Or.inr (Or.inl (by norm_num))

private theorem seven_eleven_bar_card_conj {X : Type} [Group X] (g : X) (A : Subgroup X) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem seven_eleven_bar_cases {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    {U U' : Subgroup G} (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    {d e : G} (hd : d ∈ U) (he : e ∈ U') :
    (Odd (orderOf (d * e)) ∧ d ∉ normalizer (U' : Set G) ∧ e ∉ normalizer (U : Set G)) ∨
    (d * e = e * d ∧ d ∈ normalizer (U' : Set G) ∧ e ∈ normalizer (U : Set G)) ∨
    ((d * e) ^ 2 = (⁅e, d⁆)⁻¹ ∧ ⁅e, d⁆ ∈ U' ∧ d ∈ normalizer (U' : Set G) ∧
      e ∉ normalizer (U : Set G)) ∨
    ((d * e) ^ 2 = ⁅d, e⁆ ∧ ⁅d, e⁆ ∈ U ∧ d ∉ normalizer (U' : Set G) ∧
      e ∈ normalizer (U : Set G)) := by
  obtain ⟨a, b, rfl, rfl, hN⟩ := nVSub_conj_ne_bot_of_mem_omegaSet hTI hE hU hU'
  have hVa : IsElemAbelian 2 (conjSubgroup V a) := isElemAbelian_conjSubgroup' hV a
  have hVb : IsElemAbelian 2 (conjSubgroup V b) := isElemAbelian_conjSubgroup' hV b
  by_cases hdN : d ∈ normalizer (conjSubgroup V b : Set G)
  · by_cases heN : e ∈ normalizer (conjSubgroup V a : Set G)
    · right; left
      refine ⟨?_, hdN, heN⟩
      by_cases hab : conjSubgroup V a = conjSubgroup V b
      · have he' : e ∈ conjSubgroup V a := by rw [hab]; exact he
        exact elemAbelian_mul_comm hVa hd he'
      · exact nVSub_comm_bSub_conj hTI hab ⟨hd, hdN⟩ ⟨he, heN⟩
    · right; right; left
      have hc := commutator_conj_mem_bSub hV hTI (hw := he) (hu := ⟨hd, hdN⟩)
      refine ⟨?_, hc.1, hdN, heN⟩
      have hd2 : d⁻¹ = d := elemAbelian_inv hVa hd
      have he2 : e⁻¹ = e := elemAbelian_inv hVb he
      rw [commutatorElement_inv, commutatorElement_def, hd2, he2, pow_two]
      group
  · by_cases heN : e ∈ normalizer (conjSubgroup V a : Set G)
    · right; right; right
      have hc := commutator_conj_mem_nVSub hV hTI (hv := hd) (hy := ⟨he, heN⟩)
      refine ⟨?_, hc.1, hdN, heN⟩
      have hd2 : d⁻¹ = d := elemAbelian_inv hVa hd
      have he2 : e⁻¹ = e := elemAbelian_inv hVb he
      rw [commutatorElement_def, hd2, he2, pow_two]
      group
    · left
      exact ⟨odd_orderOf_mul_of_conj hV hTI hN hd (fun h => hdN h.2) he
        (fun h => heN h.2), hdN, heN⟩

private theorem seven_eleven_bar_root_pair (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ)
    {k l : ↥(kSub V H E)} (hk : (k : G) ∈ dSet V H E) (hl : (l : G) ∈ dSet V H E) :
    (orderOf (φ k * φ l) = 2 ∨ orderOf (φ k * φ l) = 4 ∨
      Odd (orderOf (φ k * φ l))) ∧
    (orderOf (φ k * φ l) = 4 →
      (φ k * φ l) ^ 2 ∈ barSet (kSub V H E) φ (dSet V H E)) := by
  obtain ⟨U, hU, hkU, hkO⟩ := mem_dSet.mp hk
  obtain ⟨U', hU', hlU, hlO⟩ := mem_dSet.mp hl
  have hk2 : (φ k) ^ 2 = 1 := seven_eleven_bar_sq_eq_one h hφ hk
  have hl2 : (φ l) ^ 2 = 1 := seven_eleven_bar_sq_eq_one h hφ hl
  have hdvdKL : orderOf (φ k * φ l) ∣ orderOf (k * l : ↥(kSub V H E)) := by
    rw [← map_mul]
    exact orderOf_map_dvd φ (k * l)
  have hcoe : orderOf ((k : G) * (l : G)) = orderOf (k * l : ↥(kSub V H E)) :=
    Subgroup.orderOf_coe (k * l)
  have hdvdG : orderOf (φ k * φ l) ∣ orderOf ((k : G) * (l : G)) := hcoe ▸ hdvdKL
  refine ⟨?_, ?_⟩
  · rcases seven_eleven_bar_cases h.elemAbelian h.ti h.abelian hU hU' hkU hlU with
      ⟨hodd, -, -⟩ | ⟨hcomm, -, -⟩ | ⟨hsq, hcU', hdN, heN⟩ | ⟨hsq, hcU, hdN, heN⟩
    · exact Or.inr (Or.inr (Odd.of_dvd_nat hodd hdvdG))
    · have hkl : k * l = l * k :=
        Subtype.ext (by simpa only [Subgroup.coe_mul] using hcomm)
      have hcommX : φ k * φ l = φ l * φ k := by rw [← map_mul, ← map_mul, hkl]
      have h2 : (φ k * φ l) ^ 2 = 1 :=
        seven_eleven_bar_mul_sq_eq_one hcommX hk2 hl2
      rcases seven_eleven_bar_dvd_two (orderOf_dvd_of_pow_eq_one h2) with h2eq | hodd
      · exact Or.inl h2eq
      · exact Or.inr (Or.inr hodd)
    · have hUab : IsElemAbelian 2 U' := isElemAbelian_of_mem_omegaSet h.elemAbelian hU'
      have h4G : ((k : G) * (l : G)) ^ 4 = 1 := by
        have hmul : ((k : G) * (l : G)) ^ 4 = (((k : G) * (l : G)) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        rw [hmul, hsq, pow_two]
        exact elemAbelian_mul_self hUab ((U').inv_mem hcU')
      exact seven_eleven_bar_dvd_four (hdvdG.trans (orderOf_dvd_of_pow_eq_one h4G))
    · have hUab : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
      have h4G : ((k : G) * (l : G)) ^ 4 = 1 := by
        have hmul : ((k : G) * (l : G)) ^ 4 = (((k : G) * (l : G)) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        rw [hmul, hsq, pow_two]
        exact elemAbelian_mul_self hUab hcU
      exact seven_eleven_bar_dvd_four (hdvdG.trans (orderOf_dvd_of_pow_eq_one h4G))
  · rcases seven_eleven_bar_cases h.elemAbelian h.ti h.abelian hU hU' hkU hlU with
      ⟨hodd, -, -⟩ | ⟨hcomm, -, -⟩ | ⟨hsq, hcU', hdN, heN⟩ | ⟨hsq, hcU, hdN, heN⟩
    · intro h4
      exfalso
      have hodd' : Odd (orderOf (φ k * φ l)) := Odd.of_dvd_nat hodd hdvdG
      rw [h4] at hodd'
      norm_num at hodd'
    · intro h4
      exfalso
      have hkl : k * l = l * k :=
        Subtype.ext (by simpa only [Subgroup.coe_mul] using hcomm)
      have hcommX : φ k * φ l = φ l * φ k := by rw [← map_mul, ← map_mul, hkl]
      have h2 : (φ k * φ l) ^ 2 = 1 :=
        seven_eleven_bar_mul_sq_eq_one hcommX hk2 hl2
      have hdiv : orderOf (φ k * φ l) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [h4] at hdiv
      norm_num at hdiv
    · intro h4
      let c : G := ⁅(l : G), (k : G)⁆
      have hcU'c : c ∈ U' := hcU'
      have hsqc : ((k : G) * (l : G)) ^ 2 = c⁻¹ := hsq
      have hcK : c ∈ kSub V H E := le_kSub hU' hcU'c
      have hcoe' : ((k * l) ^ 2 : ↥(kSub V H E)) = ⟨c⁻¹, (kSub V H E).inv_mem hcK⟩ :=
        Subtype.ext hsqc
      have hsqX : (φ k * φ l) ^ 2 = (φ ⟨c, hcK⟩)⁻¹ := by
        rw [← map_mul, ← map_pow, hcoe', ← map_inv]
        exact congrArg φ (Subtype.ext rfl)
      have hcJ : c ∉ J := by
        intro hcJ
        have hφc : φ ⟨c, hcK⟩ = 1 := (hφ.ker_iff ⟨c, hcK⟩).mpr hcJ
        have h2 : (φ k * φ l) ^ 2 = 1 := by rw [hsqX, hφc, inv_one]
        have hdiv : orderOf (φ k * φ l) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        rw [h4] at hdiv
        norm_num at hdiv
      have hcO : c ∉ pCoreOf 2 H := by
        intro hcO
        have hmem : c ∈ U' ⊓ iSub V H E := by
          rw [inf_iSub_eq_inf_pCoreOf hU']
          exact ⟨hcU'c, hcO⟩
        exact hcJ (h.iSub_le hmem.2)
      have hcd : (c⁻¹ : G) ∈ dSet V H E := by
        refine mem_dSet.mpr ⟨U', hU', (U').inv_mem hcU'c, ?_⟩
        intro h
        exact hcO (by rw [← inv_inv c]; exact (pCoreOf 2 H).inv_mem h)
      refine mem_barSet.mpr ⟨⟨c⁻¹, (kSub V H E).inv_mem hcK⟩, hcd, ?_⟩
      rw [hsqX, ← map_inv]
      exact congrArg φ (Subtype.ext rfl)
    · intro h4
      let c : G := ⁅(k : G), (l : G)⁆
      have hcUc : c ∈ U := hcU
      have hsqc : ((k : G) * (l : G)) ^ 2 = c := hsq
      have hcK : c ∈ kSub V H E := le_kSub hU hcUc
      have hcoe' : ((k * l) ^ 2 : ↥(kSub V H E)) = ⟨c, hcK⟩ := Subtype.ext hsqc
      have hsqX : (φ k * φ l) ^ 2 = φ ⟨c, hcK⟩ := by
        rw [← map_mul, ← map_pow, hcoe']
      have hcJ : c ∉ J := by
        intro hcJ
        have hφc : φ ⟨c, hcK⟩ = 1 := (hφ.ker_iff ⟨c, hcK⟩).mpr hcJ
        have h2 : (φ k * φ l) ^ 2 = 1 := by rw [hsqX, hφc]
        have hdiv : orderOf (φ k * φ l) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        rw [h4] at hdiv
        norm_num at hdiv
      have hcO : c ∉ pCoreOf 2 H := by
        intro hcO
        have hmem : c ∈ U ⊓ iSub V H E := by
          rw [inf_iSub_eq_inf_pCoreOf hU]
          exact ⟨hcUc, hcO⟩
        exact hcJ (h.iSub_le hmem.2)
      have hcd : c ∈ dSet V H E := mem_dSet.mpr ⟨U, hU, hcUc, hcO⟩
      exact mem_barSet.mpr ⟨⟨c, hcK⟩, hcd, hsqX.symm⟩

private theorem seven_eleven_bar_odd_pair (h : Hyp73 V H E J)
    (htr : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k)
    {X : Type} [Group X] {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2)
    {k l : ↥(kSub V H E)} (hk : (k : G) ∈ dSet V H E) (hl : (l : G) ∈ dSet V H E) :
    orderOf (φ k * φ l) ∣ 2 ∨ Odd (orderOf (φ k * φ l)) := by
  obtain ⟨U, hU, hkU, hkO⟩ := mem_dSet.mp hk
  obtain ⟨U', hU', hlU, hlO⟩ := mem_dSet.mp hl
  have hk2 : (φ k) ^ 2 = 1 := seven_eleven_bar_sq_eq_one h hφ hk
  have hl2 : (φ l) ^ 2 = 1 := seven_eleven_bar_sq_eq_one h hφ hl
  have hdvdKL : orderOf (φ k * φ l) ∣ orderOf (k * l : ↥(kSub V H E)) := by
    rw [← map_mul]
    exact orderOf_map_dvd φ (k * l)
  have hcoe : orderOf ((k : G) * (l : G)) = orderOf (k * l : ↥(kSub V H E)) :=
    Subgroup.orderOf_coe (k * l)
  have hdvdG : orderOf (φ k * φ l) ∣ orderOf ((k : G) * (l : G)) := hcoe ▸ hdvdKL
  rcases seven_eleven_bar_cases h.elemAbelian h.ti h.abelian hU hU' hkU hlU with
    ⟨hodd, -, -⟩ | ⟨hcomm, -, -⟩ | ⟨hsq, hcU', hdN, heN⟩ | ⟨hsq, hcU, hdN, heN⟩
  · exact Or.inr (Odd.of_dvd_nat hodd hdvdG)
  · have hkl : k * l = l * k :=
      Subtype.ext (by simpa only [Subgroup.coe_mul] using hcomm)
    have hcommX : φ k * φ l = φ l * φ k := by rw [← map_mul, ← map_mul, hkl]
    exact Or.inl (orderOf_dvd_of_pow_eq_one (seven_eleven_bar_mul_sq_eq_one hcommX hk2 hl2))
  · obtain ⟨k', hk'K, hUk'⟩ := htr U' hU'
    let k'K : ↥(kSub V H E) := ⟨k', hk'K⟩
    have hU'bar : barSub (kSub V H E) φ U' =
        conjSubgroup (barSub (kSub V H E) φ V) (φ k'K) := by
      rw [hUk']
      exact barSub_conjSubgroup φ V k'K
    have hcard : Nat.card (barSub (kSub V H E) φ U') = 2 := by
      rw [hU'bar, seven_eleven_bar_card_conj (φ k'K) (barSub (kSub V H E) φ V), hS]
    have hy1 : φ l ∈ barSub (kSub V H E) φ U' := mem_barSub.mpr ⟨l, hlU, rfl⟩
    have hz1 : φ k * φ l * (φ k)⁻¹ ∈ barSub (kSub V H E) φ U' := by
      have hmem : (k : G) * (l : G) * (k : G)⁻¹ ∈ U' :=
        (Subgroup.mem_normalizer_iff.mp hdN (l : G)).mp hlU
      refine mem_barSub.mpr ⟨k * l * k⁻¹, ?_, ?_⟩
      · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
      · rw [map_mul, map_mul, map_inv]
    have hye : φ l ≠ 1 := fun h1 => hlO (h.pcore_le ((hφ.ker_iff l).mp h1))
    have hzne : φ k * φ l * (φ k)⁻¹ ≠ 1 := by
      intro h1
      apply hye
      have h2 : φ l = 1 := by
        have hconj : (φ k)⁻¹ * (φ k * φ l * (φ k)⁻¹) * φ k = φ l := by group
        rw [h1] at hconj
        simpa using hconj.symm
      exact h2
    obtain ⟨y, -, hyuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(barSub (kSub V H E) φ U'))).mp hcard
    have heq1 : (⟨φ l, hy1⟩ : ↥(barSub (kSub V H E) φ U')) = y :=
      hyuniq _ (fun hh => hye (Subtype.ext_iff.mp hh))
    have heq2 : (⟨φ k * φ l * (φ k)⁻¹, hz1⟩ : ↥(barSub (kSub V H E) φ U')) = y :=
      hyuniq _ (fun hh => hzne (Subtype.ext_iff.mp hh))
    have heq : φ k * φ l * (φ k)⁻¹ = φ l :=
      (Subtype.ext_iff.mp (heq1.trans heq2.symm)).symm
    have hcommX : φ k * φ l = φ l * φ k := by
      calc φ k * φ l = φ k * φ l * (φ k)⁻¹ * φ k := by group
        _ = φ l * φ k := by rw [heq]
    exact Or.inl (orderOf_dvd_of_pow_eq_one (seven_eleven_bar_mul_sq_eq_one hcommX hk2 hl2))
  · obtain ⟨k', hk'K, hUk'⟩ := htr U hU
    let k'K : ↥(kSub V H E) := ⟨k', hk'K⟩
    have hUbar : barSub (kSub V H E) φ U =
        conjSubgroup (barSub (kSub V H E) φ V) (φ k'K) := by
      rw [hUk']
      exact barSub_conjSubgroup φ V k'K
    have hcard : Nat.card (barSub (kSub V H E) φ U) = 2 := by
      rw [hUbar, seven_eleven_bar_card_conj (φ k'K) (barSub (kSub V H E) φ V), hS]
    have hy1 : φ k ∈ barSub (kSub V H E) φ U := mem_barSub.mpr ⟨k, hkU, rfl⟩
    have hz1 : φ l * φ k * (φ l)⁻¹ ∈ barSub (kSub V H E) φ U := by
      have hmem : (l : G) * (k : G) * (l : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp heN (k : G)).mp hkU
      refine mem_barSub.mpr ⟨l * k * l⁻¹, ?_, ?_⟩
      · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
      · rw [map_mul, map_mul, map_inv]
    have hye : φ k ≠ 1 := fun h1 => hkO (h.pcore_le ((hφ.ker_iff k).mp h1))
    have hzne : φ l * φ k * (φ l)⁻¹ ≠ 1 := by
      intro h1
      apply hye
      have h2 : φ k = 1 := by
        have hconj : (φ l)⁻¹ * (φ l * φ k * (φ l)⁻¹) * φ l = φ k := by group
        rw [h1] at hconj
        simpa using hconj.symm
      exact h2
    obtain ⟨y, -, hyuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(barSub (kSub V H E) φ U))).mp hcard
    have heq1 : (⟨φ k, hy1⟩ : ↥(barSub (kSub V H E) φ U)) = y :=
      hyuniq _ (fun hh => hye (Subtype.ext_iff.mp hh))
    have heq2 : (⟨φ l * φ k * (φ l)⁻¹, hz1⟩ : ↥(barSub (kSub V H E) φ U)) = y :=
      hyuniq _ (fun hh => hzne (Subtype.ext_iff.mp hh))
    have heq : φ l * φ k * (φ l)⁻¹ = φ k :=
      (Subtype.ext_iff.mp (heq1.trans heq2.symm)).symm
    have hcommX : φ k * φ l = φ l * φ k := by
      have h2 : φ l * φ k = φ k * φ l := by
        calc φ l * φ k = φ l * φ k * (φ l)⁻¹ * φ l := by group
          _ = φ k * φ l := by rw [heq]
      exact h2.symm
    exact Or.inl (orderOf_dvd_of_pow_eq_one (seven_eleven_bar_mul_sq_eq_one hcommX hk2 hl2))

theorem conj_mem_dSet (h : Hyp73 V H E J) {u x : G} (hu : u ∈ dSet V H E) (hx : x ∈ H) :
    x * u * x⁻¹ ∈ dSet V H E := by
  obtain ⟨U, hU, huU, huO⟩ := mem_dSet.mp hu
  refine mem_dSet.mpr ⟨conjSubgroup U x⁻¹, ?_, ?_, ?_⟩
  · exact conjSubgroup_mem_omegaSet h.le h.normal hU (H.inv_mem hx)
  · rw [mem_conjSubgroup_iff, inv_inv]
    have hxu : (x⁻¹) * (x * u * x⁻¹) * x = u := by group
    rw [hxu]; exact huU
  · intro hmem
    apply huO
    have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hx)
    rw [Subgroup.mem_normalizer_iff] at hnorm
    have hthis : x⁻¹ * (x * u * x⁻¹) * x ∈ pCoreOf 2 H := by
      simpa only [inv_inv] using (hnorm (x * u * x⁻¹)).mp hmem
    rwa [show x⁻¹ * (x * u * x⁻¹) * x = u by group] at hthis

theorem barSet_dSet_eq (h : Hyp73 V H E J)
    (htr : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) :
    barSet (kSub V H E) φ (dSet V H E) =
      Group.conjugatesOfSet ((barSub (kSub V H E) φ V : Set X) \ {1}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hx
    obtain ⟨U, hU, hkU, hkO⟩ := mem_dSet.mp hkS
    obtain ⟨k', hk'K, hUk'⟩ := htr U hU
    let k'K : ↥(kSub V H E) := ⟨k', hk'K⟩
    have hx1 : φ k ≠ 1 := fun h1 => hkO (h.pcore_le ((hφ.ker_iff k).mp h1))
    have hmem : φ k ∈ barSub (kSub V H E) φ U := mem_barSub.mpr ⟨k, hkU, rfl⟩
    have hmem' : φ k ∈ conjSubgroup (barSub (kSub V H E) φ V) (φ k'K) := by
      have h1 : barSub (kSub V H E) φ U =
          conjSubgroup (barSub (kSub V H E) φ V) (φ k'K) := by
        rw [hUk']
        exact barSub_conjSubgroup φ V k'K
      rwa [h1] at hmem
    refine Group.mem_conjugatesOfSet_iff.mpr
      ⟨φ k'K * φ k * (φ k'K)⁻¹, ⟨mem_conjSubgroup_iff.mp hmem', ?_⟩, ?_⟩
    · intro h1
      apply hx1
      have h3 : (φ k'K)⁻¹ * (φ k'K * φ k * (φ k'K)⁻¹) * φ k'K = φ k := by group
      rw [h1] at h3
      simpa using h3.symm
    · exact isConj_iff.mpr ⟨(φ k'K)⁻¹, by group⟩
  · intro hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    have haS : a ∈ barSub (kSub V H E) φ V := ha.1
    have ha1 : a ≠ 1 := by simpa using ha.2
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    obtain ⟨w, hwV, hwφ⟩ := mem_barSub.mp haS
    obtain ⟨k₀, hk₀⟩ := hφ.surjective c
    have hk₀H : (k₀ : G) ∈ H := kSub_le_of_forall_le h.omega_le k₀.2
    have hΩ : conjSubgroup V (k₀ : G)⁻¹ ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet h.le h.normal h.mem (H.inv_mem hk₀H)
    have hx1 : x ≠ 1 := by
      intro h1
      apply ha1
      have h3 : a = c⁻¹ * (c * a * c⁻¹) * c := by group
      rw [hc, h1] at h3
      simpa using h3
    let w' : G := (k₀ : G) * (w : G) * (k₀ : G)⁻¹
    have hw'K : w' ∈ kSub V H E := by
      have hmem : w' ∈ conjSubgroup V (k₀ : G)⁻¹ := by
        rw [mem_conjSubgroup_iff, inv_inv]
        have h : (k₀ : G)⁻¹ * w' * (k₀ : G) = (w : G) := by simp only [w']; group
        rw [h]; exact hwV
      exact le_kSub hΩ hmem
    have hw'O : w' ∉ pCoreOf 2 H := by
      intro hO
      have hmem : w' ∈ conjSubgroup V (k₀ : G)⁻¹ := by
        rw [mem_conjSubgroup_iff, inv_inv]
        have h : (k₀ : G)⁻¹ * w' * (k₀ : G) = (w : G) := by simp only [w']; group
        rw [h]; exact hwV
      have hJ : w' ∈ J := by
        have h2 := (show w' ∈ conjSubgroup V (k₀ : G)⁻¹ ⊓ pCoreOf 2 H from ⟨hmem, hO⟩)
        rw [← inf_iSub_eq_inf_pCoreOf hΩ] at h2
        exact h.iSub_le h2.2
      have hxeq : x = 1 := by
        have h3 : φ ⟨w', hw'K⟩ = x := by
          have he : (⟨w', hw'K⟩ : ↥(kSub V H E)) = k₀ * w * k₀⁻¹ :=
            Subtype.ext (by simp only [w', Subgroup.coe_mul, Subgroup.coe_inv])
          rw [he, map_mul, map_mul, map_inv, hk₀, hwφ, hc]
        have h4 : φ ⟨w', hw'K⟩ = 1 := (hφ.ker_iff ⟨w', hw'K⟩).mpr hJ
        rw [h3] at h4
        exact h4
      exact hx1 hxeq
    have hw'mem : w' ∈ conjSubgroup V (k₀ : G)⁻¹ := by
      rw [mem_conjSubgroup_iff, inv_inv]
      have h : (k₀ : G)⁻¹ * w' * (k₀ : G) = (w : G) := by simp only [w']; group
      rw [h]; exact hwV
    have hw'd : w' ∈ dSet V H E :=
      mem_dSet.mpr ⟨conjSubgroup V (k₀ : G)⁻¹, hΩ, hw'mem, hw'O⟩
    refine mem_barSet.mpr ⟨⟨w', hw'K⟩, hw'd, ?_⟩
    have he : (⟨w', hw'K⟩ : ↥(kSub V H E)) = k₀ * w * k₀⁻¹ :=
      Subtype.ext (by simp only [w', Subgroup.coe_mul, Subgroup.coe_inv])
    rw [he, map_mul, map_mul, map_inv, hk₀, hwφ, hc]

theorem isRootInvolutionSet_barSet (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) :
    CFSG.Timmesfeld.IsRootInvolutionSet (barSet (kSub V H E) φ (dSet V H E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hx
    obtain ⟨U, hU, hkU, hkO⟩ := mem_dSet.mp hkS
    have hx1 : φ k ≠ 1 := fun h1 => hkO (h.pcore_le ((hφ.ker_iff k).mp h1))
    exact orderOf_eq_prime (seven_eleven_bar_sq_eq_one h hφ hkS) hx1
  · intro x hx y hy
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hx
    obtain ⟨l, hlS, rfl⟩ := mem_barSet.mp hy
    exact (seven_eleven_bar_root_pair h hφ hkS hlS).1
  · intro x hx y hy h4
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hx
    obtain ⟨l, hlS, rfl⟩ := mem_barSet.mp hy
    exact (seven_eleven_bar_root_pair h hφ hkS hlS).2 h4

theorem isOddTransp_barSet (h : Hyp73 V H E J)
    (htr : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (barSet (kSub V H E) φ (dSet V H E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hx
    obtain ⟨U, hU, hkU, hkO⟩ := mem_dSet.mp hkS
    have hx1 : φ k ≠ 1 := fun h1 => hkO (h.pcore_le ((hφ.ker_iff k).mp h1))
    exact orderOf_eq_prime (seven_eleven_bar_sq_eq_one h hφ hkS) hx1
  · intro x hx y hy
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hx
    obtain ⟨l, hlS, rfl⟩ := mem_barSet.mp hy
    exact seven_eleven_bar_odd_pair h htr hφ hS hkS hlS

theorem exists_conj_of_isConj_barSet (h : Hyp73 V H E J) (hJK : J ≤ kSub V H E)
    {X : Type} [Group X] {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ)
    (hconj : ∀ x ∈ barSet (kSub V H E) φ (dSet V H E),
      ∀ y ∈ barSet (kSub V H E) φ (dSet V H E), IsConj y x) :
    ∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹ := by
  intro u hu v hv
  have huK : u ∈ kSub V H E := mem_kSub_of_mem_dSet hu
  have hvK : v ∈ kSub V H E := mem_kSub_of_mem_dSet hv
  have huBar : φ ⟨u, huK⟩ ∈ barSet (kSub V H E) φ (dSet V H E) :=
    mem_barSet.mpr ⟨⟨u, huK⟩, hu, rfl⟩
  have hvBar : φ ⟨v, hvK⟩ ∈ barSet (kSub V H E) φ (dSet V H E) :=
    mem_barSet.mpr ⟨⟨v, hvK⟩, hv, rfl⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ huBar _ hvBar)
  obtain ⟨k₀, hk₀⟩ := hφ.surjective c
  have hk₀H : (k₀ : G) ∈ H := kSub_le_of_forall_le h.omega_le k₀.2
  let v' : G := (k₀ : G) * v * (k₀ : G)⁻¹
  have hv'K : v' ∈ kSub V H E := by
    show (k₀ : G) * v * (k₀ : G)⁻¹ ∈ kSub V H E
    exact (kSub V H E).mul_mem ((kSub V H E).mul_mem k₀.2 hvK) ((kSub V H E).inv_mem k₀.2)
  have hv'd : v' ∈ dSet V H E := by
    show (k₀ : G) * v * (k₀ : G)⁻¹ ∈ dSet V H E
    exact conj_mem_dSet h hv hk₀H
  have hφv' : φ ⟨v', hv'K⟩ = φ ⟨u, huK⟩ := by
    have he : (⟨v', hv'K⟩ : ↥(kSub V H E)) = k₀ * ⟨v, hvK⟩ * k₀⁻¹ :=
      Subtype.ext (by simp only [v', Subgroup.coe_mul, Subgroup.coe_inv])
    rw [he, map_mul, map_mul, map_inv, hk₀, hc]
  have huv : u⁻¹ * v' ∈ J := by
    have h1 : φ ((⟨u, huK⟩ : ↥(kSub V H E))⁻¹ * ⟨v', hv'K⟩) = 1 := by
      rw [map_mul, map_inv, hφv', inv_mul_cancel]
    have h2 := (hφ.ker_iff ((⟨u, huK⟩ : ↥(kSub V H E))⁻¹ * ⟨v', hv'K⟩)).mp h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  obtain ⟨j, hjJ, hju⟩ := seven_three_three h.elemAbelian h.ti h.abelian h.le h.normal
    h.omega_le h.pcore_le h.jnormal hu hv'd huv
  refine ⟨j⁻¹ * (k₀ : G), (kSub V H E).mul_mem ((kSub V H E).inv_mem (hJK hjJ)) k₀.2, ?_⟩
  rw [hju]
  simp only [v']
  group

theorem barSet_dSet_eq_setOf_isConj (h : Hyp73 V H E J)
    (htr : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : X} (hs : s ∈ barSub (kSub V H E) φ V)
    (hs1 : s ≠ 1) :
    barSet (kSub V H E) φ (dSet V H E) = {x | IsConj s x} := by
  rw [barSet_dSet_eq h htr hφ]
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    have haS : a ∈ barSub (kSub V H E) φ V := ha.1
    have ha1 : a ≠ 1 := by simpa using ha.2
    have haeq : a = s := by
      obtain ⟨y, -, hyuniq⟩ :=
        (Nat.card_eq_two_iff' (1 : ↥(barSub (kSub V H E) φ V))).mp hS
      have h1 : (⟨a, haS⟩ : ↥(barSub (kSub V H E) φ V)) = y :=
        hyuniq _ (fun hh => ha1 (Subtype.ext_iff.mp hh))
      have h2 : (⟨s, hs⟩ : ↥(barSub (kSub V H E) φ V)) = y :=
        hyuniq _ (fun hh => hs1 (Subtype.ext_iff.mp hh))
      exact Subtype.ext_iff.mp (h1.trans h2.symm)
    rwa [haeq] at hconj
  · intro hx
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨s, ⟨hs, by simpa using hs1⟩, hx⟩

theorem exists_conj_dSet_of_card_eq_two (h : Hyp73 V H E J)
    (htr : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k)
    (hJK : J ≤ kSub V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) J φ) (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    ∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹ := by
  have hSne : barSub (kSub V H E) φ V ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (⊥ : Subgroup X) = 1 := by simp
    rw [hbot] at hS
    rw [h1] at hS
    norm_num at hS
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have hs : (s : X) ∈ barSub (kSub V H E) φ V := s.2
  have hsne : (s : X) ≠ 1 := fun h => hs1 (Subtype.ext h)
  refine exists_conj_of_isConj_barSet h hJK hφ ?_
  intro x hx y hy
  rw [barSet_dSet_eq_setOf_isConj h htr hφ hS hs hsne] at hx hy
  exact (hy.symm).trans hx

end CFSG.LocalAnalysis.WeakClosure81
