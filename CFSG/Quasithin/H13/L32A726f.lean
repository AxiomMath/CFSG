module

public import CFSG.Quasithin.H13.L32A726e
public import CFSG.RankThree.PGroups.SolvableTrivialComplementCore

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem one_add_one_eq_zero_726 {F : Type*} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : (1 : F) + 1 = 0 := by
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at h0
  rw [one_add_one_eq_two]
  exact pow_eq_zero_iff (by omega) |>.mp h0

theorem exists_orderOf_three_sl2_726 {F : Type*} [Field F] (h2 : (1 : F) + 1 = 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, orderOf A = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdet : Matrix.det !![(0 : F), 1; 1, 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    have : (-1 : F) = 1 := neg_eq_iff_add_eq_zero.mpr h2
    simpa using this
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; 1, 1], hdet⟩
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := rfl
  have h3 : (!![(0 : F), 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [pow_three, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [h2]
  refine ⟨A, orderOf_eq_prime ?_ ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hA, h3, Matrix.SpecialLinearGroup.coe_one]
  · intro h
    have h' := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) F =>
      (B : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [hA, Matrix.SpecialLinearGroup.coe_one] at h'
    simp at h'

theorem exists_orderOf_three_alt_726 {m : ℕ} (hm : 3 ≤ m) :
    ∃ g : alternatingGroup (Fin m), orderOf g = 3 := by
  set a : Fin m := ⟨0, by omega⟩
  set b : Fin m := ⟨1, by omega⟩
  set c : Fin m := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have h : (Equiv.swap a b * Equiv.swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  exact ⟨⟨_, h.mem_alternatingGroup⟩, by rw [Subgroup.orderOf_mk]; exact h.orderOf⟩

omit [Finite G] in
theorem three_dvd_card_of_surjective_726 {K : Subgroup G} {X : Type*} [Group X] (α : ↥K →* X)
    (hα : Function.Surjective α) {g : X} (hg : orderOf g = 3) : 3 ∣ Nat.card K := by
  obtain ⟨k, rfl⟩ := hα g
  rw [← hg]
  exact (orderOf_map_dvd α k).trans (orderOf_dvd_natCard k)

omit [Finite G] in
theorem three_dvd_card_of_isChi0Block_726 {X K : Subgroup G} (h : IsChi0Block X K) :
    3 ∣ Nat.card K := by
  rcases h.2 with ⟨n, hn, F, _, _, hcard, α, hα, -⟩ | ⟨α, hα, -⟩ | ⟨α, hα, -⟩
  · obtain ⟨A, hA⟩ := exists_orderOf_three_sl2_726 (one_add_one_eq_zero_726 (by omega) hcard)
    exact three_dvd_card_of_surjective_726 α hα hA
  · obtain ⟨g, hg⟩ := exists_orderOf_three_alt_726 (m := 3) le_rfl
    exact three_dvd_card_of_surjective_726 α hα hg
  · obtain ⟨g, hg⟩ := exists_orderOf_three_alt_726 (m := 5) (by norm_num)
    exact three_dvd_card_of_surjective_726 α hα hg

theorem relIndex_sup_eq_726 {T I : Subgroup G} (hT : T ≤ Subgroup.normalizer (I : Set G)) :
    T.relIndex (T ⊔ I) = (T ⊓ I).relIndex I := by
  have h1 := Subgroup.relIndex_mul_card T (T ⊔ I)
  have h2 := Subgroup.relIndex_mul_card I (T ⊔ I)
  have h3 := Subgroup.relIndex_mul_card I T
  have h4 := Subgroup.relIndex_mul_card (T ⊓ I) I
  have h5 : I.relIndex (T ⊔ I) = I.relIndex T := A4.relIndex_sup_eq_of_le_normalizer' hT
  rw [inf_eq_left.mpr (le_sup_left : T ≤ T ⊔ I)] at h1
  rw [inf_eq_left.mpr (le_sup_right : I ≤ T ⊔ I), h5] at h2
  rw [inf_eq_left.mpr (inf_le_right : T ⊓ I ≤ I)] at h4
  rw [inf_comm] at h3
  have hpos : 0 < Nat.card (T ⊓ I : Subgroup G) := Nat.card_pos
  have hpos' : 0 < I.relIndex T := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := T)).ne' h3.symm
  have key : T.relIndex (T ⊔ I) * Nat.card (T ⊓ I : Subgroup G) =
      (T ⊓ I).relIndex I * Nat.card (T ⊓ I : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left hpos'
    calc I.relIndex T * (T.relIndex (T ⊔ I) * Nat.card (T ⊓ I : Subgroup G))
        = T.relIndex (T ⊔ I) * (I.relIndex T * Nat.card (T ⊓ I : Subgroup G)) := by ring
      _ = T.relIndex (T ⊔ I) * Nat.card T := by rw [h3]
      _ = I.relIndex T * Nat.card I := by rw [h1, h2]
      _ = I.relIndex T * ((T ⊓ I).relIndex I * Nat.card (T ⊓ I : Subgroup G)) := by rw [h4]
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem card_sup_mul_726 {T I : Subgroup G} (hT : T ≤ Subgroup.normalizer (I : Set G)) :
    Nat.card (T ⊔ I : Subgroup G) * Nat.card (T ⊓ I : Subgroup G) = Nat.card T * Nat.card I := by
  have h1 := Subgroup.relIndex_mul_card T (T ⊔ I)
  have h4 := Subgroup.relIndex_mul_card (T ⊓ I) I
  rw [inf_eq_left.mpr (le_sup_left : T ≤ T ⊔ I)] at h1
  rw [inf_eq_left.mpr (inf_le_right : T ⊓ I ≤ I)] at h4
  rw [← h1, relIndex_sup_eq_726 hT, ← h4]
  ring

theorem charTwo_of_isSolvable_726 {I : Subgroup G} (hs : Group.IsSolvable I)
    (hO : CFSG.pPrimeCore 2 ↥I = ⊥) : CharTwo I := by
  have := hs
  rw [CT.charTwo_iff_internal]
  exact CFSG.RankThree.PGroups.solvable_trivial_complement_core Nat.prime_two hO

theorem charTwo_sup_726 {I Q : Subgroup G} (hI : CharTwo I) (hQ : IsPGroup 2 Q)
    (hQI : Q ≤ Subgroup.normalizer (I : Set G)) : CharTwo (Q ⊔ I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Q ⊔ I with hXdef
  have hXI : X ≤ Subgroup.normalizer (I : Set G) := sup_le hQI Subgroup.le_normalizer
  have hOI : pCoreOf 2 I ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 I).trans le_sup_right)
      (hXI.trans (normalizer_le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  set C := X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) with hCdef
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ g ∈ X, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hg hc.1) (X.inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : g⁻¹ * p * g ∈ pCoreOf 2 X := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 X (X.inv_mem hg)) p).mp hp
        simpa using this
      have h1 := (Subgroup.mem_centralizer_iff.mp hc.2) _ hp'
      calc p * (g * c * g⁻¹) = g * ((g⁻¹ * p * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * p := by group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key g hg c, fun hc => ?_⟩
    have h := key g⁻¹ (X.inv_mem hg) _ hc
    rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at h
  have hCI : I ⊓ C ≤ pCoreOf 2 I := fun x hx => hI ⟨hx.1,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOI) hx.2.2⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 I).exists_card_eq
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have h1 : Nat.card (I ⊓ C : Subgroup G) ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le hCI
  have h2 : I.relIndex C ∣ 2 ^ m := by
    have e1 : I.relIndex (C ⊔ I) = I.relIndex C :=
      A4.relIndex_sup_eq_of_le_normalizer' (inf_le_left.trans hXI)
    have e2 : I.relIndex (Q ⊔ I) = I.relIndex Q := A4.relIndex_sup_eq_of_le_normalizer' hQI
    have e3 := Subgroup.relIndex_mul_relIndex I (C ⊔ I) X le_sup_right
      (sup_le inf_le_left le_sup_right)
    rw [e1, e2] at e3
    rw [← hm]
    exact (Dvd.intro _ e3).trans (Subgroup.relIndex_dvd_card I Q)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hCp : IsPGroup 2 C := by
    refine IsPGroup.of_card (n := j + i) ?_
    rw [← Subgroup.relIndex_mul_card I C, hj, hi, pow_add]
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hXC hCp

theorem pPrimeCore_eq_bot_726 {I G0 : Subgroup G} (hIG0 : I ≤ G0)
    (hG0I : G0 ≤ Subgroup.normalizer (I : Set G))
    (hO : ∀ N : Subgroup G, N ≤ G0 → G0 ≤ Subgroup.normalizer (N : Set G) →
      Odd (Nat.card N) → N = ⊥) : CFSG.pPrimeCore 2 ↥I = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K0 := CFSG.pPrimeCore 2 ↥I with hK0
  have h1 : G0 ≤ Subgroup.normalizer ((K0.map I.subtype : Subgroup G) : Set G) :=
    hG0I.trans (normalizer_le_normalizer_map_of_characteristic K0)
  have h2 : Odd (Nat.card (K0.map I.subtype : Subgroup G)) := by
    rw [Subgroup.card_map_of_injective I.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have h3 := hO _ ((Subgroup.map_subtype_le K0).trans hIG0) h1 h2
  exact (Subgroup.map_eq_bot_iff_of_injective K0 I.subtype_injective).mp h3

section Ctx

variable {T L V H D : Subgroup G}

theorem le_hd_of_not_three_dvd_726 (hC129 : ASC129Statement G) (hc : Ctx726 G T L V H D)
    {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T)
    (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G))
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) {I : Subgroup G}
    (hIG0 : I ≤ G0) (hG0I : G0 ≤ Subgroup.normalizer (I : Set G)) (h3I : ¬ 3 ∣ Nat.card I)
    (hXc : CharTwo (pCoreOf 2 H ⊔ I)) : I ≤ H ⊓ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hd := H ⊓ Subgroup.centralizer ({d} : Set G) with hHd
  set Q := pCoreOf 2 H with hQdef
  have hQHd : Q ≤ Hd := hQ.trans (td_le_hd_726 hc d)
  have hQG0 : Q ≤ G0 := hQHd.trans hHdG0
  have h2el : ∀ g ∈ I, g ∈ H → ∃ n : ℕ, g ^ 2 ^ n = 1 := by
    intro g hgI hgH
    have h3 : ¬ 3 ∣ orderOf g := fun h => h3I (by
      have h1 := orderOf_dvd_natCard (⟨g, hgI⟩ : ↥I)
      rw [Subgroup.orderOf_mk] at h1
      exact h.trans h1)
    have hH : orderOf g ∣ Nat.card H := by
      have h1 := orderOf_dvd_natCard (⟨g, hgH⟩ : ↥H)
      rwa [Subgroup.orderOf_mk] at h1
    have hpow : ∃ n : ℕ, orderOf g = 2 ^ n := by
      refine ⟨(orderOf g).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd
        (orderOf_pos g).ne' fun {r} hr hrd => ?_⟩
      rcases hc.two_three r hr (hrd.trans hH) with h | h
      · exact h
      · exact absurd (h ▸ hrd) h3
    obtain ⟨n, hn⟩ := hpow
    exact ⟨n, by rw [← hn]; exact pow_orderOf_eq_one g⟩
  have hIHd : I ⊓ Hd ≤ Q := by
    rw [hQdef, ← pCoreOf_hd_eq_726 hc hdD hdV hQ]
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
    · intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp (hG0I (hHdG0 hh)) y
      have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hh) y
      exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
    · intro y
      obtain ⟨n, hn⟩ := h2el y y.2.1 y.2.2.1
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hQnI : Q ≤ Subgroup.normalizer (I : Set G) := hQG0.trans hG0I
  set X := Q ⊔ I with hXdef
  have hXG0 : X ≤ G0 := sup_le hQG0 hIG0
  have hTd := isSylowTwoOf_td_g0_726 hc hdD hdV htT htd hHdG0 hG0
  have hTdI : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({d} : Set G) ⊓ I) I :=
    A4.isSylowTwoOf_inf_normal hTd hIG0 hG0I
  have hsylX : IsSylowTwoOf Q X := by
    refine ⟨le_sup_left, pCoreOf_isPGroup 2 H, ?_⟩
    have e := relIndex_sup_eq_726 hQnI
    show ¬ 2 ∣ Q.relIndex (Q ⊔ I)
    rw [e]
    intro h2
    apply hTdI.2.2
    have hle : T ⊓ Subgroup.centralizer ({d} : Set G) ⊓ I ≤ Q ⊓ I := le_inf
      (fun x hx => hIHd ⟨hx.2, td_le_hd_726 hc d hx.1⟩) inf_le_right
    have hmul := Subgroup.relIndex_mul_relIndex _ (Q ⊓ I) I hle inf_le_right
    exact h2.trans (Dvd.intro_left _ hmul)
  have hNQ : Subgroup.normalizer (Q : Set G) = H :=
    le_antisymm (normalizer_le_of_le_normalizer_726 hc (pCoreOf_h_ne_bot_726 hc)
      (pCoreOf_isPGroup 2 H) (le_normalizer_pCoreOf 2 H)) (le_normalizer_pCoreOf 2 H)
  have hyp : HypC23 X Q (Hd ⊓ X) := by
    refine ⟨(isSQTKIn_of_pCoreOf_ne_bot_726 hc
      (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0)).mono hXG0, ?_, inf_le_right, ?_, ?_⟩
    · refine ⟨le_sup_left, pCoreOf_h_ne_bot_726 hc, ?_⟩
      have heq : X ⊓ Subgroup.normalizer (Q : Set G) = Hd ⊓ X := by
        rw [hNQ]
        apply le_antisymm
        · exact fun x hx => ⟨⟨hx.2, hG0 (hXG0 hx.1)⟩, hx.1⟩
        · exact fun x hx => ⟨hx.2, hx.1.1⟩
      rw [heq]
      apply le_antisymm
      · exact le_pCoreOf_of_le_normalizer 2 (le_inf hQHd le_sup_left)
          (inf_le_left.trans (inf_le_left.trans (le_normalizer_pCoreOf 2 H)))
          (pCoreOf_isPGroup 2 H)
      · exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf
          (isSylowTwoOf_of_le_726 hsylX (le_inf hQHd le_sup_left) inf_le_right)
    · exact le_inf ((cgsIn_le_726 hc (hXG0.trans hG0))) (cgsIn_le X Q)
    · rw [conjClosure_eq_of_le_normalizer_726
        (inf_le_left.trans (inf_le_left.trans (le_normalizer_pCoreOf 2 H)))]
      refine ⟨le_rfl, pCoreOf_isPGroup 2 H, ?_⟩
      rw [Subgroup.subgroupOf_self, Subgroup.index_top]
      norm_num
  have h3X : ¬ 3 ∣ Nat.card X := by
    intro h3
    have e := card_sup_mul_726 hQnI
    have h3' : 3 ∣ Nat.card Q * Nat.card I := e ▸ h3.mul_right _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
    · obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
      rw [hm] at h
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
    · exact h3I h
  obtain ⟨r, Lb, hLb, hprod⟩ := c2_5 hC129 hyp hsylX hXc
  have hr0 : r = 0 := by
    by_contra hr
    have hb := hLb ⟨0, Nat.pos_of_ne_zero hr⟩
    exact h3X ((three_dvd_card_of_isChi0Block_726 hb).trans (Subgroup.card_dvd_of_le hb.1.2.1))
  subst hr0
  intro x hx
  obtain ⟨m, hm, y, -, hxm⟩ := hprod x ((le_sup_right : I ≤ X) hx)
  have : x = m := by simpa using hxm
  rw [this]
  exact hm.1

theorem le_pCoreOf_of_pow_prime_726 (hC129 : ASC129Statement G) (hc : Ctx726 G T L V H D)
    {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T)
    (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G))
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G))
    (hO : ∀ N : Subgroup G, N ≤ G0 → G0 ≤ Subgroup.normalizer (N : Set G) →
      Odd (Nat.card N) → N = ⊥)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) {I : Subgroup G} (hIG0 : I ≤ G0)
    (hG0I : G0 ≤ Subgroup.normalizer (I : Set G)) (hQI : pCoreOf 2 G0 ≤ I)
    (hIq : ∀ g ∈ I, ∃ k : ℕ, g ^ q ^ k ∈ pCoreOf 2 G0) : I ≤ pCoreOf 2 G0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  have h2el : ∀ g ∈ I, g ∈ H → ∃ n : ℕ, g ^ 2 ^ n = 1 := by
    intro g hgI hgH
    obtain ⟨k, hk⟩ := hIq g hgI
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G0) ⟨_, hk⟩
    have hm' : (g ^ q ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hdvd : orderOf g ∣ q ^ k * 2 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hm'
    have hcop : Nat.Coprime (orderOf g) (q ^ k) := by
      refine Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hq).mpr ?_).symm
      intro hqg
      have hqH : q ∣ Nat.card H := by
        have h1 := orderOf_dvd_natCard (⟨g, hgH⟩ : ↥H)
        rw [Subgroup.orderOf_mk] at h1
        exact hqg.trans h1
      rcases hc.two_three q hq hqH with h | h
      · exact hq2 h
      · exact hq3 h
    exact ⟨m, orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)⟩
  have hIsolv : Group.IsSolvable I := by
    set N := (pCoreOf 2 G0).subgroupOf I with hN
    have hNs : Group.IsSolvable ↥N := by
      have hp : IsPGroup 2 ↥N :=
        (pCoreOf_isPGroup 2 G0).of_equiv (Subgroup.subgroupOfEquivOfLe hQI).symm
      have : Group.IsNilpotent ↥N := hp.isNilpotent
      infer_instance
    have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQI).mpr
      (hIG0.trans (le_normalizer_pCoreOf 2 G0))
    have hQs : Group.IsSolvable (↥I ⧸ N) := by
      have hp : IsPGroup q (↥I ⧸ N) := by
        intro a
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨k, hk⟩ := hIq a a.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
        exact hk
      have : Group.IsNilpotent (↥I ⧸ N) := hp.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hIc : CharTwo I := charTwo_of_isSolvable_726 hIsolv (pPrimeCore_eq_bot_726 hIG0 hG0I hO)
  have hQG0 : pCoreOf 2 H ≤ G0 := (hQ.trans (td_le_hd_726 hc d)).trans hHdG0
  have hXc : CharTwo (pCoreOf 2 H ⊔ I) :=
    charTwo_sup_726 hIc (pCoreOf_isPGroup 2 H) (hQG0.trans hG0I)
  have h3I : ¬ 3 ∣ Nat.card I := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨k, hk⟩ := hIq g g.2
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G0) ⟨_, hk⟩
    have hm' : ((g : G) ^ q ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcop : (orderOf (g : G)).Coprime (q ^ k) := by
      rw [Subgroup.orderOf_coe, hg]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm hq3))
    have hord : orderOf ((g : G) ^ q ^ k) = 3 := by
      rw [hcop.orderOf_pow, Subgroup.orderOf_coe, hg]
    have : 3 ∣ 2 ^ m := hord ▸ orderOf_dvd_of_pow_eq_one hm'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)
  have hIHd := le_hd_of_not_three_dvd_726 hC129 hc hdD hdV hd2 htT htd hHdG0 hG0 hQ hIG0 hG0I
    h3I hXc
  have hI2 : IsPGroup 2 I := fun g => by
    obtain ⟨n, hn⟩ := h2el g g.2 (hIHd g.2).1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  exact le_pCoreOf_of_le_normalizer 2 hIG0 hG0I hI2

theorem oddCoreModTwoTrivial_726 (hC129 : ASC129Statement G) (hc : Ctx726 G T L V H D)
    {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T)
    (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) (hG0H : ¬ G0 ≤ H)
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G))
    (hO : ∀ N : Subgroup G, N ≤ G0 → G0 ≤ Subgroup.normalizer (N : Set G) →
      Odd (Nat.card N) → N = ⊥) : OddCoreModTwoTrivial G0 := by
  by_contra h
  obtain ⟨q, hq, hq2, hne⟩ := exists_odd_pCore_ne_bot h
  have : Fact q.Prime := ⟨hq⟩
  set P := CFSG.pCore q (OTwoQuot G0) with hPdef
  have : P.Normal := inferInstance
  set I := preimH G0 P with hIdef
  have hIG0 : I ≤ G0 := preimH_le G0 P
  have hG0I : G0 ≤ Subgroup.normalizer (I : Set G) := normalizer_preimH
  have hQI : pCoreOf 2 G0 ≤ I := pCoreOf_le_preimH G0 P
  have hIq : ∀ g ∈ I, ∃ k : ℕ, g ^ q ^ k ∈ pCoreOf 2 G0 := by
    intro g hg
    obtain ⟨hgG0, hgP⟩ := mem_preimH.mp hg
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup q (CFSG.pCore q (OTwoQuot G0))) ⟨_, hgP⟩
    refine ⟨k, ⟨⟨g, hgG0⟩ ^ q ^ k, ?_, by simp⟩⟩
    have hk' : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥G0) (⟨g, hgG0⟩ ^ q ^ k) : OTwoQuot G0) =
        1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff _).mp hk'
  have hIle : I ≤ pCoreOf 2 G0 := by
    by_cases hq3 : q = 3
    · subst hq3
      exact le_pCoreOf_of_pow_three_726 hc hdD hdV hd2 htT htd hHdG0 hG0 hG0H hIG0 hG0I hIq
    · exact le_pCoreOf_of_pow_prime_726 hC129 hc hdD hdV hd2 htT htd hHdG0 hG0 hQ hO hq hq2
        hq3 hIG0 hG0I hQI hIq
  apply hne
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥G0) a
  have haI : (a : G) ∈ I := mem_preimH.mpr ⟨a.2, by simpa using ha⟩
  obtain ⟨b, hb, hba⟩ := hIle haI
  have : b = a := Subtype.ext hba
  rw [Subgroup.mem_bot, ← this]
  exact (QuotientGroup.eq_one_iff _).mpr hb

end Ctx

end CFSG.Quasithin.H13.L32A
