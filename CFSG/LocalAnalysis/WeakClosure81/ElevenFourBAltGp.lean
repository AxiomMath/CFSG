module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem le_index_of_ne_top_of_card_mul_two {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    {n : ℕ} (hn : 3 ≤ n) (hcard : Nat.card A * 2 = n.factorial) {H : Subgroup A}
    (hH : H ≠ ⊤) : n ≤ H.index := by
  let ρ : A →* Equiv.Perm (A ⧸ H) := MulAction.toPermHom A (A ⧸ H)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hker | hker
  · rw [← not_lt]
    intro hlt
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
    have hcard_le : Nat.card A ≤ H.index.factorial := by
      calc Nat.card A ≤ Nat.card (Equiv.Perm (A ⧸ H)) :=
            Nat.card_le_card_of_injective (ρ : A → Equiv.Perm (A ⧸ H)) hinj
        _ = (Nat.card (A ⧸ H)).factorial := Nat.card_perm
        _ = H.index.factorial := by rw [Subgroup.index_eq_card]
    have hidx_le : H.index ≤ n - 1 := Nat.le_pred_of_lt hlt
    have hfac : H.index.factorial ≤ (n - 1).factorial := Nat.factorial_le hidx_le
    have h2le : Nat.card A * 2 ≤ (n - 1).factorial * 2 :=
      Nat.mul_le_mul_right 2 (hcard_le.trans hfac)
    have hn0 : n ≠ 0 := by omega
    have hnfac : n * (n - 1).factorial = n.factorial := Nat.mul_factorial_pred hn0
    have hmul : n * (n - 1).factorial ≤ 2 * (n - 1).factorial := by
      calc n * (n - 1).factorial = n.factorial := hnfac
        _ = Nat.card A * 2 := hcard.symm
        _ ≤ (n - 1).factorial * 2 := h2le
        _ = 2 * (n - 1).factorial := by ring
    have : n ≤ 2 := Nat.le_of_mul_le_mul_right hmul (Nat.factorial_pos (n - 1))
    omega
  · have hcore : H.normalCore = ⊤ := by rw [Subgroup.normalCore_eq_ker, hker]
    exact absurd (top_le_iff.mp (hcore ▸ Subgroup.normalCore_le H)) hH

theorem closure_setOf_isTwoPow_eq_top {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (h2 : 2 ∣ Nat.card A) :
    Subgroup.closure {x : A | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
  let X : Set A := {x : A | ∃ k : ℕ, orderOf x = 2 ^ k}
  have hXconj : Group.conjugatesOfSet X ⊆ X := by
    rintro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨y, ⟨k, hk⟩, c, hc⟩ := hx
    exact ⟨k, by rw [(SemiconjBy.orderOf_eq (c : A) hc).symm, hk]⟩
  have hnormal_eq : Subgroup.normalClosure X = Subgroup.closure X :=
    le_antisymm
      (by simpa [Subgroup.normalClosure] using Subgroup.closure_mono (hXconj.trans
        Subgroup.subset_closure))
      Subgroup.closure_le_normalClosure
  haveI hnormal : (Subgroup.closure X).Normal := by rw [← hnormal_eq]; infer_instance
  haveI := Fintype.ofFinite A
  have h2' : 2 ∣ Fintype.card A := by rwa [← Nat.card_eq_fintype_card]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 h2'
  have hxX : x ∈ X := ⟨1, by rw [hx]; norm_num⟩
  have hxne : x ≠ 1 := by rintro rfl; simp at hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure X) with h | h
  · have hxbot : x ∈ (⊥ : Subgroup A) := h ▸ Subgroup.subset_closure hxX
    exact absurd (by simpa using hxbot) hxne
  · exact h

theorem exists_isTwoPow_preimage {H H' : Type} [Group H] [Group H'] [Finite H] (f : H →* H')
    {y : H'} (hy : y ∈ f.range) (hk : ∃ k : ℕ, orderOf y = 2 ^ k) :
    ∃ x : H, f x = y ∧ ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨x₀, hx₀⟩ := hy
  obtain ⟨b, hb⟩ := hk
  obtain ⟨α, r, hr, ha⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hcop : r.Coprime (2 ^ b) := (Nat.coprime_two_right.mpr hr).pow_right b
  let c := Nat.chineseRemainder hcop 0 1
  have hcr : r ∣ c.1 := Nat.modEq_zero_iff_dvd.mp c.prop.1
  obtain ⟨t, ht⟩ := hcr
  refine ⟨x₀ ^ c.1, ?_, ?_⟩
  · rw [map_pow, hx₀]
    have hmod : c.1 % orderOf y = 1 % orderOf y := by rw [hb]; exact c.prop.2
    calc y ^ c.1 = y ^ (c.1 % orderOf y) := (pow_mod_orderOf y c.1).symm
      _ = y ^ (1 % orderOf y) := by rw [hmod]
      _ = y ^ 1 := pow_mod_orderOf y 1
      _ = y := pow_one y
  · have hxpow : (x₀ ^ c.1) ^ 2 ^ α = 1 := by
      have hct : c.1 * 2 ^ α = (2 ^ α * r) * t := by rw [ht]; ring
      calc (x₀ ^ c.1) ^ 2 ^ α = x₀ ^ (c.1 * 2 ^ α) := (pow_mul x₀ c.1 (2 ^ α)).symm
        _ = x₀ ^ ((2 ^ α * r) * t) := by rw [hct]
        _ = (x₀ ^ (2 ^ α * r)) ^ t := pow_mul x₀ (2 ^ α * r) t
        _ = (x₀ ^ orderOf x₀) ^ t := by rw [ha]
        _ = 1 := by rw [pow_orderOf_eq_one, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_iff_pow_eq_one.mpr hxpow)
    exact ⟨j, hj⟩

theorem eq_or_eq_top_of_le_of_index_eq {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    {n : ℕ} (hn : 3 ≤ n) (hcard : Nat.card A * 2 = n.factorial) {S D : Subgroup A}
    (hS : S.index = n) (hSD : S ≤ D) : D = S ∨ D = ⊤ := by
  by_cases hD : D = ⊤
  · exact Or.inr hD
  · left
    have hge : n ≤ D.index := le_index_of_ne_top_of_card_mul_two hn hcard hD
    have hdiv : D.index ∣ S.index := Subgroup.index_dvd_of_le hSD
    have hle : D.index ≤ n := by
      rw [hS] at hdiv
      exact Nat.le_of_dvd (by omega) hdiv
    have hidx : D.index = S.index := by rw [hS]; exact le_antisymm hle hge
    have hcard_eq : Nat.card D = Nat.card S := by
      have hS' := Subgroup.card_mul_index S
      have hD' := Subgroup.card_mul_index D
      rw [hS] at hS'
      rw [hidx, hS] at hD'
      exact Nat.eq_of_mul_eq_mul_right (by omega) (hD'.trans hS'.symm)
    exact (Subgroup.eq_of_le_of_card_ge (H := S) (K := D) hSD (by omega)).symm

theorem b114_ElevenFourBAltGp_factorization_twelve_three : Nat.factorization 12 3 = 1 := by
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h12, Nat.factorization_mul (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)]
  simp [Nat.factorization_eq_zero_iff, Nat.prime_three]

theorem b114_ElevenFourBAltGp_card_le_twelve_of_ne_top {A : Type} [Group A] [Finite A]
    [IsSimpleGroup A] (hA : Nat.card A = 60) {H : Subgroup A} (hH : H ≠ ⊤) :
    Nat.card H ≤ 12 := by
  have hcard5 : Nat.card A * 2 = (5).factorial := by rw [hA]; decide
  have hidx : 5 ≤ H.index := le_index_of_ne_top_of_card_mul_two (by norm_num) hcard5 hH
  have hmul : Nat.card H * 5 ≤ 60 := by
    calc Nat.card H * 5 ≤ Nat.card H * H.index := Nat.mul_le_mul_left _ hidx
      _ = 60 := by rw [Subgroup.card_mul_index, hA]
  have hmul' : 5 * Nat.card H ≤ 5 * 12 := by
    calc 5 * Nat.card H = Nat.card H * 5 := by ring
      _ ≤ 60 := hmul
      _ = 5 * 12 := by norm_num
  exact Nat.le_of_mul_le_mul_left hmul' (by norm_num)

theorem b114_ElevenFourBAltGp_sylow_card_three {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 12) (P : Sylow 3 G) : Nat.card P = 3 := by
  rw [Sylow.card_eq_multiplicity]
  have hfac : Nat.factorization (Nat.card G) 3 = 1 := by
    rw [hG]
    exact b114_ElevenFourBAltGp_factorization_twelve_three
  rw [hfac]
  norm_num

theorem b114_ElevenFourBAltGp_eight_le_card_orderOf_three {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 12) (h3 : Nat.card (Sylow 3 G) = 4) :
    8 ≤ Nat.card {x : G // orderOf x = 3} := by
  classical
  haveI := Fintype.ofFinite G
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hPcard := b114_ElevenFourBAltGp_sylow_card_three hG
  have hfiber : ∀ P : Sylow 3 G, Nat.card {y : P // y ≠ 1} = 2 := by
    intro P
    haveI := Fintype.ofFinite P
    have h1 : Nat.card {y : P // y ≠ 1} = ((Finset.univ : Finset P).erase 1).card :=
      Nat.subtype_card _ (fun y => by simp [Finset.mem_erase])
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      Fintype.card_eq_nat_card, hPcard P]
  have horder : ∀ (P : Sylow 3 G) (y : P), y ≠ 1 → orderOf (y : G) = 3 := by
    intro P y hy
    have hcard : Nat.card (↥P) = 3 := hPcard P
    have hdvd : orderOf y ∣ 3 := by
      have h := orderOf_dvd_natCard y
      rwa [hcard] at h
    rw [Subgroup.orderOf_coe]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy
    · exact h
  let F : (Σ P : Sylow 3 G, {y : P // y ≠ 1}) → {x : G // orderOf x = 3} :=
    fun z => ⟨(z.2.1 : G), horder z.1 z.2.1 z.2.2⟩
  have hinj : Function.Injective F := by
    rintro ⟨P, ⟨y, hy⟩⟩ ⟨Q, ⟨w, hw⟩⟩ h
    have hval : (y : G) = (w : G) := Subtype.ext_iff.mp h
    have hy3 : orderOf (y : G) = 3 := horder P y hy
    have hw3 : orderOf (w : G) = 3 := horder Q w hw
    have hPQ : P = Q := by
      refine Sylow.ext ?_
      have hPz : (P : Subgroup G) = Subgroup.zpowers (y : G) := by
        symm
        exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2)
          (by rw [Nat.card_zpowers, hy3, hPcard P])
      have hQz : (Q : Subgroup G) = Subgroup.zpowers (w : G) := by
        symm
        exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr w.2)
          (by rw [Nat.card_zpowers, hw3, hPcard Q])
      rw [hPz, hQz, hval]
    subst hPQ
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hval)))
  have hdom : Nat.card (Σ P : Sylow 3 G, {y : P // y ≠ 1}) = 8 := by
    rw [Nat.card_sigma]
    have hsum : (∑ P : Sylow 3 G, Nat.card {y : P // y ≠ 1}) = 8 := by
      simp only [hfiber]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h3]
      norm_num
    exact hsum
  calc 8 = Nat.card (Σ P : Sylow 3 G, {y : P // y ≠ 1}) := hdom.symm
    _ ≤ Nat.card {x : G // orderOf x = 3} := Nat.card_le_card_of_injective F hinj

theorem le_or_eq_top_of_card_sixty {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hA : Nat.card A = 60) {S K D : Subgroup A} (hS : Nat.card S = 12) (hKS : K ≤ S)
    (hK : Nat.card K = 4) (hKn : (K.subgroupOf S).Normal) (hKD : K ≤ D) :
    D ≤ S ∨ D = ⊤ := by
  classical
  by_cases hDtop : D = ⊤
  · exact Or.inr hDtop
  · left
    by_contra hDS
    have hDle : Nat.card D ≤ 12 := b114_ElevenFourBAltGp_card_le_twelve_of_ne_top hA hDtop
    have h4dvd : 4 ∣ Nat.card D := by
      rw [← hK]
      exact Subgroup.card_dvd_of_le hKD
    have hDdvd : Nat.card D ∣ 60 := by
      have h : Nat.card D ∣ Nat.card A := by
        simpa using Subgroup.card_dvd_of_le (H := D) (K := ⊤) le_top
      rw [hA] at h
      exact h
    have hD4or12 : Nat.card D = 4 ∨ Nat.card D = 12 := by
      have h4le : 4 ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos h4dvd
      interval_cases Nat.card D <;> norm_num at *
    have hDcard : Nat.card D = 12 := by
      rcases hD4or12 with h4 | h12
      · exfalso
        have hDK : D = K :=
          (Subgroup.eq_of_le_of_card_ge (H := K) (K := D) hKD (by omega)).symm
        exact hDS (hDK ▸ hKS)
      · exact h12
    have hD12 : Nat.card (↥D) = 12 := hDcard
    let K' : Subgroup ↥D := K.subgroupOf D
    have hK'card : Nat.card K' = 4 := by
      have h := Subgroup.card_map_of_injective (f := D.subtype) (K := K')
        (Subtype.coe_injective : Function.Injective (D.subtype : ↥D → A))
      rw [Subgroup.map_subgroupOf_eq_of_le hKD] at h
      exact h.symm.trans hK
    have hN : Subgroup.normalizer (K : Set A) = S := by
      have hle : S ≤ Subgroup.normalizer (K : Set A) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKS).mp hKn
      have hne : Subgroup.normalizer (K : Set A) ≠ ⊤ := by
        intro htop
        haveI : K.Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hbot | htop'
        · have : Nat.card K = 1 := by rw [hbot]; simp
          omega
        · have : Nat.card K = 60 := by simpa [htop'] using hA
          omega
      have hle12 : Nat.card (Subgroup.normalizer (K : Set A)) ≤ 12 :=
        b114_ElevenFourBAltGp_card_le_twelve_of_ne_top hA hne
      exact (Subgroup.eq_of_le_of_card_ge (H := S)
        (K := Subgroup.normalizer (K : Set A)) hle (by rw [hS]; exact hle12)).symm
    have hK'nn : ¬ K'.Normal := by
      intro hnormal
      have hle : D ≤ Subgroup.normalizer (K : Set A) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mp hnormal
      rw [hN] at hle
      exact hDS hle
    let P : Sylow 3 ↥D := Classical.choice Sylow.nonempty
    have hPcard : Nat.card (P : Subgroup ↥D) = 3 :=
      b114_ElevenFourBAltGp_sylow_card_three hDcard P
    have hPnormal : (P : Subgroup ↥D).Normal := by
      by_contra hPn
      have h3card : Nat.card (Sylow 3 ↥D) = 4 := by
        have hmod : Nat.card (Sylow 3 ↥D) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 ↥D
        have hidx : Nat.card (Sylow 3 ↥D) = (Subgroup.normalizer (P : Set ↥D)).index :=
          Sylow.card_eq_index_normalizer P
        have hindexP : (P : Subgroup ↥D).index = 4 := by
          have h := Subgroup.card_mul_index (P : Subgroup ↥D)
          have hcard : Nat.card (↥(P : Subgroup ↥D)) = 3 := hPcard
          rw [hcard, hD12] at h
          omega
        have hdvd : Nat.card (Sylow 3 ↥D) ∣ 4 := by
          rw [hidx]
          have h1 : (Subgroup.normalizer (P : Set ↥D)).index ∣ (P : Subgroup ↥D).index :=
            Subgroup.index_dvd_of_le (H := (P : Subgroup ↥D)) Subgroup.le_normalizer
          rwa [hindexP] at h1
        have hne1 : Nat.card (Sylow 3 ↥D) ≠ 1 := by
          intro h1
          haveI : Subsingleton (Sylow 3 ↥D) := (Nat.card_eq_one_iff_unique.mp h1).1
          exact hPn (Sylow.normal_of_subsingleton P)
        haveI : Nonempty (Sylow 3 ↥D) := Sylow.nonempty
        have hnpos : 1 ≤ Nat.card (Sylow 3 ↥D) :=
          Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
        set n := Nat.card (Sylow 3 ↥D) with hn
        have hnle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases n
        · exact absurd rfl hne1
        · exact absurd hmod (by decide)
        · norm_num at hdvd
        · rfl
      have h8 : 8 ≤ Nat.card {x : ↥D // orderOf x = 3} :=
        b114_ElevenFourBAltGp_eight_le_card_orderOf_three hDcard h3card
      have hcompl_le : Nat.card {x : ↥D // ¬ orderOf x = 3} ≤ 4 := by
        haveI := Fintype.ofFinite ↥D
        rw [Nat.card_eq_fintype_card,
          Fintype.card_subtype_compl (fun x : ↥D => orderOf x = 3)]
        simp only [Fintype.card_eq_nat_card]
        omega
      have hKle : ∀ y : K', ¬ orderOf (y : ↥D) = 3 := by
        intro y hy
        have hcard : Nat.card (↥K') = 4 := hK'card
        have hdvd : orderOf (y : ↥D) ∣ 4 := by
          rw [Subgroup.orderOf_coe]
          have h := orderOf_dvd_natCard y
          rwa [hcard] at h
        rw [hy] at hdvd
        norm_num at hdvd
      have hconj : ∀ (g n : ↥D), orderOf (g * n * g⁻¹) = orderOf n := by
        intro g n
        have h : SemiconjBy g n (g * n * g⁻¹) := by
          rw [SemiconjBy]; group
        exact (SemiconjBy.orderOf_eq g h).symm
      have hcompl_sub : ∀ x : ↥D, ¬ orderOf x = 3 → x ∈ K' := by
        intro x hx
        let inc : K' → {z : ↥D // ¬ orderOf z = 3} := fun y => ⟨(y : ↥D), hKle y⟩
        have hinc : Function.Injective inc := by
          intro y z h
          have hval : (y : ↥D) = (z : ↥D) :=
            congrArg (fun t : {z : ↥D // ¬ orderOf z = 3} => (t : ↥D)) h
          exact Subtype.ext hval
        have hcard_eq : Nat.card K' = Nat.card {z : ↥D // ¬ orderOf z = 3} :=
          le_antisymm (Nat.card_le_card_of_injective inc hinc) (by omega)
        haveI := Fintype.ofFinite K'
        haveI := Fintype.ofFinite {z : ↥D // ¬ orderOf z = 3}
        let e : K' ≃ {z : ↥D // ¬ orderOf z = 3} :=
          Fintype.equivOfCardEq (by
            rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
            exact hcard_eq)
        have hsurj : Function.Surjective inc := by
          have h1 : Function.Injective (e.symm ∘ inc) := e.symm.injective.comp hinc
          have h2 : Function.Surjective (e.symm ∘ inc) := Finite.surjective_of_injective h1
          intro t
          obtain ⟨y, hy⟩ := h2 (e.symm t)
          exact ⟨y, e.symm.injective hy⟩
        obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
        have hval : (y : ↥D) = x :=
          congrArg (fun t : {z : ↥D // ¬ orderOf z = 3} => (t : ↥D)) hy
        have hy2 := y.2
        rw [hval] at hy2
        exact hy2
      have hK'normal : K'.Normal := by
        refine ⟨fun n hn g => hcompl_sub (g * n * g⁻¹) ?_⟩
        rw [hconj g n]
        exact hKle ⟨n, hn⟩
      exact hK'nn hK'normal
    let P' : Subgroup A := Subgroup.map D.subtype (P : Subgroup ↥D)
    have hP'card : Nat.card P' = 3 := by
      have h := Subgroup.card_map_of_injective (f := D.subtype)
        (K := (P : Subgroup ↥D))
        (Subtype.coe_injective : Function.Injective (D.subtype : ↥D → A))
      rw [h, hPcard]
    have hDleN : D ≤ Subgroup.normalizer (P' : Set A) := by
      have h1 := Subgroup.le_normalizer_map (H := (P : Subgroup ↥D)) D.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hPnormal, Subgroup.map_top,
        Subgroup.range_subtype] at h1
      exact h1
    have hnotdvd : ¬ 3 ∣ P'.index := by
      have h : 3 * P'.index = 60 := by
        have hh := Subgroup.card_mul_index P'
        rw [hP'card, hA] at hh
        exact hh
      have hidx : P'.index = 20 := by omega
      rw [hidx]; norm_num
    let Q : Sylow 3 A :=
      (IsPGroup.of_card (p := 3) (n := 1) (by rw [hP'card]; norm_num)).toSylow hnotdvd
    have hQcoe : (Q : Subgroup A) = P' := rfl
    have hnormQ : Subgroup.normalizer (Q : Set A) = Subgroup.normalizer (P' : Set A) := rfl
    have hNne : Subgroup.normalizer (P' : Set A) ≠ ⊤ := by
      intro htop
      haveI : P'.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P' with hbot | htop'
      · have : Nat.card P' = 1 := by rw [hbot]; simp
        omega
      · have : Nat.card P' = 60 := by simpa [htop'] using hA
        omega
    have hNle12 : Nat.card (Subgroup.normalizer (P' : Set A)) ≤ 12 :=
      b114_ElevenFourBAltGp_card_le_twelve_of_ne_top hA hNne
    have hNge12 : 12 ≤ Nat.card (Subgroup.normalizer (P' : Set A)) := by
      have hdvd : Nat.card D ∣ Nat.card (Subgroup.normalizer (P' : Set A)) :=
        Subgroup.card_dvd_of_le hDleN
      rw [hDcard] at hdvd
      exact Nat.le_of_dvd Nat.card_pos hdvd
    have hNcard : Nat.card (Subgroup.normalizer (P' : Set A)) = 12 :=
      le_antisymm hNle12 hNge12
    have hindexN : (Subgroup.normalizer (P' : Set A)).index = 5 := by
      have h := Subgroup.card_mul_index (Subgroup.normalizer (P' : Set A))
      rw [hNcard, hA] at h
      omega
    have hcount : Nat.card (Sylow 3 A) = 5 := by
      rw [Sylow.card_eq_index_normalizer Q, hnormQ, hindexN]
    have hmod3 : Nat.card (Sylow 3 A) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 A
    rw [hcount] at hmod3
    exact absurd hmod3 (by decide)

theorem le_or_eq_top_of_forall_isTwoPow_mem {A : Type} [Group A] [Finite A] {m : ℕ}
    (hm : 2 ≤ m) (φ : A ≃* alternatingGroup (Fin (2 * m + 1))) {S : Subgroup A}
    (hS : Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) {D : Subgroup A}
    (hD : ∀ x ∈ S, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ D) : D ≤ S ∨ D = ⊤ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin (2 * m + 1))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  haveI : IsSimpleGroup A := φ.isSimpleGroup
  haveI : (2 * m + 1).AtLeastTwo := ⟨by omega⟩
  have hcardA : Nat.card A = (2 * m + 1).factorial / 2 := by
    calc Nat.card A = Nat.card (alternatingGroup (Fin (2 * m + 1))) := Nat.card_congr φ.toEquiv
      _ = (Nat.card (Fin (2 * m + 1))).factorial / 2 := nat_card_alternatingGroup
      _ = (2 * m + 1).factorial / 2 := by rw [Nat.card_fin]
  by_cases hm2 : m = 2
  · subst hm2
    have hA60 : Nat.card A = 60 := by rw [hcardA]; decide
    obtain ⟨e⟩ := hS
    have hS12 : Nat.card S = 12 := by
      calc Nat.card S = Nat.card (alternatingGroup (Fin (2 * 2))) := Nat.card_congr e.toEquiv
        _ = (Nat.card (Fin 4)).factorial / 2 := nat_card_alternatingGroup
        _ = 12 := by rw [Nat.card_fin]; decide
    set H : Subgroup S :=
      (alternatingGroup.kleinFour (Fin 4)).map (e.symm : alternatingGroup (Fin 4) →* S)
      with hHdef
    have hkf : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 :=
      alternatingGroup.kleinFour_card_of_card_eq_four (by rw [Nat.card_fin])
    have hKS : H.map S.subtype ≤ S := Subgroup.map_subtype_le H
    have hKcard : Nat.card (H.map S.subtype : Subgroup A) = 4 := by
      have h1 := Subgroup.card_map_of_injective (f := S.subtype) (K := H)
        (Subtype.coe_injective : Function.Injective (S.subtype : S → A))
      have h2 := Subgroup.card_map_of_injective
        (f := (e.symm : alternatingGroup (Fin 4) →* S))
        (K := alternatingGroup.kleinFour (Fin 4)) e.symm.injective
      rw [h1, hHdef, h2, hkf]
    have hHnormal : H.Normal := by
      rw [hHdef]
      exact (alternatingGroup.normal_kleinFour (by rw [Nat.card_fin])).map _
        e.symm.surjective
    have hKsub : (H.map S.subtype).subgroupOf S = H := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨h, hh, hhx⟩
        have : h = x := Subtype.ext hhx
        rwa [← this]
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hKn : ((H.map S.subtype).subgroupOf S).Normal := by
      rw [hKsub]
      exact hHnormal
    have hKD : H.map S.subtype ≤ D := by
      rintro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      rw [hHdef, Subgroup.mem_map] at hh
      obtain ⟨y, hy, rfl⟩ := hh
      exact hD (e.symm y) (e.symm y).2 (by
        have hdvd : orderOf y ∣ 4 := by
          have h := orderOf_dvd_natCard
            (⟨y, hy⟩ : alternatingGroup.kleinFour (Fin 4))
          rw [← Subgroup.orderOf_coe, hkf] at h
          exact h
        have hdvd' : orderOf y ∣ 2 ^ 2 := by
          simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num] using hdvd
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
        exact ⟨k, by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm y, hk]⟩)
    exact le_or_eq_top_of_card_sixty hA60 hS12 hKS hKcard hKn hKD
  · have hm3 : 3 ≤ m := by omega
    obtain ⟨e⟩ := hS
    haveI : (2 * m).AtLeastTwo := ⟨by omega⟩
    haveI : IsSimpleGroup (alternatingGroup (Fin (2 * m))) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    haveI : IsSimpleGroup S := e.isSimpleGroup
    have hScard : Nat.card S = (2 * m).factorial / 2 := by
      calc Nat.card S = Nat.card (alternatingGroup (Fin (2 * m))) := Nat.card_congr e.toEquiv
        _ = (Nat.card (Fin (2 * m))).factorial / 2 := nat_card_alternatingGroup
        _ = (2 * m).factorial / 2 := by rw [Nat.card_fin]
    have h2dvd : 2 ∣ Nat.card S := by
      rw [hScard, Nat.dvd_div_iff_mul_dvd (Nat.dvd_factorial (by norm_num) (by omega))]
      exact Nat.dvd_factorial (by norm_num) (by omega)
    have hgen := closure_setOf_isTwoPow_eq_top (A := S) h2dvd
    have hcle : Subgroup.closure {x : S | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ D.subgroupOf S := by
      rw [Subgroup.closure_le]
      rintro x hx
      change (x : A) ∈ D
      exact hD (x : A) x.2 (by
        obtain ⟨k, hk⟩ := hx
        exact ⟨k, by rw [Subgroup.orderOf_coe, hk]⟩)
    have hSD : S ≤ D := by
      have htop : D.subgroupOf S = ⊤ := top_le_iff.mp (hgen ▸ hcle)
      intro x hx
      have hmem : (⟨x, hx⟩ : S) ∈ D.subgroupOf S := by rw [htop]; trivial
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hcard : Nat.card A * 2 = (2 * m + 1).factorial := by
      have h2f : 2 ∣ (2 * m + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
      rw [hcardA, Nat.div_mul_cancel h2f]
    have hSindex : S.index = 2 * m + 1 := by
      have h := Subgroup.card_mul_index S
      have hkey : Nat.card A = Nat.card S * (2 * m + 1) := by
        rw [hcardA, hScard, Nat.factorial_succ (2 * m)]
        rw [Nat.mul_div_assoc _ (Nat.dvd_factorial (by norm_num) (by omega))]
        ring
      rw [hkey] at h
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
    rcases eq_or_eq_top_of_le_of_index_eq (n := 2 * m + 1) (by omega) hcard hSindex hSD with
      h | h
    · exact Or.inl (le_of_eq h)
    · exact Or.inr h

end CFSG.LocalAnalysis.WeakClosure81
