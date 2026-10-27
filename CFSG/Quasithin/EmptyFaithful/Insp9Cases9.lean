module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases6
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped commutatorElement

namespace Insp9

section Small

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

omit [Finite D] in
theorem Data.le_or_card_dvd_six (h : Data D₁ D₂ J N) {K : Subgroup D} [K.Normal]
    (hKq : CFSG.IsQuasisimple ↥K) (hidx : K.index ∣ 2)
    (hZ : Nat.card ↥(Subgroup.center ↥K) ∣ 3) : K ≤ N ∨ Nat.card ↥N ∣ 6 := by
  have hN := h.normal
  rcases qs_normal_le_center_or_top hKq (N.subgroupOf K) with hc | htop
  · right
    let g : ↥(K ⊓ N) →* ↥(Subgroup.center ↥K) :=
      (Subgroup.inclusion (inf_le_left : K ⊓ N ≤ K)).codRestrict (Subgroup.center ↥K) (by
        intro x
        exact hc (show (Subgroup.inclusion (inf_le_left : K ⊓ N ≤ K) x) ∈ N.subgroupOf K from
          x.2.2))
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subgroup.inclusion_injective (inf_le_left : K ⊓ N ≤ K)
      exact congrArg Subtype.val hxy
    have h3 : Nat.card ↥(K ⊓ N) ∣ 3 := (Subgroup.card_dvd_of_injective g hg).trans hZ
    have h2 : K.relIndex N ∣ 2 := (Subgroup.relIndex_dvd_index_of_normal K N).trans hidx
    have hmul := Subgroup.relIndex_mul_card (H := K) (K := N)
    rw [← hmul]
    have : (2 : ℕ) * 3 = 6 := rfl
    exact this ▸ Nat.mul_dvd_mul h2 h3
  · left
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := by rw [htop]; trivial
    exact this

end Small

theorem B56Setting.s3_of_small {D : Type} [Group D] [Finite D] {N : Subgroup D}
    (hs : B56Setting D N) (h4 : ¬ 4 ∣ Nat.card ↥N) (hpf : (Nat.card ↥N).primeFactors.card < 3) :
    Nonempty (↥N ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨W, _, _, _, ρ, hρ, -, hcases⟩ := hs
  have hcardN : Nat.card ↥(N.map ρ) = Nat.card ↥N := Subgroup.card_map_of_injective hρ
  rcases hcases with h1 | h2 | h3 | h4' | h5
  · exfalso
    rcases b56_four_dvd_or_three_primes (Or.inl h1) with h | h
    · rw [hcardN] at h; exact h4 h
    · rw [hcardN] at h; omega
  · obtain ⟨e⟩ := h2.1
    exact ⟨(Subgroup.equivMapOfInjective N ρ hρ).trans e⟩
  all_goals
    exfalso
    rcases b56_four_dvd_or_three_primes (by tauto) with h | h
    · rw [hcardN] at h; exact h4 h
    · rw [hcardN] at h; omega

theorem card_small_of_dvd_six {n : ℕ} (h : n ∣ 6) :
    ¬ 4 ∣ n ∧ n.primeFactors.card < 3 := by
  refine ⟨fun h4 => by have := h4.trans h; omega, ?_⟩
  have hsub : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hp6 : p ∣ 2 * 3 := hp'.2.1.trans h
    rcases (Nat.Prime.dvd_mul hp'.1).mp hp6 with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp'.1 Nat.prime_two).mp h2
      simp [this]
    · have := (Nat.prime_dvd_prime_iff_eq hp'.1 Nat.prime_three).mp h3
      simp [this]
  exact lt_of_le_of_lt (Finset.card_le_card hsub) (by decide)

theorem B56Setting.normal_quasisimple_cases {D : Type} [Group D] [Finite D] {N K : Subgroup D}
    (hs : B56Setting D N) (hKN : K ≤ N) (hKn : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hKq : CFSG.IsQuasisimple ↥K) (h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N) :
    Nat.card ↥K ∣ 12096 ∨ Nat.card ↥K ∈ omegaQL ∨ (∃ c ∈ flOrders, Nat.card ↥K ∣ c) ∨
      Nat.card ↥K ∣ 360 ∨ Nat.card ↥K ∣ 168 ∨
      ∃ c : ℕ, Nat.card ↥K ∣ c ∧ 168 * c ∣ Nat.card ↥N := by
  obtain ⟨W, _, _, _, ρ, hρ, -, hcases⟩ := hs
  have eK : ↥K ≃* ↥(K.map ρ) := Subgroup.equivMapOfInjective K ρ hρ
  have hKJ : K.map ρ ≤ N.map ρ := Subgroup.map_mono hKN
  have hn : ∀ x ∈ N.map ρ, ∀ k ∈ K.map ρ, x * k * x⁻¹ ∈ K.map ρ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨x * k * x⁻¹, hKn x hx k hk, by simp⟩
  have hq' : CFSG.IsQuasisimple ↥(K.map ρ) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
  have hcK : Nat.card ↥(K.map ρ) = Nat.card ↥K := Subgroup.card_map_of_injective hρ
  have hcN : Nat.card ↥(N.map ρ) = Nat.card ↥N := Subgroup.card_map_of_injective hρ
  have h8' : ¬ 2 ^ 8 ∣ Nat.card ↥(N.map ρ) := by rw [hcN]; exact h8
  have hle8 : ∀ {X : Subgroup (MulAut W)}, X ≤ N.map ρ → ¬ 2 ^ 8 ∣ Nat.card ↥X :=
    fun hX hd => h8' (hd.trans (Subgroup.card_dvd_of_le hX))
  rw [← hcK]
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, -⟩
  ·
    have hE : quasithinGenFitting (N.map ρ) = K.map ρ := eq_of_le_quasisimple hKJ hn hq' h1.1
    have hQL := h1.2.2
    rw [hE] at hQL
    have hfinK : Finite ↥(K.map ρ) := Finite.of_equiv _ eK.toEquiv
    rcases b56QL_card_le7 hQL (hle8 hKJ) with hd | hm
    · exact Or.inl hd
    · exact Or.inr (Or.inl hm)
  · exact (not_le_perm_three hq' hKJ e).elim
  ·
    have h₁J : G₁ ≤ N.map ρ := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ N.map ρ := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hq' with h | h
    · have hfin₁ : Finite ↥G₁ := Finite.of_injective (Subgroup.inclusion h₁J)
        (Subgroup.inclusion_injective h₁J)
      exact Or.inr (Or.inr (Or.inl ⟨_, b56FL_card_le7 hf₁ (hle8 h₁J),
        Subgroup.card_dvd_of_le h⟩))
    · have hfin₂ : Finite ↥G₂ := Finite.of_injective (Subgroup.inclusion h₂J)
        (Subgroup.inclusion_injective h₂J)
      exact Or.inr (Or.inr (Or.inl ⟨_, b56FL_card_le7 hf₂ (hle8 h₂J),
        Subgroup.card_dvd_of_le h⟩))
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hq' with h | h
    · have hG1 : Nat.card ↥G₁ = 360 := by
        rw [Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
        simp [Nat.factorial]
      exact Or.inr (Or.inr (Or.inr (Or.inl ((Subgroup.card_dvd_of_le h).trans hG1.dvd))))
    · exact (not_le_of_card_prime hq' h hc₂).elim
  ·
    have hG1 : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hq' with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Subgroup.card_dvd_of_le h).trans hG1.dvd)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.card ↥G₂,
        Subgroup.card_dvd_of_le h, ?_⟩))))
      have hprod := card_sup_eq_mul hc hinf
      rw [hsup, hG1] at hprod
      rw [← hcN, hprod]

section Case9

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem case9_s7 (h : Data D₁ D₂ J N) (hs : B56Setting D N) (e : D ≃* Equiv.Perm (Fin 7)) :
    InspGoal D N := by
  have hA : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let K : Subgroup D := (alternatingGroup (Fin 7)).map e.symm.toMonoidHom
  have hKn : K.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  let eK : ↥(alternatingGroup (Fin 7)) ≃* ↥K :=
    Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective
  have hsK : IsSimpleGroup ↥K := eK.symm.isSimpleGroup
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥K := ⟨⟨fun a b => hcomm a b⟩⟩
    have hq : (Nat.card ↥K).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr eK.symm.toEquiv, card_alternatingGroup1527d 7 (by norm_num)] at hq
    norm_num [Nat.factorial] at hq
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hZ : Nat.card ↥(Subgroup.center ↥K) ∣ 3 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc, Subgroup.card_bot]
    exact one_dvd _
  have hK2 : K.index = 2 := by
    rw [Subgroup.index_map_of_bijective e.symm.bijective, alternatingGroup.index_eq_two]
  rcases h.le_or_card_dvd_six hKq hK2.dvd hZ with hKN | hsmall
  · have hrel : K.relIndex N * N.index = K.index := Subgroup.relIndex_mul_index hKN
    have hN1 : N.index ∣ 2 := ⟨K.relIndex N, by rw [← hK2, ← hrel]; ring⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hN1 with h1 | h2
    · have hN : N = ⊤ := Subgroup.index_eq_one.mp h1
      right
      refine ⟨?_, by rw [hN]; exact le_top⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(topEquivOfEq hN).trans e⟩))))
    · have hrel1 : K.relIndex N = 1 := by rw [h2, hK2] at hrel; omega
      have hNK : N ≤ K := Subgroup.relIndex_eq_one.mp hrel1
      have hNKeq : N = K := le_antisymm hNK hKN
      right
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hNKeq).trans eK.symm⟩))), ?_⟩
      rw [hNKeq]
      refine oTwoUpper_le_of_pow_mem (fun x _ => ⟨1, ?_⟩)
      have := Subgroup.pow_index_mem K x
      rw [hK2] at this
      simpa using this
  · left
    exact hs.s3_of_small (card_small_of_dvd_six hsmall).1 (card_small_of_dvd_six hsmall).2

theorem case9_hat7 (h : Data D₁ D₂ J N) (hs : B56Setting D N) (hH : F6.IsHatSym 7 D)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 4) : InspGoal D N := by
  obtain ⟨φ, hφ, -, hQ⟩ := hH
  set K : Subgroup D := (alternatingGroup (Fin 7)).comap φ with hKdef
  have hKn : K.Normal := inferInstance
  have hKq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_open hQ.1
  have hZ : Nat.card ↥(Subgroup.center ↥K) ∣ 3 := by rw [hQ.2.1]
  have hK2 : K.index = 2 := by
    rw [hKdef, Subgroup.index_comap_of_surjective _ hφ, alternatingGroup.index_eq_two]
  rcases h.le_or_card_dvd_six hKq hK2.dvd hZ with hKN | hsmall
  · exfalso
    have hKcard : Nat.card ↥K = 7560 := by
      rw [card_hatAlt hQ (by norm_num)]
      simp [Nat.factorial]
    have h5 : ¬ 2 ^ 5 ∣ Nat.card D := h.not_two_pow_dvd hT (m := 5) (by norm_num)
    have h5N : ¬ 2 ^ 5 ∣ Nat.card ↥N := fun hd =>
      h5 (hd.trans (Subgroup.card_subgroup_dvd_card N))
    have h8N : ¬ 2 ^ 8 ∣ Nat.card ↥N := fun hd =>
      h5N ((Nat.pow_dvd_pow 2 (by norm_num : 5 ≤ 8)).trans hd)
    have hKn' : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x _ k hk => hKn.conj_mem k hk x
    have keyFL : ∀ c ∈ flOrders, 7560 ∣ c → False := by
      unfold flOrders; decide +kernel
    have keyQL : Nat.card ↥K ∈ omegaQL → False := by
      rw [hKcard]; unfold omegaQL; decide +kernel
    rcases hs.normal_quasisimple_cases hKN hKn' hKq h8N with hd | hm | ⟨c, hc, hdc⟩ | hd | hd |
        ⟨c, hdc, hcN⟩
    · rw [hKcard] at hd; omega
    · exact keyQL hm
    · rw [hKcard] at hdc; exact keyFL c hc hdc
    · rw [hKcard] at hd; omega
    · rw [hKcard] at hd; omega
    · rw [hKcard] at hdc
      have h1 : 168 * 7560 ∣ 168 * c := Nat.mul_dvd_mul_left 168 hdc
      exact h5N ((show 2 ^ 5 ∣ 168 * 7560 by norm_num).trans (h1.trans hcN))
  · left
    exact hs.s3_of_small (card_small_of_dvd_six hsmall).1 (card_small_of_dvd_six hsmall).2

end Case9

end Insp9

end CFSG.Quasithin
