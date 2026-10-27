module

public import CFSG.Quasithin.EmptyFaithful.Insp9Top
public import CFSG.Quasithin.EmptyFaithful.Insp9Psl
public import CFSG.Quasithin.EmptyFaithful.Insp9P7
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped commutatorElement

namespace Insp9

@[expose] def flOrders : Finset ℕ := {6, 60, 504, 4080, 32736, 262080, 2097024, 120, 168}

theorem b56FL_card_le7 {X : Type} [Group X] [Finite X] (h : B56FactorList X)
    (h8 : ¬ 2 ^ 8 ∣ Nat.card X) : Nat.card X ∈ flOrders := by
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases h with ⟨n, K, _, _, hn1, hK, ⟨e⟩⟩ | he | ⟨m, K, _, _, hm1, hmodd, hK, ⟨e⟩⟩
  · have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    have hn : n ≤ 7 := by
      by_contra hn
      exact h8 (by rw [hX]; exact (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [flOrders] at hX hpos ⊢ <;> omega
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    simp [flOrders, Nat.factorial]
  · have hX : Nat.card X = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    have hm : m ≤ 2 := by
      by_contra hm
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ m * 3)).trans (Dvd.intro _ rfl))
    obtain ⟨k, rfl⟩ := hmodd
    have hk : k = 0 := by omega
    subst hk
    simp [flOrders] at hX ⊢
    omega

theorem B56Setting.false_of_normal_quasisimple {D : Type} [Group D] [Finite D] {N K : Subgroup D}
    (hs : B56Setting D N) (hKN : K ≤ N) (hKn : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hKq : CFSG.IsQuasisimple ↥K) (h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N)
    (h6 : 2 ^ 6 ∣ Nat.card ↥K) (h11 : 11 ∣ Nat.card ↥K) : False := by
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
  have h6' : 2 ^ 6 ∣ Nat.card ↥(K.map ρ) := by rw [hcK]; exact h6
  have h11' : 11 ∣ Nat.card ↥(K.map ρ) := by rw [hcK]; exact h11
  have hle8 : ∀ {X : Subgroup (MulAut W)}, X ≤ N.map ρ → ¬ 2 ^ 8 ∣ Nat.card ↥X :=
    fun hX hd => h8' (hd.trans (Subgroup.card_dvd_of_le hX))
  have keyQL : ∀ c ∈ omegaQL, 2 ^ 6 ∣ c → 11 ∣ c → False := by
    unfold omegaQL; decide +kernel
  have keyFL : ∀ c ∈ flOrders, 2 ^ 6 ∣ c → 11 ∣ c → False := by
    unfold flOrders; decide +kernel
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, -⟩
  ·
    have hE : quasithinGenFitting (N.map ρ) = K.map ρ := eq_of_le_quasisimple hKJ hn hq' h1.1
    have hQL := h1.2.2
    rw [hE] at hQL
    have hfinK : Finite ↥(K.map ρ) := Finite.of_equiv _ eK.toEquiv
    rcases b56QL_card_le7 hQL (hle8 hKJ) with hd | hm
    · have := h11'.trans hd
      omega
    · exact keyQL _ hm h6' h11'
  ·
    exact not_le_perm_three hq' hKJ e
  ·
    have h₁J : G₁ ≤ N.map ρ := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ N.map ρ := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hq' with h | h
    · have hfin₁ : Finite ↥G₁ := Finite.of_injective (Subgroup.inclusion h₁J)
        (Subgroup.inclusion_injective h₁J)
      exact keyFL _ (b56FL_card_le7 hf₁ (hle8 h₁J)) (h6'.trans (Subgroup.card_dvd_of_le h))
        (h11'.trans (Subgroup.card_dvd_of_le h))
    · have hfin₂ : Finite ↥G₂ := Finite.of_injective (Subgroup.inclusion h₂J)
        (Subgroup.inclusion_injective h₂J)
      exact keyFL _ (b56FL_card_le7 hf₂ (hle8 h₂J)) (h6'.trans (Subgroup.card_dvd_of_le h))
        (h11'.trans (Subgroup.card_dvd_of_le h))
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hq' with h | h
    · have hG1 : Nat.card ↥G₁ = 360 := by
        rw [Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
        simp [Nat.factorial]
      have := h11'.trans ((Subgroup.card_dvd_of_le h).trans hG1.dvd)
      omega
    · exact not_le_of_card_prime hq' h hc₂
  ·
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hq' with h | h
    · have hG1 : Nat.card ↥G₁ = 168 := by
        rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
        norm_num
      have := h11'.trans ((Subgroup.card_dvd_of_le h).trans hG1.dvd)
      omega
    · have hG1 : Nat.card ↥G₁ = 168 := by
        rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
        norm_num
      have hprod := card_sup_eq_mul hc hinf
      rw [hsup, hG1] at hprod
      have h2 : 2 ^ 6 ∣ Nat.card ↥G₂ := h6'.trans (Subgroup.card_dvd_of_le h)
      have h9 : 2 ^ 3 * 2 ^ 6 ∣ 168 * Nat.card ↥G₂ := Nat.mul_dvd_mul (by norm_num) h2
      rw [← hprod] at h9
      exact h8' ((Nat.pow_dvd_pow 2 (by norm_num : 8 ≤ 3 + 6)).trans (by simpa [pow_add] using h9))

section AutSimple

variable {M : Type} [Group M]

theorem conj_injective_of_center_eq_bot (hM : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : a * g * a⁻¹ = g := by
      simpa [MulAut.conj_apply] using congrArg (fun σ : MulAut M => σ g) ha
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hM] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem mulAut_mul_conj_mul_inv (σ : MulAut M) (m : M) :
    σ * MulAut.conj m * σ⁻¹ = MulAut.conj (σ m) := by
  ext x
  simp [MulAut.conj_apply]

end AutSimple

section Case13

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem case13_core {M : Type} [Group M] [Finite M] [IsSimpleGroup M]
    (hnc : ∃ a b : M, a * b ≠ b * a) (hcard : Nat.card M = 95040)
    (h : Data D₁ D₂ J N) (hs : B56Setting D N) (e : D ≃* MulAut M)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 7) : False := by
  have hN := h.normal
  have hZ : Subgroup.center M = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc
  have hinj := conj_injective_of_center_eq_bot hZ
  let Kb : Subgroup (MulAut M) := (MulAut.conj : M →* MulAut M).range
  let K : Subgroup D := Kb.map e.symm.toMonoidHom
  have hmemK : ∀ x : D, x ∈ K ↔ ∃ m : M, MulAut.conj m = e x := by
    intro x
    rw [Subgroup.mem_map_equiv]
    simp [Kb, MonoidHom.mem_range]
  have hKnormal : K.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm⟩ := (hmemK x).mp hx
    refine (hmemK _).mpr ⟨e g m, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hm, mulAut_mul_conj_mul_inv]
  let eKM : ↥K ≃* M :=
    (Subgroup.equivMapOfInjective Kb e.symm.toMonoidHom e.symm.injective).symm.trans
      (MonoidHom.ofInjective hinj).symm
  have : IsSimpleGroup ↥K := eKM.isSimpleGroup
  have hqM : CFSG.IsQuasisimple M := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hqK : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv eKM.symm hqM
  have hcardK : Nat.card ↥K = 95040 := by rw [Nat.card_congr eKM.toEquiv, hcard]
  have hKN : K ≤ N := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with hbot | htop
    · exfalso
      have hNK : ∀ x ∈ N, x ∈ K → x = 1 := by
        intro x hxN hxK
        have : (⟨x, hxK⟩ : ↥K) ∈ N.subgroupOf K := hxN
        rw [hbot, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      apply h.N_ne_bot
      rw [eq_bot_iff]
      intro n hn
      rw [Subgroup.mem_bot]
      have hcomm : ∀ m : M, e n * MulAut.conj m = MulAut.conj m * e n := by
        intro m
        have hk : e.symm (MulAut.conj m) ∈ K := (hmemK _).mpr ⟨m, by simp⟩
        have hc : ⁅n, e.symm (MulAut.conj m)⁆ = 1 := by
          refine hNK _ ?_ ?_
          · rw [commutatorElement_def]
            have h1 : e.symm (MulAut.conj m) * n⁻¹ * (e.symm (MulAut.conj m))⁻¹ ∈ N :=
              hN.conj_mem n⁻¹ (N.inv_mem hn) _
            have h2 : n * e.symm (MulAut.conj m) * n⁻¹ * (e.symm (MulAut.conj m))⁻¹ =
                n * (e.symm (MulAut.conj m) * n⁻¹ * (e.symm (MulAut.conj m))⁻¹) := by group
            rw [h2]
            exact N.mul_mem hn h1
          · rw [commutatorElement_def]
            exact K.mul_mem (hKnormal.conj_mem _ hk n) (K.inv_mem hk)
        have hnk : n * e.symm (MulAut.conj m) = e.symm (MulAut.conj m) * n :=
          commutatorElement_eq_one_iff_mul_comm.mp hc
        have h2 := congrArg e hnk
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
        exact h2
      have hσ : e n = 1 := by
        ext m
        have h3 : MulAut.conj (e n m) = MulAut.conj m := by
          rw [← mulAut_mul_conj_mul_inv, hcomm m, mul_assoc, mul_inv_cancel, mul_one]
        exact hinj h3
      exact e.injective (by rw [hσ, map_one])
    · intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := by rw [htop]; trivial
      exact this
  have hKn' : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x _ k hk => hKnormal.conj_mem k hk x
  have h8D : ¬ 2 ^ 8 ∣ Nat.card D := h.not_two_pow_dvd hT (m := 8) (by norm_num)
  have h8N : ¬ 2 ^ 8 ∣ Nat.card ↥N := fun hd => h8D (hd.trans (Subgroup.card_subgroup_dvd_card N))
  exact hs.false_of_normal_quasisimple hKN hKn' hqK h8N (by rw [hcardK]; norm_num)
    (by rw [hcardK]; norm_num)

theorem inspCase13 :
    InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseThirteen H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  exfalso
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseThirteen H₁ H₂ → False := by
    intro H₁ H₂ hHH hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 7 := by rw [← hHH, hc.card_inf]; norm_num
    obtain ⟨⟨e⟩, -⟩ := hc
    have : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M12 :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    have hnc : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M12, a * b ≠ b * a := by
      by_contra hcomm
      push Not at hcomm
      have : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M12 := ⟨⟨fun a b => hcomm a b⟩⟩
      have hq : (Nat.card ↥CFSG.Blueprint.NativeSporadic.M12).Prime := IsSimpleGroup.prime_card
      rw [CFSG.Sporadic.Mathieu.card_M12] at hq
      norm_num at hq
    exact case13_core hnc CFSG.Sporadic.Mathieu.card_M12 h hs e hT
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Case13

end Insp9

end CFSG.Quasithin
