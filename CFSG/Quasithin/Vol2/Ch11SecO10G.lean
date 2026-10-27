module

public import CFSG.Quasithin.Vol2.Ch11SecO10F
public import CFSG.Quasithin.Vol2.Ch11SecO1B
public import CFSG.Quasithin.Vol2.Ch11SecA14Lines
public import CFSG.Quasithin.Vol2.Ch11SecE42S1d

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 Matrix
open scoped IsMulCommutative

theorem center_sl2_eq_bot_two {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  rw [hr1] at hA'
  have : (A : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [← hA']; simp
  exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using this))

theorem isSimpleGroup_sl2_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : 4 ≤ Nat.card F) : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := by
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) h
  have e : SpecialLinearGroup (Fin 2) F ≃*
      (SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :=
    ((QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot_two (F := F))).trans
      QuotientGroup.quotientBot).symm
  exact e.isSimpleGroup

variable {G : Type} [Group G] [Finite G]

theorem lOf_le_normalizer_or (h1110 : Stmt11_1_0) {T L I K I' : Subgroup G} {n : ℕ}
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hSK : SecD.NatSetting11 G T K I' n)
    (hk : KindSL3 K (fsuV T I') n ∨ KindSp4 K (fsuV T I') n) (hK : Hyp11 G T K I' n)
    {V'₁ V'₂ V'₃ : Subgroup G} (h₁ : IsVi T K I' n 1 V'₁) (h₂ : IsVi T K I' n 2 V'₂)
    (h₃ : IsVi T K I' n 3 V'₃) (hLK : LOf L V₁ ≤ K) :
    LOf L V₁ ≤ Subgroup.normalizer (V'₁ : Set G) ∨
      LOf L V₁ ≤ Subgroup.normalizer (V'₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := SecO1.isMulCommutative hSK
  have hn : 2 ≤ n := hSK.one_lt
  set V' := fsuV T I' with hV'
  set L₁ := LOf L V₁ with hL₁
  have hL₁V : L₁ ≤ Subgroup.normalizer (V' : Set G) := hLK.trans hSK.le_normalizer
  have hTL₁ : T ⊓ K ≤ Subgroup.normalizer (L₁ : Set G) := fun t ht =>
    SecD.mem_normalizer_lOf (h.normal ht.1) (SecA.IsVi.le_normalizer hV₁ ht.1)
  obtain ⟨F, _, _, hF, ⟨eL⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  have : CharP F 2 := KGNat.charP_two_of_card (by omega) hF
  have hBH : autOn L₁ V' ≤ autOn K V' := SecA.autOn_mono hLK
  have hPB := SecS.autOn_le_normalizer (V := V') hTL₁
  have hSL : pCoreOf 2 (autOn L₁ V') = ⊥ →
      Nonempty (↥(autOn L₁ V') ≃* SpecialLinearGroup (Fin 2) F) := by
    intro hO
    have hC2 : IsPGroup 2 ↥(L₁ ⊓ Subgroup.centralizer (V' : Set G)) :=
      (SecO1.isPGroup_inf_centralizer hSK).to_le (inf_le_inf_right _ hLK)
    have hOB := SecA.autOn_pCoreOf hL₁V hC2
    rw [hO] at hOB
    have hO2 : pCoreOf 2 L₁ ≤ Subgroup.centralizer (V' : Set G) := by
      intro x hx
      have hxV : x ∈ Subgroup.normalizer (V' : Set G) :=
        hL₁V ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁) hx)
      have h1 : SecA.conjV V' x hxV ∈ autOn (pCoreOf 2 L₁) V' := SecA.conjV_mem_autOn hx hxV
      rw [hOB, Subgroup.mem_bot] at h1
      exact SecD.mem_centralizer_of_conjV_eq_one hxV h1
    have hs : IsSimpleGroup (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := by
      have := isSimpleGroup_sl2_two (F := F) (by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
      exact eL.isSimpleGroup
    have hne : ¬ L₁ ≤ Subgroup.centralizer (V' : Set G) := by
      intro hle
      have h2 : IsPGroup 2 ↥L₁ := (SecO1.isPGroup_inf_centralizer hSK).to_le
        fun x hx => ⟨hLK hx, hle hx⟩
      have h3 : IsPGroup 2 (SpecialLinearGroup (Fin 2) F) :=
        (h2.to_quotient (CFSG.pCore 2 ↥L₁)).of_equiv eL
      obtain ⟨k, hk⟩ := h3.exists_card_eq
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF] at hk
      have hdvd : (2 ^ n) ^ 2 - 1 ∣ 2 ^ k := ⟨2 ^ n, by rw [← hk]; ring⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have h4 : 4 ≤ (2 ^ n) ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (le_self_pow₀ (by norm_num) (by omega)) 2
      obtain ⟨c, hc⟩ : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
      generalize (2 ^ n) ^ 2 = m at hj h4 hc
      rcases j with _ | j
      · rw [pow_zero] at hj
        omega
      · rw [pow_succ] at hj
        omega
    obtain ⟨e⟩ := SecE.nonempty_autOn_equiv hs hL₁V hO2 hne
    exact ⟨e.trans eL⟩
  have hNF : NatFactsW (autOn K V') (autOn (T ⊓ K) V') n := by
    rcases hk with hk | hk
    · obtain ⟨F₀, _, _, hF₀, π, hπ⟩ := SecO1.exists_realizes_sl3 hSK hk
      exact natFacts_sl3 hn hF₀ (SecO1.sq_eq_one hSK) hπ (SecO1.isSylowTwoOf_P hSK)
    · obtain ⟨F₀, _, _, hF₀, π, hπ⟩ := SecO1.exists_realizes_sp4 hSK hk
      exact natFacts_sp4 hn hF₀ (SecO1.sq_eq_one hSK) hπ (SecO1.isSylowTwoOf_P hSK)
  obtain ⟨d, hd, U, hUf, hUt, hBU⟩ :=
    levi_ident (SecO1.sq_eq_one hSK) hn hNF (SecO1.isSylowTwoOf_P hSK) hBH hPB hF hSL
  obtain ⟨U₁, U₂, U₃, -, -, -, -, -, hu₁, hu₂, hu₃⟩ := SecO1.hasUniqueFlag hSK
  have hstab : ∀ {W₀ : Subgroup G}, W₀ ≤ V' → U = W₀.subgroupOf V' →
      L₁ ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro W₀ hW₀ hUeq l hl
    have hmem := hBU (SecA.conjV_mem_autOn hl (hL₁V hl))
    rw [hUeq] at hmem
    exact (SecA.conjV_mem_stabW_iff hW₀ (hL₁V hl)).mp hmem
  rcases hd with rfl | rfl | rfl
  · exact Or.inl (hstab (SecA.IsVi.le_fsuV h₁)
      ((hu₁ U hUf).trans (hu₁ _ (SecO1.isFlagW_of_isVi hSK h₁)).symm))
  · exact Or.inr (hstab (SecA.IsVi.le_fsuV h₂)
      ((hu₂ U hUf).trans (hu₂ _ (SecO1.isFlagW_of_isVi hSK h₂)).symm))
  · have hU3 := (hu₃ U hUf).trans (hu₃ _ (SecO1.isFlagW_of_isVi hSK h₃)).symm
    have h33 := (h1110 G T K I' n hK).2.2 V'₁ V'₃ h₁ h₃
    rcases hk with hk | hk
    · exact absurd (by rw [hU3, h33.1 hk]; exact Subgroup.subgroupOf_self _) hUt
    · have hN3 := h33.2 fun h' => SecA.kind_not_SL3_Sp4 (by omega) h' hk
      have hL3 := hstab (SecA.IsVi.le_fsuV h₃) hU3
      refine Or.inl fun l hl => ?_
      have hmem : l ∈ Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (V'₃ : Set G) :=
        ⟨Subgroup.le_normalizer (hLK hl), hL3 hl⟩
      rw [hN3] at hmem
      exact hmem.2

end CFSG.Quasithin.Vol2.Ch11.O10
