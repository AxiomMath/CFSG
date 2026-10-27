module

public import CFSG.Quasithin.EmptyFaithful.S151bJ1
public import CFSG.Quasithin.EmptyFaithful.S152O4Iso
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.EmptyFaithful.S151b13Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

section Generic

variable {K : Type*} [Group K] [Finite K]

theorem card_ge_two_of_ne_bot151b {J : Subgroup K} (hJ : J ≠ ⊥) : 2 ≤ Nat.card J := by
  by_contra h
  push Not at h
  have hpos : 0 < Nat.card J := Nat.card_pos
  exact hJ (Subgroup.card_eq_one.mp (by omega))

theorem eq_of_ne_bot_of_card_le_two151b {J F : Subgroup K} (hJ : J ≠ ⊥) (hJF : J ≤ F)
    (hF : Nat.card F ≤ 2) : J = F :=
  Subgroup.eq_of_le_of_card_ge hJF (by have := card_ge_two_of_ne_bot151b hJ; omega)

theorem card_le_two_of_pGroup_dvd151b {F : Subgroup K} (hF : IsPGroup 2 F) {n : ℕ}
    (hdvd : Nat.card F ∣ n) (h4 : ¬ 4 ∣ n) : Nat.card F ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF
  by_contra hgt
  push Not at hgt
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : k ≤ 1 := by omega
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h4F : 4 ∣ Nat.card F := by
    rw [hk]
    have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
    simpa using this
  exact h4 (h4F.trans hdvd)

omit [Finite K] in
theorem card_sup_zpowers_dvd151b {P : Subgroup K} {t : K}
    (hPt : t ∈ Subgroup.normalizer (P : Set K)) (ht : t ^ 2 = 1) :
    Nat.card ↥(P ⊔ Subgroup.zpowers t) ∣ 2 * Nat.card P := by
  have hz : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set K) :=
    Subgroup.zpowers_le.mpr hPt
  have h1 : P.relIndex (Subgroup.zpowers t ⊔ P) = P.relIndex (Subgroup.zpowers t) :=
    A4.relIndex_sup_eq_of_le_normalizer' hz
  have h2 : P.relIndex (Subgroup.zpowers t ⊔ P) * Nat.card ↥(P ⊓ (Subgroup.zpowers t ⊔ P)) =
      Nat.card ↥(Subgroup.zpowers t ⊔ P) := Subgroup.relIndex_mul_card P _
  rw [inf_eq_left.mpr (le_sup_right : P ≤ Subgroup.zpowers t ⊔ P), h1] at h2
  have h3 : P.relIndex (Subgroup.zpowers t) * Nat.card ↥(P ⊓ Subgroup.zpowers t) =
      Nat.card (Subgroup.zpowers t) := Subgroup.relIndex_mul_card P _
  have h4 : Nat.card (Subgroup.zpowers t) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ht
  have h5 : P.relIndex (Subgroup.zpowers t) ∣ 2 :=
    (Dvd.intro _ h3).trans h4
  rw [sup_comm, ← h2]
  exact Nat.mul_dvd_mul_right h5 _

end Generic

section Core

theorem thompsonJi_le_of_sylow151b {T M : Subgroup G} (hT : IsSylowTwoOf T M) (i : ℕ) :
    thompsonJi T i ≤ thompsonJi M i := by
  refine iSup₂_le fun A hA => le_iSup₂_of_le A ⟨hA.1.trans hT.1, hA.2.1, ?_⟩ le_rfl
  rw [pRank_two_eq_of_sylow151b hT]
  exact hA.2.2

theorem autI_thompsonJi_eq_jhat151b {T M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hSyl : IsSylowTwoOf T M)
    (hJeq : autI hV (thompsonJi T 1) = autI hV T ⊓ Jhat (autI hV M)) :
    autI hV (thompsonJi M 1) = Jhat (autI hV M) := by
  have hSylb : IsSylowTwoOf (autI hV T) (autI hV M) := B2F.isSylowTwoOf_autI hV hMN hSyl
  apply le_antisymm
  · exact autI_thompsonJi_le151b hV hMN hSyl 1 (fun y hy z hz => mem_Jhat_conj hy hz)
      (hJeq ▸ inf_le_right)
  · exact jhat_le_of_inf_le151b hSylb hJeq.symm.le
      (autI_mono hV (thompsonJi_le_of_sylow151b hSyl 1))
      (normal_autI_thompsonJi151b hV 1)

theorem jeq_of_not_four_dvd151b {W : Type*} [CommGroup W] [Finite W]
    {J Tb X0 : Subgroup (MulAut W)} (hTb : IsPGroup 2 Tb) (hJne : J ≠ ⊥) (hJ : J ≤ Tb ⊓ X0)
    (h4 : ¬ 4 ∣ Nat.card X0) : J = Tb ⊓ X0 :=
  eq_of_ne_bot_of_card_le_two151b hJne hJ
    (card_le_two_of_pGroup_dvd151b (hTb.to_inf_left) (Subgroup.card_dvd_of_le inf_le_right) h4)

theorem not_four_dvd_sup_oTwoUpper151b {W : Type*} [CommGroup W] [Finite W]
    {X A₀ : Subgroup (MulAut W)} {t : MulAut W} (hA₀ : A₀ = oTwoUpper X ⊔ Subgroup.zpowers t)
    (hA₀X : A₀ ≤ X) (ht : t ^ 2 = 1) {n : ℕ} (hn : Nat.card (oTwoUpper X) = n) (hodd : ¬ 2 ∣ n) :
    ¬ 4 ∣ Nat.card A₀ := by
  have htX : t ∈ X := hA₀X (hA₀ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have htN : t ∈ Subgroup.normalizer (oTwoUpper X : Set (MulAut W)) :=
    le_normalizer_oTwoUpper X htX
  have hdvd := card_sup_zpowers_dvd151b htN ht
  rw [← hA₀, hn] at hdvd
  intro h4
  have := h4.trans hdvd
  omega

theorem card_eq_36_of_isOmegaFourPlus151b {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (hX : IsOmegaFourPlus X) : Nat.card X = 36 := by
  obtain ⟨c, hc⟩ := S152O4.om4_model hX
  have hR36 : Nat.card (S152O4.rhoV c).range = 36 := by
    rw [← S152O4.card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (S152O4.rhoV_injective c)).toEquiv).symm
  rw [← hc]
  exact hR36

theorem four_of_cases151b {T M V : Subgroup G} {A₀ : Subgroup (MulAut ↥V)}
    (hV : IsElemAbelian 2 V) (hTM : T ≤ M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hSyl : IsSylowTwoOf T M) (hA0 : A₀ = Jhat (autI hV M))
    (hJne : autI hV (thompsonJi T 1) ≠ ⊥) (hcases : Lemma1517Cases T M V A₀)
    (h3 : (∀ A : Subgroup G, IsElemAbelianCorank T 1 A → autOn A V ≠ ⊥ →
        Nat.card (autOn A V) = 2 ∧ autOn A V ∈ QhatStarOn M V) ∨ Case1517Three M V A₀)
    (h6 : ∀ p : ℕ, (p = 3 ∨ p = 5) → ¬ Case1517Three M V A₀ → Case1517Six T M V A₀ p →
      (∀ A : Subgroup G, IsElemAbelianCorank T 1 A → autOn A V ≠ ⊥ →
        Nat.card (autOn A V) = 2 ∧ autOn A V ∈ QhatStarOn M V) →
      autI hV (thompsonJi T 1) ≤ autI hV T ⊓ Jhat (autI hV M) →
      autI hV (thompsonJi T 1) = autI hV T ⊓ Jhat (autI hV M)) :
    (autOn (thompsonJi T 1) V = autOn T V ⊓ A₀ ∧ autOn (thompsonJi M 1) V = A₀) ∨
      (Case1517Three M V A₀ ∧ Nat.card (autOn (thompsonJi T 1) V) = 2) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hSylb : IsSylowTwoOf (autI hV T) (autI hV M) := B2F.isSylowTwoOf_autI hV hMN hSyl
  have hTbp : IsPGroup 2 (autI hV T) := hSylb.2.1
  have hJT : autI hV (thompsonJi T 1) ≤ autI hV T :=
    autI_mono hV (iSup₂_le fun _ hA => hA.1)
  have hA₀X : A₀ ≤ autI hV M := hA0 ▸ Jhat_le (autI hV M)
  have key : autI hV (thompsonJi T 1) = autI hV T ⊓ Jhat (autI hV M) →
      (autOn (thompsonJi T 1) V = autOn T V ⊓ A₀ ∧ autOn (thompsonJi M 1) V = A₀) := by
    intro hJeq
    refine ⟨?_, ?_⟩
    · rw [hA0]
      exact hJeq
    · rw [hA0]
      exact autI_thompsonJi_eq_jhat151b hV hMN hSyl hJeq
  by_cases hc3 : Case1517Three M V A₀
  ·
    obtain ⟨hcardV, hMA, hΩ⟩ := hc3
    obtain ⟨hV', hOm⟩ := hΩ
    have hX36 : Nat.card (autI hV M) = 36 := card_eq_36_of_isOmegaFourPlus151b hOm
    have hTb4 : Nat.card (autI hV T) ≤ 4 := by
      have hdvd : Nat.card (autI hV T) ∣ 36 := hX36 ▸ Subgroup.card_dvd_of_le hSylb.1
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTbp
      rw [hk] at hdvd ⊢
      have hk2 : k ≤ 2 := by
        by_contra hgt
        have h1 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
        have := h1.trans hdvd
        omega
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    have hJp : IsPGroup 2 (autI hV (thompsonJi T 1)) := hTbp.to_le hJT
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hJp
    have hJ2 := card_ge_two_of_ne_bot151b hJne
    have hJle := Subgroup.card_le_of_le hJT
    by_cases hJ2' : Nat.card (autI hV (thompsonJi T 1)) = 2
    · exact Or.inr ⟨⟨hcardV, hMA, ⟨hV', hOm⟩⟩, hJ2'⟩
    · refine Or.inl (key ?_)
      have hJ4 : Nat.card (autI hV (thompsonJi T 1)) = 4 := by
        rw [hk] at hJ2 hJle hJ2' ⊢
        have hk2 : k ≤ 2 := by
          by_contra hgt
          have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        obtain h0 | h1 | h2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        · rw [h0] at hJ2; omega
        · rw [h1] at hJ2'; omega
        · rw [h2]; norm_num
      have hJeq : autI hV (thompsonJi T 1) = autI hV T :=
        Subgroup.eq_of_le_of_card_ge hJT (by omega)
      rw [hJeq]
      refine (inf_eq_left.mpr ?_).symm
      intro x hx
      have : x ∈ autI hV M := hSylb.1 hx
      rw [← hA0] at *
      exact hMA ▸ this
  · have h3' := h3.resolve_right hc3
    have hJle : autI hV (thompsonJi T 1) ≤ Jhat (autI hV M) := by
      rw [autI_thompsonJi_eq_iSup151b hV hTN 1]
      refine iSup_le fun A => iSup_le fun hA => ?_
      by_cases hbot : autI hV A = ⊥
      · rw [hbot]
        exact bot_le
      · have hmem := (mem_QhatStarOn_iff151b hV _).mp (h3' A hA hbot).2
        exact le_iSup₂_of_le (autI hV A) hmem le_rfl
    have hJ' : autI hV (thompsonJi T 1) ≤ autI hV T ⊓ Jhat (autI hV M) := le_inf hJT hJle
    refine Or.inl (key ?_)
    have h4 : ¬ 4 ∣ Nat.card A₀ → autI hV (thompsonJi T 1) = autI hV T ⊓ Jhat (autI hV M) := by
      intro h4
      refine jeq_of_not_four_dvd151b hTbp hJne hJ' ?_
      rw [← hA0]
      exact h4
    rcases hcases with c1 | c2 | c3 | c4 | c5 | ⟨p, hp, c6⟩ | c7
    · obtain ⟨-, -, ⟨e⟩⟩ := c1
      refine h4 ?_
      have : Nat.card A₀ = 6 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · obtain ⟨-, ⟨e⟩, -⟩ := c2
      refine h4 ?_
      have : Nat.card A₀ = 6 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · exact absurd c3 hc3
    · obtain ⟨-, ⟨hel, hn9, t, ht2, -, hAt⟩, -⟩ := c4
      exact h4 (not_four_dvd_sup_oTwoUpper151b (X := autI hV M) hAt hA₀X
        (by rw [← ht2]; exact pow_orderOf_eq_one t) hn9 (by norm_num))
    · obtain ⟨-, ⟨e⟩, -⟩ := c5
      refine h4 ?_
      have : Nat.card A₀ = 10 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · exact h6 p hp hc3 c6 h3' hJ'
    · obtain ⟨-, ⟨⟨-, hn27, -⟩, ⟨t, ht2, -, hAt⟩, -⟩⟩ := c7
      exact h4 (not_four_dvd_sup_oTwoUpper151b (X := autI hV M) hAt hA₀X
        (by rw [← ht2]; exact pow_orderOf_eq_one t) (n := 27)
        (by rw [show (27 : ℕ) = 3 ^ 3 by norm_num]; exact hn27) (by norm_num))

end Core

end CFSG.Quasithin
