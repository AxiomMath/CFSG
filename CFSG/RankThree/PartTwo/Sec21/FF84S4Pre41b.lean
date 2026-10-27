module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre41a
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreJ
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreFr

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem J₁_sylow (h : FF84Sec4 b L B K b₁ b₂) {D₀ J₁ J₂ : Subgroup G} (hJ₁ : J₁ ≤ D₀)
    (hn₁ : ∀ g ∈ D₀, ∀ x ∈ J₁, g * x * g⁻¹ ∈ J₁) (hP₁J₁ : Subgroup.zpowers (b * b₁ ^ 2) ≤ J₁)
    (hP₂J₂ : Subgroup.zpowers b₂ ≤ J₂) (hJO : J₁ ⊓ J₂ ≤ Opp 3 D₀)
    (hsyl : IsSylowOf 3 (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) D₀) :
    IsSylowOf 3 (Subgroup.zpowers (b * b₁ ^ 2)) J₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) with hU
  set P₁ := Subgroup.zpowers (b * b₁ ^ 2) with hP₁
  have hsup : P₁ ⊔ Subgroup.zpowers b₂ = U := zpowers_sup_eq _ _
  have hP₁U : P₁ ≤ U := hsup ▸ le_sup_left
  have hP₂U : Subgroup.zpowers b₂ ≤ U := hsup ▸ le_sup_right
  have hS := FF79.L14.isSylowOf_inf_normal hsyl hJ₁ hn₁
  have hP₁c : Nat.card P₁ = 3 := by rw [hP₁, Nat.card_zpowers, orderOf_bb₁sq h]
  have hle : P₁ ≤ U ⊓ J₁ := le_inf hP₁U hP₁J₁
  have hd9 : Nat.card ↥(U ⊓ J₁) ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : U ⊓ J₁ ≤ U)
    rwa [card_U h, show (9 : ℕ) = 3 ^ 2 by norm_num] at this
  have hd3 : 3 ∣ Nat.card ↥(U ⊓ J₁) := hP₁c ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd9
  have heq : U ⊓ J₁ = P₁ := by
    interval_cases k
    · rw [hk] at hd3; norm_num at hd3
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hP₁c, hk]; norm_num)).symm
    · exfalso
      have hUJ : U ≤ J₁ := by
        have : U ⊓ J₁ = U :=
          Subgroup.eq_of_le_of_card_ge (inf_le_left : U ⊓ J₁ ≤ U) (by rw [card_U h, hk]; norm_num)
        exact this ▸ inf_le_right
      have hb₂O : b₂ ∈ Opp 3 D₀ :=
        hJO ⟨hUJ (hP₂U (Subgroup.mem_zpowers b₂)), hP₂J₂ (Subgroup.mem_zpowers b₂)⟩
      have hdvd : orderOf b₂ ∣ Nat.card (Opp 3 D₀) :=
        Subgroup.orderOf_dvd_natCard (Opp 3 D₀) hb₂O
      rw [orderOf_b₂ h] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_Opp 3 D₀) hdvd) (by norm_num)
  rw [heq] at hS
  exact hS

theorem D₀_decomp (h : FF84Sec4 b L B K b₁ b₂) (hA : A8Model L)
    {D₀ J₁ J₂ : Subgroup G} (hDD : D₀ ≤ Cen (b * b₁)) (hJ₁ : J₁ ≤ D₀) (hJ₂ : J₂ ≤ D₀)
    (hn₁ : ∀ g ∈ D₀, ∀ x ∈ J₁, g * x * g⁻¹ ∈ J₁) (hn₂ : ∀ g ∈ D₀, ∀ x ∈ J₂, g * x * g⁻¹ ∈ J₂)
    (hP₁J₁ : Subgroup.zpowers (b * b₁ ^ 2) ≤ J₁) (hP₂J₂ : Subgroup.zpowers b₂ ≤ J₂)
    (hJO : J₁ ⊓ J₂ ≤ Opp 3 D₀)
    (hsyl : IsSylowOf 3 (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) D₀) :
    ∀ x ∈ D₀, ∃ o ∈ Opp 3 D₀, ∃ n ∈ D₀ ⊓ Nor (Subgroup.zpowers (b * b₁ ^ 2)), x = o * n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSyl := J₁_sylow h hJ₁ hn₁ hP₁J₁ hP₂J₂ hJO hsyl
  have hcard : Nat.card (Subgroup.zpowers (b * b₁ ^ 2)) = 3 := by
    rw [Nat.card_zpowers, orderOf_bb₁sq h]
  have hps := J₁_psolv h hA hDD hJ₁ hJ₂ hn₁ hn₂ hP₂J₂ hJO
  intro x hx
  obtain ⟨m, hm, n, hn, rfl⟩ := frattini_G hJ₁ hn₁ hSyl x hx
  obtain ⟨o, ho, n', hn', rfl⟩ := three_solv_decomp hps hSyl hcard m hm
  refine ⟨o, FF79.L14.Opp_le_Opp_of_normalized hJ₁ hn₁ ho, n' * n, ?_, by group⟩
  obtain ⟨hn'J, hn'N⟩ := Subgroup.mem_inf.1 hn'
  obtain ⟨hnD, hnN⟩ := Subgroup.mem_inf.1 hn
  exact Subgroup.mem_inf.2 ⟨mul_mem (hJ₁ hn'J) hnD, mul_mem hn'N hnN⟩

theorem nor_zpowers {n g : G} (hn : n * g = g * n) : n ∈ Nor (Subgroup.zpowers g) := by
  have key : ∀ m : G, m * g = g * m → ∀ z ∈ Subgroup.zpowers g, m * z * m⁻¹ ∈ Subgroup.zpowers g := by
    intro m hm z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← conj_zpow, show m * g * m⁻¹ = g by rw [hm]; group]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) k
  have hn' : n⁻¹ * g = g * n⁻¹ := (Commute.inv_left (show Commute n g from hn)).eq
  rw [Nor, Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key n hn z, fun hz => ?_⟩
  have := key n⁻¹ hn' _ hz
  have e : n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem nor_sup {A A' : Subgroup G} : Nor A ⊓ Nor A' ≤ Nor (A ⊔ A') := by
  intro n hn
  have hmap : ∀ m ∈ Nor A ⊓ Nor A', ∀ z ∈ A ⊔ A', m * z * m⁻¹ ∈ A ⊔ A' := by
    intro m hm z hz
    have h1 : A.map (MulAut.conj m).toMonoidHom ≤ A := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hm).1) y).1 hy
    have h2 : A'.map (MulAut.conj m).toMonoidHom ≤ A' := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hm).2) y).1 hy
    have : (A ⊔ A').map (MulAut.conj m).toMonoidHom ≤ A ⊔ A' := by
      rw [Subgroup.map_sup]
      exact sup_le_sup h1 h2
    exact this ⟨z, hz, rfl⟩
  rw [Nor, Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨hmap n hn z, fun hz => ?_⟩
  have := hmap n⁻¹ (inv_mem hn) _ hz
  have e : n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem E_eq (h : FF84Sec4 b L B K b₁ b₂) :
    Subgroup.closure ({b, b₁} : Set G) =
      Subgroup.zpowers (b * b₁) ⊔ Subgroup.zpowers (b * b₁ ^ 2) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    have h1 : b₁ ∈ Subgroup.zpowers (b * b₁) ⊔ Subgroup.zpowers (b * b₁ ^ 2) := by
      have := mul_mem (inv_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers (b * b₁))))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers (b * b₁ ^ 2)) :
          b * b₁ ^ 2 ∈ Subgroup.zpowers (b * b₁) ⊔ Subgroup.zpowers (b * b₁ ^ 2))
      rwa [show (b * b₁)⁻¹ * (b * b₁ ^ 2) = b₁ by group] at this
    have h0 : b ∈ Subgroup.zpowers (b * b₁) ⊔ Subgroup.zpowers (b * b₁ ^ 2) := by
      have := mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers (b * b₁)) :
          b * b₁ ∈ Subgroup.zpowers (b * b₁) ⊔ Subgroup.zpowers (b * b₁ ^ 2)) (inv_mem h1)
      rwa [show b * b₁ * b₁⁻¹ = b by group] at this
    rintro z (hz | hz)
    · rw [hz]; exact h0
    · rw [Set.mem_singleton_iff.1 hz]; exact h1
  · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 (bb₁sq_mem_E h))
    exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem B_le_nor_P₁ (h : FF84Sec4 b L B K b₁ b₂) :
    B ≤ Nor (Subgroup.zpowers (b * b₁ ^ 2)) := fun y hy =>
  nor_zpowers (comm_of_mem h hy (bb₁sq_mem h)).eq

theorem nor_P₁_le_nor_E (h : FF84Sec4 b L B K b₁ b₂) :
    Cen (b * b₁) ⊓ Nor (Subgroup.zpowers (b * b₁ ^ 2)) ≤ Nor (Subgroup.closure ({b, b₁} : Set G)) := by
  rintro n ⟨hn1, hn2⟩
  rw [E_eq h]
  exact nor_sup ⟨nor_zpowers (Subgroup.mem_centralizer_singleton_iff.1 hn1), hn2⟩

theorem exists_mul_of_index_three {D D₀ N : Subgroup G} (hDD : D₀ ≤ D)
    (hn : ∀ g ∈ D, ∀ x ∈ D₀, g * x * g⁻¹ ∈ D₀) (hND : N ≤ D) (h3 : D₀.relIndex D = 3)
    (hNnot : ¬ N ≤ D₀) : ∀ d ∈ D, ∃ d₀ ∈ D₀, ∃ n ∈ N, d = d₀ * n := by
  let Q : Subgroup G :=
    { carrier := {d | ∃ d₀ ∈ D₀, ∃ n ∈ N, d = d₀ * n}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, n, hn', rfl⟩ ⟨a', ha', n', hn'', rfl⟩
        refine ⟨a * (n * a' * n⁻¹), mul_mem ha (hn n (hND hn') a' ha'), n * n', mul_mem hn' hn'',
          by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, n, hn', rfl⟩
        refine ⟨n⁻¹ * a⁻¹ * n⁻¹⁻¹, hn n⁻¹ (inv_mem (hND hn')) a⁻¹ (inv_mem ha), n⁻¹,
          inv_mem hn', by group⟩ }
  have hQD : Q ≤ D := by
    rintro _ ⟨a, ha, n, hn', rfl⟩
    exact mul_mem (hDD ha) (hND hn')
  have hD₀Q : D₀ ≤ Q := fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩
  have hNQ : N ≤ Q := fun n hn' => ⟨1, one_mem _, n, hn', by simp⟩
  have hmul := Subgroup.relIndex_mul_relIndex D₀ Q D hD₀Q hQD
  rw [h3] at hmul
  rcases (Nat.prime_mul_iff).1 (hmul ▸ Nat.prime_three) with ⟨-, hc⟩ | ⟨-, ha⟩
  · have hDQ : D ≤ Q := Subgroup.relIndex_eq_one.1 hc
    intro d hd
    exact hDQ hd
  · exfalso
    exact hNnot (hNQ.trans (Subgroup.relIndex_eq_one.1 ha))

theorem B_not_le_D₀ (h : FF84Sec4 b L B K b₁ b₂) {D₀ : Subgroup G}
    (hsyl : IsSylowOf 3 (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) D₀) : ¬ B ≤ D₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hBD
  have hBU : B ≤ Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) :=
    le_of_isSylowOf hsyl hBD (isPGroup_B h) (U_le_B h)
  have heq : Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) = B := le_antisymm (U_le_B h) hBU
  have := relIndex_U h
  rw [heq, Subgroup.relIndex_self] at this
  omega

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
