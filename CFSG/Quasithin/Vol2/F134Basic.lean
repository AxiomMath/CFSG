module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Group
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.Quasithin.F134

open CFSG.Quasithin.P134 CFSG.QuasithinUnique

@[expose] def NoElemNine (X : Type*) [Group X] : Prop :=
  ∀ Q : Subgroup X, Nat.card Q = 9 → (∀ x ∈ Q, x ^ 3 = 1) → False

theorem NoElemNine.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoElemNine Y) : NoElemNine X := by
  intro Q hQ hexp
  refine h (Q.map e.toMonoidHom) ?_ ?_
  · rw [← hQ]
    exact (Nat.card_congr (Q.equivMapOfInjective _ e.injective).toEquiv).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

theorem not_isCyclic_of_card_nine {X : Type*} [Group X] {Q : Subgroup X} (hQ : Nat.card Q = 9)
    (hexp : ∀ x ∈ Q, x ^ 3 = 1) : ¬ IsCyclic Q := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg, hQ] at this
  norm_num at this

theorem noElemNine_of_isCyclic {X : Type*} [Group X]
    (h : ∀ Q : Subgroup X, IsPGroup 3 Q → IsCyclic Q) : NoElemNine X := by
  intro Q hQ hexp
  refine not_isCyclic_of_card_nine hQ hexp (h Q ?_)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  exact IsPGroup.iff_card.mpr ⟨2, by rw [hQ]; norm_num⟩

theorem isCyclic_of_isPGroup_of_surjective {G G' : Type*} [Group G] [Finite G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} [Fact p.Prime]
    (hG : ∀ P : Sylow p G, IsCyclic (P : Subgroup G)) (Q : Subgroup G') (hQ : IsPGroup p Q) :
    IsCyclic Q := by
  have : Finite G' := Finite.of_surjective f hf
  obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf p S'
  have : IsCyclic (S : Subgroup G) := hG S
  have : IsCyclic ((S : Subgroup G).map f) :=
    isCyclic_of_surjective (f.subgroupMap S) (MonoidHom.subgroupMap_surjective f S)
  have hS'' : Q ≤ (S : Subgroup G).map f := by
    rw [← Sylow.coe_mapSurjective hf S]
    exact hS'
  exact Subgroup.isCyclic_of_le hS''

section Config

variable {A : Type} [Group A] {L P T : Subgroup A}

theorem E9Config.exists_subgroup (h : E9Config L P T) :
    ∃ Q : Subgroup L, Nat.card Q = 9 ∧ ∀ x ∈ Q, x ^ 3 = 1 :=
  ⟨P.subgroupOf L, by
    rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv,
    fun x hx => Subtype.ext (by simpa using h.exp x (Subgroup.mem_subgroupOf.mp hx))⟩

theorem E9Config.nine_dvd_card (h : E9Config L P T) : 9 ∣ Nat.card L :=
  h.card ▸ Subgroup.card_dvd_of_le h.le

theorem E9Config.isSylowTwoOf_inf [Finite A] (h : E9Config L P T) : IsSylowTwoOf (T ⊓ L) L :=
  have := h.normal
  RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow le_top
    (Subgroup.Normal.isSubnormal inferInstance).subgroupOf

theorem E9Config.mul_inf (h : E9Config L P T) :
    ∀ t ∈ T ⊓ L, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T ⊓ L, t * x = y * s := by
  intro t ht x hx
  obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht.1 x hx
  refine ⟨y, hy, s, ⟨hs, ?_⟩, he⟩
  have hs' : s = y⁻¹ * (t * x) := by rw [he]; group
  rw [hs']
  exact L.mul_mem (L.inv_mem (h.le hy)) (L.mul_mem ht.2 (h.le hx))

theorem E9Config.card_sup_inf [Finite A] (h : E9Config L P T) :
    Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = 9 * Nat.card (T ⊓ L : Subgroup A) :=
  card_sup_eq_of_mul h.card (h.sylow.2.1.to_le inf_le_left) (E9Config.mul_inf h)

theorem E9Config.sup_inf_le (h : E9Config L P T) : P ⊔ (T ⊓ L) ≤ L :=
  sup_le h.le inf_le_right

theorem E9Config.exists_model [Finite A] (h : E9Config L P T) {X : Type*} [Group X]
    (e : ↥L ≃* X) : ∃ H : Subgroup X, ∃ k : ℕ, Nat.card H = 9 * 2 ^ k ∧ 2 ^ k ∣ Nat.card X ∧
      ¬ 2 ∣ Nat.card X / 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := E9Config.isSylowTwoOf_inf h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hcardX : Nat.card X = Nat.card L := (Nat.card_congr e.toEquiv).symm
  have hidx := ((T ⊓ L).subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hk] at hidx
  refine ⟨((P ⊔ (T ⊓ L)).subgroupOf L).map e.toMonoidHom, k, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E9Config.sup_inf_le h)).toEquiv,
      E9Config.card_sup_inf h, hk]
  · rw [hcardX, ← hidx]
    exact Dvd.intro _ rfl
  · rw [hcardX, ← hidx, Nat.mul_div_cancel_left _ (by positivity)]
    exact hS.2.2

end Config

theorem noE9Config_of_noElemNine {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → NoElemNine X) : NoE9Config F := by
  intro A _ _ L P T hL hcfg
  obtain ⟨Q, hQ, hexp⟩ := E9Config.exists_subgroup hcfg
  exact hF L hL Q hQ hexp

theorem noE9Config_of_not_dvd {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → ¬ 9 ∣ Nat.card X) : NoE9Config F := by
  intro A _ _ L P T hL hcfg
  exact hF L hL (E9Config.nine_dvd_card hcfg)

theorem card_dvd_factorial_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) : Nat.card G ∣ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    have := H.normalCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ H.normalCore_le)) hH
  have := H.index_normalCore_dvd_factorial_index
  rwa [hcore, Subgroup.index_bot] at this

theorem card_ne_seventytwo {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) (H : Subgroup G) : Nat.card H ≠ 72 := by
  intro hH
  have hidx := H.card_mul_index
  rw [hH, hG] at hidx
  have h5 : H.index = 5 := by omega
  have hne : H ≠ ⊤ := by
    rintro rfl
    rw [Subgroup.index_top] at h5
    omega
  have := card_dvd_factorial_index H hne
  rw [h5, hG] at this
  norm_num [Nat.factorial] at this

theorem noE9Config_of_simple_card_360 {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X →
      ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (_ : IsSimpleGroup Y), Nat.card Y = 360 ∧
        Nonempty (X ≃* Y)) : NoE9Config F := by
  intro A _ _ L P T hL hcfg
  obtain ⟨Y, _, _, _, hY, ⟨e⟩⟩ := hF L hL
  obtain ⟨H, k, hH, hk, hodd⟩ := E9Config.exists_model hcfg e
  rw [hY] at hk hodd
  have hk3 : k = 3 := by
    have hle : k ≤ 3 := by
      by_contra hlt
      have : 2 ^ 4 ∣ 360 := (Nat.pow_dvd_pow 2 (by omega)).trans hk
      norm_num at this
    interval_cases k <;> simp_all
  subst hk3
  exact card_ne_seventytwo hY H (by rw [hH]; norm_num)

theorem conj_mem_sup {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ B) (hB : ∀ b ∈ B, x * b * x⁻¹ ∈ A ⊔ B) :
    ∀ y ∈ A ⊔ B, x * y * x⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  exact fun y hy => hle hy

theorem not_dvd_nine_mul_two_pow {p k : ℕ} (hp : p = 5 ∨ p = 7 ∨ p = 11) : ¬ p ∣ 9 * 2 ^ k := by
  have hprime : p.Prime := by rcases hp with h | h | h <;> rw [h] <;> norm_num
  intro h
  rcases (Nat.Prime.dvd_mul hprime).1 h with h9 | h2
  · have := Nat.le_of_dvd (by norm_num) h9
    rcases hp with h | h | h <;> rw [h] at h9 <;> norm_num at h9
  · have := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 (hprime.dvd_of_dvd_pow h2)
    rcases hp with h | h | h <;> omega

end CFSG.Quasithin.F134
