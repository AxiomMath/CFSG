module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5TransvG
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFA5

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup

lemma card_dvd_sixty_pow_two {c n : ℕ} (h60 : c ∣ 60) (hn : c ∣ 2 ^ n) :
    c = 1 ∨ c = 2 ∨ c = 4 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn
  subst hm
  have hm3 : m < 3 := by
    by_contra h
    have h3 : 3 ≤ m := by omega
    have h8 : 2 ^ 3 ∣ 2 ^ m := pow_dvd_pow 2 h3
    have := h8.trans h60
    norm_num at this
  interval_cases m <;> norm_num

lemma natCard_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  have hP : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  omega

theorem not_relIndex_le_two {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {A : Subgroup L}
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    {y : L} (hy : y ∈ A) (hφy : φ y ≠ 1) (hφy2 : φ y ^ 2 = 1) :
    ¬ (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V ≤ 2 := by
  intro hle
  obtain ⟨a, ha, v, hv, hne⟩ := hAnt
  have hcent_contra : (a : G) ∈ Subgroup.centralizer (V : Set G) → False := fun hc =>
    hne ((Subgroup.mem_centralizer_iff.mp hc) v hv).symm
  have hrel : (V ⊓ Subgroup.centralizer {(y : G)}).relIndex V ≤ 2 := by
    have hC : Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)
        ≤ Subgroup.centralizer {(y : G)} :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ⟨y, hy, rfl⟩)
    have hsub : V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)
        ≤ V ⊓ Subgroup.centralizer {(y : G)} := inf_le_inf_left V hC
    have hpos : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
        ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    exact (Subgroup.relIndex_le_of_le_left hsub hpos).trans hle
  have hL : L ≤ Subgroup.centralizer (V : Set G) :=
    CFSG.Quasithin.FA5.centralizes_of_alt5_transvection hV2 hLV φ hφ hker hφy hφy2 hrel
  exact hcent_contra (hL a.2)

theorem card_image_eq_four {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {A : Subgroup L} (hA : IsPGroup 2 A)
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    (hidx : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ≤ Nat.card (A.map φ)) :
    Nat.card (A.map φ) = 4 := by
  have hdiv60 : Nat.card (A.map φ) ∣ 60 := by
    have h := Subgroup.card_subgroup_dvd_card (A.map φ)
    rwa [natCard_alt5] at h
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hA
  have hdiv2 : Nat.card (A.map φ) ∣ 2 ^ n := by
    have hsub : Nat.card (A.map φ) ∣ Nat.card A := Subgroup.card_map_dvd A φ
    exact hsub.trans hn
  rcases card_dvd_sixty_pow_two hdiv60 hdiv2 with h1 | h2 | h4
  · exfalso
    obtain ⟨a, ha, v, hv, hne⟩ := hAnt
    have hbot : A.map φ = ⊥ := Subgroup.card_eq_one.mp h1
    have hφa : φ a = 1 := by
      have hmem : φ a ∈ A.map φ := Subgroup.mem_map_of_mem φ ha
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact hne ((Subgroup.mem_centralizer_iff.mp (hker a hφa)) v hv).symm
  · exfalso
    have hne_bot : A.map φ ≠ ⊥ := fun h => by
      have := Subgroup.card_eq_one.mpr h
      omega
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne_bot
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    have hsq : x ^ 2 = 1 := by
      have hdvd := orderOf_dvd_natCard x
      rw [h2] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hφy : φ y ≠ 1 := by
      intro h
      apply hx1
      apply Subtype.ext
      have h' : (x : alternatingGroup (Fin 5)) = 1 := by rw [← hyx, h]
      exact h'
    have hφy2 : φ y ^ 2 = 1 := by
      rw [hyx]
      have := congrArg Subtype.val hsq
      simpa using this
    exact not_relIndex_le_two hV2 hLV φ hφ hker hAnt hy hφy hφy2 (hidx.trans h2.le)
  · exact h4

theorem relIndex_eq_four {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {A : Subgroup L} (hA : IsPGroup 2 A)
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    (hidx : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ≤ Nat.card (A.map φ)) :
    (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V = 4 := by
  have hc4 := card_image_eq_four hV2 hLV φ hφ hker hA hAnt hidx
  have hbot : A.map φ ≠ ⊥ := fun h => by
    have := Subgroup.card_eq_one.mpr h
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
  have hx4 : x ^ 4 = 1 := by
    have hdvd := orderOf_dvd_natCard x
    rw [hc4] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hφy : φ y ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    have h' : (x : alternatingGroup (Fin 5)) = 1 := by rw [← hyx, h]
    exact h'
  have hφy2 : φ y ^ 2 = 1 := by
    have h4 : φ y ^ 4 = 1 := by
      rw [hyx]
      have := congrArg Subtype.val hx4
      simpa using this
    exact alt5_no_order_four _ h4
  have hlow : 3 ≤ (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V := by
    by_contra h
    exact not_relIndex_le_two hV2 hLV φ hφ hker hAnt hy hφy hφy2 (by omega)
  have hup : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V ≤ 4 :=
    hidx.trans hc4.le
  have hVp : IsPGroup 2 V := by
    refine isPGroup_iff_orderOf_dvd_pow.mpr fun g => ⟨1, ?_⟩
    have hg2 : g ^ 2 = 1 := by
      rw [sq]
      exact Subtype.ext (hV2 g.1 g.2)
    simpa using orderOf_dvd_of_pow_eq_one hg2
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hVp
  have hdvdV : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ∣ 2 ^ n := by
    have h1 : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
        ∣ Nat.card V := by
      unfold Subgroup.relIndex
      exact Subgroup.index_dvd_card _
    exact h1.trans hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvdV
  rw [hm] at hlow hup ⊢
  have hm3 : m < 3 := by
    by_contra h
    have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h8.trans hup) (by norm_num)
  interval_cases m
  · norm_num at hlow
  · norm_num at hlow
  · norm_num

end CFSG.Quasithin.Kleidman.F204

end
