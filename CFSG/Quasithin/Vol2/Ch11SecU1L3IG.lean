module

public import CFSG.Goldschmidt.Steps.Sec87d
public import CFSG.Quasithin.Vol2.Ch11SecU1Main

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b

variable {G : Type} [Group G]

structure SettingL3 [Finite G] (L : Subgroup G) : Prop where
  almostSimple : SecE3.AlmostSimple L
  two_dvd : 2 ∣ Nat.card L
  inner_conj : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ L, g * x * g⁻¹ = y
  inner_max : ∀ x ∈ L, orderOf x = 2 → IsCoatom (Subgroup.centralizer ({x} : Set G))
  inner_nParam : ∀ x ∈ L, orderOf x = 2 → nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1
  inner_torus : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
    ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) →
      ∃ P : Subgroup G, (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
        Q ≤ Subgroup.normalizer (P : Set G) ∧ ¬ P ≤ Subgroup.centralizer ({x} : Set G)
  outer : ∀ b : G, b ∉ L → orderOf b = 2 → SigmaFacts L b
  outer_pair : ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L → orderOf t₁ = 2 → orderOf t₂ = 2 →
    t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L

variable [Finite G]

theorem exists_central_involution_of_normal {L : Subgroup G} (hLn : L.Normal)
    (h2 : 2 ∣ Nat.card L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) :
    ∃ z ∈ L, orderOf z = 2 ∧ z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  have hSyl : IsSylowIn 2 (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hne : T ⊓ L ≠ ⊥ := by
    intro hbot
    apply hSyl.2.2
    rw [hbot, Subgroup.relIndex_bot_left]
    exact h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hLn.conj_mem x hxL t⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, ?_⟩
      · have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using this
      · have := hLn.conj_mem _ hxL t⁻¹
        simpa [mul_assoc] using this
  have hX := CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hT.2.1 inf_le_left hTN hne
  have hXp : IsPGroup 2 ↥((T ⊓ L) ⊓ (T ⊓ Subgroup.centralizer (T : Set G))) :=
    hT.2.1.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨k, hk⟩ := hXp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hX (Subgroup.card_eq_one.mp hk)
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' (G := ↥((T ⊓ L) ⊓
    (T ⊓ Subgroup.centralizer (T : Set G)))) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  obtain ⟨⟨hyT, hyL⟩, -, hyc⟩ := y.2
  refine ⟨y, hyL, by rw [Subgroup.orderOf_coe]; exact hy2, hyT, fun t ht => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hyc t ht

theorem sup_eq_top_of_almostSimple {L : Subgroup G} (h : SecE3.AlmostSimple L)
    {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) : L ⊔ T = ⊤ := by
  have := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (L ⊔ T).index ∣ L.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (L ⊔ T).index ∣ T.index := Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp h.isPGroup_quotient)
  rw [← Subgroup.index] at hk
  rw [hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact Subgroup.index_eq_one.mp hj
  · exact absurd ((hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2) hT2

theorem member_of_sigma_L3 (hComp : ComponentMember) {L : Subgroup G}
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {v b z : G} (hvA : v ∈ A) (hvL : v ∈ L)
    (hv1 : v ≠ 1) (hbA : b ∈ A) (hA4 : ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.centralizer {b}) (Subgroup.centralizer {b}))
    (hb : SigmaFacts L b) (hzL : z ∈ L) (hz1 : z ≠ 1) :
    ∃ K : Subgroup G, IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer {z} := by
  obtain ⟨L₀, hle, hs, hnab, hnorm, hcent⟩ := hb
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hL₀C : L₀ ≤ C := hle.trans inf_le_right
  have hSyl₀ : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    have h1 := B6.isSylowTwoOf_inf_normal hSyl hL₀C hnorm
    rwa [inf_assoc, inf_eq_right.mpr hL₀C] at h1
  have hbc : b ∈ Subgroup.centralizer (L₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL₀C hl)
  have hnotc : ∀ w ∈ L, w ≠ 1 → w ∉ Subgroup.centralizer (L₀ : Set G) := fun w hwL hw1 hw =>
    hw1 (by
      have h1 : w ∈ L ⊓ Subgroup.centralizer (L₀ : Set G) := ⟨hwL, hw⟩
      rw [hcent] at h1
      exact Subgroup.mem_bot.mp h1)
  have hcomm : v * b = b * v := le_centralizer_of_isElemAbelian hA hbA hvA |>
    Subgroup.mem_centralizer_singleton_iff.mp
  have hvv : v * v = 1 := by rw [← sq]; exact hA.2 v hvA
  have hrel : (A ⊓ Subgroup.centralizer (L₀ : Set G)).relIndex A = 2 := by
    refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
      ⟨v, hvA, fun hv => hnotc v hvL hv1 hv.2, fun x hx => ?_⟩
    rcases hA4 x hx with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨A.one_mem, Subgroup.one_mem _⟩
    · exact Or.inl ⟨A.mul_mem hvA hvA, by rw [hvv]; exact Subgroup.one_mem _⟩
    · exact Or.inr ⟨hbA, hbc⟩
    · refine Or.inl ⟨A.mul_mem (A.mul_mem hvA hbA) hvA, ?_⟩
      rw [mul_assoc, ← hcomm, ← mul_assoc, hvv, one_mul]
      exact hbc
  have hτ : tauOf ⊤ T A ≤ Subgroup.normalizer (L₀ : Set G) :=
    (tauOf_le_centralizer hO2 hbA).trans hnorm
  refine ⟨L₀ ⊔ tauOf ⊤ T A, hComp G T A L₀ hT hAT hA hs hnab hτ hSyl₀ hrel, fun hK => ?_⟩
  refine hnotc z hzL hz1 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp ((le_sup_left.trans hK) hl)

theorem member_of_torus_L3 (hTor : TorusMember) {L : Subgroup G} (h : SettingL3 L)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {z y : G} (hzA : z ∈ A) (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hyA : y ∈ A) (hyL : y ∈ L) (hy2 : orderOf y = 2) (hzy : z ≠ y) :
    ∃ K : Subgroup G, IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer {z} := by
  have hτ2 : IsPGroup 2 ↥(tauOf ⊤ T A) := hT.2.1.to_le (tauOf_le ⊤ T A)
  have hτC : tauOf ⊤ T A ≤ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) :=
    le_inf (tauOf_le_centralizer hO2 hzA) (tauOf_le_centralizer hO2 hyA)
  have hzyc : z * y = y * z :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isElemAbelian hA hyA hzA)
  obtain ⟨P, hPp, hP2, hPN, hPz⟩ := h.inner_torus z hzL y hyL hz2 hy2 hzy hzyc _ hτ2 hτC
  exact ⟨P ⊔ tauOf ⊤ T A, hTor G T A P hT hAT hA hPp hP2 hPN ⟨z, hzA, hPz⟩,
    fun hle => hPz (le_sup_left.trans hle)⟩

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
