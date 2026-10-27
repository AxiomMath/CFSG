module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cSzFF
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem ordA_one_two_pow_ne_20160 {n : ℕ} (hn : 1 ≤ n) : ordA 1 (2 ^ n) ≠ 20160 := by
  intro h
  obtain ⟨r, hr, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordA (n := 1) le_rfl hn).two
  have h6 : n * (1 * (1 + 1) / 2) = 6 :=
    CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (b := 6) hr (⟨157, by norm_num⟩ : Odd 315)
      (hm.symm.trans (h.trans (by norm_num)))
  have hn6 : n = 6 := by omega
  subst hn6
  rw [ordA_one_two_pow_eq hn] at h
  norm_num at h

section Leaves

variable {K Y : Type} [Group K] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect K]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (ψ : K →* Y) (hψ : Function.Surjective ψ)
  (hL : IsPSL 3 2 2 Y)
include hY hN hQ hψ hL

theorem false_of_card_lt_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) (h1 : 1 < Nat.card X) (h2 : Nat.card X < 20160) : False := by
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
  have h := card_le_of_surjective hY hN hQ ψ hψ f hf
  rw [card_isPSL_three_two_two hL] at h
  omega

theorem false_of_simple_of_l34 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (f : K →* X) (hf : Function.Surjective f) (hX : Nat.card X ≠ 20160) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  exact hX (by rw [← Nat.card_congr e.toEquiv, card_isPSL_three_two_two hL])

theorem false_of_psl41_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) (h : IsPSL 4 2 1 X) : False := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  exact not_nonempty_mulEquiv_psl_three_four hL h ⟨e⟩

theorem false_of_alt_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (e : X ≃* alternatingGroup (Fin n)) : False := by
  have hc : Nat.card X = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, card_alt (by omega)]
  refine false_of_card_lt_of_l34 hY hN hQ ψ hψ hL f hf ?_ ?_ <;> rw [hc]
  · interval_cases n <;> decide
  · interval_cases n <;> decide

theorem false_of_hatAlt_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (h : IsHat X (alternatingGroup (Fin n))) : False := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact false_of_alt_of_l34 hY hN hQ ψ hψ hL
    ((QuotientGroup.mk' (Subgroup.center X)).comp f) ((QuotientGroup.mk'_surjective _).comp hf)
    hn5 hn7 e

theorem false_of_sl2_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : IsSL2 p X) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := h
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    isSimpleGroup_psl2 hp5
  refine false_of_simple_of_l34 hY hN hQ ψ hψ hL
    (((QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))).comp e.toMonoidHom).comp f)
    (((QuotientGroup.mk'_surjective _).comp e.surjective).comp hf) fun hc => ?_
  have h2 := two_mul_card_psl2 (p := p) (by omega)
  rw [hc] at h2
  exact false_of_isPSL3_of_card (k := 2) le_rfl hL hp (by omega)
    (by rw [card_isPSL_three_two_two hL]; exact h2)

theorem false_of_psl2_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : IsPSL 2 p 1 X) :
    False := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  refine false_of_simple_of_l34 hY hN hQ ψ hψ hL f hf fun hc => ?_
  have h2 := two_mul_card_isPSL_two (by omega) h
  rw [hc] at h2
  exact false_of_isPSL3_of_card (k := 2) le_rfl hL hp (by omega)
    (by rw [card_isPSL_three_two_two hL]; exact h2)

theorem false_of_psl22_of_l34 {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (h : IsPSL 2 2 n X) : False := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h).2
  have hn : 1 ≤ n := by
    obtain ⟨⟨-, h1, -⟩, -⟩ := h
    exact h1
  refine false_of_simple_of_l34 hY hN hQ ψ hψ hL f hf ?_
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
  exact ordA_one_two_pow_ne_20160 hn

theorem false_of_sz_of_l34 {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f) {e : ℕ} (h : IsSz e X) : False := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 e h).2
  refine false_of_simple_of_l34 hY hN hQ ψ hψ hL f hf fun hc => ?_
  exact not_three_dvd_card_isSz h (by rw [hc]; norm_num)

theorem false_of_m22_of_l34 (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f) (h : IsSporadic .M22 X) : False := by
  obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := h
  have := hM.1
  have : IsSimpleGroup X := e.isSimpleGroup
  refine false_of_simple_of_l34 hY hN hQ ψ hψ hL f hf ?_
  rw [Nat.card_congr e.toEquiv, hM.2.1]
  norm_num

theorem false_of_m24_of_l34 (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f) (h : IsSporadic .M24 X) : False := by
  obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
  have := hM.2.2.1
  have : IsSimpleGroup X := e.isSimpleGroup
  refine false_of_simple_of_l34 hY hN hQ ψ hψ hL f hf ?_
  rw [Nat.card_congr e.toEquiv, hM.2.2.2]
  norm_num

theorem false_of_hatM22_of_l34 (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f)
    (h : IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : False := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) := Finite.of_equiv _ e.toEquiv
  exact false_of_m22_of_l34 hY hN hQ ψ hψ hL hM
    ((e.toMonoidHom.comp (QuotientGroup.mk' _)).comp f)
    ((e.surjective.comp (QuotientGroup.mk'_surjective _)).comp hf) ⟨MulEquiv.refl _⟩

theorem m23_of_case_of_l34 (hM : FactMathieuOrders) {Γ : Type}
    [Group Γ] [Finite Γ] {B L : Subgroup Γ} (σ : K →* ↥B) (hσ : Function.Surjective σ)
    (hcase : A312Case B L) : IsSporadic .M23 ↥L := by
  set σ2 := (QuotientGroup.mk' (CFSG.pCore 2 ↥B)).comp σ with hσ2def
  have hσ2 : Function.Surjective σ2 := (QuotientGroup.mk'_surjective _).comp hσ
  have hcard : ∀ {X : Type} [Group X] [Finite X] {c : ℕ} (f : K →* X), Function.Surjective f →
      Nat.card X = c → 1 < c → c < 20160 → False :=
    fun f hf hc h1 h2 => false_of_card_lt_of_l34 hY hN hQ ψ hψ hL f hf (hc ▸ h1) (hc ▸ h2)
  have halt : ∀ {X : Type} [Group X] [Finite X] {n : ℕ} (f : K →* X), Function.Surjective f →
      5 ≤ n → n ≤ 7 → (X ≃* alternatingGroup (Fin n)) → False :=
    fun f hf hn5 hn7 e => false_of_alt_of_l34 hY hN hQ ψ hψ hL f hf hn5 hn7 e
  have hhat : ∀ {X : Type} [Group X] [Finite X] {n : ℕ} (f : K →* X), Function.Surjective f →
      5 ≤ n → n ≤ 7 → IsHat X (alternatingGroup (Fin n)) → False :=
    fun f hf hn5 hn7 h => false_of_hatAlt_of_l34 hY hN hQ ψ hψ hL f hf hn5 hn7 h
  have hl41 : ∀ {X : Type} [Group X] [Finite X] (f : K →* X), Function.Surjective f →
      IsPSL 4 2 1 X → False :=
    fun f hf h => false_of_psl41_of_l34 hY hN hQ ψ hψ hL f hf h
  unfold A312Case A312C2 A312C3 A312C4 A312C5 A312C6 A312C7 A312C8 A312C9 A312C10 A312C11
    A312C12 A312C13 A312C14 A312C15 A312C16 A312C17 A312C18 A312C19 A312C20 at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨⟨n, hn⟩, -, -⟩ := h
    exact (false_of_psl22_of_l34 hY hN hQ ψ hψ hL σ2 hσ2 hn).elim
  · obtain ⟨f, hf, -, -⟩ := h
    exact (false_of_sz_of_l34 hY hN hQ ψ hψ hL σ2 hσ2 hf).elim
  · obtain ⟨hB, -, -⟩ := h
    exact (hcard σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)).elim
  · obtain ⟨hB, -, -⟩ := h
    exact (hl41 σ2 hσ2 hB).elim
  · exfalso
    obtain ⟨hB | hB, -⟩ := h
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
    · exact hcard σ hσ (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)
  · exfalso
    rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 6)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
    · exact hhat σ hσ (by norm_num) (by norm_num) hB
  · exfalso
    rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · exact false_of_psl2_of_l34 hY hN hQ ψ hψ hL σ hσ hp hp3 hB
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
  · exfalso
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · exact false_of_sl2_of_l34 hY hN hQ ψ hψ hL σ hσ hp hp3 hB
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 6)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
    · exact hhat σ hσ (by norm_num) (by norm_num) hB
  · exfalso
    obtain ⟨p, hp, hp3, hB, -⟩ := h
    exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
      false_of_sl2_of_l34 hY hN hQ ψ hψ hL g' hg' hp hp3 hZ
  · exfalso
    obtain ⟨hB, -⟩ := h
    obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 6)) := hB
    exact halt σ hσ (by norm_num) (by norm_num) e
  · exfalso
    rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 6)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hhat g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL23⟩ := h
    · exact (false_of_m22_of_l34 hY hN hQ ψ hψ hL hM σ hσ hB).elim
    · exact hL23
    · exfalso
      exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 7)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exfalso
      exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exfalso
      exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exfalso
      exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 6)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exfalso
      exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
  · exfalso
    obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hl41 g' hg' hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hhat g' hg' (by norm_num) (by norm_num) hZ
  · exfalso
    obtain ⟨hB, -⟩ := h
    obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hB
    exact halt σ hσ (by norm_num) (by norm_num) e
  · exfalso
    obtain ⟨hB, -⟩ := h
    exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
      obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
      exact halt g' hg' (by norm_num) (by norm_num) e
  · exfalso
    obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        false_of_hatM22_of_l34 hY hN hQ ψ hψ hL hM g' hg' hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        false_of_m24_of_l34 hY hN hQ ψ hψ hL hM g' hg' hZ
    · obtain ⟨e⟩ : Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ2 hσ2 (by norm_num) (by norm_num) e
    · exact hhat σ2 hσ2 (by norm_num) (by norm_num) hB
    · exact hl41 σ2 hσ2 hB
    · exact hcard σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)
  · exfalso
    obtain ⟨hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
  · exfalso
    obtain ⟨hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hhat g' hg' (by norm_num) (by norm_num) hZ
  · exfalso
    obtain ⟨hB | hB, -, -⟩ := h
    · obtain ⟨e⟩ : Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ2 hσ2 (by norm_num) (by norm_num) e
    · exact hcard σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)

end Leaves

variable {G : Type} [Group G] [Finite G]

theorem overgroup_iso_or_m23_of_l34
    (hM : FactMathieuOrders) {T K Kp : Subgroup G} {Y : Type} [Group Y] [Finite Y]
    (hYL : IsPSL 3 2 2 Y)
    (hKl : quasithinIsLocal T K) (hKpl : quasithinIsLocal T Kp) (hKKp : K ≤ Kp)
    (hKq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) (ψ : ↥K →* Y)
    (hψ : Function.Surjective ψ)
    (h312 : A312Refined (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T))) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) ∨
      IsSporadic .M23 ↥(modO2Image (Kp ⊔ T) Kp) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Kp ⊔ T with hHdef
  have hS : IsSylowTwoOf T H := ⟨le_sup_right, hKpl.1, hKpl.2.2.1⟩
  have hBH : K ≤ H := hKKp.trans le_sup_left
  have hL : Kp ∈ cComp H := hKpl.2.1
  have hB : K ∈ lFamily T := hKl.2.1
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  have hY : L2BadType 2 Y := Or.inr (Or.inr (Or.inl hYL))
  have hYs : IsSimpleGroup Y := hY.isSimpleGroup le_rfl
  have hYab : ∃ a b : Y, a * b ≠ b * a := nonabelian_of_perfect_surjective ψ hψ
  set σ : ↥K →* ↥(modO2Image H K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom with hσ
  have hσs : Function.Surjective σ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  have hBL : modO2Image H K ≤ modO2Image H Kp := Subgroup.map_mono fun x hx => hKKp hx
  have hN : IsPGroup 2 (CFSG.Open.pCore 2 ↥K) := by
    exact CFSG.pCore_isPGroup
  have hNn : (CFSG.Open.pCore 2 ↥K).Normal := by
    exact CFSG.pCore_normal
  rcases lemma_1_2_4_refined h312 hS hBH hB hL hKKp with heq | ⟨-, hcase⟩ | ⟨-, hnon⟩
  · exact Or.inl (nonempty_mulEquiv_modO2_of_eq hBH hL heq)
  · exact Or.inr (m23_of_case_of_l34 hYab hN hKq ψ hψ hYL hM σ hσs hcase)
  · exact (false_of_a312Nonquasi le_rfl hY hKq ψ hψ hBL σ hσs hnon).elim

end CFSG.Quasithin.Vol2.Ch11.SecB
