module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Perf
public import CFSG.Quasithin.Vol2.Ch12Sec6T2A6

public section

namespace CFSG.Quasithin.H13

namespace S126T2

open Equiv

section Perfect

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_top_of_index_le_four (hY : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊤ : Subgroup Y))
    {H : Subgroup Y}
    (h4 : H.index ≤ 4) : H = ⊤ := by
  have : Group.IsSolvable (Perm (Y ⧸ H)) :=
    Equiv.Perm.isSolvable (by rw [← Subgroup.index_eq_card]; exact h4)
  have h1 := map_eq_bot_of_perfect hY (MulAction.toPermHom Y (Y ⧸ H)) inferInstance
  have hker : H.normalCore = ⊤ := by
    rw [Subgroup.normalCore_eq_ker, eq_top_iff]
    intro y _
    have : MulAction.toPermHom Y (Y ⧸ H) y ∈
        (⊤ : Subgroup Y).map (MulAction.toPermHom Y (Y ⧸ H)) := ⟨y, trivial, rfl⟩
    rw [h1, Subgroup.mem_bot] at this
    exact this
  exact eq_top_iff.2 (hker ▸ Subgroup.normalCore_le H)

theorem smul_eq_of_ncard_orbit_le_four {α : Type*} [MulAction Y α]
    (hY : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊤ : Subgroup Y)) {x : α}
    (h4 : (MulAction.orbit Y x).ncard ≤ 4) (y : Y) :
    y • x = x := by
  have h := eq_top_of_index_le_four hY (H := MulAction.stabilizer Y x)
    (by rw [MulAction.index_stabilizer]; exact h4)
  have hy : y ∈ MulAction.stabilizer Y x := by
    rw [h]
    trivial
  exact hy

end Perfect

theorem false_of_card_45 {H : Subgroup (Perm (Fin 8))} (hH : Nat.card H = 45) {p : Fin 8}
    (hp : ∀ σ ∈ H, σ p = p) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 ↥H) := inferInstance
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hPi := (P : Subgroup ↥H).card_mul_index
  rw [hk, hH] at hPi
  have hk1 : k = 1 := by
    have hnd := P.not_dvd_index
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have : 5 ^ 3 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h
      have h5 : 5 ^ k ≤ 45 := Nat.le_of_dvd (by norm_num) ⟨_, hPi.symm⟩
      omega
    interval_cases k
    · exact absurd (by omega : (P : Subgroup ↥H).index = 45) (fun h => hnd (h ▸ by norm_num))
    · rfl
    · omega
  subst hk1
  have hPi9 : (P : Subgroup ↥H).index = 9 := by omega
  have hn1 : Nat.card (Sylow 5 ↥H) = 1 := by
    have h1 := card_sylow_modEq_one 5 ↥H
    have h2 := P.card_dvd_index
    rw [hPi9] at h2
    have hpos : 0 < Nat.card (Sylow 5 ↥H) := Nat.card_pos
    have hle : Nat.card (Sylow 5 ↥H) ≤ 9 := Nat.le_of_dvd (by norm_num) h2
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card (Sylow 5 ↥H) <;> simp_all
  have : Subsingleton (Sylow 5 ↥H) := (Nat.card_eq_one_iff_unique.1 hn1).1
  have hPn : (P : Subgroup ↥H).Normal := P.normal_of_subsingleton
  set Q : Subgroup (Perm (Fin 8)) := (P : Subgroup ↥H).map H.subtype with hQ
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hQ5 : Nat.card Q = 5 := by
    rw [hQ, Subgroup.card_map_of_injective H.subtype_injective, hk, pow_one]
  have hQp : IsPGroup 5 ↥Q := IsPGroup.of_card (n := 1) (by rw [hQ5, pow_one])
  set Fx := MulAction.fixedPoints ↥Q (Fin 8) with hFx
  have hmem : ∀ y : Fin 8, y ∈ Fx ↔ ∀ τ ∈ Q, τ y = y := fun y =>
    ⟨fun h τ hτ => h ⟨τ, hτ⟩, fun h τ => h τ τ.2⟩
  have hcong : 8 ≡ Fx.ncard [MOD 5] := by
    have := hQp.card_modEq_card_fixedPoints (Fin 8)
    rwa [Nat.card_fin, Nat.card_coe_set_eq] at this
  have hFle : Fx.ncard ≤ 8 := by
    have := Set.ncard_le_ncard (Set.subset_univ Fx)
    rwa [Set.ncard_univ, Nat.card_fin] at this
  have hF8 : Fx.ncard ≠ 8 := by
    intro h8
    have huniv : Fx = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ, Nat.card_fin, h8]) (Set.toFinite _)
    have hbot : Q = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      exact Equiv.ext fun y => (hmem y).1 (huniv ▸ Set.mem_univ y) τ hτ
    rw [hbot, Subgroup.card_bot] at hQ5
    omega
  have hF3 : Fx.ncard = 3 := by
    unfold Nat.ModEq at hcong
    omega
  have hpF : p ∈ Fx := (hmem p).2 fun τ hτ => hp τ (hQH hτ)
  have hHF : ∀ σ ∈ H, ∀ y ∈ Fx, σ y ∈ Fx := by
    intro σ hσ y hy
    refine (hmem _).2 fun τ hτ => ?_
    obtain ⟨t, ht, rfl⟩ := hτ
    have h1 : (⟨σ, hσ⟩ : ↥H)⁻¹ * t * (⟨σ, hσ⟩ : ↥H) ∈ (P : Subgroup ↥H) := by
      have := hPn.conj_mem t ht (⟨σ, hσ⟩ : ↥H)⁻¹
      simpa using this
    have h2 := (hmem y).1 hy _ ⟨_, h1, rfl⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv,
      Perm.mul_apply] at h2
    have h3 := congrArg σ h2
    rwa [show σ (σ⁻¹ ((t : Perm (Fin 8)) (σ y))) = (t : Perm (Fin 8)) (σ y) from
      Equiv.apply_symm_apply σ _] at h3
  have hHfix : ∀ σ ∈ H, ∀ y ∈ Fx, σ y = y := by
    intro σ hσ y hy
    by_contra hne
    have hyp : y ≠ p := fun h => hne (h ▸ hp σ hσ)
    have hσyp : σ y ≠ p := fun h => hyp (σ.injective (h.trans (hp σ hσ).symm))
    have hFeq : Fx = {p, y, σ y} := by
      refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact hpF
        · exact hy
        · exact hHF σ hσ _ hy
      · rw [hF3, Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hyp.symm, hσyp.symm⟩), Set.ncard_pair (Ne.symm hne)]
    have h2 : σ (σ y) = y := by
      have h1 : σ (σ y) ∈ Fx := hHF σ hσ _ (hHF σ hσ _ hy)
      rw [hFeq] at h1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      rcases h1 with h | h | h
      · exact absurd (σ.injective (h.trans (hp σ hσ).symm)) hσyp
      · exact h
      · exact absurd (σ.injective h) hne
    have hpow : ∀ m : ℕ, (σ ^ (2 * m + 1)) y = σ y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show 2 * (m + 1) + 1 = 2 + (2 * m + 1) by ring, pow_add, Perm.mul_apply, ih, sq,
          Perm.mul_apply, h2]
    have h45 : σ ^ 45 = 1 := by
      have := pow_card_eq_one' (G := ↥H) (x := (⟨σ, hσ⟩ : ↥H))
      rw [hH] at this
      exact congrArg Subtype.val this
    have := hpow 22
    rw [show 2 * 22 + 1 = 45 by norm_num, h45] at this
    exact hne this.symm
  set F := Fx.toFinset with hFdef
  have hFc : F.card = 3 := by rw [hFdef, ← Set.ncard_eq_toFinset_card']; exact hF3
  have hle : H ≤ (Perm.ofSubtype : Perm {x // x ∉ F} →* Perm (Fin 8)).range := by
    intro σ hσ
    have hinv : ∀ x, (σ x ∉ F) ↔ (x ∉ F) := by
      intro x
      rw [hFdef, Set.mem_toFinset, Set.mem_toFinset]
      constructor
      · intro h hx
        apply h
        rw [hHfix σ hσ x hx]
        exact hx
      · intro h hx
        apply h
        have h1 : σ x = x := σ.injective (hHfix σ hσ _ hx)
        rw [h1] at hx
        exact hx
    refine ⟨σ.subtypePerm hinv, Perm.ofSubtype_subtypePerm hinv fun x hx => ?_⟩
    intro hxF
    rw [hFdef, Set.mem_toFinset] at hxF
    exact hx (hHfix σ hσ x hxF)
  have hcard := Subgroup.card_dvd_of_le hle
  rw [hH, Nat.card_congr (MonoidHom.ofInjective Perm.ofSubtype_injective).toEquiv.symm,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe, hFc] at hcard
  norm_num at hcard

theorem card_A6s : Nat.card A6s = 360 := by
  rw [A6s, Subgroup.card_map_of_injective Equiv.Perm.ofSubtype_injective]
  have : Nontrivial ↥six := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_six]
    norm_num
  rw [nat_card_alternatingGroup, card_six]
  rfl

theorem le_alternatingGroup_of_perfect {X : Subgroup (Perm (Fin 8))} (hXp : ⁅X, X⁆ = X) :
    X ≤ alternatingGroup (Fin 8) := by
  rw [← hXp]
  refine (Subgroup.commutator_mono le_top le_top).trans ?_
  intro σ hσ
  exact Perm.mem_alternatingGroup.2
    (Abelianization.commutator_subset_ker (Perm.sign : Perm (Fin 8) →* ℤˣ) hσ)

theorem false_of_index_seven {X : Subgroup ↥(alternatingGroup (Fin 8))} (h7 : X.index = 7) :
    False := by
  classical
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  set φ := MulAction.toPermHom ↥(alternatingGroup (Fin 8)) (↥(alternatingGroup (Fin 8)) ⧸ X)
    with hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, ← Subgroup.index_eq_card, h7, nat_card_alternatingGroup,
      Nat.card_fin] at this
    norm_num [Nat.factorial] at this
  · have h1 : X.normalCore = ⊤ := by rw [Subgroup.normalCore_eq_ker, ← hφ, h]
    have hX : X = ⊤ := eq_top_iff.2 (h1 ▸ Subgroup.normalCore_le X)
    rw [hX, Subgroup.index_top] at h7
    omega

theorem false_of_transitive_sup {X : Subgroup (Perm (Fin 8))} (hXp : ⁅X, X⁆ = X)
    {K : Subgroup ↥X} [K.Normal] {j : ℕ} (hj : Nat.card K = 2 ^ j)
    (hcard : Nat.card X = 360 * 2 ^ j) {x : Fin 8} (htrans : ∀ y : Fin 8, ∃ s : ↥X, s • x = y)
    (htop : MulAction.stabilizer ↥X x ⊔ K = ⊤) : False := by
  classical
  have hXA := le_alternatingGroup_of_perfect hXp
  have hKt : ∀ y : Fin 8, ∃ k : ↥K, k • x = y := by
    intro y
    obtain ⟨s, rfl⟩ := htrans y
    have hs : s ∈ ((K ⊔ MulAction.stabilizer ↥X x : Subgroup ↥X) : Set ↥X) := by
      rw [sup_comm, htop]
      trivial
    rw [Subgroup.normal_mul] at hs
    obtain ⟨k, hk, t, ht, rfl⟩ := hs
    refine ⟨⟨k, hk⟩, ?_⟩
    have ht' : t • x = x := MulAction.mem_stabilizer_iff.1 ht
    show k • x = (k * t) • x
    rw [mul_smul, ht']
  have h8K : 8 ∣ 2 ^ j := by
    rw [← hj]
    have h1 : (MulAction.orbit ↥K x).ncard = 8 := by
      have : MulAction.orbit ↥K x = Set.univ := Set.eq_univ_of_forall hKt
      rw [this, Set.ncard_univ, Nat.card_fin]
    have := Subgroup.index_dvd_card (MulAction.stabilizer ↥K x)
    rwa [MulAction.index_stabilizer, h1] at this
  have hdvd : 360 * 2 ^ j ∣ 20160 := by
    rw [← hcard]
    have := Subgroup.card_dvd_of_le hXA
    rwa [nat_card_alternatingGroup, Nat.card_fin] at this
  have hj3 : j = 3 := by
    have hj1 : 3 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j <;> norm_num at h8K
    have hj2 : j ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ∣ 2 ^ j := Nat.pow_dvd_pow 2 h
      have h1 : 360 * 2 ^ 4 ∣ 20160 := (Nat.mul_dvd_mul_left 360 this).trans hdvd
      norm_num at h1
    omega
  subst hj3
  have hidx : (X.subgroupOf (alternatingGroup (Fin 8))).index = 7 := by
    have h1 := (X.subgroupOf (alternatingGroup (Fin 8))).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXA).toEquiv, hcard,
      nat_card_alternatingGroup, Nat.card_fin] at h1
    norm_num [Nat.factorial] at h1
    omega
  exact false_of_index_seven hidx

theorem fix_two_or_transitive {X : Subgroup (Perm (Fin 8))} (hXp : ⁅X, X⁆ = X)
    (h7 : ¬ 7 ∣ Nat.card X) :
    (∃ a b : Fin 8, a ≠ b ∧ ∀ σ ∈ X, σ a = a ∧ σ b = b) ∨
      ∃ x : Fin 8, ∀ y : Fin 8, ∃ s : ↥X, s • x = y := by
  classical
  have hY : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = (⊤ : Subgroup ↥X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hXp]
  by_cases hno : ∃ a b : Fin 8, a ≠ b ∧ ∀ σ ∈ X, σ a = a ∧ σ b = b
  · exact Or.inl hno
  right
  have hfix1 : ∀ a b : Fin 8, (∀ s : ↥X, s • a = a) → (∀ s : ↥X, s • b = b) → a = b := by
    intro a b ha hb
    by_contra hab
    exact hno ⟨a, b, hab, fun σ hσ => ⟨ha ⟨σ, hσ⟩, hb ⟨σ, hσ⟩⟩⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin 8, ¬ ∀ s : ↥X, s • x = x := by
    by_contra h
    push Not at h
    exact absurd (hfix1 0 1 (h 0) (h 1)) (by decide)
  have hsmall : ∀ y : Fin 8, (¬ ∀ s : ↥X, s • y = y) → 5 ≤ (MulAction.orbit ↥X y).ncard := by
    intro y hy
    by_contra h
    push Not at h
    exact hy (smul_eq_of_ncard_orbit_le_four hY (by omega))
  have hle8 : ∀ A : Set (Fin 8), A.ncard ≤ 8 := fun A => by
    have := Set.ncard_le_ncard (Set.subset_univ A)
    rwa [Set.ncard_univ, Nat.card_fin] at this
  have hout : ∀ y, y ∉ MulAction.orbit ↥X x → ∀ s : ↥X, s • y = y := by
    intro y hy
    by_contra h
    have hdisj : Disjoint (MulAction.orbit ↥X x) (MulAction.orbit ↥X y) := by
      rw [Set.disjoint_left]
      intro z hzO hzy
      apply hy
      have h1 : MulAction.orbit ↥X z = MulAction.orbit ↥X x := MulAction.orbit_eq_iff.2 hzO
      have h2 : MulAction.orbit ↥X z = MulAction.orbit ↥X y := MulAction.orbit_eq_iff.2 hzy
      rw [← h1, h2]
      exact MulAction.mem_orbit_self y
    have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have h2 := hle8 (MulAction.orbit ↥X x ∪ MulAction.orbit ↥X y)
    have h3 := hsmall x hx
    have h4 := hsmall y h
    omega
  have hO7 : 7 ≤ (MulAction.orbit ↥X x).ncard := by
    have hc : (MulAction.orbit ↥X x)ᶜ.ncard ≤ 1 := by
      rw [Set.ncard_le_one]
      intro a ha b hb
      exact hfix1 a b (hout a ha) (hout b hb)
    have := Set.ncard_add_ncard_compl (MulAction.orbit ↥X x)
    rw [Nat.card_fin] at this
    omega
  have hOdvd : (MulAction.orbit ↥X x).ncard ∣ Nat.card X := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  have hO8 : (MulAction.orbit ↥X x).ncard = 8 := by
    have hle := hle8 (MulAction.orbit ↥X x)
    interval_cases h : (MulAction.orbit ↥X x).ncard
    · exact absurd hOdvd h7
    · rfl
  have huniv : MulAction.orbit ↥X x = Set.univ := Set.eq_of_subset_of_ncard_le
    (Set.subset_univ _) (by rw [Set.ncard_univ, Nat.card_fin, hO8]) (Set.toFinite _)
  refine ⟨x, fun y => ?_⟩
  have : y ∈ MulAction.orbit ↥X x := huniv ▸ Set.mem_univ y
  exact this

theorem false_of_transitive {X : Subgroup (Perm (Fin 8))} (hXp : ⁅X, X⁆ = X) {K : Subgroup ↥X}
    [K.Normal] {j : ℕ} (hj : Nat.card K = 2 ^ j) (hcard : Nat.card X = 360 * 2 ^ j) {x : Fin 8}
    (htrans : ∀ y : Fin 8, ∃ s : ↥X, s • x = y) : False := by
  classical
  have hY : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = (⊤ : Subgroup ↥X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hXp]
  set X₀ := MulAction.stabilizer ↥X x with hX₀
  have hX₀i : X₀.index = 8 := by
    rw [hX₀, MulAction.index_stabilizer]
    have huniv : MulAction.orbit ↥X x = Set.univ := Set.eq_univ_of_forall htrans
    rw [huniv, Set.ncard_univ, Nat.card_fin]
  set Hs := X₀ ⊔ K with hHs
  have hHi : Hs.index ∣ 8 := by
    have := Subgroup.index_dvd_of_le (le_sup_left : X₀ ≤ Hs)
    rwa [hX₀i] at this
  have hcases : Hs.index ≤ 4 ∨ Hs.index = 8 := by
    rcases Nat.lt_or_ge Hs.index 5 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Nat.eq_of_dvd_of_lt_two_mul (by norm_num) hHi (by omega)).symm
  rcases hcases with h4 | h8
  · exact false_of_transitive_sup hXp hj hcard htrans (eq_top_of_index_le_four hY h4)
  ·
    have hle : K ≤ X₀ := by
      have h1 : X₀.relIndex Hs = 1 := by
        have h2 := Subgroup.relIndex_mul_index (le_sup_left : X₀ ≤ Hs)
        rw [h8, hX₀i] at h2
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8) (by rw [h2, one_mul])
      exact le_sup_right.trans (Subgroup.relIndex_eq_one.1 h1)
    have hKbot : K = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      apply Equiv.ext
      intro y
      obtain ⟨s, rfl⟩ := htrans y
      have hks : s⁻¹ * k * s ∈ K := by
        have := ‹K.Normal›.conj_mem k hk s⁻¹
        simpa using this
      have h1 : (s⁻¹ * k * s) • x = x := MulAction.mem_stabilizer_iff.1 (hle hks)
      have h2 : k • s • x = s • x := by
        calc k • s • x = s • ((s⁻¹ * k * s) • x) := by
              rw [← mul_smul, ← mul_smul]
              group
          _ = s • x := by rw [h1]
      exact h2
    have h2j : 2 ^ j = 1 := by rw [← hj, hKbot, Subgroup.card_bot]
    rw [h2j, mul_one] at hcard
    have hX₀c : Nat.card X₀ = 45 := by
      have := X₀.card_mul_index
      rw [hX₀i, hcard] at this
      omega
    refine false_of_card_45 (H := X₀.map X.subtype) ?_ (p := x) ?_
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hX₀c]
    · rintro _ ⟨s, hs, rfl⟩
      exact MulAction.mem_stabilizer_iff.1 hs

theorem exists_fix_two_of_perfect {X : Subgroup (Perm (Fin 8))} (hXp : ⁅X, X⁆ = X)
    {K : Subgroup ↥X} [K.Normal] (hK2 : IsPGroup 2 ↥K) (hcard : Nat.card X = 360 * Nat.card K) :
    ∃ a b : Fin 8, a ≠ b ∧ ∀ σ ∈ X, σ a = a ∧ σ b = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hK2.exists_card_eq
  rw [hj] at hcard
  have h7 : ¬ 7 ∣ Nat.card X := by
    rw [hcard]
    intro h
    have h7 : (7 : ℕ).Prime := by norm_num
    rcases (Nat.Prime.dvd_mul h7).1 h with h | h
    · norm_num at h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow h7 h) (by norm_num)
  rcases fix_two_or_transitive hXp h7 with h | ⟨x, hx⟩
  · exact h
  · exact (false_of_transitive hXp hj hcard hx).elim

theorem eq_conj_A6s {X : Subgroup (Perm (Fin 8))} (hXp : ⁅X, X⁆ = X) {K : Subgroup ↥X}
    [K.Normal] (hK2 : IsPGroup 2 ↥K) (hcard : Nat.card X = 360 * Nat.card K) :
    ∃ τ ∈ alternatingGroup (Fin 8), X = A6s.map (MulAut.conj τ).toMonoidHom := by
  classical
  obtain ⟨a, b, hab, hfix⟩ := exists_fix_two_of_perfect hXp hK2 hcard
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 2 := by
    have h6 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 6 := by
      have := alternatingGroup.isMultiplyPretransitive (Fin 8)
      rwa [Nat.card_fin] at this
    exact MulAction.isMultiplyPretransitive_of_le (show 2 ≤ 6 by norm_num)
      (by rw [Nat.card_fin]; norm_num)
  let e : Fin 2 ↪ Fin 8 := ⟨![0, 1], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let e' : Fin 2 ↪ Fin 8 := ⟨![a, b], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm]⟩
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) e e'
  have hτi : ∀ i : Fin 2, (τ : Perm (Fin 8)) (e i) = e' i := fun i => by
    have := congrArg (fun f : Fin 2 ↪ Fin 8 => f i) hτ
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def] using this
  have hτ0 : (τ : Perm (Fin 8)) 0 = a := hτi 0
  have hτ1 : (τ : Perm (Fin 8)) 1 = b := hτi 1
  have hτ0' : (τ : Perm (Fin 8))⁻¹ a = 0 := by rw [Perm.inv_eq_iff_eq, hτ0]
  have hτ1' : (τ : Perm (Fin 8))⁻¹ b = 1 := by rw [Perm.inv_eq_iff_eq, hτ1]
  refine ⟨τ, τ.2, ?_⟩
  have hXA := le_alternatingGroup_of_perfect hXp
  have hle : X ≤ A6s.map (MulAut.conj (τ : Perm (Fin 8))).toMonoidHom := by
    intro σ hσ
    refine ⟨(τ : Perm (Fin 8))⁻¹ * σ * τ, mem_A6s.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Perm.mul_apply, Perm.mul_apply, hτ0, (hfix σ hσ).1, hτ0']
    · rw [Perm.mul_apply, Perm.mul_apply, hτ1, (hfix σ hσ).2, hτ1']
    · exact (alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).mul_mem
        ((alternatingGroup (Fin 8)).inv_mem τ.2) (hXA hσ)) τ.2
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, card_A6s, hcard]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

end S126T2

end CFSG.Quasithin.H13
