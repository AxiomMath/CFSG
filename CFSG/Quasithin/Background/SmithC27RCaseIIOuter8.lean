module

public import CFSG.Quasithin.Background.SmithC27RCaseIIPerm8
public import CFSG.Quasithin.Background.SmithC27RCaseIIPar8
public import CFSG.Quasithin.Background.SmithC27RCaseIIStd8

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm MulAction

theorem transitive_eight {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P) (hrad : IsRadSig P)
    (hodd : ¬ P ≤ alternatingGroup (Fin 8)) (htr : ∀ x y : Fin 8, ∃ g ∈ P, g x = y) :
    ∃ T : Subgroup (Perm (Fin 8)), IsSylowTwoOf T ⊤ ∧
      T ≤ Subgroup.normalizer (P : Set (Perm (Fin 8))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcP, hc2, hc1, hcc⟩ : ∃ c : Perm (Fin 8), c ∈ P ∧ c * c = 1 ∧ c ≠ 1 ∧
      ∀ g ∈ P, g * c = c * g := by
    have hne : Nontrivial ↥P := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      rintro rfl
      exact hodd bot_le
    obtain ⟨n, hn, hcard⟩ :=
      (hP.to_subgroup (Subgroup.center ↥P)).nontrivial_iff_card.1 hP.center_nontrivial
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2
      (by rw [hcard]; exact dvd_pow_self 2 (by omega))
    refine ⟨((x : ↥P) : Perm (Fin 8)), (x : ↥P).2, ?_, ?_, fun g hg => ?_⟩
    · have h1 := pow_orderOf_eq_one x
      rw [hx, pow_two] at h1
      exact congrArg (fun y : ↥(Subgroup.center ↥P) => ((y : ↥P) : Perm (Fin 8))) h1
    · intro h1
      have : x = 1 := Subtype.ext (Subtype.ext h1)
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 x.2 ⟨g, hg⟩)
  have hfpf : ∀ c' : Perm (Fin 8), c' ≠ 1 → (∀ g ∈ P, g * c' = c' * g) → ∀ x, c' x ≠ x :=
    fun c' hc' hcc' x hx => hc' (eq_one_of_mem_center_of_apply_eq htr hcc' hx)
  by_cases huniq : ∀ c' : Perm (Fin 8), c' ∈ P → c' * c' = 1 → c' ≠ 1 →
      (∀ g ∈ P, g * c' = c' * g) → c' = c
  ·
    have hNc : Subgroup.normalizer (P : Set (Perm (Fin 8))) ≤ Subgroup.centralizer {c} := by
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : m * c * m⁻¹ = c := by
        refine huniq _ (conj_mem_of_mem_normalizer hm hcP) ?_ ?_ ?_
        · calc m * c * m⁻¹ * (m * c * m⁻¹) = m * (c * c) * m⁻¹ := by group
            _ = 1 := by rw [hc2, mul_one, mul_inv_cancel]
        · intro h
          apply hc1
          calc c = m⁻¹ * (m * c * m⁻¹) * m := by group
            _ = 1 := by rw [h]; group
        · intro g hg
          have hg' : m⁻¹ * g * m ∈ P := by
            have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hm) hg
            simpa using this
          have h2 := hcc _ hg'
          calc g * (m * c * m⁻¹) = m * (m⁻¹ * g * m * c) * m⁻¹ := by group
            _ = m * (c * (m⁻¹ * g * m)) * m⁻¹ := by rw [h2]
            _ = m * c * m⁻¹ * g := by group
      calc m * c = m * c * m⁻¹ * m := by group
        _ = c * m := by rw [h1]
    have hS : swapGroupOf c hc2 ≤ P :=
      hrad _ (isPGroup_swapGroupOf hc2) (by rw [normalizer_swapGroupOf]; exact hNc)
    apply exists_sylow_le_normalizer_of_sixtyFour_le hP
    have hS16 : Nat.card (swapGroupOf c hc2) = 16 := card_swapGroupOf_eight hc2 (hfpf c hc1 hcc)
    have horbS : (orbit ↥(swapGroupOf c hc2) (0 : Fin 8)).ncard ≤ 2 := by
      have hsub : orbit ↥(swapGroupOf c hc2) (0 : Fin 8) ⊆ {0, c 0} := by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.1 hy
        exact hg 0
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have horbP : (orbit ↥P (0 : Fin 8)).ncard = 8 := by
      have huniv : orbit ↥P (0 : Fin 8) = Set.univ :=
        Set.eq_univ_of_forall fun y => mem_orbit_subgroup_iff.2 (htr 0 y)
      rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hstab : Nat.card (stabilizer ↥(swapGroupOf c hc2) (0 : Fin 8)) ≤
        Nat.card (stabilizer ↥P (0 : Fin 8)) := by
      let f : ↥(stabilizer ↥(swapGroupOf c hc2) (0 : Fin 8)) → ↥(stabilizer ↥P (0 : Fin 8)) :=
        fun g => ⟨⟨((g : ↥(swapGroupOf c hc2)) : Perm (Fin 8)), hS (g : ↥(swapGroupOf c hc2)).2⟩,
          g.2⟩
      refine Nat.card_le_card_of_injective f fun g g' h => ?_
      have := congrArg (fun y : ↥(stabilizer ↥P (0 : Fin 8)) => ((y : ↥P) : Perm (Fin 8))) h
      exact Subtype.ext (Subtype.ext this)
    have h1 := Subgroup.card_mul_index (stabilizer ↥P (0 : Fin 8))
    rw [index_stabilizer, horbP] at h1
    have h2 := Subgroup.card_mul_index (stabilizer ↥(swapGroupOf c hc2) (0 : Fin 8))
    rw [index_stabilizer, hS16] at h2
    have h3 := Nat.mul_le_mul_left (Nat.card (stabilizer ↥(swapGroupOf c hc2) (0 : Fin 8))) horbS
    omega
  ·
    push Not at huniq
    obtain ⟨c', hc'P, hc'2, hc'1, hcc', hne⟩ := huniq
    exfalso
    apply hodd
    have hcc'1 : c * c' ≠ 1 := by
      intro h
      apply hne
      have h' := eq_inv_of_mul_eq_one_right h
      rwa [inv_eq_of_mul_eq_one_right hc2] at h'
    have hcen : ∀ g ∈ P, g * (c * c') = c * c' * g := fun g hg => by
      calc g * (c * c') = g * c * c' := by group
        _ = c * g * c' := by rw [hcc g hg]
        _ = c * (g * c') := by group
        _ = c * (c' * g) := by rw [hcc' g hg]
        _ = c * c' * g := by group
    intro g hg
    rw [Perm.mem_alternatingGroup]
    exact sign_eq_one_of_commute_semiregular hc2 hc'2 (hcc c' hc'P).symm (hfpf c hc1 hcc)
      (hfpf c' hc'1 hcc') (fun x => hfpf (c * c') hcc'1 hcen x) (hcc g hg) (hcc' g hg)

theorem four_orbit_eight {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P) (hrad : IsRadSig P)
    (hodd : ¬ P ≤ alternatingGroup (Fin 8)) {x₀ : Fin 8} (hx₀ : Nat.card (orbit ↥P x₀) = 4) :
    (∃ T : Subgroup (Perm (Fin 8)), IsSylowTwoOf T ⊤ ∧
        T ≤ Subgroup.normalizer (P : Set (Perm (Fin 8)))) ∨
      ∃ g : Perm (Fin 8), P.map (MulAut.conj g).toMonoidHom = d8v4 := by
  classical
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Set (Fin 8), orbit ↥P x₀ = Θ := ⟨_, rfl⟩
  rw [hΘ] at hx₀
  have hΘ4 : Θ.ncard = 4 := by rw [← Nat.card_coe_set_eq, hx₀]
  have hΘc : Θᶜ.ncard = 4 := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin, hΘ4]
  have horbΘ : ∀ y, y ∈ Θ → orbit ↥P y = Θ := fun y hy => by
    rw [← hΘ] at hy ⊢
    exact mem_orbit_of_mem_orbit hy
  have hsub : ∀ y, y ∉ Θ → orbit ↥P y ⊆ Θᶜ := by
    intro y hy w hw hwΘ
    apply hy
    rw [← horbΘ w hwΘ, mem_orbit_of_mem_orbit hw]
    exact mem_orbit_self (M := ↥P) y
  by_cases h44 : ∃ y, y ∉ Θ ∧ Nat.card (orbit ↥P y) = 4
  swap
  ·
    exfalso
    push Not at h44
    have hΘiff : ∀ y, y ∈ Θ ↔ Nat.card (orbit ↥P y) = 4 := by
      intro y
      constructor
      · intro hy
        rw [horbΘ y hy]
        exact hx₀
      · intro hy
        by_contra hyΘ
        exact h44 y hyΘ hy
    have hinv : ∀ m ∈ Subgroup.normalizer (P : Set (Perm (Fin 8))), ∀ x,
        m x ∈ Θᶜ ↔ x ∈ Θᶜ := by
      intro m hm x
      show m x ∉ Θ ↔ x ∉ Θ
      rw [hΘiff, hΘiff, card_orbit_apply hm]
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, habcd⟩ :=
      exists_eq_quad_of_ncard_eq_four hΘc
    have hK : kleinOf Θᶜ ≤ P := by
      refine hrad.kleinOf_le ?_ hinv
      rw [habcd]
      exact isPGroup_kleinOf_quad hab hac had hbc hbd hcd
    rw [habcd] at hK
    obtain ⟨hb, hc, hd⟩ := mem_orbit_of_kleinOf_le hab hac had hbc hbd hcd hK
    have haΘ : a ∉ Θ := by
      have : a ∈ Θᶜ := by
        rw [habcd]
        exact Or.inl rfl
      exact this
    have heq : orbit ↥P a = Θᶜ := by
      refine Set.Subset.antisymm (hsub a haΘ) ?_
      rw [habcd]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with h | h | h | h <;> rw [h]
      exacts [mem_orbit_self (M := ↥P) a, hb, hc, hd]
    exact h44 a haΘ (by rw [heq, Nat.card_coe_set_eq, hΘc])
  obtain ⟨y₀, hy₀Θ, hy₀⟩ := h44
  have hΘ2 : orbit ↥P y₀ = Θᶜ := Set.eq_of_subset_of_ncard_le (hsub y₀ hy₀Θ)
    (by rw [hΘc, ← Nat.card_coe_set_eq, hy₀])
  have hmΘ : ∀ m ∈ Subgroup.normalizer (P : Set (Perm (Fin 8))),
      (m : Fin 8 → Fin 8) '' Θ = Θ ∨ (m : Fin 8 → Fin 8) '' Θ = Θᶜ := by
    intro m hm
    rw [← hΘ, ← orbit_apply_eq_image hm x₀, hΘ]
    by_cases hmx : m x₀ ∈ Θ
    · exact Or.inl (horbΘ _ hmx)
    · right
      rw [← hΘ2]
      apply mem_orbit_of_mem_orbit
      rw [hΘ2]
      exact hmx
  have hWN : Subgroup.normalizer (P : Set (Perm (Fin 8))) ≤
      Subgroup.normalizer ((kleinOf Θ ⊔ kleinOf Θᶜ : Subgroup (Perm (Fin 8))) :
        Set (Perm (Fin 8))) := by
    intro m hm
    apply mem_normalizer_of_map_conj_eq
    rw [map_conj_kleinOf_sup, Set.image_compl_eq m.bijective]
    rcases hmΘ m hm with h | h <;> rw [h]
    rw [compl_compl, sup_comm]
  obtain ⟨h, hh⟩ : ∃ h : Perm (Fin 8), ∀ x, (h x : ℕ) < 4 ↔ x ∈ Θ := by
    have hcard : Fintype.card {x // x ∈ Θ} = Fintype.card {x : Fin 8 // (x : ℕ) < 4} := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      show Nat.card ↥Θ = _
      rw [Nat.card_coe_set_eq, hΘ4, Nat.card_eq_fintype_card]
      rfl
    let e := Fintype.equivOfCardEq hcard
    refine ⟨e.extendSubtype, fun x => ⟨fun hx => ?_, fun hx => Equiv.extendSubtype_mem e x hx⟩⟩
    by_contra hxΘ
    exact Equiv.extendSubtype_not_mem e x hxΘ hx
  have himg : (h : Fin 8 → Fin 8) '' Θ = {x : Fin 8 | (x : ℕ) < 4} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hh x).2 hx
    · intro hy
      refine ⟨h⁻¹ y, (hh _).1 ?_, by simp⟩
      simpa using hy
  have hWV : (kleinOf Θ ⊔ kleinOf Θᶜ).map (MulAut.conj h).toMonoidHom = Claim2526.V8 := by
    rw [map_conj_kleinOf_sup, Set.image_compl_eq h.bijective, himg, V8_eq_kleinOf_sup]
  have hWc : Nat.card ↥(kleinOf Θ ⊔ kleinOf Θᶜ) = 16 := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective, hWV, card_V8]
  have hWP : kleinOf Θ ⊔ kleinOf Θᶜ ≤ P :=
    hrad _ (IsPGroup.of_card (n := 4) (by rw [hWc]; norm_num)) hWN
  have hV8P' : Claim2526.V8 ≤ P.map (MulAut.conj h).toMonoidHom := by
    rw [← hWV]
    exact Subgroup.map_mono hWP
  have hP' : IsPGroup 2 (P.map (MulAut.conj h).toMonoidHom) := hP.map _
  have hcardP' : Nat.card (P.map (MulAut.conj h).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
  have hΘP : ∀ g ∈ P, ∀ y, g y ∈ Θ ↔ y ∈ Θ := fun g hg y => by
    rw [← hΘ]
    exact apply_mem_orbit_of_mem hg x₀ y
  have hstab' : ∀ g ∈ P.map (MulAut.conj h).toMonoidHom, ∀ x : Fin 8,
      (x : ℕ) < 4 ↔ (g x : ℕ) < 4 := by
    rintro _ ⟨g, hg, rfl⟩ x
    show (x : ℕ) < 4 ↔ ((h * g * h⁻¹) x : ℕ) < 4
    rw [Perm.mul_apply, Perm.mul_apply, hh, hΘP g hg, ← hh]
    simp
  have hodd' : ¬ P.map (MulAut.conj h).toMonoidHom ≤ alternatingGroup (Fin 8) := by
    intro hle
    apply hodd
    intro g hg
    have h1 := Perm.mem_alternatingGroup.1 (hle ⟨g, hg, rfl⟩)
    change sign (h * g * h⁻¹) = 1 at h1
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at h1
    exact Perm.mem_alternatingGroup.2 h1
  obtain ⟨k, hk⟩ := hP'.exists_card_eq
  have h16 : 16 ∣ 2 ^ k := by
    rw [← hk, ← card_V8]
    exact Subgroup.card_dvd_of_le hV8P'
  have hne16 : 2 ^ k ≠ 16 := by
    intro he
    apply hodd'
    have : Claim2526.V8 = P.map (MulAut.conj h).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hV8P' (by rw [hk, he, card_V8])
    rw [← this]
    exact V8_le_alt
  have hk5 : 5 ≤ k := by
    by_contra hk5
    have h1 : 2 ^ k ∣ 2 ^ 4 := Nat.pow_dvd_pow 2 (by omega)
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := Nat.le_of_dvd (by positivity) h16
    omega
  rcases (by omega : k = 5 ∨ 6 ≤ k) with rfl | hk6
  · right
    obtain ⟨h', hh'⟩ := std44_classify hP' hstab' hV8P' hodd' (by rw [hk]; norm_num)
    refine ⟨h' * h, ?_⟩
    rw [← hh', Subgroup.map_map]
    congr 1
  · left
    apply exists_sylow_le_normalizer_of_sixtyFour_le hP
    rw [← hcardP', hk]
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk6

theorem radical_outer_eight {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P)
    (hrad : IsRadSig P) (hodd : ¬ P ≤ alternatingGroup (Fin 8)) :
    (∃ T : Subgroup (Perm (Fin 8)), IsSylowTwoOf T ⊤ ∧
        T ≤ Subgroup.normalizer (P : Set (Perm (Fin 8)))) ∨
      (∃ a b : Fin 8, a ≠ b ∧ P = Subgroup.zpowers (swap a b)) ∨
      ∃ g : Perm (Fin 8), P.map (MulAut.conj g).toMonoidHom = d8v4 := by
  rcases fix_cases_eight hP hrad hodd with hfree | hB
  · by_cases h8 : ∃ x : Fin 8, Nat.card (orbit ↥P x) = 8
    · obtain ⟨x, hx⟩ := h8
      exact Or.inl (transitive_eight hP hrad hodd (forall_exists_apply_eq_of_card_orbit hx))
    by_cases h4 : ∃ x : Fin 8, Nat.card (orbit ↥P x) = 4
    · obtain ⟨x, hx⟩ := h4
      rcases four_orbit_eight hP hrad hodd hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    push Not at h8 h4
    refine Or.inl (pairs_eight hrad fun x => ?_)
    rcases card_orbit_cases_eight hP hfree x with h | h | h
    · exact h
    · exact absurd h (h4 x)
    · exact absurd h (h8 x)
  · exact Or.inr (Or.inl hB)

end CFSG.Quasithin.SmithC27
