module

public import CFSG.Holt.H78.Sec4SEAut

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Holt.H78 MulAction

theorem card_le_two_of_forall_eq {G : Type*} [Group G] [Finite G]
    (h : ∀ a b : G, a ≠ 1 → b ≠ 1 → a = b) : Nat.card G ≤ 2 := by
  by_contra hle
  have hlt : 2 < Nat.card G := not_le.mp hle
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hlt
  by_cases ha : a = 1
  · exact hbc (h b c (fun hb => hab (ha.trans hb.symm)) (fun hc => hac (ha.trans hc.symm)))
  · by_cases hb : b = 1
    · exact hac (h a c ha (fun hc => hbc (hb.trans hc.symm)))
    · exact hab (h a b ha hb)

theorem card_le_four_of_orbits_le_two {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}
    (hL : IsNaturalSE L) {F : Subgroup (Equiv.Perm Δ)}
    (hFN : F ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hF : ∀ f ∈ F, ∀ f' ∈ F, ∀ x : Δ, f x = x ∨ f' x = x ∨ f x = f' x) :
    Nat.card F ≤ 4 := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  have hsq : ∀ f ∈ F, f * f = 1 := by
    intro f hf
    ext x
    have h1 : f (f x) = x := by
      rcases hF f hf f⁻¹ (inv_mem hf) x with h | h | h
      · simp [h]
      · have h' : f x = x := (Equiv.Perm.inv_eq_iff_eq.mp h).symm
        simp [h']
      · rw [h]
        simp
    exact h1
  have hF2 : IsPGroup 2 F := fun f => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hsq f f.2)⟩
  have : (L.subgroupOf F).Normal := normal_subgroupOf_of_le_normalizer hFN
  have hq : Nat.card (↥F ⧸ L.subgroupOf F) ≤ 2 := by
    have hcyc : IsCyclic (↥F ⧸ L.subgroupOf F) := hL.isCyclic_quotient hF2 hFN
    have hsqQ : ∀ a : ↥F ⧸ L.subgroupOf F, a * a = 1 := fun a => by
      induction a using QuotientGroup.induction_on with
      | H f =>
        rw [← QuotientGroup.mk_mul, show f * f = 1 from Subtype.ext (hsq f f.2)]
        exact QuotientGroup.mk_one _
    exact card_le_two_of_forall_eq fun a b ha hb =>
      eq_of_mul_self_eq_one_of_isCyclic (hsqQ a) (hsqQ b) ha hb
  have hP : IsPGroup 2 (F.subgroupOf L) := fun p => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext (hsq _ p.2))⟩
  obtain ⟨ω, hω⟩ := hA.exists_le_stabilizer hP
  have hfixω : ∀ a ∈ L, a ∈ F → a ω = ω := fun a haL haF => by
    have := hω (show (⟨a, haL⟩ : ↥L) ∈ F.subgroupOf L from haF)
    rw [mem_stabilizer_iff] at this
    exact this
  have hnt : Nontrivial Δ := by
    have := hL.odd_card_and_five_le
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨μ, hμω⟩ := exists_ne ω
  have hmove : ∀ c ∈ L, c ∈ F → c ≠ 1 → c μ ≠ μ := fun c hcL hcF hc1 hcμ =>
    hc1 (hL.eq_one_of_mem_seRadical (mem_seRadical_of_pow_eq_one hcL (hfixω c hcL hcF) (k := 1)
      (by rw [pow_one, sq]; exact hsq c hcF)) hμω hcμ)
  have key : ∀ a b : Equiv.Perm Δ, a ∈ F → a ∈ L → b ∈ F → b ∈ L → a ≠ 1 → b ≠ 1 → a = b := by
    intro a b haF haL hbF hbL ha1 hb1
    have hab : a μ = b μ :=
      ((hF a haF b hbF μ).resolve_left (hmove a haL haF ha1)).resolve_left (hmove b hbL hbF hb1)
    have hc : a⁻¹ * b = 1 := by
      by_contra hc1
      refine hmove (a⁻¹ * b) (mul_mem (inv_mem haL) hbL) (mul_mem (inv_mem haF) hbF) hc1 ?_
      rw [Equiv.Perm.mul_apply, ← hab]
      simp
    exact inv_mul_eq_one.mp hc
  have hF0 : Nat.card ↥(L.subgroupOf F) ≤ 2 := by
    refine card_le_two_of_forall_eq fun a b ha hb => ?_
    have ha' := Subgroup.mem_subgroupOf.mp a.2
    have hb' := Subgroup.mem_subgroupOf.mp b.2
    refine Subtype.ext (Subtype.ext (key _ _ (a : ↥F).2 ha' (b : ↥F).2 hb' ?_ ?_))
    · exact fun h => ha (Subtype.ext (Subtype.ext h))
    · exact fun h => hb (Subtype.ext (Subtype.ext h))
  calc Nat.card F = Nat.card (↥F ⧸ L.subgroupOf F) * Nat.card ↥(L.subgroupOf F) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ ≤ 2 * 2 := Nat.mul_le_mul hq hF0

theorem exists_finset_two_cycles {Δ : Type*} [Finite Δ] {y : Equiv.Perm Δ} (hy : y * y = 1)
    {k : ℕ} (hk : 2 * k ≤ {x : Δ | y x ≠ x}.ncard) :
    ∃ R : Finset Δ, k ≤ R.card ∧ ∀ x ∈ R, y x ≠ x ∧ y x ∉ R := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat Δ
  have hyy : ∀ x, y (y x) = x := fun x => by
    have := congrArg (fun π : Equiv.Perm Δ => π x) hy
    simpa [Equiv.Perm.mul_apply] using this
  obtain ⟨R, hmem⟩ : ∃ R : Finset Δ, ∀ x, x ∈ R ↔ f x < f (y x) :=
    ⟨(Set.toFinite {x : Δ | f x < f (y x)}).toFinset, fun x => by simp⟩
  refine ⟨R, ?_, fun x hx => ?_⟩
  · have hsub : {x : Δ | y x ≠ x} ⊆ (R : Set Δ) ∪ y '' (R : Set Δ) := by
      intro x hx
      rcases lt_trichotomy (f x) (f (y x)) with h | h | h
      · exact Or.inl ((hmem x).mpr h)
      · exact absurd (hf h).symm hx
      · exact Or.inr ⟨y x, (hmem _).mpr (by rw [hyy]; exact h), hyy x⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (R : Set Δ) (y '' (R : Set Δ))
    have h3 : (y '' (R : Set Δ)).ncard ≤ (R : Set Δ).ncard := Set.ncard_image_le (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h2 h3
    omega
  · have hx' := (hmem x).mp hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at hx'
      exact lt_irrefl _ hx'
    · have := (hmem _).mp h
      rw [hyy] at this
      omega

theorem exists_fixed_two_mul_le {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}
    (hL : IsNaturalSE L) {y : Equiv.Perm Δ}
    (hyN : y ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ ω : Δ, y ω = ω ∧ 2 * {c : Δ | y c = c ∧ c ≠ ω}.ncard ≤ Nat.card (seRadical L ω) := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  have hP : IsPGroup 2 (Subgroup.zpowers y) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq]; exact hy)
  obtain ⟨ω, hω⟩ := CFSG.Holt.fixSet_nonempty_of_odd (Ω := Δ) hA.odd_card hP
  have hyω : y ω = ω := (CFSG.Holt.mem_fixSet.mp hω) y (Subgroup.mem_zpowers y)
  refine ⟨ω, hyω, ?_⟩
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  by_cases hex : ∃ μ : Δ, μ ≠ ω ∧ y μ = μ
  swap
  · have : {c : Δ | y c = c ∧ c ≠ ω} = ∅ :=
      Set.eq_empty_of_forall_notMem fun c hc => hex ⟨c, hc.2, hc.1⟩
    rw [this, Set.ncard_empty]
    simp
  obtain ⟨μ, hμω, hyμ⟩ := hex
  have hconj : ∀ r ∈ seRadical L ω, y * r * y⁻¹ ∈ seRadical L ω := fun r hr =>
    conj_mem_seRadical hyN hyω hr
  set C : Subgroup (Equiv.Perm Δ) :=
    seRadical L ω ⊓ Subgroup.centralizer ({y} : Set (Equiv.Perm Δ)) with hC
  have hCle : C ≤ seRadical L ω := inf_le_left
  have hS : {c : Δ | y c = c ∧ c ≠ ω} ⊆
      (fun r : Equiv.Perm Δ => r μ) '' (C : Set (Equiv.Perm Δ)) := by
    rintro c ⟨hyc, hcω⟩
    obtain ⟨r, hrR, hrc⟩ := hL.exists_mem_seRadical_apply_eq hμω hcω
    refine ⟨r, ⟨hrR, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hrc⟩
    have h1 : r⁻¹ * (y * r * y⁻¹) = 1 := by
      refine hL.eq_one_of_mem_seRadical (mul_mem (inv_mem hrR) (hconj r hrR)) hμω ?_
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hyi, hyμ, hrc, hyc]
      exact Equiv.Perm.inv_eq_iff_eq.mpr hrc.symm
    have h2 : y * r * y⁻¹ = r := (inv_mul_eq_one.mp h1).symm
    calc r * y = y * r * y⁻¹ * y := by rw [h2]
      _ = y * r := by group
  have h1 : {c : Δ | y c = c ∧ c ≠ ω}.ncard ≤ Nat.card C :=
    calc _ ≤ ((fun r : Equiv.Perm Δ => r μ) '' (C : Set (Equiv.Perm Δ))).ncard :=
          Set.ncard_le_ncard hS (Set.toFinite _)
      _ ≤ (C : Set (Equiv.Perm Δ)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card C := (Nat.card_coe_set_eq _).symm
  have h2 : 2 * Nat.card C ≤ Nat.card (seRadical L ω) := by
    have hdvd : Nat.card C ∣ Nat.card (seRadical L ω) := Subgroup.card_dvd_of_le hCle
    have hlt : Nat.card C < Nat.card (seRadical L ω) := by
      refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun hEq => ?_
      have hCR : C = seRadical L ω := Subgroup.eq_of_le_of_card_ge hCle hEq.symm.le
      apply hy1
      ext c
      by_cases hcω : c = ω
      · rw [hcω]
        exact hyω
      · obtain ⟨r, hrR, hrc⟩ := hL.exists_mem_seRadical_apply_eq hμω hcω
        have hrC : r ∈ C := by rw [hCR]; exact hrR
        have hcomm : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.mp hrC.2
        calc y c = y (r μ) := by rw [hrc]
          _ = (y * r) μ := rfl
          _ = (r * y) μ := by rw [hcomm]
          _ = r (y μ) := rfl
          _ = c := by rw [hyμ, hrc]
    obtain ⟨k, hk⟩ := hdvd
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hk2 : 2 ≤ k := by
      by_contra hge
      have hk2 : k < 2 := not_le.mp hge
      interval_cases k <;> omega
    calc 2 * Nat.card C ≤ k * Nat.card C := Nat.mul_le_mul_right _ hk2
      _ = Nat.card (seRadical L ω) := by rw [hk, mul_comm]
  exact (Nat.mul_le_mul_left 2 h1).trans h2

theorem exists_four_two_cycles {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}
    (hL : IsNaturalSE L) (h9 : 9 ≤ Nat.card Δ) {y : Equiv.Perm Δ}
    (hyN : y ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ R : Finset Δ, 4 ≤ R.card ∧ ∀ x ∈ R, y x ≠ x ∧ y x ∉ R := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  have hN : Nat.card Δ = (2 ^ n) ^ i + 1 := hA.card_eq
  have hcompl : {x : Δ | y x = x}.ncard + {x : Δ | y x ≠ x}.ncard = Nat.card Δ :=
    Set.ncard_add_ncard_compl _
  have h8 : 8 ≤ {x : Δ | y x ≠ x}.ncard := by
    by_cases hyL : y ∈ L
    · have hord : orderOf (⟨y, hyL⟩ : ↥L) = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine orderOf_eq_prime ?_ ?_
        · rw [sq]
          exact Subtype.ext hy
        · intro h
          exact hy1 (congrArg Subtype.val h)
      obtain ⟨ω, hω, huniq⟩ := hA.existsUnique_fixed hord
      have hfix : {x : Δ | y x = x} = {ω} := by
        ext x
        constructor
        · intro hx
          exact huniq x hx
        · intro hx
          rw [Set.mem_singleton_iff.mp hx]
          exact hω
      rw [hfix, Set.ncard_singleton] at hcompl
      omega
    · have h16 : 16 ≤ (2 ^ n) ^ i := by
        by_contra hge
        have hlt : (2 ^ n) ^ i < 16 := not_le.mp hge
        obtain ⟨hi1, hi3, hn2⟩ := hA.params
        have hN8 : 8 ≤ (2 ^ n) ^ i := by omega
        have hmul : (2 ^ n) ^ i = 2 ^ (n * i) := (pow_mul 2 n i).symm
        have hni : n * i = 3 := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have : 2 ^ (n * i) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          · have : 2 ^ 4 ≤ 2 ^ (n * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
        have hi : i = 1 := by
          by_contra hne
          have h2 : 2 ≤ i := by omega
          have := Nat.mul_le_mul hn2 h2
          omega
        subst hi
        have hn : n = 3 := by omega
        subst hn
        have he : e = 1 := by
          rcases hA.benderType.cases' with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
        subst he
        obtain ⟨-, hcard⟩ := hA.benderType.outer_linear
        have hz2 : normalizerOuterHom L ⟨y, hyN⟩ ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set (Equiv.Perm Δ))) ^ 2 = 1 := by
            rw [sq]
            exact Subtype.ext hy
          rw [this, map_one]
        have hz3 : normalizerOuterHom L ⟨y, hyN⟩ ^ 3 = 1 := by
          rw [← hcard]
          exact pow_card_eq_one'
        have hz1 : normalizerOuterHom L ⟨y, hyN⟩ = 1 := by
          have h : normalizerOuterHom L ⟨y, hyN⟩ ^ 3 =
              normalizerOuterHom L ⟨y, hyN⟩ ^ 2 * normalizerOuterHom L ⟨y, hyN⟩ := pow_succ _ _
          rw [hz3, hz2, one_mul] at h
          exact h.symm
        exact hyL ((hL.normalizerOuterHom_eq_one_iff ⟨y, hyN⟩).mp hz1)
      obtain ⟨ω, hω, hle⟩ := exists_fixed_two_mul_le hL hyN hy hy1
      rw [hA.card_seRadical ω] at hle
      have hfix : {x : Δ | y x = x}.ncard ≤ {c : Δ | y c = c ∧ c ≠ ω}.ncard + 1 := by
        refine le_trans (Set.ncard_le_ncard (t := insert ω {c : Δ | y c = c ∧ c ≠ ω})
          (fun x hx => ?_) (Set.toFinite _)) (Set.ncard_insert_le _ _)
        by_cases hxω : x = ω
        · exact Or.inl hxω
        · exact Or.inr ⟨hx, hxω⟩
      omega
  obtain ⟨R, hR⟩ := exists_finset_two_cycles hy (k := 4) (by omega)
  exact ⟨R, hR⟩

end CFSG.Quasithin.SzVB
