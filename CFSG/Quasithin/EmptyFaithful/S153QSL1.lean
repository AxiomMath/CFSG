module

public import CFSG.Quasithin.EmptyFaithful.S153QPD4

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin

section Derived

theorem solv2_of_surjective {Y Z : Type*} [Group Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) (h : IsPGroup 2 ↥⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆) :
    IsPGroup 2 ↥⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ := by
  have h1 : ⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ =
      (⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆).map π := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ]
  rw [h1]
  exact h.map π

theorem solv2_of_commutator {G : Type*} [Group G] (X : Subgroup G) (h : IsPGroup 2 ↥⁅X, X⁆) :
    IsPGroup 2 ↥⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ := by
  intro z
  have hz : (((z : ↥X) : G)) ∈ ⁅X, X⁆ := by
    have h1 : ((⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆).map X.subtype) = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← h1]
    exact ⟨_, z.2, rfl⟩
  obtain ⟨k, hk⟩ := h ⟨_, hz⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h2 := congrArg Subtype.val hk
  simpa using h2

end Derived

section Four

variable {F : Type} [Field F] [Finite F]

theorem false_of_solv2_normalizes_sl4 (hF : Nat.card F = 2)
    {X : Subgroup (SpecialLinearGroup (Fin 4) F)}
    (hN : unitriangular 4 F ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 4) F)))
    (hX : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆)
    {g : SpecialLinearGroup (Fin 4) F} (hgX : g ∈ X) (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := unitriangular 4 F with hU
  have hUp : IsPGroup 2 U :=
    IsPGroup.of_card (n := 6) (by rw [hU, card_unitriangular, hF])
  set A := X ⊔ U with hA
  have : Group.IsPerfect (SpecialLinearGroup (Fin 4) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl (by norm_num))
  by_cases hAtop : A = ⊤
  · have hXtop : X = ⊤ := eq_top_of_sup_isPGroup_of_isPerfect hUp hN hAtop
    have hφ : Function.Surjective X.subtype := fun g => ⟨⟨g, hXtop ▸ Subgroup.mem_top g⟩, rfl⟩
    have hG := solv2_of_surjective X.subtype hφ hX
    have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 4) F)),
        (⊤ : Subgroup (SpecialLinearGroup (Fin 4) F))⁆ = (⊤ : Subgroup (SpecialLinearGroup (Fin 4) F)) := by
      have := Group.isPerfect_def.1 (inferInstance : Group.IsPerfect (SpecialLinearGroup (Fin 4) F))
      rwa [commutator_def] at this
    rw [hperf] at hG
    obtain ⟨b, hb⟩ := hG.exists_card_eq
    rw [Subgroup.card_top] at hb
    have h7 : 7 ∣ 2 ^ b := by rw [← hb]; exact seven_dvd_card_sl_four hF
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7) (by norm_num)
  · obtain ⟨i, hi1, hi4, hAi⟩ := exists_le_stabilizer_of_ne_top (le_sup_right : U ≤ A) hAtop
    have hmem : g ∈ stabilizer (flagSpace 4 F i) := hAi (Subgroup.mem_sup_left hgX)
    refine false_of_stable_four hF (g := (g : Matrix (Fin 4) (Fin 4) F))
      ?_ ?_ (W := flagSpace 4 F i) (fun w hw => mulVec_mem_of_mem_stabilizer hmem hw) ?_ ?_
    · rw [← Matrix.SpecialLinearGroup.coe_pow, hg5, Matrix.SpecialLinearGroup.coe_one]
    · exact fun h => hg1 (Subtype.ext h)
    · rw [finrank_flagSpace hi4.le]; exact hi1
    · rw [finrank_flagSpace hi4.le]; omega

end Four

section Five

variable {F : Type} [Field F] [Finite F]

theorem false_of_block_four_solv2 (hF : Nat.card F = 2) {I : Set ℕ} {a : ℕ} (h : a + 4 ≤ 5)
    (ha : a = 0 ∨ a ∈ I) (hb : a + 4 = 5 ∨ a + 4 ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + 4))
    {X : Subgroup (SpecialLinearGroup (Fin 5) F)} (hXQ : X ≤ flagStabilizer 5 F I)
    (hN : unitriangular 5 F ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 5) F)))
    (hX : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆)
    {g : SpecialLinearGroup (Fin 5) F} (hgX : g ∈ X) (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 (unitriangular 5 F) :=
    IsPGroup.of_card (n := 10) (by rw [card_unitriangular, hF])
  set Q := flagStabilizer 5 F I with hQ
  have hL : BlockLeft Q a 4 := blockLeft_of_cut 4 ha
  have hR : BlockRight Q a 4 := blockRight_of_cut hb
  let ι : ↥X →* SpecialLinearGroup (Fin 4) F :=
    (blkSLTwo hF Q a 4 h hL hR).comp (Subgroup.inclusion hXQ)
  have hι_coe : ∀ z : ↥X, ((ι z : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkAt a 4 h ((z : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := fun z => rfl
  have hker : ∀ z : ↥X, ι z = 1 → (z : SpecialLinearGroup (Fin 5) F) ∈ unitriangular 5 F := by
    intro z hz
    have hzQ : (z : SpecialLinearGroup (Fin 5) F) ∈ Q := hXQ z.2
    refine mem_unitriangular_of_blocks hzQ fun a₂ m₂ h₂ ha₂ hb₂ hno₂ => ?_
    by_cases hm₂ : m₂ = 0
    · subst hm₂
      exact blkAt_zero a₂ h₂ _
    · rcases maxBlock_eq_or_disjoint h h₂ ha hb ha₂ hb₂ hno hno₂ with ⟨rfl, rfl⟩ | hd | hd
      · have := congrArg Subtype.val hz
        rw [hι_coe] at this
        exact this
      · obtain rfl : m₂ = 1 := by omega
        exact blkAt_one_eq_one hF Q a₂ h₂ (blockLeft_of_cut 1 ha₂) (blockRight_of_cut hb₂) ⟨_, hzQ⟩
      · obtain rfl : m₂ = 1 := by omega
        exact blkAt_one_eq_one hF Q a₂ h₂ (blockLeft_of_cut 1 ha₂) (blockRight_of_cut hb₂) ⟨_, hzQ⟩
  have hg1' : ι ⟨g, hgX⟩ ≠ 1 := by
    intro h1
    have hu := hker _ h1
    have h2 : orderOf (⟨g, hu⟩ : ↥(unitriangular 5 F)) ∣ 5 := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext hg5
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).mp hUp ⟨g, hu⟩
    rw [hk] at h2
    have h3 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num)) h2
    rw [h3, orderOf_eq_one_iff] at hk
    exact hg1 (by simpa using congrArg Subtype.val hk)
  have hg5' : (ι ⟨g, hgX⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨g, hgX⟩ : ↥X) ^ 5 = 1 := Subtype.ext (by simpa using hg5)
    rw [this, map_one]
  have hconj : ∀ u' ∈ unitriangular 4 F, ∀ h' ∈ ι.range, u' * h' * u'⁻¹ ∈ ι.range := by
    intro u' hu' h' hh'
    obtain ⟨p, rfl⟩ := hh'
    obtain ⟨u, huU, hublk⟩ := exists_emb a 4 h hu'
    have huQ : u ∈ Q :=
      upperTriangular_le_flagStabilizer I (unitriangular_le_upperTriangular 5 F huU)
    have hupu : u * (p : SpecialLinearGroup (Fin 5) F) * u⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hN huU) p).1 p.2
    refine ⟨⟨_, hupu⟩, ?_⟩
    have hb1 : blkSLTwo hF Q a 4 h hL hR ⟨u, huQ⟩ = u' := Subtype.ext hublk
    have hb2 : ι ⟨u * (p : SpecialLinearGroup (Fin 5) F) * u⁻¹, hupu⟩ =
        blkSLTwo hF Q a 4 h hL hR (⟨u, huQ⟩ * ⟨(p : SpecialLinearGroup (Fin 5) F), hXQ p.2⟩ *
          ⟨u, huQ⟩⁻¹) := rfl
    rw [hb2, map_mul, map_mul, map_inv, hb1]
    rfl
  have hNU : unitriangular 4 F ≤ Subgroup.normalizer (ι.range : Set (SpecialLinearGroup (Fin 4) F)) := by
    intro u' hu'
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    refine ⟨fun hh => hconj u' hu' h' hh, fun hh => ?_⟩
    have h3 := hconj u'⁻¹ (inv_mem hu') _ hh
    have e : u'⁻¹ * (u' * h' * u'⁻¹) * u'⁻¹⁻¹ = h' := by group
    rwa [e] at h3
  have hXr : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥ι.range), (⊤ : Subgroup ↥ι.range)⁆ :=
    solv2_of_surjective ι.rangeRestrict (MonoidHom.rangeRestrict_surjective ι) hX
  exact false_of_solv2_normalizes_sl4 hF hNU hXr (g := ι ⟨g, hgX⟩) ⟨_, rfl⟩ hg5' hg1'

theorem false_of_solv2_normalizes_sl5 (hF : Nat.card F = 2)
    {X : Subgroup (SpecialLinearGroup (Fin 5) F)}
    (hN : unitriangular 5 F ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 5) F)))
    (hX : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆)
    {g : SpecialLinearGroup (Fin 5) F} (hgX : g ∈ X) (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := unitriangular 5 F with hU
  have hUp : IsPGroup 2 U := IsPGroup.of_card (n := 10) (by rw [hU, card_unitriangular, hF])
  set A := X ⊔ U with hA
  have : Group.IsPerfect (SpecialLinearGroup (Fin 5) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl (by norm_num))
  by_cases hAtop : A = ⊤
  · have hXtop : X = ⊤ := eq_top_of_sup_isPGroup_of_isPerfect hUp hN hAtop
    have hφ : Function.Surjective X.subtype := fun g => ⟨⟨g, hXtop ▸ Subgroup.mem_top g⟩, rfl⟩
    have hG := solv2_of_surjective X.subtype hφ hX
    have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 5) F)),
        (⊤ : Subgroup (SpecialLinearGroup (Fin 5) F))⁆ = (⊤ : Subgroup (SpecialLinearGroup (Fin 5) F)) := by
      have := Group.isPerfect_def.1 (inferInstance : Group.IsPerfect (SpecialLinearGroup (Fin 5) F))
      rwa [commutator_def] at this
    rw [hperf] at hG
    obtain ⟨b, hb⟩ := hG.exists_card_eq
    rw [Subgroup.card_top] at hb
    have h7 : 7 ∣ 2 ^ b := by rw [← hb]; exact seven_dvd_card_sl_five hF
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7) (by norm_num)
  · obtain ⟨i, hi1, hi5, hAi⟩ := exists_le_stabilizer_of_ne_top (le_sup_right : U ≤ A) hAtop
    have hmem : g ∈ stabilizer (flagSpace 5 F i) := hAi (Subgroup.mem_sup_left hgX)
    have hi : i = 1 ∨ i = 4 := by
      by_contra hcon
      have h23 : 2 ≤ i ∧ i ≤ 3 := by omega
      refine false_of_stable_five hF (g := (g : Matrix (Fin 5) (Fin 5) F))
        ?_ ?_ (W := flagSpace 5 F i) (fun w hw => mulVec_mem_of_mem_stabilizer hmem hw) ?_ ?_
      · rw [← Matrix.SpecialLinearGroup.coe_pow, hg5, Matrix.SpecialLinearGroup.coe_one]
      · exact fun h => hg1 (Subtype.ext h)
      · rw [finrank_flagSpace hi5.le]; exact h23.1
      · rw [finrank_flagSpace hi5.le]; exact h23.2
    have hXQ : ∀ j : ℕ, X ≤ stabilizer (flagSpace 5 F j) → X ≤ flagStabilizer 5 F {j} := by
      intro j hj g hg
      rw [mem_flagStabilizer]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact hj hg
    have hXi : X ≤ stabilizer (flagSpace 5 F i) := (le_sup_left : X ≤ A).trans hAi
    rcases hi with rfl | rfl
    · exact false_of_block_four_solv2 hF (I := {1}) (a := 1) (by norm_num) (Or.inr rfl)
        (Or.inl rfl) (by intro c hc; rw [Set.mem_singleton_iff] at hc; omega) (hXQ 1 hXi) hN hX hgX
        hg5 hg1
    · exact false_of_block_four_solv2 hF (I := {4}) (a := 0) (by norm_num) (Or.inl rfl)
        (Or.inr rfl) (by intro c hc; rw [Set.mem_singleton_iff] at hc; omega) (hXQ 4 hXi) hN hX hgX
        hg5 hg1

end Five

end CFSG.Quasithin.QP
