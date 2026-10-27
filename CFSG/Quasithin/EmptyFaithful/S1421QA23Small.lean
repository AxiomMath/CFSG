module

public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Quasithin.Background.A312SporShapes

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace QA23

theorem card_dvd_factorial_index {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {P : Subgroup Q} (hP : P ≠ ⊤) : Nat.card Q ∣ (P.index).factorial := by
  let f : Q →* Equiv.Perm (Q ⧸ P) := MulAction.toPermHom Q (Q ⧸ P)
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      apply hP
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ f.ker := by rw [h]; trivial
      have h1 : f g (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
        rw [MonoidHom.mem_ker] at hg
        rw [hg]
        rfl
      have h2 : (QuotientGroup.mk (g * 1) : Q ⧸ P) = QuotientGroup.mk 1 := h1
      rw [mul_one, QuotientGroup.eq, mul_one] at h2
      simpa using P.inv_mem h2
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have := Subgroup.card_dvd_of_injective f hinj
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at this

theorem sixty_le_card_of_perfect {Q : Type} [Group Q] [Finite Q] {K : Subgroup Q}
    (hK : ⁅K, K⁆ = K) (hne : K ≠ ⊥) : 60 ≤ Nat.card K := by
  by_contra hlt
  push Not at hlt
  have hs := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  exact Group.IsPerfect.not_isSolvable ↥K hs

theorem exists_overgroup_bar {X : Type} [Group X] [Finite X] (hXq : CFSG.IsQuasisimple X)
    {U K : Subgroup X} (hKU : K ⊔ U ≠ ⊤) :
    ∃ P : Subgroup (X ⧸ Subgroup.center X),
      K.map (QuotientGroup.mk' (Subgroup.center X)) ≤ P ∧
        U.map (QuotientGroup.mk' (Subgroup.center X)) ≤ P ∧ P ≠ ⊤ := by
  refine ⟨(K ⊔ U).map (QuotientGroup.mk' (Subgroup.center X)),
    Subgroup.map_mono le_sup_left, Subgroup.map_mono le_sup_right, ?_⟩
  intro htop
  apply hKU
  have h1 : K ⊔ U ⊔ Subgroup.center X = ⊤ := by
    have := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center X))) htop
    rwa [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
  have hnorm : (K ⊔ U).Normal := by
    have hle : K ⊔ U ⊔ Subgroup.center X ≤ Subgroup.normalizer ((K ⊔ U : Subgroup X) : Set X) :=
      sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
    rw [h1, top_le_iff] at hle
    exact Subgroup.normalizer_eq_top_iff.mp hle
  have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h1 inferInstance
  have hperf : commutator X = ⊤ := by
    have : Group.IsPerfect X := hXq.1
    exact Group.IsPerfect.commutator_eq_top
  rw [hperf, top_le_iff] at hcomm
  exact hcomm

theorem pow_eq_of_mul_odd {k a i c : ℕ} (hi : i % 2 = 1) (hc : c % 2 = 1)
    (h : 2 ^ k * i = 2 ^ a * c) : k = a := by
  rcases lt_trichotomy k a with hka | hka | hka
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hka
    have h2 : 2 ^ k * i = 2 ^ k * (2 ^ (d + 1) * c) := by rw [h]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have : 2 ∣ i := by rw [h3]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    omega
  · exact hka
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hka
    have h2 : 2 ^ a * (2 ^ (d + 1) * i) = 2 ^ a * c := by rw [← h]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have : 2 ∣ c := by rw [← h3]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    omega

theorem card_eq_of_isSylowTwoOf_top {Q : Type} [Group Q] [Finite Q] {U : Subgroup Q}
    (hU : IsSylowTwoOf U ⊤) {a c : ℕ} (hc : c % 2 = 1) (hQ : Nat.card Q = 2 ^ a * c) :
    Nat.card U = 2 ^ a := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU.2.1
  have hidx : ¬ 2 ∣ U.index := by
    have h2 : ¬ 2 ∣ U.relIndex ⊤ := hU.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  have h1 := Subgroup.card_mul_index U
  rw [hk, hQ] at h1
  have hka := pow_eq_of_mul_odd (by omega) hc h1
  rw [hk, hka]

theorem overgroup_numbers {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] {P K U : Subgroup Q}
    (hP : P ≠ ⊤) (hKP : K ≤ P) (hUP : U ≤ P) (hK60 : 60 ≤ Nat.card K) :
    60 ≤ Nat.card P ∧ Nat.card Q = Nat.card P * P.index ∧ P.index ≠ 1 ∧
      Nat.card Q ∣ (P.index).factorial ∧ Nat.card U ∣ Nat.card P := by
  refine ⟨hK60.trans (Subgroup.card_le_of_le hKP), (Subgroup.card_mul_index P).symm, ?_,
    card_dvd_factorial_index hP, Subgroup.card_dvd_of_le hUP⟩
  intro h1
  exact hP (Subgroup.index_eq_one.mp h1)

theorem sixty_le_card_map_center {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hKp : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) :
    60 ≤ Nat.card (K.map (QuotientGroup.mk' (Subgroup.center X))) := by
  refine sixty_le_card_of_perfect ?_ ?_
  · rw [← Subgroup.map_commutator, hKp]
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    apply hKne
    rw [← hKp, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b _
    exact Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hbot ha) b).symm)

theorem false_of_card_168 {p m : ℕ} (h60 : 60 ≤ p) (hpm : 168 = p * m) (hm : m ≠ 1)
    (hf : 168 ∣ m.factorial) : False := by
  have hm2 : m ≤ 2 := by
    by_contra h
    push Not at h
    nlinarith
  interval_cases m
  · omega
  · omega
  · norm_num [Nat.factorial] at hf

theorem false_of_card_360 {p m : ℕ} (h60 : 60 ≤ p) (hpm : 360 = p * m) (hm : m ≠ 1)
    (hf : 360 ∣ m.factorial) (h8 : 8 ∣ p) : False := by
  have hm6 : m ≤ 6 := by
    by_contra h
    push Not at h
    nlinarith
  interval_cases m <;> first | omega | (norm_num [Nat.factorial] at hf)

theorem false_of_isPSL_three_two {X : Type} [Group X] [Finite X] (hXq : CFSG.IsQuasisimple X)
    (hl : IsPSL 3 2 1 (X ⧸ Subgroup.center X)) {U K : Subgroup X}
    (hKp : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (hKU : K ⊔ U ≠ ⊤) : False := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hXq.2.1
  obtain ⟨P, hKP, hUP, hP⟩ := exists_overgroup_bar hXq hKU
  obtain ⟨h60, hcard, hm, hfac, -⟩ :=
    overgroup_numbers hP hKP hUP (sixty_le_card_map_center hKp hKne)
  rw [A312S.card_of_isPSL32 hl] at hcard hfac
  exact false_of_card_168 h60 hcard hm hfac

theorem false_of_isAlt_six {X : Type} [Group X] [Finite X] (hXq : CFSG.IsQuasisimple X)
    (hl : IsAlt 6 (X ⧸ Subgroup.center X)) {U K : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hKp : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (hKU : K ⊔ U ≠ ⊤) : False := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hXq.2.1
  obtain ⟨P, hKP, hUP, hP⟩ := exists_overgroup_bar hXq hKU
  obtain ⟨h60, hcard, hm, hfac, hUd⟩ :=
    overgroup_numbers hP hKP hUP (sixty_le_card_map_center hKp hKne)
  have hN : Nat.card (X ⧸ Subgroup.center X) = 360 := by
    obtain ⟨e⟩ := hl
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hUc : Nat.card (U.map (QuotientGroup.mk' (Subgroup.center X))) = 8 := by
    have := card_eq_of_isSylowTwoOf_top
      (isSylowTwoOf_top_map_of_surjective hU _ (QuotientGroup.mk'_surjective _))
      (a := 3) (c := 45) (by norm_num) (by rw [hN]; norm_num)
    simpa using this
  rw [hN] at hcard hfac
  rw [hUc] at hUd
  exact false_of_card_360 h60 hcard hm hfac hUd

end QA23

end CFSG.Quasithin
