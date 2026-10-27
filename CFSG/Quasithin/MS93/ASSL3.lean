module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup
public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.SkConcl

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

variable {G : Type} [Group G]

theorem card_center_statedSL3_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (Subgroup.center ↥(StatedSL 3 K)) ∣ 3 := by
  rw [← Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 K)).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  have h3 : max (Fintype.card (Fin 3)) 1 = 3 := by simp
  rw [h3, ← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
  exact Subtype.ext ((mem_rootsOfUnity 3 _).mp g.2)

theorem statedSL3_normal_isPGroup_eq_bot (K : Type) [Field K] [Finite K]
    (N : Subgroup ↥(StatedSL 3 K)) (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple ↥(StatedSL 3 K) :=
    EmptyFaithfulMultiple.FFL.isQuasisimple_statedSL (m := 2) le_rfl K
  have hq' : CFSG.Open.IsQuasisimple ↥(StatedSL 3 K) := ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq' N with hc | ht
  · obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hd : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le hc).trans (card_center_statedSL3_dvd K)
    rw [hk] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have h23 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hd
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    subst ht
    have h2' : IsPGroup 2 ↥(StatedSL 3 K) := h2.of_equiv Subgroup.topEquiv
    have : Group.IsPerfect ↥(StatedSL 3 K) := hq.1
    have : Nontrivial ↥(StatedSL 3 K) := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      obtain ⟨-, -, a, b, hab⟩ := hq
      exact hab (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isNilpotent ↥(StatedSL 3 K) h2'.isNilpotent

variable [Finite G]

theorem pCore_le_ker_of_statedSL3 {L : Subgroup G} {K : Type} [Field K] [Finite K]
    (α : ↥L →* ↥(StatedSL 3 K)) (hα : Function.Surjective α) : CFSG.pCore 2 ↥L ≤ α.ker :=
  pCore_le_ker_of_surjective α hα (statedSL3_normal_isPGroup_eq_bot K)

theorem exists_pow_eq_one_of_le_pCoreOf {M A : Subgroup G} (hA : A ≤ pCoreOf 2 M) :
    ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k = 1 := fun a ha => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨a, hA ha⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isModO2Surj_of_case5 {M T L : Subgroup G} (h : PUHyp M T L)
    (h5 : MS93Case5 (Vq M L) L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsSumOfNaturalModulesVia L (Vq M L) ⊥ α false 2 := by
  obtain ⟨n, F, _, _, α, hF, hα, hn⟩ := h5
  exact ⟨n, F, inferInstance, inferInstance, α, hF,
    ⟨hα, le_antisymm (ker_le_pCore_of_natural h bot_le hn) (pCore_le_ker_of_statedSL3 α hα)⟩, hn⟩

theorem commute_step {M : Subgroup G} {ℓ : G} (hodd : Odd (orderOf ℓ)) {A B : Subgroup G}
    (hAQ : A ≤ pCoreOf 2 M) (hA : ∀ a ∈ A, ℓ * a = a * ℓ)
    (hB : ∀ b ∈ B, ℓ * b * ℓ⁻¹ * b⁻¹ ∈ A) : ∀ b ∈ B, ℓ * b = b * ℓ :=
  commute_of_commutator_mem hodd hA (exists_pow_eq_one_of_le_pCoreOf hAQ) hB

theorem isModO2Surj_of_case11 {M T L : Subgroup G} (h : PUHyp M T L)
    (h11 : MS93Case11 (Vq M L) T L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α := by
  obtain ⟨n, F, _, _, α, hF, hα, h1, h2, -⟩ := h11
  refine ⟨n, F, inferInstance, inferInstance, α, hF, hα,
    le_antisymm (ker_le_pCore_of_odd α fun ℓ hℓ hodd => ?_) (pCore_le_ker_of_statedSL3 α hα)⟩
  have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
  have hZQ : centerOf (Vq M L) ≤ pCoreOf 2 M := inf_le_left.trans (Vq_le_pCoreOf h.L_le)
  have hZ : ∀ z ∈ centerOf (Vq M L), (ℓ : G) * z = z * ℓ := fun z hz => by
    have := commutator_mem_of_mem_ker h1 hℓ hz
    rw [Subgroup.mem_bot] at this
    calc (ℓ : G) * z = (ℓ : G) * z * (ℓ : G)⁻¹ * z⁻¹ * (z * ℓ) := by group
      _ = z * ℓ := by rw [this, one_mul]
  have hV := commute_step hodd' hZQ hZ fun b hb => commutator_mem_of_mem_ker h2 hℓ hb
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hV)

omit [Finite G] in
private theorem frattiniIn_le (V : Subgroup G) : frattiniIn V ≤ V := Subgroup.map_subtype_le _

theorem isModO2Surj_of_case13 {M T L : Subgroup G} (h : PUHyp M T L)
    (h13 : MS93Case13 (Vq M L) T L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α := by
  obtain ⟨n, F, _, _, α, hF, hα, -, -, hZeq, -, hU, hΦ, hC, hVC, -⟩ := h13
  refine ⟨n, F, inferInstance, inferInstance, α, hF, hα,
    le_antisymm (ker_le_pCore_of_odd α fun ℓ hℓ hodd => ?_) (pCore_le_ker_of_statedSL3 α hα)⟩
  have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
  have hVQ : Vq M L ≤ pCoreOf 2 M := Vq_le_pCoreOf h.L_le
  have hZ : ∀ z ∈ centerOf (Vq M L), (ℓ : G) * z = z * ℓ := by
    have hle : centerOf (Vq M L) ≤ Subgroup.centralizer ({(ℓ : G)} : Set G) := by
      rw [hZeq]
      refine sup_le (fun c hc => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 ℓ ℓ.2).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := commutator_mem_of_mem_ker hU hℓ hu
        rw [Subgroup.mem_bot] at this
        calc u * ℓ = (ℓ : G) * u * (ℓ : G)⁻¹ * u⁻¹ * (u * ℓ) := by rw [this, one_mul]
          _ = ℓ * u := by group
    intro z hz
    exact ((Subgroup.mem_centralizer_singleton_iff).mp (hle hz)).symm
  have hZQ : centerOf (Vq M L) ≤ pCoreOf 2 M := inf_le_left.trans hVQ
  have hΦ' := commute_step hodd' hZQ hZ fun b hb => commutator_mem_of_mem_ker hΦ hℓ hb
  have hC' := commute_step hodd' ((frattiniIn_le _).trans hVQ) hΦ' fun b hb =>
    commutator_mem_of_mem_ker hC hℓ hb
  have hV := commute_step hodd' (inf_le_left.trans hVQ) hC' fun b hb =>
    commutator_mem_of_mem_ker hVC hℓ hb
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hV)

theorem center_statedSL3_two_eq_bot : Subgroup.center ↥(StatedSL 3 (ZMod 2)) = ⊥ := by
  have hc : Nat.card (Subgroup.center ↥(StatedSL 3 (ZMod 2))) = 1 := by
    rw [← Nat.card_congr
        (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 (ZMod 2))).toEquiv,
      Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
    have hle := Subgroup.card_le_of_le (le_top : rootsOfUnity (max (Fintype.card (Fin 3)) 1)
      (ZMod 2) ≤ ⊤)
    have hu : Nat.card (ZMod 2)ˣ = 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      decide
    rw [Subgroup.card_top, hu] at hle
    exact le_antisymm hle Nat.card_pos
  exact Subgroup.eq_bot_of_card_eq _ hc

theorem eq_bot_of_perfect_of_isPGroup {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (h2 : IsPGroup 2 L) : L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hsub : Subsingleton ↥L := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent ↥L h2.isNilpotent
  refine eq_bot_iff.mpr fun x hx => ?_
  have := Subsingleton.elim (⟨x, hx⟩ : ↥L) 1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem isModO2Surj_of_case8 {M T L : Subgroup G} (h : PUHyp M T L) (h8 : MS93Case8 M T L) :
    ∃ α : ↥L →* ↥(StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧
      IsSumOfNaturalModulesVia L (Vq M L) (Vq M L ⊓ Subgroup.centralizer (M : Set G)) α false
        1 := by
  obtain ⟨⟨α, hα, hn⟩, -⟩ := h8
  set α' : ↥L →* ↥(StatedSL 3 (ZMod 2)) := α.comp (Subgroup.inclusion h.L_le) with hα'
  have hn' : IsSumOfNaturalModulesVia L (Vq M L) (Vq M L ⊓ Subgroup.centralizer (M : Set G))
      α' false 1 := by
    obtain ⟨-, hZV, β, hβ, hker, hβeq⟩ := hn
    exact ⟨h.L_le.trans (le_normalizer_Vq h.le_normalizer), hZV, β, hβ, hker,
      fun a u v huv i => hβeq (Subgroup.inclusion h.L_le a) u v huv i⟩
  have hZL : Vq M L ⊓ Subgroup.centralizer (M : Set G) ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le h.L_le)
  have hk := ker_le_pCore_of_natural h hZL hn'
  have hsurj : Function.Surjective α' := by
    have hq : CFSG.IsQuasisimple ↥(StatedSL 3 (ZMod 2)) :=
      EmptyFaithfulMultiple.FFL.isQuasisimple_statedSL (m := 2) le_rfl (ZMod 2)
    have hq' : CFSG.Open.IsQuasisimple ↥(StatedSL 3 (ZMod 2)) :=
      ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
    have hLn : (L.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
    have hrange : α'.range = (L.subgroupOf M).map α := by
      rw [hα', MonoidHom.range_comp]
      congr 1
      ext x
      simp [Subgroup.mem_subgroupOf]
    have hN : α'.range.Normal := hrange ▸ Subgroup.Normal.map hLn α hα
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq' α'.range
      with hc | ht
    · exfalso
      rw [center_statedSL3_two_eq_bot, le_bot_iff, MonoidHom.range_eq_bot_iff] at hc
      have htop : α'.ker = ⊤ := by
        rw [hc]
        exact MonoidHom.ker_one
      have h2 : IsPGroup 2 L := by
        have hP := isPGroup_cfsgPCore ↥L
        have : (⊤ : Subgroup ↥L) ≤ CFSG.pCore 2 ↥L := htop ▸ hk
        exact (hP.to_le this).of_equiv Subgroup.topEquiv
      exact h.L_ne_bot (eq_bot_of_perfect_of_isPGroup h.perfect h2)
    · exact MonoidHom.range_eq_top.mp ht
  exact ⟨α', ⟨hsurj, le_antisymm hk (pCore_le_ker_of_statedSL3 α' hsurj)⟩, hn'⟩

end CFSG.Quasithin.MS93
