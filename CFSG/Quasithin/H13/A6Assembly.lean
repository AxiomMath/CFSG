module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.A6Realize
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {G : Type} [Group G]

theorem card_alt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem map_center_le_center {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) : (Subgroup.center X).map f ≤ Subgroup.center Y := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]

theorem false_of_surjective_alt5 {L : Subgroup G} (hA6 : A6CentralQuotient L)
    (φ : ↥L →* ↥(alternatingGroup (Fin 5))) (hφ : Function.Surjective φ) : False := by
  classical
  have hO2 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    have hN : ((CFSG.pCore 2 ↥L).map φ).Normal := Subgroup.Normal.map CFSG.pCore_normal φ hφ
    have hP : IsPGroup 2 ((CFSG.pCore 2 ↥L).map φ) := CFSG.pCore_isPGroup.map φ
    have hs5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases hs5.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map φ) with h | h
    · rw [Subgroup.map_eq_bot_iff] at h
      exact h
    · exfalso
      rw [h] at hP
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
      rw [Subgroup.card_top, card_alt5] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 60)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  let φ₁ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(alternatingGroup (Fin 5)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2
  have hφ₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), rfl⟩
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≤ φ₁.ker := by
    intro z hz
    have h1 : φ₁ z ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) :=
      map_center_le_center φ₁ hφ₁ ⟨z, hz, rfl⟩
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
    exact h1
  let φ₂ : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) →*
      ↥(alternatingGroup (Fin 5)) :=
    QuotientGroup.lift (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) φ₁ hZ
  have hφ₂ : Function.Surjective φ₂ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ₁ y
    exact ⟨(x : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)), rfl⟩
  obtain ⟨e⟩ := hA6
  let ψ : ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 5)) :=
    φ₂.comp e.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hφ₂.comp e.symm.surjective
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases hsimp.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  ·
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp h
    have hle := Nat.card_le_card_of_injective ψ hinj
    rw [card_alt5, card_alt6] at hle
    omega
  ·
    have hall : ∀ y : ↥(alternatingGroup (Fin 5)), y = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x)
    have h1 : Nat.card ↥(alternatingGroup (Fin 5)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    rw [card_alt5] at h1
    omega

theorem card_of_statedClassicalModel_psl32 {X : Type} [Group X]
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem statedClassicalModel_of_lieModel_psl32 {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 1) : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem false_of_psl32_of_a6CentralQuotient {L : Subgroup G} (hA6 : A6CentralQuotient L)
    (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) : False := by
  have hcard := card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h)
  obtain ⟨e⟩ := hA6
  have hdvd := Subgroup.card_quotient_dvd_card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [Nat.card_congr e.toEquiv, card_alt6, hcard] at hdvd
  exact absurd hdvd (by norm_num)

theorem false_of_surjective_alt6_of_alt5 {K : Subgroup G}
    (hA5 : quasithinO2QuotientIso K (alternatingGroup (Fin 5)))
    (φ : ↥K →* ↥(alternatingGroup (Fin 6))) (hφ : Function.Surjective φ) : False := by
  classical
  have hO2 : CFSG.pCore 2 ↥K ≤ φ.ker := by
    have hN : ((CFSG.pCore 2 ↥K).map φ).Normal := Subgroup.Normal.map CFSG.pCore_normal φ hφ
    have hP : IsPGroup 2 ((CFSG.pCore 2 ↥K).map φ) := CFSG.pCore_isPGroup.map φ
    have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases hsimp.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map φ) with h | h
    · rw [Subgroup.map_eq_bot_iff] at h
      exact h
    · exfalso
      rw [h] at hP
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
      rw [Subgroup.card_top, card_alt6] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 360)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  let φ₁ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(alternatingGroup (Fin 6)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hO2
  have hφ₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨(x : ↥K ⧸ CFSG.pCore 2 ↥K), rfl⟩
  obtain ⟨e⟩ := (quasithinO2QuotientIso_iff K _).1 hA5
  have hle := Nat.card_le_card_of_surjective (φ₁.comp e.symm.toMonoidHom)
    (hφ₁.comp e.symm.surjective)
  rw [card_alt5, card_alt6] at hle
  omega

theorem not_alt5_of_psu33 {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    ¬ Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  have hm : Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1 := by
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := hm
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have f' : X ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 3 K) := f
  have hdvd := Subgroup.card_quotient_dvd_card
    ((Assembly.LowTwoRank.StatedScalars (Fin 3) K).subgroupOf
      (Assembly.LowTwoRank.StatedSU 3 3 K))
  have hX : Nat.card (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 3 K)) = 60 :=
    by rw [← Nat.card_congr f'.toEquiv, Nat.card_congr e.toEquiv, card_alt5]
  rw [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hK9] at hdvd
  have h60 : (60 : ℕ) ∣ 6048 := by
    rw [← hX]
    exact hdvd
  exact absurd h60 (by norm_num)

open scoped IsMulCommutative in
theorem isA6On_of_modules (h13316 : Stmt13_3_16) [Finite G] {T L V : Subgroup G}
    (hH : QTH13 G T L) (hA6 : A6CentralQuotient L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) [IsMulCommutative ↥V]
    (hmod : Modules13_3_2 L V) : IsA6On L V := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, -, hc⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
  · exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
    obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLN
    exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  · exact nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h6
  · exact nonempty_mulEquiv_of_realizes (altCoreModel_faithful (by norm_num)) hc
  · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
  · exact (h13316 G T L hH hu).elim

open scoped IsMulCommutative in
theorem stmt13_4_1_of_inputs (h1332 : Stmt13_3_2) (h1335 : Stmt13_3_5) (h1349 : Stmt13_4_9)
    (h13410 : Stmt13_4_10_17) : Stmt13_4_1 := by
  intro G _ _ T L V hH hV hZV
  obtain ⟨-, -, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hc, hmod⟩ := hall V hV
  have hA6V : IsA6On L V := by
    rcases hmod with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, hc6⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact absurd h hZV
    · exact absurd h hZV
    · exact nonempty_mulEquiv_of_realizes (altCoreModel_faithful (by norm_num)) hc6
    · exact absurd h hZV
    · exact absurd h hZV
  obtain ⟨z, hz, hzL, hzM⟩ := (h1335 G T L V hH hV).2.2 hA6V
  exact h1349 G T L V z hH hV hZV hz hzL hzM (h13410 G T L V z hH hV hZV hz hzL hzM)

open scoped IsMulCommutative in
theorem stmt13_5_2_of_inputs (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) :
    Stmt13_5_2 := by
  intro G _ _ T L hH hSp K hK
  obtain ⟨hfive, ⟨hTK, hmaxK, -, -⟩, ⟨hex, hall⟩, h4⟩ := h1332 G T L hH K hK
  have hU33 : ¬ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSU 3 3 1 := by
    intro hu
    have hnA5 : ¬ quasithinO2QuotientIso K (alternatingGroup (Fin 5)) := fun hA5 =>
      not_alt5_of_psu33 hu ((quasithinO2QuotientIso_iff K _).1 hA5)
    exact h13316 G T K (h4 (Or.inl hnA5)) hu
  refine ⟨?_, ⟨hTK, hmaxK⟩, hex, fun VK hVK => ?_⟩
  · rcases hfive with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd h hU33
  · obtain ⟨hVT, hTV, hfsu, hc, hmod⟩ := hall VK hVK
    refine ⟨hVK.1, hVT, hTV, hfsu, ?_⟩
    rcases hmod with ⟨h5, h5c⟩ | ⟨h6, h6c⟩ | ⟨-, hcard2, hcore⟩ | ⟨-, hsl, hslc⟩ | ⟨hu, -, -⟩
    · exact ⟨h5c, hc, Or.inl h5⟩
    · exact ⟨h6c, hc, Or.inr (Or.inl h6)⟩
    · exfalso
      have hne : VK ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard2
        exact absurd hcard2 (by norm_num)
      by_cases hA5 : quasithinO2QuotientIso K (alternatingGroup (Fin 5))
      · have hKN : K ≤ Subgroup.normalizer (VK : Set G) := hVK.2.2.1
        obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altCoreModel_faithful (by norm_num)) hcore
        obtain ⟨φ, hφ⟩ := exists_surjective_autOn hKN
        exact false_of_surjective_alt6_of_alt5 hA5 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
      · exact hSp (h1341 G T K VK (h4 (Or.inl hA5)) hVK hne)
    · exact ⟨hslc, hc, Or.inr (Or.inr hsl)⟩
    · exact absurd hu hU33

open scoped IsMulCommutative in
theorem stmt13_8_1_of_inputs (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16) (h1378 : Stmt13_7_8)
    (h138 : Stmt13_8_3_34) : Stmt13_8_1 := by
  intro G _ _ T L hH hA6
  obtain ⟨-, -, ⟨⟨V, hV⟩, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hc, hmod⟩ := hall V hV
  have hA6V : IsA6On L V := isA6On_of_modules h13316 hH hA6 hV hmod
  by_contra hcon
  rw [not_or] at hcon
  exact h138 G T L V hH hA6 hV hcon.1 hcon.2 (h1378 G T L V hH hV hA6V hcon.1 hcon.2)

end CFSG.Quasithin.H13.A6
