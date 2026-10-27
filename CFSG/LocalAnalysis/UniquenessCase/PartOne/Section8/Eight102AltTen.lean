module


import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

theorem barImage_le_centralizer_barImage {L P Q : Subgroup G} (hPL : P ≤ L)
    (hQL : Q ≤ L) (hQP : Q ≤ centralizer (P : Set G)) :
    barImage L Q ≤ centralizer (barImage L P : Set (Bar2 L)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨m, hm, hzm⟩ := uc22p21c_mem_barImage.mp hz
  obtain ⟨q, hq, hyq⟩ := uc22p21c_mem_barImage.mp hy
  rw [← hzm, ← hyq]
  have hcomm : (q : G) * (m : G) = (m : G) * (q : G) :=
    Subgroup.mem_centralizer_iff.mp (hQP hm) (q : G) hq
  have hcommL : q * m = m * q := Subtype.ext hcomm
  have := congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hcommL
  simpa only [map_mul] using this

theorem isPerfect_derInf8 (X : Subgroup G) : Group.IsPerfect ↥(F08.DerInf8 X) := by
  have hperf : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥X n) : Subgroup ↥X) :=
    CFSG.perfect_residual_characterization.2.2.1
  haveI := hperf
  unfold F08.DerInf8
  exact Group.IsPerfect.map X.subtype

theorem rhoL_fix_barImage_of_mem_centralizer {L P : Subgroup G} {w : G}
    (hPL : P ≤ L) (hwN : w ∈ normalizer (L : Set G))
    (hwP : w ∈ centralizer (P : Set G)) :
    ∀ a ∈ barImage L P, rhoL L ⟨w, hwN⟩ a = a := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := uc22p21c_mem_barImage.mp ha
  have hcomm : w * (p : G) * w⁻¹ = (p : G) := by
    have h := Subgroup.mem_centralizer_iff.mp hwP (p : G) hp
    calc w * (p : G) * w⁻¹ = (p : G) * w * w⁻¹ := by rw [h]
      _ = (p : G) := by group
  change ((rhoL L) ⟨w, hwN⟩) (QuotientGroup.mk p) = QuotientGroup.mk p
  rw [UC6S846.rhoL_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  rw [UC6S846.rhoL_mk_coe]
  exact hcomm

theorem rhoL_fix_image_of_mem_centralizer {L U : Subgroup G} {w : G} {u₀ : ↥L}
    (hwN : w ∈ normalizer (L : Set G)) (hu₀U : (u₀ : G) ∈ U)
    (hwU : w ∈ centralizer (U : Set G)) :
    rhoL L ⟨w, hwN⟩ (QuotientGroup.mk u₀ : Bar2 L) = QuotientGroup.mk u₀ := by
  have hcomm : w * (u₀ : G) * w⁻¹ = (u₀ : G) := by
    have h := Subgroup.mem_centralizer_iff.mp hwU (u₀ : G) hu₀U
    calc w * (u₀ : G) * w⁻¹ = (u₀ : G) * w * w⁻¹ := by rw [h]
      _ = (u₀ : G) := by group
  change ((rhoL L) ⟨w, hwN⟩) (QuotientGroup.mk u₀) = QuotientGroup.mk u₀
  rw [UC6S846.rhoL_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  rw [UC6S846.rhoL_mk_coe]
  exact hcomm

theorem not_mem_of_rhoL_eq_one {L : Subgroup G} (hZ : center (Bar2 L) = ⊥) {w : G}
    (hwN : w ∈ normalizer (L : Set G)) (hword : orderOf w = 5)
    (hrho : rhoL L ⟨w, hwN⟩ = 1) : w ∉ L := by
  intro hwL
  have hinner := UC6S846.rhoL_inner L w hwL
  have h1 : rhoL L ⟨w, Subgroup.le_normalizer hwL⟩ = 1 := by simpa using hrho
  rw [hinner] at h1
  have hcent : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut (Bar2 L) => f x) h1
    rw [MulAut.conj_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rw [hZ] at hcent
  have hq : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : Bar2 L) = 1 := by simpa using hcent
  have hpc : w ∈ CFSG.Open.pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff (⟨w, hwL⟩ : ↥L)).2 ((QuotientGroup.eq_one_iff _).1 hq)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (UC6S846.isPGroup_pCoreOf L)
  have hdvd : 5 ∣ 2 ^ k := by
    have h := Subgroup.orderOf_dvd_natCard (s := CFSG.Open.pCoreOf 2 L) hpc
    rwa [hword, hk] at h
  exact absurd (Nat.prime_five.dvd_of_dvd_pow hdvd) (by norm_num)

private theorem exists_not_centralizing_image {L A E U₁ U₂ : Subgroup G}
    (hAL : A ≤ L) (hEL : E ≤ L ⊓ centralizer (A : Set G))
    (hEp : IsPGroup 5 ↥E) (hU₁E : U₁ ≤ E) (hU₂E : U₂ ≤ E)
    (hc₁ : Nat.card U₁ = 5) (hc₂ : Nat.card U₂ = 5) (hne : U₁ ≠ U₂)
    (hd₁ : 5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U₁ : Set G))))
    (hd₂ : 5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U₂ : Set G))))
    (hKU : ∀ V₁ V₂ : Subgroup (Bar2 L),
      V₁ ≤ centralizer (barImage L A : Set (Bar2 L)) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) →
      V₂ ≤ centralizer (barImage L A : Set (Bar2 L)) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) →
      Nat.card V₁ = 5 → Nat.card V₂ = 5 → V₁ = V₂) :
    ∃ U : Subgroup G, U ≤ E ∧ Nat.card U = 5 ∧
      5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U : Set G))) ∧
      ¬ barImage L U ≤ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) := by
  have hU₁L : U₁ ≤ L := hU₁E.trans (hEL.trans inf_le_left)
  have hU₂L : U₂ ≤ L := hU₂E.trans (hEL.trans inf_le_left)
  have hU₁C : U₁ ≤ centralizer (A : Set G) := hU₁E.trans (hEL.trans inf_le_right)
  have hU₂C : U₂ ≤ centralizer (A : Set G) := hU₂E.trans (hEL.trans inf_le_right)
  have hUbar₁C : barImage L U₁ ≤ centralizer (barImage L A : Set (Bar2 L)) :=
    barImage_le_centralizer_barImage hAL hU₁L hU₁C
  have hUbar₂C : barImage L U₂ ≤ centralizer (barImage L A : Set (Bar2 L)) :=
    barImage_le_centralizer_barImage hAL hU₂L hU₂C
  have hUbar₁card : Nat.card (barImage L U₁) = 5 := by
    rw [card_barImage_of_isPGroup hU₁L Nat.prime_five (by norm_num)
      (IsPGroup.of_card (n := 1) (by rw [hc₁]; norm_num)), hc₁]
  have hUbar₂card : Nat.card (barImage L U₂) = 5 := by
    rw [card_barImage_of_isPGroup hU₂L Nat.prime_five (by norm_num)
      (IsPGroup.of_card (n := 1) (by rw [hc₂]; norm_num)), hc₂]
  have hUbar_ne : barImage L U₁ ≠ barImage L U₂ := by
    intro h
    exact hne (eq_of_barImage_eq (hEL.trans inf_le_left) Nat.prime_five (by norm_num)
      hEp hU₁E hU₂E h)
  by_cases h1 : barImage L U₁ ≤ centralizer
      (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L))
  · refine ⟨U₂, hU₂E, hc₂, hd₂, ?_⟩
    intro h2
    have hle₁ : barImage L U₁ ≤ centralizer (barImage L A : Set (Bar2 L)) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) :=
      le_inf hUbar₁C h1
    have hle₂ : barImage L U₂ ≤ centralizer (barImage L A : Set (Bar2 L)) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) :=
      le_inf hUbar₂C h2
    exact hUbar_ne (hKU _ _ hle₁ hle₂ hUbar₁card hUbar₂card)
  · exact ⟨U₁, hU₁E, hc₁, hd₁, h1⟩

private theorem exists_order_five_not_centralizing {L A U : Subgroup G}
    (hAL : A ≤ L) (hUL : U ≤ L) (hUC : U ≤ centralizer (A : Set G))
    (hUcard : Nat.card U = 5)
    (hUnotcent : ¬ barImage L U ≤ centralizer
      (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L))) :
    ∃ (u : Bar2 L) (u₀ : ↥L), orderOf u = 5 ∧ (u₀ : G) ∈ U ∧
      (QuotientGroup.mk u₀ : Bar2 L) = u ∧
      u ∈ centralizer (barImage L A : Set (Bar2 L)) ∧ u ∉ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) := by
  have hUbarC : barImage L U ≤ centralizer (barImage L A : Set (Bar2 L)) :=
    barImage_le_centralizer_barImage hAL hUL hUC
  have hUbar_card : Nat.card (barImage L U) = 5 := by
    rw [card_barImage_of_isPGroup hUL Nat.prime_five (by norm_num)
      (IsPGroup.of_card (n := 1) (by rw [hUcard]; norm_num)), hUcard]
  obtain ⟨u, huUbar, hu_notcent⟩ := Set.not_subset.mp hUnotcent
  obtain ⟨u₀, hu₀U, hu₀eq⟩ := uc22p21c_mem_barImage.mp huUbar
  have hu_ne : u ≠ 1 := by
    intro h1
    exact hu_notcent (h1 ▸ Subgroup.one_mem _)
  have hurdvd : orderOf u ∣ 5 := by
    have h := Subgroup.orderOf_dvd_natCard (s := barImage L U) huUbar
    rwa [hUbar_card] at h
  refine ⟨u, u₀, ?_, hu₀U, hu₀eq, hUbarC huUbar, hu_notcent⟩
  rcases (Nat.dvd_prime Nat.prime_five).mp hurdvd with h1 | h5
  · exact absurd (orderOf_eq_one_iff.mp h1) hu_ne
  · exact h5


private theorem exists_reduction_witness {L A E U₁ U₂ : Subgroup G}
    (hAL : A ≤ L) (hEL : E ≤ L ⊓ centralizer (A : Set G))
    (hEp : IsPGroup 5 ↥E) (hU₁E : U₁ ≤ E) (hU₂E : U₂ ≤ E)
    (hc₁ : Nat.card U₁ = 5) (hc₂ : Nat.card U₂ = 5) (hne : U₁ ≠ U₂)
    (hd₁ : 5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U₁ : Set G))))
    (hd₂ : 5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U₂ : Set G))))
    (hKU : ∀ V₁ V₂ : Subgroup (Bar2 L),
      V₁ ≤ centralizer (barImage L A : Set (Bar2 L)) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) →
      V₂ ≤ centralizer (barImage L A : Set (Bar2 L)) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) →
      Nat.card V₁ = 5 → Nat.card V₂ = 5 → V₁ = V₂) :
    ∃ (U : Subgroup G) (u : Bar2 L) (u₀ : ↥L), U ≤ E ∧ Nat.card U = 5 ∧
      U ≤ L ∧ U ≤ centralizer (A : Set G) ∧
      5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U : Set G))) ∧
      orderOf u = 5 ∧ (u₀ : G) ∈ U ∧ (QuotientGroup.mk u₀ : Bar2 L) = u ∧
      u ∈ centralizer (barImage L A : Set (Bar2 L)) ∧
      u ∉ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) := by
  obtain ⟨U, hUE, hUcard, hdU, hUnotcent⟩ :=
    exists_not_centralizing_image hAL hEL hEp hU₁E hU₂E hc₁ hc₂ hne hd₁ hd₂ hKU
  have hUL : U ≤ L := hUE.trans (hEL.trans inf_le_left)
  have hUC : U ≤ centralizer (A : Set G) := hUE.trans (hEL.trans inf_le_right)
  obtain ⟨u, u₀, huord, hu₀U, hu₀eq, huCbar, hu_notcent⟩ :=
    exists_order_five_not_centralizing hAL hUL hUC hUcard hUnotcent
  exact ⟨U, u, u₀, hUE, hUcard, hUL, hUC, hdU, huord, hu₀U, hu₀eq, huCbar, hu_notcent⟩

private theorem rho_image_eq_bot {L A U W : Subgroup G} {u : Bar2 L} {u₀ : ↥L}
    (hAL : A ≤ L) (hWN : W ≤ normalizer (L : Set G)) (hWA : W ≤ centralizer (A : Set G))
    (hWU : W ≤ centralizer (U : Set G)) (hWperf : Group.IsPerfect ↥W)
    (hu₀U : (u₀ : G) ∈ U) (hu₀eq : (QuotientGroup.mk u₀ : Bar2 L) = u)
    (huord : orderOf u = 5) (huCbar : u ∈ centralizer (barImage L A : Set (Bar2 L)))
    (hunot : u ∉ centralizer
      (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)))
    (hKU : ∀ u ∈ centralizer (barImage L A : Set (Bar2 L)), orderOf u = 5 →
      u ∉ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) : Set (Bar2 L)) →
      ∀ Y : Subgroup (MulAut (Bar2 L)), ⁅Y, Y⁆ = Y →
        (∀ α ∈ Y, ∀ a ∈ barImage L A, α a = a) → (∀ α ∈ Y, α u = u) → Y = ⊥) :
    (⊤ : Subgroup ↥W).map ((rhoL L).comp (Subgroup.inclusion hWN)) = ⊥ ∧
      ∀ (e : G) (heW : e ∈ W), rhoL L ⟨e, hWN heW⟩ = 1 := by
  let φ : ↥W →* MulAut (Bar2 L) := (rhoL L).comp (Subgroup.inclusion hWN)
  let Y : Subgroup (MulAut (Bar2 L)) := (⊤ : Subgroup ↥W).map φ
  have hYperf : Group.IsPerfect ↥Y := by
    haveI : Group.IsPerfect ↥W := hWperf
    change Group.IsPerfect ↥((⊤ : Subgroup ↥W).map φ)
    exact Group.IsPerfect.map φ
  have hYcomm : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.mp hYperf
  have hfixA : ∀ α ∈ Y, ∀ a ∈ barImage L A, α a = a := by
    intro α hα a ha
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hα
    exact rhoL_fix_barImage_of_mem_centralizer hAL (hWN w.2) (hWA w.2) a ha
  have hfixu : ∀ α ∈ Y, α u = u := by
    intro α hα
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hα
    rw [← hu₀eq]
    exact rhoL_fix_image_of_mem_centralizer (hWN w.2) hu₀U (hWU w.2)
  have hYbot : Y = ⊥ := hKU u huCbar huord hunot Y hYcomm hfixA hfixu
  refine ⟨hYbot, ?_⟩
  intro e heW
  have hmem : φ ⟨e, heW⟩ ∈ Y := Subgroup.mem_map_of_mem φ (Subgroup.mem_top _)
  rw [hYbot] at hmem
  have hsub : (Subgroup.inclusion hWN ⟨e, heW⟩ : ↥(normalizer (L : Set G))) =
      ⟨e, hWN heW⟩ := rfl
  rw [← hsub]
  simpa [φ] using hmem

private theorem exists_order_five_not_mem {L W : Subgroup G} (hZ : center (Bar2 L) = ⊥)
    (hWN : W ≤ normalizer (L : Set G)) (hW5 : 5 ∣ Nat.card W)
    (hrho : ∀ (w : G) (hw : w ∈ W), rhoL L ⟨w, hWN hw⟩ = 1) :
    ∃ w ∈ W, orderOf w = 5 ∧ w ∉ L := by
  obtain ⟨w, hword⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 5 hW5
  have hword' : orderOf (w : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hword
  exact ⟨(w : G), w.2, hword',
    not_mem_of_rhoL_eq_one hZ (hWN w.2) hword' (hrho (w : G) w.2)⟩

private theorem exists_elemAbelian_centralizing_copy {L F E : Subgroup G}
    (hFL : F ≤ L) (hFel : IsElemAbelian 5 F) (hFcard : Nat.card F = 5 ^ 3)
    (hEp : IsPGroup 5 ↥E)
    (hEO : E ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G))
    (hcomm : ∀ e ∈ E, ∀ a ∈ F, e * a * e⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    ∃ F' : Subgroup G, F' ≤ centralizer (E : Set G) ∧
      F' ≤ F ⊔ CFSG.Open.pCoreOf 2 L ∧ IsElemAbelian 5 F' ∧ Nat.card F' = 5 ^ 3 := by
  have hAO : F ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hFL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  obtain ⟨F', hF'C, hF'le, ⟨eF'⟩⟩ :=
    UC6S846.exists_centralizing_copy (ℓ := 5) (p := 5) Nat.prime_five (by norm_num)
      Nat.prime_five (by norm_num) (CFSG.Open.pCoreOf 2 L) F E
      (UC6S846.isPGroup_pCoreOf L) hAO hEO hFel.isPGroup hEp hcomm
  have hF'card : Nat.card F' = 5 ^ 3 := by
    rw [Nat.card_congr eF'.toEquiv, hFcard]
  have hF'el : IsElemAbelian 5 F' := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro x y
      exact eF'.injective (by
        rw [map_mul, map_mul]
        exact isMulCommutative_iff.mp hFel.1 (eF' x) (eF' y))
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥F') ^ 5 = 1 := by
        apply eF'.injective
        rw [map_pow, map_one]
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hFel.2 (eF' ⟨x, hx⟩) (eF' ⟨x, hx⟩).2
      simpa using hx'
  exact ⟨F', hF'C, hF'le, hF'el, hF'card⟩

private theorem exists_elemAbelian_five_four {L W : Subgroup G} {w : G}
    (hWN : W ≤ normalizer (L : Set G))
    (hrho_one : ∀ (e : G) (heW : e ∈ W), rhoL L ⟨e, hWN heW⟩ = 1)
    (hwW : w ∈ W) (hword : orderOf w = 5)
    (hL5 : 3 ≤ CFSG.Open.pRank 5 L) :
    ∃ F' : Subgroup G, IsElemAbelian 5 F' ∧ Nat.card F' = 5 ^ 3 ∧
      F' ≤ L ∧ F' ≤ centralizer (Subgroup.zpowers w : Set G) := by
  obtain ⟨F, hFL, hFel, hFcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 5) (k := 3) hL5
  have hFpow : IsPGroup 5 ↥(Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hword]; norm_num)
  have hzpowN : Subgroup.zpowers w ≤ normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (hWN hwW)
  have hEO : Subgroup.zpowers w ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hzpowN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hcommO : ∀ e ∈ Subgroup.zpowers w, ∀ a ∈ F,
      e * a * e⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro e he a ha
    have heW : e ∈ W := Subgroup.zpowers_le.mpr hwW he
    have h1 : rhoL L ⟨e, hWN heW⟩ (QuotientGroup.mk (⟨a, hFL ha⟩ : ↥L)) =
        QuotientGroup.mk (⟨a, hFL ha⟩ : ↥L) := by
      rw [hrho_one e heW]
      rfl
    exact (UC6S846.rhoL_fix_iff L ⟨e, hWN heW⟩ ⟨a, hFL ha⟩).mp h1
  obtain ⟨F', hF'C, hF'le, hF'el, hF'card⟩ :=
    exists_elemAbelian_centralizing_copy hFL hFel hFcard hFpow hEO hcommO
  exact ⟨F', hF'el, hF'card, hF'le.trans (sup_le hFL (CFSG.openPCoreOf_le 2 L)), hF'C⟩

private theorem four_le_pRank_of_elemAbelian_join {M L F' : Subgroup G} {w : G}
    (hLM : L ≤ M) (hF' : IsElemAbelian 5 F') (hF'card : Nat.card F' = 5 ^ 3)
    (hF'L : F' ≤ L) (hwM : w ∈ M) (hwL : w ∉ L)
    (hF'C : F' ≤ centralizer (Subgroup.zpowers w : Set G)) (hw : orderOf w = 5) :
    4 ≤ CFSG.Open.pRank 5 M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hw_notF' : w ∉ F' := fun h => hwL (hF'L h)
  have hcomm : ∀ e ∈ F', Commute e w := by
    intro e he
    exact (commute_iff_eq e w).mpr
      ((Subgroup.mem_centralizer_iff.mp (hF'C he) w (Subgroup.mem_zpowers w)).symm)
  have hsup := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hF' hw hcomm hw_notF'
  have hsup_card : Nat.card (F' ⊔ Subgroup.zpowers w : Subgroup G) = 5 ^ 4 := by
    rw [hsup.2, hF'card]
    norm_num
  have hle : F' ⊔ Subgroup.zpowers w ≤ M :=
    sup_le (hF'L.trans hLM) (Subgroup.zpowers_le.mpr hwM)
  exact CFSG.SectionRank.le_pRank (p := 5) (by norm_num) hle hsup.1 (k := 4) hsup_card

theorem false_of_isAlt_five {D : Data G} (hSg : SigmaStd D) (he : evenRank G = 3)
    (hK9 : KU45AltFive) {L P A E U₁ U₂ : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G))
    (hA : F08.NotationA8103 L P p n A) (hp5 : p = 5)
    (hA5 : IsAlt (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) 5)
    (hEL : E ≤ L ⊓ centralizer (A : Set G)) (hEp : IsPGroup 5 E) (hU₁E : U₁ ≤ E)
    (hU₂E : U₂ ≤ E) (hc₁ : Nat.card U₁ = 5) (hc₂ : Nat.card U₂ = 5) (hne : U₁ ≠ U₂)
    (hd₁ : 5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U₁ : Set G))))
    (hd₂ : 5 ∣ Nat.card (F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U₂ : Set G)))) :
    False := by
  classical
  have hAL : A ≤ L := hA.2.1.trans hH.2.2.2.2.le
  have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by rw [hA.1]; norm_num)
  have hAbar_card : Nat.card (barImage L A) = 3 := by
    rw [card_barImage_of_isPGroup hAL Nat.prime_three (by norm_num) hA3, hA.1]
  have hJbar_alt : IsAlt (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer
      (barImage L A : Set (Bar2 L))))) 5 := by
    obtain ⟨e⟩ := nonempty_bar2_derInf8_equiv (L := L) (X := A) hAL Nat.prime_three
      (by norm_num) hA3
    exact ⟨e.symm.trans hA5.some⟩
  obtain ⟨hK9a, hK9b, hK9c⟩ := hK9 (Bar2 L) n hX (barImage L A) hAbar_card hJbar_alt
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hH.1.1
  have hsp5 : IsStronglyPEmbedded 5 D.M := UC6S846.sp_of_mem_sig hSg
    (UC6S846.not_solvable_of_mem_calC hH.1) (hp5 ▸ hH.2.2.2.1)
  obtain ⟨U, u, u₀, hUE, hUcard, hUL, hUC, hdU, huord, hu₀U, hu₀eq, huCbar,
    hu_notcent⟩ := exists_reduction_witness hAL hEL hEp hU₁E hU₂E hc₁ hc₂ hne hd₁ hd₂ hK9a
  have hNU : normalizer (U : Set G) ≤ D.M := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le hsp5 ?_
      (IsPGroup.of_card (n := 1) (by rw [hUcard, pow_one])) (hUL.trans hLM)
    rintro rfl
    rw [Subgroup.card_bot] at hUcard
    omega
  let W : Subgroup G :=
    F08.DerInf8 (centralizer (A : Set G) ⊓ centralizer (U : Set G))
  have hWle : W ≤ centralizer (A : Set G) ⊓ centralizer (U : Set G) :=
    Subgroup.map_subtype_le _
  have hWM : W ≤ D.M :=
    ((hWle.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer (U : Set G))).trans hNU
  have hWN : W ≤ normalizer (L : Set G) := hWM.trans hN
  have hWperf : Group.IsPerfect ↥W := isPerfect_derInf8 _
  obtain ⟨-, hrho_one⟩ := rho_image_eq_bot hAL hWN (hWle.trans inf_le_left)
    (hWle.trans inf_le_right) hWperf hu₀U hu₀eq huord huCbar hu_notcent hK9b
  have hW5 : 5 ∣ Nat.card W := by simpa [W] using hdU
  obtain ⟨w, hwW, hword, hwL⟩ :=
    exists_order_five_not_mem (center_bar2_eq_bot_of_hyp8102 hH) hWN hW5 hrho_one
  have hL5 : 3 ≤ CFSG.Open.pRank 5 L := by
    rw [← UC22.pRank_bar2_eq_of_odd (Y := L) Nat.prime_five (by norm_num)]; exact hK9c
  obtain ⟨F', hF'el, hF'card, hF'leL, hF'C⟩ :=
    exists_elemAbelian_five_four hWN hrho_one hwW hword hL5
  have h4 := four_le_pRank_of_elemAbelian_join hLM hF'el hF'card hF'leL (hWM hwW) hwL hF'C hword
  have h3 := pRank_le_three_of_evenRank D he Nat.prime_five (by norm_num)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
