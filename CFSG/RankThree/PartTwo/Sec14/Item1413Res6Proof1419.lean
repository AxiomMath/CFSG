module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1419
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res6

variable {G : Type} [Group G] [Finite G]

open Proof1413Res3 in
theorem le_centralizer_inf_of_pointC
    (h1413 : Item1413CR)
    (h142 : Concl142S14) (hbot : Item145BotS14) (h131 : Item131) (hOne : Item1419OneR)
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (hR : Sec15R G A c₀ L₀)
    (hfail : Fail1411 A (lB A)) {x : G} (hxΓ : Subgroup.zpowers x ∈ gammaA A (lB A))
    {Lx : Subgroup G} (hLx : Lx ∈ lA A x)
    (htype : Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx) ∨
      Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA x Lx A)) {R O : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRO : R ≤ O) (hO2 : IsPGroup 2 O)
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) (hRx : R ≤ Subgroup.centralizer ({x} : Set G))
    (hB : IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G))) :
    A ⊓ Subgroup.centralizer (R : Set G) ≤
      Subgroup.centralizer ((O ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hSx := Proof1413.sec14Std_at hR.toSec14Std hxΓ.1 hLx
  have hDx := hSx.toSec13Data
  have hxL : x ∉ Lx := not_mem_of_type hDx (type_four_of_three htype)
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hDx hxL hPGL
  have h3 : 3 ∣ Nat.card Lx := three_dvd_card_of_card_inf h9
  set Q := R ⊔ (O ⊓ Subgroup.centralizer ({x} : Set G)) with hQdef
  have hQO : Q ≤ O := sup_le hRO inf_le_left
  have hQ2 : IsPGroup 2 Q := hO2.to_le hQO
  have hQx : Q ≤ Subgroup.centralizer ({x} : Set G) := sup_le hRx inf_le_right
  have hAx : A ≤ Subgroup.centralizer ({x} : Set G) := hDx.A_le_centralizer
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_sup hAR (le_normalizer_inf hAO (hAx.trans Subgroup.le_normalizer))
  have hQL : Q ≤ Lx :=
    le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hxΓ hLx h3 hAa hQx hAQ hQ2
  have hQmem : Q ∈ scriptQPi A (lB A) Lx (piOf 2) :=
    Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hxΓ.1 hLx hQL hAQ hQ2
  obtain ⟨R', hQR', hR'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) Lx (piOf 2))) hQmem
  have hB' := hOne G A c₀ L₀ hR hfail x hxΓ Lx hLx htype R' hR'
  have hRR' : R ≤ R' := le_sup_left.trans hQR'
  have hle : A ⊓ Subgroup.centralizer (R' : Set G) ≤ A ⊓ Subgroup.centralizer (R : Set G) :=
    inf_le_inf_left A (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRR'))
  have heq : A ⊓ Subgroup.centralizer (R' : Set G) = A ⊓ Subgroup.centralizer (R : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by have := hB.2; have := hB'.2; omega)
  rw [← heq]
  have hOR' : O ⊓ Subgroup.centralizer ({x} : Set G) ≤ R' := le_sup_right.trans hQR'
  exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOR'))

open Proof1413Res3 in
theorem false_of_pointsC
    (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (h133 : Item133) (h1416 : Item1416R)
    (hPGL : Item1412NotPGLR) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hOne : Item1419OneR)
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (hR : Sec15R G A c₀ L₀)
    (hfail : Fail1411 A (lB A)) {c : G} (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A))
    {L : Subgroup G} (hL : L ∈ lA A c)
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    {R : Subgroup G} (hR' : R ∈ scriptQPiStar A (lB A) L (piOf 2)) {a t : G}
    (hF : Frame2 L c a) (hB : IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G)))
    (hcB : c ∈ A ⊓ Subgroup.centralizer (R : Set G))
    (haB : a ∈ A ⊓ Subgroup.centralizer (R : Set G))
    (hBel : ∀ f ∈ A ⊓ Subgroup.centralizer (R : Set G), ∃ i j : ℕ, f = c ^ i * a ^ j)
    (htW : t ∈ Subgroup.normalizer (A : Set G)) (htc : t * c * t⁻¹ = c)
    (hta : t * a * t⁻¹ = a⁻¹) (hcaΓ : Subgroup.zpowers (c * a) ∈ gammaA A (lB A))
    (hc2aΓ : Subgroup.zpowers (c ^ 2 * a) ∈ gammaA A (lB A)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Sec14Std G A c L := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hPGLc := hPGL G A c₀ L₀ hR hfail c hcΓ L hL
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hR'.prop
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR'.prop.1.1.1.2.2
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := hR'.prop.1.2.trans hD.le_centralizer
  have hR0 : R ≠ ⊥ := by
    intro h0
    have hAB : A ≤ B := fun y hy => ⟨hy, Subgroup.mem_centralizer_iff.mpr fun r hr => by
      have hr1 : r = 1 := Subgroup.mem_bot.mp (by rw [h0] at hr; exact hr)
      rw [hr1, one_mul, mul_one]⟩
    have h1 := Subgroup.card_le_of_le hAB
    have h2 := hB.2
    have h3 := hA.2
    omega
  set O := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) with hOdef
  have hRO : R ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 R hR2
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    (hAR.trans Subgroup.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hne := hF.zpowers_ne
  have hWca : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (c * a) : Set G) := by
    intro hW
    apply hne
    rw [← hF.map_conj_ca htc hta, Late.map_conj_eq_of_mem_normalizer (hW htW)]
  have hWc2a : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (c ^ 2 * a) : Set G) := by
    intro hW
    apply hne
    rw [← hF.map_conj_c2a htc hta, Late.map_conj_eq_of_mem_normalizer (hW htW)]
  have hcent : ∀ x : G, (x = c ∨ x = c * a ∨ x = c ^ 2 * a) →
      B ≤ Subgroup.centralizer
        ((O ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rintro x (rfl | rfl | rfl)
    · exact le_centralizer_inf_of_pointC h1413 h142 hbot h131 hOne hR hfail hcΓ hL htype hPGLc
        hAR hRO hO2 hAO hRc hB
    · obtain ⟨Lx, hLx, htx⟩ :=
        exists_lA_of_moved h133 h1416 h422 h45 hR hfail hcΓ hL htype hcaΓ hWca
      exact le_centralizer_inf_of_pointC h1413 h142 hbot h131 hOne hR hfail hcaΓ hLx htx
        (hPGL G A c₀ L₀ hR hfail _ hcaΓ Lx hLx) hAR hRO hO2 hAO
        (le_centralizer_of_mem_inf (mul_mem hcB haB)) hB
    · obtain ⟨Lx, hLx, htx⟩ :=
        exists_lA_of_moved h133 h1416 h422 h45 hR hfail hcΓ hL htype hc2aΓ hWc2a
      exact le_centralizer_inf_of_pointC h1413 h142 hbot h131 hOne hR hfail hc2aΓ hLx htx
        (hPGL G A c₀ L₀ hR hfail _ hc2aΓ Lx hLx) hAR hRO hO2 hAO
        (le_centralizer_of_mem_inf (mul_mem (pow_mem hcB 2) haB)) hB
  have hfin : ∀ x : G, (x = c ∨ x = c * a ∨ x = c ^ 2 * a) →
      O ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    fun x hx y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hcent x hx haB) y hy)
  have hOa : O ≤ Subgroup.centralizer ({a} : Set G) := by
    refine Proof1413Res2.le_of_forall_centralizer hA hB hAO (not_three_dvd_of_isPGroup_two hO2)
      fun b hb hb1 _ => ?_
    obtain ⟨i, j, rfl⟩ := hBel b hb
    rcases hF.zpowers_cases hb1 with h | h | h | h
    · rw [centralizer_singleton_eq_of_zpowers_eq h]
      exact hfin c (Or.inl rfl)
    · rw [centralizer_singleton_eq_of_zpowers_eq h]
      exact inf_le_right
    · rw [centralizer_singleton_eq_of_zpowers_eq h]
      exact hfin _ (Or.inr (Or.inl rfl))
    · rw [centralizer_singleton_eq_of_zpowers_eq h]
      exact hfin _ (Or.inr (Or.inr rfl))
  have haN : a ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _ haB.2
  have ha1 := eq_one_of_le_centralizer_pCoreOf hD hR0 hR2 haN hF.ha3 hOa
  have h3 := hF.ha
  rw [ha1, orderOf_one] at h3
  omega

end Proof1413Res6

open Proof1413Res3 Proof1413Res6 in
theorem item1419TwoR_of_c
    (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (h133 : Item133) (h1416 : Item1416R)
    (hPGL : Item1412NotPGLR) (h1418 : Item1418R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hOne : Item1419OneR) (hInv : Step1419InvR) : Item1419TwoR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL htype R hR'
  have hS : Sec14Std G A c L := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  have hcA : c ∈ A := hD.mem_A
  have hPGLc := hPGL G A c₀ L₀ hR hfail c hcΓ L hL
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  obtain ⟨-, hAa⟩ := facts_of_type h131 hD hcL hPGLc
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hB : IsHyperplane A B := hOne G A c₀ L₀ hR hfail c hcΓ L hL htype R hR'
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := hR'.prop.1.2.trans hD.le_centralizer
  have hcB : c ∈ B := ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)⟩
  obtain ⟨a, haBL, ha3, hBL, hBel⟩ :=
    exists_point_of_hyperplane hA.1 hA.2 hcA hD.orderOf_eq hcL hAa hB hcB
  have hF : Frame2 L c a := ⟨hD.commute hcA haBL.1.1, hD.orderOf_eq, hcL, haBL.2, ha3⟩
  obtain ⟨t, htLW, htinv⟩ := hInv G A c₀ L₀ hR hfail c hcΓ L hL htype hPGLc R hR'
  have htW : t ∈ Subgroup.normalizer (A : Set G) := htLW.2
  have htc : t * c * t⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer htLW.1),
      mul_inv_cancel_right]
  have hta : t * a * t⁻¹ = a⁻¹ := htinv a haBL
  have hR0 : R ≠ ⊥ := by
    intro h0
    have hAB : A ≤ B := fun y hy => ⟨hy, Subgroup.mem_centralizer_iff.mpr fun r hr => by
      have hr1 : r = 1 := Subgroup.mem_bot.mp (by rw [h0] at hr; exact hr)
      rw [hr1, one_mul, mul_one]⟩
    have h1 := Subgroup.card_le_of_le hAB
    have h2 := hB.2
    have h3 := hA.2
    omega
  have hpts : ∀ F ∈ gammaA A (lB A), F ≤ B →
      F = Subgroup.zpowers c ∨ F = Subgroup.zpowers a ∨ F = Subgroup.zpowers (c * a) ∨
        F = Subgroup.zpowers (c ^ 2 * a) := by
    intro F hFΓ hFB
    obtain ⟨-, hF3, f, rfl, -⟩ := hFΓ.1
    obtain ⟨i, j, rfl⟩ := hBel f (hFB (Subgroup.mem_zpowers f))
    have hne : c ^ i * a ^ j ≠ 1 := by
      intro h1
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hF3
      norm_num at hF3
    exact hF.zpowers_cases hne
  have hca : Subgroup.zpowers (c * a) ∉ gammaA A (lB A) := by
    intro hcaΓ
    have hc2aΓ : Subgroup.zpowers (c ^ 2 * a) ∈ gammaA A (lB A) := by
      have h1 := Proof1413Res2.map_conj_mem_gammaA htW hcaΓ
      rwa [hF.map_conj_ca htc hta] at h1
    exact false_of_pointsC h1413 h142 hbot h131 h133 h1416 hPGL h422 h45 hOne hR hfail hcΓ hL
      htype hR' hF hB hcB haBL.1 hBel htW htc hta hcaΓ hc2aΓ
  have hc2a : Subgroup.zpowers (c ^ 2 * a) ∉ gammaA A (lB A) := by
    intro hc2aΓ
    apply hca
    have h1 := Proof1413Res2.map_conj_mem_gammaA htW hc2aΓ
    rwa [hF.map_conj_c2a htc hta] at h1
  have hpts' : ∀ F ∈ gammaA A (lB A), F ≤ B →
      F = Subgroup.zpowers c ∨ F = Subgroup.zpowers a := by
    intro F hFΓ hFB
    rcases hpts F hFΓ hFB with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hFΓ) hca
    · exact absurd (h ▸ hFΓ) hc2a
  have haΓ : Subgroup.zpowers a ∈ gammaA A (lB A) := by
    obtain ⟨S, hS', hRS⟩ := Proof1413.exists_scriptQPiStar_top hR'.prop
    have hRB : R ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.le_centralizer_iff.mpr inf_le_right
    have hSB : S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
      intro h0
      apply hR0
      rw [eq_bot_iff, ← h0]
      exact le_inf hRS hRB
    obtain ⟨F₁, hF₁, F₂, hF₂, hne, hF₁B, hF₂B⟩ := h1418 G A c₀ L₀ hR hfail S hS' B hB hSB
    rcases hpts' F₁ hF₁ hF₁B with h1 | h1
    · rcases hpts' F₂ hF₂ hF₂B with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · exact h2 ▸ hF₂
    · exact h1 ▸ hF₁
  ext F
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hFΓ, hFB⟩
    rcases hpts' F hFΓ hFB with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hBL.symm)
  · rintro (rfl | rfl)
    · exact ⟨hcΓ, Subgroup.zpowers_le.mpr hcB⟩
    · rw [hBL]
      exact ⟨haΓ, Subgroup.zpowers_le.mpr haBL.1⟩

end CFSG.RankThree.PartTwo.Sec14
