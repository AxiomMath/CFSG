module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgGe
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Statements

@[expose] def KF148SubfieldOver : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X K H : Subgroup Γ) (σ : Γ) (n : ℕ), 1 ≤ n →
    Sec4.IsoLThreePi ↥X 2 (3 * n) → KFacts.InducesStdKind X σ .field → σ ^ 3 = 1 →
    σ ∈ Subgroup.normalizer (X : Set Γ) → K ≤ X → K ≤ Subgroup.centralizer ({σ} : Set Γ) →
    IsSimpleGroup ↥K → Sec4.IsoLThreePi ↥K 2 n → K ≤ H → H ≤ X →
      H = X ∨ (H ≤ Subgroup.normalizer (K : Set Γ) ∧ Nat.card H ∣ 3 * Nat.card K)

@[expose] def Step148RankImgGeFieldTopDich : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) → J = Y →
        letI := ker148_normal hY.2
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) ∨
          img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y K

@[expose] def Step148RankImgGeFieldTopNotK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) → J = Y →
        letI := ker148_normal hY.2
        ¬ img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y K

end Statements

namespace Item148Res6

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem mem_of_dvd_three_mul_card {K H : Subgroup Γ} (hKH : K ≤ H)
    (hHN : H ≤ Subgroup.normalizer (K : Set Γ)) (hH : Nat.card H ∣ 3 * Nat.card K) {x : Γ}
    (hxH : x ∈ H) (hx3 : ¬ 3 ∣ orderOf x) : x ∈ K := by
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set Γ) :=
    (Subgroup.zpowers_le.mpr hxH).trans hHN
  have hprod := Sec6.card_sup_mul_card_inf hxN
  have hsup : Nat.card (Subgroup.zpowers x ⊔ K : Subgroup Γ) ∣ 3 * Nat.card K :=
    (Subgroup.card_dvd_of_le (sup_le (Subgroup.zpowers_le.mpr hxH) hKH)).trans hH
  set i := Nat.card (Subgroup.zpowers x ⊓ K : Subgroup Γ) with hi
  have hdvd : Nat.card (Subgroup.zpowers x) * Nat.card K ∣ 3 * i * Nat.card K := by
    rw [← hprod]
    calc Nat.card (Subgroup.zpowers x ⊔ K : Subgroup Γ) * i ∣ (3 * Nat.card K) * i :=
          Nat.mul_dvd_mul_right hsup i
      _ = 3 * i * Nat.card K := by ring
  have hdvd' : Nat.card (Subgroup.zpowers x) ∣ 3 * i :=
    Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) 3 := by
    rw [Nat.card_zpowers]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx3).symm
  have hdi : Nat.card (Subgroup.zpowers x) ∣ i := hcop.dvd_of_dvd_mul_left hdvd'
  have heq : Subgroup.zpowers x ⊓ K = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos hdi)
  have hx : x ∈ Subgroup.zpowers x ⊓ K := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact hx.2

end Item148Res6

open Item148Res6

section Provers

theorem step148RankImgGeFieldTopDich_of (hKF : KF148SubfieldOver) :
    Step148RankImgGeFieldTopDich := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hJY
  let := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKY : K ≤ Y := hKYC.trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hKX : K ≤ deltaZero A (lB A) Y := hP.2.2.2.2.2.2.1.le.trans (deltaZero_mono148 hKY)
  have : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  obtain ⟨n, hn, hKn, hJn, hkind⟩ := hF
  have hKs : IsSimpleGroup ↥(img148 A Y K) :=
    (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hKn).1
  have hXJ : img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y J := by
    rw [hJY]
    exact img148_mono (deltaZero_le Y)
  have heN : alpha148 A Y e he ∈
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ (alpha148_mem_img148 he)
  have hKC : img148 A Y K ≤
      Subgroup.centralizer ({alpha148 A Y e he} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro z hz
    obtain ⟨k, hkM, hkK, rfl⟩ := mem_img148_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKe hkK))
  rcases hKF _ (img148 A Y J) (img148 A Y K) (img148 A Y (deltaZero A (lB A) Y))
      (alpha148 A Y e he) n hn hJn hkind (alpha148_pow_three hA3 he) heN (img148_mono hKJ) hKC
      hKs hKn (img148_mono hKX) hXJ with h | ⟨hN, hdvd⟩
  · exact Or.inl h.ge
  · right
    refine Item148Res4.img148_deltaZero_le fun R hR => ?_
    intro x hx
    have hxX : x ∈ img148 A Y (deltaZero A (lB A) Y) :=
      img148_mono (le_deltaZero hR.1 hR.2) hx
    have hR3 : ¬ 3 ∣ Nat.card R :=
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mp (mem_scriptQ_iff.mp hR.1.1).1
    have hRb3 : ¬ 3 ∣ Nat.card (img148 A Y R) := Item148PtRes.not_three_dvd_card_img148 hR3
    have hx3 : ¬ 3 ∣ orderOf x := fun h => hRb3 (h.trans (Subgroup.orderOf_dvd_natCard _ hx))
    exact mem_of_dvd_three_mul_card (img148_mono hKX) hN hdvd hxX hx3

theorem step148RankImgGeFieldTop_of_dich (hD : Step148RankImgGeFieldTopDich)
    (hNK : Step148RankImgGeFieldTopNotK) : Step148RankImgGeFieldTop :=
  fun G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hJY =>
    (hD G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hJY).resolve_right
      (hNK G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA hJY)

end Provers

end CFSG.RankThree.PartTwo.Sec14
