module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
import all CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.Quasithin.Background.F1Amalgam
public import Certificates.Certificate40701
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin.F112R.J2L

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312J2
  CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat CFSG.QuasithinUnique.K1.SporadicPerm


theorem row_eq {j : ℕ} (hj : j < 5) :
    defaultRow 7 j2LatD j2OtD j = J2Y9K.mems.getD j ⟨0, 0, 0⟩ := by
  have hm := Certificates.certificate40701.1.2
  calc defaultRow 7 j2LatD j2OtD j
      = ((List.range 5).map (defaultRow 7 j2LatD j2OtD)).getD j ⟨0, 0, 0⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rfl
    _ = J2Y9K.mems.getD j ⟨0, 0, 0⟩ := by rw [hm]

theorem memStmt_Y {j : ℕ} (hj : j < 5) : MemStmt (j2CtxA.Y j) (J2Y9K.mems.getD j ⟨0, 0, 0⟩) := by
  have hJ : j2CtxA.J = 5 := j2A_J
  have h := j2CtxA.memStmt_default (Ot := j2OtD) Certificates.certificate40701.1.1
    (j := j) (by omega)
  have hrow : defaultRow j2CtxA.k j2CtxA.D j2OtD j = J2Y9K.mems.getD j ⟨0, 0, 0⟩ := row_eq hj
  rwa [hrow] at h

theorem card_Y2 : Nat.card (j2CtxA.Y 2) = 1152 := (memStmt_Y (j := 2) (by norm_num)).1

theorem card_Y3 : Nat.card (j2CtxA.Y 3) = 1920 := (memStmt_Y (j := 3) (by norm_num)).1

theorem card_pCoreOf_Y2 : Nat.card (pCoreOf 2 (j2CtxA.Y 2)) = 2 ^ 6 :=
  (memStmt_Y (j := 2) (by norm_num)).2.1

theorem card_pCoreOf_Y3 : Nat.card (pCoreOf 2 (j2CtxA.Y 3)) = 2 ^ 5 :=
  (memStmt_Y (j := 3) (by norm_num)).2.1

theorem Y4_le_Y2 : j2CtxA.Y 4 ≤ j2CtxA.Y 2 := by
  have hJ : j2CtxA.J = 5 := j2A_J
  exact j2CtxA.gensIn_le (by omega) (by omega) Certificates.certificate40701.2.1

theorem Y1_le_Y3 : j2CtxA.Y 1 ≤ j2CtxA.Y 3 := by
  have hJ : j2CtxA.J = 5 := j2A_J
  exact j2CtxA.gensIn_le (by omega) (by omega) Certificates.certificate40701.2.2

theorem overgroup {Z : Subgroup ↥CFSG.Sporadic.J2.J} (hSZ : j2CtxA.S ≤ Z) :
    Z = ⊤ ∨ ∃ j < 5, Z = j2CtxA.Y j ∧ Nat.card Z = (#[1, 3, 9, 15, 3] : Array ℕ)[j]! * 2 ^ 7 := by
  obtain ⟨j, hj, hZ⟩ := lat_all j2CtxA j2A_hL Z hSZ
  by_cases hj5 : j < 5
  · have hm : memberOrTop 5 j2CtxA.Y j = j2CtxA.Y j := by simp [memberOrTop, hj5]
    have hm' : memberOrTop (#[1, 3, 9, 15, 3] : Array ℕ).size j2CtxA.Y j = j2CtxA.Y j := hm
    rw [hm'] at hZ
    exact Or.inr ⟨j, hj5, hZ, by rw [hZ]; exact j2A_card hj5⟩
  · left
    have hm : memberOrTop 5 j2CtxA.Y j = ⊤ := by simp [memberOrTop, hj5]
    exact hZ.trans hm

theorem normalizer_ne_top {P : Subgroup ↥CFSG.Sporadic.J2.J} (hP : P ≠ ⊥) (h2 : IsPGroup 2 P) :
    Subgroup.normalizer (P : Set ↥CFSG.Sporadic.J2.J) ≠ ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hn : P.Normal := Subgroup.normalizer_eq_top_iff.mp h
  haveI := CFSG.Sporadic.J2.isSimpleGroup_J
  rcases hn.eq_bot_or_eq_top with h1 | h1
  · exact hP h1
  · subst h1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h2
    rw [Subgroup.card_top, CFSG.Sporadic.J2.card_J] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 604800)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

theorem not_isTwoLocal_top : ¬ IsTwoLocal (⊤ : Subgroup ↥CFSG.Sporadic.J2.J) := by
  rintro ⟨P, hP, h2, h⟩
  exact normalizer_ne_top hP h2 h.symm

theorem eq_normalizer_of_card {j : ℕ} (hj : j < 5)
    (hc : ∀ i < 5, Nat.card (j2CtxA.Y j) ∣ (#[1, 3, 9, 15, 3] : Array ℕ)[i]! * 2 ^ 7 → i = j)
    (hO : pCoreOf 2 (j2CtxA.Y j) ≠ ⊥) :
    j2CtxA.Y j = Subgroup.normalizer (pCoreOf 2 (j2CtxA.Y j) : Set ↥CFSG.Sporadic.J2.J) := by
  have hle : j2CtxA.Y j ≤ Subgroup.normalizer (pCoreOf 2 (j2CtxA.Y j) : Set ↥CFSG.Sporadic.J2.J) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  rcases overgroup ((j2CtxA.S_le_Y j).trans hle) with h | ⟨i, hi, hN, hcard⟩
  · exact absurd h (normalizer_ne_top hO (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
  · have hdvd : Nat.card (j2CtxA.Y j) ∣ Nat.card (Subgroup.normalizer
        (pCoreOf 2 (j2CtxA.Y j) : Set ↥CFSG.Sporadic.J2.J)) := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    have := hc i hi hdvd
    subst this
    exact hN.symm

theorem isTwoLocal_Y2 : IsTwoLocal (j2CtxA.Y 2) := by
  have hO : pCoreOf 2 (j2CtxA.Y 2) ≠ ⊥ := fun h => by
    have := card_pCoreOf_Y2
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  refine ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, eq_normalizer_of_card (by norm_num)
    (fun i hi h => ?_) hO⟩
  rw [card_Y2] at h
  interval_cases i <;> simp_all

theorem isTwoLocal_Y3 : IsTwoLocal (j2CtxA.Y 3) := by
  have hO : pCoreOf 2 (j2CtxA.Y 3) ≠ ⊥ := fun h => by
    have := card_pCoreOf_Y3
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  refine ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, eq_normalizer_of_card (by norm_num)
    (fun i hi h => ?_) hO⟩
  rw [card_Y3] at h
  interval_cases i <;> simp_all

theorem eq_Y2_or_Y3 {M : Subgroup ↥CFSG.Sporadic.J2.J} (hM : IsMaximalTwoLocal M) (hSM : j2CtxA.S ≤ M) :
    M = j2CtxA.Y 2 ∨ M = j2CtxA.Y 3 := by
  obtain ⟨hloc, hmax⟩ := hM
  rcases overgroup hSM with h | ⟨j, hj, rfl, hcard⟩
  · exact absurd (h ▸ hloc) not_isTwoLocal_top
  · have h2 := card_Y2
    have h3 := card_Y3
    interval_cases j
    · exfalso
      have := hmax _ isTwoLocal_Y3 (by rw [j2CtxA.Y_zero]; exact j2CtxA.S_le_Y 3)
      rw [this] at h3
      simp at hcard
      omega
    · exfalso
      have := hmax _ isTwoLocal_Y3 Y1_le_Y3
      rw [this] at h3
      simp at hcard
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have := hmax _ isTwoLocal_Y2 Y4_le_Y2
      rw [this] at h2
      simp at hcard
      omega

theorem yPair_eq {M₁ M₂ : Subgroup ↥CFSG.Sporadic.J2.J} (hp : IsYAmalgamPair j2CtxA.S M₁ M₂) :
    (M₁ = j2CtxA.Y 3 ∧ M₂ = j2CtxA.Y 2) ∨ (M₁ = j2CtxA.Y 2 ∧ M₂ = j2CtxA.Y 3) := by
  obtain ⟨-, hne, hiff⟩ := hp
  have h1 := (hiff M₁).2 (Or.inl rfl)
  have h2 := (hiff M₂).2 (Or.inr rfl)
  have hS1 : j2CtxA.S ≤ M₁ := Subgroup.le_normalizer.trans h1.2
  have hS2 : j2CtxA.S ≤ M₂ := Subgroup.le_normalizer.trans h2.2
  rcases eq_Y2_or_Y3 h1.1 hS1 with e1 | e1 <;> rcases eq_Y2_or_Y3 h2.1 hS2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · exact Or.inr ⟨e1, e2⟩
  · exact Or.inl ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hne

end CFSG.Quasithin.F112R.J2L
