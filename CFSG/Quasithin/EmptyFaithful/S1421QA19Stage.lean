module

public import CFSG.Quasithin.EmptyFaithful.S1421QA19Ctx
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Cent
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Bend
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Gen
public import CFSG.Quasithin.EmptyFaithful.S1421QA15SLe2
public import CFSG.Quasithin.EmptyFaithful.S1421QNSRad
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA19

theorem centA_mem_benderLs {N : ℕ} (hN : smallOrder N) : centA N ∈ benderLs := by
  rcases hN with rfl | rfl | rfl | rfl | rfl <;> simp [centA, benderLs]

theorem not_prime_card_isL2Quot {n : ℕ} (hn : 2 ≤ n) {X : Type*} [Group X]
    (h : IsL2Quot n X) : ¬ (Nat.card X).Prime := by
  rw [h.card (by omega)]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ 4 ^ n := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact Nat.not_prime_mul (by omega) (by omega)

theorem three_dvd_card_isL2Quot {n : ℕ} (hn : 1 ≤ n) {X : Type*} [Group X] (h : IsL2Quot n X) :
    3 ∣ Nat.card X := by
  rw [h.card hn]
  have : 3 ∣ 4 ^ n - 1 := by
    have := Nat.sub_dvd_pow_sub_pow 4 1 n
    simpa using this
  exact Dvd.dvd.mul_left this _

end QA19

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

abbrev zbar (L : Subgroup G) (z : G) (hz : z ∈ L) : ↥L ⧸ CFSG.pCore 2 ↥L :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hz⟩

theorem Core3Ctx.small_data (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (hd : Core3SmallData) (hcd : QA19.Core3CentData)
    (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hsm : Core3IsSmall (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ (N : ℕ) (z : G) (hz : z ∈ L), QA19.smallOrder N ∧
      (N = 86775571046077562880 → IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
      H ≤ Subgroup.centralizer ({z} : Set G) ∧
      Nat.card (Subgroup.centralizer ({zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L))) ∣
        QA19.centA N ∧
      Nat.card (OTwoQuot K1) ∣ QA19.centA N ∧
      ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (OTwoQuot K1) ∧ QA19.benderN (QA19.centA N) n := by
  obtain ⟨hex, -⟩ := hd _ hsm
  obtain ⟨N, hN, hX, hJ4⟩ := hcd _ hsm
  obtain ⟨z, hz, -, hHz, hord, P, hP, hPle⟩ := c.exists_involution_data hF h36 h38 hq hex
  refine ⟨N, z, hz, hN, hJ4, hHz, hX.2 _ hord ⟨P, hP, hPle⟩, ?_⟩
  have hK1H : K1 ≤ H := Q9.k1_le_H c.st
  have hdvd1 := QA19.card_oTwoQuot_dvd_card_centralizer c.lt_L.le hz (hK1H.trans hHz)
  have hcdvd := hX.2 _ hord ⟨P, hP, hPle⟩
  obtain ⟨n, hn2, hBQ⟩ := c.st.notation_.bender
  have hmem := QA19.centA_mem_benderLs hN
  obtain ⟨hL2, hnN⟩ := QA19.IsBenderQuot.isL2Quot_of_dvd hn2 hBQ hmem (hdvd1.trans hcdvd)
  exact ⟨hdvd1.trans hcdvd, n, hn2, hL2, hnN⟩

end S1421

namespace QA19

open CFSG.Quasithin.S1421NS in
theorem core3KThree_of_inputs (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (hd : Core3SmallData) (hcd : Core3CentData) : Core3KThree := by
  intro G _ _ T M H K1 L M₁ c hq hsm
  obtain ⟨N, z, hz, -, -, -, -, -, n, hn2, hL2, -⟩ := c.small_data hF h36 h38 hd hcd hq hsm
  have hsimple : IsSimpleGroup (OTwoQuot K1) := isSimpleGroup_of_isL2Quot hn2 hL2
  have hrad : solvRad K1 ≤ pCoreOf 2 K1 :=
    solvRad_le_pCoreOf_of_simple hsimple (not_prime_card_isL2Quot hn2 hL2)
  have h3 : 3 ∣ Nat.card K1 :=
    (three_dvd_card_isL2Quot (by omega) hL2).trans (Subgroup.card_quotient_dvd_card _)
  have h1 : K1 ≤ oPrimeResidualOf 3 K1 :=
    le_oPrimeResidualOf_of_cComp c.st.notation_.cComp_mem hrad h3
  have h1' : K1 ≤ oPrimeResidualOf 3 (oTwoUpper H) :=
    h1.trans (Subgroup.closure_mono fun x hx => ⟨c.st.notation_.le_K hx.1, hx.2⟩)
  have hT : IsPGroup 2 T := (Q9.isSylowTwoOf_H c.st).2.1
  exact oTwoUpper_le_oPrimeResidualOf_of_k1 hT c.st.hStar.1.1 (Q9.sup_eq_hStar c.st) h1'

end QA19

end CFSG.Quasithin
