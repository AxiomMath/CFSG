module

public import CFSG.Quasithin.Vol2.Ch3T326PK
public import CFSG.Quasithin.Vol2.Ch3T326PM
public import CFSG.Quasithin.Vol2.Ch3T326PJ

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem card_eq_five_or_of_le {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 5 ↥P) (hexp : ∀ g ∈ P, g ^ 5 = 1) (hle : Nat.card ↥P ≤ 25)
    (hne : ∃ c ∈ P, c ≠ 1) :
    Nat.card ↥P = 5 ∨ (Nat.card ↥P = 25 ∧ ∀ x ∈ P, x ^ 5 = 1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  obtain ⟨c, hcP, hc1⟩ := hne
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero, Subgroup.card_eq_one] at hm
    rw [hm, Subgroup.mem_bot] at hcP
    exact hc1 hcP
  have hm2 : m ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 5 ^ 3 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hcon
    rw [hm] at hle
    omega
  interval_cases m
  · exact Or.inl (by rw [hm]; norm_num)
  · exact Or.inr ⟨by rw [hm]; norm_num, hexp⟩

theorem O2Sit.o2_card {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (h : O2Sit M Mp T L V t) :
    Nat.card ↥(oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 5 ∨
      (Nat.card ↥(oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 25 ∧
        ∀ x ∈ oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))), x ^ 5 = 1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S⟩ : Nonempty (Sylow 5 ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) :=
    inferInstance
  obtain ⟨c, hcC, hc1, hodd⟩ := h.exists_odd_ne_one
  have hcO : c ∈ oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) :=
    mem_oTwoUpper_of_odd hcC hodd
  rw [h.oTwoUpper_eq S] at hcO ⊢
  obtain ⟨hexp, -, hle⟩ := h.five_subgroup (P := (S : Subgroup _).map (Subgroup.subtype _))
    (Subgroup.map_subtype_le _) (S.2.map _)
  exact card_eq_five_or_of_le (S.2.map _) hexp hle ⟨c, hcO, hc1⟩

theorem o2_card_of_d321
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42) (h36 : D36c) (h37 : D37)
    (hB56 : AsB56) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hL38 : D3L38) {M Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} (hD : D3Std M Mp T L V) {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ)) (htop : orbSup T V ≠ ⊤) (hL3 : IsPSL 3 2 1 ↥L) :
    Nat.card ↥(oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 5 ∨
      (Nat.card ↥(oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 25 ∧
        ∀ x ∈ oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))), x ^ 5 = 1) := by
  obtain ⟨X, V', t', A, r, hS, hVt, hU, hAC, hAL, hL3', hnat⟩ := exists_natSide hA21 hB42 h9
    h36 h37 hB56 h38 hA23 hSzF hL38 hD htT htn hMp hqM htop hL3
  exact (O2Sit.of hA21 hB42 h9 hS hVt hU hAC hAL hL3' hnat).o2_card

theorem d321O2_of
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42) (h36 : D36c) (h37 : D37)
    (hB56 : AsB56) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hL38 : D3L38) : D321O2 := by
  intro W _ _ M Mp T L V hD t htT htn hMp hqM htop hL3
  exact o2_card_of_d321 hA21 hB42 h9 h36 h37 hB56 h38 hA23 hSzF hL38 hD htT htn hMp hqM htop hL3

end CFSG.Quasithin.H13.T326
