module

public import CFSG.Quasithin.Vol2.Ch11SecA12Cases
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.Ch11SecA12O3
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin

variable {H : Type} [Group H] [Finite H]

theorem oPrimeResidualOf_eq_top {K A : Subgroup H} [K.Normal] (hsup : K ⊔ A = ⊤)
    (hA : IsPGroup 3 A) (hO : CFSG.pPrimeCore 3 H = (CFSG.pCore 2 ↥K).map K.subtype)
    (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∣ 3)
    (h9 : 9 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) :
    oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ
  set R := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) with hR
  have hRn : R.Normal := oPrimeResidualOf_top_normal 3
  obtain ⟨e⟩ := starImage_mulEquiv hO
  have hQ' : CFSG.IsQuasisimple ↥(starImage 3 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  have hKR : starImage 3 K ≤ R := by
    by_contra hne
    have hNn : (R.subgroupOf (starImage 3 K)).Normal := Subgroup.Normal.subgroupOf hRn _
    have hNt : R.subgroupOf (starImage 3 K) ≠ ⊤ := fun ht =>
      hne (Subgroup.subgroupOf_eq_top.mp ht)
    have hNZ := le_center_of_normal_ne_top hQ' hNt
    have hZ' : Nat.card (Subgroup.center ↥(starImage 3 K)) ∣ 3 := by
      have h1 := Subgroup.map_center_eq e
      rw [← h1, Subgroup.card_map_of_injective e.injective] at hZ
      exact hZ
    have h9' : 3 ^ 2 ∣ Nat.card ↥(starImage 3 K) := by
      rw [Nat.card_congr e.toEquiv]
      exact h9
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9'
    have hPN : P ≤ R.subgroupOf (starImage 3 K) := by
      intro z hz
      obtain ⟨m, hm⟩ := (IsPGroup.of_card hP) ⟨z, hz⟩
      refine Subgroup.mem_subgroupOf.mpr (mem_oPrimeResidualOf_top_of_pow Nat.prime_three
        (m := m) ?_)
      have : z ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
    have h1 := (Subgroup.card_dvd_of_le (hPN.trans hNZ)).trans hZ'
    rw [hP] at h1
    norm_num at h1
  have hAR : A.map π ≤ R := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
    refine mem_oPrimeResidualOf_top_of_pow Nat.prime_three (m := m) ?_
    have : a ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [← map_pow, this, map_one]
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _), ← hsup,
    Subgroup.map_sup]
  exact sup_le hKR hAR

theorem case2_mulEquiv (hPSL : FactList2PSL3) {K A : Subgroup H} [K.Normal]
    (hsup : K ⊔ A = ⊤) (hA : IsPGroup 3 A)
    (hO : CFSG.pPrimeCore 3 H = (CFSG.pCore 2 ↥K).map K.subtype)
    (hP : CFSG.pCore 2 H = (CFSG.pCore 2 ↥K).map K.subtype)
    (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∣ 3)
    (h9 : 9 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) 2) (h2 : A318Case2 (starImage 3 K)) :
    IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (H ⧸ CFSG.pCore 2 H ≃* (Matrix.GeneralLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F))) := by
  obtain ⟨s, q, -, ⟨p, e, hp, he, rfl, hS⟩, hO3⟩ := h2
  obtain ⟨φ⟩ := starImage_mulEquiv hO
  have hS' := IsPSLEps3.of_mulEquiv φ hS
  obtain ⟨rfl, rfl, rfl⟩ := hPSL _ hlist s p e hp he hS'
  refine ⟨hS', ?_⟩
  rcases hO3 with ⟨F, _, _, hF, ⟨ψ⟩⟩ | ⟨m, hm, -⟩
  · obtain ⟨χ⟩ := statedProj_top_mulEquiv F
    have hR := oPrimeResidualOf_eq_top hsup hA hO hQ hZ h9
    refine ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num, ⟨?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq (hP.trans hO.symm)).trans
      ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hR.symm)).trans (ψ.trans χ))
  · exfalso
    have h3 : 2 = 3 * m := Nat.pow_right_injective le_rfl hm
    omega

end CFSG.Quasithin.Vol2.Ch11.SecA
