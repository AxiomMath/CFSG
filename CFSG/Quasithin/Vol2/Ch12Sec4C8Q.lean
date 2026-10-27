module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Stmt
public import CFSG.Goldschmidt.Steps.AxB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248

namespace S1248

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_centralizer_le {U₀ U : Subgroup G} (hU : IsPGroup 2 U) (hU₀U : U₀ ≤ U)
    (hUC : U ≤ Subgroup.centralizer (U₀ : Set G)) :
    QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) ≤
      Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer (U₀ : Set G)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (U₀ : Set G) with hH
  set P := pCoreOf 2 H with hP
  set R := QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) with hR
  have hCH : Subgroup.centralizer (U : Set G) ≤ H := Subgroup.centralizer_le hU₀U
  have hRC : R ≤ Subgroup.centralizer (U : Set G) := QuasithinUnique.oddCoreIn_le _
  have hRH : R ≤ H := hRC.trans hCH
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hcop : Nat.Coprime (Nat.card R) 2 :=
    Nat.coprime_two_right.2 (QuasithinUnique.odd_card_oddCoreIn _)
  have hRP : R ⊓ P = ⊥ := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hcop' : Nat.Coprime (Nat.card R) (Nat.card P) := by
      rw [hk]
      exact Nat.Coprime.pow_right k hcop
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop')
  have hRU : ⁅R, U⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hRC
  have hfix : P ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (R : Set G) := by
    rintro x ⟨hxP, hxU⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : x * r * x⁻¹ * r⁻¹ ∈ R :=
      R.mul_mem ((Subgroup.mem_normalizer_iff.1
        (QuasithinUnique.le_normalizer_oddCoreIn _ hxU) r).1 hr) (R.inv_mem hr)
    have h2 : x * r * x⁻¹ * r⁻¹ ∈ P := by
      have h3 : r * x⁻¹ * r⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.1 (hHP (hRH hr)) x⁻¹).1 (P.inv_mem hxP)
      have e : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
      rw [e]
      exact P.mul_mem hxP h3
    have h4 : x * r * x⁻¹ * r⁻¹ = 1 := by
      have h5 : x * r * x⁻¹ * r⁻¹ ∈ R ⊓ P := ⟨h1, h2⟩
      rw [hRP] at h5
      exact h5
    calc r * x = (x * r * x⁻¹ * r⁻¹)⁻¹ * (x * r) := by group
      _ = x * r := by rw [h4, inv_one, one_mul]
  exact Subgroup.le_centralizer_iff.1 (CFSG.Goldschmidt.N10 G P R U hP2 hcop hU
    (hRH.trans hHP) (hUC.trans hHP) hRU hfix)

end S1248

theorem oddCentQ1248_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) :
    OddCentQ1248 := by
  intro G _ _ T L V U hS U₀ hU₀ _
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hS.cx hS.quot
  have hVp : IsPGroup 2 V := hS.cx.hyp.sylow.1.to_le hf.le_T
  exact S1248.oddCoreIn_centralizer_le (hVp.to_le hS.le) hU₀
    fun u hu => Subgroup.centralizer_le (hU₀.trans hS.le) (hf.le_centralizer (hS.le hu))

end CFSG.Quasithin.H13
