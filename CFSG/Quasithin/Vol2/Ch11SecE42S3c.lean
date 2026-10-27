module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.Vol2.Ch11SecE42S2b
public import CFSG.Quasithin.Vol2.Ch11SecE42S3a

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem le_centralizer_of_cartan (hF : Facts42) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h : Hyp11 G T L I n) {V₁ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hX : IsCartanX T L X) {z : G} (hzV₁ : z ∈ V₁) (hz1 : z ≠ 1) {Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hYz : Y ≤ Subgroup.centralizer ({z} : Set G)) :
    Y ≤ Subgroup.centralizer (V₁ : Set G) := by
  have hnat := SecD.natSetting11_of h1102 h1141 h hV₁
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1, one_mul, mul_one]
  obtain ⟨x, hx, hxw⟩ := hF.cartan G T L I n V₁ X hnat hV₁ hX z hzV₁ hz1 w hw hw1
  have hk' : x⁻¹ * k * x ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXY hx)) k).mp hk
    simpa using this
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hYz hk')
  rw [← hxw]
  calc x * z * x⁻¹ * k = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by rw [hc]
    _ = k * (x * z * x⁻¹) := by group

theorem normalizer_thompsonJ_le (hK : QuasithinUnique.quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) {K R : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hmax : quasithinIsMaximalLocal T K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hOR : pCoreOf 2 (K ⊔ T) ≤ R) (hRT : R ≤ T)
    (hJ : thompsonJ R ≤ pCoreOf 2 (K ⊔ T)) :
    Subgroup.normalizer (thompsonJ R : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := lemma_1_2_7_three hK hs hnab (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
    (a39ForSQTK_of_cat h39) hT hmax
  rw [conjClosure_eq_self hTK] at hU
  have hJeq : thompsonJ (pCoreOf 2 (K ⊔ T)) = thompsonJ R :=
    QuasithinUnique.GammaExtra.thompsonJ_eq_of_le hJ hOR
  have hKT : K ⊔ T ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
    rw [← hJeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
      (QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hR2 : IsPGroup 2 R := hT.1.to_le hRT
  have hR1 : R ≠ ⊥ := fun h0 => hmax.1.2.2.2 (le_bot_iff.mp (h0 ▸ hOR))
  have hJ1 := QuasithinUnique.Setup.thompsonJ_ne_bot hR2 hR1
  have hJO : thompsonJ R ≤ pCoreOf 2 (Subgroup.normalizer (thompsonJ R : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (hR2.to_le (B6.thompsonJ_le R))
  have hO : pCoreOf 2 (Subgroup.normalizer (thompsonJ R : Set G)) ≠ ⊥ := fun h0 =>
    hJ1 (le_bot_iff.mp (h0 ▸ hJO))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  rw [← hU.2 M' ⟨hM'.1, hKT.trans hM'.2⟩]
  exact hM'.2

theorem not_thompsonJ_le (hF : Facts42) (hF43 : Facts43) (hN : SecA.NatFacts)
    (hPar : ParInFacts) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) {V₁ : Subgroup G} {z : G}
    (hc : Conf11_4_2 T L I n V₁ z) (hmax : quasithinIsMaximalLocal T (kz L V₁ z)) :
    ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T) := by
  intro hJ
  have h := hc.hyp
  obtain ⟨hTK, hLK, hKz, hnC, -, hzV₁⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  have hNJ := normalizer_thompsonJ_le h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h38 h39
    h.fsu.sylow hmax hTK (pCoreOf_le_rOf h hLK) (rOf_le_T h V₁) hJ
  have hXK : X ≤ Subgroup.normalizer (kz L V₁ z : Set G) :=
    (cartan_le_normalizer_rOf hN hPar h1102 h hcV hc.vi hX).trans
      ((QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ _).trans hNJ)
  exact hnC (le_centralizer_of_cartan hF h1102 h1141 h hc.vi hX hzV₁ hc.ne_one hXK hKz)

end CFSG.Quasithin.Vol2.Ch11.SecE
