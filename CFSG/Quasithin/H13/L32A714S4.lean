module

public import CFSG.Quasithin.H13.L32ASk5
public import CFSG.Quasithin.H13.L32A71

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

structure Ctx722 (G : Type) [Group G] [Finite G] (T L V H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g k : ↥((L ⊔ T) ⊔ H)) : Prop where
  setting : Setting147 G T L V H
  three : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))
  hypF98 : HypF98 T V L (fsuV1 T V) V H
  not1471 : L32A.Not1471 T L V H γ γ' g k
  eq_hz : H = L32A.hz T V
  eq_kt : H = oTwoUpper H ⊔ T
  l1_eq : L32A.l1 T L V = oTwoUpper (L32A.o2z (oTwoUpper H))
  l1_normal : H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G)
  u_comm : ⁅fsuU T V, L32A.l1 T L V⁆ ⊔ fsuV1 T V = fsuU T V
  card_u : (fsuV1 T V).relIndex (fsuU T V) = 64
  faithful_u : ∀ x ∈ oTwoUpper H, (∀ u ∈ fsuU T V, x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V) →
    x ∈ pCoreOf 2 (oTwoUpper H)
  irred_u : ∀ W : Subgroup G, fsuV1 T V ≤ W → W ≤ fsuU T V →
    oTwoUpper H ≤ Subgroup.normalizer (W : Set G) → W = fsuV1 T V ∨ W = fsuU T V
  fpf_u : ∀ u ∈ fsuU T V, (∀ l ∈ L32A.l1 T L V, l * u * l⁻¹ * u⁻¹ ∈ fsuV1 T V) →
    u ∈ fsuV1 T V
  card_ualpha : (pCoreOf 2 H).relIndex (conjSub (k : G) (F8.Uγ V H (g : G)) ⊔ pCoreOf 2 H) = 2
  ualpha_central : modO2Image H (conjSub (k : G) (F8.Uγ V H (g : G))) ≤
    (Subgroup.center ↥(modO2Image H T)).map (modO2Image H T).subtype
  ualpha_omega : ∀ r ∈ modO2Image H (pCoreOf 2 (L32A.l1 T L V ⊔ T)), r ^ 2 = 1 →
    r ∈ modO2Image H (conjSub (k : G) (F8.Uγ V H (g : G)))
  comm_ualpha : ⁅fsuU T V, conjSub (k : G) (F8.Uγ V H (g : G))⁆ ⊔ fsuV1 T V = V
  cent_q : ∀ u ∈ fsuU T V, (∀ q ∈ pCoreOf 2 (L ⊔ T), q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V) → u ∈ V
  v_le_e : V ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆
  relIndex_ve : V.relIndex ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = 4
  relIndex_eu : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆.relIndex (fsuU T V) = 4
  fpf_e : ∀ e ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, (∀ l ∈ L32A.l1 T L V, l * e * l⁻¹ * e⁻¹ ∈ V) →
    e ∈ V
  ualpha_mem : ∃ l ∈ L, conjSub (k : G) (F8.Uγ V H (g : G)) = conjSub l (fsuU T V)
  conj_cases : ∀ l ∈ L, conjSub l (fsuU T V) = fsuU T V ∨
    ∃ x ∈ L32A.l1 T L V ⊔ T, conjSub l (fsuU T V) = conjSub x (conjSub (k : G) (F8.Uγ V H (g : G)))
  sq : ⁅L32A.sL T L V, pCoreOf 2 (L ⊔ T)⁆ = conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L
  rq : ⁅conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L, pCoreOf 2 (L ⊔ T)⁆ = V
  r_center : conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ centerOf (L32A.sL T L V)
  frattini : frattiniOf (L32A.sL T L V) = ⁅L32A.sL T L V, L32A.sL T L V⁆ ∧
    ⁅L32A.sL T L V, L32A.sL T L V⁆ = V
  qh_eq : pCoreOf 2 H =
    pCoreOf 2 (oTwoUpper H) ⊔ (pCoreOf 2 H ⊓ Subgroup.centralizer (fsuU T V : Set G))
  relIndex_pc : (pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex
    (pCoreOf 2 (oTwoUpper H)) = 64
  cases_720 : ⁅H ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper H⁆ ≤ fsuU T V ∨
    ∃ W₁ W₂ : Subgroup G, fsuU T V ≤ W₂ ∧ W₂ ≤ W₁ ∧
      W₁ ≤ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) ∧
      H ≤ Subgroup.normalizer (W₁ : Set G) ∧ H ≤ Subgroup.normalizer (W₂ : Set G) ∧
      W₂.relIndex W₁ = 64 ∧
      (∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₂ ∧ x ^ 2 ∈ W₂) ∧
      (∀ X : Subgroup G, W₂ ≤ X → X ≤ W₁ → oTwoUpper H ≤ Subgroup.normalizer (X : Set G) →
        X = W₂ ∨ X = W₁) ∧
      (∀ x ∈ H, (∀ w ∈ W₁, x * w * x⁻¹ * w⁻¹ ∈ W₂) → x ∈ pCoreOf 2 H) ∧
      ⁅W₂, oTwoUpper H⁆ ≤ fsuU T V ∧
      ⁅H ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper H⁆ ≤ W₁
  o2_l1 : pCoreOf 2 (L32A.l1 T L V) = pCoreOf 2 (oTwoUpper H)
  relIndex_pq : (pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T)).relIndex
    (pCoreOf 2 (oTwoUpper H)) = 4
  pq_eq : pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T) =
    ⁅pCoreOf 2 (oTwoUpper H), pCoreOf 2 (L ⊔ T)⁆ ⊔
      (pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G))
  center_p : ∀ x ∈ pCoreOf 2 (oTwoUpper H), (∀ y ∈ pCoreOf 2 (oTwoUpper H), x * y = y * x) →
    ∀ k ∈ oTwoUpper H, x * k = k * x

end CFSG.Quasithin.H13
