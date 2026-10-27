module

public import CFSG.Quasithin.H13.L32AC36j
public import CFSG.Quasithin.H13.L32AC36l
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem alt5_center : ∀ z : alternatingGroup (Fin 5), (∀ g, z * g = g * z) → z = 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

theorem groups_of_hom {W : Type} [CommGroup W] [Finite W] (Ψ : ↥H →* MulAut W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) (hKH : K ≤ H) (hTH : T ≤ H)
    (hKnH : H ≤ Subgroup.normalizer (K : Set G)) (hT : IsSylowTwoOf T H) (hHKT : H = K ⊔ T) :
    (K.subgroupOf H).map Ψ ≤ Ψ.range ∧
    Ψ.range ≤ Subgroup.normalizer (((K.subgroupOf H).map Ψ : Subgroup _) : Set (MulAut W)) ∧
    Subgroup.centralizer (((K.subgroupOf H).map Ψ : Subgroup _) : Set (MulAut W)) ⊓ Ψ.range ≤
      (K.subgroupOf H).map Ψ ∧
    IsSylowTwoOf ((T.subgroupOf H).map Ψ) Ψ.range ∧
    Ψ.range = (K.subgroupOf H).map Ψ ⊔ (T.subgroupOf H).map Ψ := by
  have hLX : (K.subgroupOf H).map Ψ ≤ Ψ.range := Subgroup.map_le_range Ψ _
  have hXN : Ψ.range ≤
      Subgroup.normalizer (((K.subgroupOf H).map Ψ : Subgroup _) : Set (MulAut W)) := by
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨h * k * h⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKnH h.2) k).mp hk
    · rintro ⟨k, hk, hke⟩
      refine ⟨h⁻¹ * k * h, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hKnH (H.inv_mem h.2)) k).mp hk
        simpa using this
      · rw [map_mul, map_mul, map_inv, hke]
        group
  have hXeq : Ψ.range = (K.subgroupOf H).map Ψ ⊔ (T.subgroupOf H).map Ψ := by
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hKH hTH, MonoidHom.range_eq_map]
    congr 1
    conv_rhs => rw [← hHKT]
    exact (Subgroup.subgroupOf_self H).symm
  have hS2 : IsPGroup 2 ((T.subgroupOf H).map Ψ) :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
  have hO2X : pCoreOf 2 Ψ.range = ⊥ := LRed5.pCoreOf_range_eq_bot Ψ hker
  have hSyl : IsSylowTwoOf ((T.subgroupOf H).map Ψ) Ψ.range := by
    have := isSylowTwoOf_map_subgroupOf Ψ hT
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  exact ⟨hLX, hXN, centralizer_inf_le hLX hXN hXeq hS2 hO2X, hSyl, hXeq⟩

theorem nonempty_cStar_equiv_map {W : Type*} [Group W] (Ψ : ↥H →* W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) (hK : K ∈ cComp H) :
    Nonempty (cStar K ≃* ↥((K.subgroupOf H).map Ψ)) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  let f : ↥K →* ↥((K.subgroupOf H).map Ψ) :=
    (Ψ.comp (Subgroup.inclusion hKH)).codRestrict _ fun k =>
      ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hkerf : (pCoreOf 2 K).subgroupOf K = f.ker := by
    ext k
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have e : f k = 1 ↔ Ψ (Subgroup.inclusion hKH k) = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e, hker, ← mem_pCoreOf_iff_of_mem_cComp hK k.2]
    rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerf).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

omit [Finite G] in
theorem card_map_eq_relIndex {W : Type*} [Group W] (Ψ : ↥H →* W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {A : Subgroup G} (hAH : A ≤ H) :
    Nat.card ↥((A.subgroupOf H).map Ψ) = (pCoreOf 2 H).relIndex A := by
  have hk : Ψ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hAH]

theorem exists_orderOf_three {W : Type*} [Group W] [Finite W] (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) (Ψ : ↥H →* W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    ∃ a ∈ ((l1 T L V).subgroupOf H).map Ψ, orderOf a = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hL3 := relIndex_l1 h1222 h1332 h1334 S.hyp
  have hle : l1 T L V ⊓ pCoreOf 2 H ≤ pCoreOf 2 (l1 T L V) := by
    refine le_pCoreOf 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_inf_right)
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(l1 T L V).mul_mem ((l1 T L V).mul_mem g.2 hn.1) ((l1 T L V).inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (hL1H g.2)) n).mp hn.2
    simpa using this
  have hdvd : 3 ∣ Nat.card ↥(((l1 T L V).subgroupOf H).map Ψ) := by
    rw [card_map_eq_relIndex Ψ hker hL1H, ← Subgroup.inf_relIndex_right, inf_comm,
      ← Subgroup.relIndex_mul_relIndex (l1 T L V ⊓ pCoreOf 2 H) (pCoreOf 2 (l1 T L V))
      (l1 T L V) hle (pCoreOf_le 2 _), hL3]
    exact Dvd.intro_left _ rfl
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨a, a.2, by rw [← ha, Subgroup.orderOf_coe]⟩

theorem relIndex_R1_T (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) : (pCoreOf 2 (l1 T L V ⊔ T)).relIndex T = 2 := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  exact hl1eq ▸ S14.index2_eq

theorem card_map_T {W : Type*} [Group W] (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) (hTH : T ≤ H) (Ψ : ↥H →* W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    Nat.card ↥((T.subgroupOf H).map Ψ) =
      2 * Nat.card ↥(((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf H).map Ψ) := by
  have hRT := Setting147.R1_le_T S
  have hQR := Setting147.O2H_le_R1 S
  rw [card_map_eq_relIndex Ψ hker hTH, card_map_eq_relIndex Ψ hker (hRT.trans hTH),
    ← Subgroup.relIndex_mul_relIndex _ _ _ hQR hRT, relIndex_R1_T h1222 h1332 h1334 S, mul_comm]

end CFSG.Quasithin.H13.L32A.C
