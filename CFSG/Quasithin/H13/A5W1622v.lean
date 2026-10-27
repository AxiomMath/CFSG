module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.H13.A5W13616a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem isMSPair_of (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hchar : CharTwo (K₀ ⊔ S.Tv))
    (hRk : IsRankTwoLie2Derived
      ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸ Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))) :
    IsMSPair (K₀ ⊔ S.Tv) S.Tv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := K₀ ⊔ S.Tv with hHdef
  have hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have hsylH : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) le_sup_right hHG
  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hO : pCoreOf 2 H ≠ ⊥ := by
    have hle : Subgroup.zpowers S.v12 ≤ H := (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : H ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := hHG hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    intro h
    have hvO := le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
    rw [h, Subgroup.mem_bot] at hvO
    exact S.v12_ne_one hvO
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO
  have hset : (H : Set G) = (K₀ : Set G) * (S.Tv : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₀ S.Tv hTK₀
  have hlt : S.Tv < H := by
    refine lt_of_le_of_ne le_sup_right fun h => ?_
    have hK₀T : K₀ ≤ S.Tv := h ▸ le_sup_left
    apply hz
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := S.conj_z_of_mem_T (hK₀T hk).1
    calc k * S.z = (k * S.z * k⁻¹) * k := by group
      _ = S.z * k := by rw [h1]
  refine ⟨⟨hSQ, hchar, K₀, hK₀, hset, hRk⟩, Or.inl ⟨S.Tv, hlt, hsylH.2.2, ?_⟩, ?_⟩
  · exact (F6.pCoreOf_eq_self_of_isPGroup hsylH.2.1).symm
  · intro C hCT hC hCc hHC
    exact S.not_le_normalizer_of_characteristic h1222 h517 h132two h132fsu h132A5 h331 h1327 h37
      h39 hK₀G hK₀ hTK₀ hz hCT hC hCc (le_sup_left.trans hHC)

end Setting

end CFSG.Quasithin.H13.A5
