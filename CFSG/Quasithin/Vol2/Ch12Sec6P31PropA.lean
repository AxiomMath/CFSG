module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropACore
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAStar
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAFrame
public import CFSG.Quasithin.Background.QuasisimpleSp4G2Facts
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.Milestones.ASVolI.A3Aut.SBSp4
public import CFSG.Milestones.ASVolI.A3Aut.SBG2
public import CFSG.GroupTheory.SteinbergCBFTSCN

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P31
open scoped IsMulCommutative Pointwise commutatorElement

namespace P31A

theorem false_of_propA_setting (h1222 : Stmt12_2_2) {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} [IsMulCommutative ↥V] (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {H K : Subgroup G} (hHK : S126.IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hK₀ : conjClosure K T = K)
    (hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(star H K)))
    (hZ : Subgroup.center ↥(star H K) = ⊥)
    (hSB : ∀ S : Subgroup ↥(star H K), CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
      CFSG.ASVolI.burnsideAut_SolvBorel ↥(star H K) S)
    (hK3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(star H K))) : False := by
  haveI : (star H K).Normal := P31A.normal_star_K F h918 hK₀
  have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup (HStar H)) ≤ 2 :=
    S126P31.pRank_hStar_le hH (S126P31.pCoreOf_ne_bot h918.toHypF98.toHypF91)
  have hT2 : IsPGroup 2 ↥(star H T) := P31A.isPGroup_star_T F hH hHK
  have hTmax : ∀ S : Subgroup (HStar H), IsPGroup 2 ↥S → star H T ≤ S → S = star H T :=
    P31A.star_T_max F hH hHK
  have hTL : star H T ≤ Subgroup.normalizer (star H (S126.Li L F.V1) : Set (HStar H)) :=
    S126P31.star_le_normalizer_star (P31A.L1_le_H F hHK) (P31A.T_le_H F hHK)
      (S126L19b.T_le_normalizer_L1 h1222 hH)
  have hL1solv : Group.IsSolvable ↥(star H (S126.Li L F.V1)) :=
    P31A.isSolvable_star (P31A.isSolvable_L1 h1222 F hH)
  have hL1T : ⁅star H (S126.Li L F.V1), star H T⁆ = star H (S126.Li L F.V1) := by
    rw [← P31A.star_commutator (P31A.L1_le_H F hHK) (P31A.T_le_H F hHK),
      P31A.comm_L1_T h1222 F hH]
  have hL1gen : star H (S126.Li L F.V1) =
      Subgroup.closure {x : HStar H | x ∈ star H (S126.Li L F.V1) ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1} :=
    P31A.star_eq_closure_three (P31A.L1_le_H F hHK)
      (P31A.L1_eq_closure_three h1222 F hH)
  let N : Subgroup G := S126.Li L F.V1 ⊓ Subgroup.centralizer (V : Set G)
  have hN2 : IsPGroup 2 ↥N := P31A.isPGroup_L1_inf_centralizer h1222 F hH
  have hXN : S126.Li L F.V1 ≤ Subgroup.normalizer (N : Set G) := by
    refine Subgroup.le_normalizer_inf ?_ ?_
    · exact Subgroup.le_normalizer
    · exact CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer
        ((S126L19b.L1_le_L F).trans hH.hyp.irrPlus.2.2.1)
  have hNle : star H N ≤ pCoreOf 2 (star H (S126.Li L F.V1)) :=
    P31A.star_le_pCoreOf (N := N) (X := S126.Li L F.V1) inf_le_left
      (P31A.L1_le_H F hHK) hN2 hXN
  have hTL1 : T ≤ Subgroup.normalizer (S126.Li L F.V1 : Set G) :=
    S126L19b.T_le_normalizer_L1 h1222 hH
  have hconj : ∀ t ∈ T, ∀ z ∈ S126.Li L F.V1, t * z * t⁻¹ ∈ S126.Li L F.V1 :=
    fun t ht z hz => (Subgroup.mem_normalizer_iff.1 (hTL1 ht) z).1 hz
  have hmem1 : ∀ t ∈ T, ∀ z ∈ S126.Li L F.V1, ∀ w ∈ S126.Li L F.V1,
      t * z * t⁻¹ * w ∈ S126.Li L F.V1 :=
    fun t ht z hz w hw => (S126.Li L F.V1).mul_mem (hconj t ht z hz) hw
  have hmem2 : ∀ t ∈ T, ∀ z ∈ S126.Li L F.V1, ∀ w ∈ S126.Li L F.V1,
      t * z * t⁻¹ * w⁻¹ ∈ S126.Li L F.V1 :=
    fun t ht z hz w hw =>
      (S126.Li L F.V1).mul_mem (hconj t ht z hz) ((S126.Li L F.V1).inv_mem hw)
  obtain ⟨x, hxL1, y, hyL1, t₁, ht₁T, t₂, ht₂T, h1c, h2c, h3c, hx2ne, hyxne, hyx'ne⟩ :=
    P31A.exists_e9_frame h1222 F hH
  have hxH : x ∈ H := P31A.L1_le_H F hHK hxL1
  have hyH : y ∈ H := P31A.L1_le_H F hHK hyL1
  have ht₁H : t₁ ∈ H := P31A.T_le_H F hHK ht₁T
  have ht₂H : t₂ ∈ H := P31A.T_le_H F hHK ht₂T
  let q : ↥H →* HStar H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let x' : HStar H := q ⟨x, hxH⟩
  let y' : HStar H := q ⟨y, hyH⟩
  let t₁' : HStar H := q ⟨t₁, ht₁H⟩
  let t₂' : HStar H := q ⟨t₂, ht₂H⟩
  have key : ∀ g : ↥H, (g : G) ∈ S126.Li L F.V1 →
      (g : G) ∈ Subgroup.centralizer (V : Set G) →
      q g ∈ pCoreOf 2 (star H (S126.Li L F.V1)) :=
    fun g h₁ h₂ => by
      show q g ∈ pCoreOf 2 (star H (S126.Li L F.V1))
      simpa [q] using hNle (S126P31.mk_mem_star (h := g) ⟨h₁, h₂⟩)
  have key' : ∀ g : ↥H, (∀ k : ℕ, (g : G) ^ (2 ^ k) ≠ 1) →
      q g ∉ pCoreOf 2 (star H (S126.Li L F.V1)) :=
    fun g hg => by
      show q g ∉ pCoreOf 2 (star H (S126.Li L F.V1))
      simpa [q] using P31A.mk_not_mem_pCoreOf (H := H) (g := g) hg
        (star H (S126.Li L F.V1))
  have h1 : t₁' * x' * t₁'⁻¹ * x' ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    rw [show t₁' * x' * t₁'⁻¹ * x' =
        q ((⟨t₁, ht₁H⟩ : ↥H) * ⟨x, hxH⟩ * (⟨t₁, ht₁H⟩ : ↥H)⁻¹ * ⟨x, hxH⟩) by
      simp only [x', t₁', map_mul, map_inv]]
    exact key _ (hmem1 t₁ ht₁T x hxL1 x hxL1) h1c
  have h2 : t₂' * x' * t₂'⁻¹ * y'⁻¹ ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    rw [show t₂' * x' * t₂'⁻¹ * y'⁻¹ =
        q ((⟨t₂, ht₂H⟩ : ↥H) * ⟨x, hxH⟩ * (⟨t₂, ht₂H⟩ : ↥H)⁻¹ * (⟨y, hyH⟩ : ↥H)⁻¹) by
      simp only [x', y', t₂', map_mul, map_inv]]
    exact key _ (hmem2 t₂ ht₂T x hxL1 y hyL1) h2c
  have h3 : t₂' * y' * t₂'⁻¹ * x'⁻¹ ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    rw [show t₂' * y' * t₂'⁻¹ * x'⁻¹ =
        q ((⟨t₂, ht₂H⟩ : ↥H) * ⟨y, hyH⟩ * (⟨t₂, ht₂H⟩ : ↥H)⁻¹ * (⟨x, hxH⟩ : ↥H)⁻¹) by
      simp only [x', y', t₂', map_mul, map_inv]]
    exact key _ (hmem2 t₂ ht₂T y hyL1 x hxL1) h3c
  have hx2 : x' ^ 2 ∉ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    have hg : ∀ k : ℕ, (((⟨x, hxH⟩ : ↥H) ^ 2 : ↥H) : G) ^ (2 ^ k) ≠ 1 := by
      intro k
      simpa [Subgroup.coe_pow] using hx2ne k
    rw [show x' ^ 2 = q ((⟨x, hxH⟩ : ↥H) ^ 2) by simp only [x', map_pow]]
    exact key' _ hg
  have hyx : y' * x' ∉ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    have hg : ∀ k : ℕ, (((⟨y, hyH⟩ : ↥H) * ⟨x, hxH⟩ : ↥H) : G) ^ (2 ^ k) ≠ 1 := by
      intro k
      simpa [Subgroup.coe_mul] using hyxne k
    rw [show y' * x' = q ((⟨y, hyH⟩ : ↥H) * ⟨x, hxH⟩) by simp only [x', y', map_mul]]
    exact key' _ hg
  have hyx' : y' * x'⁻¹ ∉ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    have hg : ∀ k : ℕ,
        (((⟨y, hyH⟩ : ↥H) * (⟨x, hxH⟩ : ↥H)⁻¹ : ↥H) : G) ^ (2 ^ k) ≠ 1 := by
      intro k
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hyx'ne k
    rw [show y' * x'⁻¹ = q ((⟨y, hyH⟩ : ↥H) * (⟨x, hxH⟩ : ↥H)⁻¹) by
      simp only [x', y', map_mul, map_inv]]
    exact key' _ hg
  exact P31A.false_of_propA (X := HStar H) (K := star H K)
    (L₁ := star H (S126.Li L F.V1)) (T := star H T)
    hcyc hZ (hSB _ (P31A.isSylowTwoOf_inf_subgroupOf hT2 hTmax))
    hK3 hX3 hT2 hTmax hTL hL1solv hL1T hL1gen
    (S126P31.mk_mem_star (h := ⟨x, hxH⟩) hxL1)
    (S126P31.mk_mem_star (h := ⟨y, hyH⟩) hyL1)
    (S126P31.mk_mem_star (h := ⟨t₁, ht₁H⟩) ht₁T)
    (S126P31.mk_mem_star (h := ⟨t₂, ht₂H⟩) ht₂T)
    h1 h2 h3 hx2 hyx hyx'

end P31A

theorem noSp4F_w31_of
    (h1222 : Stmt12_2_2) : NoSp4F_w31 := by
  intro h1229 G _ _ T L V _ F hH hV H K hHK h918 hK₀ n hn hSp4
  have hsimple : IsSimpleGroup (starMod_w31 H K) :=
    CFSG.Quasithin.E2.isSimpleGroup_of_isPSp4 hSp4
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1).2
      ⟨P31A.commutator_star_K_eq_top F h918, hsimple⟩
  have hZ : Subgroup.center ↥(star H K) = ⊥ :=
    CFSG.Quasithin.center_eq_bot_of_isPSp4_quot hn hq hSp4
  have hK : CFSG.Quasithin.IsPSp4 2 n ↥(star H K) :=
    CFSG.Quasithin.isPSp4_of_center_eq_bot hZ hSp4
  have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(star H K)) :=
    CFSG.Quasithin.isCyclic_outer_of_isPSp4 hK
  have hSB : ∀ S : Subgroup ↥(star H K), CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
      CFSG.ASVolI.burnsideAut_SolvBorel ↥(star H K) S :=
    CFSG.ASVolI.burnsideAut_solvBorel_Sp4 _ n hn hK
  have hK3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(star H K)) :=
    CFSG.Quasithin.R3c3.two_le_pRank_three_isPSp_two hK
  exact P31A.false_of_propA_setting h1222 F hH hHK h918 hK₀ hcyc hZ hSB hK3

theorem noG2F_w31_of
    (h1222 : Stmt12_2_2) : NoG2F_w31 := by
  intro h1229 G _ _ T L V _ F hH hV H K hHK h918 hK₀ n hn hG2
  have hsimple : IsSimpleGroup (starMod_w31 H K) :=
    (CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 n hG2).2
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1).2
      ⟨P31A.commutator_star_K_eq_top F h918, hsimple⟩
  have hZ : Subgroup.center ↥(star H K) = ⊥ :=
    CFSG.Quasithin.center_eq_bot_of_isG2_quot hq
      (P31A.odd_card_center_star_K F h918) hG2
  have hK : CFSG.Quasithin.IsG2 2 n ↥(star H K) :=
    CFSG.Quasithin.isG2_of_center_eq_bot hZ hG2
  have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(star H K)) :=
    CFSG.Quasithin.isCyclic_outer_of_isG2 hK
  have hSB : ∀ S : Subgroup ↥(star H K), CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
      CFSG.ASVolI.burnsideAut_SolvBorel ↥(star H K) S :=
    CFSG.ASVolI.burnsideAut_solvBorel_G2 _ n hn hK
  have hK3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(star H K)) :=
    CFSG.Quasithin.R3c3.two_le_pRank_three_isG2 hK
  exact P31A.false_of_propA_setting h1222 F hH hHK h918 hK₀ hcyc hZ hSB hK3

end CFSG.Quasithin.H13
