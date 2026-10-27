module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5k
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieDelta5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2262
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate4139
public import Certificates.Certificate8033
public import Certificates.Certificate18000
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.QuasithinUnique.A5.G3
open scoped commutatorElement

theorem not_isSL25_of_parabolicFacts {G : Type} [Group G] {P Q : Subgroup G}
    (hF : ParabolicFacts P Q) : ¬ IsSL25Group ↥(perfectCore P) := by
  intro hD
  obtain ⟨α, hαs, hαk⟩ := hD.alt
  rcases hF.levi with hPQ | ⟨hgen, -⟩
  ·
    have h2 : IsPGroup 2 ↥(perfectCore P) := hF.pGroup.to_le hPQ
    have hcore : CFSG.pCore 2 ↥(perfectCore P) = ⊤ := by
      rw [eq_top_iff]
      refine Vol2Native.L239.le_pCore_of_normal (N := (⊤ : Subgroup ↥(perfectCore P)))
        fun x => ?_
      obtain ⟨k, hk⟩ := h2 (x : ↥(perfectCore P))
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨y, hy⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨x, rfl⟩ := hαs y
    apply hy
    exact MonoidHom.mem_ker.1 (hαk ▸ hcore ▸ Subgroup.mem_top x)
  ·
    have hQP : Q ≤ perfectCore P := hgen.trans (by
      refine Subgroup.commutator_le.2 fun q hq x hx => ?_
      have : ⁅q, x⁆ = (q * x * q⁻¹) * x⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact (perfectCore P).mul_mem
        ((Subgroup.mem_normalizer_iff.1
          (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P
            (Subgroup.le_normalizer (hF.le hq))) x).1 hx)
        ((perfectCore P).inv_mem hx))
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    have hPinf : perfectCore P ≤ Subgroup.normalizer (Q : Set G) :=
      (perfectCore_le P).trans hF.normalizes
    have hnorm : (Q.subgroupOf (perfectCore P)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2 hPinf
    have hQ2 : IsPGroup 2 (Q.subgroupOf (perfectCore P)) :=
      hF.pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
    have hle : Q.subgroupOf (perfectCore P) ≤ CFSG.pCore 2 ↥(perfectCore P) :=
      Vol2Native.L239.le_pCore_of_normal hQ2
    have hcomm := hD.comm ⟨x, hQP hx⟩ (hle (Subgroup.mem_subgroupOf.2 hx)) ⟨y, hQP hy⟩
      (hle (Subgroup.mem_subgroupOf.2 hy))
    apply hxy
    have := congrArg (fun w : ↥(perfectCore P) => (w : G)) hcomm
    simpa using this

theorem not_isSL25_perfectCore_g2
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : IsG2 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsSL25Group ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isSL25_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  refine not_isSL25_perfectCore_of_equiv e ?_
  refine not_isSL25_perfectCore_parabolic hU₀ G2_residualOvergroupsAt (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  have hPC : parabolicSubgroup Tag.G2 K {g2Index j} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup _ _ _
  refine not_isSL25_perfectCore_subgroupOf_of hPC ?_
  rcases G2.fin_two_cases (g2Index j) with h | h
  · rw [h]
    exact not_isSL25_of_parabolicFacts (G2.parabolicFacts_zero hK hf)
  · rw [h]
    exact not_isSL25_of_parabolicFacts (G2.parabolicFacts_one hK hf)

theorem not_isSL25_perfectCore_d4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : Is3D4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsSL25Group ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isSL25_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hL
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
      id_eq, RingHom.one_def, RingHom.id_apply]
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    let _ := Fintype.ofFinite K
    have hq : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [hq]
    exact FiniteField.pow_card c
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK3]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine not_isSL25_perfectCore_of_equiv e ?_
  refine not_isSL25_perfectCore_parabolic hU₀ (triality_residualOvergroupsAt σ) (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  refine not_isSL25_perfectCore_subgroupOf_of (graphFixedParabolic_le _ _ _ _) ?_
  have hcases : ∀ i : Fin TwistTag.D4.foldedTag.rank, i = D4.fa0 ∨ i = D4.fa1 := by decide
  rcases hcases (d4Index j) with h | h
  · rw [h]
    exact not_isSL25_of_parabolicFacts (D4.parabolicFacts_a0 σ hσ3 hK4)
  · rw [h]
    exact not_isSL25_of_parabolicFacts (D4.parabolicFacts_a1 σ hσ3)

theorem not_isSL25_perfectCore_f4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hodd : Odd f) (hf : 3 ≤ f) (hL : Is2F4 f ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsSL25Group ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isSL25_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hL
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a K ha hK
  refine not_isSL25_perfectCore_of_equiv e ?_
  refine not_isSL25_perfectCore_parabolic hU₀ (large_Ree_residualOvergroupsAt hK) (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  have hPC : F4.reeParabolic K a {f4Index j} ≤ F4.reeGamma K a := reeParabolic_le F4 K a _
  refine not_isSL25_perfectCore_subgroupOf_of hPC ?_
  rw [reeParabolic_singleton (t := F4) (K := K) (a := a)]
  rcases hcases (f4Index j) with h | h
  · rw [h]
    exact not_isSL25_of_parabolicFacts hF0
  · rw [h]
    exact not_isSL25_of_parabolicFacts hF1

theorem not_isSL25_perfectCore_tits
    {G : Type} [Group G] [Finite G] (L P : Subgroup G)
    (hT : IsTits ↥L) (hP : IsMaxParabolic2 L P) : ¬ IsSL25Group ↥(perfectCore P) := by
  obtain ⟨⟨hPL, S, hS, hN⟩, hPne, -⟩ := hP
  have hU : IsSylowTwoOf (S.subgroupOf L) (⊤ : Subgroup ↥L) := isSylowTwoOf_top_subgroupOf hS
  obtain ⟨H, N, -, hUH, hUN, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice ↥L hT _ hU
  have hSP : S ≤ P := fun x hx => hN ⟨hS.1 hx, Subgroup.le_normalizer hx⟩
  have hUP : S.subgroupOf L ≤ P.subgroupOf L := fun x hx => hSP hx
  have hsolv : Group.IsSolvable ↥(P.subgroupOf L) := by
    rcases hlat _ hUP with h | h | h | h
    · rw [h]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥(S.subgroupOf L) := hU.2.1
      have : Group.IsNilpotent ↥(S.subgroupOf L) := hp.isNilpotent
      infer_instance
    · rw [h]; exact hHs
    · rw [h]; exact hNs
    · exfalso
      apply hPne
      refine le_antisymm hPL fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
  have hPs : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPL).symm.injective
  rw [(isSolvable_iff_perfectCore_eq_bot P).mp hPs]
  exact not_isSL25_bot

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
