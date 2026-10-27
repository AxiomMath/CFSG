module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKZ
public import CFSG.Quasithin.Background.C48PfA
public import CFSG.Quasithin.Background.C22HoldsA37

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G}

theorem V_le_omegaRp (c : Conf4212 G T M L I H K) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) := by
  rw [← c.omega_eq]
  have hLN : L ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) : Set G) :=
    (le_sup_left : L ≤ L ⊔ T).trans ((le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (normalizer_le_normalizer_omegaOneCenterOf _))
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp hLN

theorem V_le_omega (c : Conf4212 G T M L I H K) (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ omegaOneCenterOf (pCoreOf 2 I) :=
  (V_le_omegaRp c).trans (omegaOneCenterOf_Rp_le hy h37 h38 h39)

theorem Rp_le_centralizer_V (c : Conf4212 G T M L I H K) :
    pCoreOf 2 (L ⊔ T) ≤
      Subgroup.centralizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
  have hVR : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_centralizer_of_le_omegaOneCenterOf (V_le_omegaRp c) le_rfl
  exact Subgroup.le_centralizer_iff.mpr hVR

theorem omega_le_pCoreOf_sup (c : Conf4212 G T M L I H K) (h37 : A37ForSQTK)
    (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hMS : IsMSPair (K ⊔ pCoreOf 2 I) (pCoreOf 2 I)) :
    omegaOneCenterOf (pCoreOf 2 I) ≤ pCoreOf 2 (K ⊔ pCoreOf 2 I) := by
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    ((pCoreOf_le 2 I).trans c.inH.1).trans hKH
  have hQR : pCoreOf 2 (K ⊔ pCoreOf 2 I) ≤ pCoreOf 2 I :=
    CFSG.Quasithin.C48Pf.pCoreOf_sup_le (asc22Three_of_a37 h37 G) c.hypC28 c.K_mem hRK
  intro z hz
  have hzR : z ∈ pCoreOf 2 I := A4.omegaOneCenterOf_le (pCoreOf 2 I) hz
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 (K ⊔ pCoreOf 2 I) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQR)
      (A4.centerOf_le_centralizer (pCoreOf 2 I) (A4.omegaOneCenterOf_le_centerOf (pCoreOf 2 I) hz))
  have hmem : z ∈ (K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (pCoreOf 2 (K ⊔ pCoreOf 2 I) : Set G) :=
    ⟨Subgroup.mem_sup_right hzR, hzC⟩
  exact hMS.1.2.1 hmem

theorem commutator_omega_le_Q (c : Conf4212 G T M L I H K) (h37 : A37ForSQTK)
    (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hMS : IsMSPair (K ⊔ pCoreOf 2 I) (pCoreOf 2 I)) :
    ⁅omegaOneCenterOf (pCoreOf 2 I), K⁆ ≤ c134Q (K ⊔ pCoreOf 2 I) K :=
  Subgroup.commutator_mono (omega_le_pCoreOf_sup c h37 hKH hMS) le_rfl

theorem V_le_Q (c : Conf4212 G T M L I H K) (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hMS : IsMSPair (K ⊔ pCoreOf 2 I) (pCoreOf 2 I)) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ c134Q (K ⊔ pCoreOf 2 I) K := by
  have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
    le_antisymm (conjClosure_le fun _ hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (c.LH_normal hk) z).mp hz)
      (le_conjClosure _ _)
  have hV : ⁅⁅reducedAggregate (L ⊔ T), L⁆, perfectCore (L ⊓ H)⁆ =
      ⁅reducedAggregate (L ⊔ T), L⁆ := by
    have h := c.hypC28.V_comm
    rwa [hcc] at h
  calc ⁅reducedAggregate (L ⊔ T), L⁆ = ⁅⁅reducedAggregate (L ⊔ T), L⁆, perfectCore (L ⊓ H)⁆ :=
        hV.symm
    _ ≤ ⁅omegaOneCenterOf (pCoreOf 2 I), K⁆ :=
        Subgroup.commutator_mono (V_le_omega c hy h37 h38 h39) c.LH_le
    _ ≤ c134Q (K ⊔ pCoreOf 2 I) K := commutator_omega_le_Q c h37 hKH hMS

theorem pCoreOf_LH_le_R (c : Conf4212 G T M L I H K) :
    pCoreOf 2 (perfectCore (L ⊓ H)) ≤ pCoreOf 2 I := by
  set LH := perfectCore (L ⊓ H) with hLH
  have hcc : conjClosure LH (H ⊓ M) = LH :=
    le_antisymm (conjClosure_le fun _ hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (c.LH_normal hk) z).mp hz) (le_conjClosure LH (H ⊓ M))
  have hsyl := c.hypC28.sylow
  rw [hcc] at hsyl
  set C := centralizerSection (H ⊓ M) LH (pCoreOf 2 LH) with hC
  have hLHM : LH ≤ H ⊓ M := le_of_mem_cComp c.LH_mem
  have hOC : pCoreOf 2 LH ≤ C := by
    intro o ho
    have hoLH : o ∈ LH := pCoreOf_le 2 LH ho
    refine ⟨hLHM hoLH, Subgroup.le_normalizer hoLH,
      normalizer_le_normalizer_pCoreOf 2 LH (Subgroup.le_normalizer hoLH), fun x hx => ?_⟩
    have h1 : x * o * x⁻¹ ∈ pCoreOf 2 LH :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 LH hx) o).mp ho
    exact (pCoreOf 2 LH).mul_mem h1 ((pCoreOf 2 LH).inv_mem ho)
  have hON : ((pCoreOf 2 LH).subgroupOf C).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro y hy
    exact hy.2.2.1
  exact le_of_normal_of_isSylowTwoOf hsyl hOC hON (pCoreOf_isPGroup 2 LH)

end CFSG.Quasithin.H13.Ch4.CentK
