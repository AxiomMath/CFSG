module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentIndexFour
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiagA5
import CFSG.Quasithin.Recognition.J2RecTwoBCent
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S1414Defs
import CFSG.Quasithin.EmptyFaithful.S1417Sylow
import CFSG.Quasithin.Recognition.J2RecWords
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem map_characteristic_le_normalizer_X {K0 : Subgroup D.X} (hK0 : K0.Normal)
    {L0 : Subgroup K0} (hL0 : L0.Characteristic) :
    D.X ≤ normalizer (L0.map (D.X.subtype.comp K0.subtype) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  haveI : K0.Normal := hK0
  have hmap : L0.map (MulAut.conjNormal (⟨x, hx⟩ : D.X)).toMonoidHom = L0 :=
    characteristic_iff_map_eq.mp hL0 (MulAut.conjNormal (⟨x, hx⟩ : D.X))
  have h1 : L0.map ((D.X.subtype.comp K0.subtype).comp
        (MulAut.conjNormal (⟨x, hx⟩ : D.X)).toMonoidHom) =
      L0.map (D.X.subtype.comp K0.subtype) := by
    rw [← Subgroup.map_map, hmap]
  have hcomp : (D.X.subtype.comp K0.subtype).comp
        (MulAut.conjNormal (⟨x, hx⟩ : D.X)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (D.X.subtype.comp K0.subtype) := by
    ext y
    show D.X.subtype (K0.subtype (MulAut.conjNormal (⟨x, hx⟩ : D.X) y)) =
      x * D.X.subtype (K0.subtype y) * x⁻¹
    have hz : K0.subtype (MulAut.conjNormal (⟨x, hx⟩ : D.X) y) =
        (⟨x, hx⟩ : D.X) * (y : D.X) * (⟨x, hx⟩ : D.X)⁻¹ :=
      MulAut.conjNormal_apply (⟨x, hx⟩ : D.X) y
    rw [hz]
    simp [map_mul, map_inv]
  rw [hcomp, ← Subgroup.map_map] at h1
  exact h1

theorem characteristic_kernel_eq_diagonal {K0 : Subgroup D.X} (hK0 : K0.Normal)
    (hidx : K0.index = 2) (hK0T : K0.map D.X.subtype ⊓ D.T = D.M) {L0 : Subgroup K0}
    (hL0 : L0.Characteristic) (hL0idx : L0.index = 4)
    (hL0T : L0.map (D.X.subtype.comp K0.subtype) ⊓ D.T = D.J)
    (hAL : D.A ≤ L0.map (D.X.subtype.comp K0.subtype)) :
    L0.map (D.X.subtype.comp K0.subtype) = D.A := by
  let L : Subgroup G := L0.map (D.X.subtype.comp K0.subtype)
  have hLX : L ≤ D.X := by
    rintro _ ⟨y, -, rfl⟩
    exact (K0.subtype y).2
  have hXnorm : D.X ≤ normalizer (L : Set G) := D.map_characteristic_le_normalizer_X hK0 hL0
  have hLnormX : (L.subgroupOf D.X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXnorm
  have hJL : D.J ≤ L := by rw [← hL0T]; exact inf_le_left
  have hvL : D.v ∈ L := hJL (subset_closure (by simp))
  have hwL : D.w ∈ L := hJL (subset_closure (by simp))
  have hJodd : ¬ 2 ∣ (D.J.subgroupOf L).index := by
    have heq : (D.J.subgroupOf L).index = D.T.relIndex L := by
      show (D.J.subgroupOf L).index = (D.T.subgroupOf L).index
      rw [← hL0T, Subgroup.inf_subgroupOf_left]
    rw [heq]
    have hburn : (D.T.subgroupOf D.X).relIndex (L.subgroupOf D.X) ∣
        (D.T.subgroupOf D.X).index := by
      haveI : (L.subgroupOf D.X).Normal := hLnormX
      have h1 := Subgroup.relIndex_mul_relIndex
        ((D.T.subgroupOf D.X) ⊓ (L.subgroupOf D.X)) (D.T.subgroupOf D.X)
        ((D.T.subgroupOf D.X) ⊔ (L.subgroupOf D.X)) inf_le_left le_sup_left
      have h2 := Subgroup.relIndex_mul_relIndex
        ((D.T.subgroupOf D.X) ⊓ (L.subgroupOf D.X)) (L.subgroupOf D.X)
        ((D.T.subgroupOf D.X) ⊔ (L.subgroupOf D.X)) inf_le_right le_sup_right
      rw [Subgroup.relIndex_sup_right,
        ← Subgroup.inf_relIndex_left (D.T.subgroupOf D.X) (L.subgroupOf D.X)] at h2
      have hne : ((D.T.subgroupOf D.X) ⊓ (L.subgroupOf D.X)).relIndex (D.T.subgroupOf D.X) ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have h3 : (D.T.subgroupOf D.X).relIndex ((D.T.subgroupOf D.X) ⊔ (L.subgroupOf D.X)) =
          ((D.T.subgroupOf D.X) ⊓ (L.subgroupOf D.X)).relIndex (L.subgroupOf D.X) := by
        have := h1.trans h2.symm
        rw [mul_comm
          (((D.T.subgroupOf D.X) ⊓ (L.subgroupOf D.X)).relIndex (L.subgroupOf D.X))] at this
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this
      rw [← Subgroup.inf_relIndex_right, ← h3]
      exact ⟨_, (Subgroup.relIndex_mul_index le_sup_left).symm⟩
    have hdiv : D.T.relIndex L ∣ D.T.relIndex D.X := by
      rw [← Subgroup.relIndex_subgroupOf (H := D.T) hLX]
      exact hburn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hSylow⟩ :=
      D.second_centralizer_sylow_presentation
    obtain ⟨P, hP⟩ := hSylow
    have hPeq : (P : Subgroup D.X) = D.T.subgroupOf D.X := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        rw [← hP]
        exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rw [← hP] at hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
        rwa [Subtype.coe_injective hzy] at hz
    have hPodd : ¬ 2 ∣ D.T.relIndex D.X := by
      have hPidx : P.index = D.T.relIndex D.X := by
        rw [show P.index = (P : Subgroup D.X).index from rfl, hPeq]
        rfl
      have hnd := P.not_dvd_index
      rwa [hPidx] at hnd
    exact fun h => hPodd (dvd_trans h hdiv)
  have hJp : IsPGroup 2 D.J := IsPGroup.of_card (n := 2) (by rw [D.card_J]; norm_num)
  have hJLp : IsPGroup 2 (D.J.subgroupOf L) := hJp.comap_subtype
  let hSylJ : Sylow 2 L := hJLp.toSylow hJodd
  have hA60 : Nat.card D.A = 60 := by
    obtain ⟨eA⟩ := D.toSwapData.nonempty_A_mulEquiv_alt5
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num
  have h5 : 5 ∣ Nat.card L :=
    dvd_trans (by rw [hA60]; norm_num) (Subgroup.card_dvd_of_le hAL)
  obtain ⟨e⟩ := CFSG.Quasithin.nonempty_mulEquiv_alt5_of_centralizer
    (Y := L) (z := ⟨D.v, hvL⟩) (s := ⟨D.w, hwL⟩)
    (Subtype.ext (by simp [D.v_mul_v]))
    (by
      intro hh
      have h1 : D.v = 1 := congrArg Subtype.val hh
      have h2 := D.orderOf_v
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num))
    (Subtype.ext (by simp [D.w_mul_w]))
    (by
      intro hh
      have h1 : D.w = 1 := congrArg Subtype.val hh
      have h2 := D.orderOf_w
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num))
    (by intro hh; exact D.w_ne_v (congrArg Subtype.val hh))
    (Subtype.ext (by simp [D.commute_v_w.eq]))
    (by
      intro g hg
      have hgv : (g : G) * D.v = D.v * (g : G) := by simpa using congrArg Subtype.val hg
      have hgT : (g : G) ∈ D.T :=
        mem_inf.mpr ⟨show (g : G) ∈ centralizer {D.u} from hLX g.2,
          mem_centralizer_singleton_iff.mpr hgv⟩
      have hgJ : (g : G) ∈ D.J := by rw [← hL0T]; exact mem_inf.mpr ⟨g.2, hgT⟩
      rcases mem_closure_pair D.orderOf_v D.orderOf_w D.commute_v_w hgJ with h | h | h | h
      · exact Or.inl (Subtype.ext (by simpa using h))
      · exact Or.inr (Or.inl (Subtype.ext (by simpa using h)))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa using h))))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simpa using h)))))
    (by
      intro u' hu'2 hu'1
      have hgen : IsPGroup 2 (Subgroup.zpowers u') :=
        IsPGroup.of_card_dvd_pow (n := 1) (by
          rw [Nat.card_zpowers]
          have hord : orderOf u' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu'2) hu'1
          rw [hord]; norm_num)
      obtain ⟨Q, hQle⟩ := hgen.exists_le_sylow
      haveI : Finite (Sylow 2 L) := Sylow.finite_of_finiteIndex Q
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q hSylJ
      have hmem : (g * u' * g⁻¹ : L) ∈ D.J.subgroupOf L := by
        have h1 : (g * u' * g⁻¹ : L) ∈ (hSylJ : Subgroup L) := by
          rw [← hg]
          change (MulAut.conj g) u' ∈ (MulAut.conj g • (Q : Subgroup L) : Subgroup L)
          exact Subgroup.smul_mem_pointwise_smul u' (MulAut.conj g) Q
            (hQle (Subgroup.mem_zpowers u'))
        rwa [show (hSylJ : Subgroup L) = D.J.subgroupOf L from
          hJLp.toSylow_coe hJodd] at h1
      have hJmem : (g : G) * (u' : G) * (g : G)⁻¹ ∈ D.J :=
        Subgroup.mem_subgroupOf.mp hmem
      rcases mem_closure_pair D.orderOf_v D.orderOf_w D.commute_v_w hJmem with h | h | h | h
      · exfalso
        apply hu'1
        apply Subtype.ext
        calc (u' : G) = (g : G)⁻¹ * ((g : G) * (u' : G) * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h]; group
      · exact ⟨g, Subtype.ext h⟩
      · obtain ⟨a, haA, ha⟩ := D.toSwapData.exists_mem_A_conj_v_eq_w
        refine ⟨⟨a * g, mul_mem (hAL haA) g.2⟩, ?_⟩
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc a * (g : G) * (u' : G) * (a * (g : G))⁻¹
            = a * ((g : G) * (u' : G) * (g : G)⁻¹) * a⁻¹ := by group
          _ = a * D.w * a⁻¹ := by rw [h]
          _ = D.v := by rw [← ha]; group
      · obtain ⟨a, haA, ha⟩ := D.toSwapData.exists_mem_A_conj_v_eq_v_mul_w
        refine ⟨⟨a * g, mul_mem (hAL haA) g.2⟩, ?_⟩
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc a * (g : G) * (u' : G) * (a * (g : G))⁻¹
            = a * ((g : G) * (u' : G) * (g : G)⁻¹) * a⁻¹ := by group
          _ = a * (D.v * D.w) * a⁻¹ := by rw [h]
          _ = D.v := by rw [← ha]; group)
    h5
  have hL60 : Nat.card L = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hAL
    (le_of_eq (by rw [show L0.map (D.X.subtype.comp K0.subtype) = L from rfl, hL60, hA60]))).symm

end CFSG.OddTranspositions.PartThree.Wong.SplitData
