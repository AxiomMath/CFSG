module

public import CFSG.Assembly.Subnormal
public import CFSG.Blueprint.Chevalley
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsSpComp
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepF4
import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LargeExtraspecial.S5Comp
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S2Basic
import CFSG.LargeExtraspecial.S5Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieExc
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapF4
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split

public section

namespace CFSG.StandardType.TBCF4

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open

section


theorem ggTBC_F4Two_comp_split {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {d : adjointGroup .F4 K} (hd : orderOf d = 3) {J : Subgroup (adjointGroup .F4 K)}
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({d} : Set (adjointGroup .F4 K)))) :
    J ⊓ (Subgroup.centralizer ({d} : Set (adjointGroup .F4 K)) ⊓
        Subgroup.centralizer (J : Set (adjointGroup .F4 K))) = ⊥ ∧
      ∀ g ∈ Subgroup.centralizer ({d} : Set (adjointGroup .F4 K)), ∃ a ∈ J,
        ∃ b ∈ Subgroup.centralizer ({d} : Set (adjointGroup .F4 K)) ⊓
          Subgroup.centralizer (J : Set (adjointGroup .F4 K)), g = a * b := by
  classical
  let G := ↥(adjointGroup .F4 K)
  let N : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hJopen : CFSG.Open.IsComponentOf J N := CFSG.Assembly.isComponentOf_iff_open.mp hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G := CFSG.LieType.Chevalley.generated_group_finite .F4 K
  obtain ⟨F, hFfield, hFfinite, hFcard, ⟨e⟩⟩ :=
    CFSG.StandardType.A6Red.ggA6F4_comp_iso_sp (K := K) hK d hd J hJopen
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hFcard]; norm_num)
  have hcenterJ : Subgroup.center ↥J = ⊥ := by
    have hcenterSp : Subgroup.center ↥(CFSG.Open.StatedSp 3 F) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := 3) (by norm_num)
    rw [eq_bot_iff]
    intro x hx
    have hmem : e x ∈ Subgroup.center ↥(CFSG.Open.StatedSp 3 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
    rw [hcenterSp, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hmem, map_one])
  have hZJ : J ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      refine Subtype.ext ?_
      exact (Subgroup.mem_centralizer_iff.mp hx.2) y y.2
    rw [hcenterJ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    simpa using Subtype.ext_iff.mp hxZ
  have hcardJ : Nat.card ↥J = 1451520 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hFcard]
    decide
  have hnorm : ∀ c ∈ N, J.map (MulAut.conj c).toMonoidHom = J := by
    intro c hc
    by_contra hne
    let J' : Subgroup G := J.map (MulAut.conj c).toMonoidHom
    have hJ' : CFSG.Open.IsComponentOf J' N :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hJopen hc
    have hne' : J ≠ J' := fun h => hne h.symm
    have hcomm : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a :=
      fun a ha b hb =>
        CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hJopen hJ' hne' ha hb
    have hle : J' ≤ Subgroup.centralizer (J : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    have hdisj : J ⊓ J' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxZ : x ∈ J ⊓ Subgroup.centralizer (J : Set G) :=
        Subgroup.mem_inf.2 ⟨hx.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact hcomm y hy x hx.2⟩
      rw [hZJ, Subgroup.mem_bot] at hxZ
      rwa [Subgroup.mem_bot]
    have hcardJ' : Nat.card ↥J' = 1451520 := by
      change Nat.card ↥(J.map (MulAut.conj c).toMonoidHom) = 1451520
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcardJ]
    have hcardsup : Nat.card ↥(J ⊔ J') = 1451520 * 1451520 := by
      rw [CFSG.SeitzReduction.F4Pilot.card_sup_eq_mul_of_le_centralizer hle hdisj, hcardJ,
        hcardJ']
    have hdvd : Nat.card ↥(J ⊔ J') ∣ Nat.card G := by
      have h := Subgroup.card_dvd_of_le (show J ⊔ J' ≤ (⊤ : Subgroup G) from le_top)
      simpa only [Subgroup.card_top] using h
    have hcardG : Nat.card G ∣
        2 ^ 24 * ((2 ^ 12 - 1) * (2 ^ 8 - 1) * (2 ^ 6 - 1) * (2 ^ 2 - 1)) := by
      have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.card_adjointGroup_F4_dvd K
      rw [hK] at h
      simpa only [G, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_assoc] using h
    have h3dvd : 3 ^ 8 ∣ Nat.card G := by
      have h1 : 3 ^ 8 ∣ Nat.card ↥(J ⊔ J') := by
        rw [hcardsup]
        norm_num
      exact h1.trans hdvd
    have hbig : 3 ^ 8 ∣
        2 ^ 24 * ((2 ^ 12 - 1) * (2 ^ 8 - 1) * (2 ^ 6 - 1) * (2 ^ 2 - 1)) :=
      h3dvd.trans hcardG
    exact absurd hbig (by norm_num)
  refine ⟨?_, ?_⟩
  ·
    rw [← inf_assoc, inf_eq_left.2 hJopen.1]
    exact hZJ
  ·
    intro g hg
    have hJg : J.map (MulAut.conj g).toMonoidHom = J := hnorm g hg
    let α : MulAut ↥J :=
      { toFun := fun x =>
          ⟨g * (x : G) * g⁻¹, by
            have hx : g * (x : G) * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := by
              refine Subgroup.mem_map.2 ⟨x, x.2, ?_⟩
              change (MulAut.conj g) (x : G) = g * (x : G) * g⁻¹
              rfl
            rwa [hJg] at hx⟩
        invFun := fun x =>
          ⟨g⁻¹ * (x : G) * g, by
            have hx : (x : G) ∈ J.map (MulAut.conj g).toMonoidHom := by
              rw [hJg]
              exact x.2
            obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
            change (MulAut.conj g) (y : G) = (x : G) at hyx
            rw [MulAut.conj_apply] at hyx
            rw [show g⁻¹ * (x : G) * g = y by rw [← hyx]; group]
            exact hy⟩
        left_inv := fun x => Subtype.ext (by
          change g⁻¹ * (g * (x : G) * g⁻¹) * g = (x : G)
          group)
        right_inv := fun x => Subtype.ext (by
          change g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G)
          group)
        map_mul' := fun x y => Subtype.ext (by
          change g * ((x : G) * (y : G)) * g⁻¹ =
            (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
          group) }
    have hαapply : ∀ x : ↥J, (α x : G) = g * x * g⁻¹ := fun x => rfl
    let ψ : F ≃+* ZMod 2 :=
      (ZMod.ringEquivOfPrime F Nat.prime_two
        (by simpa [Nat.card_eq_fintype_card] using hFcard)).symm
    let c : ↥(CFSG.Open.StatedSp 3 F) ≃* ↥(CFSG.Open.StatedSp 3 (ZMod 2)) :=
      CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr ψ 3
    obtain ⟨t, ht⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_statedSp
        (MulAut.congr c (MulAut.congr e α))
    let a : ↥J := e.symm (c.symm t)
    have hα : α = MulAut.conj a := by
      have hcongr_e : MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
        refine MulEquiv.ext fun x => ?_
        change e (a * e.symm x * a⁻¹) = e a * x * (e a)⁻¹
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply e x]
      refine (MulAut.congr e).injective ?_
      rw [hcongr_e]
      have hea : e a = c.symm t := by simp [a]
      rw [hea]
      have hcongr_c : MulAut.congr c (MulAut.conj (c.symm t)) =
          MulAut.conj (c (c.symm t)) := by
        refine MulEquiv.ext fun x => ?_
        change c (c.symm t * c.symm x * (c.symm t)⁻¹) =
          c (c.symm t) * x * (c (c.symm t))⁻¹
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply c x]
      refine (MulAut.congr c).injective ?_
      rw [hcongr_c]
      simp only [MulEquiv.apply_symm_apply]
      exact ht
    have hconj : ∀ x ∈ J, g * x * g⁻¹ = (a : G) * x * (a : G)⁻¹ := by
      intro x hx
      let x' : ↥J := ⟨x, hx⟩
      have h1 : (α x' : G) = g * x * g⁻¹ := by simpa using hαapply x'
      have h2 : (α x' : G) = (a : G) * x * (a : G)⁻¹ := by
        rw [hα, MulAut.conj_apply]
        rfl
      rw [← h1]
      exact h2
    have haJ : (a : G) ∈ J := a.2
    have haN : (a : G) ∈ N := hJopen.1 haJ
    have hbN : (a : G)⁻¹ * g ∈ N := N.mul_mem (N.inv_mem haN) hg
    have hbC : (a : G)⁻¹ * g ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * ((a : G)⁻¹ * g) =
          (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * g := by group
        _ = (a : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hconj x hx]
        _ = ((a : G)⁻¹ * g) * x := by group
    exact ⟨(a : G), haJ, (a : G)⁻¹ * g, Subgroup.mem_inf.2 ⟨hbN, hbC⟩, by group⟩

end

end CFSG.StandardType.TBCF4

end
