module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open
open scoped commutatorElement

theorem f3_sylow_TL {G : Type} [Group G] [Finite G] {T TL : Subgroup G} {e : G}
    (hT : CFSG.Open.quasithinIsSylowTwo T) (hTL : TL ≤ T)
    (hTL' : T ⊓ Subgroup.centralizer ({e} : Set G) = TL)
    (hTidx : Nat.card T ≤ 2 * Nat.card TL) (heT : e ∈ T) (he1 : e ≠ 1) (he2 : e ^ 2 = 1)
    (hnot : ¬ ∃ g : G, g⁻¹ * e * g ∈ CFSG.Open.quasithinOmegaOneCenter T) :
    CFSG.QuasithinUnique.IsSylowTwoOf TL (Subgroup.centralizer ({e} : Set G)) := by
  have hTLG : TL ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [← hTL']
    exact inf_le_right
  have hTL2 : IsPGroup 2 ↥TL := IsPGroup.to_le hT.1 hTL
  have he_cent : e ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
  have hzpow : Subgroup.zpowers e ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.zpowers_le.2 he_cent
  have hcentz : Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hx' : e * x = x * e := Subgroup.mem_centralizer_iff.1 hx e (Set.mem_singleton e)
    exact Commute.zpow_left hx' k
  have hnorm : Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) :=
    hcentz.trans (Subgroup.centralizer_le_normalizer _)
  have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
  have hPG : IsPGroup 2 ↥(Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, hord, pow_one])
  have hzle : Subgroup.zpowers e ≤ pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hzpow hnorm hPG
  have he_core : e ∈ pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) :=
    hzle (Subgroup.mem_zpowers e)
  obtain ⟨S, hS, hTLS⟩ := CFSG.Quasithin.A4.exists_isSylowTwoOf_ge hTLG hTL2
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hT le_top
  obtain ⟨P, hP, hSP⟩ := CFSG.Quasithin.A4.exists_isSylowTwoOf_ge (le_top : S ≤ ⊤) hS.2.1
  have hcardP : Nat.card P = Nat.card T := hP.card_eq.trans hTsyl.card_eq.symm
  have hSP_card : Nat.card S ≤ Nat.card P := Subgroup.card_le_of_le hSP
  have hle : Nat.card S ≤ Nat.card T := by omega
  have hne : Nat.card S ≠ Nat.card T := by
    intro heq
    have hSP' : S = P := Subgroup.eq_of_le_of_card_ge hSP (by omega)
    have hSsyl : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
      rw [hSP']
      exact hP
    obtain ⟨h, -, hconj⟩ := CFSG.Quasithin.A4.exists_conj_of_isSylowTwoOf hSsyl hTsyl
    have hcoreS : pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) ≤ S :=
      CFSG.Quasithin.pCoreOf_two_le_of_sylowIn hS.1 hS.2.1 hS.2.2
    have he_S : e ∈ S := hcoreS he_core
    have hzT : h * e * h⁻¹ ∈ T := by
      rw [hconj]
      have hc : h⁻¹ * (h * e * h⁻¹) * h = e := by group
      rw [hc]
      exact he_S
    have hcomm : ∀ t ∈ T, (h * e * h⁻¹) * t = t * (h * e * h⁻¹) := by
      intro t ht
      have hw : h⁻¹ * t * h ∈ Subgroup.centralizer ({e} : Set G) :=
        hS.1 ((hconj t).1 ht)
      have h1 : e * (h⁻¹ * t * h) = (h⁻¹ * t * h) * e :=
        Subgroup.mem_centralizer_iff.1 hw e (Set.mem_singleton e)
      calc (h * e * h⁻¹) * t = h * (e * (h⁻¹ * t * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * t * h) * e) * h⁻¹ := by rw [h1]
        _ = t * (h * e * h⁻¹) := by group
    have hzC : h * e * h⁻¹ ∈ Subgroup.centralizer (T : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun t ht => (hcomm t ht).symm
    have hz2 : (h * e * h⁻¹) ^ 2 = 1 := by
      have hc : (h * e * h⁻¹) ^ 2 = h * e ^ 2 * h⁻¹ := by
        simp only [sq]
        group
      rw [hc, he2]
      simp
    have hmemS : h * e * h⁻¹ ∈
        ({z : G | z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ^ 2 = 1} : Set G) :=
      And.intro (Subgroup.mem_inf.2 ⟨hzT, hzC⟩) hz2
    have hmem : h * e * h⁻¹ ∈ CFSG.Open.quasithinOmegaOneCenter T :=
      Subgroup.subset_closure hmemS
    apply hnot
    refine ⟨h⁻¹, ?_⟩
    rw [inv_inv]
    exact hmem
  have hSlt : Nat.card S < Nat.card T := lt_of_le_of_ne hle hne
  have hlt : Nat.card S < 2 * Nat.card TL := lt_of_lt_of_le hSlt hTidx
  have hpos : 0 < Nat.card S := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hTLS
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> omega
    · exfalso
      have hmul : Nat.card TL * 2 ≤ Nat.card TL * k := Nat.mul_le_mul le_rfl hk2
      omega
  rw [hk1, mul_one] at hk
  have hST : TL = S := Subgroup.eq_of_le_of_card_ge hTLS hk.le
  rw [hST]
  exact hS

end CFSG.Quasithin.H13.NF314pt
