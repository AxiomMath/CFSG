module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfX0
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfLift
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec15.Liebeck143AtDelta
import CFSG.Walter.Bender1970.S3.ABar
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem deltaZero_normalizer_le (h142 : Item142R) (h : Ctx A c L d) :
    deltaZero A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G)
  let V : Subgroup G := pPrimeCoreOf 3 H
  let O' : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  change deltaZero A (lB A) H ≤ L ⊔ V
  obtain ⟨Q, hQ, -⟩ := exists_le_mem_maxInvariantPiSubgroups
    (bot_mem_invariantPiSubgroups H A (piCompl 3))
  obtain ⟨-, hcases⟩ := h142 G A c L h.conf.sec15R Q hQ
  have hK : delta A (lB A) H = L ⊔ V ⊔ O' := by
    rcases hcases with ⟨hprod, -, -, -⟩ | ⟨hK, -⟩
    · exfalso
      obtain ⟨φ⟩ := hprod
      obtain ⟨hS, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod h.conf.sec15R.toSec13Data hS hZ φ
      exact (Sec16.isEmpty_mulEquiv_l34_of_j2 h.conf.j2).false ψ
    · exact hK
  refine Liebeck156.deltaZero_le_of_delta_le_sup (LB := lB A) (Y := H) (O' := O')
    (N₀ := L ⊔ V) ?_ ?_ ?_ ?_
  · have hAH : A ≤ H :=
      h.conf.sec15R.toSec13Data.A_le_centralizer.trans
        (CFSG.Walter.centralizer_singleton_le_normalizer_zpowers c)
    have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
      hAH.trans (le_normalizer_pPrimeCoreOf 3 H)
    exact (le_inf h.conf.sec15R.toSec13Data.le_normalizer hAV).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L V)
  · have hO'A : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
    have hO'c : O' ≤ Subgroup.centralizer ({c} : Set G) :=
      hO'A.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.conf.sec15R.mem_A))
    have hO'L : O' ≤ Subgroup.normalizer (L : Set G) :=
      hO'c.trans (centralizer_le_normalizer_of_j2 h.conf.sec15R.toSec14Std h.conf.j2)
    have hO'H : O' ≤ H :=
      hO'c.trans (CFSG.Walter.centralizer_singleton_le_normalizer_zpowers c)
    have hO'V : O' ≤ Subgroup.normalizer (V : Set G) :=
      hO'H.trans (le_normalizer_pPrimeCoreOf 3 H)
    exact (le_inf hO'L hO'V).trans (Subgroup.inf_normalizer_le_normalizer_sup L V)
  · exact pPrimeCoreOf_le 3 _
  · rw [hK]
    exact le_of_eq (sup_comm (L ⊔ V) O')

theorem sup_inf_centralizer_le
    (h : Ctx A c L d) :
    (L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ⊓
        Subgroup.centralizer ({d} : Set G) ≤
      x₀ L d ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G)
  let V : Subgroup G := pPrimeCoreOf 3 H
  change (L ⊔ V) ⊓ Subgroup.centralizer ({d} : Set G) ≤ x₀ L d ⊔ V
  have hLH : L ≤ H :=
    h.conf.sec15R.toSec13Data.le_centralizer.trans
      (CFSG.Walter.centralizer_singleton_le_normalizer_zpowers c)
  have hLV : L ≤ Subgroup.normalizer (V : Set G) :=
    hLH.trans (le_normalizer_pPrimeCoreOf 3 H)
  have hdL : d ∈ L := h.mem_L
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := hLV hdL
  have hd3 : orderOf d = 3 :=
    orderOf_eq_prime (h.conf.sec15R.isElemAbelian.2 d h.mem_d) h.ne_d
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV3 : ¬ 3 ∣ Nat.card ↥V :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 H)
  have hK3 : ¬ 3 ∣ Nat.card ↥(L ⊓ V) := fun h3 =>
    hV3 (h3.trans (Subgroup.card_dvd_of_le (inf_le_right : L ⊓ V ≤ V)))
  intro y hy
  obtain ⟨hyLV, hyd⟩ := Subgroup.mem_inf.mp hy
  have hyLV' : y ∈ ((L ⊔ V : Subgroup G) : Set G) := hyLV
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L V hLV] at hyLV'
  obtain ⟨l, hl, v, hv, rfl⟩ := hyLV'
  have hyd' : l * v * d = d * (l * v) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyd
  have h1 : l * (v * d * v⁻¹) = d * l := by
    calc l * (v * d * v⁻¹) = (l * v * d) * v⁻¹ := by group
      _ = (d * (l * v)) * v⁻¹ := by rw [hyd']
      _ = d * l := by group
  have h2 : l⁻¹ * d * l = v * d * v⁻¹ := by
    have h := congrArg (fun x => l⁻¹ * x) h1
    simpa [mul_assoc] using h.symm
  have hcomm : l⁻¹ * d * l * d⁻¹ ∈ L ⊓ V := by
    refine ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hl) hdL) hl) (L.inv_mem hdL)
    · rw [h2]
      simpa [mul_assoc] using
        V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp hdN (v⁻¹)).mp (V.inv_mem hv))
  have hlift : l⁻¹ ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ (L ⊓ V) :=
    mem_inf_centralizer_sup (inf_le_left : L ⊓ V ≤ L)
      ((le_inf Subgroup.le_normalizer hLV).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hdL, hLV hdL⟩))
      hd3 hK3 (L.inv_mem hl) (by simpa using hcomm)
  have hsup : (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ (L ⊓ V) ≤ x₀ L d ⊔ V :=
    sup_le (h.inf_centralizer_le_x₀.trans (le_sup_left : x₀ L d ≤ x₀ L d ⊔ V))
      ((inf_le_right : L ⊓ V ≤ V).trans (le_sup_right : V ≤ x₀ L d ⊔ V))
  have hlmem : l ∈ x₀ L d ⊔ V := by
    simpa using (x₀ L d ⊔ V).inv_mem (hsup hlift)
  exact (x₀ L d ⊔ V).mul_mem hlmem ((le_sup_right : V ≤ x₀ L d ⊔ V) hv)

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
