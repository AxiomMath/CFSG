module

public import CFSG.Quasithin.Background.A3Structure38Facts
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftGomi
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
import CFSG.Quasithin.Vol2.Ch4Sec4L443E4Inner
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.SectionRank.SectionAssembly
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Structure312Facts
import CFSG.Quasithin.Vol2.Ch4Sec4L443E3Conj
import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
import CFSG.Quasithin.Vol2.Ch4Sec4W446
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin
open scoped Pointwise commutatorElement

namespace SecFiveRk1C

theorem commutator_mul_centralizer {G : Type*} [Group G] {X : Subgroup G}
    {a a' c c' : G} (ha : a ∈ X) (ha' : a' ∈ X) (hc : c ∈ Subgroup.centralizer (X : Set G))
    (hc' : c' ∈ Subgroup.centralizer (X : Set G)) :
    ⁅a * c, a' * c'⁆ = ⁅a, a'⁆ * ⁅c, c'⁆ := by
  set C := Subgroup.centralizer (X : Set G)
  have hC : ∀ d ∈ C, ∀ y ∈ X, d * y = y * d := fun d hd y hy =>
    ((Subgroup.mem_centralizer_iff.mp hd) y hy).symm
  have e1 : c * a' = a' * c := hC c hc a' ha'
  have e2 : (c * c' * c⁻¹) * a⁻¹ = a⁻¹ * (c * c' * c⁻¹) :=
    hC _ (C.mul_mem (C.mul_mem hc hc') (C.inv_mem hc)) _ (X.inv_mem ha)
  have e3 : (c * c' * c⁻¹ * c'⁻¹) * a'⁻¹ = a'⁻¹ * (c * c' * c⁻¹ * c'⁻¹) :=
    hC _ (C.mul_mem (C.mul_mem (C.mul_mem hc hc') (C.inv_mem hc)) (C.inv_mem hc')) _
      (X.inv_mem ha')
  calc ⁅a * c, a' * c'⁆ = a * (c * a') * c' * c⁻¹ * a⁻¹ * c'⁻¹ * a'⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * a' * ((c * c' * c⁻¹) * a⁻¹) * c'⁻¹ * a'⁻¹ := by rw [e1]; group
    _ = a * a' * a⁻¹ * ((c * c' * c⁻¹ * c'⁻¹) * a'⁻¹) := by rw [e2]; group
    _ = ⁅a, a'⁆ * ⁅c, c'⁆ := by
        rw [e3, commutatorElement_def, commutatorElement_def]; group

theorem le_commutator_sup_centralizer_of_perfect {G : Type*} [Group G]
    {X K Q : Subgroup G} (hKX : K ≤ X) (hQQ : ⁅Q, Q⁆ = Q)
    (hQK : Q ≤ K ⊔ Subgroup.centralizer (X : Set G)) :
    Q ≤ ⁅K, K⁆ ⊔ Subgroup.centralizer (X : Set G) := by
  have hKN : K ≤ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
    hKX.trans (Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer X))
  have hd : ∀ y ∈ Q, y ∈ (K : Set G) * (Subgroup.centralizer (X : Set G) : Set G) :=
    fun y hy => by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _ hKN]
      exact hQK hy
  rw [← hQQ, Subgroup.commutator_le]
  intro q hq q' hq'
  obtain ⟨a, ha, c, hc, rfl⟩ := hd q hq
  obtain ⟨a', ha', c', hc', rfl⟩ := hd q' hq'
  rw [commutator_mul_centralizer (hKX ha) (hKX ha') hc hc']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha ha'))
    (Subgroup.mem_sup_right (A3.commutator_self_le _ (Subgroup.commutator_mem_commutator hc hc')))

theorem le_perfectCore_sup_centralizer {G : Type*} [Group G] [Finite G]
    {X K Q : Subgroup G} (hKX : K ≤ X) (hQQ : ⁅Q, Q⁆ = Q)
    (hQK : Q ≤ K ⊔ Subgroup.centralizer (X : Set G)) :
    Q ≤ perfectCore K ⊔ Subgroup.centralizer (X : Set G) := by
  have h : ∀ n, Q ≤ derivedSeriesOf K n ⊔ Subgroup.centralizer (X : Set G) := by
    intro n
    induction n with
    | zero => rw [derivedSeriesOf_zero]; exact hQK
    | succ n ih =>
      rw [derivedSeriesOf_succ]
      exact le_commutator_sup_centralizer_of_perfect ((derivedSeriesOf_le K n).trans hKX) hQQ ih
  obtain ⟨n, hn⟩ := exists_perfectCore_eq K
  rw [hn n le_rfl]
  exact h n

theorem le_inf_centralizer_sup_of_perfect {G : Type*} [Group G] {X H Q : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hQH : Q ≤ Subgroup.centralizer (H : Set G)) (hQQ : ⁅Q, Q⁆ = Q)
    (hQX : Q ≤ X ⊔ Subgroup.centralizer (X : Set G)) :
    Q ≤ (X ⊓ Subgroup.centralizer (H : Set G)) ⊔ Subgroup.centralizer (X : Set G) := by
  set C := Subgroup.centralizer (X : Set G)
  have hXN : X ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer X)
  have hHNC : H ≤ Subgroup.normalizer (C : Set G) :=
    hHN.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer X)
  have hd : ∀ y ∈ Q, y ∈ (X : Set G) * (C : Set G) := fun y hy => by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X C hXN]
    exact hQX hy
  have key : ∀ a ∈ X, ∀ c ∈ C, a * c ∈ Q → ∀ h ∈ H, a⁻¹ * (h * a * h⁻¹) ∈ X ⊓ C := by
    intro a ha c hc hq h hh
    have hqh : h * (a * c) = (a * c) * h := (Subgroup.mem_centralizer_iff.mp (hQH hq)) h hh
    have e : a⁻¹ * (h * a * h⁻¹) = c * (h * c * h⁻¹)⁻¹ := by
      calc a⁻¹ * (h * a * h⁻¹) = a⁻¹ * (h * (a * c)) * c⁻¹ * h⁻¹ := by group
        _ = a⁻¹ * ((a * c) * h) * c⁻¹ * h⁻¹ := by rw [hqh]
        _ = c * (h * c * h⁻¹)⁻¹ := by group
    refine ⟨X.mul_mem (X.inv_mem ha) ((Subgroup.mem_normalizer_iff.mp (hHN hh) a).mp ha), ?_⟩
    rw [e]
    exact C.mul_mem hc (C.inv_mem ((Subgroup.mem_normalizer_iff.mp (hHNC hh) c).mp hc))
  rw [← hQQ, Subgroup.commutator_le]
  intro q hq q' hq'
  obtain ⟨a, ha, c, hc, rfl⟩ := hd q hq
  obtain ⟨a', ha', c', hc', rfl⟩ := hd q' hq'
  rw [commutator_mul_centralizer ha ha' hc hc']
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨?_, ?_⟩)
    (Subgroup.mem_sup_right (A3.commutator_self_le _ (Subgroup.commutator_mem_commutator hc hc')))
  · exact A3.commutator_self_le X (Subgroup.commutator_mem_commutator ha ha')
  · show ⁅a, a'⁆ ∈ Subgroup.centralizer (H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨z, hz, e1⟩ : ∃ z ∈ X ⊓ C, h * a * h⁻¹ = a * z :=
      ⟨_, key a ha c hc hq h hh, by group⟩
    obtain ⟨z', hz', e2⟩ : ∃ z' ∈ X ⊓ C, h * a' * h⁻¹ = a' * z' :=
      ⟨_, key a' ha' c' hc' hq' h hh, by group⟩
    have hzz : ⁅z, z'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hz'.2) z hz.1
    have hconj : h * ⁅a, a'⁆ * h⁻¹ = ⁅a, a'⁆ := by
      calc h * ⁅a, a'⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * a' * h⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅a * z, a' * z'⁆ := by rw [e1, e2]
        _ = ⁅a, a'⁆ * ⁅z, z'⁆ := commutator_mul_centralizer ha ha' hz.2 hz'.2
        _ = ⁅a, a'⁆ := by rw [hzz, mul_one]
    calc h * ⁅a, a'⁆ = (h * ⁅a, a'⁆ * h⁻¹) * h := by group
      _ = ⁅a, a'⁆ * h := by rw [hconj]

theorem perfectCore_le_ggOTwoPrime {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    perfectCore Y ≤ ggOTwoPrime Y :=
  (CFSG.SeitzReduction.F4Pilot.le_closure_two_pow_of_perfect (perfectCore_perfect Y)).trans
    (Subgroup.closure_mono fun _ hy => ⟨perfectCore_le Y hy.1, hy.2⟩)

end SecFiveRk1C

theorem ggPerfect_le_oddResidual_centralizer
    {G : Type} [Group G] [Finite G] {X H P : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hPH : P ≤ Subgroup.centralizer (H : Set G))
    (hPP : ⁅P, P⁆ = P)
    (hPXC : P ≤ X ⊔ Subgroup.centralizer (X : Set G)) :
    P ≤ ggOTwoPrime (X ⊓ Subgroup.centralizer (H : Set G)) ⊔
      Subgroup.centralizer (X : Set G) :=
  (SecFiveRk1C.le_perfectCore_sup_centralizer inf_le_left hPP
    (SecFiveRk1C.le_inf_centralizer_sup_of_perfect hHN hPH hPP hPXC)).trans
    (sup_le_sup_right (SecFiveRk1C.perfectCore_le_ggOTwoPrime _) _)

theorem ggRankOnePerf_le_of_normalizer_outSolvable
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (hHN : ggHyperplane Bs r ≤ Subgroup.normalizer (X : Set G))
    (hPN : ggRankOnePerf Bs r ≤ Subgroup.normalizer (X : Set G))
    (hOut : CFSG.Quasithin.OutSolvable ↥X) :
    ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ⊔ Subgroup.centralizer (X : Set G) := by
  have hPP : ⁅ggRankOnePerf Bs r, ggRankOnePerf Bs r⁆ = ggRankOnePerf Bs r :=
    perfectCore_perfect _
  have hPH : ggRankOnePerf Bs r ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    perfectCore_le _
  have hPXC : ggRankOnePerf Bs r ≤ X ⊔ Subgroup.centralizer (X : Set G) :=
    CFSG.Quasithin.H13.Ch4.E443.le_sup_centralizer_of_outSolvable hOut hPN hPP
  simpa [ggRankOneIn] using
    ggPerfect_le_oddResidual_centralizer hHN hPH hPP hPXC

end CFSG.StandardType

end
