module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Position
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Centralizer
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Sylow
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Lines
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Chain
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Comm
import CFSG.LocalAnalysis.StandardType.FS81.RootFusionGen
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.FF81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction
open CFSG.StandardType.FrameRoute.FS81 (IsConjLine)

theorem exists_conj_eq_of_conj_mem_centralizer_inf {G : Type} [Group G] [Finite G] {n : ℕ}
    {b : G} {L : Subgroup G} {K : ℕ → Subgroup G} {t : G} (hA : HypA G n b L)
    (hup : Upstream n b L K t) {Q : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hQn : ∀ x ∈ Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ),
      ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hQL : Q ⊓ L = ⊥)
    (hsup : Q ⊔ L = Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))
    (hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)) =
      Nat.card Q * Nat.card L)
    {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)) :
    ∃ y ∈ ⨆ i : Fin (n + 2), K (i : ℕ), g * b * g⁻¹ = y * b * y⁻¹ := by
  obtain ⟨z, hz, hF⟩ := hup
  have hb3 : orderOf b = 3 := hA.ord
  have hn : 3 ≤ n := by rcases hA.n_cases with h | h <;> omega
  have hKY : ∀ i, i < n + 2 → K i ≤ ⨆ i : Fin (n + 2), K (i : ℕ) := fun i hi =>
    le_iSup (fun j : Fin (n + 2) => K (j : ℕ)) ⟨i, hi⟩
  have hQC : Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ) := by
    rw [← hsup]; exact le_sup_left
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ) := by
    rw [← hsup]; exact le_sup_right
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hβ3 : orderOf (g * b * g⁻¹) = 3 := by
    simpa [hb3] using (MulAut.conj g).orderOf_eq b
  obtain ⟨q, hq, hqL⟩ := exists_conj_mem_of_card_eq_mul hQC hLC hQn hQ3 hQL hcard hg hβ3
  have hl3 : orderOf (q * (g * b * g⁻¹) * q⁻¹) = 3 := by
    simpa [hβ3] using (MulAut.conj q).orderOf_eq (g * b * g⁻¹)
  have hlb : IsConjLine b (Subgroup.zpowers (q * (g * b * g⁻¹) * q⁻¹)) :=
    ⟨q * g, by rw [show q * g * b * (q * g)⁻¹ = q * (g * b * g⁻¹) * q⁻¹ by group]⟩
  obtain ⟨x, hx, hx3, hxb⟩ := hF.conj_b 2 (by omega)
  have hK2L : K 2 ≤ L := by
    rw [← hF.sysL.2.1]
    exact le_iSup (fun i : Fin n => K ((i : ℕ) + 2)) ⟨0, by omega⟩
  obtain ⟨c, hc, hcl⟩ := exists_conj_eq_of_isConjLine hA hz hqL (hK2L hx) hl3 hx3 hlb hxb
  obtain ⟨y, hy, hyx⟩ := exists_conj_eq_of_mem_frame hF hb3 hn hx hx3
  have hyY : y ∈ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    sup_le (sup_le (hKY 0 (by omega)) (hKY 1 (by omega))) (hKY 2 (by omega)) hy
  have hw : (y * c * q) ∈ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyY (hLC hc).2) (hQC hq).2
  refine ⟨(y * c * q)⁻¹, Subgroup.inv_mem _ hw, ?_⟩
  calc g * b * g⁻¹ = (y * c * q)⁻¹ * (y * (c * (q * (g * b * g⁻¹) * q⁻¹) * c⁻¹) * y⁻¹) *
        (y * c * q) := by group
    _ = (y * c * q)⁻¹ * b * ((y * c * q)⁻¹)⁻¹ := by rw [hcl, hyx, inv_inv]

theorem rootFusionE6_holds
    : RootFusionE6 := by
  intro G _ _ _ _ _ n b L hA K t hup hYd h5 hlab hcent g hg
  obtain ⟨F, _, _, hF2, ⟨φ⟩⟩ := exists_mulEquiv_adjointGroup_of_ggHasLabel_E6 hlab
  have : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hF2]; norm_num)
  obtain ⟨S, hS, htS, ht2, hcS⟩ := hYd.syl
  have htY : t ∈ ⨆ i : Fin (n + 2), K (i : ℕ) := hS.1 htS
  obtain ⟨c, hc⟩ := exists_conj_eq_pinnedElt_of_isSylow2In φ hS htY ht2 hcS
  have hZ : Subgroup.center ↥(⨆ i : Fin (n + 2), K (i : ℕ)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : φ y ∈ Subgroup.center (adjointGroup .E6 F) := by
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro a
      have h1 := congrArg φ (hy (φ.symm a))
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hy'
    rw [Subgroup.mem_bot]
    exact φ.injective (by rw [hy', map_one])
  have hbC := centralizer_le_of_yData hA hup hYd hZ hcent
  have hbY : b ∈ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    hbC (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hinv : t * b * t⁻¹ = b⁻¹ := by
    obtain ⟨_, _, hF⟩ := id hup
    exact hF.inv_b
  obtain ⟨hQ2, hQL, hsup, hcard⟩ := twoCore_inf_eq_bot_and_sup_eq hA hup hYd h5 hlab
  refine ⟨g, FrameRoute.FS81.mem_of_conj_mem_of_commute_conj hbC (fun x hx => ?_)
    (fun x hx => ?_) hg, rfl⟩
  ·
    refine exists_conj_eq_of_conj_mem_centralizer_inf hA hup hQ2 ?_ hQL hsup hcard ⟨hx, hcent hx⟩
    intro y hy q hq
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hq
    exact Subgroup.mem_map.2
      ⟨⟨y, hy⟩ * q' * ⟨y, hy⟩⁻¹, (CFSG.pCore_normal).conj_mem q' hq' ⟨y, hy⟩, rfl⟩
  ·
    refine exists_commute_conj_of_conj_eq_pinnedElt φ htY ht2 hc hbY hA.ord hinv hx ?_
    simpa [ht2] using (MulAut.conj x).orderOf_eq t

end CFSG.StandardType.FF81
