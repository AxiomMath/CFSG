module

public import CFSG.LocalAnalysis.UniquenessCase.UCK332RankOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.ConclNineteenTwelveWC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactNineteenTwentySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 (Zsub)
open scoped Pointwise commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactCentralOmega)

variable {G : Type} [Group G] [Finite G]

theorem nineteen_twentysix_orbit_one (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B 3 A₀ H) (hAV : A ≤ centralizer (V₀ : Set G))
    (hΩ : ∀ Q : Subgroup G, IsPGroup 3 Q → ∀ x ∈ Q, x ^ 3 = 1 → ∀ y ∈ Q, y ^ 3 = 1 →
      x * y = y * x)
    (hrk : ∀ X : Subgroup G, IsElemAbelian 3 X → Nat.card X ≤ 27)
    (hwc : Concl19_12wc A) (h332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hCO : KFactCentralOmega) (hK1 : K_19_26_rankOne) {E K : Subgroup G} (hEA : E ≤ A)
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hA₀E : A₀ ≤ E)
    (hNEM : normalizer (E : Set G) ≤ D.M) (hKH : K ≤ H)
    (hKcomp : CFSG.IsComponent (K.subgroupOf H)) (hfaith : ActsFaithfullyOn V₀ K)
    (hZodd : Odd (Nat.card (Subgroup.center ↥K)))
    (hZV : V₀ ≤ centralizer (Zsub K : Set G))
    (hEN : E ≤ normalizer (K : Set G)) : False := by
  classical
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKH)).mp hKcomp.1
  have hKq' : CFSG.Open.IsQuasisimple ↥K :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hKq
  have hcenter : Subgroup.center G = ⊥ :=
    @CFSG.Walter.center_eq_bot_of_isSimpleGroup G _ D.standing.simple D.standing.nonab
  have hHne_top : H ≠ ⊤ := by
    intro hHtop
    have hA0center : A₀ ≤ Subgroup.center G := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer (A₀ : Set G) := by
        rw [← h.hH, hHtop]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg a ha).symm
    have hA0bot : A₀ = ⊥ := le_bot_iff.mp (hA0center.trans (le_of_eq hcenter))
    have hcard := h.ctx22.hcard
    rw [hA0bot, Subgroup.card_bot] at hcard
    omega
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.Open.IsKProper.isKGroup D.standing.kProper H hHne_top
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hKK : CFSG.Open.IsKGroup ↥K := hHK.of_le hKH
  have hKEK : CFSG.Open.IsKGroup ↥(K ⊔ E) := hHK.of_le (sup_le hKH (hEA.trans hAH))
  have hA₀C : A₀ ≤ centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mpr (h.hH ▸ hKH)
  have hA₀K : A₀ ⊓ K = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.inf_eq_bot_of_kFactCentralOmega hCO hKq' hKK h.ctx22.hcard
      hA₀C hΩ hrk
  have hEK : ¬ E ≤ centralizer (K : Set G) := by
    intro hc
    apply not_le_M_of_actsFaithfullyOn D h hKH hKcomp hfaith
    exact (Subgroup.le_centralizer_iff.mp hc).trans
      ((Subgroup.centralizer_le_normalizer (E : Set G)).trans hNEM)
  obtain ⟨e, heE, he3, hEeq, hcase, hrk1⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.exists_elt_of_k332 h332 hKq' hKEK hEN hEel hEcard hA₀E
      h.ctx22.hcard hA₀C hA₀K hEK hΩ hrk
      (fun g _ hg => hwc E hEA hEel hEcard g hg)
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0M : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV0in
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
  have hV0NK : V₀ ≤ normalizer (K : Set G) := nineteen_twentyfour_two D h K hKH hKcomp
  have hV04 : 4 ≤ Nat.card V₀ := by
    rw [card_eq_two_pow_mSub (CFSG.Open.IsElemAbelian.isPGroup hV0el)]
    have hbig : 2 ≤ mSub V₀ := h.ctx22.ctx.hyp.big
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) hbig
  have heV : V₀ ≤ centralizer ({e} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp (hAV (hEA heE)) v hv).symm
  have hle := hK1 G K V₀ e hKq' hKK hZodd hrk1 hV0el hV04 hV0NK hfaith hTI hZV he3
    (hEN heE) heV hcase
  apply not_le_M_of_actsFaithfullyOn D h hKH hKcomp hfaith
  refine hle.trans (sup_le ?_ ?_)
  ·
    intro x hx
    obtain ⟨hxK, hxe⟩ := Subgroup.mem_inf.mp hx
    have hxA : x ∈ centralizer (A₀ : Set G) := h.hH ▸ hKH hxK
    have hA₀x : A₀ ≤ centralizer ({x} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (Subgroup.mem_centralizer_iff.mp hxA a ha).symm
    have hex : Subgroup.zpowers e ≤ centralizer ({x} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (Subgroup.mem_centralizer_iff.mp hxe e (Set.mem_singleton e)).symm
    have hEx : E ≤ centralizer ({x} : Set G) := by
      rw [hEeq]
      exact sup_le hA₀x hex
    apply hNEM
    apply Subgroup.centralizer_le_normalizer (E : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hEx hy) x (Set.mem_singleton x)).symm
  ·
    intro x hx
    obtain ⟨-, hxV⟩ := Subgroup.mem_inf.mp hx
    rw [← hV0M]
    exact Subgroup.centralizer_le_normalizer (V₀ : Set G) hxV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
