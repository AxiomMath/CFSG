module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortRank
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortLift
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Assembly.OpenBridges
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem frameRoutePortPumpAux_elem3Disjoint_mulEquiv
    {A B : Type} [Group A] [Group B] (e : A ≃* B) {r : ℕ}
    (h : Elem3Disjoint A r) : Elem3Disjoint B r := by
  obtain ⟨E, hE, hcard, hdisj⟩ := h
  refine ⟨E.map e.toMonoidHom, hE.map e.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, hz⟩
    have hz' : ∀ g : B, g * e a = e a * g := Subgroup.mem_center_iff.mp hz
    have hza : a ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun g =>
      e.injective (by rw [map_mul, map_mul]; exact hz' (e g))
    have ha1 : a ∈ E ⊓ Subgroup.center A := ⟨ha, hza⟩
    rw [hdisj, Subgroup.mem_bot] at ha1
    rw [Subgroup.mem_bot, ha1, map_one]

theorem F10_normalizer_invariance (hPU : GGPumpupInput) {B Bs : Subgroup G} {x z : G}
    {L D₁ J₁ : Subgroup G} (h : P5Out B Bs x z L D₁ J₁) :
    LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G))
        (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) ∧
      J₁ ≤ ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ ∧
      Bs ≤ Subgroup.normalizer
        ((ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ : Subgroup G) : Set G) ∧
      (Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) ≤
        Subgroup.normalizer
          ((ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ : Subgroup G) : Set G) := by
  obtain ⟨hcfg, hplane, -, h3, -, r, hlt, hw⟩ := h
  obtain ⟨hI, hBs, hDJ⟩ := hcfg
  obtain ⟨hBleBs, hBselem, -, -⟩ := hBs
  obtain ⟨hzB, -, hz1, hz3⟩ := facts_of_closure_pair hI hDJ hplane
  have hzBs : z ∈ Bs := hBleBs hzB
  have hzorder : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let K : Subgroup G := ggLayerClosure 3 C J₁
  have hKdata := pumpup_of_stdSub hPU hI hDJ h3 hplane
  obtain ⟨hKc, hJK, -, -⟩ := hKdata
  have hKC : K ≤ C := hKc.1
  obtain ⟨hPre, -⟩ := hDJ
  obtain ⟨-, -, -, -, -, hJ1comp, -⟩ := hPre
  have hJ1q : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J₁).mp
      hJ1comp.2.2
  have hJ1C : J₁ ≤ C := hJK.trans hKC
  let O : Subgroup ↥C := LargeEvenPPrimeCore 3 ↥C
  let mk : ↥C →* (↥C ⧸ O) := QuotientGroup.mk' O
  let φ : ↥J₁ →* (↥C ⧸ O) := mk.comp (Subgroup.inclusion hJ1C)
  have hperf : commutator ↥J₁ = ⊤ := hJ1q.1
  have hker : φ.ker ≤ Subgroup.center ↥J₁ := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.i253_normal_le_center_or_top hJ1q φ.ker
      with hcent | htop
    · exact hcent
    · exfalso
      have hJ1O : J₁.subgroupOf C ≤ O := by
        intro y hy
        have hyJ : y.val ∈ J₁ := (Subgroup.mem_subgroupOf).mp hy
        have hφ : φ ⟨y.val, hyJ⟩ = 1 := by
          have : (⟨y.val, hyJ⟩ : ↥J₁) ∈ φ.ker := by rw [htop]; trivial
          simpa [MonoidHom.mem_ker] using this
        have hincl : Subgroup.inclusion hJ1C ⟨y.val, hyJ⟩ = y := Subtype.ext rfl
        rw [show φ ⟨y.val, hyJ⟩ = mk y by simp [φ, hincl]] at hφ
        exact (QuotientGroup.eq_one_iff (N := O) y).mp hφ
      have hcardEq : Nat.card J₁ = Nat.card (J₁.subgroupOf C) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ1C).toEquiv).symm
      have hdvd : Nat.card J₁ ∣ Nat.card O := by
        rw [hcardEq]
        exact Subgroup.card_dvd_of_le hJ1O
      have h3O : 3 ∣ Nat.card O := h3.trans hdvd
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcop : Nat.Coprime 3 (Nat.card O) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥C)
      exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop h3O
  have hrange : φ.range ≤ barImage z K := by
    dsimp [φ, barImage]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono C hJK)
  have hwK : Rank3Witness ↥(barImage z K) r :=
    F08b_transfer φ hperf hker (barImage z K) hrange hw
  have hCnormK : C ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    let K' : Subgroup G := K.map (MulAut.conj g).toMonoidHom
    have hCmap : C.map (MulAut.conj g).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    have hK'C : K' ≤ C := by
      have hmono : K.map (MulAut.conj g).toMonoidHom ≤ C.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hKC
      rwa [hCmap] at hmono
    have hK'c : LargeEvenPComponent 3 C K' := by
      have hKgla : CFSG.Open.GLAPComponent 3 C K :=
        (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 C K).1 hKc
      have hconj := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hKgla g⁻¹
      have hCGLB : GLBConj g⁻¹ C = C := by
        dsimp [GLBConj]
        rw [inv_inv]
        exact hCmap
      have hKGLB : GLBConj g⁻¹ K = K' := by
        dsimp [GLBConj, K']
        rw [inv_inv]
      have hconj' : CFSG.Open.GLAPComponent 3 C K' := by
        rwa [hCGLB, hKGLB] at hconj
      exact (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 C K').mpr hconj'
    have hbar : barImage z K' = (barImage z K).map (MulAut.conj (mk ⟨g, hg⟩)).toMonoidHom := by
      have hcomp : (MulAut.conj (mk ⟨g, hg⟩)).toMonoidHom.comp mk =
          mk.comp (MulAut.conj (⟨g, hg⟩ : ↥C)).toMonoidHom := by
        ext y
        simp [mk, MulAut.conj_apply]
      have hsub : K'.subgroupOf C =
          (K.subgroupOf C).map (MulAut.conj (⟨g, hg⟩ : ↥C)).toMonoidHom := by
        ext y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · intro hy
          obtain ⟨k, hkK, hky⟩ := Subgroup.mem_map.mp hy
          refine ⟨⟨k, hKC hkK⟩, (Subgroup.mem_subgroupOf).mpr hkK, Subtype.ext ?_⟩
          simpa [MulAut.conj_apply] using hky
        · rintro ⟨k, hk, rfl⟩
          exact Subgroup.mem_map.mpr ⟨k.val, (Subgroup.mem_subgroupOf).mp hk,
            by simp [MulAut.conj_apply]⟩
      change (K'.subgroupOf C).map mk = ((K.subgroupOf C).map mk).map _
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hsub]
    have hwK_elem : Elem3Disjoint ↥(barImage z K) r := by
      obtain ⟨E, t, hE, hcard, hdisj, -, -, -⟩ := hwK
      exact ⟨E, hE, hcard, hdisj⟩
    have hwK'_elem : Elem3Disjoint ↥(barImage z K') r := by
      have e : ↥(barImage z K) ≃* ↥(barImage z K') :=
        (Subgroup.equivMapOfInjective (barImage z K) (MulAut.conj (mk ⟨g, hg⟩)).toMonoidHom
          (MulAut.conj _).injective).trans (MulEquiv.subgroupCongr hbar.symm)
      exact frameRoutePortPumpAux_elem3Disjoint_mulEquiv e hwK_elem
    have hK'eqK : K' = K := by
      by_contra hne
      have hne' : K ≠ K' := fun h => hne h.symm
      have hcontra := F09_rank_obstruction hzorder hne' hKc hK'c hwK hwK'_elem
      exact (not_le_of_gt hlt) hcontra
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hK'eqK
  have hBsC : Bs ≤ C := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : IsMulCommutative Bs := hBselem.1
    exact Subgroup.mul_comm_of_mem_isMulCommutative Bs hb hzBs
  refine ⟨hKc, hJK, hBsC.trans hCnormK, ?_⟩
  intro g hg
  exact hCnormK hg.2

end CFSG.StandardType.FrameRoute

end
