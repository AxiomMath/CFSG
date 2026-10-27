module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4t_J_le_K {G : Type} [Group G] [Finite G] (hI3 : GGNbrSubcomponentInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    J ≤ K :=
  hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb

private theorem l05nL4t_isComponentOf {G : Type} [Group G] [Finite G]
    {p : ℕ} {B : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hnb : GGNbr p B x D J y K) (hJK : J ≤ K) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
  isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnb hJK

theorem ggNbrK_label_J_of_tcj {G : Type} [Group G] [Finite G] (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hinn : GGInnerDiagAll p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (K ⧸ Subgroup.center K) ∧ LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hx : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hx
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJK : J ≤ K := l05nL4t_J_le_K hI3 hcfg hnb
  have hK : GGInnerDiagOn Bs K := hinn.2 y K hnb
  have hKperf : commutator ↥K = ⊤ := hK.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hTCJ p hp hp2 lab hlab) hK
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨hBN, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBN hxBs
  have hx1 : x ^ p = 1 := hBel.2 x hx
  have hxp : K.normalizerMonoidHom ⟨x, hxN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  let ψ : ↥K →* R := (θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥K := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (K.normalizerMonoidHom ⟨x, hxN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (K.normalizerMonoidHom ⟨x, hxN⟩ l) ?_⟩
    show ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    l05nL4t_isComponentOf hSS hDJ hnb hJK
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥K ψ hψsurj hψker hKperf _ hxp hφe (J.subgroupOf K) hJcomp
  refine ⟨lab, labJ, hlab, hhas, hlabJ, hdvd, ?_⟩
  exact ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
    (Subgroup.map_center_eq _)) hhasJ

end CFSG.StandardType
