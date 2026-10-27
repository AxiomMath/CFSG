module

public import CFSG.LocalAnalysis.StandardType.GGTCJD4Tag
public import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48d_join
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} {n : ℕ}
    (hD4 : GGTCJD4TagKnown) (hn : LargeEvenInLambda2 (⟨.D, 4, n⟩ : LargeEvenLabel))
    (hM : LargeEvenMarking ↥X (fun lab' _ _ I _ θ => lab' = (⟨.D, 4, n⟩ : LargeEvenLabel) ∧
      Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : ↥X ⧸ Subgroup.center ↥X ≃* R),
      (Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      (∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
              GGHasLabel labJ (J ⧸ Subgroup.center J) → labJ.tag ≠ .G2 ∧ labJ.tag ≠ .triD4) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hM
  obtain ⟨R, hR, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have hlab_eq : lab = (⟨.D, 4, n⟩ : LargeEvenLabel) := hP.1
  subst lab
  obtain ⟨-, hBs, hind⟩ := hP
  have hjoin := hD4 n hn _ hraw
  obtain ⟨R', hR', I', F', ⟨hs', hna', θ', hP'⟩, hD4'⟩ := largeEvenRawDatum_exists hjoin
  obtain ⟨-, hBs', hind'⟩ := hP'
  exact ⟨R', hR', I', F', θ', ⟨hBs', hind'⟩, hD4'⟩

theorem ggNbr_D4Tag_L
    {G : Type} [Group G] [Finite G] (hD4 : GGTCJD4TagKnown) (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) (hp : p = 3) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {n : ℕ} (hn : LargeEvenInLambda2 (⟨.D, 4, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.D, 4, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    {labJ : LargeEvenLabel} (hJ2 : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    labJ.tag ≠ .G2 ∧ labJ.tag ≠ .triD4 := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hy : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hy
  subst hp
  have hM := ggInnerDiagOn_relabel hRig hinn hn hL
  have hLperf : commutator ↥L = ⊤ := hM.1
  obtain ⟨R, _, I, F, θ, ⟨hBs, hind⟩, hD4prop⟩ := l48d_join hD4 hn hM
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hBs hyBs
  have hy1 : y ^ 3 = 1 := hBel.2 y hy
  have hep : L.normalizerMonoidHom ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (Bs.inv_mem hyBs)
  let ψ : ↥L →* R := (θ : L ⧸ Subgroup.center L →* R).comp (QuotientGroup.mk' (Subgroup.center L))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥L := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : L ⧸ Subgroup.center L) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (L.normalizerMonoidHom ⟨y, hyN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hDy : D = Subgroup.closure {x, y} := hnb.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rw [hDy, ggInf_centralizer_pair hLx] at hcomp
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hyN hcomp
  have hJ' : GGHasLabel labJ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
      (Subgroup.map_center_eq _)).symm hJ
  exact hD4prop ↥L ψ hψsurj hψker hLperf (L.normalizerMonoidHom ⟨y, hyN⟩) hep hφe
    (J.subgroupOf L) hJcomp labJ hJ2 hJ'

theorem ggNbr_D4Tag_K
    {G : Type} [Group G] [Finite G] (hD4 : GGTCJD4TagKnown) (hRig : GGLabelRigidInput)
    (hI3 : GGNbrSubcomponentInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hinn : GGInnerDiagAll p B Bs x L D J) (hp : p = 3)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.D, 4, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.D, 4, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    {labJ : LargeEvenLabel} (hJ2 : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    labJ.tag ≠ .G2 ∧ labJ.tag ≠ .triD4 := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hx : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hx
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJK : J ≤ K := hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb
  have hKinn : GGInnerDiagOn Bs K := hinn.2 y K hnb
  subst hp
  have hM := ggInnerDiagOn_relabel hRig hKinn hn hK
  have hKperf : commutator ↥K = ⊤ := hM.1
  obtain ⟨R, _, I, F, θ, ⟨hBs, hind⟩, hD4prop⟩ := l48d_join hD4 hn hM
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBs hxBs
  have hx1 : x ^ 3 = 1 := hBel.2 x hx
  have hep : K.normalizerMonoidHom ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
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
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  have hJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)).symm hJ
  exact hD4prop ↥K ψ hψsurj hψker hKperf (K.normalizerMonoidHom ⟨x, hxN⟩) hep hφe
    (J.subgroupOf K) hJcomp labJ hJ2 hJ'

end CFSG.StandardType

end
