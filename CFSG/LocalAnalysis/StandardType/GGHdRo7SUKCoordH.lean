module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordD
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordHA
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_jCentralizerCard {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 := by
  exact hH.1.card_bstar_inf_centralizer_J_le

private noncomputable def hdRo7SUKCoordAux_quotAut (H : Type) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun α := QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro α β
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]

private theorem hdRo7SUKCoordAux_quotAut_injective (H : Type) [Group H]
    (hperf : commutator H = ⊤) : Function.Injective (hdRo7SUKCoordAux_quotAut H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  have hfix : ∀ g : H, (α g)⁻¹ * g ∈ Subgroup.center H := by
    intro g
    have h1 : QuotientGroup.mk' (Subgroup.center H) (α g) =
        QuotientGroup.mk' (Subgroup.center H) g := by
      have := congrArg (fun f : MulAut (H ⧸ Subgroup.center H) =>
        f (QuotientGroup.mk' (Subgroup.center H) g)) hα
      simpa [hdRo7SUKCoordAux_quotAut, QuotientGroup.congr_mk] using this
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨w, hw, hwg⟩ := h1
    have : (α g)⁻¹ * g = w := by
      calc (α g)⁻¹ * g = (α g)⁻¹ * (α g * w) := by rw [hwg]
        _ = w := by rw [inv_mul_cancel_left]
    rw [this]
    exact hw
  let z : H →* H :=
    { toFun := fun g => (α g)⁻¹ * g
      map_one' := by simp
      map_mul' := by
        intro a b
        have hza : (α a)⁻¹ * a ∈ Subgroup.center H := hfix a
        have hzb : (α b)⁻¹ * b ∈ Subgroup.center H := hfix b
        have hcomm : (α a)⁻¹ * a * (α b)⁻¹ = (α b)⁻¹ * ((α a)⁻¹ * a) :=
          (Subgroup.mem_center_iff.mp hza (α b)⁻¹).symm
        calc (α (a * b))⁻¹ * (a * b)
            = (α b)⁻¹ * (α a)⁻¹ * (a * b) := by rw [map_mul, mul_inv_rev]
          _ = ((α b)⁻¹ * ((α a)⁻¹ * a)) * b := by group
          _ = (((α a)⁻¹ * a) * (α b)⁻¹) * b := by rw [hcomm]
          _ = ((α a)⁻¹ * a) * ((α b)⁻¹ * b) := by group }
  have hzle : z.range ≤ Subgroup.center H := by
    rintro _ ⟨g, rfl⟩
    exact hfix g
  have hker : commutator H ≤ z.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    have ha := hzle (show z a ∈ z.range from ⟨a, rfl⟩)
    have hb := hzle (show z b ∈ z.range from ⟨b, rfl⟩)
    have hcomm : Commute (z a) (z b) :=
      (Subgroup.mem_center_iff.mp ha (z b)).symm
    rw [map_commutatorElement]
    exact hcomm.commutator_eq
  have hkertop : z.ker = ⊤ := by
    rw [← top_le_iff, ← hperf]
    exact hker
  have hz : z = 1 := by
    ext g
    exact MonoidHom.mem_ker.mp (hkertop ▸ Subgroup.mem_top g)
  ext g
  have hg : z g = 1 := by rw [hz]; rfl
  exact (inv_mul_eq_one.mp hg)

theorem hdRo7SUKCoordAux_jAction {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∃ f : ↥Bs →* MulAut (↥J ⧸ Subgroup.center ↥J),
      f.ker = (Bs ⊓ Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
  have hstdPre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hD_le_B : D ≤ B := hstdPre.1
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hstdPre.2.2.2.2.2.2
  have hJlayer : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstdPre.2.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstdPre.2.2.2.2.2.1
  have hJperf : commutator ↥J = ⊤ := hJcomp.2.2.1
  have hBs_ab : CFSG.Open.IsElemAbelian p Bs := hH.1.2.1.2.1
  have hB_le_Bs : B ≤ Bs := hH.1.2.1.1
  have hBsN_L : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  have hBs_cent_D : Bs ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (CFSG.Open.IsElemAbelian.comm hBs_ab hb (hB_le_Bs (hD_le_B hd))).symm
  have hBsN_J : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hJlayer]
    refine le_normalizer_of_map_conj_le (fun g hg => map_conj_largeEvenLayer_le ?_)
    exact mem_normalizer_inf_centralizer (hBsN_L hg) (hBs_cent_D hg)
  let g : ↥Bs →* MulAut ↥J :=
    (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hBsN_J)
  let f : ↥Bs →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    (hdRo7SUKCoordAux_quotAut ↥J).comp g
  refine ⟨f, ?_⟩
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hb
    have hgb : g b = 1 :=
      hdRo7SUKCoordAux_quotAut_injective ↥J hJperf (by
        show (hdRo7SUKCoordAux_quotAut ↥J) (g b) = (hdRo7SUKCoordAux_quotAut ↥J) 1
        rw [map_one]
        simpa [f] using hb)
    refine ⟨b.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun j hj => ?_)
    have h1 : ((g b) ⟨j, hj⟩ : ↥J) = ⟨j, hj⟩ := by rw [hgb]; rfl
    have hcoe : (((g b) ⟨j, hj⟩ : ↥J) : G) = (b : G) * j * (b : G)⁻¹ := rfl
    have h2 : (b : G) * j * (b : G)⁻¹ = j := by rw [← hcoe, h1]
    have h3 : (b : G) * j = j * (b : G) := by
      have := congrArg (fun z : G => z * (b : G)) h2
      simpa [mul_assoc] using this
    exact h3.symm
  · rintro ⟨hbBs, hbC⟩
    have hgb : g b = 1 := by
      ext j
      show (b : G) * (j : G) * (b : G)⁻¹ = (j : G)
      have hbj : (j : G) * (b : G) = (b : G) * (j : G) :=
        Subgroup.mem_centralizer_iff.mp hbC (j : G) j.2
      rw [hbj.symm]
      group
    show f b = 1
    simp [f, hgb]

theorem hdRo7SUKCoordAux_jImageCard {G : Type} [Group G] [Finite G] {p : ℕ}
    {J K : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank2 p J K)
    (A : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hA : CFSG.Open.IsElemAbelian 3 A) :
    Nat.card A ≤ 3 ^ (hdRo7SUKCoordAux_rowRank hrow - 3) := by
  let labJ := Classical.choose hrow
  let labK := Classical.choose (Classical.choose_spec hrow)
  have hspec := Classical.choose_spec (Classical.choose_spec hrow)
  have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := hspec.2.2.1
  have hrowData : ggRowSUCorank2 p labJ labK := hspec.2.2.2.2
  obtain ⟨hp3, hJtag, hJn, hKtag, hKn, hrank, hrank6, h3m⟩ := hrowData
  have hHasJ' : LargeEvenRecipeUnitary (labJ.rank + 1) (2 ^ labJ.n)
      (fun R' _ _ _ => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R')) := by
    simpa only [GGHasLabel, LargeEvenRawDatum, hJtag] using hHasJ
  obtain ⟨K', hK'field, hK'fin, hK'card, hQ⟩ := hHasJ'
  letI : Field K' := hK'field
  letI : Finite K' := hK'fin
  rw [hJn] at hK'card hQ
  obtain ⟨θ⟩ := hQ
  let N := labJ.rank + 1
  have hrowRank : hdRo7SUKCoordAux_rowRank hrow = labK.rank + 1 :=
    hdRo7SUKCoordAux_rowRank_eq hrow
  have hN5 : 5 ≤ N := by omega
  have hK'card' : Nat.card K' = (2 ^ 1) ^ 2 := hK'card
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K' :=
    ⟨Nat.prime_two, le_rfl, by rw [hK'card']; norm_num⟩
  let A' : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K' (2 ^ 1)))) :=
    A.map (MulAut.congr θ).toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian 3 A' := hA.map (MulAut.congr θ).toMonoidHom
  have hrange :=
    hdRo7SUKCoordAux_le_range_uConjAut_of_isElemAbelian h (by omega : 4 ≤ N) A' hA'
  have hI : (A' : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K' (2 ^ 1))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K' (2 ^ 1)))
        (LargeEvenGUSet (Fin N) K' (2 ^ 1)) := by
    intro a ha
    obtain ⟨g, hg⟩ := hrange a ha
    rw [← hg]
    exact hdRo7SUKCoordAux_range_uConjAut_subset h (by omega : 1 ≤ N) ⟨g, rfl⟩
  have hbound : Nat.card A' ≤ 3 ^ (N - 1) :=
    hdRo7SUKCoordAux_card_le_unitary h hK'card' (by omega : 3 ≤ N)
      (by intro hh; have h1 : N = 3 := congrArg Prod.fst hh; omega)
      Nat.prime_three (by norm_num) hA' hI
  have hcardA' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr θ).injective
  rw [hcardA'] at hbound
  have hexp : N - 1 = hdRo7SUKCoordAux_rowRank hrow - 3 := by
    rw [hrowRank]
    omega
  rwa [hexp] at hbound

theorem hdRo7SUKCoordAux_rankUpper_viaJ {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Nat.card ↥Bs ≤ p ^ (hdRo7SUKCoordAux_rowRank hrow) := by
  have hspec := hdRo7SUKCoordAux_rowRank_spec hrow
  have hp3 : p = 3 := hspec.1
  have hm7 : 7 ≤ hdRo7SUKCoordAux_rowRank hrow := hspec.2.1
  obtain ⟨f, hker⟩ := hdRo7SUKCoordAux_jAction hH hRig hrow
  have hC : Nat.card f.ker ≤ p ^ 3 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hdRo7SUKCoordAux_jCentralizerCard hH
  have hI : Nat.card f.range ≤ 3 ^ (hdRo7SUKCoordAux_rowRank hrow - 3) := by
    refine hdRo7SUKCoordAux_jImageCard hrow f.range ?_
    have hBsE : CFSG.Open.IsElemAbelian p Bs := hH.1.2.1.2.1
    have htop : CFSG.Open.IsElemAbelian p (⊤ : Subgroup ↥Bs) := by
      refine ⟨?_, ?_⟩
      · rw [isMulCommutative_iff]
        intro a b
        exact Subtype.ext (isMulCommutative_iff.mp hBsE.1 (a : ↥Bs) (b : ↥Bs))
      · intro a _
        exact Subtype.ext (hBsE.2 (a : ↥Bs) (a : ↥Bs).2)
    have hmap := hdRo7SUKCoordAux_isElemAbelian_map f (E := ⊤) htop
    rw [← MonoidHom.range_eq_map f] at hmap
    rw [hp3] at hmap
    exact hmap
  have hcard : Nat.card ↥Bs = Nat.card f.ker * Nat.card f.range := by
    have h1 : Nat.card ↥Bs = Nat.card (↥Bs ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥Bs ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h1, h2, mul_comm]
  calc Nat.card ↥Bs = Nat.card f.ker * Nat.card f.range := hcard
    _ ≤ p ^ 3 * 3 ^ (hdRo7SUKCoordAux_rowRank hrow - 3) := Nat.mul_le_mul hC hI
    _ = p ^ (hdRo7SUKCoordAux_rowRank hrow) := by
          subst hp3
          rw [← pow_add]
          congr 1
          omega

end CFSG.StandardType.HdRo7SU

end
