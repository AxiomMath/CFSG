module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic
public import CFSG.GroupTheory.CommutingConjugatePair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem bParam_le_of_isComponentOf {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (h77 : Inputs1719.W4Lem7_7)
    {Y X : Subgroup (MulAut W)} {𝒦 : Set (Subgroup (MulAut W))} {m : ℕ}
    (hcomp : ∀ K ∈ 𝒦, CFSG.Open.IsComponentOf K Y)
    (hX : X ≤ ⨆ K ∈ 𝒦, K)
    (hm : ∀ K ∈ 𝒦, ∀ n, Nonempty (Inputs1719.ACandidate ↥K n) → n ≤ m) :
    bParam X Y ≤ m := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun φ : MulAut W => (φ : W → W)) DFunLike.coe_injective
  change sSup {k : ℕ | 0 < k ∧ ∃ A ∈ E3.aSet k Y, ⁅X, A⁆ ≠ ⊥} ≤ m
  refine csSup_le' fun k hk => ?_
  obtain ⟨-, A, hA, hne⟩ := hk
  by_contra hle
  push Not at hle
  have hex : ∃ K ∈ 𝒦, ⁅K, A⁆ ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine hX.trans (iSup₂_le fun K hK => ?_)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (h K hK)
  obtain ⟨K, hK, hKA⟩ := hex
  have hKc : CFSG.Open.IsComponentOf K Y := hcomp K hK
  have hlt : ∀ n, Nonempty (Inputs1719.ACandidate ↥K n) → n < k := by
    intro n hn
    have hnle : n ≤ m := hm K hK n hn
    omega
  have h77K : ⁅K, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h77 W hW Y K A k hKc hA hlt
  exact hKA h77K

namespace Inputs1719

theorem InGq.of_mulEquiv {X Y : Type} [Group X] [Group Y] {q : ℕ}
    (h : InGq X q) (e : X ≃* Y) : InGq Y q := by
  rcases h with ⟨t, n, p, e', hp, hp2, he, hq, hmodel⟩ | ⟨hq3, hmodel⟩
  · exact Or.inl ⟨t, n, p, e', hp, hp2, he, hq, CFSG.Blueprint.LieModel.of_mulEquiv e hmodel⟩
  · exact Or.inr ⟨hq3, CFSG.Blueprint.LieModel.of_mulEquiv e hmodel⟩

theorem InGq.exists_odd_prime_pow {X : Type} [Group X] {q : ℕ} (h : InGq X q) :
    ∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < e ∧ q = p ^ e := by
  rcases h with ⟨-, -, p, e, hp, hp2, he, hq, -⟩ | ⟨hq3, -⟩
  · exact ⟨p, e, hp, hp2, he, hq⟩
  · exact ⟨3, 1, Nat.prime_three, by norm_num, by norm_num, by omega⟩

end Inputs1719

theorem aCandidate_bounds_of_inGq (h106 : Inputs1719.W4Lem10_6Q)
    {H : Type} [Group H] [Finite H] (hH : CFSG.Open.IsQuasisimple H)
    (hodd : Odd (Nat.card (Subgroup.center H)))
    {q : ℕ} (hq : Inputs1719.InGq (H ⧸ Subgroup.center H) q)
    {n : ℕ} (c : Inputs1719.ACandidate H n) :
    (9 < q → n = 1) ∧ (3 < q → n ≤ 2) := by
  classical
  letI := c.commGroup
  letI := c.finiteW
  haveI : Finite (MulAut c.W) :=
    Finite.of_injective (fun φ : MulAut c.W => (φ : c.W → c.W)) DFunLike.coe_injective
  have hHtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup H) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hH
  have hft : fstarTop H = ⊤ := fstar_eq_self_of_isQuasisimple hHtop
  obtain ⟨Z₀, hZ₀, hZ₀le, ⟨e⟩⟩ := c.central_factor
  letI : Z₀.Normal := hZ₀
  have hFle : Fstar c.Y ≤ c.Y := Subgroup.map_subtype_le _
  let eY : ↥(fstarSubOf c.Y) ≃* ↥(Fstar c.Y) :=
    Subgroup.subgroupOfEquivOfLe hFle
  let qmap : ↥(fstarTop H) →* (↥(fstarTop H) ⧸ Z₀) := QuotientGroup.mk' Z₀
  let φ : ↥(fstarTop H) →* ↥(Fstar c.Y) :=
    eY.toMonoidHom.comp (e.symm.toMonoidHom.comp qmap)
  have hφs : Function.Surjective φ :=
    eY.surjective.comp (e.symm.surjective.comp (QuotientGroup.mk'_surjective Z₀))
  have hker : φ.ker ≤ Subgroup.center ↥(fstarTop H) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : e.symm (qmap x) = 1 := by
      apply eY.injective
      rw [map_one]
      simpa [φ] using hx
    have h2 : qmap x = 1 := e.symm.injective (by simpa using h1)
    exact hZ₀le ((QuotientGroup.eq_one_iff x).1 h2)
  have hcenter : Subgroup.center ↥(Fstar c.Y) =
      (Subgroup.center ↥(fstarTop H)).map φ :=
    CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple c.hLq hφs hker
  have hoddTop : Odd (Nat.card (Subgroup.center ↥(fstarTop H))) := by
    rw [hft]
    rw [Nat.card_congr (Subgroup.centerCongr
      (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)).toEquiv]
    exact hodd
  have hoddF : Odd (Nat.card (Subgroup.center ↥(Fstar c.Y))) := by
    rw [hcenter]
    exact Odd.of_dvd_nat hoddTop
      (Subgroup.card_map_dvd (H := Subgroup.center ↥(fstarTop H)) (f := φ))
  have hLgq : CFSG.Open.IsQuasisimple ↥(fstarSubOf c.Y) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).1 c.hLgq
  have hLq : CFSG.Open.IsQuasisimple ↥(Fstar c.Y) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eY.symm hLgq
  have hO2 : O2Trivial (Fstar c.Y) := by
    intro P hP hPn hP2
    have hP2' : IsPGroup 2 (P.subgroupOf (Fstar c.Y)) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
    have hpc : P.subgroupOf (Fstar c.Y) ≤ CFSG.pCore 2 ↥(Fstar c.Y) := by
      rw [CFSG.pCore]
      exact le_sSup ⟨hPn, hP2'⟩
    have hcent : CFSG.pCore 2 ↥(Fstar c.Y) ≤ Subgroup.center ↥(Fstar c.Y) :=
      _root_.GL83.I243.pCore_le_center Nat.prime_two hLq
    have hle : P.subgroupOf (Fstar c.Y) ≤ Subgroup.center ↥(Fstar c.Y) := hpc.trans hcent
    have hbot : P.subgroupOf (Fstar c.Y) = ⊥ := by
      have h := _root_.CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hP2' hoddF
      rwa [inf_eq_left.mpr hle] at h
    rw [← Subgroup.map_subgroupOf_eq_of_le hP, hbot, Subgroup.map_bot]
  have hInTarget : Inputs1719.InGq
      (↥(Fstar c.Y) ⧸ Subgroup.center ↥(Fstar c.Y)) q := by
    let eTop : ↥(fstarTop H) ≃* H :=
      hft ▸ (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
    let eQTop : (H ⧸ Subgroup.center H) ≃*
        (↥(fstarTop H) ⧸ Subgroup.center ↥(fstarTop H)) :=
      QuotientGroup.congr (Subgroup.center H)
        (Subgroup.center ↥(fstarTop H)) eTop.symm
        (Subgroup.map_center_eq eTop.symm)
    let eQY : (↥(fstarSubOf c.Y) ⧸ Subgroup.center ↥(fstarSubOf c.Y)) ≃*
        (↥(Fstar c.Y) ⧸ Subgroup.center ↥(Fstar c.Y)) :=
      QuotientGroup.congr (Subgroup.center ↥(fstarSubOf c.Y))
        (Subgroup.center ↥(Fstar c.Y)) eY (Subgroup.map_center_eq eY)
    exact InGq.of_mulEquiv (InGq.of_mulEquiv (InGq.of_mulEquiv hq eQTop) c.φ) eQY
  obtain ⟨p, e', hp, hp2, he, hqpow⟩ := InGq.exists_odd_prime_pow hInTarget
  have hLqNat : CFSG.IsQuasisimple ↥(Fstar c.Y) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hLq
  have h106App := fun h3 : 3 < q => h106 c.W c.expTwo c.Y (Fstar c.Y) p e' q
    hFle c.hLgn rfl hLqNat hO2 hp hp2 he hqpow h3 hInTarget
  refine ⟨fun h9 => ?_, fun h3 => ?_⟩
  · rw [c.eq_n, (h106App (by omega)).1 h9]
  · rw [c.eq_n]
    exact (h106App h3).2

theorem aCandidate_barSub_conj_bounds {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : S17.Ctx17_6 D V₀ V L r q) (h106 : Inputs1719.W4Lem10_6Q)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥) {g : ↥D.M} {n : ℕ}
    (c : Inputs1719.ACandidate
      ↥(barSub V₀ V hC.hyp125.isElemAbelian
        (L.map (MulAut.conj (g : G)).toMonoidHom)) n) :
    (9 < q → n = 1) ∧ (3 < q → n ≤ 2) := by
  classical
  set hV := hC.hyp125.isElemAbelian
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hC.hyp125.pairFacts.le_normalizer hC.hyp125.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil V₀ V := hC.memL.1.le.trans hMS
  have hgstab : (g : G) ∈ stabTil V₀ V := hMS g.2
  have hKmem : L.map (MulAut.conj (g : G)).toMonoidHom ∈ UC22.conjSetOf D.M L :=
    ⟨(g : G), g.2, rfl⟩
  have hKC : L.map (MulAut.conj (g : G)).toMonoidHom ∈ calC D.M :=
    uc22p2214_calC_of_mem_conjSetOf hC.memL hKmem
  have hKne : barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom) ≠ ⊥ := by
    rw [TwelveTwentyThree.barSub_map_conj hV hLstab hgstab]
    intro hbot
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hker : (MulAut.conj
        ((actTil V₀ V hV) ⟨(g : G), hgstab⟩)).toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact (MulAut.conj _).injective
    rw [hker] at hbot
    exact hL1 (le_bot_iff.1 hbot)
  have hInL : Inputs1719.InGq (UC22.BarInf L) q := by
    obtain ⟨hr, hr2, t, m, f, hadm, hq, hmodel⟩ := hC.lie
    have hf : 0 < f := by
      have h := hadm.2.1
      omega
    exact Or.inl ⟨t, m, r, f, hr, hr2, hf, hq, hmodel⟩
  have hInK : Inputs1719.InGq (UC22.BarInf (L.map (MulAut.conj (g : G)).toMonoidHom)) q := by
    obtain ⟨e⟩ := uc22p20c_barInf_equiv_map L (g : G)
    exact InGq.of_mulEquiv hInL e
  have hInKq : Inputs1719.InGq
      (↥(barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom)) ⧸
        Subgroup.center ↥(barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom))) q := by
    obtain ⟨e⟩ := S17.barSub_centerQuot_equiv_barInf hC.hyp125 hKC hKne
    exact InGq.of_mulEquiv hInK e
  have hHq : CFSG.Open.IsQuasisimple
      ↥(barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom)) :=
    (barSub_mem_compBar_of_ne_bot hC.hyp125 hKC hKne).2.2
  have hodd : Odd (Nat.card (Subgroup.center
      ↥(barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom)))) :=
    S17.odd_center_barSub hC.hyp125 hKC hKne
  exact aCandidate_bounds_of_inGq h106 hHq hodd hInKq c

theorem bBar_conjClosure_le_of_candidate_bound_of_hyp125 {D : Data G} {V₀ V L : Subgroup G}
    (hp : Hyp125 D V₀ V) (hL : L ∈ calC D.M) (h77 : Inputs1719.W4Lem7_7)
    (hL1 : barSub V₀ V hp.isElemAbelian L ≠ ⊥) {m : ℕ}
    (hm : ∀ (g : ↥D.M) (n : ℕ), Nonempty (Inputs1719.ACandidate
      ↥(barSub V₀ V hp.isElemAbelian
        (L.map (MulAut.conj (g : G)).toMonoidHom)) n) → n ≤ m) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hp.isElemAbelian ≤ m := by
  classical
  set hV := hp.isElemAbelian
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hp.pairFacts.le_normalizer hp.pairFacts.le_normalizer₀
  have hKle : ∀ g : ↥D.M,
      L.map (MulAut.conj (g : G)).toMonoidHom ≤ stabTil V₀ V := by
    intro g x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact hMS (D.M.mul_mem (D.M.mul_mem g.2 (hL.1.le hl)) (D.M.inv_mem g.2))
  have hcl : UC22.conjClosure D.M L =
      ⨆ g : ↥D.M, L.map (MulAut.conj (g : G)).toMonoidHom :=
    uc22br4_conjClosure_eq D.M L
  have hbar : barSub V₀ V hV (UC22.conjClosure D.M L) =
      ⨆ g : ↥D.M, barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom) := by
    rw [hcl]
    exact barSub_iSup_of_le hV hKle
  let f : ↥D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun g => barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom)
  have hX : barSub V₀ V hV (UC22.conjClosure D.M L) ≤ ⨆ K ∈ Set.range f, K := by
    rw [hbar]
    exact le_of_eq (iSup_range (g := id) (f := f)).symm
  have hcomp : ∀ K ∈ Set.range f, CFSG.Open.IsComponentOf K (Mbar D.M V₀ V hV) := by
    rintro K ⟨g, rfl⟩
    have hKmem : L.map (MulAut.conj (g : G)).toMonoidHom ∈ UC22.conjSetOf D.M L :=
      ⟨(g : G), g.2, rfl⟩
    have hKC : L.map (MulAut.conj (g : G)).toMonoidHom ∈ calC D.M :=
      uc22p2214_calC_of_mem_conjSetOf hL hKmem
    have hKne : barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom) ≠ ⊥ := by
      rw [TwelveTwentyThree.barSub_map_conj hV (hL.1.le.trans hMS) (hMS g.2)]
      intro hbot
      rw [Subgroup.map_eq_bot_iff] at hbot
      have hker : (MulAut.conj
          ((actTil V₀ V hV) ⟨(g : G), hMS g.2⟩)).toMonoidHom.ker = ⊥ := by
        rw [MonoidHom.ker_eq_bot_iff]
        exact (MulAut.conj _).injective
      rw [hker] at hbot
      exact hL1 (le_bot_iff.1 hbot)
    exact barSub_mem_compBar_of_ne_bot hp hKC hKne
  have hbound : ∀ K ∈ Set.range f, ∀ n : ℕ,
      Nonempty (Inputs1719.ACandidate ↥K n) → n ≤ m := by
    rintro K ⟨g, rfl⟩ n hn
    exact hm g n hn
  show bParam (barSub V₀ V hV (UC22.conjClosure D.M L)) (Mbar D.M V₀ V hV) ≤ m
  exact bParam_le_of_isComponentOf
    (s15_Infra_vtil_sq_eq_one V₀ V hV) h77 hcomp hX hbound

theorem bBar_conjClosure_le_of_candidate_bound {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : S17.Ctx17_6 D V₀ V L r q) (h77 : Inputs1719.W4Lem7_7)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥)
    {m : ℕ}
    (hm : ∀ (g : ↥D.M) (n : ℕ), Nonempty (Inputs1719.ACandidate
      ↥(barSub V₀ V hC.hyp125.isElemAbelian
        (L.map (MulAut.conj (g : G)).toMonoidHom)) n) → n ≤ m) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ m :=
  bBar_conjClosure_le_of_candidate_bound_of_hyp125 hC.hyp125 hC.memL h77 hL1 hm

theorem bBar_conjClosure_le_two {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : S17.Ctx17_6 D V₀ V L r q) (h77 : Inputs1719.W4Lem7_7)
    (h106 : Inputs1719.W4Lem10_6Q)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥) (hq : 3 < q) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 2 := by
  refine bBar_conjClosure_le_of_candidate_bound hC h77 hL1 fun g n hn => ?_
  exact (aCandidate_barSub_conj_bounds hC h106 hL1 hn.some).2 hq

theorem bBar_conjClosure_le_one {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : S17.Ctx17_6 D V₀ V L r q) (h77 : Inputs1719.W4Lem7_7)
    (h106 : Inputs1719.W4Lem10_6Q)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥) (hq : 9 < q) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 1 := by
  refine bBar_conjClosure_le_of_candidate_bound hC h77 hL1 fun g n hn => ?_
  have hn1 : n = 1 := (aCandidate_barSub_conj_bounds hC h106 hL1 hn.some).1 hq
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
