module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmCoordinates
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.Assembly.Defs
public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGTBJOmSupportCentralizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageNormB
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedMaps
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.Foundations.QuasisimpleMulEquiv
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

open Module Multiplicative QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalGroups.Orthogonal
open CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open scoped commutatorElement

namespace CFSG.StandardType

variable {G F V : Type} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {p r n : ℕ} [Fact p.Prime]
  {E : Subgroup (V ≃ₗ[F] V)} {Bs X : Subgroup G} {z : G}

private theorem quasisimple_image_of_orthChart
    (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank F V = 2 * (r + 1)) (hr3 : 3 ≤ r)
    (κ : ↥(orthDerived Q) →* G)
    (hκinj : Function.Injective κ) (hκrange : κ.range = X) :
    CFSG.IsQuasisimple ↥X ∧ Subgroup.center ↥X = ⊥ := by
  classical
  let eX : ↥(orthDerived Q) ≃* ↥X :=
    (MonoidHom.ofInjective hκinj).trans (MulEquiv.subgroupCongr hκrange)
  have hfull := OrthRestOdd.orthDerived_facts Q hQ (by omega : 6 ≤ finrank F V)
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv eX.symm hfull.1, ?_⟩
  rw [← Subgroup.map_center_eq eX, hfull.2.1, Subgroup.map_bot]

private theorem normalize_image_of_outside
    {H : Subgroup G} {t : G}
    (hX : CFSG.Assembly.IsComponentOf X
        (Subgroup.centralizer ({z} : Set G)) ∨
      CFSG.Assembly.LargeEvenPComponent p
        (Subgroup.centralizer ({z} : Set G)) X)
    (hzH : z ∈ H) (htX : t ∈ X) (htH : t ∈ H)
    (htord : orderOf t = p)
    (htCnot : t ∉ Subgroup.centralizer (X : Set G))
    (hJq : CFSG.Assembly.IsQuasisimple ↥X)
    (c : G) (hcH : c ∈ Subgroup.centralizer (H : Set G)) :
    c ∈ Subgroup.normalizer (X : Set G) := by
  have hge : c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hcH z hzH).symm
  have hct : c * t = t * c :=
    (Subgroup.mem_centralizer_iff.mp hcH t htH).symm
  rcases hX with hcomp | hpcomp
  · exact ggMem_normalizer_of_component hcomp htX htCnot
      (Subgroup.le_normalizer hge) hct
  · have hpJ : p ∣ Nat.card ↥X := by
      have h := Subgroup.orderOf_dvd_natCard X htX
      rwa [htord] at h
    exact ggMem_normalizer_of_pComponent hpcomp le_rfl hJq hpJ htX htCnot hge hct

theorem ggTBJOm_smallBlocks_eq_ggBlockComm
    {G F V : Type} [Group G] [Finite G]
    [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} {p r n : ℕ} [Fact p.Prime]
    {E : Subgroup (V ≃ₗ[F] V)} {Bs X : Subgroup G} {z : G}
    (hp2 : p ≠ 2) (hn : 4 ≤ n) (hrn : r + 1 = n)
    (Δ : OrthTorus.TBJOmData Q p E r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hE : E ≤ orthDerived Q)
    (hdim : finrank F V = 2 * (r + 1))
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hrow : p ∣ Nat.card F - 1 ∨ Odd r ∧ p ∣ Nat.card F + 1)
    (κ : ↥(orthDerived Q) →* G)
    (hκinj : Function.Injective κ) (hκrange : κ.range = X)
    (Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘκ : ∀ w c,
      ((Θ (w, c) : ↥Bs) : G) = κ (Δ.τΩ hE w) * (c : G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hz : z ∈ Bs ⊓ Subgroup.centralizer (X : Set G))
    (hX : CFSG.Assembly.IsComponentOf X
        (Subgroup.centralizer ({z} : Set G)) ∨
      CFSG.Assembly.LargeEvenPComponent p
        (Subgroup.centralizer ({z} : Set G)) X) :
    ∃ ι : Fin r ≃ {i : Fin n // i ≠ i0},
      (∀ (b : ↥Bs) (a : Fin r),
        (Θ.symm b).1 a = 1 ↔ eta b (ι a).val = 1) ∧
      ∀ S : Finset (Fin r), S.Nonempty → S.card ≤ 2 →
        ((supportedDerived Q (Δ.originalAnchor ⊔ S.sup Δ.F.U)).subgroupOf
          (orthDerived Q)).map κ =
        ggBlockComm Bs eta ((fun a => (ι a).val) '' (S : Set (Fin r))) := by
  classical
  have hr3 : 3 ≤ r := by omega
  have hr1 : 1 ≤ r := by omega
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hτΩinj : Function.Injective (Δ.τΩ hE) := by
    intro a b h
    apply Δ.τ_inj
    have h' := congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) h
    simpa [OrthTorus.TBJOmData.τΩ] using h'
  obtain ⟨ι, hι⟩ := exists_axisEquiv_coord_eq_one_of_bCoordinateBlock_eq
    (Fact.out : p.Prime) hp2 hn hrn Θ eta i0 hcoord
  have hdata := Δ.inactive_plane_of_minus hp2 hQ hE hr1 hdim hminus hrow
  have hWS : IsCompl Δ.originalAnchor Δ.originalActive := by
    simpa only [OrthTorus.TBJOmData.originalAnchor, OrthTorus.TBJOmData.originalActive]
      using hdata.2.2.2.1
  let o : Fin r := ⟨0, by omega⟩
  refine ⟨ι, hι, ?_⟩
  intro S hS hS2
  have hlt : S.card < (Finset.univ : Finset (Fin r)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let labels : Set (Fin n) := (fun a => (ι a).val) '' (S : Set (Fin r))
  let H : Subgroup G := ggBsCoordZeroOn Bs eta labels
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let R0 : Subgroup (V ≃ₗ[F] V) := supportedDerived Q (Δ.originalAnchor ⊔ S.sup Δ.F.U)
  let RΩ : Subgroup ↥(orthDerived Q) := R0.subgroupOf (orthDerived Q)
  let R : Subgroup G := RΩ.map κ
  let A : Subgroup G := Bs ⊓ R
  let D : Subgroup G := X ⊓ C
  let N : Subgroup G := ⁅D, D⁆
  have hsmall := Δ.smallSupport_facts hp2 hr3 hQ hE hdim hminus hrow hS hS2
  have hreg : (polarBilin (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)).Nondegenerate :=
    hsmall.1
  have hdict : ∀ b : ↥Bs, (b : G) ∈ H ↔ ∀ a ∈ S, (Θ.symm b).1 a = 1 := by
    intro b
    change (b : G) ∈ ggBsCoordZeroOn Bs eta labels ↔ _
    rw [mem_ggBsCoordZeroOn]
    constructor
    · rintro ⟨hb, hzero⟩ a ha
      have hb' : (⟨(b : G), hb⟩ : ↥Bs) = b := Subtype.ext rfl
      have h := hzero (ι a).val ⟨a, ha, rfl⟩
      rw [hb'] at h
      exact (hι b a).mpr h
    · rintro h
      refine ⟨b.2, ?_⟩
      intro j hj
      rw [Set.mem_image] at hj
      obtain ⟨a, ha, rfl⟩ := hj
      exact (hι b a).mp (h a ha)
  have hTorus_mem_Bs : ∀ w : Fin r → Multiplicative (ZMod p),
      κ (Δ.τΩ hE w) ∈ Bs := by
    intro w
    have h := (hΘκ w (1 : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))).symm
    rw [show κ (Δ.τΩ hE w) = ((Θ (w, 1) : ↥Bs) : G) by
      simpa using h]
    exact (Θ (w, 1)).2
  have hTorus_mem_H : ∀ w : Fin r → Multiplicative (ZMod p),
      (∀ a ∈ S, w a = 1) → κ (Δ.τΩ hE w) ∈ H := by
    intro w hw
    have hh : (((Θ (w, 1) : ↥Bs) : G)) ∈ H := by
      rw [hdict]
      intro a ha
      simpa using hw a ha
    rw [show κ (Δ.τΩ hE w) = ((Θ (w, 1) : ↥Bs) : G) by
      simpa using (hΘκ w (1 : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))).symm]
    exact hh
  have hzH : z ∈ H := by
    let cz : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := ⟨z, hz⟩
    have hzeq : ((Θ (1, cz) : ↥Bs) : G) = z := by
      simpa using hΘκ (1 : Fin r → Multiplicative (ZMod p)) cz
    rw [← hzeq]
    rw [hdict]
    intro a ha
    simp
  let v : Fin r → Multiplicative (ZMod p) := Pi.mulSingle d (ofAdd (1 : ZMod p))
  let t : G := κ (Δ.τΩ hE v)
  have hof_ne : (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
    intro h
    have h10 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (by simpa using h)
    exact one_ne_zero h10
  have hT_ne : ∀ (w : Fin r → Multiplicative (ZMod p)) (i : Fin r),
      w i = Multiplicative.ofAdd (1 : ZMod p) → κ (Δ.τΩ hE w) ≠ 1 := by
    intro w i hwi h1
    have hτ : Δ.τΩ hE w = 1 := hκinj (by simpa using h1)
    have hGL : ((Δ.τΩ hE w : ↥(orthDerived Q)) : V ≃ₗ[F] V) = 1 := by
      simpa using congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) hτ
    have hw1 : w = 1 := Δ.τ_inj (by simpa [OrthTorus.TBJOmData.τΩ] using hGL)
    have h1i : w i = 1 := by rw [hw1]; rfl
    exact hof_ne (hwi.symm.trans h1i)
  have htX : t ∈ X := by
    rw [← hκrange]
    exact ⟨Δ.τΩ hE v, rfl⟩
  have htH : t ∈ H := by
    exact hTorus_mem_H v (by
      intro a ha
      exact Pi.mulSingle_eq_of_ne' (fun hda : d = a => hd (hda ▸ ha)) _)
  have htne : t ≠ 1 := by
    exact hT_ne v d (by simp [v])
  have htorder : orderOf t = p := by
    calc orderOf t = orderOf (Δ.τΩ hE v) := orderOf_injective κ hκinj (Δ.τΩ hE v)
      _ = orderOf v := orderOf_injective (Δ.τΩ hE) hτΩinj v
      _ = p := by
          rw [show v = Pi.mulSingle d (ofAdd (1 : ZMod p)) from rfl,
            orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hqX := quasisimple_image_of_orthChart hQ hdim hr3 κ hκinj hκrange
  have hJq_native : CFSG.IsQuasisimple ↥X := hqX.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥X :=
    ⟨Group.isPerfect_def.mp hJq_native.1, hJq_native.2.1⟩
  have hcenterX : Subgroup.center ↥X = ⊥ := hqX.2
  have htCnot : t ∉ Subgroup.centralizer (X : Set G) := by
    intro htC
    have hmemcenter : (⟨t, htX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp htC (y : G) y.2
    have h1 : (⟨t, htX⟩ : ↥X) = 1 := by
      simpa [hcenterX] using hmemcenter
    exact htne (by simpa using congrArg Subtype.val h1)
  have hgen : ∀ e ∈ Bs, ∃ h ∈ H, ∃ w ∈ A, e = h * w := by
    intro e he
    let b : ↥Bs := ⟨e, he⟩
    let w : Fin r → Multiplicative (ZMod p) := (Θ.symm b).1
    let c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := (Θ.symm b).2
    let wOut : Fin r → Multiplicative (ZMod p) := fun i => if i ∈ S then 1 else w i
    let wIn : Fin r → Multiplicative (ZMod p) := fun i => if i ∈ S then w i else 1
    have hw_split : wOut * wIn = w := by
      funext i
      by_cases hi : i ∈ S <;> simp [wOut, wIn, hi]
    have hprod : (wOut, c) * (wIn, 1) = (w, c) := by
      apply Prod.ext
      · exact hw_split
      · simp
    have hb_eq : ((Θ (w, c) : ↥Bs) : G) = e := by
      have h1 : (Θ (w, c) : ↥Bs) = b := by
        dsimp [w, c]
        exact Θ.apply_symm_apply b
      simpa [b] using congrArg Subtype.val h1
    have hhH : ((Θ (wOut, c) : ↥Bs) : G) ∈ H := by
      rw [hdict]
      intro a ha
      simp [wOut, ha]
    have hwIn_supp : ∀ i, i ∉ S → wIn i = 1 := by
      intro i hi
      simp [wIn, hi]
    have hmemR0 : ((Δ.τΩ hE wIn : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ R0 := by
      have h := Δ.tau_mem_supportedDerived_of_smallSupport hp2 hr3 hQ hE hdim hminus hrow
        hS hS2 hwIn_supp
      simpa [R0, OrthTorus.TBJOmData.τΩ] using h
    have hκR : κ (Δ.τΩ hE wIn) ∈ R := by
      change κ (Δ.τΩ hE wIn) ∈ RΩ.map κ
      exact Subgroup.mem_map.mpr ⟨Δ.τΩ hE wIn, hmemR0, rfl⟩
    have haR : ((Θ (wIn, 1) : ↥Bs) : G) ∈ R := by
      rw [show ((Θ (wIn, 1) : ↥Bs) : G) = κ (Δ.τΩ hE wIn) by
        simpa using hΘκ wIn (1 : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))]
      exact hκR
    have haA : ((Θ (wIn, 1) : ↥Bs) : G) ∈ A := ⟨(Θ (wIn, 1)).2, haR⟩
    refine ⟨((Θ (wOut, c) : ↥Bs) : G), hhH,
      ((Θ (wIn, 1) : ↥Bs) : G), haA, ?_⟩
    calc e = ((Θ (w, c) : ↥Bs) : G) := hb_eq.symm
      _ = ((Θ ((wOut, c) * (wIn, 1)) : ↥Bs) : G) := by rw [hprod]
      _ = ((Θ (wOut, c) : ↥Bs) : G) * ((Θ (wIn, 1) : ↥Bs) : G) := by
          rw [map_mul]
          rfl
  have hSkeep : S.Nonempty := hS
  obtain ⟨a0, ha0⟩ := hS
  let v0 : Fin r → Multiplicative (ZMod p) := Pi.mulSingle a0 (ofAdd (1 : ZMod p))
  have hv0supp : ∀ i, i ∉ S → v0 i = 1 := by
    intro i hi
    exact Pi.mulSingle_eq_of_ne' (fun h : a0 = i => hi (h ▸ ha0)) _
  have hv0R0 : ((Δ.τΩ hE v0 : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ R0 := by
    have h := Δ.tau_mem_supportedDerived_of_smallSupport hp2 hr3 hQ hE hdim hminus hrow
      hSkeep hS2 hv0supp
    simpa [R0, OrthTorus.TBJOmData.τΩ] using h
  have hv0R : κ (Δ.τΩ hE v0) ∈ R := by
    change κ (Δ.τΩ hE v0) ∈ RΩ.map κ
    exact Subgroup.mem_map.mpr ⟨Δ.τΩ hE v0, hv0R0, rfl⟩
  have hv0A : κ (Δ.τΩ hE v0) ∈ A := ⟨hTorus_mem_Bs v0, hv0R⟩
  have hv0ne : κ (Δ.τΩ hE v0) ≠ 1 := hT_ne v0 a0 (by simp [v0])
  have hAne : A ≠ ⊥ := by
    intro hbot
    exact hv0ne (Subgroup.mem_bot.mp (hbot ▸ hv0A))
  let eR0 : ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) ≃* R0 :=
    orthDerivedSupportedEquiv hreg
  let hR0Ω : R0 ≤ orthDerived Q := supportedDerived_le_orthDerived_of_regular hreg
  let eRΩ : R0 ≃* RΩ := (Subgroup.subgroupOfEquivOfLe hR0Ω).symm
  let eMap : RΩ ≃* ↥(RΩ.map κ) := Subgroup.equivMapOfInjective RΩ κ hκinj
  let eR : ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) ≃*
      ↥(RΩ.map κ) := (eR0.trans eRΩ).trans eMap
  have hsimpleR : IsSimpleGroup ↥R := by
    haveI : IsSimpleGroup
        ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) :=
      hsmall.2.2.1
    change IsSimpleGroup ↥(RΩ.map κ)
    exact eR.symm.isSimpleGroup
  have hperfR : Group.IsPerfect ↥R := by
    haveI : Group.IsPerfect
        ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) :=
      hsmall.2.2.2.1
    change Group.IsPerfect ↥(RΩ.map κ)
    exact Group.IsPerfect.ofSurjective (f := eR.toMonoidHom) eR.surjective
  haveI : IsSimpleGroup ↥R := hsimpleR
  haveI : Group.IsPerfect ↥R := hperfR
  have hcenterR : Subgroup.center ↥R = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥R)
  have hRC : R ≤ Subgroup.centralizer (H : Set G) := by
    intro r hr
    change r ∈ RΩ.map κ at hr
    obtain ⟨u, huRΩ, rfl⟩ := Subgroup.mem_map.mp hr
    have huR0 : (u : V ≃ₗ[F] V) ∈ R0 := huRΩ
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    change h ∈ ggBsCoordZeroOn Bs eta labels at hh
    have hb : h ∈ Bs := ggBsCoordZeroOn_le Bs eta labels hh
    let hB : ↥Bs := ⟨h, hb⟩
    let w : Fin r → Multiplicative (ZMod p) := (Θ.symm hB).1
    let c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := (Θ.symm hB).2
    have hw0 : ∀ i ∈ S, w i = 1 := by
      have h := (hdict hB).mp hh
      intro i hi
      exact h i hi
    have hhG : (h : G) = κ (Δ.τΩ hE w) * (c : G) := by
      have h1 : (Θ (w, c) : ↥Bs) = hB := by
        dsimp [w, c]
        exact Θ.apply_symm_apply hB
      have h2 := hΘκ w c
      rw [h1] at h2
      exact h2
    have hcX : (c : G) ∈ Subgroup.centralizer (X : Set G) := c.2.2
    have hκuX : κ u ∈ X := by
      rw [← hκrange]
      exact ⟨u, rfl⟩
    have hcu : Commute (κ u) (c : G) := by
      rw [commute_iff_eq]
      exact Subgroup.mem_centralizer_iff.mp hcX (κ u) hκuX
    have htorus : Commute (Δ.τ w) ((u : V ≃ₗ[F] V)) :=
      Δ.commute_supportedDerived_of_zeroOn hQ hE o hWS S hw0
        ((u : V ≃ₗ[F] V)) huR0
    have hcommΩ : Commute (Δ.τΩ hE w) u := by
      rw [commute_iff_eq]
      apply Subtype.ext
      simpa [OrthTorus.TBJOmData.τΩ] using htorus.eq
    have hcommG : Commute (κ (Δ.τΩ hE w)) (κ u) := by
      rw [commute_iff_eq]
      rw [← map_mul, ← map_mul, hcommΩ.eq]
    have hfull : Commute (κ u) (h : G) := by
      rw [hhG]
      exact hcommG.symm.mul_right hcu
    exact hfull.symm.eq
  have hCnormX : C ≤ Subgroup.normalizer (X : Set G) := by
    intro c hc
    exact normalize_image_of_outside (H := H) (t := t) hX hzH htX htH htorder
      htCnot hJq c hc
  have hCnormD : C ≤ Subgroup.normalizer (D : Set G) := by
    change C ≤ Subgroup.normalizer ((X ⊓ C : Subgroup G) : Set G)
    exact (le_inf hCnormX C.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCnormN : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    have hcD := hCnormD hc
    change c ∈ Subgroup.normalizer (⁅D, D⁆ : Subgroup G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hcD ⊢
    rw [Subgroup.map_commutator, hcD]
  have hR_le_X : R ≤ X := by
    intro r hr
    change r ∈ RΩ.map κ at hr
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hr
    rw [← hκrange]
    exact ⟨u, rfl⟩
  have hR_le_D : R ≤ D := by
    intro r hr
    exact ⟨hR_le_X hr, hRC hr⟩
  have hRN : R ≤ N := by
    calc R = ⁅R, R⁆ := (Subgroup.commutator_eq_self (H := R)).symm
      _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hR_le_D hR_le_D
  have hAN : A ≤ N := (inf_le_right : A ≤ R).trans hRN
  have hNR : N ≤ R := by
    let Dκ : Subgroup ↥(orthDerived Q) := D.comap κ
    let Dgl : Subgroup (V ≃ₗ[F] V) := Dκ.map (orthDerived Q).subtype
    have hDleRange : D ≤ κ.range := by
      rw [hκrange]
      exact inf_le_left
    have hmapD : Dκ.map κ = D := Subgroup.map_comap_eq_self hDleRange
    have hDgl_le : Dgl ≤ orthDerived Q ⊓ Subgroup.centralizer
        ({g : V ≃ₗ[F] V | ∃ i ∈ Sᶜ,
          g = Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))}) := by
      intro x hx
      change x ∈ Dκ.map (orthDerived Q).subtype at hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have hκuMap : κ u ∈ Dκ.map κ := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      have hκuD : κ u ∈ D := by rwa [hmapD] at hκuMap
      have hκuC : κ u ∈ C := hκuD.2
      have hcomm_i : ∀ i ∈ Sᶜ, Commute ((u : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) := by
        intro i hi
        have hiS : i ∉ S := Finset.mem_compl.mp hi
        have hmemH : κ (Δ.τΩ hE (Pi.mulSingle i (ofAdd (1 : ZMod p)))) ∈ H :=
          hTorus_mem_H _ (by
            intro a ha
            exact Pi.mulSingle_eq_of_ne' (fun hia : i = a => hiS (hia ▸ ha)) _)
        have hcommG : Commute (κ u)
            (κ (Δ.τΩ hE (Pi.mulSingle i (ofAdd (1 : ZMod p))))) :=
          (Subgroup.mem_centralizer_iff.mp hκuC _ hmemH).symm
        have hcommΩ : Commute u
            (Δ.τΩ hE (Pi.mulSingle i (ofAdd (1 : ZMod p)))) := by
          rw [commute_iff_eq]
          apply hκinj
          rw [map_mul, map_mul]
          exact hcommG.eq
        rw [commute_iff_eq]
        simpa [OrthTorus.TBJOmData.τΩ] using
          congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) hcommΩ.eq
      refine ⟨Subgroup.map_subtype_le Dκ (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [Set.mem_setOf_eq] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact (hcomm_i i hi).symm.eq
    have hupper : ⁅Dgl, Dgl⁆ ≤ R0 := by
      change ⁅Dgl, Dgl⁆ ≤ supportedDerived Q (Δ.originalAnchor ⊔ S.sup Δ.F.U)
      exact (Subgroup.commutator_mono hDgl_le hDgl_le).trans
        (Δ.commutator_centralizer_le_supportedDerived_originalAnchor_sup hQ hE o hWS S)
    have hDκ_le : ⁅Dκ, Dκ⁆ ≤ RΩ := by
      intro u hu
      have hsub : ((u : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ ⁅Dgl, Dgl⁆ := by
        have h1 : ((u : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
            (⁅Dκ, Dκ⁆).map (orthDerived Q).subtype :=
          Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
        rwa [Subgroup.map_commutator] at h1
      exact hupper hsub
    have hNmap : N = (⁅Dκ, Dκ⁆).map κ := by
      change ⁅D, D⁆ = (⁅Dκ, Dκ⁆).map κ
      rw [← hmapD, ← Subgroup.map_commutator]
    rw [hNmap]
    exact Subgroup.map_mono hDκ_le
  have hRW : R ≤ ⁅R, A⁆ :=
    le_commutator_of_isSimpleGroup_of_ne_bot (R := R) (W := A)
      inf_le_right hcenterR hAne
  have hfinal : ⁅Subgroup.centralizer (H : Set G), Bs⁆ = R :=
    ggCommutator_centralizer_eq_of_mul (E := Bs) (H := H) (W := A)
      (N := N) (R := R) hgen inf_le_left hCnormN hAN hNR hRC hRW
  change R = ggBlockComm Bs eta labels
  rw [show ggBlockComm Bs eta labels =
      ⁅Subgroup.centralizer (H : Set G), Bs⁆ from rfl]
  exact hfinal.symm

end CFSG.StandardType

end
