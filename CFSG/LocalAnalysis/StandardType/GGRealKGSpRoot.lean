module

public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenForm
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenPlane
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenGen
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenSign
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenCompPair
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenCompSign
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenA
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
import CFSG.LocalAnalysis.StandardType.GGKGForkSpRow
import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.RealKGSpRoot

open Polynomial QuadraticMap Multiplicative CFSG.ClassicalGroups.Alternating
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.StandardType.OmNsRootGen CFSG.StandardType.SpNsRootGen

section Weyl

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

private theorem frameSwap_conj_omPlusRefl_false [NeZero p]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (Multiplicative.ofAdd 1)) = e d)
    {i j : Fin k} (hij : i < j) (f : Fin k → Multiplicative (ZMod p)) :
    (⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim h3⟩ :
        ↥(orthDerived Q)) * τ f *
      (⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim h3⟩ :
        ↥(orthDerived Q))⁻¹ =
      τ (omPlusRefl p (⟨(i, j), hij⟩, false) f) := by
  let sw : ↥(orthDerived Q) :=
    ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim h3⟩
  have hsw2 : sw * sw = 1 := Subtype.ext (frameSwap_mul_self hF hij.ne)
  have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
  refine conj_eq_of_mulSingle τ sw (omPlusRefl p (⟨(i, j), hij⟩, false)) ?_ f
  intro d
  rw [hswinv]
  by_cases hdi : d = i
  · subst d
    have hs : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle i (ofAdd 1)) =
        Pi.mulSingle j (ofAdd 1) := by
      rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
        Equiv.swap_apply_left]
    rw [hs, hτ j, hτ i]
    exact Subtype.ext (frameSwap_conj_left hF hij.ne)
  · by_cases hdj : d = j
    · subst d
      have hs : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle j (ofAdd 1)) =
          Pi.mulSingle i (ofAdd 1) := by
        rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
          Equiv.swap_apply_right]
      rw [hs, hτ i, hτ j]
      exact Subtype.ext (frameSwap_conj_right hF hij.ne)
    · have hs : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle d (ofAdd 1)) =
          Pi.mulSingle d (ofAdd 1) := by
        rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
          Equiv.swap_apply_of_ne_of_ne hdi hdj]
      rw [hs, hτ d]
      exact Subtype.ext (frameSwap_conj_of_ne hF hij.ne hdi hdj)

private theorem signedSwap_conj_omPlusRefl_true [NeZero p]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (Multiplicative.ofAdd 1)) = e d)
    {i j : Fin k} (hij : i < j) (f : Fin k → Multiplicative (ZMod p)) :
    (⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim h3 hF⟩ :
        ↥(orthDerived Q)) * τ f *
      (⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim h3 hF⟩ :
        ↥(orthDerived Q))⁻¹ =
      τ (omPlusRefl p (⟨(i, j), hij⟩, true) f) := by
  let sw : ↥(orthDerived Q) :=
    ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim h3 hF⟩
  have hsw2 : sw * sw = 1 := Subtype.ext (signedSwap_mul_self hF hij.ne)
  have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
  refine conj_eq_of_mulSingle τ sw (omPlusRefl p (⟨(i, j), hij⟩, true)) ?_ f
  intro d
  rw [hswinv]
  by_cases hdi : d = i
  · subst d
    have hs : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle i (ofAdd 1)) =
        (Pi.mulSingle j (ofAdd 1))⁻¹ := by
      rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
        SpCoord.permAut_mulSingle, Equiv.swap_apply_left, SpCoord.sgnAut_mulSingle_self,
        ← Pi.mulSingle_inv, SpCoord.sgnAut_mulSingle_of_ne hij.ne']
    rw [hs, map_inv, hτ j, hτ i]
    exact Subtype.ext (signedSwap_conj_left hF hij.ne)
  · by_cases hdj : d = j
    · subst d
      have hs : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle j (ofAdd 1)) =
          (Pi.mulSingle i (ofAdd 1))⁻¹ := by
        rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
          SpCoord.permAut_mulSingle, Equiv.swap_apply_right, SpCoord.sgnAut_mulSingle_of_ne
            hij.ne, SpCoord.sgnAut_mulSingle_self]
      rw [hs, map_inv, hτ i, hτ j]
      exact Subtype.ext (signedSwap_conj_right hF hij.ne)
    · have hs : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle d (ofAdd 1)) =
          Pi.mulSingle d (ofAdd 1) := by
        rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
          SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hdi hdj,
          SpCoord.sgnAut_mulSingle_of_ne hdj, SpCoord.sgnAut_mulSingle_of_ne hdi]
      rw [hs, hτ d]
      exact Subtype.ext (signedSwap_conj_of_ne hF hij.ne hdi hdj)

private theorem frameSwap_mem_pairBlock_false
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k} (hab : a ≠ b) :
    (⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim h3⟩ : ↥(orthDerived Q)) ∈
      pairBlock Q e t a b false := by
  let sw : ↥(orthDerived Q) :=
    ⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim h3⟩
  have hsw2 : sw * sw = 1 := Subtype.ext (frameSwap_mul_self hF hab)
  have h1 : sw * e a * sw = e b := Subtype.ext (frameSwap_conj_left hF hab)
  have h2 : sw * e b * sw = e a := Subtype.ext (frameSwap_conj_right hF hab)
  have hcomm : Commute (e a) (e b) := by
    have h := (isMulCommutative_iff.mp hF.isElemAbelian.1)
      (⟨e a, IsPlaneFrame.mem hF.toIsPlaneFrame a⟩ : ↥E)
        (⟨e b, IsPlaneFrame.mem hF.toIsPlaneFrame b⟩ : ↥E)
    exact Subtype.ext_iff.mp h
  have hy : sw * (e a * e b) * sw = e a * e b := by
    calc sw * (e a * e b) * sw
        = sw * e a * (sw * sw) * e b * sw := by rw [hsw2]; group
      _ = (sw * e a * sw) * (sw * e b * sw) := by group
      _ = e b * e a := by rw [h1, h2]
      _ = e a * e b := hcomm.eq.symm
  have hgy : sw * (e a * e b) = (e a * e b) * sw := by
    calc sw * (e a * e b)
        = sw * (e a * e b) * (sw * sw) := by rw [hsw2, mul_one]
      _ = (sw * (e a * e b) * sw) * sw := by group
      _ = (e a * e b) * sw := by rw [hy]
  refine mem_pairBlock_of_mul_self hQ hp hp2 hpq hF hab false ?_ ?_ hsw2
  · exact hgy
  · intro x hx
    exact frameSwap_apply_of_mem_polarPerp hF hx

private theorem signedSwap_mem_pairBlock_true
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k} (hab : a ≠ b) :
    (⟨signedSwap Q e u c t a b, signedSwap_mem_orthDerived hQ hdim h3 hF⟩ :
        ↥(orthDerived Q)) ∈ pairBlock Q e t a b true := by
  let sw : ↥(orthDerived Q) :=
    ⟨signedSwap Q e u c t a b, signedSwap_mem_orthDerived hQ hdim h3 hF⟩
  have hsw2 : sw * sw = 1 := Subtype.ext (signedSwap_mul_self hF hab)
  have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
  have h1 : sw * e a * sw = (e b)⁻¹ := Subtype.ext (signedSwap_conj_left hF hab)
  have h2 : sw * e b * sw = (e a)⁻¹ := Subtype.ext (signedSwap_conj_right hF hab)
  have h2' : sw * (e b)⁻¹ * sw = e a := by
    have h := congrArg Inv.inv h2
    rw [mul_inv_rev, mul_inv_rev, hswinv, inv_inv, ← mul_assoc] at h
    exact h
  have hcomm0 : Commute (e a) (e b) := by
    have h := (isMulCommutative_iff.mp hF.isElemAbelian.1)
      (⟨e a, IsPlaneFrame.mem hF.toIsPlaneFrame a⟩ : ↥E)
        (⟨e b, IsPlaneFrame.mem hF.toIsPlaneFrame b⟩ : ↥E)
    exact Subtype.ext_iff.mp h
  have hcomm : Commute (e a) ((e b)⁻¹) := hcomm0.inv_right
  have hy : sw * (e a * (e b)⁻¹) * sw = e a * (e b)⁻¹ := by
    calc sw * (e a * (e b)⁻¹) * sw
        = sw * e a * (sw * sw) * (e b)⁻¹ * sw := by rw [hsw2]; group
      _ = (sw * e a * sw) * (sw * (e b)⁻¹ * sw) := by group
      _ = (e b)⁻¹ * e a := by rw [h1, h2']
      _ = e a * (e b)⁻¹ := hcomm.eq.symm
  have hgy : sw * (e a * (e b)⁻¹) = (e a * (e b)⁻¹) * sw := by
    calc sw * (e a * (e b)⁻¹)
        = sw * (e a * (e b)⁻¹) * (sw * sw) := by rw [hsw2, mul_one]
      _ = (sw * (e a * (e b)⁻¹) * sw) * sw := by group
      _ = (e a * (e b)⁻¹) * sw := by rw [hy]
  refine mem_pairBlock_of_mul_self hQ hp hp2 hpq hF hab true ?_ ?_ hsw2
  · exact hgy
  · intro x hx
    exact signedSwap_apply_of_mem_polarPerp hF hx

end Weyl

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private theorem finite_gsp (B : LinearMap.BilinForm F V) : Finite (Gsp B) := by
  haveI : Finite V := Module.finite_of_finite F
  exact Finite.of_injective (fun g : Gsp B => g.app) fun g h hgh => by
    apply Subtype.ext
    apply Units.ext
    exact LinearMap.ext fun v => congrFun hgh v

theorem exists_signedTorusModel_gsp {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ)
    {E : Subgroup (Gsp B)} (hE : CFSG.Open.IsElemAbelian p E)
    (hsc : ∀ g : Gsp B, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (τ : (Fin ℓ → Multiplicative (ZMod p)) →* Gsp B) (w : OmPlusIdx ℓ ⊕ Fin ℓ → Gsp B)
      (S : OmPlusIdx ℓ ⊕ Fin ℓ → Subgroup (Gsp B)), Function.Injective τ ∧ τ.range = E ∧
      (∀ i f, w i * τ f * (w i)⁻¹ = τ (Sum.elim (omPlusRefl p) SpCoord.sgnAut i f)) ∧
      (∀ i, w i ∈ S i) ∧
      (∀ i, CFSG.Assembly.IsComponentOf (S i)
        (Subgroup.centralizer (τ '' {f | Sum.elim (omPlusRefl p) SpCoord.sgnAut i f = f}))) ∧
      ∀ i, p ∣ Nat.card (S i) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Gsp B) := finite_gsp B
  have hodd : Odd (Nat.card E) := by
    have hpg : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨Q, rfl, hQE⟩ := exists_invariant_quadraticForm hB hBn hodd
  have h3 : 3 ≤ ℓ := hℓ
  have h6 : 6 ≤ Module.finrank F V := by omega
  have hEΩ : E ≤ (omegaToGsp Q).range := fun g hg =>
    mem_range_omegaToGsp_of_pow_eq_one hBn h6 (hQE g hg) (hp.odd_of_ne_two hp2) (hE.2 g hg)
  obtain ⟨U, e, u, c, t, hC, htop⟩ := exists_coherentFrame_of_selfCentralizing_gsp hBn hp hp2 hpq
    hdim h3 hE hEΩ hsc fun W hW2 hWn => exists_orderOf_eq_mem_gspFixPerp hB hBn hW2 hWn hp hpq
  obtain ⟨τ, hτinj, hτrange, hτc, hact⟩ := exists_frameTorus hC.toIsPlaneFrame hp
  have hUn : ∀ a, (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) (U a)).Nondegenerate :=
    fun a => hC.nondeg a
  let w : OmPlusIdx ℓ ⊕ Fin ℓ → Gsp (QuadraticMap.polarBilin Q) := Sum.elim
    (fun x => omegaToGsp Q (cond x.2
      ⟨signedSwap Q e u c t x.1.1.1 x.1.1.2, signedSwap_mem_orthDerived hBn hdim h3 hC⟩
      ⟨frameSwap Q e u c t x.1.1.1 x.1.1.2, frameSwap_mem_orthDerived hBn hdim h3⟩))
    (frameSignSwap Q e u c t)
  let S : OmPlusIdx ℓ ⊕ Fin ℓ → Subgroup (Gsp (QuadraticMap.polarBilin Q)) := Sum.elim
    (fun x => (pairBlock Q e t x.1.1.1 x.1.1.2 x.2).map (omegaToGsp Q))
    (fun a => gspFixPerp (QuadraticMap.polarBilin Q) (U a))
  refine ⟨(omegaToGsp Q).comp τ, w, S, (omegaToGsp_injective Q).comp hτinj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hτrange]
    exact Subgroup.map_comap_eq_self hEΩ
  · rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | a) f
    · cases b
      · show omegaToGsp Q ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hBn hdim h3⟩ *
            omegaToGsp Q (τ f) *
            (omegaToGsp Q ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hBn hdim h3⟩)⁻¹ =
          omegaToGsp Q (τ (omPlusRefl p (⟨(i, j), hij⟩, false) f))
        rw [← map_inv, ← map_mul, ← map_mul,
          frameSwap_conj_omPlusRefl_false hBn hdim h3 hC τ hτc hij f]
      · show omegaToGsp Q ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hBn hdim h3 hC⟩ *
            omegaToGsp Q (τ f) *
            (omegaToGsp Q
              ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hBn hdim h3 hC⟩)⁻¹ =
          omegaToGsp Q (τ (omPlusRefl p (⟨(i, j), hij⟩, true) f))
        rw [← map_inv, ← map_mul, ← map_mul,
          signedSwap_conj_omPlusRefl_true hBn hdim h3 hC τ hτc hij f]
    · exact frameSignSwap_conj_torus hBn hp hC τ hτc a f
  · rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | a)
    · cases b
      · exact Subgroup.mem_map_of_mem _
          (frameSwap_mem_pairBlock_false hBn hp hp2 hpq hdim h3 hC hij.ne)
      · exact Subgroup.mem_map_of_mem _
          (signedSwap_mem_pairBlock_true hBn hp hp2 hpq hdim h3 hC hij.ne)
    · exact frameSignSwap_mem_gspFixPerp hC a
  · rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | a)
    · obtain ⟨z, hzX, hz⟩ := exists_fixedPointFree_mem_image_fix_omPlusRefl hBn hp
        hC.toIsPlaneFrame htop τ hact (⟨(i, j), hij⟩, b)
      show CFSG.Assembly.IsComponentOf ((pairBlock Q e t i j b).map (omegaToGsp Q))
        (Subgroup.centralizer
          (((omegaToGsp Q).comp τ) '' {f | omPlusRefl p (⟨(i, j), hij⟩, b) f = f}))
      rw [MonoidHom.coe_comp, Set.image_comp]
      refine isComponentOf_map_omegaToGsp hzX hz ?_
      cases b
      · exact isComponentOf_pairBlock hBn hp hp2 hpq hC hij.ne hF4 false
          (mem_image_fix_swap τ e hτc hij.ne) (image_fix_swap_subset τ e hτc hij.ne)
      · exact isComponentOf_pairBlock hBn hp hp2 hpq hC hij.ne hF4 true
          (mem_image_fix_omPlusRefl_true τ e hτc hij) (image_fix_omPlusRefl_true_subset τ e hτc hij)
    · show CFSG.Assembly.IsComponentOf (gspFixPerp (QuadraticMap.polarBilin Q) (U a))
        (Subgroup.centralizer (((omegaToGsp Q).comp τ) '' {f | SpCoord.sgnAut a f = f}))
      refine isComponentOf_gspFixPerp_frame hBn hC.toIsPlaneFrame htop a (fun b hba => ?_)
        (image_fix_sgnAut_subset hp hp2 ((omegaToGsp Q).comp τ) (fun b => omegaToGsp Q (e b))
          fun b => by rw [MonoidHom.comp_apply, hτc b])
        (isQuasisimple_gspFixPerp hB hBn (hC.finrank_eq a) (hUn a) hF4)
      refine ⟨Pi.mulSingle b (ofAdd 1), SpCoord.sgnAut_mulSingle_of_ne hba _, ?_⟩
      rw [MonoidHom.comp_apply, hτc b]
  · rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | a)
    · show p ∣ Nat.card ↥((pairBlock Q e t i j b).map (omegaToGsp Q))
      rw [Subgroup.card_map_of_injective (omegaToGsp_injective Q)]
      exact dvd_card_pairBlock hBn hp hp2 hpq hC hij.ne hF4 b
    · obtain ⟨g, hg, hord⟩ :=
        exists_orderOf_eq_mem_gspFixPerp hB hBn (hC.finrank_eq a) (hUn a) hp hpq
      show p ∣ Nat.card ↥(gspFixPerp (QuadraticMap.polarBilin Q) (U a))
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hg

private theorem card_coord (p k : ℕ) [NeZero p] :
    Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
  congr 1
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)

theorem ggKGRootDatum_gsp {B : LinearMap.BilinForm F V} (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F)
    {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ)
    (hsign : GGTorusSignedEltSC p (Gsp B))
    (hlayer : ∀ a : Gsp B, a ^ p = 1 → ∀ J : Subgroup (Gsp B), ⁅J, J⁆ = J →
      J ≤ Subgroup.centralizer ({a} : Set (Gsp B)) →
        J ≤ CFSG.Assembly.LargeEvenLayer (Subgroup.centralizer ({a} : Set (Gsp B))))
    (r : ℕ) : GGKGRootDatum p r (Gsp B) := by
  intro E hE h3 _ hsc
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨τ, w, S, hτ, hτE, hws, hwS, hcomp, hdvd⟩ :=
    exists_signedTorusModel_gsp hB hBn hp hp2 hpq hF4 hdim hℓ hE hsc
  obtain ⟨k, τ', hτ', hτ'E, -, -, hnorm⟩ := hsign E hE h3 hsc
  have hk : k = ℓ := by
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) =
        Nat.card (Fin ℓ → Multiplicative (ZMod p)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hτ').toEquiv,
        Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, hτ'E, hτE]
    rw [card_coord, card_coord] at h1
    exact Nat.pow_right_injective hp.two_le h1
  subst hk
  exact RealKGModelRoot.ggKGRootDatumAt_of_signedModel hp hp2 hτ hτE hτ' hτ'E hnorm w S hws hwS
    hcomp hdvd fun a ha J hJ hJa => hlayer a (hE.2 a ha) J hJ hJa

end CFSG.StandardType.RealKGSpRoot

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp CFSG.Yardstones.Md0ec50421ce4
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic

private theorem isChevSimple_of_mulEquiv' {r : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsChevSimple r B) : IsChevSimple r A := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem ggTorusRootSL2_spNonsplit
    {K : Type} [Field K] [Finite K] {n l p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF4 : 4 ≤ Nat.card K) (hK : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1) (hl2 : 2 ≤ l)
    {lab : LargeEvenLabel}
    (hmark : MarkedModel lab (LargeEvenProj (LargeEvenSpGroup K l))) :
    ∃ r, GGTorusLift p r (LargeEvenProj (LargeEvenSpGroup K l)) ∧
      GGTorusRootSL2 p r (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l)) := by
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  obtain ⟨hsignR, hcp⟩ := ggSpNonsplitTorusInput_holds K l p hl2 hp hpK
  refine ⟨0, TypeA.ggTorusLift_zero (ggKGSp_two_dvd_card (by omega)),
    ggTorusRootSL2_of_rootDatum hp (fun φ hφ _ => sp_I_subset_inn hφ) center_spProj_eq_bot hcp ?_⟩
  rcases (show l = 2 ∨ 3 ≤ l by omega) with rfl | hl3
  · intro E hE h3 _ _
    exfalso
    have hpF : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
    have hcard := SpJoin.card_le_pow_of_isElemAbelian hp hp2 hpF
      (E.map (spProjEquivSp (K := K) (m := 2)).toMonoidHom) (TableB.isElemAbelian_map hE _)
    rw [Subgroup.card_map_of_injective (spProjEquivSp (K := K) (m := 2)).injective] at hcard
    exact absurd (h3.trans hcard) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  · let α : LargeEvenProj (LargeEvenSpGroup K l) ≃* Gsp (spForm l K) :=
      spProjEquivSp.trans spEquiv
    have hchevR : IsChevSimple 2 (LargeEvenProj (LargeEvenSpGroup K l)) :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
        (isChevTwo_of_markedModel hmark)
    have hchev : IsChevSimple 2 (Gsp (spForm l K)) := isChevSimple_of_mulEquiv' α.symm hchevR
    have hS : IsSimpleGroup (Gsp (spForm l K)) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two hchev
    haveI : Finite (Gsp (spForm l K)) := Finite.of_equiv _ α.toEquiv
    refine ggKGRootDatum_of_mulEquiv α (RealKGSpRoot.ggKGRootDatum_gsp spForm_isAlt
      spForm_nondegenerate hp hp2 hpK hF4 finrank_spSpace hl3
      (ggTorusSignedEltSC_of_mulEquiv α.symm hsignR) (fun a hap J hJ hJa => ?_) 0)
    by_cases hJb : J = ⊥
    · rw [hJb]
      exact bot_le
    have hnc : ∃ a b : Gsp (spForm l K), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      apply hJb
      rw [← hJ, eq_bot_iff]
      exact Subgroup.commutator_le.mpr fun x _ y _ => by
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hcon x y
    exact ggKG_layer_of_chevSimple hS hnc hchev hp hp2 hap hJ hJa

theorem ggRealRootSL2On_spNonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .spNonsplit p lab := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp5, htag, hpn⟩ := hs
  have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab
    (by rcases htag with h | h <;> simp [h]) Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hM ⊢
    obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hp2 : p ≠ 2 := by omega
    have hF4 : 4 ≤ Nat.card K := by
      have := Nat.le_of_dvd (by omega) hpK
      omega
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusRootSL2_spNonsplit hp hp2 hF4 hK hpn hl2 hmark⟩

end CFSG.StandardType

end
