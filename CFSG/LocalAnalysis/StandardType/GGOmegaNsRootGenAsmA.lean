module

public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial QuadraticMap Multiplicative CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

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

theorem ggTorusModelAt_of_coherentFrame_of_iSup_pairBlock
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ) {k : ℕ} (hkℓ : k = ℓ)
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}
    {u : Fin k → V} {c t : F} (hF : IsCoherentFrame Q p U e E u c t)
    (hgen : ∀ x₀ : OmPlusIdx k,
      (⨆ (x : OmPlusIdx k) (_ : x ≠ x₀), pairBlock Q e t x.1.1.1 x.1.1.2 x.2) = ⊤) :
    GGTorusModelAt p E := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h3 : 3 ≤ ℓ := by omega
  obtain ⟨τ, hτinj, hτrange, hτc, _hact⟩ := exists_frameTorus hF.toIsPlaneFrame hp
  have hk4 : 4 ≤ k := by omega
  haveI : Nonempty (OmPlusIdx k) := by
    refine ⟨(⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩, false)⟩
    simp [Fin.lt_def]
  let w : OmPlusIdx k → ↥(orthDerived Q) := fun x =>
    cond x.2
      ⟨signedSwap Q e u c t x.1.1.1 x.1.1.2,
        signedSwap_mem_orthDerived hQ hdim h3 hF⟩
      ⟨frameSwap Q e u c t x.1.1.1 x.1.1.2, frameSwap_mem_orthDerived hQ hdim h3⟩
  refine ⟨k, τ, OmPlusIdx k, w, omPlusRefl p,
    fun x => pairBlock Q e t x.1.1.1 x.1.1.2 x.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · exact hτinj
  · exact hτrange
  · intro x f
    obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
    cases b
    · exact frameSwap_conj_omPlusRefl_false hQ hdim h3 hF τ hτc hij f
    · exact signedSwap_conj_omPlusRefl_true hQ hdim h3 hF τ hτc hij f
  · intro x
    exact omPlusRefl_mul_self x
  · intro x
    exact card_fix_omPlusRefl hp hp2 x
  · exact omPlusRefl_injective hp hp2
  · intro x
    obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
    cases b
    · exact frameSwap_mem_pairBlock_false hQ hp hp2 hpq hdim h3 hF hij.ne
    · exact signedSwap_mem_pairBlock_true hQ hp hp2 hpq hdim h3 hF hij.ne
  · intro x
    obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
    cases b
    · exact isComponentOf_pairBlock hQ hp hp2 hpq hF hij.ne hF4 false
        (mem_image_fix_swap τ e hτc hij.ne)
        (image_fix_swap_subset τ e hτc hij.ne)
    · exact isComponentOf_pairBlock hQ hp hp2 hpq hF hij.ne hF4 true
        (mem_image_fix_omPlusRefl_true τ e hτc hij)
        (image_fix_omPlusRefl_true_subset τ e hτc hij)
  · intro x
    obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
    cases b
    · exact dvd_card_pairBlock hQ hp hp2 hpq hF hij.ne hF4 false
    · exact dvd_card_pairBlock hQ hp hp2 hpq hF hij.ne hF4 true
  · exact hgen

end CFSG.StandardType.OmNsRootGen

end
