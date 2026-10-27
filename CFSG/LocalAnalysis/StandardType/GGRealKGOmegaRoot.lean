module

public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCompSgn
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
import CFSG.RankThree.PartOne.S11d.OrthCaseH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RealKGOmega

open Module QuadraticMap Multiplicative SpCoord CFSG.Assembly
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Blocks

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

private theorem pair_model (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ)
    (h3 : 3 ≤ ℓ) (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d) (x : OmPlusIdx k) :
    ∃ (w : ↥(orthDerived Q)) (S : Subgroup ↥(orthDerived Q)),
      (∀ f, w * τ f * w⁻¹ = τ (omPlusRefl p x f)) ∧ w ∈ S ∧
      IsComponentOf S (Subgroup.centralizer (τ '' {f | omPlusRefl p x f = f})) ∧
      p ∣ Nat.card S := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcomm0 : ∀ a b, Commute (e a) (e b) := fun a b => by
    have h := (isMulCommutative_iff.mp hF.isElemAbelian.1)
      (⟨e a, IsPlaneFrame.mem hF.toIsPlaneFrame a⟩ : ↥E)
        (⟨e b, IsPlaneFrame.mem hF.toIsPlaneFrame b⟩ : ↥E)
    exact Subtype.ext_iff.mp h
  obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
  cases b
  · let sw : ↥(orthDerived Q) :=
      ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim h3⟩
    have hsw2 : sw * sw = 1 := Subtype.ext (frameSwap_mul_self hF hij.ne)
    have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
    have h1 : sw * e i * sw = e j := Subtype.ext (frameSwap_conj_left hF hij.ne)
    have h2 : sw * e j * sw = e i := Subtype.ext (frameSwap_conj_right hF hij.ne)
    refine ⟨sw, pairBlock Q e t i j false, ?_, ?_, ?_, ?_⟩
    · refine conj_eq_of_mulSingle τ sw (omPlusRefl p (⟨(i, j), hij⟩, false)) (fun d => ?_)
      rw [hswinv]
      by_cases hdi : d = i
      · subst d
        have hs : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle i (ofAdd 1)) =
            Pi.mulSingle j (ofAdd 1) := by
          rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
            Equiv.swap_apply_left]
        rw [hs, hτ j, hτ i]
        exact h1
      · by_cases hdj : d = j
        · subst d
          have hs : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle j (ofAdd 1)) =
              Pi.mulSingle i (ofAdd 1) := by
            rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
              Equiv.swap_apply_right]
          rw [hs, hτ i, hτ j]
          exact h2
        · have hs : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle d (ofAdd 1)) =
              Pi.mulSingle d (ofAdd 1) := by
            rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
              Equiv.swap_apply_of_ne_of_ne hdi hdj]
          rw [hs, hτ d]
          exact Subtype.ext (frameSwap_conj_of_ne hF hij.ne hdi hdj)
    · have hy : sw * (e i * e j) * sw = e i * e j := by
        calc sw * (e i * e j) * sw
            = sw * e i * (sw * sw) * e j * sw := by rw [hsw2]; group
          _ = (sw * e i * sw) * (sw * e j * sw) := by group
          _ = e j * e i := by rw [h1, h2]
          _ = e i * e j := (hcomm0 i j).eq.symm
      have hgy : sw * (e i * e j) = (e i * e j) * sw := by
        calc sw * (e i * e j)
            = sw * (e i * e j) * (sw * sw) := by rw [hsw2, mul_one]
          _ = (sw * (e i * e j) * sw) * sw := by group
          _ = (e i * e j) * sw := by rw [hy]
      exact mem_pairBlock_of_mul_self hQ hp hp2 hpq hF hij.ne false hgy
        (fun y hy => frameSwap_apply_of_mem_polarPerp hF hy) hsw2
    · exact isComponentOf_pairBlock hQ hp hp2 hpq hF hij.ne hF4 false
        (mem_image_fix_swap τ e hτ hij.ne) (image_fix_swap_subset τ e hτ hij.ne)
    · exact dvd_card_pairBlock hQ hp hp2 hpq hF hij.ne hF4 false
  · let sw : ↥(orthDerived Q) :=
      ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim h3 hF⟩
    have hsw2 : sw * sw = 1 := Subtype.ext (signedSwap_mul_self hF hij.ne)
    have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
    have h1 : sw * e i * sw = (e j)⁻¹ := Subtype.ext (signedSwap_conj_left hF hij.ne)
    have h2 : sw * e j * sw = (e i)⁻¹ := Subtype.ext (signedSwap_conj_right hF hij.ne)
    refine ⟨sw, pairBlock Q e t i j true, ?_, ?_, ?_, ?_⟩
    · refine conj_eq_of_mulSingle τ sw (omPlusRefl p (⟨(i, j), hij⟩, true)) (fun d => ?_)
      rw [hswinv]
      by_cases hdi : d = i
      · subst d
        have hs : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle i (ofAdd 1)) =
            (Pi.mulSingle j (ofAdd 1))⁻¹ := by
          rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
            SpCoord.permAut_mulSingle, Equiv.swap_apply_left, SpCoord.sgnAut_mulSingle_self,
            ← Pi.mulSingle_inv, SpCoord.sgnAut_mulSingle_of_ne hij.ne']
        rw [hs, map_inv, hτ j, hτ i]
        exact h1
      · by_cases hdj : d = j
        · subst d
          have hs : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle j (ofAdd 1)) =
              (Pi.mulSingle i (ofAdd 1))⁻¹ := by
            rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply,
              MulAut.mul_apply, SpCoord.permAut_mulSingle, Equiv.swap_apply_right,
              SpCoord.sgnAut_mulSingle_of_ne hij.ne, SpCoord.sgnAut_mulSingle_self]
          rw [hs, map_inv, hτ i, hτ j]
          exact h2
        · have hs : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle d (ofAdd 1)) =
              Pi.mulSingle d (ofAdd 1) := by
            rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply,
              MulAut.mul_apply, SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hdi hdj,
              SpCoord.sgnAut_mulSingle_of_ne hdj, SpCoord.sgnAut_mulSingle_of_ne hdi]
          rw [hs, hτ d]
          exact Subtype.ext (signedSwap_conj_of_ne hF hij.ne hdi hdj)
    · have h2' : sw * (e j)⁻¹ * sw = e i := by
        have h := congrArg Inv.inv h2
        rw [mul_inv_rev, mul_inv_rev, hswinv, inv_inv, ← mul_assoc] at h
        exact h
      have hcomm : Commute (e i) ((e j)⁻¹) := (hcomm0 i j).inv_right
      have hy : sw * (e i * (e j)⁻¹) * sw = e i * (e j)⁻¹ := by
        calc sw * (e i * (e j)⁻¹) * sw
            = sw * e i * (sw * sw) * (e j)⁻¹ * sw := by rw [hsw2]; group
          _ = (sw * e i * sw) * (sw * (e j)⁻¹ * sw) := by group
          _ = (e j)⁻¹ * e i := by rw [h1, h2']
          _ = e i * (e j)⁻¹ := hcomm.eq.symm
      have hgy : sw * (e i * (e j)⁻¹) = (e i * (e j)⁻¹) * sw := by
        calc sw * (e i * (e j)⁻¹)
            = sw * (e i * (e j)⁻¹) * (sw * sw) := by rw [hsw2, mul_one]
          _ = (sw * (e i * (e j)⁻¹) * sw) * sw := by group
          _ = (e i * (e j)⁻¹) * sw := by rw [hy]
      exact mem_pairBlock_of_mul_self hQ hp hp2 hpq hF hij.ne true hgy
        (fun y hy => signedSwap_apply_of_mem_polarPerp hF hy) hsw2
    · exact isComponentOf_pairBlock hQ hp hp2 hpq hF hij.ne hF4 true
        (mem_image_fix_omPlusRefl_true τ e hτ hij) (image_fix_omPlusRefl_true_subset τ e hτ hij)
    · exact dvd_card_pairBlock hQ hp hp2 hpq hF hij.ne hF4 true

private theorem finrank_perp_eq_two {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ) (hkℓ : k + 1 = ℓ)
    (hS : IsPlaneSystem Q U) : finrank F (polarPerp Q (⨆ j, U j)) = 2 := by
  have hsum : finrank F ↥(⨆ j, U j) = 2 * k := by
    have h := hS.finrank_biSup (Finset.univ : Finset (Fin k))
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [show (⨆ j, U j : Submodule F V) = ⨆ j ∈ (Finset.univ : Finset (Fin k)), U j from by
      rw [← Finset.sup_eq_iSup, Finset.sup_univ_eq_iSup]]
    exact h
  have hcompl : IsCompl (⨆ j, U j) (polarPerp Q (⨆ j, U j)) := hS.isCompl_iSup
  have hV : finrank F ↥(⨆ j, U j) + finrank F (polarPerp Q (⨆ j, U j)) = finrank F V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (s := (⨆ j, U j : Submodule F V)) (t := polarPerp Q (⨆ j, U j))
    rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h
    exact h.symm
  omega

private theorem sign_model (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsCoherentFrame Q p U e E u c t)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)} (hτrange : τ.range = E)
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d)
    (hact : ∀ f c, ∀ x ∈ U c, ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      (((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (toAdd (f c)).val) x)
    (hW2 : finrank F (polarPerp Q (⨆ j, U j)) = 2) {f f' : V}
    (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hQf' : Q f' = 0) (hff' : polar Q f f' = 1) (a : Fin k) :
    ∃ (w : ↥(orthDerived Q)) (S : Subgroup ↥(orthDerived Q)),
      (∀ g, w * τ g * w⁻¹ = τ (sgnAut a g)) ∧ w ∈ S ∧
      IsComponentOf S (Subgroup.centralizer (τ '' {g | sgnAut a g = g})) ∧
      p ∣ Nat.card S := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hQv0 : Q (f + f') ≠ 0 := by
    rw [show Q (f + f') = Q f + Q f' + polar Q f f' from QuadraticMap.map_add Q f f', hQf, hQf',
      hff']
    simp
  have hvW : f + f' ∈ polarPerp Q (⨆ j, U j) := by
    rw [mem_polarPerp_iff] at hf hf' ⊢
    intro y hy
    rw [polar_add_right, hf y hy, hf' y hy, add_zero]
  let sv : Fin k → Multiplicative (ZMod p) := fun j => if j = a then 1 else ofAdd 1
  let x : ↥(orthDerived Q) := τ sv
  have hxE : x ∈ E := by
    rw [← hτrange]
    exact MonoidHom.mem_range.mpr ⟨sv, rfl⟩
  have hxpred : (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v := by
    constructor
    · intro v hv
      have h := hact sv a v hv
      rw [show sv a = 1 from if_pos rfl] at h
      simpa using h
    · intro j hja v hv
      have h := hact sv j v hv
      rw [show sv j = ofAdd 1 from if_neg hja, toAdd_ofAdd, ZMod.val_one p, pow_one] at h
      simpa using h
  have hc0 : Q (u a) ≠ 0 := by rw [hF.quad_eq a]; exact hF.c_ne_zero
  refine ⟨⟨signChange Q u (f + f') a, signChange_mem_orthDerived hQ hF hQv0⟩,
    (supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q), ?_, ?_, ?_, ?_⟩
  · refine conj_eq_of_mulSingle τ _ (sgnAut a) (fun l => Subtype.ext ?_)
    change signChange Q u (f + f') a * (τ (Pi.mulSingle l (ofAdd 1)) : V ≃ₗ[F] V) *
      (signChange Q u (f + f') a)⁻¹ = _
    rw [inv_eq_of_mul_eq_one_left (signChange_mul_self hF hvW)]
    by_cases hla : l = a
    · rw [hla, SpCoord.sgnAut_mulSingle_self, map_inv, hτ a]
      exact signChange_conj_self hF hvW
    · rw [SpCoord.sgnAut_mulSingle_of_ne hla, hτ l]
      exact signChange_conj_of_ne hF hvW hla
  · refine Subgroup.mem_subgroupOf.mpr ?_
    exact reflect_mul_reflect_mem_signBlock hF.toIsPlaneFrame a hQ hp hp2 ⟨hxE, hxpred⟩
      (Submodule.mem_sup_left (hF.mem a)) (Submodule.mem_sup_right hvW) hc0 hQv0
  · exact isComponentOf_signBlock hF.toIsPlaneFrame a hQ hp hp2 hW2 hf hQf hff' ⟨hxE, hxpred⟩
      (mem_image_fix_sgnAut hF.toIsPlaneFrame hp τ hτrange hact hxE hxpred.1)
      (image_fix_sgnAut_subset hp hp2 τ e hτ)
  · exact dvd_card_signBlock hF.toIsPlaneFrame a hQ hp hp2 hW2 hf hQf hff' ⟨hxE, hxpred⟩

end Blocks

section Datum

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem ggKGRootDatumAt_orthDerived (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ}
    (hdim : finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ) {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hlayer : ∀ a ∈ E, ∀ J : Subgroup ↥(orthDerived Q), ⁅J, J⁆ = J →
      J ≤ Subgroup.centralizer ({a} : Set ↥(orthDerived Q)) →
        J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set ↥(orthDerived Q)))) :
    GGKGRootDatumAt p E := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hℓ hdim
  have hpq' : ¬ p ∣ Nat.card F - 1 := by
    intro h
    have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  obtain ⟨k, U, e₀, hF₀, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim (by omega) hE hsc
  have hk : 1 ≤ k := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨e, u, c, t, hF, -⟩ := exists_coherentFrame hF₀ hp hp2 hpq hk
  obtain ⟨τ, hτinj, hτrange, hτc, hact⟩ := exists_frameTorus hF.toIsPlaneFrame hp
  have hSP : ∀ (g : ↥(orthDerived Q)) (s : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ f * g⁻¹ = τ (s f)) → IsSignedPerm ⇑s := fun g s hgs =>
    isSignedPerm_of_normalizer hQ hp hp2 hpq hT hF (by omega) hsc hτinj hτrange hτc hgs
  choose w₁ S₁ hws₁ hwS₁ hcomp₁ hdvd₁ using
    pair_model hQ hp hp2 hpq hF4 hdim (by omega : 3 ≤ ℓ) hF τ hτc
  rcases hcase with ⟨_, htop⟩ | ⟨hkℓ, f, f', hf, hf', hQf, hQf', hff'⟩
  · refine RealKGModelRoot.ggKGRootDatumAt_of_model hp hτinj hτrange w₁ (omPlusRefl p) S₁ hws₁
      hwS₁ hcomp₁ hdvd₁ ?_ hlayer
    intro g s hgs hs2 hfix
    rcases RealKGSignedRefl.signedRefl_cases hp hp2 (hSP g s hgs) hs2 hfix with
      ⟨a, rfl⟩ | ⟨x, rfl⟩
    · exact (not_induces_sgnAut hQ hp hpq' hF.toIsPlaneFrame htop hτc (hF.mem a)
        (by rw [hF.quad_eq a]; exact hF.c_ne_zero) g hgs).elim
    · exact ⟨x, rfl⟩
  · have hW2 := finrank_perp_eq_two hdim hkℓ hF.toIsPlaneFrame.toIsPlaneSystem
    choose w₂ S₂ hws₂ hwS₂ hcomp₂ hdvd₂ using
      sign_model hQ hp hp2 hF hτrange hτc hact hW2 hf hf' hQf hQf' hff'
    refine RealKGModelRoot.ggKGRootDatumAt_of_model hp hτinj hτrange (Sum.elim w₁ w₂)
      (Sum.elim (omPlusRefl p) sgnAut) (Sum.elim S₁ S₂) ?_ ?_ ?_ ?_ ?_ hlayer
    · rintro (x | a) f
      exacts [hws₁ x f, hws₂ a f]
    · rintro (x | a)
      exacts [hwS₁ x, hwS₂ a]
    · rintro (x | a)
      exacts [hcomp₁ x, hcomp₂ a]
    · rintro (x | a)
      exacts [hdvd₁ x, hdvd₂ a]
    · intro g s hgs hs2 hfix
      rcases RealKGSignedRefl.signedRefl_cases hp hp2 (hSP g s hgs) hs2 hfix with
        ⟨a, rfl⟩ | ⟨x, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
      · exact ⟨Sum.inl x, rfl⟩

end Datum

end RealKGOmega

end CFSG.StandardType

end
