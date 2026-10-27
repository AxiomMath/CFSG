module

public import CFSG.LocalAnalysis.StandardType.GGRealSgnDefs
public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCompSgn
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
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

section Signed

variable {p k : ℕ}

theorem omPlusRefl_not_commute_conj_swap (hp : p.Prime) (x : OmPlusIdx k) {c : Fin k}
    (hc1 : c ≠ x.1.1.1) (hc2 : c ≠ x.1.1.2) :
    ¬ Commute (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c) * omPlusRefl p x *
      (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c))⁻¹) (omPlusRefl p x) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
  have hic : i ≠ c := fun h => hc1 h.symm
  have hji : j ≠ i := hij.ne'
  have hjc : j ≠ c := fun h => hc2 h.symm
  have hne : (Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin k → Multiplicative (ZMod p)) ≠
      (Pi.mulSingle c (ofAdd (1 : ZMod p)) : Fin k → Multiplicative (ZMod p)) := by
    intro h
    exact hic (SpCoord.mulSingle_ofAdd_eq_iff (a := i) (b := c) (x := 1) (y := 1)
      (SpCoord.coord_zero_ne_one hp).symm h).1
  intro hcomm
  have heval := congrArg (fun g : MulAut (Fin k → Multiplicative (ZMod p)) =>
    g (Pi.mulSingle j (ofAdd 1))) hcomm.eq
  simp only [MulAut.mul_apply] at heval
  cases b
  ·
    have hB_j : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle j (ofAdd 1)) =
        Pi.mulSingle i (ofAdd 1) := by
      rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
        Equiv.swap_apply_right]
    have hB_c : omPlusRefl p (⟨(i, j), hij⟩, false) (Pi.mulSingle c (ofAdd 1)) =
        Pi.mulSingle c (ofAdd 1) := by
      rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle,
        Equiv.swap_apply_of_ne_of_ne hc1 hc2]
    have hσ_i : SpCoord.permAut (p := p) (Equiv.swap i c) (Pi.mulSingle i (ofAdd 1)) =
        Pi.mulSingle c (ofAdd 1) := by
      rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_left]
    have hσ_c : SpCoord.permAut (p := p) (Equiv.swap i c) (Pi.mulSingle c (ofAdd 1)) =
        Pi.mulSingle i (ofAdd 1) := by
      rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_right]
    have hσinv_j : (SpCoord.permAut (p := p) (Equiv.swap i c))⁻¹
        (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1) := by
      rw [SpCoord.permAut_inv_mulSingle, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne hji hjc]
    have hσinv_i : (SpCoord.permAut (p := p) (Equiv.swap i c))⁻¹
        (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [SpCoord.permAut_inv_mulSingle, Equiv.swap_inv, Equiv.swap_apply_left]
    have hA_j : SpCoord.permAut (p := p) (Equiv.swap i c)
        (omPlusRefl p (⟨(i, j), hij⟩, false)
          ((SpCoord.permAut (p := p) (Equiv.swap i c))⁻¹ (Pi.mulSingle j (ofAdd 1)))) =
        Pi.mulSingle c (ofAdd 1) := by
      rw [hσinv_j, hB_j, hσ_i]
    rw [hB_j, hσinv_i, hB_c, hσ_c, hA_j, hB_c] at heval
    exact hne heval
  ·
    have hB_j : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle j (ofAdd 1)) =
        (Pi.mulSingle i (ofAdd 1))⁻¹ := by
      rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
        SpCoord.permAut_mulSingle, Equiv.swap_apply_right,
        SpCoord.sgnAut_mulSingle_of_ne hij.ne, SpCoord.sgnAut_mulSingle_self]
    have hB_c : omPlusRefl p (⟨(i, j), hij⟩, true) (Pi.mulSingle c (ofAdd 1)) =
        Pi.mulSingle c (ofAdd 1) := by
      rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
        SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hc1 hc2,
        SpCoord.sgnAut_mulSingle_of_ne hc2, SpCoord.sgnAut_mulSingle_of_ne hc1]
    have hB_c_inv : omPlusRefl p (⟨(i, j), hij⟩, true)
        ((Pi.mulSingle c (ofAdd 1))⁻¹) = (Pi.mulSingle c (ofAdd 1))⁻¹ := by
      rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
        ← Pi.mulSingle_inv, SpCoord.permAut_mulSingle,
        Equiv.swap_apply_of_ne_of_ne hc1 hc2,
        SpCoord.sgnAut_mulSingle_of_ne hc2, SpCoord.sgnAut_mulSingle_of_ne hc1,
        Pi.mulSingle_inv]
    have hσ_i_inv : SpCoord.permAut (p := p) (Equiv.swap i c)
        ((Pi.mulSingle i (ofAdd 1))⁻¹) = (Pi.mulSingle c (ofAdd 1))⁻¹ := by
      rw [← Pi.mulSingle_inv, ← Pi.mulSingle_inv, SpCoord.permAut_mulSingle,
        Equiv.swap_apply_left]
    have hσ_c_inv : SpCoord.permAut (p := p) (Equiv.swap i c)
        ((Pi.mulSingle c (ofAdd 1))⁻¹) = (Pi.mulSingle i (ofAdd 1))⁻¹ := by
      rw [← Pi.mulSingle_inv, ← Pi.mulSingle_inv, SpCoord.permAut_mulSingle,
        Equiv.swap_apply_right]
    have hσinv_j : (SpCoord.permAut (p := p) (Equiv.swap i c))⁻¹
        (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1) := by
      rw [SpCoord.permAut_inv_mulSingle, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne hji hjc]
    have hσinv_i_inv : (SpCoord.permAut (p := p) (Equiv.swap i c))⁻¹
        ((Pi.mulSingle i (ofAdd 1))⁻¹) = (Pi.mulSingle c (ofAdd 1))⁻¹ := by
      rw [← Pi.mulSingle_inv, ← Pi.mulSingle_inv, SpCoord.permAut_inv_mulSingle,
        Equiv.swap_inv, Equiv.swap_apply_left]
    have hA_j : SpCoord.permAut (p := p) (Equiv.swap i c)
        (omPlusRefl p (⟨(i, j), hij⟩, true)
          ((SpCoord.permAut (p := p) (Equiv.swap i c))⁻¹ (Pi.mulSingle j (ofAdd 1)))) =
        (Pi.mulSingle c (ofAdd 1))⁻¹ := by
      rw [hσinv_j, hB_j, hσ_i_inv]
    rw [hB_j, hσinv_i_inv, hB_c_inv, hσ_c_inv, hA_j, hB_c_inv] at heval
    exact hne (inv_injective heval)

end Signed

section Blocks

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

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
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
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

theorem ggKGSgnComponentDatumAt_orthDerived (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    GGKGSgnComponentDatumAt p E := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hℓ hdim
  have hpq' : ¬ p ∣ Nat.card F - 1 := by
    intro h
    have : Nonempty F := ⟨0⟩
    have hFpos : 0 < Nat.card F := Nat.card_pos
    have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  obtain ⟨k, U, e₀, hF₀, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim (by omega) hE hsc
  have hk : 1 ≤ k := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨e, u, c, t, hF, -⟩ := exists_coherentFrame hF₀ hp hp2 hpq hk
  obtain ⟨τ, hτinj, hτrange, hτc, hact⟩ := exists_frameTorus hF.toIsPlaneFrame hp
  have hτmem : ∀ f, τ f ∈ E := fun f => by rw [← hτrange]; exact ⟨f, rfl⟩
  have hSP : ∀ (g : ↥(orthDerived Q)) (s : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ f * g⁻¹ = τ (s f)) → IsSignedPerm ⇑s := fun g s hgs =>
    isSignedPerm_of_normalizer hQ hp hp2 hpq hT hF (by omega) hsc hτinj hτrange hτc hgs
  intro w₀ hrefl hcomm
  obtain ⟨hnorm, hinv, hfix⟩ := hrefl
  obtain ⟨v, hv⟩ := RealKGModelRoot.exists_inducedAut hp hτinj hτrange hnorm
  have hv2 : v * v = 1 := by
    refine MulEquiv.ext fun f => hτinj ?_
    rw [MulAut.mul_apply, MulAut.one_apply, ← hv, ← hv]
    exact hinv _ (hτmem f)
  let eE : (Fin k → Multiplicative (ZMod p)) ≃* E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτrange)
  have hfix' : Nat.card {f // v f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := by
    have h1 : Nat.card {f // v f = f} =
        Nat.card {e : E // w₀ * (e : ↥(orthDerived Q)) * w₀⁻¹ = e} := by
      refine Nat.card_congr (Equiv.subtypeEquiv eE.toEquiv fun f => ?_)
      change v f = f ↔ w₀ * τ f * w₀⁻¹ = τ f
      rw [hv]
      exact hτinj.eq_iff.symm
    rw [h1, hfix]
    exact Nat.card_congr eE.toEquiv.symm
  rcases RealKGSignedRefl.signedRefl_cases hp hp2 (hSP w₀ v hv) hv2 hfix' with
    ⟨a, ha⟩ | ⟨x, hx⟩
  ·
    rcases hcase with ⟨hkℓ, htop⟩ | ⟨hkℓ, f, f', hf, hf', hQf, hQf', hff'⟩
    · have hgs : ∀ g, w₀ * τ g * w₀⁻¹ = τ (sgnAut a g) := by
        intro g
        rw [hv g, ha]
      exact (not_induces_sgnAut hQ hp hpq' hF.toIsPlaneFrame htop hτc (hF.mem a)
        (by rw [hF.quad_eq a]; exact hF.c_ne_zero) w₀ hgs).elim
    · have hW2 := finrank_perp_eq_two hdim hkℓ hF.toIsPlaneFrame.toIsPlaneSystem
      obtain ⟨w, S, hws, hwS, hcomp, hdvd⟩ :=
        sign_model hQ hp hp2 hF hτrange hτc hact hW2 hf hf' hQf hQf' hff' a
      refine ⟨w, ?_, S, hwS, ?_, hdvd⟩
      · intro y hy
        rw [← hτrange] at hy
        obtain ⟨g, rfl⟩ := hy
        rw [hws g, hv g, ha]
      · have hinf : ((E ⊓ Subgroup.centralizer ({w} : Set ↥(orthDerived Q)) :
            Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) =
            τ '' {g | sgnAut a g = g} := by
          ext y
          constructor
          · rintro ⟨hyE, hyc⟩
            rw [← hτrange] at hyE
            obtain ⟨g, rfl⟩ := hyE
            refine ⟨g, hτinj ?_, rfl⟩
            rw [← hws g, mul_inv_eq_iff_eq_mul]
            exact (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
          · rintro ⟨g, hg, rfl⟩
            refine ⟨hτmem g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
            have h := hws g
            rw [show sgnAut a g = g from hg, mul_inv_eq_iff_eq_mul] at h
            exact h.symm
        rw [hinf]
        exact hcomp
  ·
    have hk3 : 3 ≤ k := by
      rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    obtain ⟨c', hc'i, hc'j⟩ : ∃ c' : Fin k, c' ≠ x.1.1.1 ∧ c' ≠ x.1.1.2 := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (Fin k)) ⊆
          ({x.1.1.1, x.1.1.2} : Finset (Fin k)) := by
        intro d _
        by_cases hd : d = x.1.1.1
        · rw [hd]; simp
        · rw [h d hd]; simp
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at hle
      have h2 : ({x.1.1.1, x.1.1.2} : Finset (Fin k)).card ≤ 2 := by
        calc ({x.1.1.1, x.1.1.2} : Finset (Fin k)).card
            ≤ ({x.1.1.2} : Finset (Fin k)).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      omega
    let sw : ↥(orthDerived Q) :=
      ⟨frameSwap Q e u c t x.1.1.1 c', frameSwap_mem_orthDerived hQ hdim (by omega)⟩
    have hsw2 : sw * sw = 1 := Subtype.ext (frameSwap_mul_self hF (Ne.symm hc'i))
    have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
    have hsw_conj : ∀ g, sw * τ g * sw⁻¹ =
        τ (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g) := by
      refine conj_eq_of_mulSingle τ sw (SpCoord.permAut (Equiv.swap x.1.1.1 c')) (fun d => ?_)
      rw [hswinv]
      by_cases hdi : d = x.1.1.1
      · subst d
        have hs : SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c')
            (Pi.mulSingle x.1.1.1 (ofAdd 1)) = Pi.mulSingle c' (ofAdd 1) := by
          rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_left]
        rw [hs, hτc c', hτc x.1.1.1]
        exact Subtype.ext (frameSwap_conj_left hF (Ne.symm hc'i))
      · by_cases hdc : d = c'
        · subst d
          have hs : SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c')
              (Pi.mulSingle c' (ofAdd 1)) = Pi.mulSingle x.1.1.1 (ofAdd 1) := by
            rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_right]
          rw [hs, hτc x.1.1.1, hτc c']
          exact Subtype.ext (frameSwap_conj_right hF (Ne.symm hc'i))
        · have hs : SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c')
              (Pi.mulSingle d (ofAdd 1)) = Pi.mulSingle d (ofAdd 1) := by
            rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hdi hdc]
          rw [hs, hτc d]
          exact Subtype.ext (frameSwap_conj_of_ne hF (Ne.symm hc'i) hdi hdc)
    have hmap : ∀ y ∈ E, sw * y * sw⁻¹ ∈ E := by
      intro y hy
      rw [← hτrange] at hy ⊢
      obtain ⟨g, rfl⟩ := hy
      exact ⟨SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g, (hsw_conj g).symm⟩
    have hswN : sw ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨hmap y, fun hy => by
        have h2 : sw * (sw * y * sw⁻¹) * sw⁻¹ = y := by
          calc sw * (sw * y * sw⁻¹) * sw⁻¹
              = (sw * sw) * y * (sw⁻¹ * sw⁻¹) := by group
            _ = y := by rw [hsw2, ← mul_inv_rev, hsw2, inv_one, one_mul, mul_one]
        have h3 := hmap (sw * y * sw⁻¹) hy
        rwa [h2] at h3⟩
    have hσinv_eq : (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c'))⁻¹ =
        SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') := by
      refine MulEquiv.ext fun g => ?_
      rw [SpCoord.permAut_inv_apply, SpCoord.permAut_apply, Equiv.swap_inv]
    have hconjW : ∀ g, (sw * w₀ * sw⁻¹) * τ g * (sw * w₀ * sw⁻¹)⁻¹ =
        τ ((SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') * v *
          (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c'))⁻¹) g) := by
      intro g
      have hsw_conj_inv : sw⁻¹ * τ g * sw =
          τ (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g) := by
        calc sw⁻¹ * τ g * sw = sw * τ g * sw⁻¹ := by rw [hswinv]
          _ = τ (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g) := hsw_conj g
      calc (sw * w₀ * sw⁻¹) * τ g * (sw * w₀ * sw⁻¹)⁻¹
          = sw * (w₀ * (sw⁻¹ * τ g * sw) * w₀⁻¹) * sw⁻¹ := by group
        _ = sw * (w₀ * τ (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g) * w₀⁻¹) *
              sw⁻¹ := by rw [hsw_conj_inv]
        _ = sw * τ (v (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g)) * sw⁻¹ := by
              rw [hv]
        _ = τ (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c')
              (v (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') g))) := hsw_conj _
        _ = τ ((SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') * v *
              (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c'))⁻¹) g) := by
              rw [hσinv_eq]
              rfl
    have hEq : ∀ g, (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') * v *
        (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c'))⁻¹) (v g) =
        v ((SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') * v *
          (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c'))⁻¹) g) := by
      intro g
      have h := hcomm sw hswN (τ g) (hτmem g)
      rw [hv g] at h
      rw [hconjW (v g), hconjW g, hv] at h
      exact hτinj h
    have hcommv : Commute (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c') * v *
        (SpCoord.permAut (p := p) (Equiv.swap x.1.1.1 c'))⁻¹) v := by
      refine MulEquiv.ext fun g => ?_
      simpa only [MulAut.mul_apply] using hEq g
    rw [hx] at hcommv
    exact (omPlusRefl_not_commute_conj_swap hp x hc'i hc'j hcommv).elim

theorem ggKGSgnComponentDatum_orthDerived (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    {r : ℕ} : GGKGSgnComponentDatum p r ↥(orthDerived Q) :=
  fun _ hE _ _ hsc => ggKGSgnComponentDatumAt_orthDerived hQ hp hp2 hpq hdim hℓ hE hsc

end Datum

end RealKGOmega

end CFSG.StandardType

end
