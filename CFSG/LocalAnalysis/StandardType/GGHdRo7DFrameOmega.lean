module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeEvenAux
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.RankThree.PartOne.S11d.OrthCaseH

public section

namespace CFSG.StandardType.HdRo7D

open Module QuadraticMap Multiplicative SpCoord NbrOrth
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Basic

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {p k : ℕ} {E : Subgroup ↥(orthDerived Q)}

private theorem hdRo7DFrOAux_conj_mul
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    {w₁ w₂ : ↥(orthDerived Q)} {s₁ s₂ : MulAut (Fin k → Multiplicative (ZMod p))}
    (h₁ : ∀ f, w₁ * τ f * w₁⁻¹ = τ (s₁ f))
    (h₂ : ∀ f, w₂ * τ f * w₂⁻¹ = τ (s₂ f)) :
    ∀ f, (w₁ * w₂) * τ f * (w₁ * w₂)⁻¹ = τ ((s₁ * s₂) f) := by
  intro f
  rw [mul_inv_rev, MulAut.mul_apply]
  calc w₁ * w₂ * τ f * (w₂⁻¹ * w₁⁻¹)
      = w₁ * (w₂ * τ f * w₂⁻¹) * w₁⁻¹ := by group
    _ = w₁ * τ (s₂ f) * w₁⁻¹ := by rw [h₂]
    _ = τ (s₁ (s₂ f)) := h₁ _

private noncomputable def hdRo7DFrOAux_indSet
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)) :
    Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) where
  carrier := {s | ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (s f)}
  one_mem' := ⟨1, by intro f; simp⟩
  mul_mem' := by
    rintro s₁ s₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    exact ⟨w₁ * w₂, hdRo7DFrOAux_conj_mul h₁ h₂⟩
  inv_mem' := by
    rintro s ⟨w, h⟩
    refine ⟨w⁻¹, fun f => ?_⟩
    have h1 : w * τ (s⁻¹ f) * w⁻¹ = τ f := by
      rw [h (s⁻¹ f)]
      simp
    calc w⁻¹ * τ f * (w⁻¹)⁻¹
        = w⁻¹ * (w * τ (s⁻¹ f) * w⁻¹) * w := by rw [h1]; group
      _ = τ (s⁻¹ f) := by group

theorem hdRo7DFrOAux_exists_indAut
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    {g : ↥(orthDerived Q)} (hg : ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hτinj : Function.Injective τ) (hτrange : τ.range = E) [Finite ↥E] :
    ∃ w : MulAut (Fin k → Multiplicative (ZMod p)), ∀ f, g * τ f * g⁻¹ = τ (w f) := by
  classical
  have hτmem : ∀ f, τ f ∈ E := by
    intro f
    rw [← hτrange]
    exact ⟨f, rfl⟩
  let τ' : (Fin k → Multiplicative (ZMod p)) →* ↥E := τ.codRestrict E hτmem
  have hτ'inj : Function.Injective τ' := fun f₁ f₂ h =>
    hτinj (congrArg (fun x : ↥E => (x : ↥(orthDerived Q))) h)
  have hτ'surj : Function.Surjective τ' := by
    intro x
    have hx : (x : ↥(orthDerived Q)) ∈ τ.range := by
      rw [hτrange]
      exact x.2
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hx
    exact ⟨f, Subtype.ext hf⟩
  let eτ : (Fin k → Multiplicative (ZMod p)) ≃* ↥E :=
    MulEquiv.ofBijective τ' ⟨hτ'inj, hτ'surj⟩
  let cg : ↥E →* ↥E :=
    { toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
        group) }
  have hcg_inj : Function.Injective cg := by
    intro x y h
    have h1 : g * (x : ↥(orthDerived Q)) * g⁻¹ = g * (y : ↥(orthDerived Q)) * g⁻¹ :=
      congrArg (fun z : ↥E => (z : ↥(orthDerived Q))) h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  let cgAut : MulAut ↥E :=
    MulEquiv.ofBijective cg ⟨hcg_inj, Finite.injective_iff_surjective.mp hcg_inj⟩
  let w : MulAut (Fin k → Multiplicative (ZMod p)) := (MulAut.congr eτ).symm cgAut
  refine ⟨w, fun f => ?_⟩
  have h1 : eτ (w f) = cgAut (eτ f) := by
    have h2 : MulAut.congr eτ w = cgAut := MulEquiv.apply_symm_apply (MulAut.congr eτ) cgAut
    have h3 := congrArg (fun u : MulAut ↥E => u (eτ f)) h2
    rw [MulAut.congr_apply] at h3
    simpa [MulEquiv.trans_apply] using h3
  have h4 : τ (w f) = g * τ f * g⁻¹ :=
    congrArg (fun z : ↥E => (z : ↥(orthDerived Q))) h1
  exact h4.symm

end Basic

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

private theorem hdRo7DFrOAux_pairWeyl
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d) (x : OmPlusIdx k) :
    ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (omPlusRefl p x f) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨⟨⟨i, j⟩, hij⟩, b⟩ := x
  cases b
  · let sw : ↥(orthDerived Q) :=
      ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim h3⟩
    have hsw2 : sw * sw = 1 := Subtype.ext (frameSwap_mul_self hF hij.ne)
    have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
    have h1 : sw * e i * sw = e j := Subtype.ext (frameSwap_conj_left hF hij.ne)
    have h2 : sw * e j * sw = e i := Subtype.ext (frameSwap_conj_right hF hij.ne)
    refine ⟨sw, fun f => ?_⟩
    refine conj_eq_of_mulSingle τ sw (omPlusRefl p (⟨(i, j), hij⟩, false)) (fun d => ?_) f
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
  · let sw : ↥(orthDerived Q) :=
      ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim h3 hF⟩
    have hsw2 : sw * sw = 1 := Subtype.ext (signedSwap_mul_self hF hij.ne)
    have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
    have h1 : sw * e i * sw = (e j)⁻¹ := Subtype.ext (signedSwap_conj_left hF hij.ne)
    have h2 : sw * e j * sw = (e i)⁻¹ := Subtype.ext (signedSwap_conj_right hF hij.ne)
    refine ⟨sw, fun f => ?_⟩
    refine conj_eq_of_mulSingle τ sw (omPlusRefl p (⟨(i, j), hij⟩, true)) (fun d => ?_) f
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

private theorem hdRo7DFrOAux_swapWeyl
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d) {a b : Fin k} (hab : a ≠ b) :
    ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (permAut (Equiv.swap a b) f) := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨w, hw⟩ := hdRo7DFrOAux_pairWeyl hQ hp hdim h3 hF τ hτ
      (⟨(a, b), h⟩, false)
    exact ⟨w, fun f => by rw [hw f, omPlusRefl_false (p := p) h]⟩
  · obtain ⟨w, hw⟩ := hdRo7DFrOAux_pairWeyl hQ hp hdim h3 hF τ hτ
      (⟨(b, a), h⟩, false)
    exact ⟨w, fun f => by rw [hw f, omPlusRefl_false (p := p) h, Equiv.swap_comm]⟩

private theorem hdRo7DFrOAux_dinvWeyl
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    {ℓ : ℕ} (hdim : finrank F V = 2 * ℓ) (h3 : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d) {a b : Fin k} (hab : a ≠ b) :
    ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (dinv a b f) := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨wt, hwt⟩ := hdRo7DFrOAux_pairWeyl hQ hp hdim h3 hF τ hτ
      (⟨(a, b), h⟩, true)
    obtain ⟨wf, hwf⟩ := hdRo7DFrOAux_pairWeyl hQ hp hdim h3 hF τ hτ
      (⟨(a, b), h⟩, false)
    refine ⟨wt * wf, fun f => ?_⟩
    rw [hdRo7DFrOAux_conj_mul hwt hwf f]
    have h2 : (omPlusRefl p (⟨(a, b), h⟩, true) * omPlusRefl p (⟨(a, b), h⟩, false) :
        MulAut (Fin k → Multiplicative (ZMod p))) = sgnAut a * sgnAut b := by
      rw [omPlusRefl_true (p := p) h, omPlusRefl_false (p := p) h, mul_assoc,
        OrthExcEven.permAut_swap_mul_self, mul_one]
    rw [h2, OrthExcEven.sgnAut_mul_sgnAut_apply]
  · obtain ⟨wt, hwt⟩ := hdRo7DFrOAux_pairWeyl hQ hp hdim h3 hF τ hτ
      (⟨(b, a), h⟩, true)
    obtain ⟨wf, hwf⟩ := hdRo7DFrOAux_pairWeyl hQ hp hdim h3 hF τ hτ
      (⟨(b, a), h⟩, false)
    refine ⟨wt * wf, fun f => ?_⟩
    rw [hdRo7DFrOAux_conj_mul hwt hwf f]
    have h2 : (omPlusRefl p (⟨(b, a), h⟩, true) * omPlusRefl p (⟨(b, a), h⟩, false) :
        MulAut (Fin k → Multiplicative (ZMod p))) = sgnAut a * sgnAut b := by
      rw [omPlusRefl_true (p := p) h, omPlusRefl_false (p := p) h, mul_assoc]
      rw [show (permAut (Equiv.swap b a) : MulAut (Fin k → Multiplicative (ZMod p))) *
          permAut (Equiv.swap b a) = 1 by
        rw [Equiv.swap_comm]
        exact OrthExcEven.permAut_swap_mul_self a b]
      rw [mul_one]
      exact SpCoord.sgnAut_mul_comm b a
    rw [h2, OrthExcEven.sgnAut_mul_sgnAut_apply]

private theorem hdRo7DFrOAux_sgnWeyl
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hF : IsCoherentFrame Q p U e E u c t)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d) {f f' : V}
    (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j))
    (hQf : Q f = 0) (hQf' : Q f' = 0) (hff' : polar Q f f' = 1) (a : Fin k) :
    ∃ w : ↥(orthDerived Q), ∀ g, w * τ g * w⁻¹ = τ (sgnAut a g) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hQv0 : Q (f + f') ≠ 0 := by
    rw [show Q (f + f') = Q f + Q f' + polar Q f f' from QuadraticMap.map_add Q f f', hQf,
      hQf', hff']
    simp
  have hvW : f + f' ∈ polarPerp Q (⨆ j, U j) := by
    rw [mem_polarPerp_iff] at hf hf' ⊢
    intro y hy
    rw [polar_add_right, hf y hy, hf' y hy, add_zero]
  refine ⟨⟨signChange Q u (f + f') a, signChange_mem_orthDerived hQ hF hQv0⟩, ?_⟩
  refine conj_eq_of_mulSingle τ _ (sgnAut a) (fun l => Subtype.ext ?_)
  change signChange Q u (f + f') a * (τ (Pi.mulSingle l (ofAdd 1)) : V ≃ₗ[F] V) *
    (signChange Q u (f + f') a)⁻¹ = _
  rw [inv_eq_of_mul_eq_one_left (signChange_mul_self hF hvW)]
  by_cases hla : l = a
  · rw [hla, SpCoord.sgnAut_mulSingle_self, map_inv, hτ a]
    exact signChange_conj_self hF hvW
  · rw [SpCoord.sgnAut_mulSingle_of_ne hla, hτ l]
    exact signChange_conj_of_ne hF hvW hla


private theorem hdRo7DFrOAux_prod_eq_one
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq' : ¬ p ∣ Nat.card F - 1) (hF : IsCoherentFrame Q p U e E u c t)
    (htop : (⨆ j, U j) = ⊤)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτ : ∀ d, τ (Pi.mulSingle d (ofAdd 1)) = e d)
    (hdinv : ∀ i j : Fin k, i ≠ j → ∃ w : ↥(orthDerived Q),
      ∀ f, w * τ f * w⁻¹ = τ (dinv i j f))
    (hswap : ∀ a b : Fin k, a ≠ b → ∃ w : ↥(orthDerived Q),
      ∀ f, w * τ f * w⁻¹ = τ (permAut (Equiv.swap a b) f))
    {w : MulAut (Fin k → Multiplicative (ZMod p))}
    (hw : ∃ g : ↥(orthDerived Q), ∀ f, g * τ f * g⁻¹ = τ (w f))
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hrel : ∀ f i, toAdd (w f (π i)) = ε i * toAdd (f i)) :
    ∏ i, ε i = 1 := by
  classical
  let H := hdRo7DFrOAux_indSet τ
  have hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
    intro i j hij
    obtain ⟨u, hu⟩ := hdinv i j hij
    exact ⟨u, hu⟩
  have ht : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    obtain ⟨u, hu⟩ := hswap a b hab
    exact ⟨u, hu⟩
  have hperm : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ H := by
    intro σ
    refine Equiv.Perm.swap_induction_on σ ?_ ?_
    · exact H.one_mem
    · intro π x y hxy ih
      rw [ggWTEven_permAut_mul]
      exact H.mul_mem (ht x y hxy) ih
  obtain ⟨g, hg⟩ := hw
  have hu : w ∈ H := ⟨g, hg⟩
  have hw_decomp : w = permAut π * diagAut ε (fun i => coord_sign_mul_self (hε i)) := by
    refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
    obtain ⟨i, rfl⟩ := π.surjective j
    have hπ : π⁻¹ (π i) = i := by simp
    rw [MulAut.mul_apply, permAut_apply, Function.comp_apply, hπ, diagAut_apply, hrel f i,
      toAdd_ofAdd]
  have hdiag : diagAut ε (fun i => coord_sign_mul_self (hε i)) ∈ H := by
    have h1 : diagAut ε (fun i => coord_sign_mul_self (hε i)) = (permAut π)⁻¹ * w := by
      rw [hw_decomp]; group
    rw [h1]
    exact H.mul_mem (H.inv_mem (hperm π)) hu
  by_contra hprod
  have hex : ∃ i₀ : Fin k, ε i₀ = -1 := by
    by_contra h
    push Not at h
    exact hprod (Finset.prod_eq_one fun i _ => (hε i).resolve_right (h i))
  obtain ⟨i₀, hεi₀⟩ := hex
  let ε' : Fin k → ZMod p := Function.update ε i₀ 1
  have hε' : ∀ i, ε' i = 1 ∨ ε' i = -1 := by
    intro i
    by_cases hii : i = i₀
    · subst hii; simp [ε']
    · rw [show ε' i = ε i from Function.update_of_ne hii (1 : ZMod p) ε]
      exact hε i
  have hε'i₀ : ε' i₀ = 1 := by simp [ε']
  have hεprod : ∏ i, ε i = -1 := by
    have h1 : (∏ i, ε i) = (-1 : ZMod p) ^ (Finset.univ.filter (fun i => ε i = -1)).card := by
      have hc' : (∏ i, ε i) = ∏ i, (if ε i = -1 then (-1 : ZMod p) else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        rcases hε i with h | h <;> simp [h]
      rw [hc']
      rw [← Finset.prod_filter (s := Finset.univ) (f := fun _ => (-1 : ZMod p))
        (p := fun i => ε i = -1), Finset.prod_const]
    rw [h1] at hprod ⊢
    rcases Nat.even_or_odd (Finset.univ.filter (fun i => ε i = -1)).card with he | ho
    · exact absurd (Even.neg_one_pow he) hprod
    · exact Odd.neg_one_pow ho
  have hprod' : ∏ i, ε' i = 1 := by
    have hupdate : ∏ i, ε' i = ∏ i ∈ Finset.univ \ {i₀}, ε i := by
      rw [show (∏ i, ε' i) = ∏ i ∈ (Finset.univ : Finset (Fin k)), ε' i from rfl]
      rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i₀) ε', hε'i₀, one_mul]
      refine Finset.prod_congr rfl fun i hi => ?_
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact Function.update_of_ne hi.2 (1 : ZMod p) ε
    have herase : (∏ i ∈ Finset.univ \ {i₀}, ε i) * ε i₀ = ∏ i, ε i :=
      (Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ i₀) ε).symm
    rw [hεi₀, hεprod] at herase
    have hneg : (-1 : ZMod p) * (-1) = 1 := by ring
    have hone : ∏ i ∈ Finset.univ \ {i₀}, ε i = 1 := by
      calc ∏ i ∈ Finset.univ \ {i₀}, ε i
          = (∏ i ∈ Finset.univ \ {i₀}, ε i) * ((-1) * (-1)) := by rw [hneg, mul_one]
        _ = ((∏ i ∈ Finset.univ \ {i₀}, ε i) * (-1)) * (-1) := by ring
        _ = (-1) * (-1) := by rw [herase]
        _ = 1 := hneg
    rw [hupdate, hone]
  have heven : Even (Finset.univ.filter (fun i => ε' i = -1)).card :=
    ggWTEven_even_card_of_prod hp hp2 ε' hε' hprod'
  obtain ⟨n, hn⟩ := heven
  have hdiag' : diagAut ε' (fun i => coord_sign_mul_self (hε' i)) ∈ H := by
    refine OrthExcEven.mem_of_diag_even hd n (Finset.univ.filter (fun i => ε' i = -1))
      (by omega) _ ε' ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hε' i with h | h
      · exact h
      · exact absurd h hi
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro f i
      simp [diagAut_apply]
  have hdecomp : diagAut ε (fun i => coord_sign_mul_self (hε i)) =
      diagAut ε' (fun i => coord_sign_mul_self (hε' i)) * sgnAut i₀ := by
    refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
    rw [MulAut.mul_apply, diagAut_apply, diagAut_apply, sgnAut_apply]
    by_cases hii : i = i₀
    · subst i
      simp only [Function.update_self, toAdd_ofAdd]
      rw [toAdd_inv, hεi₀, hε'i₀]
      ring
    · have h1 : ε' i = ε i := Function.update_of_ne hii (1 : ZMod p) ε
      have h2 : Function.update f i₀ (f i₀)⁻¹ i = f i := Function.update_of_ne hii _ _
      rw [h1, h2]
  have hsgn : sgnAut i₀ ∈ H := by
    have h1 : sgnAut i₀ = (diagAut ε' (fun i => coord_sign_mul_self (hε' i)))⁻¹ *
        diagAut ε (fun i => coord_sign_mul_self (hε i)) := by
      rw [hdecomp]; group
    rw [h1]
    exact H.mul_mem (H.inv_mem hdiag') hdiag
  obtain ⟨g', hg'⟩ : ∃ g' : ↥(orthDerived Q), ∀ f, g' * τ f * g'⁻¹ = τ (sgnAut i₀ f) := hsgn
  exact RealKGOmega.not_induces_sgnAut hQ hp hpq' hF.toIsPlaneFrame htop hτ (hF.mem i₀)
    (by rw [hF.quad_eq i₀]; exact hF.c_ne_zero) g' hg'

theorem d_frameOmega_holds : DFrameOmegaLeaf := by
  intro F _ _ _ V _ _ _ Q hQ p hp hp2 hpq ℓ hdim hℓ E hE h3 hsc
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun x : V ≃ₗ[F] V => (x : V → V))
    fun x y hxy => LinearEquiv.ext (congrFun hxy)
  have : Finite ↥(orthDerived Q) := Finite.of_injective (Subtype.val) Subtype.val_injective
  have : Finite ↥E := Finite.of_injective (Subtype.val) Subtype.val_injective
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hℓ hdim
  have hpq' : ¬ p ∣ Nat.card F - 1 := by
    intro h
    have hcardF : 1 ≤ Nat.card F := Nat.card_pos
    have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  obtain ⟨k, U, e₀, hF₀, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim (by omega) hE hsc
  have hk : 1 ≤ k := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨e, u, c, t, hF, -⟩ := exists_coherentFrame hF₀ hp hp2 hpq hk
  obtain ⟨τ, hτinj, hτrange, hτc, hact⟩ := exists_frameTorus hF.toIsPlaneFrame hp
  have hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥(orthDerived Q),
      ∀ f, w * τ f * w⁻¹ = τ (permAut σ f) := by
    intro σ
    refine Equiv.Perm.swap_induction_on σ ⟨1, ?_⟩ ?_
    · intro f
      simp [permAut_apply]
    · intro π x y hxy ih
      obtain ⟨w₁, hw₁⟩ := hdRo7DFrOAux_swapWeyl hQ hp hdim (by omega) hF τ hτc hxy
      obtain ⟨w₂, hw₂⟩ := ih
      exact ⟨w₁ * w₂, fun f => by
        rw [hdRo7DFrOAux_conj_mul hw₁ hw₂ f, ggWTEven_permAut_mul]⟩
  refine ⟨k, τ, hτinj, hτrange, hperm, ?_⟩
  rcases hcase with ⟨hkℓ, htop⟩ | ⟨hkℓ, f, f', hf, hf', hQf, hQf', hff'⟩
  · refine Or.inl ⟨hkℓ, fun i j hij =>
      hdRo7DFrOAux_dinvWeyl hQ hp hdim (by omega) hF τ hτc hij, ?_⟩
    intro g hg
    obtain ⟨w, hgw⟩ := hdRo7DFrOAux_exists_indAut hg hτinj hτrange
    obtain ⟨π, ε, hε, hrel⟩ :=
      RealKGOmega.isSignedPerm_of_normalizer hQ hp hp2 hpq hT hF (by omega) hsc hτinj
        hτrange hτc hgw
    refine ⟨π, ε, hε, ?_, ?_⟩
    · exact hdRo7DFrOAux_prod_eq_one hQ hp hp2 hpq' hF htop hτc
        (fun i j hij => hdRo7DFrOAux_dinvWeyl hQ hp hdim (by omega) hF τ hτc hij)
        (fun a b hab => hdRo7DFrOAux_swapWeyl hQ hp hdim (by omega) hF τ hτc hab)
        ⟨g, hgw⟩ hε hrel
    · intro f₀ f₁ hff' i
      have h1 : τ f₁ = τ (w f₀) := by rw [← hff', hgw f₀]
      have h2 : f₁ = w f₀ := hτinj h1
      rw [h2]
      exact hrel f₀ i
  · refine Or.inr ⟨by omega, fun i =>
      hdRo7DFrOAux_sgnWeyl hQ hp hF hτc hf hf' hQf hQf' hff' i, ?_⟩
    intro g hg
    obtain ⟨w, hgw⟩ := hdRo7DFrOAux_exists_indAut hg hτinj hτrange
    obtain ⟨π, ε, hε, hrel⟩ :=
      RealKGOmega.isSignedPerm_of_normalizer hQ hp hp2 hpq hT hF (by omega) hsc hτinj
        hτrange hτc hgw
    refine ⟨π, ε, hε, ?_⟩
    intro f₀ f₁ hff' i
    have h1 : τ f₁ = τ (w f₀) := by rw [← hff', hgw f₀]
    have h2 : f₁ = w f₀ := hτinj h1
    rw [h2]
    exact hrel f₀ i


end CFSG.StandardType.HdRo7D
