module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAIface
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAForm
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrABridgeLin
public import CFSG.RankThree.GF2n.Stroth80.Sec715Triality

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714 Module
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem configAData_ker_trivial (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
    (hφk : ∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t))
    {L₃ L₄ : Type} [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
    {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
    {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
    {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
    {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
    {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}
    (hD : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) :
    (∀ h, φ₈ h = 1 → ρ₃ h = 1) ∧ (∀ h, φ₈ h = 1 → ρ₄ h = 1) :=
  ⟨fun h hh => eq_one_of_coord (wvAct hS hs.toSec5.mem) ρ₃ eM hD.equivM
      (wvAct_of_mem_CN h310chi h52a hS hs hr h ((hφk h).mp hh)),
    fun h hh => eq_one_of_coord (deltaAct hS hs.toSec5.mem) ρ₄ eN hD.equivN
      (deltaAct_of_mem_CN h310chi h52a hS hs hr h ((hφk h).mp hh))⟩

theorem endScalar4_of (hEnd : Omega8EndScalarStatement) (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
    (hφr : φ₈.range = StatedOmega (StatedQuadPlus 4 K))
    (hφk : ∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t))
    {L₃ L₄ : Type} [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
    {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
    {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
    {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
    {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
    {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}
    (hD : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) :
    ∀ T : L₄ →ₗ[K] L₄, (∀ x, T ∘ₗ (ρ₄ x : L₄ →ₗ[K] L₄) = (ρ₄ x : L₄ →ₗ[K] L₄) ∘ₗ T) →
      ∃ c : K, T = c • LinearMap.id := by
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  haveI : FiniteDimensional K L₄ :=
    Module.finite_of_finrank_pos (by rw [hD.finrank₄]; norm_num)
  have h4 : 4 ≤ Nat.card K := hS.card ▸ hc.hyp.q4
  exact hEnd K h4 _ φ₈ hφr L₄ ρ₄ (configAData_ker_trivial h310chi h52a hS hs hr φ₈ hφk hD).2
    hD.irr₄ (exists_ne_one_of_irr ρ₄ hD.irr₄ (by rw [hD.finrank₄]; norm_num))
    (by rw [hD.finrank₄]; norm_num)

theorem trialityFacts_of (hTri : Omega8TrialityStatement) (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
    (hφr : φ₈.range = StatedOmega (StatedQuadPlus 4 K))
    (hφk : ∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t))
    (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (he : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
      e ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS hs.toSec5.mem _ x.2 _ w.2⟩ =
        (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w)
    {L₃ L₄ : Type} [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
    {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
    {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
    {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
    {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
    {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}
    (hD : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) :
    TrialityFacts q₃ q₄ μ := by
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  haveI : FiniteDimensional K L₃ :=
    Module.finite_of_finrank_pos (by rw [hD.finrank₃]; norm_num)
  haveI : FiniteDimensional K L₄ :=
    Module.finite_of_finrank_pos (by rw [hD.finrank₄]; norm_num)
  haveI : Nontrivial L₃ := Module.nontrivial_of_finrank_pos (by rw [hD.finrank₃]; norm_num)
  haveI : Nontrivial L₄ := Module.nontrivial_of_finrank_pos (by rw [hD.finrank₄]; norm_num)
  have h4 : 4 ≤ Nat.card K := hS.card ▸ hc.hyp.q4
  obtain ⟨htr₃, htr₄⟩ := configAData_ker_trivial h310chi h52a hS hs hr φ₈ hφk hD
  set β : L₃ →ₗ[K] L₄ →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    μ.compr₂ (e : ↥(hc.VtSub hS.model t) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) with hβdef
  have hβapp : ∀ x y, β x y = e (μ x y) := fun x y => rfl
  have hβeq : ∀ (h : ↥(bar M Q (Rt M (LB M Q B) t))) (x : L₃) (y : L₄),
      β (ρ₃ h x) (ρ₄ h y) = ((φ₈ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ β x y := by
    intro h x y
    rw [hβapp, hβapp, hD.μ_equiv, ← he]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hD.μ_ne
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have h1 : e (μ x y) = 0 := by
      rw [← hβapp, h0]
      rfl
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    exact (LinearEquiv.map_eq_zero_iff e).mp h1
  obtain ⟨-, -, -, -, -, -, -, -, hlast⟩ := hTri K h4 _ φ₈ hφr L₃ ρ₃ L₄ ρ₄ htr₃ htr₄ hD.irr₃
    hD.irr₄ hD.finrank₃ hD.finrank₄ β hβeq hβ0
  obtain ⟨c₁, c₂, -, -, c₅, -, c₇, -, -, -, -⟩ := hlast q₃ q₄ hD.q₃_inv hD.q₄_inv
    (quadraticForm_ne_zero_of_nd q₃ hD.q₃_nd) (quadraticForm_ne_zero_of_nd q₄ hD.q₄_nd)
  have hflip : ∀ y : L₄, β.flip y =
      (e : ↥(hc.VtSub hS.model t) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∘ₗ μ.flip y := fun y =>
    LinearMap.ext fun x => rfl
  have hrange : ∀ y : L₄, LinearMap.range (β.flip y) =
      (LinearMap.range (μ.flip y)).map (e : ↥(hc.VtSub hS.model t) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
    fun y => by rw [hflip, LinearMap.range_comp]
  have hfin : ∀ y : L₄, finrank K (LinearMap.range (β.flip y)) =
      finrank K (LinearMap.range (μ.flip y)) := fun y => by
    rw [hrange]
    exact LinearEquiv.finrank_map_eq e _
  have hker : ∀ y : L₄, LinearMap.ker (β.flip y) = LinearMap.ker (μ.flip y) := fun y => by
    rw [hflip, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  refine ⟨fun y hy hqy => ?_, fun y hy hqy => ?_, fun y hy hqy => ?_,
    fun y y' hy hy' hqy hqy' h => ?_, fun y y' hy hy' hqy hqy' h => ?_⟩
  ·
    have h1 := c₁ y hy hqy
    rw [hfin] at h1
    have h2 := LinearMap.finrank_range_add_finrank_ker (μ.flip y)
    rw [h1, hD.finrank₃] at h2
    exact Submodule.finrank_eq_zero.mp (by omega)
  · have h1 := (c₂ y hy hqy).1
    rwa [hfin] at h1
  · intro x hx
    exact c₅ y hy hqy x (by rw [hker]; exact hx)
  · exact c₇ y y' hy hy' hqy hqy' (Or.inl (by rw [hrange, hrange, h]))
  · exact c₇ y y' hy hy' hqy hqy' (Or.inr (by rw [hker, hker, h]))

end CFSG.RankThree.GF2n.Stroth80.S715L
