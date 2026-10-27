module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dat
public import CFSG.Quasithin.EmptyFaithful.S14612GB1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section M

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9_Z_le_uK (h5 : Stage1461Five) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    quasithinOmegaOneCenter T ≤ uK T M H := by
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨z₀, hz₀Y, hz₀Q, hz₀odd⟩ :=
    exists_odd_not_mem_of_pSec_GB1 hred.prime hred.odd hred.lt hred.pSec
  have hX1 : oTwoUpper PQ ≠ ⊥ := by
    intro hbot
    have hzX : z₀ ∈ oTwoUpper PQ := mem_oTwoUpper_of_odd hz₀Y hz₀odd
    rw [hbot, Subgroup.mem_bot] at hzX
    exact hz₀Q (hzX ▸ (pCoreOf 2 H).one_mem)
  have hXF : oTwoUpper PQ ≤ oTwoFstarIn H :=
    ((oTwoUpper_le PQ).trans hred.le_oTwoPIn).trans (oTwoPIn_le_oTwoFstarIn hred.prime H)
  have hZle : quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper PQ⁆ :=
    S.lemma_14_6_2 hH (h5 G T M S H hH) hX1 (S146A.oTwoUpper_idem PQ) hXF
      (hred.lt.le.trans (le_normalizer_oTwoUpper PQ))
  exact hZle.trans (Subgroup.commutator_mono le_rfl ((oTwoUpper_le PQ).trans hred.le))

theorem e9_not_centralizer_le_M (S : Setting146 G T M) (h2 : Stage1461Two)
    (hred : IsRedCE T M H PQ p) {R₁ R₂ : Subgroup G} (hR₂ : IsPlaneSub T M H PQ R₂)
    (hcent : ⁅uHi T M H R₁, R₂⁆ ≤ quasithinOmegaOneCenter T) {u : G} (hu : u ∈ uHi T M H R₁) :
    ¬ Subgroup.centralizer ({u} : Set G) ≤ M := by
  intro hCM
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hR₂PQ : R₂ ≤ PQ := hR₂.2.1
  have hR₂H : R₂ ≤ H := hR₂PQ.trans hred.le
  have hlt : pCoreOf 2 H < R₂ := by
    refine lt_of_le_of_ne hR₂.1 fun e => ?_
    have h3 := hR₂.2.2.1
    rw [← e, Subgroup.relIndex_self] at h3
    omega
  obtain ⟨z, hz2, hzQ, hzodd⟩ := exists_odd_not_mem_of_pSec_GB1 hred.prime hred.odd hlt
    (fun x hx => hred.pSec x (hR₂PQ hx))
  have hzK : z ∈ oTwoUpper R₂ := mem_oTwoUpper_of_odd hz2 hzodd
  have hK2 : oTwoUpper R₂ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
    have hc : u * x * u⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T :=
      hcent (Subgroup.commutator_mem_commutator hu hx)
    set c := u * x * u⁻¹ * x⁻¹ with hcdef
    have hcx : x * c = c * x := S146T.comm_Z (hHG (hR₂H hx)) hc
    have hc2 : c * c = 1 := by
      have := S146T.Z_sq hc
      simpa [pow_two] using this
    have e1 : u * x = c * x * u := by rw [hcdef]; group
    show x ^ 2 ^ 1 ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hx2 : x ^ 2 ^ 1 = x * x := by rw [pow_one, pow_two]
    rw [hx2]
    calc w * (x * x) = (w * x) * x := by group
      _ = (c * x * w) * x := by rw [e1]
      _ = c * x * (w * x) := by group
      _ = c * x * (c * x * w) := by rw [e1]
      _ = c * (x * c) * x * w := by group
      _ = c * (c * x) * x * w := by rw [hcx]
      _ = (c * c) * (x * x) * w := by group
      _ = x * x * w := by rw [hc2]; group
  have hzM : z ∈ M := hCM (hK2 hzK)
  have hzP : z ∈ oTwoPIn p H := hred.le_oTwoPIn (hR₂PQ hz2)
  have hint : z ∈ oTwoPIn p H ⊓ M := ⟨hzP, hzM⟩
  rw [h2 G T M S H hH p hred.prime hred.odd] at hint
  exact hzQ hint

end M

end CFSG.Quasithin
