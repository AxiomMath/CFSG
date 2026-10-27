module

public import CFSG.Quasithin.EmptyFaithful.S146P6
public import CFSG.Quasithin.EmptyFaithful.S146P7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section VDec

variable {G : Type} [Group G] [Finite G]

theorem T_fixes_V_mod_Z_P8 {T M : Subgroup G} (S : Setting146 G T M) :
    ∀ τ ∈ T, ∀ y ∈ VZ T M, τ * y * τ⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := by
  intro τ hτ y hy
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hZc2 : Nat.card (quasithinOmegaOneCenter T) = 2 := S.card_Z
  have hVc4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hrel : (quasithinOmegaOneCenter T).relIndex (VZ T M) = 2 := by
    have e := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := VZ T M)
    rw [inf_eq_left.mpr hZV, hZc2, hVc4] at e
    omega
  have hTZ : ∀ τ ∈ T, ∀ z ∈ quasithinOmegaOneCenter T, τ * z * τ⁻¹ = z := by
    intro τ hτ z hz
    have := Subgroup.mem_centralizer_iff.mp (le_centralizer_quasithinOmegaOneCenter T hτ) z hz
    rw [← this]
    group
  by_cases hyZ : y ∈ quasithinOmegaOneCenter T
  · rw [hTZ τ hτ y hyZ, mul_inv_cancel]
    exact (quasithinOmegaOneCenter T).one_mem
  · have hτV : τ * y * τ⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure (quasithinOmegaOneCenter T) M (hTM hτ)) y).mp hy
    have hτZ : τ * y * τ⁻¹ ∉ quasithinOmegaOneCenter T := by
      intro hz
      apply hyZ
      have h1 := hTZ τ⁻¹ (T.inv_mem hτ) _ hz
      have e : τ⁻¹ * (τ * y * τ⁻¹) * τ⁻¹⁻¹ = y := by group
      rw [e] at h1
      rw [h1]
      exact hz
    exact mul_inv_mem_of_relIndex_two hrel hτV hy hτZ hyZ

theorem pCoreOf_fixes_U_mod_Z_P8 {T M H PQ : Subgroup G} {p : ℕ} (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) :
    ∀ q ∈ pCoreOf 2 H, ∀ u ∈ conjClosure (VZ T M) H,
      q * u * q⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
  intro q hq u hu
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le hTsyl
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hcom : ∀ a, a ∈ conjClosure (VZ T M) H → ∀ b, b ∈ conjClosure (VZ T M) H →
      a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUab ha hb
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    (le_conjClosure _ _).trans (le_conjClosure _ _)
  have hHZ : ∀ h ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, h * z * h⁻¹ = z := by
    intro h hh z hz
    have := S146T.comm_Z (hHG hh) hz
    rw [this]
    group
  have hTV := T_fixes_V_mod_Z_P8 S
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have key : (∀ b ∈ quasithinOmegaOneCenter T, b * u = u * b) ∧
      q * u * q⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, y, hy, rfl⟩ := hx
      have hxU : h * y * h⁻¹ ∈ conjClosure (VZ T M) H := mem_conjClosure hh hy
      refine ⟨fun b hb => hcom b (hZU hb) _ hxU, ?_⟩
      have hq' : h⁻¹ * q * h⁻¹⁻¹ ∈ pCoreOf 2 H := hQn h⁻¹ (H.inv_mem hh) q hq
      have h1 := hTV _ (hQT hq') y hy
      have e : q * (h * y * h⁻¹) * q⁻¹ * (h * y * h⁻¹)⁻¹ =
          h * ((h⁻¹ * q * h⁻¹⁻¹) * y * (h⁻¹ * q * h⁻¹⁻¹)⁻¹ * y⁻¹) * h⁻¹ := by group
      rw [e, hHZ h hh _ h1]
      exact h1
    | one => exact ⟨fun b _ => by simp, by simp⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨fun b hb => ?_, comm_mul_mem_P6 ihx.1 ihx.2 ihy.2⟩
      calc b * (x * y) = (b * x) * y := by group
        _ = (x * b) * y := by rw [ihx.1 b hb]
        _ = x * (b * y) := by group
        _ = x * (y * b) := by rw [ihy.1 b hb]
        _ = (x * y) * b := by group
    | inv x _ ih =>
      have hc : ∀ b ∈ quasithinOmegaOneCenter T, b * x⁻¹ = x⁻¹ * b := fun b hb => by
        have := ih.1 b hb
        calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
          _ = x⁻¹ * (b * x) * x⁻¹ := by rw [this]
          _ = x⁻¹ * b := by group
      refine ⟨hc, comm_left_mem_P6 (x := x⁻¹) (y := x) hc ?_ ih.2⟩
      simp
  exact key.2

end VDec

theorem input14617VDec_proved : Input14617VDec := by
  intro G _ _ T M S H PQ p hred w hwU hwT
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hPQH : PQ ≤ H := hred.le
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUG : conjClosure (VZ T M) H ≤ mcOf T := fun u hu => S.mem_mcOf_of_mem_conjClosure hH hu
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  obtain ⟨k, hkE, c, hcU, hcH, hkc⟩ := decomp_mod_central_P7 (G₁ := mcOf T)
    (Z := quasithinOmegaOneCenter T) (U := conjClosure (VZ T M) H) (X := PQ)
    (Q := pCoreOf 2 H) (T := T) hred.prime hred.odd
    (fun x hx b hb => S146T.comm_Z hx hb) hUG (hPQH.trans hHG) (hTH.trans hHG)
    (fun x hx y hy => isElemAbelian_comm hUab hx hy)
    (fun x hx => isElemAbelian_pow_eq_one hUab hx)
    (fun g hg u hu => (Subgroup.mem_normalizer_iff.mp (hHU (hPQH hg)) u).mp hu)
    (fun τ hτ u hu => (Subgroup.mem_normalizer_iff.mp (hHU (hTH hτ)) u).mp hu)
    (fun τ hτ g hg => (Subgroup.mem_normalizer_iff.mp (hred.normal (hTH hτ)) g).mp hg)
    (pCoreOf_fixes_U_mod_Z_P8 S hred)
    (fun g hg q hq => hQn g (hPQH hg) q hq)
    hred.pSec hwU hwT
  refine ⟨k, ?_, c, hcU, fun h hh => hcH h (hred.eq ▸ hh), hkc⟩
  exact Subgroup.commutator_mono le_rfl hPQH hkE

theorem input14617V_proved : Input14617V := input14617V_of_dec input14617VDec_proved

end CFSG.Quasithin
