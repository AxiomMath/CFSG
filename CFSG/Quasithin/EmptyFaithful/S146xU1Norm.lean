module

public import CFSG.Quasithin.EmptyFaithful.S146xU1Sec
public import CFSG.Quasithin.EmptyFaithful.S146xU1Fix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Normal

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.u1_normal (S : Setting146 G T M) (c19 : Conc14619 T M)
    {K U₁ U₂ : Subgroup G} {s u : G} (hK : K ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K)
    (hdec : IsDecompUK T M K U₁ U₂ s) (hKn : mcOf T ≤ Subgroup.normalizer (K : Set G))
    {L : Subgroup G} (hLH : L ≤ mcOf T) (hLU : L ≤ Subgroup.normalizer (U₁ : Set G))
    (hHL : ∀ h ∈ mcOf T, ∃ a ∈ L, ∃ b ∈ T, h = a * b)
    (huU : u ∈ U₁) (hunc : ¬ ⁅Subgroup.zpowers u, K⁆ ≤ Zz)
    (hN : T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u) :
    IsSylowTwoOf (tU T u) (mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) ∧
      (tZero T u).relIndex T = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T (mcOf T) := S.isSylowTwoOf_mcOf
  obtain ⟨hSec, hU₁U, hU₂U⟩ := S.sec8_of_decomp hK hL3 hdec
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hK
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  have hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz := fun p hp w hw =>
    S.comm_mem_Z hG (hU₁U hw) (hQK hp)
  have h168 := relIndex_pCoreOf_of_kbarIsL3Two hL3
  have hout : KbarInducesOuter K s := by
    rcases hdec.dynkin with ⟨-, ho⟩ | ⟨h6, -⟩
    · exact ho
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6).elim
  have hinf : U₁ ⊓ U₂ ≤ Zz :=
    inf_U₂_le_of_decomp hSec hsimple hQ' h168 hdec.mem.1 hdec.mem.2 hout hdec.conj hdec.Z₂
  have huZ : u ∉ Zz := by
    intro hu
    apply hunc
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hu) le_rfl).trans
      (S145.commutator_le_of_le_normalizer hSec.KZ)
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U huU)
  have hUZ : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hTZ : T ≤ Subgroup.normalizer (Zz : Set G) := fun t ht => S.normalizer_Z.ge (hTH ht)
  have hTU : T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun t ht =>
    le_normalizer_conjClosure _ _ (hTH ht)
  have hfix : ∀ p ∈ T ⊓ K, p * u * p⁻¹ * u⁻¹ ∈ Zz := fun p hp =>
    (hN ⟨hp.1, hSec.KU hp.2⟩).2.2 u (Subgroup.mem_zpowers u)
  let ρ : ↥T →* MulAut ↥(tildeOf Zz (uOfL22 T M)) := secRho hTZ hTU
  let _ : MulAction ↥T ↥(tildeOf Zz (uOfL22 T M)) := MulAction.compHom _ ρ
  have hsmul : ∀ (t : ↥T) (w : ↥(tildeOf Zz (uOfL22 T M))), t • w = ρ t w := fun t w => rfl
  have huU' : u ∈ uOfL22 T M := hU₁U huU
  have hsu : s * u * s⁻¹ ∈ uOfL22 T M := by
    have hsU : s ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hTU hdec.mem.1
    have h1 : s * u * s⁻¹ ∈ conjSub s (uOfL22 T M) := mul_mem_conjSub huU'
    rwa [F7.conjSub_eq_of_mem_normalizer hsU] at h1
  have hsuu : u * (s * u * s⁻¹) ∈ uOfL22 T M := (uOfL22 T M).mul_mem huU' hsu
  set ω : ↥(tildeOf Zz (uOfL22 T M)) := tildeElt hUZ u huU' with hω
  set ω' : ↥(tildeOf Zz (uOfL22 T M)) := tildeElt hUZ (s * u * s⁻¹) hsu with hω'
  set ω'' : ↥(tildeOf Zz (uOfL22 T M)) := tildeElt hUZ (u * (s * u * s⁻¹)) hsuu with hω''
  have hT3 : ∀ t : ↥T, t • ω = ω ∨ t • ω = ω' ∨ t • ω = ω'' := by
    intro t
    have hc := S.conj_mem_classes hK hSec hsimple hQ' h168 hU₁U hU₂U hdec.sup hdec.conj hdec.Z₂
      hinf hdec.mem.1 hdec.mem.2 (fun t ht => hKn (hTH ht)) huU huZ hfix t.2
    rcases hc with h | h | h
    · left
      exact (secRho_apply_tildeElt_iff hTZ hTU hUZ t u huU').mpr h
    · right; left
      refine (secRho_apply_tildeElt_eq_iff hTZ hTU hUZ t huU' hsu).mpr ?_
      simpa [mul_inv_rev] using Subgroup.inv_mem _ h
    · right; right
      refine (secRho_apply_tildeElt_eq_iff hTZ hTU hUZ t huU' hsuu).mpr ?_
      simpa [mul_inv_rev] using Subgroup.inv_mem _ h
  have hne : ω ≠ ω' := by
    intro h
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz (uOfL22 T M)) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    have h2 : u⁻¹ * (s * u * s⁻¹) ∈ Zz := by
      have := secMk_eq_secMk_iff.mp (by simpa [hω, hω', tildeElt] using h1)
      simpa using this
    have hv₂ : s * u * s⁻¹ ∈ U₂ := by
      rw [hdec.conj]
      exact mul_mem_conjSub huU
    have hv₁ : s * u * s⁻¹ ∈ U₁ := by
      have e : s * u * s⁻¹ = u * (u⁻¹ * (s * u * s⁻¹)) := by group
      rw [e]
      exact U₁.mul_mem huU (hSec.le h2)
    have hvZ : s * u * s⁻¹ ∈ Zz := hinf ⟨hv₁, hv₂⟩
    apply huZ
    have e : u = (s * u * s⁻¹) * (u⁻¹ * (s * u * s⁻¹))⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hvZ (Subgroup.inv_mem _ h2)
  have ht0 : ∃ t : ↥T, t • ω = ω' := by
    refine ⟨⟨s, hdec.mem.1⟩, ?_⟩
    refine (secRho_apply_tildeElt_eq_iff hTZ hTU hUZ ⟨s, hdec.mem.1⟩ huU' hsu).mpr ?_
    show (s * u * s⁻¹)⁻¹ * (s * u * s⁻¹) ∈ Zz
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  obtain ⟨hidx, -⟩ := index_stabilizer_eq_two_and_orbit hT2 hne hT3 ht0
  have hstab : (tZero T u).subgroupOf T = MulAction.stabilizer ↥T ω := by
    ext t
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, mem_tZero_iff huG t.2, hsmul]
    exact (secRho_apply_tildeElt_iff hTZ hTU hUZ t u huU').symm
  have h2 : (tZero T u).relIndex T = 2 := by
    unfold Subgroup.relIndex
    rw [hstab]
    exact hidx
  refine ⟨S.isSylowTwoOf_tU_of_normalizes huG ?_ hLH hLU hHL hN, h2⟩
  exact fun x hx => hSec.mem_normalizer_of_mem_centralizerMod hKn huU huZ hx

end Normal

end CFSG.Quasithin
