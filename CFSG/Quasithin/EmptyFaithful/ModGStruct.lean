module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22
public import CFSG.Quasithin.EmptyFaithful.ModGData

public section

namespace CFSG.Quasithin.ModG

open scoped Pointwise
open MulAction CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

@[expose] def Dg : Subgroup Mg := stabilizer Mg M22Insp.data.B₀

theorem m22_struct :
    ∃ E : Subgroup Mg, Alt2Struct Dg E 6 ∧ (∀ Y : Subgroup Mg, Dg ≤ Y → Y = Dg ∨ Y = ⊤) ∧
      Nat.card Dg = 5760 ∧ ∀ B, B ∈ orbit Mg M22Insp.data.B₀ → B ∈ M22Insp.data.H := by
  classical
  set d := M22Insp.data with hd
  have hv : d.Valid := M22Insp.valid
  have hgens : Subgroup.closure {g | g ∈ d.gens} = ⊤ := M22Insp.hgens
  have hcard : Nat.card Mg = d.H.length * (16 * d.T.length) := M22Insp.hcard
  have hks : ∀ g ∈ d.ks, g ∈ stabilizer ↥NativeSporadic.M22 d.B₀ :=
    fun g hg => mem_stabilizer_iff.2 (hv.ks_fix g hg)
  have horb : ∀ B, B ∈ orbit ↥NativeSporadic.M22 d.B₀ ↔ B ∈ d.H :=
    orbit_eq_of_reach_closed hgens hv.H_reach hv.H_closed
  have hO : BlockOrbits NativeSporadic.M22 d.B₀ d.H d.R₁ d.R₂ d.c₁ d.c₂ :=
    ⟨horb, hv.H_nodup, hv.R₁_nodup, hv.R₂_nodup, hv.R₁_sub, hv.R₂_sub, hv.B₀_not₁, hv.B₀_not₂,
      hv.cover, hv.lev₁, hv.lev₂⟩
  have hsame₁ := hv.R₁_reach.sameOrbit (stabilizer ↥NativeSporadic.M22 d.B₀) hks
  have hsame₂ := hv.R₂_reach.sameOrbit (stabilizer ↥NativeSporadic.M22 d.B₀) hks
  have hNpos : 0 < d.H.length :=
    List.length_pos_of_mem ((horb d.B₀).1 (mem_orbit_self d.B₀))
  have hqpos : 0 < d.T.length := by
    have h1 := Nat.factorial_pos 6
    have h2 := hv.T_len
    omega
  have hKcard : Nat.card (stabilizer ↥NativeSporadic.M22 d.B₀) = 16 * d.T.length := by
    have h1 := Subgroup.card_mul_index (stabilizer ↥NativeSporadic.M22 d.B₀)
    rw [hO.card_stab, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hNpos (h1.trans (mul_comm _ _))
  obtain ⟨E₀, hE₀⟩ := alt2Struct_stab d.B₀ hv.card_B₀ hv.T_len hqpos d.Es hv.Es_len hv.Es_nodup
    hv.Es_fix hv.Es_sq hv.Es_comm
    (by
      obtain ⟨k, hk, e, he, hne⟩ := hv.noncentral
      exact ⟨k, hks k hk, e, he, hne⟩)
    d.t₀ hv.t₀_mem hKcard (le_card_orbit (stabilizer ↥NativeSporadic.M22 d.B₀) hks hv.T_reach hv.T_nodup)
  have hmax := stab_maximal hO hsame₁ hsame₂ hv.harith
  have hT : d.T.length = 360 := by
    have := hv.T_len
    have h6 : Nat.factorial 6 = 720 := by decide
    omega
  refine ⟨E₀, hE₀, hmax, ?_, fun B hB => (horb B).1 hB⟩
  rw [Dg, hKcard, hT]

end CFSG.Quasithin.ModG
