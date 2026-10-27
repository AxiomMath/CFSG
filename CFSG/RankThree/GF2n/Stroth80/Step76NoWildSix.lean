module

public import CFSG.RankThree.GF2n.Stroth80.Sec7GStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7NoWildPlusSix

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem step76NoWildSixCore_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement)
    (hV : Step71VanishStatement) : Step76NoWildSixCoreStatement := by
  intro G _ _ M Q Z B hc n t hs hno hp x hx hxt w hw
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hvan := hV G M Q Z B hc n t hs hno x hx hxt
  have hQx := comm_conjMod_mem_conj h310chi hc hs hx
  obtain ⟨hxM, g, hg, hq⟩ := hx
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hx0M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hx0Z : ∀ z ∈ Z, (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = z := by
    intro z hz
    have hz' : g⁻¹ * z * g ∈ Z := by simpa using hZn g⁻¹ (M.inv_mem hg) z hz
    have h1 := hc.LB_centralizes_Z ht _ hz'
    calc (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = g * (t * (g⁻¹ * z * g) * t⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
      _ = z := by group
  have hqZ : ∀ z ∈ Z, (x * (g * t * g⁻¹)⁻¹) * z * (x * (g * t * g⁻¹)⁻¹)⁻¹ = z := by
    intro z hz
    have h1 := hc.hyp.toHyp79.V_central hz hq
    rw [← h1]
    group
  have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := by
    intro z hz
    have e : x * z * x⁻¹ = (x * (g * t * g⁻¹)⁻¹) * ((g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹) *
        (x * (g * t * g⁻¹)⁻¹)⁻¹ := by group
    rw [e, hx0Z z hz, hqZ z hz]
  have hx2 : x ^ 2 ∈ Q := by
    have ht2 : t ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB ht
    have hg2 : (g * t * g⁻¹) ^ 2 ∈ Q := by
      rw [conj_pow]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) (t ^ 2)).mp ht2
    have hq2 : (g * t * g⁻¹) * (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hx0M) _).mp hq
    have e : x ^ 2 = (x * (g * t * g⁻¹)⁻¹) * ((g * t * g⁻¹) * (x * (g * t * g⁻¹)⁻¹) *
        (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) ^ 2 := by
      rw [pow_two, pow_two]
      group
    rw [e]
    exact Q.mul_mem (Q.mul_mem hq hq2) hg2
  exact no_wild_plus6_of h34 hA hPts h52a h52b h310chi hc hs hp hxM hxt hvan hxZ hx2 hQx w hw

end CFSG.RankThree.GF2n.Stroth80
