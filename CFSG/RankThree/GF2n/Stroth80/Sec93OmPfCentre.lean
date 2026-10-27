module

public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem false_of_comm_CN_le_centre (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {x : G} (hs : Sec9Hyp hc n x)
    {Z0x : Subgroup G} (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q)
    (hcomm : ∀ f ∈ hc.CN x, ∀ ρ ∈ Rt M (LB M Q B) x, ⁅f, ρ⁆ ∈ Z0x) : False := by
  classical
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hs5.mem
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n x hs
  have hrR : r ∈ Rt M (LB M Q B) x := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M x hrR
  obtain ⟨hprod, hcomm', -⟩ := sec9_N51 h34 h311a hNC hs hr
  have heq := isCentrePre_eq_inf91 hs hr hprod hcomm' hZ0x
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
  have hZL : Z0x ≤ LB M Q B := by rw [heq]; exact inf_le_left
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M x hρ)) y).mp hy
  have hZnorm : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ z ∈ Z0x, ρ * z * ρ⁻¹ ∈ Z0x := fun ρ hρ z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZ0x.mem_normalizer hQn hρ) z).mp hz
  have hLN : ∀ a ∈ LB M Q B ⊓ hc.CN x, a ∈ Z0x := by
    intro a ha
    have hcr : ⁅a, r⁆ ∈ Z0x := hcomm a ha.2 r hrR
    have hrar : r * a * r⁻¹ = ⁅r, a⁆ * a := by
      simp only [commutatorElement_def]; group
    have hra : ⁅r, a⁆ ∈ Z0x := by
      rw [← commutatorElement_inv]
      exact Z0x.inv_mem hcr
    have hL1 : r * a * r⁻¹ ∈ LB M Q B := by
      rw [hrar]
      exact (LB M Q B).mul_mem (hZL hra) ha.1
    have hL2 : r * a * r⁻¹ ∈ LB M Q (conjSubgroup r B) := by
      rw [hLA, mem_conjSubgroup]
      have e : r⁻¹ * (r * a * r⁻¹) * r = a := by group
      rw [e]
      exact ha.1
    have hmem : r * a * r⁻¹ ∈ Z0x := by
      rw [heq]
      exact Subgroup.mem_inf.mpr ⟨hL1, hL2⟩
    have h4 := hZnorm r⁻¹ ((Rt M (LB M Q B) x).inv_mem hrR) _ hmem
    have e : r⁻¹ * (r * a * r⁻¹) * r⁻¹⁻¹ = a := by group
    rw [e] at h4
    exact h4
  have hLAN : ∀ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN x, b ∈ Z0x := by
    intro b hb
    obtain ⟨hbA, hbN⟩ := Subgroup.mem_inf.mp hb
    have hb1 : r⁻¹ * b * r ∈ LB M Q B := by
      rw [hLA, mem_conjSubgroup] at hbA
      exact hbA
    have hb2 : r⁻¹ * b * r ∈ hc.CN x := by
      have h5 := hc.CN_conj_mem hxL ((Rt M (LB M Q B) x).inv_mem hrR) hbN
      have e : r⁻¹⁻¹ ⁻¹ = r⁻¹⁻¹⁻¹ := rfl
      simpa using h5
    have h3 := hLN _ (Subgroup.mem_inf.mpr ⟨hb1, hb2⟩)
    have h6 := hZnorm r hrR _ h3
    have e : r * (r⁻¹ * b * r) * r⁻¹ = b := by group
    rw [e] at h6
    exact h6
  have hNZ : hc.CN x ≤ Z0x := by
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod f hf
    exact Z0x.mul_mem (hLN a ha) (hLAN b hb)
  have hcard := card_centrePre_le91 h34 h311bCard hs hZ0x hZL
  have hle := Subgroup.card_le_of_le hNZ
  have hlarge := hs.large_t
  omega

end HS9

end CFSG.RankThree.GF2n.Stroth80
