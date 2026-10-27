module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Loc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

theorem centralizer_clause_conj {G : Type*} [Group G] {W : Subgroup G} {a c : G} (hc : c ∈ W)
    (hC : ∀ x ∈ Subgroup.centralizer ({a} : Set G), Nat.Coprime (orderOf x) 7 → x ∈ W) :
    ∀ x ∈ Subgroup.centralizer ({c * a * c⁻¹} : Set G), Nat.Coprime (orderOf x) 7 → x ∈ W := by
  intro x hx hcop
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : c⁻¹ * x * c ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [hx]
      _ = a * (c⁻¹ * x * c) := by group
  have hord : orderOf (c⁻¹ * x * c) = orderOf x := by
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj c⁻¹) x
  have := hC _ hx' (hord ▸ hcop)
  have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [e]
  exact W.mul_mem (W.mul_mem hc this) (W.inv_mem hc)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem rootU_le_of_centralizer (hq3 : p ^ f % 3 = 1) (hp2 : p ≠ 2) (hp7 : p = 7)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hTW : (tSU hF).range ≤ W)
    {a : SU (unitaryInvolution F p f) 3} (haU : a ∈ rootU hF) (haW : a ∈ W)
    (hC : ∀ x ∈ Subgroup.centralizer ({a} : Set (SU (unitaryInvolution F p f) 3)),
      Nat.Coprime (orderOf x) 7 → x ∈ W) : rootU hF ≤ W := by
  have hSU : W ⊓ rootU hF ≤ rootU hF := inf_le_right
  have hSt : ∀ μ ∈ rootsOfUnity (p ^ f + 1) F, ∀ x ∈ W ⊓ rootU hF,
      tSU hF μ * x * (tSU hF μ)⁻¹ ∈ W ⊓ rootU hF := by
    intro μ _ x hx
    have ht : tSU hF μ ∈ W := hTW ⟨μ, rfl⟩
    exact ⟨W.mul_mem (W.mul_mem ht hx.1) (W.inv_mem ht), tSU_conj_mem_rootU hF μ hx.2⟩
  rcases eq_top_or_ca_eq_zero hF hq3 hSU hSt with h | h
  · rw [← h]
    exact inf_le_left
  · exfalso
    have hca : ca a = 0 := h a ⟨haW, haU⟩
    obtain ⟨ν, hνo, -, -⟩ := exists_unit_orderOf_card_add_one hF hp2
    have hν1 : ν ^ (p ^ f + 1) = 1 := hνo ▸ pow_orderOf_eq_one ν
    have hνmem : ν ∈ rootsOfUnity (p ^ f + 1) F := (mem_rootsOfUnity _ _).2 hν1
    have hf0 : f ≠ 0 := fun h0 => by
      have := two_le_prime_pow_of_card hF
      rw [h0, pow_zero] at this
      omega
    have hq7 : 7 ≤ p ^ f := by
      rw [hp7]
      exact Nat.le_self_pow hf0 7
    have hta : tSU hF ν * a * (tSU hF ν)⁻¹ = a := by
      refine eq_of_ca_cb hF (tSU_conj_mem_rootU hF ν haU) haU ?_ ?_
      · rw [ca_tSU_conj_of_mem hF hνmem haU, hca, mul_zero]
      · exact cb_tSU_conj_of_mem hF hνmem haU
    obtain ⟨u, huU, hu0⟩ := exists_ca_ne_zero hF
    have hau : Commute a u := zU_central hF ⟨haU, hca⟩ huU
    have hat : Commute a (tSU hF ν) := (mul_inv_eq_iff_eq_mul.1 hta).symm
    have hcomm : Commute a (u * tSU hF ν * u⁻¹) := (hau.mul_right hat).mul_right hau.inv_right
    have hy : u * tSU hF ν * u⁻¹ ∈ Subgroup.centralizer
        ({a} : Set (SU (unitaryInvolution F p f) 3)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.eq.symm
    have hy7 : Nat.Coprime (orderOf (u * tSU hF ν * u⁻¹)) 7 := by
      have hpow : (u * tSU hF ν * u⁻¹) ^ (p ^ f + 1) = 1 := by
        rw [conj_pow, ← map_pow, hν1, map_one]
        group
      refine Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpow) ?_
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 fun h7 => ?_)
      have h7q : 7 ∣ p ^ f := by
        rw [hp7]
        exact dvd_pow_self 7 hf0
      have : 7 ∣ 1 := (Nat.dvd_add_right h7q).1 h7
      omega
    have hyW := hC _ hy hy7
    have hcW : (u * tSU hF ν * u⁻¹) * (tSU hF ν)⁻¹ ∈ W := W.mul_mem hyW (W.inv_mem (hTW ⟨ν, rfl⟩))
    have hcU : (u * tSU hF ν * u⁻¹) * (tSU hF ν)⁻¹ = u * (tSU hF ν * u⁻¹ * (tSU hF ν)⁻¹) := by
      group
    have hvU : tSU hF ν * u⁻¹ * (tSU hF ν)⁻¹ ∈ rootU hF :=
      tSU_conj_mem_rootU hF ν ((rootU hF).inv_mem huU)
    have hcmem : (u * tSU hF ν * u⁻¹) * (tSU hF ν)⁻¹ ∈ W ⊓ rootU hF :=
      ⟨hcW, by rw [hcU]; exact (rootU hF).mul_mem huU hvU⟩
    have hca0 := h _ hcmem
    rw [hcU, ca_mul hF huU hvU, ca_tSU_conj_of_mem hF hνmem ((rootU hF).inv_mem huU),
      ca_inv hF huU] at hca0
    have h3 : ν ^ 3 = 1 := by
      have : (1 - ((ν ^ 3 : Fˣ) : F)) * ca u = 0 := by linear_combination hca0
      rcases mul_eq_zero.1 this with h1 | h1
      · exact Units.ext (by simpa using (sub_eq_zero.1 h1).symm)
      · exact absurd h1 hu0
    have := Nat.le_of_dvd (by norm_num) (hνo ▸ orderOf_dvd_of_pow_eq_one h3)
    omega

theorem rootU_le_of_seven (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1) (hp7 : p = 7) {ω : Fˣ}
    (hω : orderOf ω = 3) {W : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hNW : normA0 hF ω ≤ W) {a d : SU (unitaryInvolution F p f) 3} (haW : a ∈ W)
    (ha7 : orderOf a = 7) (hdA : d ∈ Subgroup.zpowers (tSU hF ω)) (hd3 : orderOf d = 3)
    (hda : d * a * d⁻¹ = a ^ 2)
    (hC : ∀ x ∈ Subgroup.centralizer ({a} : Set (SU (unitaryInvolution F p f) 3)),
      Nat.Coprime (orderOf x) 7 → x ∈ W) : rootU hF ≤ W := by
  have hTW : (tSU hF).range ≤ W := (range_tSU_le_normA0 hF hω hq3).trans hNW
  have hsW : (sSU : SU (unitaryInvolution F p f) 3) ∈ W :=
    hNW ((mem_normalizer_a0_iff hF hω hq3 sSU).2 (Or.inr ⟨1, one_mem _, (one_mul _).symm⟩))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdA
  have hd : d = tSU hF (ω ^ k) := by rw [map_zpow, hk]
  have hd3' : d ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd3] at this
  have hω3 : (ω ^ k) ^ 3 = 1 := by
    apply tSU_injective hF
    rw [map_pow, map_one, ← hd]
    exact hd3'
  have hω1 : ω ^ k ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    rw [hd, orderOf_one] at hd3
    omega
  have hap : orderOf a = p := by rw [ha7, hp7]
  rw [hd] at hda
  rcases mem_rootU_or_conj hF hω1 hω3 hq3 hap hda with h | h
  · exact rootU_le_of_centralizer hF hq3 hp2 hp7 hTW h haW hC
  · exact rootU_le_of_centralizer hF hq3 hp2 hp7 hTW h
      (W.mul_mem (W.mul_mem hsW haW) (W.inv_mem hsW)) (centralizer_clause_conj hsW hC)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
