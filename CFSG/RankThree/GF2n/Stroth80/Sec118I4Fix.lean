module

public import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

omit [(Q.subgroupOf M).Normal] [Finite K] in
theorem Ctx.mem_centralizer_B_of_odd_fix (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {b₀ : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b₀)
    {g : G} (hgH : g ∈ H0 M Z) (hodd : Odd (orderOf g)) (hfix : φ ⟨g, hgH⟩ b₀ = b₀) :
    g ∈ Subgroup.centralizer (B : Set G) := by
  classical
  have hZ2 : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    have := hc.hyp.isElemAbelian_Z.2 z hz
    rwa [sq] at this
  have hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hgH.2 z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have key : ∀ b ∈ B, g * (g * b * g⁻¹) * g⁻¹ = b := by
    intro b hb
    have hbQ : b ∈ Q := hc.le hb
    have hxQ : g * b * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgH.1) b).mp hbQ
    have hπ : M₀.π b = M₀.π (g * b * g⁻¹) := by
      rw [hφπ ⟨g, hgH⟩ b hbQ]
      obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hb hbQ)
      rw [hs, map_smul, hfix]
    have hz : b⁻¹ * (g * b * g⁻¹) ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hbQ hxQ).mp hπ
    set z := b⁻¹ * (g * b * g⁻¹) with hzdef
    have e1 : g * b * g⁻¹ = b * z := by rw [hzdef]; group
    have e2 : g * (b * z) * g⁻¹ = (g * b * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e1, e2, hgZ z hz, e1, mul_assoc, hZ2 z hz, mul_one]
  have hg2 : g ^ 2 ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h2 : g ^ 2 * b * (g ^ 2)⁻¹ = b := by
      have h3 : g ^ 2 * b * (g ^ 2)⁻¹ = g * (g * b * g⁻¹) * g⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      rw [h3]
      exact key b hb
    have h4 : g ^ 2 * b = b * g ^ 2 := by
      calc g ^ 2 * b = (g ^ 2 * b * (g ^ 2)⁻¹) * g ^ 2 := by simp
        _ = b * g ^ 2 := by rw [h2]
    exact h4.symm
  obtain ⟨k, hk⟩ := hodd
  have hgpow : g = (g ^ 2) ^ (k + 1) := by
    have h1 := pow_orderOf_eq_one g
    rw [hk] at h1
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h1, one_mul]
  rw [hgpow]
  exact Subgroup.pow_mem _ hg2 _

omit [Finite K] in
theorem conj_mem_QB_of_mem_normalizer {g : G} (hgB : g ∈ Subgroup.normalizer (B : Set G))
    {x : G} (hx : x ∈ QB B) : g * x * g⁻¹ ∈ QB B := by
  have h1 : conjSubgroup g⁻¹ B = B := by
    ext y
    rw [mem_conjSubgroup, inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp hgB y).symm
  have h2 := QB_conj g⁻¹ B
  rw [h1] at h2
  have h3 : x ∈ conjSubgroup g⁻¹ (QB B) := by rw [← h2]; exact hx
  rwa [mem_conjSubgroup, inv_inv] at h3

omit [(Q.subgroupOf M).Normal] [Finite K] in
theorem Ctx.act_mem_img_inf_QB_of_normalizer (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {g : G} (hgH : g ∈ H0 M Z) (hgB : g ∈ Subgroup.normalizer (B : Set G))
    {v : M₀.E} (hv : v ∈ M₀.img (Q ⊓ QB B)) : φ ⟨g, hgH⟩ v ∈ M₀.img (Q ⊓ QB B) := by
  obtain ⟨x, hxS, hxQ, rfl⟩ := hv
  rw [← hφπ ⟨g, hgH⟩ x hxQ]
  have hgxQ : g * x * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgH.1) x).mp hxQ
  exact M₀.pi_mem_img ⟨hgxQ, conj_mem_QB_of_mem_normalizer hgB (Subgroup.mem_inf.mp hxS).2⟩ hgxQ

omit [(Q.subgroupOf M).Normal] in
theorem Ctx.conj_mem_LB_of_normalizer (hc : Ctx M Q Z B) {g : G} (hgM : g ∈ M)
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) {l : G} (hl : l ∈ LB M Q B) :
    g * l * g⁻¹ ∈ LB M Q B := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have e : g * (s * y) * g⁻¹ = (g * s * g⁻¹) * (g * y * g⁻¹) := by group
  rw [e]
  have h1 : g * s * g⁻¹ ∈ LB M Q B := by
    refine le_sup_right (a := Q) ⟨conj_mem_QB_of_mem_normalizer hgB hs.1, ?_⟩
    exact M.mul_mem (M.mul_mem hgM hs.2) (M.inv_mem hgM)
  have h2 : g * y * g⁻¹ ∈ LB M Q B := by
    refine le_sup_left (b := QB B ⊓ M) ?_
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) y).mp hy
  exact (LB M Q B).mul_mem h1 h2

end CFSG.RankThree.GF2n.Stroth80
