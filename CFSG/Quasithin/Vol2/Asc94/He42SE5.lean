module

public import CFSG.Quasithin.Vol2.Asc94.He42TI

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private abbrev he42s5_sing (M : M2) : Prop :=
  M ≠ 0 ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0

private theorem he42s5_factor : ∀ M : M2, he42s5_sing M →
    ∃ P Q : GL2, (P : M2) * (!![0, 1; 0, 0] : M2) * (Q : M2)ᵀ = M := by
  decide +kernel

private theorem he42s5_fin_three : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 →
    he42s5_sing ((g : M2) + (!![0, 1; 0, 0] : M2) + 1) ∧
      he42s5_sing ((1 + (g : M2)) + (!![0, 1; 0, 0] : M2) + 1) := by
  decide +kernel

private theorem he42s5_one : he42s5_sing (1 + (!![0, 1; 0, 0] : M2) + 1) := by
  decide +kernel

private theorem he42s5_e12 : he42s5_sing (!![0, 1; 0, 0] : M2) := by
  decide +kernel

private theorem he42s5_e12_add_one : ((!![0, 1; 0, 0] : M2) + 1).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  decide +kernel

private theorem he42s5_det_of_sing {M : M2} (h : he42s5_sing M) : M.det = 0 := by
  rw [Matrix.det_fin_two]
  exact h.2

theorem HeSetup.fusion_facts (S : HeSetup G) (hfus : S.StepFus) {z : G} (hzZ : z ∈ S.Z)
    (hz : S.m z = Matrix.of ![![0, 1], ![0, 0]]) :
    (∀ y ∈ S.Z, y ≠ 1 → (S.m y).det = 0 → ∃ s : G, s * z * s⁻¹ = y) ∧
      (∀ y ∈ S.Z, (S.m y).det ≠ 0 → ∀ s : G, s * z * s⁻¹ ≠ y) := by
  have hdz : (S.m z).det = 0 := by
    rw [hz]
    exact he42s5_det_of_sing he42s5_e12
  constructor
  · intro y hy hy1 hdy
    have hmy0 : S.m y ≠ 0 := by
      intro h0
      apply hy1
      apply S.hD.hT.minj y hy 1 (Subgroup.one_mem _)
      rw [h0, S.hD.hT.m_one]
    have hsing : he42s5_sing (S.m y) := by
      refine ⟨hmy0, ?_⟩
      have h := hdy
      rw [Matrix.det_fin_two] at h
      exact h
    obtain ⟨P, Q, hPQ⟩ := he42s5_factor (S.m y) hsing
    obtain ⟨n, hn⟩ := S.hD.hT.rho_surjective S.hD.hK (P, Q)
    refine ⟨(n : G), ?_⟩
    have hnz : (n : G) * z * (n : G)⁻¹ ∈ S.Z := S.hD.mem_Z_conj n.2 hzZ
    apply S.hD.hT.minj _ hnz y hy
    rw [S.hD.hT.m_conj S.N S.hD.hK.norm n hzZ, hn, hz]
    exact hPQ
  · intro y hy hdy s hsy
    have hconj : s⁻¹ * y * s = z := by
      rw [← hsy]
      group
    obtain ⟨n, hnN, hn⟩ := hfus y hy z hzZ s hconj
    have hn' : n⁻¹ ∈ S.N := S.N.inv_mem hnN
    have hm := S.hD.hT.m_conj S.N S.hD.hK.norm ⟨n⁻¹, hn'⟩ hy
    rw [show ((⟨n⁻¹, hn'⟩ : S.N) : G) = n⁻¹ from rfl, inv_inv, hn] at hm
    obtain ⟨P, Q, hPQ⟩ : ∃ P Q : GL2, S.m z = (P : M2) * S.m y * (Q : M2)ᵀ := ⟨_, _, hm⟩
    have hPd : (P : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
    have hQd : (Q : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit).ne_zero
    have h0 := hdz
    rw [hPQ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h0
    exact mul_ne_zero (mul_ne_zero hPd hdy) hQd h0

theorem HeSetup.fix_of_centralizes_B (S : HeSetup G) (hB : S.BaseFacts) (hfus : S.StepFus) {z : G}
    (hzZ : z ∈ S.Z) (hz : S.m z = Matrix.of ![![0, 1], ![0, 0]])
    {c : G} (hcB : ∀ b ∈ S.B, c * b = b * c) (hc : c * z * c⁻¹ * z⁻¹ ∈ S.B) :
    c * z * c⁻¹ = z := by
  obtain ⟨hA, hA'⟩ := S.fusion_facts hfus hzZ hz
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  obtain ⟨b, hbB, hbm⟩ := S.hD.exists_b S.hxN S.hxa S.hx3
  have hbm' : S.m b = S.g.val := hbm
  have hbZ : b ∈ S.Z := hbB.1
  have hb1 : b ≠ 1 := by
    intro h
    apply Units.ne_zero S.g
    rw [← hbm', h, S.hD.hT.m_one]
  have hba : b ≠ S.a := by
    intro h
    apply hg1
    apply Units.ext
    rw [Units.val_one, ← hbm', h, S.hD.ham]
  have hBel := S.hD.B_elems S.hxN S.hxa S.hx3 hbB hb1 hba
  have haB : S.a ∈ S.B := S.hD.a_mem_B S.hxN S.hxa S.hx3
  have hcA : c * S.a * c⁻¹ = S.a := by
    rw [hcB S.a haB, mul_inv_cancel_right]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : G, b₀ = c * z * c⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hc' : b₀ ∈ S.B := by
    rw [hb₀]
    exact hc
  have hb₀Z : b₀ ∈ S.Z := hc'.1
  have hcz : c * z * c⁻¹ = b₀ * z := by
    rw [hb₀]
    group
  have hcza : c * (z * S.a) * c⁻¹ = b₀ * z * S.a := by
    calc c * (z * S.a) * c⁻¹ = (c * z * c⁻¹) * (c * S.a * c⁻¹) := by group
      _ = b₀ * z * S.a := by rw [hcz, hcA]
  have hmy : ∀ x ∈ S.Z, S.m (x * z * S.a) = S.m x + Matrix.of ![![0, 1], ![0, 0]] + 1 := by
    intro x hx
    rw [S.hD.hT.mmul (x * z) (S.Z.mul_mem hx hzZ) S.a S.hD.ha, S.hD.hT.mmul x hx z hzZ, hz,
      S.hD.ham]
  have contra : ∀ y : G, y = b₀ * z * S.a → S.m y ≠ 0 → (S.m y).det = 0 → False := by
    intro y hy hy0 hdy
    have hyZ : y ∈ S.Z := by
      rw [hy]
      exact S.Z.mul_mem (S.Z.mul_mem hb₀Z hzZ) S.hD.ha
    have hy1 : y ≠ 1 := fun h => hy0 (by rw [h, S.hD.hT.m_one])
    obtain ⟨s, hs⟩ := hA y hyZ hy1 hdy
    have hyc : y = c * (z * S.a) * c⁻¹ := hy.trans hcza.symm
    have ht : (c⁻¹ * s) * z * (c⁻¹ * s)⁻¹ = z * S.a := by
      calc (c⁻¹ * s) * z * (c⁻¹ * s)⁻¹ = c⁻¹ * (s * z * s⁻¹) * c := by group
        _ = c⁻¹ * y * c := by rw [hs]
        _ = c⁻¹ * (c * (z * S.a) * c⁻¹) * c := by rw [hyc]
        _ = z * S.a := by group
    have hdza : (S.m (z * S.a)).det ≠ 0 := by
      rw [S.hD.hT.mmul z hzZ S.a S.hD.ha, hz, S.hD.ham]
      exact he42s5_e12_add_one
    exact hA' (z * S.a) (S.Z.mul_mem hzZ S.hD.ha) hdza (c⁻¹ * s) ht
  rcases hBel b₀ hc' with h1 | h1 | h1 | h1
  · rw [hcz, h1, one_mul]
  ·
    exfalso
    have hs : he42s5_sing (S.m (b₀ * z * S.a)) := by
      rw [hmy b₀ hb₀Z, h1, S.hD.ham]
      exact he42s5_one
    exact contra (b₀ * z * S.a) rfl hs.1 (he42s5_det_of_sing hs)
  ·
    exfalso
    have hs : he42s5_sing (S.m (b₀ * z * S.a)) := by
      rw [hmy b₀ hb₀Z, h1, hbm']
      exact (he42s5_fin_three S.g hg3 hg1).1
    exact contra (b₀ * z * S.a) rfl hs.1 (he42s5_det_of_sing hs)
  ·
    exfalso
    have hs : he42s5_sing (S.m (b₀ * z * S.a)) := by
      rw [hmy b₀ hb₀Z, h1, S.hD.hT.mmul S.a S.hD.ha b hbZ, S.hD.ham, hbm']
      exact (he42s5_fin_three S.g hg3 hg1).2
    exact contra (b₀ * z * S.a) rfl hs.1 (he42s5_det_of_sing hs)

end CFSG.Quasithin.A94.He42
