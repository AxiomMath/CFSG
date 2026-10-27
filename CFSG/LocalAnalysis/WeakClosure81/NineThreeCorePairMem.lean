module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairA
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreEnum

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_pair_exists_enum (hc : Nine3Choice V T A K S X p g x)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) :
    ∃ (n : ℕ) (B : Fin (n + 1) → Subgroup G) (σ : Equiv.Perm (Fin (n + 1)))
      (bb : Fin (n + 1) → G), (n = 2 ∨ n = 4) ∧ Nat.card ↥(nineDelta V S) = n + 1 ∧
        Nine3PairEnum V K S A g n B σ bb := by
  classical
  obtain ⟨n, B, σ, hn, hΩcard, hB0, hB1, hBinj, hBmem, hBsurj, hBΩ, hBσ, hσ0, hσ1⟩ :=
    nine3_exists_enum hc h35
  have hΔcard : Nat.card ↥(nineDelta V S) = n + 1 := by
    obtain ⟨m, hmΩ, hmΔ⟩ := hc.core.card_nineOmegaIn
    omega
  have hex : ∀ k : Fin (n + 1), ∃ b : G,
      (k ≠ 0 → b ∈ B k ∧ b ∉ pCoreOf 2 K) ∧ (k = 0 → b = 1) := by
    intro k
    by_cases hk : k = 0
    · exact ⟨1, fun h => absurd hk h, fun _ => rfl⟩
    · obtain ⟨b, hb⟩ := hc.core.exists_not_mem_pCoreOf (hBΩ k hk)
      exact ⟨b, fun _ => hb, fun h => absurd h hk⟩
  let bb : Fin (n + 1) → G := fun k => Classical.choose (hex k)
  have hbb0 : bb 0 = 1 := (Classical.choose_spec (hex 0)).2 rfl
  have hbbmem : ∀ k, k ≠ 0 → bb k ∈ B k ∧ bb k ∉ pCoreOf 2 K :=
    fun k hk => (Classical.choose_spec (hex k)).1 hk
  have hsurj : ∀ D ∈ nineOmegaIn V K S, ∃ k, k ≠ 0 ∧ B k = D := by
    intro D hD
    obtain ⟨k, hk⟩ := hBsurj D (hc.core.mem_nineDelta_iff.mpr (Or.inr hD))
    refine ⟨k, fun hk0 => ?_, hk⟩
    rw [hk0, hB0] at hk
    exact hc.core.V_not_mem_nineOmegaIn (hk.symm ▸ hD)
  exact ⟨n, B, σ, bb, hn, hΔcard,
    { B0 := hB0, B1 := hB1, inj := hBinj, mem := hBmem, Ω := hBΩ, surj := hsurj,
      conj := hBσ, σ0 := hσ0, σ1 := hσ1, bb_mem := hbbmem, bb0 := hbb0 }⟩

theorem nine3_pair_phi_mem (hI : Nine3IFacts V K S) {n : ℕ} {B : Fin (n + 1) → Subgroup G}
    {σ : Equiv.Perm (Fin (n + 1))} {bb : Fin (n + 1) → G}
    (he : Nine3PairEnum V K S A g n B σ bb) {i : G} (hi : i ∈ nineI V K) (k : Fin (n + 1)) :
    ⁅i, bb k⁆ ∈ nine3_pair_P V K g B k := by
  by_cases hk : k = 0
  · subst hk
    rw [he.bb0, commutatorElement_one_right]
    simp only [nine3_pair_P, if_pos rfl]
    exact (nineV1 V K g).one_mem
  · have hmem : ⁅i, bb k⁆ ∈ ⁅nineI V K, B k⁆ :=
      Subgroup.commutator_mem_commutator hi (he.bb_mem k hk).1
    rw [hI.comm (B k) (he.Ω k hk)] at hmem
    simpa only [nine3_pair_P, if_neg hk] using hmem

theorem nine3_pair_phi_mul (hI : Nine3IFacts V K S) {i i' b : G} (hi : i ∈ nineI V K)
    (hi' : i' ∈ nineI V K) (hb : b ∈ K) : ⁅i * i', b⁆ = ⁅i, b⁆ * ⁅i', b⁆ := by
  have hconjI : conjSubgroup (nineI V K) b = nineI V K := Nine3Core.conjSubgroup_nineI hb
  have hci' : ⁅i', b⁆ ∈ nineI V K := by
    have hx : i'⁻¹ ∈ conjSubgroup (nineI V K) b := by
      rw [hconjI]; exact (nineI V K).inv_mem hi'
    have h2 : b * i'⁻¹ * b⁻¹ ∈ nineI V K := mem_conjSubgroup_iff.mp hx
    have h3 := (nineI V K).mul_mem hi' h2
    simpa [commutatorElement_def, mul_assoc] using h3
  have hci : ⁅i, b⁆ ∈ nineI V K := by
    have hx : i⁻¹ ∈ conjSubgroup (nineI V K) b := by
      rw [hconjI]; exact (nineI V K).inv_mem hi
    have h2 : b * i⁻¹ * b⁻¹ ∈ nineI V K := mem_conjSubgroup_iff.mp hx
    have h3 := (nineI V K).mul_mem hi h2
    simpa [commutatorElement_def, mul_assoc] using h3
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hconj : i * ⁅i', b⁆ * i⁻¹ = ⁅i', b⁆ := by
    rw [CFSG.Open.IsElemAbelian.comm hI.abelian hi hci']
    group
  rw [hconj]
  exact (CFSG.Open.IsElemAbelian.comm hI.abelian hci hci').symm

theorem nine3_pair_psi_mem (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {n : ℕ} {B : Fin (n + 1) → Subgroup G} {σ : Equiv.Perm (Fin (n + 1))}
    {bb : Fin (n + 1) → G} (he : Nine3PairEnum V K S A g n B σ bb) {j : G}
    (hj : j ∈ conjSubgroup (nineI V K) g) (l : Fin (n + 1)) :
    ⁅g⁻¹ * bb (σ.symm l) * g, j⁆ ∈ nine3_pair_P V K g B l := by
  by_cases hl1 : l = 1
  · subst hl1
    have hk0 : σ.symm (1 : Fin (n + 1)) = 0 := by
      rw [Equiv.symm_apply_eq]; exact he.σ0.symm
    have hc1 : g⁻¹ * bb (σ.symm 1) * g = 1 := by rw [hk0, he.bb0]; group
    rw [hc1, commutatorElement_one_left]
    have h10 : (1 : Fin (n + 1)) ≠ 0 := by
      intro h
      exact hc.core.ne (by rw [← he.B1, congrArg B h, he.B0])
    simp only [nine3_pair_P, if_neg h10]
    exact ⟨(B 1).one_mem, (pCoreOf 2 K).one_mem⟩
  · have hk_ne : σ.symm l ≠ 0 := by
      intro h
      exact hl1 (by rw [← Equiv.apply_symm_apply σ l, h, he.σ0])
    have hw : g * j * g⁻¹ ∈ nineI V K := mem_conjSubgroup_iff.mp hj
    have hbb : bb (σ.symm l) ∈ B (σ.symm l) := (he.bb_mem _ hk_ne).1
    have hcomm : ⁅g * j * g⁻¹, bb (σ.symm l)⁆ ∈ B (σ.symm l) ⊓ pCoreOf 2 K := by
      have h := Subgroup.commutator_mem_commutator hw hbb
      rwa [hI.comm (B (σ.symm l)) (he.Ω _ hk_ne)] at h
    have hcomm' : ⁅bb (σ.symm l), g * j * g⁻¹⁆ ∈ B (σ.symm l) ⊓ pCoreOf 2 K := by
      have h := (B (σ.symm l) ⊓ pCoreOf 2 K).inv_mem hcomm
      rwa [commutatorElement_inv] at h
    have hconj : g * ⁅g⁻¹ * bb (σ.symm l) * g, j⁆ * g⁻¹ =
        ⁅bb (σ.symm l), g * j * g⁻¹⁆ := by
      have hcc := conjugate_commutatorElement (g₃ := g⁻¹) (g₁ := bb (σ.symm l))
        (g₂ := g * j * g⁻¹)
      rw [inv_inv] at hcc
      rw [show g⁻¹ * (g * j * g⁻¹) * g = j by group] at hcc
      rw [← hcc]; group
    have hmem : ⁅g⁻¹ * bb (σ.symm l) * g, j⁆ ∈
        conjSubgroup (B (σ.symm l) ⊓ pCoreOf 2 K) g := by
      rw [mem_conjSubgroup_iff, hconj]
      exact hcomm'
    have hBg : conjSubgroup (B (σ.symm l)) g = B l := by
      rw [he.conj (σ.symm l), Equiv.apply_symm_apply]
    rw [E3.conjSubgroup_inf, hBg] at hmem
    by_cases hl0 : l = 0
    · subst hl0
      simp only [nine3_pair_P, if_pos rfl]
      rw [he.B0] at hmem
      exact hmem
    · have hBlA : B l ≠ A := by
        intro h
        exact hl1 (he.inj (h.trans he.B1.symm))
      have hPin : B l ⊓ pCoreOf 2 K = B l ⊓ conjSubgroup (pCoreOf 2 K) g :=
        hc.inf_pCoreOf_eq_inf_conj hI (he.Ω l hl0) hBlA
      simp only [nine3_pair_P, if_neg hl0]
      rwa [← hPin] at hmem

theorem nine3_pair_psi_mul (hI : Nine3IFacts V K S) {b j j' : G} (hb : b ∈ K)
    (hj : j ∈ conjSubgroup (nineI V K) g) (hj' : j' ∈ conjSubgroup (nineI V K) g) :
    ⁅g⁻¹ * b * g, j * j'⁆ = ⁅g⁻¹ * b * g, j⁆ * ⁅g⁻¹ * b * g, j'⁆ := by
  have hjI : g * j' * g⁻¹ ∈ nineI V K := mem_conjSubgroup_iff.mp hj'
  have hcommI : ⁅b, g * j' * g⁻¹⁆ ∈ nineI V K := by
    have hby : b * (g * j' * g⁻¹) * b⁻¹ ∈ nineI V K := by
      have hx : g * j' * g⁻¹ ∈ conjSubgroup (nineI V K) b := by
        rw [Nine3Core.conjSubgroup_nineI hb]; exact hjI
      exact mem_conjSubgroup_iff.mp hx
    have h3 := (nineI V K).mul_mem hby ((nineI V K).inv_mem hjI)
    simpa [commutatorElement_def, mul_assoc] using h3
  have hcj' : ⁅g⁻¹ * b * g, j'⁆ ∈ conjSubgroup (nineI V K) g := by
    have hcc : g * ⁅g⁻¹ * b * g, j'⁆ * g⁻¹ = ⁅b, g * j' * g⁻¹⁆ := by
      have h := conjugate_commutatorElement (g₃ := g⁻¹) (g₁ := b) (g₂ := g * j' * g⁻¹)
      rw [inv_inv] at h
      rw [show g⁻¹ * (g * j' * g⁻¹) * g = j' by group] at h
      rw [← h]; group
    rw [mem_conjSubgroup_iff, hcc]
    exact hcommI
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hconj : j * ⁅g⁻¹ * b * g, j'⁆ * j⁻¹ = ⁅g⁻¹ * b * g, j'⁆ := by
    rw [CFSG.Open.IsElemAbelian.comm (isElemAbelian_conjSubgroup' hI.abelian g) hj hcj']
    group
  rw [show ⁅g⁻¹ * b * g, j⁆ * j * ⁅g⁻¹ * b * g, j'⁆ * j⁻¹ =
      ⁅g⁻¹ * b * g, j⁆ * (j * ⁅g⁻¹ * b * g, j'⁆ * j⁻¹) by group, hconj]

theorem nine3_pair_beta_mem (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S) {i j : G}
    (hi : i ∈ nineI V K) (hj : j ∈ conjSubgroup (nineI V K) g) : ⁅i, j⁆ ∈ nineW V S := by
  have h1 : ⁅i, j⁆ ∈ ⁅nineI V K, conjSubgroup (nineI V K) g⁆ :=
    Subgroup.commutator_mem_commutator hi hj
  exact hc.nineW0_le_nineW
    (hc.nineI_inf_conj_le_nineW0 hI (hc.commutator_nineI_conj_le hc' hI h1))

theorem nine3_pair_final {b j : G} (hbK : b ∈ K)
    (hjK : j ∈ K) (hb : ∀ h ∈ nineH V K, ⁅b, h⁆ ∈ nineI V K)
    (hbj : ∀ h ∈ nineH V K, ⁅b⁻¹ * j, h⁆ ∈ nineI V K) :
    ∀ h ∈ nineH V K, ⁅h, j⁆ ∈ nineI V K := by
  intro h hh
  have hIeq : conjSubgroup (nineI V K) b = nineI V K := Nine3Core.conjSubgroup_nineI hbK
  have h1 : b * ⁅b⁻¹ * j, h⁆ * b⁻¹ ∈ nineI V K := by
    have hx : ⁅b⁻¹ * j, h⁆ ∈ conjSubgroup (nineI V K) b := by
      rw [hIeq]; exact hbj h hh
    exact mem_conjSubgroup_iff.mp hx
  have h2 : ⁅b, h⁆ ∈ nineI V K := hb h hh
  have h3 : ⁅j, h⁆ ∈ nineI V K := by
    rw [show j = b * (b⁻¹ * j) by group, commutatorElement_mul_left_eq_conj_mul]
    exact (nineI V K).mul_mem h1 h2
  have h4 := (nineI V K).inv_mem h3
  rwa [commutatorElement_inv] at h4

end CFSG.LocalAnalysis.WeakClosure81
