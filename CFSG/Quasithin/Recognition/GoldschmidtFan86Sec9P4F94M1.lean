module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Arm
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem xβ_inv_smul_family (v : V) (j : Fin 3) :
    S.xβ⁻¹ • ((S.xβ ^ (j : ℕ))⁻¹ • v) = (S.xβ ^ ((j + 1 : Fin 3) : ℕ))⁻¹ • v := by
  have hv : ((j + 1 : Fin 3) : ℕ) = ((j : ℕ) + 1) % 3 := by
    rw [Fin.val_add]
    rfl
  rw [hv, ← pow_eq_pow_mod ((j : ℕ) + 1) S.xβ_pow_three, pow_succ, mul_inv_rev, mul_smul]

theorem xβ_inv_smul_muV (j : Fin 3) : S.xβ⁻¹ • S.muV j = S.muV (j + 1) := by
  rw [muV_eq, muV_eq, S.xβ_inv_smul_family]

theorem muV_zero : S.muV 0 = S.D.alpha 0 := by simp [muV_eq]

theorem xβ_pow_smul_muV (i j : Fin 3) : (S.xβ ^ (i : ℕ)) • S.muV j = S.muV (j - i) := by
  have h1 : ∀ k : Fin 3, S.xβ • S.muV k = S.muV (k - 1) := fun k => by
    have := S.xβ_inv_smul_muV (k - 1)
    rw [sub_add_cancel] at this
    rw [← this, smul_inv_smul]
  fin_cases i
  · simp
  · simp only [Fin.mk_one, pow_one]
    exact h1 j
  · show (S.xβ ^ 2) • S.muV j = S.muV (j - 2)
    rw [pow_two, mul_smul, h1, h1]
    congr 1
    exact (by decide : ∀ j : Fin 3, j - 1 - 1 = j - 2) j

theorem yMu_zero_eq : S.yMu 0 = L.z (S.D.alpha 0) * L.z (S.D.alpha 1) := by
  simp [yMu, zMuij]

theorem yMu_eq_conj (F : FanTree Γ G) (i : Fin 3) :
    S.yMu i = (S.xβ ^ (i : ℕ))⁻¹ * S.yMu 0 * S.xβ ^ (i : ℕ) := by
  have h0 := L.z_inv_smul (S.xβ ^ (i : ℕ)) (S.D.valence_alpha F 0)
  have h1 := L.z_inv_smul (S.xβ ^ (i : ℕ)) (S.D.valence_alpha F 1)
  rw [yMu_zero_eq]
  show L.z ((S.xβ ^ (i : ℕ))⁻¹ • S.D.alpha 0) * L.z ((S.xβ ^ (i : ℕ))⁻¹ • S.D.alpha 1) = _
  rw [h0, h1]
  group

theorem yMu_smul_iff (F : FanTree Γ G) (i : Fin 3) (v : V) :
    S.yMu i • v = v ↔ S.yMu 0 • (S.xβ ^ (i : ℕ)) • v = (S.xβ ^ (i : ℕ)) • v := by
  rw [S.yMu_eq_conj F i, mul_assoc, mul_smul, mul_smul, inv_smul_eq_iff]

theorem yMu_zero_fix_iff (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) {v : V}
    (hv : Γ.dist S.beta v ≤ 3) :
    S.yMu 0 • v = v ↔ (Γ.dist S.α v ≤ 2 ∨ Γ.dist S.beta v ≤ 2) := by
  have hZ := S.D.isZ2Pair_alpha F h71c (i := 2) (j := 0) (k := 1) (by decide) (by decide)
    (by decide)
  have h := h81 (S.D.alpha 2) S.α (S.D.beta 2) (S.D.alpha 0) (S.D.alpha 1)
    (S.D.valence_alpha F 2) hZ
  have hd : Γ.dist (S.D.alpha 2) v ≤ 4 := by
    calc Γ.dist (S.D.alpha 2) v ≤ Γ.dist (S.D.alpha 2) S.beta + Γ.dist S.beta v :=
          F.isTree.connected.dist_triangle
      _ ≤ 1 + 3 := by
          gcongr
          rw [SimpleGraph.dist_comm]
          exact (S.D.dist_beta_alpha 2).le
      _ = 4 := rfl
  constructor
  · intro hy
    have hmem : v ∈ {v | Γ.dist (S.D.alpha 2) v ≤ 4 ∧
        (L.z (S.D.alpha 0) * L.z (S.D.alpha 1)) • v = v} := ⟨hd, by rwa [S.yMu_zero_eq] at hy⟩
    rw [h] at hmem
    exact hmem
  · intro hr
    have hmem : v ∈ {v | Γ.dist S.α v ≤ 2 ∨ Γ.dist (S.D.beta 2) v ≤ 2} := hr
    rw [← h] at hmem
    rw [S.yMu_zero_eq]
    exact hmem.2

theorem dist_pow_smul_beta (F : FanTree Γ G) (n : ℕ) (v : V) :
    Γ.dist S.beta ((S.xβ ^ n) • v) = Γ.dist S.beta v := by
  have h : (S.xβ ^ n) • S.beta = S.beta :=
    MulAction.mem_stabilizer_iff.1 (pow_mem (MulAction.mem_stabilizer_iff.2 S.xβ_smul_beta) n)
  have := dist_smul F (S.xβ ^ n) S.beta v
  rwa [h] at this

theorem yMu_zero_mem_ballStab_two (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) :
    S.yMu 0 ∈ ballStab Γ G 2 S.beta :=
  mem_ballStab.2 fun _ hw =>
    (S.yMu_zero_fix_iff F h71c h81 (hw.trans (by norm_num))).2 (Or.inr hw)

theorem yMu_zero_smul_muV_iff (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (j : Fin 3) : S.yMu 0 • S.muV j = S.muV j ↔ j = 0 := by
  have hb := S.dist_beta_muV F h71c j
  rw [S.yMu_zero_fix_iff F h71c h81 (by rw [hb])]
  constructor
  · rintro (h | h)
    · by_contra hj
      have := S.dist_muV_alphaV_ne F h71c (i := 0) (j := j) hj
      rw [S.alphaV_zero, SimpleGraph.dist_comm] at this
      omega
    · rw [hb] at h
      omega
  · rintro rfl
    left
    rw [S.muV_zero]
    exact (S.D.dist_start_alpha F 0).le

theorem yMu_mem_ballStab_two (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (i : Fin 3) : S.yMu i ∈ ballStab Γ G 2 S.beta := by
  refine mem_ballStab.2 fun w hw => ?_
  rw [S.yMu_smul_iff F i]
  have h0 := mem_ballStab.1 (S.yMu_zero_mem_ballStab_two F h71c h81) ((S.xβ ^ (i : ℕ)) • w)
    (by rw [S.dist_pow_smul_beta F]; exact hw)
  exact h0

theorem yMu_smul_muV_iff (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (i j : Fin 3) :
    S.yMu i • S.muV j = S.muV j ↔ j = i := by
  rw [S.yMu_smul_iff F i, S.xβ_pow_smul_muV, S.yMu_zero_smul_muV_iff F h71c h81]
  exact sub_eq_zero

end Sec9Cfg

end CFSG.Quasithin.Fan86
