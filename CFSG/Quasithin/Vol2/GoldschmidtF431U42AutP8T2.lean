module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

@[expose] def JC (k : ℕ) : List ℕ :=
  (List.range 43).filter fun j => comp (invL j) (invL k) == comp (invL k) (invL j)

@[expose] def JZ (k : ℕ) : List ℕ := (JC k).filter zt

@[expose] def JP (k : ℕ) : List ℕ := (JC k).filter fun j => !zt j

theorem count_R : ∀ k < 43, zt k = false → 35 ≤ (JC k).length →
    17 ≤ (JZ k).length ∧ 18 ≤ (JP k).length := by decide +kernel

theorem count_Tf : ∀ k < 43, invL k = fhatL → (JZ k).length ≤ 11 ∧ (JP k).length ≤ 12 := by
  decide +kernel

theorem exists_kf : ∃ k < 43, invL k = fhatL ∧ zt k = false := by decide +kernel

theorem exists_kU : ∃ k < 43, invL k = comp fhatL dL ∧ zt k = true := by decide +kernel

theorem JC_nodup (k : ℕ) : (JC k).Nodup := (List.nodup_range).filter _

theorem JZ_nodup (k : ℕ) : (JZ k).Nodup := (JC_nodup k).filter _

theorem JP_nodup (k : ℕ) : (JP k).Nodup := (JC_nodup k).filter _

theorem mem_JC {j k : ℕ} : j ∈ JC k ↔ j < 43 ∧ comp (invL j) (invL k) = comp (invL k) (invL j) := by
  simp [JC]

theorem mem_JZ {j k : ℕ} : j ∈ JZ k ↔ j ∈ JC k ∧ zt j = true := by simp [JZ]

theorem mem_JP {j k : ℕ} : j ∈ JP k ↔ j ∈ JC k ∧ zt j = false := by simp [JP]

end CFSG.Quasithin.H13.F431.U42Aut
