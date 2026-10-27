module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphBlockSolvable
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphBridge
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphNonsolvableBlock
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphNotTrivial
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphSettingOfHyps
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphTorusBound
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphOrbitData

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

private theorem psuKind_le {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) : psuKind h X B e ≤ 5 := by
  unfold psuKind
  split_ifs <;> omega

private theorem psuKind_dag_ne {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : 2 ≤ psuKind h X B e) :
    psuDag h e ≠ e := by
  intro hd
  unfold psuKind at hk
  simp only [hd, if_true] at hk
  split_ifs at hk <;> omega

theorem psuGraph_core {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    Group.IsSolvable ↥(psuChat h B) := by
  classical
  by_contra hns
  obtain ⟨P, hP, hstar⟩ := psuGraph_primFamily S
  obtain ⟨e0, he0P, he0ns⟩ := psuGraph_exists_nonsolvable_block S P hP hns
  have hf : 1 ≤ f := h.one_le
  have hkle := psuKind_le h X B
  have hsurv : (psuKind h X B e0 = 0 ∨ psuKind h X B e0 = 2) ∧
      Matrix.rank e0 = 2 * blockDegree (psuAlg B) e0 ∧
      (psuKind h X B e0 = 0 → 4 ≤ (2 ^ f) ^ blockDegree (psuAlg B) e0) := by
    by_cases h15 : psuKind h X B e0 = 1 ∨ psuKind h X B e0 = 5
    · exact absurd (psuGraph_kind_unstable S P hP e0 he0P h15) he0ns
    by_cases h4 : psuKind h X B e0 = 4
    · exact absurd (psuGraph_kind_D S P hP e0 he0P h4) he0ns
    by_cases h3 : psuKind h X B e0 = 3
    · exact absurd (psuGraph_kind_C2 S P hP e0 he0P h3) he0ns
    have hk : psuKind h X B e0 = 0 ∨ psuKind h X B e0 = 2 := by
      have := hkle e0
      omega
    rcases hk with hk | hk
    · obtain ⟨hr, hq⟩ := psuGraph_kind_A S P hP e0 he0P hk he0ns
      exact ⟨Or.inl hk, hr, fun _ => hq⟩
    · exact ⟨Or.inr hk, psuGraph_kind_C1 S P hP e0 he0P hk he0ns, fun h0 => absurd h0 (by omega)⟩
  obtain ⟨e1, he1P, he1a, he1b⟩ := psuGraph_exists_not_trivial S P hP
  have hbound := psuGraph_torus_bound S
  obtain ⟨R, hRP, hRtrans, hnorm, hdim, hcount, hRdata⟩ := psuGraph_orbit_data S P hP
  have hinv : ∀ e ∈ P, ∀ r, (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨
      r = psuDag h (psuPsi h X e)) →
      psuKind h X B r = psuKind h X B e ∧ Matrix.rank r = Matrix.rank e ∧
        blockDegree (psuAlg B) r = blockDegree (psuAlg B) e := by
    intro e he r hr
    obtain ⟨-, hpsi⟩ := hstar e he
    have h1 := psuGraph_orbit_invariant S P hP e he
    have h2 := psuGraph_orbit_invariant S P hP (psuPsi h X e) hpsi
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exact h1.1
    · exact h1.2
    · obtain ⟨a1, a2, a3⟩ := h2.1
      obtain ⟨b1, b2, b3⟩ := h1.2
      exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩
  have hrep : ∀ e ∈ P, ∃ r ∈ R, psuKind h X B r = psuKind h X B e ∧
      Matrix.rank r = Matrix.rank e ∧ blockDegree (psuAlg B) r = blockDegree (psuAlg B) e := by
    intro e he
    obtain ⟨r, ⟨hrR, hr⟩, -⟩ := hRtrans e he
    exact ⟨r, hrR, hinv e he r hr⟩
  refine psuGraph_arith (2 ^ f) n f rfl hf R (fun r => psuKind h X B r)
    (fun r => blockDegree (psuAlg B) r) (fun r => Matrix.rank r) (fun r _ => hkle r)
    (fun r hr => (hRdata r hr).1) (fun r hr => (hRdata r hr).2) hdim hcount ?_ ?_ ?_ ?_ ?_
  ·
    have := hbound
    rw [hnorm] at this
    exact this
  ·
    obtain ⟨r, hrR, hk, hrk, hd⟩ := hrep e0 he0P
    refine ⟨r, hrR, ?_, ?_, ?_⟩
    · rw [hk]
      exact hsurv.1
    · rw [hrk, hd]
      exact hsurv.2.1
    · intro h0
      rw [hd]
      exact hsurv.2.2 (by rw [← hk]; exact h0)
  ·
    obtain ⟨r, hrR, hk, -, -⟩ := hrep e1 he1P
    exact ⟨r, hrR, by rw [hk]; exact he1a, by rw [hk]; exact he1b⟩
  ·
    intro r hr hk345
    have hrP := hRP hr
    have hsolv : Group.IsSolvable ↥(psuBlock h B r) := by
      rcases hk345 with h3 | h4 | h5
      · exact psuGraph_kind_C2 S P hP r hrP h3
      · exact psuGraph_kind_D S P hP r hrP h4
      · exact psuGraph_kind_unstable S P hP r hrP (Or.inr h5)
    have hne : psuDag h r ≠ r := psuKind_dag_ne h X B r (by omega)
    rcases psuGraph_block_solvable_cases S P hP r hrP hsolv with h1 | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 hne
  ·
    intro r hr hk1 h4
    have hrP := hRP hr
    have hsolv := psuGraph_kind_unstable S P hP r hrP (Or.inl hk1)
    rcases psuGraph_block_solvable_cases S P hP r hrP hsolv with h1 | ⟨-, h2, -⟩
    · exact h1
    · exfalso
      have h4' : 4 ≤ (2 ^ f) ^ blockDegree (psuAlg B) r := h4
      rw [h2] at h4'
      omega


theorem psuGraphNone_holds : PSUGraphNone := by
  classical
  intro f K _ _ _ h n hn i β hi hβ hodd α hα2 hcomm hfix L₁ hL₁
  obtain ⟨X, B, hβB, hS⟩ := psuGraph_setting_of_hyps h hn i β hi hβ hodd hα2 hcomm hfix
  haveI : Group.IsSolvable ↥(psuChat h (B : GL (Fin n) K)) := psuGraph_core hS
  have hle : L₁ ≤ (psuChat h (B : GL (Fin n) K)).map
      (QuotientGroup.mk' (normOneScalars h (AutPSU.XJ h n) n)) := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨x, ?_, rfl⟩
    refine psuGraph_mem_chat_of_fixed h B x ?_
    rw [← hβB]
    exact hL₁ _ hg
  haveI : Group.IsSolvable ↥((psuChat h (B : GL (Fin n) K)).map
      (QuotientGroup.mk' (normOneScalars h (AutPSU.XJ h n) n))) :=
    solvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

end CFSG.StandardType
