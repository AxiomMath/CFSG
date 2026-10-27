module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T0
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Ctx

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

section Class

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem repA_mem_Bh (t : ℕ) : repA t ∈ Bh := by
  unfold repA
  split_ifs
  · exact That_le_Bh xA_mem_That
  · exact That_le_Bh t0A_mem_That
  · exact fhatA_mem_Bh
  · exact That_le_Bh (That.mul_mem fhatA_mem_That xA_mem_That)

@[expose] noncomputable def repB (t : ℕ) : ↥Bh := ⟨repA t, repA_mem_Bh t⟩

theorem repB_zero : repB 0 = xB := Subtype.ext (by simp [repB, repA, xB])

theorem repB_one : repB 1 = t0B := Subtype.ext (by simp [repB, repA, t0B])

theorem repB_two : repB 2 = fhB := Subtype.ext (by simp [repB, repA, fhB])

theorem repB_three : repB 3 = fhB * xB :=
  Subtype.ext (by simp [repB, repA, fhB, xB, e0A])

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem ivG_class (h : F55Ctx c R) {k : ℕ} (hk : k < 43) :
    (IsConj (ivG c k) z ∧ ¬ IsConj (ivG c k) (c.iso.toG fhB) ∧ zt k = true) ∨
      (IsConj (ivG c k) (c.iso.toG fhB) ∧ ¬ IsConj (ivG c k) z ∧ zt k = false) := by
  obtain ⟨g, hg, hgeq⟩ := ivA_type hk
  have ht4 : invTgt.getD k 0 < 4 := inv_check.2.2 k hk
  have hconj : IsConj (ivG c k) (c.iso.toG (repB (invTgt.getD k 0))) := by
    refine c.iso.isConj_toG (u := ivB k) (v := repB (invTgt.getD k 0)) hg ?_
    rw [ivB_coe hk]
    exact hgeq
  have hxz : c.iso.toG xB = z := c.iso.toG_xB c.z2 c.z1 c.zc
  have hFz : ¬ IsConj z (c.iso.toG fhB) := fun hc => h.hnc hc.symm
  unfold zt
  generalize invTgt.getD k 0 = t at hconj ht4 ⊢
  interval_cases t
  · rw [repB_zero, hxz] at hconj
    refine Or.inl ⟨hconj, fun hc => hFz (hconj.symm.trans hc), by simp⟩
  · rw [repB_one] at hconj
    have hF : IsConj (ivG c k) (c.iso.toG fhB) := hconj.trans h.ht0
    exact Or.inr ⟨hF, fun hc => h.hnc ((hF.symm.trans hc)), by simp⟩
  · rw [repB_two] at hconj
    exact Or.inr ⟨hconj, fun hc => h.hnc (hconj.symm.trans hc), by simp⟩
  · rw [repB_three, AutIso.toG_mul, hxz] at hconj
    have hz : IsConj (ivG c k) z := hconj.trans h.hfz
    exact Or.inl ⟨hz, fun hc => hFz (hz.symm.trans hc), by simp⟩

theorem ivG_conj_z_iff (h : F55Ctx c R) {k : ℕ} (hk : k < 43) :
    IsConj (ivG c k) z ↔ zt k = true := by
  rcases ivG_class c h hk with ⟨h1, -, h3⟩ | ⟨-, h2, h3⟩
  · exact ⟨fun _ => h3, fun _ => h1⟩
  · exact ⟨fun hc => absurd hc h2, fun hc => by rw [h3] at hc; exact Bool.noConfusion hc⟩

theorem ivG_conj_F_iff (h : F55Ctx c R) {k : ℕ} (hk : k < 43) :
    IsConj (ivG c k) (c.iso.toG fhB) ↔ zt k = false := by
  rcases ivG_class c h hk with ⟨-, h2, h3⟩ | ⟨h1, -, h3⟩
  · exact ⟨fun hc => absurd hc h2, fun hc => by rw [h3] at hc; exact Bool.noConfusion hc⟩
  · exact ⟨fun _ => h3, fun _ => h1⟩

end Class

end CFSG.Quasithin.H13.F431.U42Aut
