module

public import CFSG.Quasithin.Background.RonanH143Sext
public import CFSG.Quasithin.Background.RonanH143ConjA

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

theorem M22g_zero_one : M22g 0 1 = mog22 := rfl

theorem smul_pair_zero_one (σ : P24) :
    σ • ({0, 1} : Finset (Fin 24)) = {0, 1} ↔ (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  rw [h143_smul_pair]
  constructor
  · intro h
    have h0 : σ 0 ∈ ({0, 1} : Finset (Fin 24)) := by
      rw [← h]
      simp
    have h1 : σ 1 ∈ ({0, 1} : Finset (Fin 24)) := by
      rw [← h]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
    have hne : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hne
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hne
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · rw [h0, h1]
    · rw [h0, h1]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto

theorem M2ab_zero_one : M2ab 0 1 = mog22plus := by
  ext g
  simp only [M2ab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, smul_pair_zero_one]
  exact Iff.rfl

theorem eq_mog22_or_plus {Γ : Subgroup P24} (h1 : mog22 ≤ Γ) (h2 : Γ ≤ mog22plus) :
    Γ = mog22 ∨ Γ = mog22plus := by
  by_cases hsw : ∃ g ∈ Γ, g 0 = 1
  · right
    obtain ⟨g, hg, hg0⟩ := hsw
    have hg1 : g 1 = 0 := by
      rcases (h2 hg).2 with ⟨a, b⟩ | ⟨a, b⟩
      · rw [hg0] at a
        exact absurd a (by decide)
      · exact b
    apply le_antisymm h2
    intro h hh
    rcases hh.2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact h1 ⟨⟨hh.1, (mem_stab_iff 0 h).2 a⟩, (mem_stab_iff 1 h).2 b⟩
    · have hm : g⁻¹ * h ∈ mog22 := by
        refine ⟨⟨AutPerm.mul_mem (AutPerm.inv_mem (h2 hg).1) hh.1, (mem_stab_iff 0 _).2 ?_⟩, (mem_stab_iff 1 _).2 ?_⟩
        · rw [Equiv.Perm.mul_apply, a, Equiv.Perm.inv_eq_iff_eq, hg0]
        · rw [Equiv.Perm.mul_apply, b, Equiv.Perm.inv_eq_iff_eq, hg1]
      have := Γ.mul_mem hg (h1 hm)
      simpa using this
  · left
    simp only [not_exists, not_and] at hsw
    apply le_antisymm _ h1
    intro g hg
    rcases (h2 hg).2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨⟨(h2 hg).1, (mem_stab_iff 0 g).2 a⟩, (mem_stab_iff 1 g).2 b⟩
    · exact absurd a (hsw g hg)

theorem conjSubg_eq_self {γ : P24} {H : Subgroup P24} (hγ : γ ∈ H) : conjSubg γ H = H := by
  ext x
  rw [mem_conjSubg_iff]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem hγ h) (H.inv_mem hγ)
    have e : γ * (γ⁻¹ * x * γ) * γ⁻¹ = x := by group
    rwa [e] at this
  · intro h
    exact H.mul_mem (H.mul_mem (H.inv_mem hγ) h) hγ

theorem conjSubg_mul (c d : P24) (H : Subgroup P24) :
    conjSubg (c * d) H = conjSubg c (conjSubg d H) := by
  ext x
  rw [mem_conjSubg_iff, mem_conjSubg_iff, mem_conjSubg_iff]
  have e : (c * d)⁻¹ * x * (c * d) = d⁻¹ * (c⁻¹ * x * c) * d := by group
  rw [e]

theorem isSylowIn_conj {p : ℕ} {T Γ : Subgroup P24} (c : P24) (h : IsSylowIn p T Γ) :
    IsSylowIn p (conjSubg c T) (conjSubg c Γ) := by
  refine ⟨conjSubg_le_conjSubg_iff.2 h.1, ?_, ?_⟩
  · unfold conjSubg
    exact h.2.1.of_equiv (T.equivMapOfInjective _ (MulAut.conj c).injective)
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj c).toMonoidHom) T Γ
      (MulAut.conj c).injective
    unfold conjSubg
    rw [this]
    exact h.2.2

theorem smul_finset_eq_map (c : P24) (X : Finset (Fin 24)) : c • X = X.map c.toEmbedding := by
  ext x
  simp only [Finset.mem_smul_finset, Finset.mem_map, Equiv.Perm.smul_def, Equiv.toEmbedding_apply]

theorem smul_finset_finset_eq_sMap (c : P24) (S : Finset (Finset (Fin 24))) : c • S = sMap c S := by
  ext T
  simp only [Finset.mem_smul_finset, sMap, Finset.mem_image, smul_finset_eq_map]

theorem isSextR_smul {c : P24} (hc : c ∈ AutPerm) {S : Finset (Finset (Fin 24))}
    (hS : IsSextR S) : IsSextR (c • S) := by
  rw [smul_finset_finset_eq_sMap]
  exact isSext_sMap hc hS

end CFSG.Quasithin.RonanH143
