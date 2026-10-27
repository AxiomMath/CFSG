module

public import CFSG.Quasithin.AppendixH.Common.OctadAltHom
public import CFSG.Quasithin.AppendixH.Common.OctadStd

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem exists_alt_two_trans {Q : Type*} [Fintype Q] [DecidableEq Q] (hQ : 4 ≤ Fintype.card Q)
    {p q p' q' : Q} (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ σ ∈ alternatingGroup Q, σ p = p' ∧ σ q = q' := by
  have h2t : MulAction.IsMultiplyPretransitive (alternatingGroup Q) Q 2 := by
    haveI : MulAction.IsMultiplyPretransitive (alternatingGroup Q) Q (Nat.card Q - 2) :=
      alternatingGroup.isMultiplyPretransitive Q
    have hsub : 2 ≤ Nat.card Q - 2 := by
      rw [Nat.card_eq_fintype_card]
      omega
    exact MulAction.isMultiplyPretransitive_of_le (m := 2) (n := Nat.card Q - 2) hsub
      (Nat.sub_le _ _)
  obtain ⟨g, hgp, hgq⟩ := MulAction.is_two_pretransitive_iff.mp h2t hpq hpq'
  exact ⟨g, g.2, by simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hgp,
    by simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hgq⟩

theorem exists_octStab_pair {p q p' q' : Fin 24}
    (hp : p ∈ octad0) (hq : q ∈ octad0) (hp' : p' ∈ octad0) (hq' : q' ∈ octad0)
    (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ g ∈ octStab octad0, g p = p' ∧ g q = q' := by
  have hcard : 4 ≤ Fintype.card ↥octad0 := by
    rw [Fintype.card_coe, isOctad_octad0.1]
    norm_num
  have hpq₀ : (⟨p, hp⟩ : ↥octad0) ≠ ⟨q, hq⟩ := fun h => hpq (Subtype.ext_iff.mp h)
  have hpq₀' : (⟨p', hp'⟩ : ↥octad0) ≠ ⟨q', hq'⟩ := fun h => hpq' (Subtype.ext_iff.mp h)
  obtain ⟨σ, hσ, hσp, hσq⟩ := exists_alt_two_trans hcard hpq₀ hpq₀'
  obtain ⟨g, hg⟩ := octActAlt_surjective isOctad_octad0 ⟨σ, hσ⟩
  have hσeq : (octAct octad0 g : Equiv.Perm ↥octad0) = σ := by
    rw [← octActAlt_apply isOctad_octad0 g, hg]
  have hgp : (g : S24) p = p' := by
    have h1 : ((octAct octad0 g ⟨p, hp⟩ : ↥octad0) : Fin 24) = p' := by
      rw [hσeq]
      exact congrArg Subtype.val hσp
    rwa [octAct_apply] at h1
  have hgq : (g : S24) q = q' := by
    have h1 : ((octAct octad0 g ⟨q, hq⟩ : ↥octad0) : Fin 24) = q' := by
      rw [hσeq]
      exact congrArg Subtype.val hσq
    rwa [octAct_apply] at h1
  exact ⟨(g : S24), g.2, hgp, hgq⟩

theorem exists_flag_pair {O : Finset (Fin 24)} {a b : Fin 24}
    (hO : IsOctad O) (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) :
    ∃ τ ∈ M24g, τ • octad0 = O ∧ τ 0 = a ∧ τ 1 = b := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octad0 hO
  have h0 : (0 : Fin 24) ∈ octad0 := by rw [mem_octad0_iff]; norm_num
  have h1 : (1 : Fin 24) ∈ octad0 := by rw [mem_octad0_iff]; norm_num
  have hσa : σ.symm a ∈ octad0 := by
    have h : a ∈ octad0.map σ.toEmbedding := by
      rw [← smul_finset_eq_map, hσO]; exact ha
    rwa [Finset.mem_map_equiv] at h
  have hσb : σ.symm b ∈ octad0 := by
    have h : b ∈ octad0.map σ.toEmbedding := by
      rw [← smul_finset_eq_map, hσO]; exact hb
    rwa [Finset.mem_map_equiv] at h
  have hne01 : (0 : Fin 24) ≠ 1 := by decide
  have hneab : σ.symm a ≠ σ.symm b := fun h => hab (σ.symm.injective h)
  obtain ⟨g, hg, hg0, hg1⟩ := exists_octStab_pair h0 h1 hσa hσb hne01 hneab
  refine ⟨σ * g, M24g.mul_mem hσ (mem_octStab_iff.mp hg).1, ?_, ?_, ?_⟩
  · rw [mul_smul, (mem_octStab_iff.mp hg).2, hσO]
  · rw [Equiv.Perm.mul_apply, hg0, Equiv.apply_symm_apply]
  · rw [Equiv.Perm.mul_apply, hg1, Equiv.apply_symm_apply]

end CFSG.ASVolI.AppH
