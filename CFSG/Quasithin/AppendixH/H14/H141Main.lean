module

public import CFSG.Quasithin.AppendixH.H14.H141Octad
public import CFSG.Quasithin.AppendixH.H14.H141Tens
public import CFSG.Quasithin.AppendixH.H14.H141Line
public import CFSG.Quasithin.AppendixH.H14.H141Classify

public section

open scoped Pointwise Matrix

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H158T CFSG.Quasithin.H.Mathieu CFSG.Open
  CFSG.Monster.Code

theorem pCoreOf_le_of_sylow_in {Γ M T : Subgroup S24} (hTM : T ≤ M) (hMΓ : M ≤ Γ)
    (hT : IsSylowIn 2 T Γ) : pCoreOf 2 M ≤ T := by
  refine pCoreOf_le_of_sylow (H := M) (P := T) hTM hT.2.1 ?_
  intro h2
  apply hT.2.2
  have hdvd : T.relIndex M ∣ T.relIndex Γ :=
    ⟨M.relIndex Γ, (Subgroup.relIndex_mul_relIndex T M Γ hTM hMΓ).symm⟩
  exact h2.trans hdvd

theorem std_conj_data
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :
    ∃ c ∈ M24g, (∀ t ∈ T₀, ∃ p : T24s2.Elem, c * t * c⁻¹ = T24s2.perm p) ∧
      (MY M24g S).map (MulAut.conj c).toMonoidHom = MY M24g stdS ∧
      (KY M24g S).map (MulAut.conj c).toMonoidHom = tab64Sub tabS tabS_ok ∧
      (MY M24g Tr).map (MulAut.conj c).toMonoidHom = MY M24g labTrio ∧
      (KY M24g Tr).map (MulAut.conj c).toMonoidHom = tab64Sub tabT tabT_ok ∧
      (KY M24g O).map (MulAut.conj c).toMonoidHom = KY M24g o2F := by
  obtain ⟨c, hc, hcT, hcO, hcTr, hcS⟩ :=
    exists_std141 (O := O) (Tr := Tr) (S := S) (T₀ := T₀) hcfg.trio hcfg.sextet hcfg.O_mem
      hcfg.trio_union hcfg.sylow hcfg.stab_O hcfg.stab_Tr hcfg.stab_S
  refine ⟨c, hc, hcT, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcS]
    exact (MY_smul hc S).symm
  · rw [← KY_smul hc S, hcS]
    exact pCore_S
  · rw [← hcTr]
    exact (MY_smul hc Tr).symm
  · rw [← KY_smul hc Tr, hcTr]
    exact pCore_T
  · rw [← KY_smul hc O, hcO]

theorem h141_part1
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :
    KY M24g S ≠ KY M24g Tr ∧
      ∀ A : Subgroup S24, (A ≤ T₀ ∧ IsE2k 6 A) ↔ (A = KY M24g S ∨ A = KY M24g Tr) := by
  obtain ⟨c, -, hcT, -, hKS, -, hKT, -⟩ := std_conj_data hcfg
  have hne : KY M24g S ≠ KY M24g Tr := by
    intro h
    exact tab64Sub_S_ne_T (by rw [← hKS, ← hKT, h])
  have hTM_S : T₀ ≤ MY M24g S := by
    intro g hg
    exact ⟨hcfg.sylow.1 hg, MulAction.mem_stabilizer_iff.mpr (hcfg.stab_S g hg)⟩
  have hTM_T : T₀ ≤ MY M24g Tr := by
    intro g hg
    exact ⟨hcfg.sylow.1 hg, MulAction.mem_stabilizer_iff.mpr (hcfg.stab_Tr g hg)⟩
  have hle_S : KY M24g S ≤ T₀ := by
    show pCoreOf 2 (MY M24g S) ≤ T₀
    exact pCoreOf_le_of_sylow_in hTM_S inf_le_left hcfg.sylow
  have hle_T : KY M24g Tr ≤ T₀ := by
    show pCoreOf 2 (MY M24g Tr) ≤ T₀
    exact pCoreOf_le_of_sylow_in hTM_T inf_le_left hcfg.sylow
  have hE_S : IsE2k 6 (KY M24g S) := by
    refine ⟨?_, ?_⟩
    · exact isElemAbelian_of_map_conj 2 c (E := KY M24g S)
        (by rw [hKS]; exact isElemAbelian_tab64Sub tabS_ok)
    · rw [← card_map_conj c (KY M24g S), hKS, card_tab64Sub tabS_ok]
      norm_num
  have hE_T : IsE2k 6 (KY M24g Tr) := by
    refine ⟨?_, ?_⟩
    · exact isElemAbelian_of_map_conj 2 c (E := KY M24g Tr)
        (by rw [hKT]; exact isElemAbelian_tab64Sub tabT_ok)
    · rw [← card_map_conj c (KY M24g Tr), hKT, card_tab64Sub tabT_ok]
      norm_num
  refine ⟨hne, ?_⟩
  intro A
  constructor
  · rintro ⟨hA0, hE⟩
    let A' : Subgroup S24 := A.map (MulAut.conj c).toMonoidHom
    have hAT' : ∀ a ∈ A', ∃ p : T24s2.Elem, a = T24s2.perm p := by
      rintro a ⟨x, hx, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hcT x (hA0 hx)
    have hE' : IsE2k 6 A' :=
      ⟨isElemAbelian_map_conj 2 c hE.1, (card_map_conj c A).trans hE.2⟩
    rcases classify_E64 hAT' hE' with h | h
    · left
      apply map_conj_injective c
      rw [hKS]
      exact h
    · right
      apply map_conj_injective c
      rw [hKT]
      exact h
  · rintro (hA | hA)
    · rw [hA]
      exact ⟨hle_S, hE_S⟩
    · rw [hA]
      exact ⟨hle_T, hE_T⟩

theorem h141_part26
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :
    Clause26 (MY M24g S) (KY M24g S) (KY M24g O) := by
  obtain ⟨c, -, -, hMS, hKS, -, -, hKO⟩ := std_conj_data hcfg
  apply clause26_of_map_conj c
  rw [hMS, hKS, hKO, ← pCore_S]
  exact clause26_std

theorem h141_part3
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :
    ConjIsoModel (MY M24g Tr) (KY M24g Tr) (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2)))
      tensorSet32 := by
  obtain ⟨c, -, -, -, -, hMT, hKT, -⟩ := std_conj_data hcfg
  apply conjIsoModel_of_map_conj c
  rw [hMT, hKT, ← pCore_T]
  exact stdMT_conjIsoModel

theorem h141_part4
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :
    ConjIsoModel (MY M24g O) (KY M24g O) (Multiplicative (Fin 4 → ZMod 2))
      ((natSub 4 (ZMod 2) ⊤ : Subgroup (MulAut (Multiplicative (Fin 4 → ZMod 2)))) :
        Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) := by
  exact octad_conjIsoModel hcfg.octad

theorem map_conj_inv_map_conj (c : S24) (X : Subgroup S24) :
    (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id S24 := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

theorem conjSubg_inv_mul_map (c g : S24) (A : Subgroup S24) :
    conjSubg (c⁻¹ * g) A = (conjSubg g A).map (MulAut.conj c⁻¹).toMonoidHom := by
  have hcomp : (MulAut.conj (c⁻¹ * g)).toMonoidHom =
      (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [conjSubg, conjSubg, Subgroup.map_map, hcomp]

theorem h141_part5
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :
    ∀ A : Subgroup S24, A ≤ M24g → A ≠ ⊥ → IsElemAbelian 2 A → 5 ≤ rk ↥A →
      ∃ g ∈ M24g, conjSubg g A ≤ KY M24g S ∨ conjSubg g A ≤ KY M24g Tr := by
  intro A hA _ hel h5
  obtain ⟨g, hg, hgA⟩ := classify_ge5 hA hel h5
  obtain ⟨c, hc, -, -, hKS, -, hKT, -⟩ := std_conj_data hcfg
  have hmapS : (tab64Sub tabS tabS_ok).map (MulAut.conj c⁻¹).toMonoidHom = KY M24g S := by
    rw [← hKS, map_conj_inv_map_conj c (KY M24g S)]
  have hmapT : (tab64Sub tabT tabT_ok).map (MulAut.conj c⁻¹).toMonoidHom = KY M24g Tr := by
    rw [← hKT, map_conj_inv_map_conj c (KY M24g Tr)]
  refine ⟨c⁻¹ * g, M24g.mul_mem (M24g.inv_mem hc) hg, ?_⟩
  rw [conjSubg_inv_mul_map]
  rcases hgA with hS | hT
  · left
    calc (conjSubg g A).map (MulAut.conj c⁻¹).toMonoidHom
        ≤ (tab64Sub tabS tabS_ok).map (MulAut.conj c⁻¹).toMonoidHom :=
          Subgroup.map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) hS
      _ = KY M24g S := hmapS
  · right
    calc (conjSubg g A).map (MulAut.conj c⁻¹).toMonoidHom
        ≤ (tab64Sub tabT tabT_ok).map (MulAut.conj c⁻¹).toMonoidHom :=
          Subgroup.map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) hT
      _ = KY M24g Tr := hmapT

end CFSG.Quasithin.AppendixH.H14
