module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFCoreAbstract
public import CFSG.LocalAnalysis.StandardType.GGExcKGFixSpan

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace GGSFCore

private lemma mulAut_conj_mul_conj_inv {Q : Type*} [Group Q] (φ : MulAut Q) (q : Q) :
    φ * MulAut.conj q * φ⁻¹ = MulAut.conj (φ q) := by
  ext r
  simp [MulAut.conj_apply, mul_assoc]

private lemma normal_range_mulAut_conj {Q : Type*} [Group Q] :
    ((MulAut.conj : Q →* MulAut Q).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨q, rfl⟩ := hn
  exact ⟨g q, (mulAut_conj_mul_conj_inv g q).symm⟩

theorem finite_ggAutU
    {t : StatedLieTag} {n f : ℕ} [Finite (ggU t n f).K] :
    Finite (GGAutU t n f) := by
  haveI : Finite ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := inferInstance
  exact inferInstanceAs (Finite (MulAut ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K)))

theorem normal_range_ggPsiU
    (t : StatedLieTag) (n f : ℕ) :
    ((ggPsiU t n f).range).Normal := by
  have hrange : (ggPsiU t n f).range =
      (MulAut.conj : ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) →*
        MulAut ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K)).range := by
    unfold ggPsiU
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective (Subgroup.center (ggU t n f).K)),
      Subgroup.map_top]
  rw [hrange]
  exact normal_range_mulAut_conj

theorem ggInnDiagU_of_mem_range
    {t : StatedLieTag} {n f : ℕ} {x : GGAutU t n f}
    (hx : x ∈ (ggPsiU t n f).range) : GGInnDiagU t n f x := by
  unfold GGInnDiagU GGPsiInnerDiag
  refine ⟨x⁻¹, Subgroup.inv_mem _ hx, fun γ _ => ⟨1, Subgroup.one_mem _, fun z _ => ?_⟩⟩
  simp only [mul_inv_cancel, inv_one, one_mul, mul_one]

end GGSFCore

theorem ggSF_core
    (hCI : GGKGInndiagCI) {t : StatedLieTag} {n f : ℕ} (ht : GGExcFive t)
    (hadm : GGKnownAdm t n f) [Finite (ggU t n f).K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) (M : GGKGModel t n f p)
    {N : Subgroup (GGAutU t n f)} (hN : (ggPsiU t n f).range ≤ N) (P : Sylow p N)
    {E : Subgroup (GGAutU t n f)} (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hEP : E ≤ (P : Subgroup N).map N.subtype) (hdiag : ∀ b ∈ E, GGInnDiagU t n f b)
    (huniq : ∀ E' : Subgroup (GGAutU t n f), E' ≤ (P : Subgroup N).map N.subtype →
      IsElemAbelian p E' → Nat.card E' = Nat.card E → E' = E) :
    ∃ κ : GGAutU t n f, GGInnDiagU t n f κ ∧
      (E.map (MulAut.conj κ).toMonoidHom = M.Bfull ∨
        E.map (MulAut.conj κ).toMonoidHom = M.Bfull ⊓ (ggPsiU t n f).range) := by
  haveI : Finite (GGAutU t n f) := GGSFCore.finite_ggAutU
  haveI : ((ggPsiU t n f).range).Normal := GGSFCore.normal_range_ggPsiU t n f
  obtain ⟨hCIa, hCId⟩ := hCI t n f ht hadm p hp hp2 hreg M.π M.hπ
  exact GGSFCore.sf_core_abstract (A := GGAutU t n f) (Inn := (ggPsiU t n f).range)
    (N := N) hp hN P (GGInnDiagU t n f)
    (fun x hx => GGSFCore.ggInnDiagU_of_mem_range hx) M.isElemAbelian M.diag M.card_full
    M.index_inner hCIa
    (fun hlt => by
      obtain ⟨hte, hp3, hπ1⟩ := ggKGModel_exceptional_of_inner_lt ht hp hp2 M hlt
      exact hCId hte hp3 hπ1)
    hE h4 hEP hdiag huniq

end CFSG.StandardType
