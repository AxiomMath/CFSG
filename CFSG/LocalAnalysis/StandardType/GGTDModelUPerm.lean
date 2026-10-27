module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutPerm
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_permAut_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ} {L' : Type} [Group L']
    [Finite L'] {φ : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 n K d) →* L'}
    (hM : UnitTB.Model φ) (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t) :
    ∃ ρ : Equiv.Perm (Fin d) →* MulAut ↥A, Function.Injective ρ ∧
      ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
      ∀ (σ : Equiv.Perm (Fin d)) (hσ : MulAut.conj (φ (LineU.permSU hM.field σ)) ∈
          Subgroup.normalizer (A : Set (MulAut L'))),
        ρ σ = ggConjAut A hσ := by
  classical
  have hN : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ (LineU.permSU hM.field σ)) ∈
        Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => unitDvd_conj_perm_mem_normalizer hM hp hpq (by omega) hA.2 hsc hdiag σ
  have hmul : ∀ σ τ : Equiv.Perm (Fin d),
      ggConjAut A (hN (σ * τ)) = ggConjAut A (hN σ) * ggConjAut A (hN τ) := by
    intro σ τ
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp only [ggConjAut_apply, MulAut.mul_apply, UnitAct.permSU_mul, map_mul]
    group
  have hone : ggConjAut A (hN 1) = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp [ggConjAut_apply, UnitAct.permSU_one]
  let ρ : Equiv.Perm (Fin d) →* MulAut ↥A :=
    { toFun := fun σ => ggConjAut A (hN σ)
      map_one' := hone
      map_mul' := hmul }
  have hρapply : ∀ σ : Equiv.Perm (Fin d), ρ σ = ggConjAut A (hN σ) := fun σ => rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_one ρ).mpr fun σ hσ => ?_
    refine UnitTB.permSU_eq_one_of_conj_comm hM hp hp2 hpq hd hsc hdiag fun b hb => ?_
    have h := congrArg (fun f : MulAut ↥A => ((f ⟨b, hb⟩ : ↥A) : MulAut L')) hσ
    rw [hρapply, ggConjAut_apply, MulAut.one_apply] at h
    simpa using h
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨σ, rfl⟩
      rw [hρapply]
      exact ggConjAut_mem_ggAutomizer
        (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A)
        (MonoidHom.mem_range.mpr ⟨φ (LineU.permSU hM.field σ), rfl⟩) (hN σ)
    · intro v hv
      obtain ⟨c, ⟨m, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
      obtain ⟨w, ⟨π, rfl⟩, hfix⟩ :=
        UnitAct.exists_weyl_fix hM hK hp hp2 hpq hd hA hsc hdiag hcN
      obtain ⟨u, hu⟩ : ∃ u : L', u = m * (φ (LineU.permSU hM.field π))⁻¹ := ⟨_, rfl⟩
      have hfixu : ∀ a ∈ A, a u = u := fun a ha => by rw [hu]; exact hfix a ha
      have hm : m = u * φ (LineU.permSU hM.field π) := by rw [hu]; group
      have hcomm : ∀ b' ∈ A, MulAut.conj u * b' = b' * MulAut.conj u := by
        intro b' hb'
        ext x
        have h := hfixu b' hb'
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]
      have hv' : v = ggConjAut A (hN π) := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        rw [hvc b, ggConjAut_apply, hm, map_mul]
        have hb' : MulAut.conj (φ (LineU.permSU hM.field π)) * (b : MulAut L') *
            (MulAut.conj (φ (LineU.permSU hM.field π)))⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (hN π) b).mp b.2
        calc MulAut.conj u * MulAut.conj (φ (LineU.permSU hM.field π)) * (b : MulAut L') *
              (MulAut.conj u * MulAut.conj (φ (LineU.permSU hM.field π)))⁻¹
            = MulAut.conj u * (MulAut.conj (φ (LineU.permSU hM.field π)) *
                (b : MulAut L') *
                (MulAut.conj (φ (LineU.permSU hM.field π)))⁻¹) * (MulAut.conj u)⁻¹ := by
              group
          _ = (MulAut.conj (φ (LineU.permSU hM.field π)) * (b : MulAut L') *
                (MulAut.conj (φ (LineU.permSU hM.field π)))⁻¹) * MulAut.conj u *
                (MulAut.conj u)⁻¹ := by
              rw [hcomm _ hb']
          _ = _ := mul_inv_cancel_right _ _
      exact MonoidHom.mem_range.mpr ⟨π, by rw [hρapply]; exact hv'.symm⟩
  · intro σ hσ
    rw [hρapply]

end CFSG.StandardType
