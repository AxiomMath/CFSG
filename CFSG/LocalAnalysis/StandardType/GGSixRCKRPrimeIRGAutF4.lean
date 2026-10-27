module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4Iso
public import CFSG.LieType.Steinberg.Adjoint.Datum

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgF4_map_ggRootSub {U : Type*} [Group U] {Q : Type*} [Group Q]
    (Δ : UniversalRootDatum U) (q : U →* Q) (θ : MulAut Q) (α : MulAut U)
    (hqα : ∀ x, q (α x) = θ (q x))
    {γ γ' : Fin Δ.rank → ℤ} (u w : U)
    (hγ : (Δ.rootGroup γ).map α.toMonoidHom =
      (Δ.rootGroup γ').map (MulAut.conj w).toMonoidHom) :
    (ggRootSub Δ q γ u).map θ.toMonoidHom = ggRootSub Δ q γ' (α u * w) := by
  have key : (ggRootSub Δ q γ u).map θ.toMonoidHom =
      ((Δ.rootGroup γ).map α.toMonoidHom).map
        (q.comp (MulAut.conj (α u)).toMonoidHom) := by
    simp only [ggRootSub, Subgroup.map_map]
    apply congrArg (fun f : U →* Q => Subgroup.map f (Δ.rootGroup γ))
    ext x
    change θ (q (u * x * u⁻¹)) = q ((α u) * (α x) * (α u)⁻¹)
    rw [← hqα (u * x * u⁻¹)]
    congr 1
    simpa only [map_mul, map_inv]
  rw [key, hγ]
  simp only [ggRootSub, Subgroup.map_map]
  apply congrArg (fun f : U →* Q => Subgroup.map f (Δ.rootGroup γ'))
  ext x
  change q ((α u) * (w * x * w⁻¹) * (α u)⁻¹) =
    q ((α u * w) * x * (α u * w)⁻¹)
  congr 1
  group

private theorem irgF4_phi_pow_rootGroup
    (F : Type) [Field F] [Finite F] [CharP F ReeTag.F4.prime]
    (k : ℕ) {β : Fin (f4Datum F).rank → ℤ} (hβ : β ∈ (f4Datum F).roots) :
    ∃ β' ∈ (f4Datum F).roots,
      ((f4Datum F).rootGroup β).map
          ((ReeTag.F4.finiteExceptionalAut F) ^ k).toMonoidHom =
        (f4Datum F).rootGroup β' ∧
      ((f4Datum F).rootGroup (-β)).map
          ((ReeTag.F4.finiteExceptionalAut F) ^ k).toMonoidHom =
        (f4Datum F).rootGroup (-β') := by
  let φ : MulAut (adjointGroup Tag.F4 F) := ReeTag.F4.finiteExceptionalAut F
  change ∃ β' ∈ (f4Datum F).roots,
      ((f4Datum F).rootGroup β).map (φ ^ k).toMonoidHom = (f4Datum F).rootGroup β' ∧
      ((f4Datum F).rootGroup (-β)).map (φ ^ k).toMonoidHom = (f4Datum F).rootGroup (-β')
  induction k with
  | zero =>
      refine ⟨β, hβ, ?_, ?_⟩ <;>
        rw [pow_zero, CFSG.LieType.Chevalley.map_mulAut_one]
  | succ k ih =>
      obtain ⟨βk, hβk, h1, h2⟩ := ih
      obtain ⟨βk', hβk', h1', h2', -⟩ :=
        CFSG.StandardType.LieKnownR2.Short.finiteExceptionalAut_F4_map_rootGroup F hβk
      have h1'' : ((f4Datum F).rootGroup βk).map φ.toMonoidHom =
          (f4Datum F).rootGroup βk' := h1'
      have h2'' : ((f4Datum F).rootGroup (-βk)).map φ.toMonoidHom =
          (f4Datum F).rootGroup (-βk') := h2'
      refine ⟨βk', hβk', ?_, ?_⟩
      · rw [pow_succ', CFSG.LieType.Chevalley.map_toMonoidHom_mul_mulAut, h1, h1'']
      · rw [pow_succ', CFSG.LieType.Chevalley.map_toMonoidHom_mul_mulAut, h2, h2'']


theorem irgRootPairAut_F4
    {g : ℕ} (hadm : StatedLieAdmissible .F4 0 2 g) : IRGRootPairAut .F4 0 g := by
  intro θ β' hβ' _hlong u'
  have hg : 1 ≤ g := hadm.2.1
  have hZ : Subgroup.center ((ggU .F4 0 g).K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4)
      (K := GaloisField 2 g)
  let q : (ggU .F4 0 g).K →* IRGQuot .F4 0 g :=
    QuotientGroup.mk' (Subgroup.center (ggU .F4 0 g).K)
  have hqinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff]
    show (QuotientGroup.mk' (Subgroup.center (ggU .F4 0 g).K)).ker = ⊥
    rw [QuotientGroup.ker_mk', hZ]
  have hqsurj : Function.Surjective q :=
    QuotientGroup.mk'_surjective (N := Subgroup.center (ggU .F4 0 g).K)
  let e : (ggU .F4 0 g).K ≃* IRGQuot .F4 0 g := MulEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  let α : MulAut (adjointGroup Tag.F4 (GaloisField 2 g)) := e.trans (θ.trans e.symm)
  have heq (x : (ggU .F4 0 g).K) : e x = q x :=
    MulEquiv.ofBijective_apply q _ x
  have hαx (x : (ggU .F4 0 g).K) : α x = e.symm (θ (e x)) := rfl
  have hqα (x : (ggU .F4 0 g).K) : q (α x) = θ (q x) := by
    rw [hαx x, ← heq (e.symm (θ (e x))), MulEquiv.apply_symm_apply, heq x]
  obtain ⟨-, hNF, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := g) hg
      (GaloisField 2 g) (GaloisField.card 2 g (by omega))
  obtain ⟨⟨g0r, k⟩, hαr⟩ := (hNF α).exists
  let g0 : adjointGroup Tag.F4 (GaloisField 2 g) := g0r
  let φ : MulAut (adjointGroup Tag.F4 (GaloisField 2 g)) :=
    ReeTag.F4.finiteExceptionalAut (GaloisField 2 g)
  have hα : α = MulAut.conj g0 * φ ^ (k : ℕ) := hαr
  obtain ⟨βk, hβk, hφβ', hφnegβ'⟩ :=
    irgF4_phi_pow_rootGroup (GaloisField 2 g) (k : ℕ) hβ'
  have hφβ'' : ((f4Datum (GaloisField 2 g)).rootGroup β').map
      (φ ^ (k : ℕ)).toMonoidHom = (f4Datum (GaloisField 2 g)).rootGroup βk := hφβ'
  have hφnegβ'' : ((f4Datum (GaloisField 2 g)).rootGroup (-β')).map
      (φ ^ (k : ℕ)).toMonoidHom = (f4Datum (GaloisField 2 g)).rootGroup (-βk) := hφnegβ'
  have hmapα : ((f4Datum (GaloisField 2 g)).rootGroup β').map α.toMonoidHom =
      ((f4Datum (GaloisField 2 g)).rootGroup βk).map
        (MulAut.conj g0).toMonoidHom := by
    rw [hα, CFSG.LieType.Chevalley.map_toMonoidHom_mul_mulAut, hφβ'']
  have hmapnegα : ((f4Datum (GaloisField 2 g)).rootGroup (-β')).map α.toMonoidHom =
      ((f4Datum (GaloisField 2 g)).rootGroup (-βk)).map
        (MulAut.conj g0).toMonoidHom := by
    rw [hα, CFSG.LieType.Chevalley.map_toMonoidHom_mul_mulAut, hφnegβ'']
  have hred : 2 • βk ∉ (f4Datum (GaloisField 2 g)).roots := by
    intro hmem
    have hroot := (CFSG.LieType.Steinberg.Adjoint.mem_adjDatum_roots).1 hmem
    have h2 := CFSG.LieType.Steinberg.Adjoint.eq_one_of_isRoot_nsmul
      (τ := .F4) (γ := βk) (n := 2) hroot
    omega
  refine ⟨βk, ?_, α u' * g0, ?_, ?_⟩
  · exact ⟨hβk, Or.inr ⟨Or.inr rfl, hred⟩⟩
  · exact irgF4_map_ggRootSub (f4Datum (GaloisField 2 g)) q θ α hqα u' g0 hmapα
  · exact irgF4_map_ggRootSub (f4Datum (GaloisField 2 g)) q θ α hqα u' g0 hmapnegα

end CFSG.StandardType.RCKRP
