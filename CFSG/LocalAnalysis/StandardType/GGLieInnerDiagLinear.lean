module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrOutsideInndiag
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSL
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDARefute

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem ltlin_conjSL_inv {m : ℕ} {F : Type} [Field F] (A : GL (Fin (m + 1)) F)
    (B : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL A (InnerDiagA.conjSL A⁻¹ B) = B := by
  apply (InnerDiagA.slEquiv m F).injective
  rw [InnerDiagA.slEquiv_conjSL, InnerDiagA.slEquiv_conjSL]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  group

theorem not_ggOutsideInndiag_of_linearOn {R : Type} [Group R] {J : Subgroup R} {t : MulAut R}
    (h : GGLinearOn J t) : ¬ GGOutsideInndiag J t := by
  rintro ⟨hnorm, hout⟩
  obtain ⟨F, _, _, f, m, hF, hf, hm, hm1, φ, hφ, hker, A, hA⟩ := h
  have hback : ∀ B, InnerDiagA.conjSL A (InnerDiagA.conjSL A⁻¹ B) = B :=
    fun B => ltlin_conjSL_inv A B
  let τ : ↥J →* ↥J := (t.toMonoidHom.comp J.subtype).codRestrict J fun j => hnorm j j.2
  have hτ : Function.Bijective τ := by
    refine ⟨fun a b hab => Subtype.ext (t.injective (congrArg Subtype.val hab)), fun j => ?_⟩
    obtain ⟨B, rfl⟩ := hφ j
    exact ⟨φ (InnerDiagA.conjSL A⁻¹ B), Subtype.ext ((hA _).trans (by rw [hback]))⟩
  let α : MulAut ↥J := MulEquiv.ofBijective τ hτ
  have hα : ∀ j : ↥J, (α j : R) = t j := fun _ => rfl
  have hαmem : α ∈ KGND.slConjSet φ := ⟨A, fun B => Subtype.ext ((hα _).trans (hA B))⟩
  obtain ⟨-, lab, -, hraw⟩ := hout _ (KGND.largeEvenMarking_slConjSet hF hf hm hm1 φ hφ hker)
  obtain ⟨_, _, _, _, -, -, θ, ⟨-, hI⟩, hno⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨ψ, hψ, hψeq⟩ := hI α hαmem
  refine hno ⟨ψ, Subgroup.subset_closure hψ, fun l l' hll' => ?_⟩
  have hl' : α l = l' := Subtype.ext ((hα l).trans hll'.symm)
  rw [hψeq l, hl']

private theorem ltlin_fixSubgroup_conj_map_symm {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (x : G') : (fixSubgroup (MulAut.conj x)).map e.symm.toMonoidHom =
      fixSubgroup (MulAut.conj (e.symm x)) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_fixSubgroup, mem_fixSubgroup, MulAut.conj_apply,
    MulAut.conj_apply, MulEquiv.symm_symm]
  constructor
  · intro h
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h
  · intro h
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using congrArg e h

theorem ggInnerDiagOnComps_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : GGInnerDiagOnComps G) : GGInnerDiagOnComps G' := by
  intro x y hx3 hx1 hy3 hxy J hJ hstab
  set J₀ : Subgroup G := J.map e.symm.toMonoidHom with hJ₀def
  have hJ₀ : CFSG.Open.IsComponentOf J₀ (fixSubgroup (MulAut.conj (e.symm x))) := by
    rw [← ltlin_fixSubgroup_conj_map_symm e x]
    exact ⟨Subgroup.map_mono hJ.1, hJ.2.1.map _,
      CFSG.Open.IsQuasisimple.of_mulEquiv
        (J.equivMapOfInjective _ e.symm.injective).symm hJ.2.2⟩
  have hstab₀ : MulAut.conj (e.symm y) ∈ CFSG.GroupActions.subgroupStabAut J₀ := by
    change J₀.map (MulAut.conj (e.symm y)).toMonoidHom = J₀
    have hJy : J.map (MulAut.conj y).toMonoidHom = J := hstab
    have hcomp : (MulAut.conj (e.symm y)).toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
      ext g
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [hJ₀def, Subgroup.map_map, hcomp, ← Subgroup.map_map, hJy]
  have hmap : ∀ w : G, w ∈ J₀ ↔ e w ∈ J := fun w => by
    rw [hJ₀def, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hconj : ∀ w : G, e (MulAut.conj (e.symm y) w) = MulAut.conj y (e w) := fun w => by
    simp [MulAut.conj_apply, map_mul, map_inv]
  rcases h (e.symm x) (e.symm y) (by rw [← map_pow, hx3, map_one])
      (fun h1 => hx1 (by simpa using congrArg e h1)) (by rw [← map_pow, hy3, map_one])
      (by rw [← map_mul, hxy, map_mul]) J₀ hJ₀ hstab₀ with ⟨z, hz, hzt⟩ | hun | hlin
  · refine Or.inl ⟨e z, (hmap z).1 hz, fun j hj => ?_⟩
    have hj₀ : e.symm j ∈ J₀ := (hmap _).2 (by rwa [MulEquiv.apply_symm_apply])
    have := congrArg e (hzt _ hj₀)
    rwa [hconj, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this
  · obtain ⟨F, _, _, _, f, k, hF, hf, hk, hkq, φ, hφ, hker, A, hA, hAt⟩ := hun
    let ε : ↥J₀ ≃* ↥J := (e.symm.subgroupMap J).symm
    have hε : ∀ w : ↥J₀, ((ε w : ↥J) : G') = e w := fun _ => rfl
    refine Or.inr (Or.inl ⟨F, inferInstance, inferInstance, inferInstance, f, k, hF, hf, hk, hkq,
      ε.toMonoidHom.comp φ, ε.surjective.comp hφ, fun B hB => hker ?_, A, hA, fun B => ?_⟩)
    · exact ε.injective (by simpa using hB)
    · change MulAut.conj y ((ε (φ B) : ↥J) : G') = ((ε (φ _) : ↥J) : G')
      rw [hε, hε, ← hconj, hAt]
  · obtain ⟨F, _, _, f, m, hF, hf, hm, hm1, φ, hφ, hker, A, hA⟩ := hlin
    let ε : ↥J₀ ≃* ↥J := (e.symm.subgroupMap J).symm
    have hε : ∀ w : ↥J₀, ((ε w : ↥J) : G') = e w := fun _ => rfl
    refine Or.inr (Or.inr ⟨F, inferInstance, inferInstance, f, m, hF, hf, hm, hm1,
      ε.toMonoidHom.comp φ, ε.surjective.comp hφ, fun B hB => hker ?_, A, fun B => ?_⟩)
    · exact ε.injective (by simpa using hB)
    · change MulAut.conj y ((ε (φ B) : ↥J) : G') = ((ε (φ _) : ↥J) : G')
      rw [hε, hε, ← hconj, hA]

theorem not_ggOutsideInndiag_of_innerDiagOnComps {R : Type} [Group R] [Finite R]
    (h : GGInnerDiagOnComps R) {x y : R} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) {J₁ : Subgroup R}
    (hJ₁ : CFSG.Open.IsComponentOf J₁ (fixSubgroup (MulAut.conj x)))
    {P : LargeEvenMarkProp ↥J₁} (hM : LargeEvenMarking ↥J₁ P) :
    ¬ GGOutsideInndiag J₁ (MulAut.conj y) := by
  intro hout
  have hstab : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut J₁ := by
    change J₁.map (MulAut.conj y).toMonoidHom = J₁
    have hle : J₁.map (MulAut.conj y).toMonoidHom ≤ J₁ := by
      rintro _ ⟨l, hl, rfl⟩
      exact hout.1 l hl
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
  rcases h x y hx3 hx1 hy3 hxy J₁ hJ₁ hstab with hin | hun | hlin
  · exact not_ggOutsideInndiag_of_innerOn hM hin hout
  · exact not_ggOutsideInndiag_of_unitaryOn hun hout
  · exact not_ggOutsideInndiag_of_linearOn hlin hout

end CFSG.StandardType.SCFourCover

end
