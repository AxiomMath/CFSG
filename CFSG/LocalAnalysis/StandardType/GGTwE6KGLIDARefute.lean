module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs
public import CFSG.LocalAnalysis.StandardType.GGNbrOutsideInndiag
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSU
import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem not_ggOutsideInndiag_of_innerOn {R : Type} [Group R] {J : Subgroup R} {t : MulAut R}
    {P : LargeEvenMarkProp ↥J} (hM : LargeEvenMarking ↥J P) (h : GGInnerOn J t) :
    ¬ GGOutsideInndiag J t := by
  rintro ⟨-, hout⟩
  obtain ⟨z, hz, hzt⟩ := h
  obtain ⟨hJ, lab, hlab, hraw⟩ := hM
  have hM' : LargeEvenMarking ↥J fun _ R' _ I' _ θ =>
      ∃ φ ∈ Subgroup.closure I', LargeEvenInduces θ (fun l l' : ↥J => (l' : R) = t l) φ := by
    refine ⟨hJ, lab, hlab, largeEvenRawDatum_mono ?_ (largeEvenRawDatum_inn_all hraw)⟩
    rintro R' _ I' F' ⟨⟨hs, hna, θ, -⟩, hinn⟩
    refine ⟨hs, hna, θ, MulAut.conj (θ (QuotientGroup.mk ⟨z, hz⟩)),
      Subgroup.subset_closure (hinn ⟨_, rfl⟩), fun l l' hll' => ?_⟩
    have hl' : l' = ⟨z, hz⟩ * l * (⟨z, hz⟩ : ↥J)⁻¹ :=
      Subtype.ext (by rw [hll', hzt l l.2]; rfl)
    subst hl'
    simp only [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
  obtain ⟨-, lab', -, hraw'⟩ := hout _ hM'
  obtain ⟨_, _, _, _, -, -, _, hPQ⟩ := largeEvenRawDatum_exists hraw'
  exact hPQ.2 hPQ.1

theorem not_ggOutsideInndiag_of_unitaryOn {R : Type} [Group R] {J : Subgroup R} {t : MulAut R}
    (h : GGUnitaryOn J t) : ¬ GGOutsideInndiag J t := by
  rintro ⟨hnorm, hout⟩
  obtain ⟨F, _, _, _, f, k, hF, hf, hk, hkq, φ, hφ, hker, A, hA, hAt⟩ := h
  have hback : ∀ B, InnerDiagSU.conjSU A hA (InnerDiagSU.conjSU A⁻¹ hA.inv B) = B := fun B =>
    Subtype.ext (by simp only [InnerDiagSU.coe_conjSU]; group)
  let τ : ↥J →* ↥J := (t.toMonoidHom.comp J.subtype).codRestrict J fun j => hnorm j j.2
  have hτ : Function.Bijective τ := by
    refine ⟨fun a b hab => Subtype.ext (t.injective (congrArg Subtype.val hab)), fun j => ?_⟩
    obtain ⟨B, rfl⟩ := hφ j
    exact ⟨φ (InnerDiagSU.conjSU A⁻¹ hA.inv B),
      Subtype.ext ((hAt _).trans (by rw [hback]))⟩
  let α : MulAut ↥J := MulEquiv.ofBijective τ hτ
  have hα : ∀ j : ↥J, (α j : R) = t j := fun _ => rfl
  have hαmem : α ∈ KGND.suConjSet φ := ⟨A, hA, fun B => Subtype.ext ((hα _).trans (hAt B))⟩
  obtain ⟨-, lab, -, hraw⟩ := hout _ (KGND.largeEvenMarking_suConjSet hF hf hk hkq φ hφ hker)
  obtain ⟨_, _, _, _, -, -, θ, ⟨-, hI⟩, hno⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨ψ, hψ, hψeq⟩ := hI α hαmem
  refine hno ⟨ψ, Subgroup.subset_closure hψ, fun l l' hll' => ?_⟩
  have hl' : α l = l' := Subtype.ext ((hα l).trans hll'.symm)
  rw [hψeq l, hl']

private theorem fixSubgroup_conj_map_symm {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
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

theorem ggInnerOrUnitaryOnComps_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : GGInnerOrUnitaryOnComps G) : GGInnerOrUnitaryOnComps G' := by
  intro x y hx3 hx1 hy3 hxy J hJ hstab
  set J₀ : Subgroup G := J.map e.symm.toMonoidHom with hJ₀def
  have hJ₀ : CFSG.Open.IsComponentOf J₀ (fixSubgroup (MulAut.conj (e.symm x))) := by
    rw [← fixSubgroup_conj_map_symm e x]
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
      (by rw [← map_mul, hxy, map_mul]) J₀ hJ₀ hstab₀ with ⟨z, hz, hzt⟩ | hun
  · refine Or.inl ⟨e z, (hmap z).1 hz, fun j hj => ?_⟩
    have hj₀ : e.symm j ∈ J₀ := (hmap _).2 (by rwa [MulEquiv.apply_symm_apply])
    have := congrArg e (hzt _ hj₀)
    rwa [hconj, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this
  · obtain ⟨F, _, _, _, f, k, hF, hf, hk, hkq, φ, hφ, hker, A, hA, hAt⟩ := hun
    let ε : ↥J₀ ≃* ↥J := (e.symm.subgroupMap J).symm
    have hε : ∀ w : ↥J₀, ((ε w : ↥J) : G') = e w := fun _ => rfl
    refine Or.inr ⟨F, inferInstance, inferInstance, inferInstance, f, k, hF, hf, hk, hkq,
      ε.toMonoidHom.comp φ, ε.surjective.comp hφ, fun B hB => hker ?_, A, hA, fun B => ?_⟩
    · exact ε.injective (by simpa using hB)
    · change MulAut.conj y ((ε (φ B) : ↥J) : G') = ((ε (φ _) : ↥J) : G')
      rw [hε, hε, ← hconj, hAt]

private theorem center_eq_bot_of_isSimpleGroup {R : Type} [Group R] (hR : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases hR.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

theorem ggInndiagOnCompBody_of_comps {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) (hR : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hfin : Finite R) (h : GGInnerOrUnitaryOnComps R) (s t : MulAut R) (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) (ht3 : t ^ 3 = 1) (hst : s * t = t * s) (hsI : s ∈ I) (htI : t ∈ I)
    (J₁ : Subgroup R) (hJ₁ : IsComponentOf J₁ (ggFix s)) {P : LargeEvenMarkProp ↥J₁}
    (hM : LargeEvenMarking ↥J₁ P) : ¬ GGOutsideInndiag J₁ t := by
  intro hout
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot
    (center_eq_bot_of_isSimpleGroup hR hna)
  obtain ⟨x, rfl⟩ := hI hsI
  obtain ⟨y, rfl⟩ := hI htI
  have hfix : ggFix (MulAut.conj x) = fixSubgroup (MulAut.conj x) :=
    Subgroup.ext fun _ => Iff.rfl
  have hstab : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut J₁ := by
    change J₁.map (MulAut.conj y).toMonoidHom = J₁
    have hle : J₁.map (MulAut.conj y).toMonoidHom ≤ J₁ := by
      rintro _ ⟨l, hl, rfl⟩
      exact hout.1 l hl
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
  rcases h x y (hinj (by rw [map_pow, hs3, map_one]))
      (fun h1 => hs1 (by rw [h1, map_one])) (hinj (by rw [map_pow, ht3, map_one]))
      (hinj (by rw [map_mul, map_mul, hst])) J₁
      (hfix ▸ CFSG.Assembly.isComponentOf_iff_open.1 hJ₁) hstab with hin | hun
  · exact not_ggOutsideInndiag_of_innerOn hM hin hout
  · exact not_ggOutsideInndiag_of_unitaryOn hun hout

end CFSG.StandardType.SCFourCover

end
