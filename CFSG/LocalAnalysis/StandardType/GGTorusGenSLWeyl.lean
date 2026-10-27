module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma ggActsDiag_of_actsDiag {d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    {X : Type} [Group X] {j : L' →* X} {a : MulAut L'} {b : X} {t : Fin d → K}
    (ht : TypeANbrDvd.ActsDiag φ' a t)
    (hb : ∀ s, j (a (φ' s)) = b * j (φ' s) * b⁻¹) :
    GGActsDiag (j.comp φ') b := by
  obtain ⟨D, hD, haD⟩ := ht
  let h : Fin d → Kˣ := fun k => Units.mk0 (t k) (TypeANbrDvd.ActsDiag.ne_zero ⟨D, hD, haD⟩ k)
  have hDg : D = ggDiagUnit h := by
    apply Units.ext
    rw [hD]
    rfl
  refine ⟨h, fun s => ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hb s, haD s, hDg]
  rfl

theorem permSL_lift_mem_normalizer_typeA
    {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE)
    {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    (hdiag : ∀ e : E, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t)
    (σ : Equiv.Perm (Fin d)) :
    ((φ' (TypeA.permSL σ) : L') : M) ∈ Subgroup.normalizer (E : Set M) := by
  classical
  cases d with
  | zero =>
    have hperm : TypeA.permSL σ = (1 : SpecialLinearGroup (Fin 0) K) := by
      apply Subtype.ext
      change σ.permMatrix K = (1 : Matrix (Fin 0) (Fin 0) K)
      funext i
      exact Fin.elim0 i
    rw [hperm, map_one, Subgroup.coe_one]
    exact Subgroup.one_mem _
  | succ n =>
    let H : Subgroup M := E ⊔ L'
    let Bs : Subgroup ↥H := E.comap H.subtype
    set φ : SpecialLinearGroup (Fin (n + 1)) K →* ↥H :=
      (Subgroup.inclusion (show L' ≤ H from le_sup_right)).comp φ' with hφ
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hperm : TypeA.permSL σ = slPerm h2 σ⁻¹ := by
      have hπ : slPerm h2 σ⁻¹ = TypeA.permSL (σ⁻¹)⁻¹ := by
        apply Subtype.ext
        rw [coe_slPerm, TypeA.coe_permSL, signedPerm_one_eq_permMatrix]
      simpa using hπ.symm
    have hkerφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) K) := by
      rw [hφ]
      intro g hg
      have hg' : φ' g = 1 := by
        apply Subtype.ext
        simpa using congrArg (fun x : ↥H => (x : M)) hg
      exact scalars_le_center (n + 1) K (hker g hg')
    have hBp : ∀ b ∈ Bs, b ^ p = 1 := fun b hb =>
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hpos.2.1.2 (b : M) hb)
    have hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set ↥H), g ^ p = 1 → g ∈ Bs := by
      intro g hg hgp
      refine hpos.2.2.2.2.2.1 (g : M) g.2 ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro e he
        let eH : ↥H := ⟨e, (le_sup_left : E ≤ H) he⟩
        exact congrArg (fun x : ↥H => (x : M))
          ((Subgroup.mem_centralizer_iff.mp hg) eH (show eH ∈ Bs from he))
      · rw [← Subgroup.coe_pow, hgp, Subgroup.coe_one]
    have hdiagφ : ∀ b ∈ Bs, GGActsDiag φ b := by
      intro b hb
      let e : E := ⟨(b : M), hb⟩
      obtain ⟨t, ht⟩ := hdiag e
      have hb' : ∀ s, Subgroup.inclusion (show L' ≤ H from le_sup_right)
            (L'.normalizerMonoidHom ⟨e, hE e.2⟩ (φ' s)) =
          b * Subgroup.inclusion (show L' ≤ H from le_sup_right) (φ' s) * b⁻¹ := by
        intro s
        apply Subtype.ext
        show ((L'.normalizerMonoidHom ⟨e, hE e.2⟩) (φ' s) : M) = (b : M) * (φ' s : M) * (b : M)⁻¹
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE e.2⟩ (φ' s)]
      rw [hφ]
      exact ggActsDiag_of_actsDiag (j := Subgroup.inclusion (show L' ≤ H from le_sup_right)) ht hb'
    have hmain : φ (slPerm h2 σ⁻¹) ∈ Subgroup.normalizer (Bs : Set ↥H) :=
      slPerm_mem_normalizer_of_actsDiag (X := ↥H) (F := K) (p := p) (Bs := Bs)
        (n := n) (φ := φ) h2 hBp hBs hkerφ hdiagφ σ⁻¹
    have hmap : (E.comap H.subtype).map H.subtype = E :=
      Subgroup.map_comap_eq_self (f := H.subtype) (H := E)
        (by rw [Subgroup.subtype_range]; exact (le_sup_left : E ≤ H))
    rw [hperm]
    have hmem : (φ (slPerm h2 σ⁻¹) : M) ∈
        Subgroup.normalizer (((E.comap H.subtype).map H.subtype : Subgroup M) : Set M) :=
      Subgroup.le_normalizer_map (H := E.comap H.subtype) H.subtype ⟨_, hmain, rfl⟩
    rw [hmap] at hmem
    exact hmem

end CFSG.StandardType
