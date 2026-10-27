module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporKRest_sylow_le {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hp : p.Prime) (hE : IsElemAbelian p E) (hE2 : Nat.card E = p ^ 2)
    (hctl : GGControlsStrongFusion H E) :
    ∃ P : Sylow p W, E ≤ (P : Subgroup W) ∧ (P : Subgroup W) ≤ H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEH : E ≤ H := hctl.1
  have hcard_ne : Nat.card E ≠ 1 := by
    rw [hE2]
    exact ne_of_gt (one_lt_pow₀ hp.one_lt (by norm_num))
  have hEne : E ≠ ⊥ := by
    intro hbot
    exact hcard_ne (by rw [hbot, Subgroup.card_bot])
  have hEp : IsPGroup p E := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    exact ⟨1, fun g => Subtype.ext (by simpa using hE.2 (g : W) g.2)⟩
  have hEsub : IsPGroup p (E.subgroupOf H) := IsPGroup.comap_subtype hEp
  obtain ⟨T, hET⟩ := IsPGroup.exists_le_sylow hEsub
  let T' : Subgroup W := (T : Subgroup ↥H).map H.subtype
  have hT'def : T' = (T : Subgroup ↥H).map H.subtype := rfl
  have hT'le : T' ≤ H := by
    rw [hT'def]
    exact Subgroup.map_subtype_le _
  have hET' : E ≤ T' := by
    have h := Subgroup.map_mono (f := H.subtype) hET
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEH] at h
    rw [hT'def]
    exact h
  have hT'p : IsPGroup p T' := by
    rw [hT'def]
    exact IsPGroup.map (Sylow.isPGroup' T) H.subtype
  have hT'max : ∀ Q : Subgroup W, IsPGroup p Q → T' ≤ Q → Q ≤ H → Q = T' := by
    intro Q hQp hT'Q hQH
    have hQsub : IsPGroup p (Q.subgroupOf H) := IsPGroup.comap_subtype hQp
    have hle : (T : Subgroup ↥H) ≤ Q.subgroupOf H := by
      intro x hx
      exact hT'Q (by
        rw [hT'def]
        exact (Subgroup.mem_map_iff_mem H.subtype_injective).mpr hx)
    have hEq : Q.subgroupOf H = (T : Subgroup ↥H) := Sylow.is_maximal' T hQsub hle
    calc Q = (Q.subgroupOf H).map H.subtype := by
          simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQH]
      _ = T' := by simp only [hEq, hT'def]
  obtain ⟨P, hT'P⟩ := IsPGroup.exists_le_sylow hT'p
  have hPp : IsPGroup p (P : Subgroup W) := Sylow.isPGroup' P
  have hPT' : (P : Subgroup W) = T' := by
    by_contra hne
    have hlt : T' < (P : Subgroup W) := lt_of_le_of_ne hT'P (Ne.symm hne)
    have hgrow := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hPp hlt
    obtain ⟨-, g, hg, hgnot⟩ := SetLike.lt_iff_le_and_exists.mp hgrow
    have hgP : g ∈ (P : Subgroup W) := (Subgroup.mem_inf.mp hg).1
    have hgN : g ∈ Subgroup.normalizer (T' : Set W) := (Subgroup.mem_inf.mp hg).2
    have hmaple : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ T' := by
      rintro y ⟨e, he, rfl⟩
      have hmem := (Subgroup.mem_normalizer_iff''.mp hgN e).mp (hET' he)
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem
    have hmapne : E.map (MulAut.conj g⁻¹).toMonoidHom ≠ ⊥ := by
      have hf : Function.Injective ((MulAut.conj g⁻¹).toMonoidHom) :=
        (MulAut.conj g⁻¹).injective
      intro h
      exact hEne
        ((Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) E hf).mp h)
    have hginf : E.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H ≠ ⊥ := by
      rw [inf_of_le_left (le_trans hmaple hT'le)]
      exact hmapne
    have hgH : g ∈ H := hctl.2 g hginf
    have hzpg : Subgroup.zpowers g ≤ (P : Subgroup W) := Subgroup.zpowers_le.mpr hgP
    have hzpp : IsPGroup p (Subgroup.zpowers g) := IsPGroup.to_le hPp hzpg
    have hsupP : IsPGroup p ↥(T' ⊔ Subgroup.zpowers g) :=
      IsPGroup.to_sup_of_normal_left' hT'p hzpp (Subgroup.zpowers_le.mpr hgN)
    have hsupH : T' ⊔ Subgroup.zpowers g ≤ H :=
      sup_le hT'le (Subgroup.zpowers_le.mpr hgH)
    have hEq := hT'max (T' ⊔ Subgroup.zpowers g) hsupP le_sup_left hsupH
    exact hgnot (by
      rw [← hEq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  exact ⟨P, by rw [hPT']; exact hET', by rw [hPT']; exact hT'le⟩

theorem ggSporKRest_controls_subgroupOf {W : Type} [Group W] {H E F : Subgroup W}
    (hctl : GGControlsStrongFusion H E) :
    SporKRestControls (E.subgroupOf F) (H.subgroupOf F) := by
  unfold SporKRestControls SporKRestControlsAt
  intro e he he1 g hg
  exact Subgroup.mem_subgroupOf.mpr
    ((ggControlsStrongFusion_iff.mp hctl).2 (e : W) (Subgroup.mem_subgroupOf.mp he)
      (fun h => he1 (Subtype.ext h)) (g : W) (Subgroup.mem_subgroupOf.mp hg))

theorem ggSporKRest_sylow_subgroupOf {W : Type} [Group W] {p : ℕ} {H F : Subgroup W}
    (P : Sylow p W) (hPF : (P : Subgroup W) ≤ F) (hPH : (P : Subgroup W) ≤ H) :
    ∃ S : Sylow p ↥F, (S : Subgroup ↥F) ≤ H.subgroupOf F := by
  refine ⟨P.subtype hPF, ?_⟩
  intro x hx
  rw [Sylow.coe_subtype P hPF] at hx
  exact Subgroup.mem_subgroupOf.mpr (hPH (Subgroup.mem_subgroupOf.mp hx))

end CFSG.StandardType.SporadicShape
