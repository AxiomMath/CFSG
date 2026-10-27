module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {G : Type*} [Group G] [Finite G]

@[expose] def projFam (Ω : Set (Subgroup G)) (D : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ X ∈ Ω, Y = projIn Ω X D}

theorem nonempty_mulEquiv_projIn {A M D : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsRegFam A M Ω ⊥) (hDM : D ≤ M) (hDA : D ≤ Subgroup.centralizer (A : Set G))
    {X : Subgroup G} (hX : X ∈ Ω) : Nonempty (↥(projIn Ω X D) ≃* ↥D) := by
  have hdp := hΩ.isDirectProduct
  let φ : ↥D →* G := X.subtype.comp ((hdp.coord hX).comp (Subgroup.inclusion hDM))
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    have h1 : hdp.coord hX ⟨d, hDM d.2⟩ = 1 := Subtype.ext (MonoidHom.mem_ker.mp hd)
    have h2 : (d : G) ∈ sSup (Ω \ {X}) := (hdp.coord_eq_one_iff hX ⟨d, hDM d.2⟩).mp h1
    have h3 : (d : G) ∈ M ⊓ Subgroup.centralizer (A : Set G) ⊓ sSup (Ω \ {X}) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hDM d.2, hDA d.2⟩, h2⟩
    rw [inf_centralizer_inf_sSup_eq_bot_of_transitive hdp hΩ.map_conj_mem hX
      (hΩ.transitive X hX), Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  have hrange : φ.range = projIn Ω X D := by
    ext x
    rw [MonoidHom.mem_range, hdp.mem_projIn_iff hX]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨⟨d, hDM d.2⟩, d.2, rfl⟩
    · rintro ⟨y, hyD, rfl⟩
      exact ⟨⟨y, hyD⟩, rfl⟩
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem map_conj_projIn_le {A M D : Subgroup G} {Ω : Set (Subgroup G)}
    (hdp : IsDirectProduct Ω M) (hA : ∀ a ∈ A, ∀ J ∈ Ω, J.map (MulAut.conj a).toMonoidHom ∈ Ω)
    (hDA : D ≤ Subgroup.centralizer (A : Set G)) {a : G} (ha : a ∈ A)
    {X : Subgroup G} (hX : X ∈ Ω) :
    (projIn Ω X D).map (MulAut.conj a).toMonoidHom ≤
      projIn Ω (X.map (MulAut.conj a).toMonoidHom) D := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyD, hyx⟩ := (hdp.mem_projIn_iff hX).mp hx
  rw [hdp.mem_projIn_iff (hA a ha X hX)]
  have hya : a * (y : G) * a⁻¹ = y := by
    have h1 := Subgroup.mem_centralizer_iff.mp (hDA hyD) a ha
    rw [h1]
    group
  refine ⟨⟨a * (y : G) * a⁻¹, hdp.conj_mem (hA a ha) y.2⟩, ?_, ?_⟩
  · change a * (y : G) * a⁻¹ ∈ D
    rw [hya]
    exact hyD
  · have h1 := hdp.coord_conj (hA a ha) hX y.2
    rw [← hyx]
    exact h1

theorem map_conj_projIn_eq {A M D : Subgroup G} {Ω : Set (Subgroup G)}
    (hdp : IsDirectProduct Ω M) (hA : ∀ a ∈ A, ∀ J ∈ Ω, J.map (MulAut.conj a).toMonoidHom ∈ Ω)
    (hDA : D ≤ Subgroup.centralizer (A : Set G)) {a : G} (ha : a ∈ A)
    {X : Subgroup G} (hX : X ∈ Ω) :
    (projIn Ω X D).map (MulAut.conj a).toMonoidHom =
      projIn Ω (X.map (MulAut.conj a).toMonoidHom) D := by
  refine le_antisymm (map_conj_projIn_le hdp hA hDA ha hX) ?_
  have h1 := map_conj_projIn_le hdp hA hDA (inv_mem ha) (hA a ha X hX)
  rw [Near.Thm210.map_conj_map_conj, inv_mul_cancel, Near.Thm210.map_conj_one] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) h1
  rwa [Near.Thm210.map_conj_map_conj, mul_inv_cancel, Near.Thm210.map_conj_one] at h2

theorem isRegFam_projFam {A M D : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : IsRegFam A M Ω ⊥)
    (hDM : D ≤ M) (hDA : D ≤ Subgroup.centralizer (A : Set G)) (hD1 : D ≠ ⊥) :
    IsRegFam A (sSup (projFam Ω D)) (projFam Ω D) ⊥ := by
  have hdp := hΩ.isDirectProduct
  have hne : ∀ X ∈ Ω, projIn Ω X D ≠ ⊥ := by
    intro X hX hbot
    obtain ⟨e⟩ := nonempty_mulEquiv_projIn hΩ hDM hDA hX
    apply hD1
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [← Nat.card_congr e.toEquiv, hbot]
    exact Subgroup.card_bot
  have hconj := fun a (ha : a ∈ A) X (hX : X ∈ Ω) =>
    map_conj_projIn_eq hdp hΩ.map_conj_mem hDA ha hX
  refine ⟨⟨?_, ?_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X₁, hX₁, rfl⟩ _ ⟨X₂, hX₂, rfl⟩ hne' x hx y hy
    have hX : X₁ ≠ X₂ := fun h => hne' (by rw [h])
    exact hdp.commute X₁ hX₁ X₂ hX₂ hX x (projIn_le X₁ D hx) y (projIn_le X₂ D hy)
  · rintro _ ⟨X, hX, rfl⟩
    have hle : sSup (projFam Ω D \ {projIn Ω X D}) ≤ sSup (Ω \ {X}) := by
      refine sSup_le ?_
      rintro _ ⟨⟨X', hX', rfl⟩, hne'⟩
      have hXX : X' ≠ X := fun h => hne' (by rw [h]; rfl)
      exact (projIn_le X' D).trans (le_sSup ⟨hX', hXX⟩)
    exact Disjoint.mono (projIn_le X D) hle (hdp.indep hX)
  · obtain ⟨X, hX⟩ := hΩ.nonempty
    exact ⟨_, X, hX, rfl⟩
  · rintro _ ⟨X, hX, rfl⟩
    exact hne X hX
  · rintro a ha _ ⟨X, hX, rfl⟩
    exact ⟨_, hΩ.map_conj_mem a ha X hX, hconj a ha X hX⟩
  · rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩
    obtain ⟨a, ha, rfl⟩ := hΩ.transitive X hX X' hX'
    exact ⟨a, ha, (hconj a ha X hX).symm⟩
  · rintro _ ⟨X, hX, rfl⟩
    refine eq_bot_iff.mpr fun a ha => ?_
    obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
    have h1 : (projIn Ω X D).map (MulAut.conj a).toMonoidHom = projIn Ω X D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
    rw [hconj a haA X hX] at h1
    by_contra ha1
    have hXa := hΩ.map_conj_mem a haA X hX
    have hdisj : Disjoint X (X.map (MulAut.conj a).toMonoidHom) :=
      hdp.indep.pairwiseDisjoint hX hXa (hΩ.map_conj_ne haA ha1 hX).symm
    exact hne X hX (disjoint_self.mp (hdisj.mono (projIn_le X D)
      ((le_of_eq h1.symm).trans (projIn_le _ D))))

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
