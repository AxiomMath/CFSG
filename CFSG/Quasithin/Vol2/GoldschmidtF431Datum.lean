module

public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Recognition.F4Local

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.QuasithinUnique

structure LieAmalgamExt (D : Type) [Group D] where
  Mbar : Subgroup (MulAut D)
  TD : Subgroup D
  P1 : Subgroup D
  P2 : Subgroup D
  inn_le : (MulAut.conj : D →* MulAut D).range ≤ Mbar
  yam : IsYAmalgamPair TD P1 P2
  diag : ∀ φ ∈ Mbar, φ ∈ autStab (P1 ⊓ P2) → φ ∈ autStab P1

namespace LieAmalgamExt

variable {D : Type} [Group D] (A : LieAmalgamExt D)

abbrev N1 : Subgroup (MulAut D) := A.Mbar ⊓ autStab A.P1

abbrev N2 : Subgroup (MulAut D) := A.Mbar ⊓ autStab A.P2

@[expose] def K : Subgroup (MulAut D) := A.N1 ⊔ A.N2

theorem N1_le_K : A.N1 ≤ A.K := le_sup_left

theorem N2_le_K : A.N2 ≤ A.K := le_sup_right

abbrev Mb1 : Subgroup ↥A.K := A.N1.subgroupOf A.K

abbrev Mb2 : Subgroup ↥A.K := A.N2.subgroupOf A.K

end LieAmalgamExt

structure LieExt (D : Type) [Group D] {G : Type} [Group G] (M1 M2 : Subgroup G)
    extends LieAmalgamExt D where
  iso : (RankTwoAmalgam.ofSubgroups M1 M2).Iso
    (RankTwoAmalgam.ofSubgroups (Mbar ⊓ autStab P1) (Mbar ⊓ autStab P2))

theorem isExtensionOfLieAmalgam_iff {D : Type} [Group D] {G : Type} [Group G]
    {M1 M2 : Subgroup G} : IsExtensionOfLieAmalgam D M1 M2 ↔ Nonempty (LieExt D M1 M2) :=
  ⟨fun ⟨Mbar, TD, P1, P2, h1, h2, h3, ⟨h4⟩⟩ => ⟨⟨⟨Mbar, TD, P1, P2, h1, h2, h3⟩, h4⟩⟩,
    fun ⟨E⟩ => ⟨E.Mbar, E.TD, E.P1, E.P2, E.inn_le, E.yam, E.diag, ⟨E.iso⟩⟩⟩

namespace LieExt

variable {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G} (E : LieExt D M1 M2)

@[expose] noncomputable def phi1 : ↥M1 ≃* ↥E.N1 := E.iso.φ1

@[expose] noncomputable def phi2 : ↥M2 ≃* ↥E.N2 := E.iso.φ2

@[expose] noncomputable def phi12 : ↥(M1 ⊓ M2) ≃* ↥(E.N1 ⊓ E.N2) := E.iso.φ12

theorem phi1_phi12 (g : ↥(M1 ⊓ M2)) :
    ((E.phi1 ⟨g.1, g.2.1⟩ : ↥E.N1) : MulAut D) = ((E.phi12 g : ↥(E.N1 ⊓ E.N2)) : MulAut D) :=
  (congrArg Subtype.val (E.iso.comm1 g)).symm

theorem phi2_phi12 (g : ↥(M1 ⊓ M2)) :
    ((E.phi2 ⟨g.1, g.2.2⟩ : ↥E.N2) : MulAut D) = ((E.phi12 g : ↥(E.N1 ⊓ E.N2)) : MulAut D) :=
  (congrArg Subtype.val (E.iso.comm2 g)).symm

@[expose] noncomputable def b1 : ↥E.Mb1 →* G :=
  M1.subtype.comp
    (E.phi1.symm.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe E.N1_le_K).toMonoidHom)

@[expose] noncomputable def b2 : ↥E.Mb2 →* G :=
  M2.subtype.comp
    (E.phi2.symm.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe E.N2_le_K).toMonoidHom)

theorem b1_apply (g : ↥E.K) (hg : g ∈ E.Mb1) :
    E.b1 ⟨g, hg⟩ = ((E.phi1.symm ⟨(g : MulAut D), hg⟩ : ↥M1) : G) := rfl

theorem b2_apply (g : ↥E.K) (hg : g ∈ E.Mb2) :
    E.b2 ⟨g, hg⟩ = ((E.phi2.symm ⟨(g : MulAut D), hg⟩ : ↥M2) : G) := rfl

theorem iso_agree (x : MulAut D) (h1 : x ∈ E.N1) (h2 : x ∈ E.N2) :
    ((E.phi1.symm ⟨x, h1⟩ : ↥M1) : G) = ((E.phi2.symm ⟨x, h2⟩ : ↥M2) : G) := by
  set y : ↥(M1 ⊓ M2) := E.phi12.symm ⟨x, ⟨h1, h2⟩⟩ with hy
  have hxy : ((E.phi12 y : ↥(E.N1 ⊓ E.N2)) : MulAut D) = x := by
    rw [hy, MulEquiv.apply_symm_apply]
  have e1 : E.phi1.symm ⟨x, h1⟩ = ⟨y.1, y.2.1⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext ((E.phi1_phi12 y).trans hxy).symm
  have e2 : E.phi2.symm ⟨x, h2⟩ = ⟨y.1, y.2.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext ((E.phi2_phi12 y).trans hxy).symm
  rw [e1, e2]

theorem comp : F431Comp E.Mb1 E.Mb2 E.b1 E.b2 :=
  ⟨M1.subtype_injective.comp (E.phi1.symm.injective.comp
      (Subgroup.subgroupOfEquivOfLe E.N1_le_K).injective),
    M2.subtype_injective.comp (E.phi2.symm.injective.comp
      (Subgroup.subgroupOfEquivOfLe E.N2_le_K).injective),
    fun g h1 h2 => by
      rw [b1_apply, b2_apply]
      exact E.iso_agree (g : MulAut D) h1 h2⟩

theorem range_b1 : E.b1.range = M1 := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (E.phi1.symm _).2
  · intro hg
    let a : ↥E.N1 := E.phi1 ⟨g, hg⟩
    have haK : (a : MulAut D) ∈ E.K := E.N1_le_K a.2
    have haM : (⟨(a : MulAut D), haK⟩ : ↥E.K) ∈ E.Mb1 := Subgroup.mem_subgroupOf.mpr a.2
    refine ⟨⟨_, haM⟩, ?_⟩
    rw [b1_apply]
    show ((E.phi1.symm a : ↥M1) : G) = g
    have : E.phi1.symm a = ⟨g, hg⟩ := MulEquiv.symm_apply_apply _ _
    rw [this]

theorem range_b2 : E.b2.range = M2 := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (E.phi2.symm _).2
  · intro hg
    let a : ↥E.N2 := E.phi2 ⟨g, hg⟩
    have haK : (a : MulAut D) ∈ E.K := E.N2_le_K a.2
    have haM : (⟨(a : MulAut D), haK⟩ : ↥E.K) ∈ E.Mb2 := Subgroup.mem_subgroupOf.mpr a.2
    refine ⟨⟨_, haM⟩, ?_⟩
    rw [b2_apply]
    show ((E.phi2.symm a : ↥M2) : G) = g
    have : E.phi2.symm a = ⟨g, hg⟩ := MulEquiv.symm_apply_apply _ _
    rw [this]

@[expose] noncomputable def β1 : ↥E.N1 →* ↥(M1 ⊔ M2) :=
  (Subgroup.inclusion (le_sup_left : M1 ≤ M1 ⊔ M2)).comp E.phi1.symm.toMonoidHom

@[expose] noncomputable def β2 : ↥E.N2 →* ↥(M1 ⊔ M2) :=
  (Subgroup.inclusion (le_sup_right : M2 ≤ M1 ⊔ M2)).comp E.phi2.symm.toMonoidHom

theorem β1_injective : Function.Injective E.β1 :=
  (Subgroup.inclusion_injective (le_sup_left : M1 ≤ M1 ⊔ M2)).comp E.phi1.symm.injective

theorem β2_injective : Function.Injective E.β2 :=
  (Subgroup.inclusion_injective (le_sup_right : M2 ≤ M1 ⊔ M2)).comp E.phi2.symm.injective

theorem β_agree (x : MulAut D) (h1 : x ∈ E.N1) (h2 : x ∈ E.N2) :
    E.β1 ⟨x, h1⟩ = E.β2 ⟨x, h2⟩ :=
  Subtype.ext (E.iso_agree x h1 h2)

theorem β_inter (y : ↥(M1 ⊔ M2)) (hy1 : y ∈ E.β1.range) (hy2 : y ∈ E.β2.range) :
    ∃ (x : MulAut D) (h1 : x ∈ E.N1) (_ : x ∈ E.N2), E.β1 ⟨x, h1⟩ = y := by
  obtain ⟨a, rfl⟩ := hy1
  obtain ⟨b, hb⟩ := hy2
  have hab : ((E.phi2.symm b : ↥M2) : G) = ((E.phi1.symm a : ↥M1) : G) := congrArg Subtype.val hb
  have hw1 : ((E.phi1.symm a : ↥M1) : G) ∈ M1 := (E.phi1.symm a).2
  have hw2 : ((E.phi1.symm a : ↥M1) : G) ∈ M2 := hab ▸ (E.phi2.symm b).2
  set w' : ↥(M1 ⊓ M2) := ⟨((E.phi1.symm a : ↥M1) : G), hw1, hw2⟩ with hw'
  have hx : ((E.phi12 w' : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.N1 := (E.phi12 w').2.1
  have hx2 : ((E.phi12 w' : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.N2 := (E.phi12 w').2.2
  refine ⟨_, hx, hx2, ?_⟩
  have e1 : (⟨((E.phi12 w' : ↥(E.N1 ⊓ E.N2)) : MulAut D), hx⟩ : ↥E.N1) = a := by
    have h := E.phi1_phi12 w'
    have e : E.phi1 ⟨w'.1, w'.2.1⟩ = a := by
      have : (⟨w'.1, w'.2.1⟩ : ↥M1) = E.phi1.symm a := Subtype.ext rfl
      rw [this, MulEquiv.apply_symm_apply]
    exact Subtype.ext (by rw [← h, e])
  rw [e1]

theorem β_gen : E.β1.range ⊔ E.β2.range = ⊤ := by
  have h1 : E.β1.range = (Subgroup.inclusion (le_sup_left : M1 ≤ M1 ⊔ M2)).range := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨E.phi1 m, by simp [β1]⟩
  have h2 : E.β2.range = (Subgroup.inclusion (le_sup_right : M2 ≤ M1 ⊔ M2)).range := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨E.phi2 m, by simp [β2]⟩
  rw [h1, h2]
  exact RankTwoAmalgam.range_inclusion_sup_eq_top M1 M2 (M1 ⊔ M2) rfl

end LieExt

end CFSG.Quasithin.H13.F431
