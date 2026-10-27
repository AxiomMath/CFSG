module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestr
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpSplit
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpFreeAbs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

theorem ggA6_sp_freeShape {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Finite F]
    [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) (hAB : A ≤ TauCeti.BilinForm.isometryGroup B) (hodd : Odd (Nat.card A))
    (hnil : Group.IsNilpotent ↥A) {J : Subgroup (V ≃ₗ[F] V)}
    (hJ : IsComponentOf J (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (A : Set (V ≃ₗ[F] V))))
    (hfix : ∀ j ∈ J, ∀ v ∈ ggA6SpFixed A, j v = v) : GGA6CharTwoLie ↥J := by
  classical
  let V₁ : Submodule F V := B.orthogonal (ggA6SpFixed A)
  obtain ⟨_hV₀nd, hcompl₀⟩ := ggA6_sp_fixed_nondegenerate B hB hnd A hAB hodd
  have hV₁orth : B.orthogonal V₁ = ggA6SpFixed A := by
    show B.orthogonal (B.orthogonal (ggA6SpFixed A)) = ggA6SpFixed A
    exact LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl (ggA6SpFixed A)
  have hcompl₁ : IsCompl V₁ (B.orthogonal V₁) := by
    rw [hV₁orth]
    exact hcompl₀.symm
  have hV₁reg : (B.restrict V₁).Nondegenerate :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal (B := B) (W := V₁)
      hB.isRefl).mpr hcompl₁
  let K : Subgroup (V ≃ₗ[F] V) := ggA6SpFixer B (B.orthogonal V₁)
  let L : Subgroup (V₁ ≃ₗ[F] V₁) := TauCeti.BilinForm.isometryGroup (B.restrict V₁)
  obtain ⟨e, he⟩ := ggA6_sp_restr_equiv B hB hnd V₁ hV₁reg
  have hAK : A ≤ K := by
    intro a ha
    refine ⟨hAB ha, ?_⟩
    intro u hu
    rw [hV₁orth] at hu
    exact hu a ha
  have hJK : J ≤ K := by
    intro j hj
    refine ⟨(hJ.1 hj).1, ?_⟩
    intro u hu
    rw [hV₁orth] at hu
    exact hfix j hj u hu
  let A_K : Subgroup ↥K := A.subgroupOf K
  let A_L : Subgroup ↥L := A_K.map e.toMonoidHom
  let A₁ : Subgroup (V₁ ≃ₗ[F] V₁) := A_L.map L.subtype
  let J_K : Subgroup ↥K := J.subgroupOf K
  let J_L : Subgroup ↥L := J_K.map e.toMonoidHom
  let J₁ : Subgroup (V₁ ≃ₗ[F] V₁) := J_L.map L.subtype
  have eA : ↥A ≃* ↥A₁ :=
    ((Subgroup.subgroupOfEquivOfLe hAK).symm.trans
      (A_K.equivMapOfInjective e.toMonoidHom e.injective)).trans
      (A_L.equivMapOfInjective L.subtype L.subtype_injective)
  have hodd₁ : Odd (Nat.card A₁) := by
    rw [← Nat.card_congr eA.toEquiv]
    exact hodd
  haveI : Group.IsNilpotent ↥A := hnil
  have hnil₁ : Group.IsNilpotent ↥A₁ := Group.nilpotent_of_mulEquiv eA
  have hA₁le : A₁ ≤ TauCeti.BilinForm.isometryGroup (B.restrict V₁) :=
    Subgroup.map_subtype_le A_L
  have hfree₁ : ∀ v : V₁, (∀ a ∈ A₁, a v = v) → v = 0 := by
    intro v hv
    refine (Submodule.mem_left_iff_eq_zero_of_disjoint (p := ggA6SpFixed A) (p' := V₁)
      hcompl₀.disjoint).mp ?_
    intro a ha
    have haK : a ∈ K := hAK ha
    have hmemA₁ : (e ⟨a, haK⟩ : V₁ ≃ₗ[F] V₁) ∈ A₁ := by
      refine Subgroup.mem_map.mpr ⟨e ⟨a, haK⟩, ?_, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hfixv : (e ⟨a, haK⟩ : V₁ ≃ₗ[F] V₁) v = v := hv _ hmemA₁
    have h1 := he ⟨a, haK⟩ v
    rw [hfixv] at h1
    exact h1.symm
  let C : Subgroup (V ≃ₗ[F] V) := Subgroup.centralizer (A : Set (V ≃ₗ[F] V))
  have hJC : J ≤ C := fun j hj => (hJ.1 hj).2
  have hJ_M : IsComponentOf J (K ⊓ C) := by
    refine ⟨fun x hx => ⟨hJK hx, hJC hx⟩, ?_, hJ.2.2⟩
    refine ggIsSubnormal_of_le_of_le hJ.2.1 (fun x hx => ⟨hJK hx, hJC hx⟩) ?_
    exact inf_le_inf_right C (fun x hx => hx.1)
  have hJ_K : IsComponentOf J_K ((K ⊓ C).subgroupOf K) := by
    refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := K.subtype)
      K.subtype_injective).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJK, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    exact hJ_M
  have hJ_L : IsComponentOf J_L ((K ⊓ C).subgroupOf K |>.map e.toMonoidHom) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := e.toMonoidHom)
      e.injective).mpr hJ_K
  have hM_L_eq : ((K ⊓ C).subgroupOf K).map e.toMonoidHom =
      Subgroup.centralizer (A_L : Set ↥L) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      have hgC : (g : V ≃ₗ[F] V) ∈ C := (Subgroup.mem_subgroupOf.mp hg).2
      have hbA : (b : V ≃ₗ[F] V) ∈ A := Subgroup.mem_subgroupOf.mp hb
      have hcomm : b * g = g * b :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC (b : V ≃ₗ[F] V) hbA)
      calc e b * e g = e (b * g) := (map_mul e b g).symm
        _ = e (g * b) := by rw [hcomm]
        _ = e g * e b := map_mul e g b
    · intro hx
      have hx' : ∀ y ∈ A_L, y * x = x * y := Subgroup.mem_centralizer_iff.mp hx
      refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      refine Subgroup.mem_subgroupOf.mpr ⟨(e.symm x).2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a ha
      have hmem : e ⟨a, hAK ha⟩ ∈ A_L :=
        Subgroup.mem_map.mpr ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have key := hx' (e ⟨a, hAK ha⟩) hmem
      have hcommK : (⟨a, hAK ha⟩ : ↥K) * e.symm x = e.symm x * ⟨a, hAK ha⟩ :=
        e.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact key)
      simpa using congrArg Subtype.val hcommK
  have hJ_Lcent : IsComponentOf J_L (Subgroup.centralizer (A_L : Set ↥L)) := by
    rw [hM_L_eq] at hJ_L
    exact hJ_L
  have hcent_map : (Subgroup.centralizer (A_L : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer (A₁ : Set (V₁ ≃ₗ[F] V₁)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      simpa using congrArg L.subtype ((Subgroup.mem_centralizer_iff.mp hy) b hb)
    · rintro ⟨hxL, hxcent⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro b hb
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxcent) (L.subtype b) ⟨b, hb, rfl⟩)
  have hJ₁ : IsComponentOf J₁
      (TauCeti.BilinForm.isometryGroup (B.restrict V₁) ⊓
        Subgroup.centralizer (A₁ : Set (V₁ ≃ₗ[F] V₁))) := by
    have h1 : IsComponentOf J₁ ((Subgroup.centralizer (A_L : Set ↥L)).map L.subtype) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := L.subtype)
        L.subtype_injective).mpr hJ_Lcent
    rwa [hcent_map] at h1
  have hB' : (B.restrict V₁).IsAlt := by
    intro x
    change B (x : V) (x : V) = 0
    exact hB x
  have hres : GGA6CharTwoLie ↥J₁ :=
    ggA6_sp_freeShape_abs (B := B.restrict V₁) hB' hV₁reg (A := A₁) hA₁le hodd₁ hnil₁ hfree₁
      (J := J₁) hJ₁
  have eJ : ↥J ≃* ↥J₁ :=
    ((Subgroup.subgroupOfEquivOfLe hJK).symm.trans
      (J_K.equivMapOfInjective e.toMonoidHom e.injective)).trans
      (J_L.equivMapOfInjective L.subtype L.subtype_injective)
  exact GGA6CharTwoLie.of_mulEquiv eJ.symm hres

end CFSG.StandardType.A6Red

end
