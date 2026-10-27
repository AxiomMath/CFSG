module

public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.F1

open CFSG.Quasithin

variable {X Y : Type} [Group X] [Group Y]

@[expose] noncomputable def restrictEquiv {G A : Subgroup X} {M C : Subgroup Y} (e : ↥G ≃* ↥M)
    (hA : A ≤ G) (hC : C ≤ M) (h : ∀ x : ↥G, (x : X) ∈ A ↔ ((e x : ↥M) : Y) ∈ C) :
    ↥A ≃* ↥C :=
  MulEquiv.ofBijective
    ({ toFun := fun a => ⟨(e ⟨a, hA a.2⟩ : Y), (h ⟨a, hA a.2⟩).mp a.2⟩
       map_one' := Subtype.ext (by
         show ((e 1 : ↥M) : Y) = 1
         rw [map_one, OneMemClass.coe_one])
       map_mul' := fun a b => Subtype.ext (by
         show ((e (⟨a, hA a.2⟩ * ⟨b, hA b.2⟩) : ↥M) : Y) = _
         rw [map_mul, Subgroup.coe_mul]
         rfl) } : ↥A →* ↥C)
    ⟨fun a b hab => by
      have h1 : ((e ⟨a, hA a.2⟩ : ↥M) : Y) = ((e ⟨b, hA b.2⟩ : ↥M) : Y) := by
        have := congrArg Subtype.val hab
        exact this
      have h2 := e.injective (Subtype.ext h1)
      apply Subtype.ext
      have := congrArg Subtype.val h2
      exact this,
    fun c => by
      set g := e.symm ⟨c, hC c.2⟩ with hg
      have hgA : (g : X) ∈ A := (h g).mpr (by rw [hg, MulEquiv.apply_symm_apply]; exact c.2)
      refine ⟨⟨g, hgA⟩, Subtype.ext ?_⟩
      show ((e ⟨(g : X), hA hgA⟩ : ↥M) : Y) = c
      rw [show (⟨(g : X), hA hgA⟩ : ↥G) = g from rfl, hg, MulEquiv.apply_symm_apply]⟩

theorem coe_restrictEquiv {G A : Subgroup X} {M C : Subgroup Y} (e : ↥G ≃* ↥M) (hA : A ≤ G)
    (hC : C ≤ M) (h : ∀ x : ↥G, (x : X) ∈ A ↔ ((e x : ↥M) : Y) ∈ C) (a : ↥A) :
    ((restrictEquiv e hA hC h a : ↥C) : Y) = ((e ⟨a, hA a.2⟩ : ↥M) : Y) := rfl

section Iso

variable {G₁ G₂ : Subgroup X} {M₁ M₂ : Subgroup Y}
  (Φ : (RankTwoAmalgam.ofSubgroups G₁ G₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))

@[expose] def isoφ1 : ↥G₁ ≃* ↥M₁ := Φ.φ1

@[expose] def isoφ12 : ↥(G₁ ⊓ G₂) ≃* ↥(M₁ ⊓ M₂) := Φ.φ12

@[expose] def isoφ2 : ↥G₂ ≃* ↥M₂ := Φ.φ2

theorem coe_isoφ12_eq_φ1 (x : ↥(G₁ ⊓ G₂)) :
    ((isoφ12 Φ x : ↥(M₁ ⊓ M₂)) : Y) = ((isoφ1 Φ ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ : ↥M₁) : Y) :=
  congrArg Subtype.val (Φ.comm1 x)

theorem coe_isoφ12_eq_φ2 (x : ↥(G₁ ⊓ G₂)) :
    ((isoφ12 Φ x : ↥(M₁ ⊓ M₂)) : Y) = ((isoφ2 Φ ⟨x, (Subgroup.mem_inf.mp x.2).2⟩ : ↥M₂) : Y) :=
  congrArg Subtype.val (Φ.comm2 x)

@[expose] noncomputable def ofSubgroupsIsoRestrict {A₁ A₂ : Subgroup X} {C₁ C₂ : Subgroup Y}
    (hA₁ : A₁ ≤ G₁) (hA₂ : A₂ ≤ G₂) (hC₁ : C₁ ≤ M₁) (hC₂ : C₂ ≤ M₂)
    (h₁ : ∀ x : ↥G₁, (x : X) ∈ A₁ ↔ ((isoφ1 Φ x : ↥M₁) : Y) ∈ C₁)
    (h₂ : ∀ x : ↥G₂, (x : X) ∈ A₂ ↔ ((isoφ2 Φ x : ↥M₂) : Y) ∈ C₂) :
    (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups C₁ C₂) where
  φ1 := restrictEquiv (isoφ1 Φ) hA₁ hC₁ h₁
  φ12 := restrictEquiv (isoφ12 Φ) (inf_le_inf hA₁ hA₂) (inf_le_inf hC₁ hC₂) fun x => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h₁ ⟨x, (Subgroup.mem_inf.mp x.2).1⟩,
      h₂ ⟨x, (Subgroup.mem_inf.mp x.2).2⟩, ← coe_isoφ12_eq_φ1 Φ x, ← coe_isoφ12_eq_φ2 Φ x]
  φ2 := restrictEquiv (isoφ2 Φ) hA₂ hC₂ h₂
  comm1 := fun (g : ↥(A₁ ⊓ A₂)) =>
    Subtype.ext (coe_isoφ12_eq_φ1 Φ ⟨g, inf_le_inf hA₁ hA₂ g.2⟩)
  comm2 := fun (g : ↥(A₁ ⊓ A₂)) =>
    Subtype.ext (coe_isoφ12_eq_φ2 Φ ⟨g, inf_le_inf hA₁ hA₂ g.2⟩)

end Iso

theorem mem_of_odd_orderOf [Finite Y] {N : Subgroup Y} (hN : N.index ≤ 2) {x : Y}
    (hx : Odd (orderOf x)) : x ∈ N := by
  have hpos : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top x
  · have hsq : x ^ 2 ∈ N := Subgroup.sq_mem_of_index_two h2 x
    obtain ⟨k, hk⟩ := hx
    have : x = (x ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [this]
    exact pow_mem hsq _

theorem mem_perfectCore_iff_of_equiv [Finite X] [Finite Y] {A : Subgroup X} {C : Subgroup Y}
    (e : ↥A ≃* ↥C) (a : ↥A) : (a : X) ∈ perfectCore A ↔ ((e a : ↥C) : Y) ∈ perfectCore C := by
  set fA : ↥A →* X := A.subtype
  set fC : ↥A →* Y := C.subtype.comp e.toMonoidHom
  have hfA : Function.Injective fA := A.subtype_injective
  have hfC : Function.Injective fC := C.subtype_injective.comp e.injective
  have hA : perfectCore A = (perfectCore (⊤ : Subgroup ↥A)).map fA := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hC : perfectCore C = (perfectCore (⊤ : Subgroup ↥A)).map fC := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [fC]⟩
    · rintro ⟨b, rfl⟩
      exact (e b).2
  rw [hA, hC]
  exact (Subgroup.mem_map_iff_mem hfA).trans (Subgroup.mem_map_iff_mem hfC).symm

end CFSG.Quasithin.F1
