module

public import CFSG.Quasithin.EmptyFaithful.S153G93DFac

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

section QPair

variable {Q : Type} [Group Q]

theorem TwoStruct.conj_pair {K N N' : Subgroup Q} {g : Q} (hK : TwoStruct K N N' g)
    (hKn : K.Normal) (x : Q) :
    (N.map (MulAut.conj x).toMonoidHom = N ∧ N'.map (MulAut.conj x).toMonoidHom = N') ∨
      (N.map (MulAut.conj x).toMonoidHom = N' ∧ N'.map (MulAut.conj x).toMonoidHom = N) := by
  have hinj : N.map (MulAut.conj x).toMonoidHom ≠ N'.map (MulAut.conj x).toMonoidHom := fun h =>
    hK.ne (Subgroup.map_injective (MulAut.conj x).injective h)
  rcases hK.conj_cases hKn x with h1 | h1
  · rcases hK.conj_cases' hKn x with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · exact Or.inl ⟨h1, h2⟩
  · rcases hK.conj_cases' hKn x with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hinj

end QPair

section Transfer

variable {G : Type} [Group G] {Γ : Subgroup G}

theorem map_subtype_conj (A : Subgroup ↥Γ) (x : ↥Γ) :
    (A.map Γ.subtype).map (MulAut.conj (x : G)).toMonoidHom =
      (A.map (MulAut.conj x).toMonoidHom).map Γ.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

end Transfer

structure TwoDataG {W : Type} [CommGroup W] (H K T' L₁ L₂ : Subgroup (MulAut W)) (t : MulAut W) :
    Prop where
  sup : K = L₁ ⊔ L₂
  comm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x
  inf : L₁ ⊓ L₂ = ⊥
  quasi₁ : CFSG.IsQuasisimple ↥L₁
  a38 : A38Types ↥L₁
  simple₁ : IsSimpleGroup ↥L₁
  simple₂ : IsSimpleGroup ↥L₂
  nab₁ : ∃ x y : ↥L₁, x * y ≠ y * x
  nab₂ : ∃ x y : ↥L₂, x * y ≠ y * x
  tT : t ∈ T'
  swap₁ : L₁.map (MulAut.conj t).toMonoidHom = L₂
  swap₂ : L₂.map (MulAut.conj t).toMonoidHom = L₁
  perm : ∀ x ∈ H, (L₁.map (MulAut.conj x).toMonoidHom = L₁ ∧
      L₂.map (MulAut.conj x).toMonoidHom = L₂) ∨
    (L₁.map (MulAut.conj x).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj x).toMonoidHom = L₁)

section TwoDataG

variable {W : Type} [CommGroup W]

theorem exists_twoDataG (hS : A38TypesSimple) {H K T' : Subgroup (MulAut W)} (hKH : K ≤ H)
    (hT' : IsSylowTwoOf T' H) {N N' : Subgroup ↥H} {g : ↥H}
    (hst : TwoStruct (K.subgroupOf H) N N' g) (hKn : (K.subgroupOf H).Normal) :
    ∃ (L₁ L₂ : Subgroup (MulAut W)) (t : MulAut W), TwoDataG H K T' L₁ L₂ t := by
  set L₁ : Subgroup (MulAut W) := N.map H.subtype with hL₁
  set L₂ : Subgroup (MulAut W) := N'.map H.subtype with hL₂
  have hsup : K = L₁ ⊔ L₂ := by
    have h1 : K = (K.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hKH).symm
    rw [h1, hst.sup, Subgroup.map_sup]
  have hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hst.comm x hx y hy)
  have e₁ : ↥N ≃* ↥L₁ := N.equivMapOfInjective H.subtype H.subtype_injective
  have hquasi : CFSG.IsQuasisimple ↥L₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁ hst.comp₁.1
  have ha38 : A38Types ↥L₁ := a38Types_congr e₁ hst.a38
  have hsimple₁ : IsSimpleGroup ↥L₁ := hS _ ha38
  have hnab₁ := nonab_of_quasisimple hquasi
  have hcenter : Subgroup.center ↥L₁ = ⊥ := center_eq_bot_of_simple hnab₁
  have hinf : L₁ ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rw [Subgroup.mem_bot]
    have hzc : (⟨z, hz1⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2 z hz2)
    rw [hcenter, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  have hT'' : IsSylowTwoOf (T'.subgroupOf H) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT'.1).symm
    · have h2 : ((T'.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).index = (T'.subgroupOf H).index :=
        Subgroup.relIndex_top_right (T'.subgroupOf H)
      rw [h2]
      exact hT'.2.2
  obtain ⟨t', ht'T, ht'⟩ := exists_swap_of_sylow hst hKn hT''
  have htT : (t' : MulAut W) ∈ T' := Subgroup.mem_subgroupOf.mp ht'T
  have hswap₁ : L₁.map (MulAut.conj (t' : MulAut W)).toMonoidHom = L₂ := by
    rw [hL₁, map_subtype_conj, ht']
  have hswap₂ : L₂.map (MulAut.conj (t' : MulAut W)).toMonoidHom = L₁ := by
    rw [hL₂, hL₁, map_subtype_conj]
    rcases hst.conj_pair hKn t' with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans ht') hst.ne
    · rw [h2]
  have hsimple₂ : IsSimpleGroup ↥L₂ := by
    have e₂ : ↥L₁ ≃* ↥L₂ := by
      refine (L₁.equivMapOfInjective (MulAut.conj (t' : MulAut W)).toMonoidHom
        (MulAut.conj (t' : MulAut W)).injective).trans (MulEquiv.subgroupCongr hswap₁)
    exact e₂.symm.isSimpleGroup
  have hnab₂ : ∃ x y : ↥L₂, x * y ≠ y * x := by
    have e₂ : ↥L₁ ≃* ↥L₂ := by
      refine (L₁.equivMapOfInjective (MulAut.conj (t' : MulAut W)).toMonoidHom
        (MulAut.conj (t' : MulAut W)).injective).trans (MulEquiv.subgroupCongr hswap₁)
    obtain ⟨x, y, hxy⟩ := hnab₁
    exact ⟨e₂ x, e₂ y, fun h => hxy (e₂.injective (by rw [map_mul, map_mul]; exact h))⟩
  refine ⟨L₁, L₂, (t' : MulAut W), ⟨hsup, hcomm, hinf, hquasi, ha38, hsimple₁, hsimple₂, hnab₁,
    hnab₂, htT, hswap₁, hswap₂, ?_⟩⟩
  intro x hx
  have e1 : L₁.map (MulAut.conj x).toMonoidHom =
      (N.map (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom).map H.subtype :=
    map_subtype_conj N ⟨x, hx⟩
  have e2 : L₂.map (MulAut.conj x).toMonoidHom =
      (N'.map (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom).map H.subtype :=
    map_subtype_conj N' ⟨x, hx⟩
  rcases hst.conj_pair hKn ⟨x, hx⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [e1, e2, h1, h2]
    exact ⟨rfl, rfl⟩
  · right
    rw [e1, e2, h1, h2]
    exact ⟨rfl, rfl⟩

end TwoDataG

end S153G93D

end CFSG.Quasithin
