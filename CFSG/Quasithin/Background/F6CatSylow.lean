module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

@[expose] def dihedralToPermFun : DihedralGroup 4 → Equiv.Perm (Fin 4)
  | .r i => finRotate 4 ^ i.val
  | .sr i => Equiv.swap 0 2 * finRotate 4 ^ i.val

theorem dihedralToPermFun_mul : ∀ x y : DihedralGroup 4,
    dihedralToPermFun (x * y) = dihedralToPermFun x * dihedralToPermFun y := by
  unfold dihedralToPermFun
  decide +kernel

theorem dihedralToPermFun_injective : ∀ x y : DihedralGroup 4,
    dihedralToPermFun x = dihedralToPermFun y → x = y := by
  unfold dihedralToPermFun
  decide +kernel

@[expose] def dihedralToPerm : DihedralGroup 4 →* Equiv.Perm (Fin 4) :=
  MonoidHom.mk' dihedralToPermFun dihedralToPermFun_mul

theorem dihedralToPerm_injective : Function.Injective dihedralToPerm :=
  fun x y h => dihedralToPermFun_injective x y h

@[expose] def z2DihedralToPerm :
    Multiplicative (ZMod 2) × DihedralGroup 4 →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) :=
  MonoidHom.prodMap (MonoidHom.id _) dihedralToPerm

theorem z2DihedralToPerm_injective : Function.Injective z2DihedralToPerm := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [z2DihedralToPerm, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp,
    MonoidHom.coe_fst, MonoidHom.coe_snd, Function.comp_apply, MonoidHom.id_apply,
    Prod.mk.injEq] at h
  exact Prod.ext h.1 (dihedralToPerm_injective h.2)

noncomputable def sylowOfCard {G : Type*} [Group G] [Finite G] (P : Subgroup G) (k : ℕ)
    (hP : Nat.card P = 2 ^ k) (hi : ¬ 2 ∣ P.index) : Sylow 2 G :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card hP).toSylow hi

theorem nonempty_inf_mulEquiv_of_left {D Y X : Type*} [Group D] [Finite D] [Group Y] [Finite Y]
    [Group X] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) (e : ↥G₁ ≃* Y)
    (f : X →* Y) (hf : Function.Injective f) (k : ℕ) (hk : Nat.card f.range = 2 ^ k)
    (hi : ¬ 2 ∣ f.range.index) : Nonempty (↥(G₁ ⊓ G₂) ≃* X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hodd⟩ := isSylowTwoOf_inf_left h
  have hp' : IsPGroup 2 ↥((G₁ ⊓ G₂).subgroupOf G₁) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  let P₁ : Sylow 2 ↥G₁ := hp'.toSylow hodd
  let P₂ : Sylow 2 Y := P₁.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q : Sylow 2 Y := sylowOfCard f.range k hk hi
  have e₁ : ↥(G₁ ⊓ G₂) ≃* ↥(P₁ : Subgroup ↥G₁) := (Subgroup.subgroupOfEquivOfLe hle).symm
  have e₂ : ↥(P₁ : Subgroup ↥G₁) ≃* ↥(P₂ : Subgroup Y) :=
    ((P₁ : Subgroup ↥G₁).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)
  have e₃ : ↥(P₂ : Subgroup Y) ≃* ↥(Q : Subgroup Y) := Sylow.equiv P₂ Q
  have e₄ : ↥(Q : Subgroup Y) ≃* X := (MonoidHom.ofInjective hf).symm
  exact ⟨((e₁.trans e₂).trans e₃).trans e₄⟩

theorem nonempty_inf_mulEquiv_dihedral_of_left {D : Type*} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) (e : ↥G₁ ≃* Equiv.Perm (Fin 4)) :
    Nonempty (↥(G₁ ⊓ G₂) ≃* DihedralGroup 4) := by
  have hc : Nat.card dihedralToPerm.range = 2 ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective dihedralToPerm_injective).toEquiv,
      DihedralGroup.nat_card]
    norm_num
  have hi : dihedralToPerm.range.index = 3 := by
    have := Subgroup.card_mul_index dihedralToPerm.range
    rw [hc, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    simp [Nat.factorial] at this
    omega
  exact nonempty_inf_mulEquiv_of_left h e dihedralToPerm dihedralToPerm_injective 3 hc
    (by rw [hi]; decide)

theorem nonempty_inf_mulEquiv_z2_dihedral_of_left {D : Type*} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂)
    (e : ↥G₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) := by
  have hc : Nat.card z2DihedralToPerm.range = 2 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective z2DihedralToPerm_injective).toEquiv,
      Nat.card_prod, DihedralGroup.nat_card]
    simp
  have hi : z2DihedralToPerm.range.index = 3 := by
    have := Subgroup.card_mul_index z2DihedralToPerm.range
    rw [hc, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4),
      Fintype.card_fin] at this
    simp [Nat.factorial] at this
    omega
  exact nonempty_inf_mulEquiv_of_left h e z2DihedralToPerm z2DihedralToPerm_injective 4 hc
    (by rw [hi]; decide)

end F6

end CFSG.Quasithin
