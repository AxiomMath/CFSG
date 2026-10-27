module

public import CFSG.Quasithin.Background.SmithD310UCount
public import CFSG.Quasithin.Background.SmithD39TwoClif

public section

namespace CFSG.Quasithin.SmithD321


section Modules

variable {R : Type*} [Ring R] {M S : Type*} [AddCommGroup M] [Module R M] [AddCommGroup S]
  [Module R S]

theorem card_ne_zero_add_one {H : Type*} [Zero H] [Finite H] :
    Nat.card {h : H // h ≠ 0} + 1 = Nat.card H := by
  classical
  have h1 := Nat.card_congr (Equiv.optionSubtypeNe (0 : H))
  rwa [Finite.card_option] at h1

theorem nonempty_linearEquiv_of_isSimpleModule {Q : Type*} [AddCommGroup Q] [Module R Q]
    [IsSimpleModule R Q] (hQ : IsIsotypicOfType R Q S) : Nonempty (Q ≃ₗ[R] S) := by
  have : IsSimpleModule R ↥(⊤ : Submodule R Q) := IsSimpleModule.congr Submodule.topEquiv
  exact ⟨Submodule.topEquiv.symm.trans (hQ ⊤).some⟩

theorem card_simple_mul_card_units [Finite M] [Finite S] [IsSimpleModule R S]
    (hM : IsIsotypicOfType R M S) :
    Nat.card {N : Submodule R M // IsSimpleModule R ↥N} * Nat.card (Module.End R S)ˣ + 1 =
      Nat.card (S →ₗ[R] M) := by
  classical
  have hHfin : Finite (S →ₗ[R] M) :=
    Finite.of_injective (fun f : S →ₗ[R] M => (f : S → M)) DFunLike.coe_injective
  have hSnt : Nontrivial S := IsSimpleModule.nontrivial R S
  let Ω := {N : Submodule R M // IsSimpleModule R ↥N}
  have hex : ∀ N : Ω, ∃ _e : S ≃ₗ[R] ↥N.1, True := fun N =>
    ⟨(@hM N.1 N.2).some.symm, trivial⟩
  choose e _ using hex
  have hu_bij : ∀ u : (Module.End R S)ˣ, Function.Bijective (u : Module.End R S) :=
    fun u => (Module.End.isUnit_iff _).1 u.isUnit
  let F : Ω × (Module.End R S)ˣ → (S →ₗ[R] M) := fun p =>
    (p.1.1.subtype ∘ₗ (e p.1).toLinearMap) ∘ₗ (p.2 : Module.End R S)
  have hFapply : ∀ p x, F p x = ((e p.1 ((p.2 : Module.End R S) x) : ↥p.1.1) : M) :=
    fun p x => rfl
  have hFne : ∀ p, F p ≠ 0 := by
    intro p hp
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    have h0 : F p x = 0 := by rw [hp]; rfl
    rw [hFapply] at h0
    have h1 : e p.1 ((p.2 : Module.End R S) x) = 0 := Subtype.ext h0
    have h2 : (p.2 : Module.End R S) x = 0 := (e p.1).injective (by rw [h1, map_zero])
    exact hx ((hu_bij p.2).1 (by rw [h2, map_zero]))
  let Φ : Ω × (Module.End R S)ˣ → {h : S →ₗ[R] M // h ≠ 0} := fun p => ⟨F p, hFne p⟩
  have hrange : ∀ p, LinearMap.range (F p) = p.1.1 := by
    intro p
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e p.1 ((p.2 : Module.End R S) x)).2
    · intro hy
      obtain ⟨x, hx⟩ := (hu_bij p.2).2 ((e p.1).symm ⟨y, hy⟩)
      refine ⟨x, ?_⟩
      rw [hFapply, hx, LinearEquiv.apply_symm_apply]
  have hinjΦ : Function.Injective Φ := by
    rintro ⟨N, u⟩ ⟨N', u'⟩ h
    have hf : F (N, u) = F (N', u') := congrArg Subtype.val h
    have hN : N = N' := Subtype.ext (by rw [← hrange (N, u), ← hrange (N', u'), hf])
    subst hN
    have huu : u = u' := by
      apply Units.ext
      apply LinearMap.ext
      intro x
      have h1 := congrArg (fun f : S →ₗ[R] M => f x) hf
      exact (e N).injective (Subtype.ext h1)
    rw [huu]
  have hsurjΦ : Function.Surjective Φ := by
    rintro ⟨f, hne⟩
    have hfinj : Function.Injective f := LinearMap.injective_of_ne_zero hne
    let ef := LinearEquiv.ofInjective f hfinj
    have : IsSimpleModule R ↥(LinearMap.range f) := IsSimpleModule.congr ef.symm
    let N : Ω := ⟨LinearMap.range f, this⟩
    let g : S ≃ₗ[R] S := ef.trans (e N).symm
    have hgunit : IsUnit (g : Module.End R S) := (Module.End.isUnit_iff _).2 g.bijective
    refine ⟨(N, hgunit.unit), Subtype.ext (LinearMap.ext fun x => ?_)⟩
    change ((e N ((e N).symm (ef x)) : ↥N.1) : M) = f x
    rw [LinearEquiv.apply_symm_apply]
    exact LinearEquiv.ofInjective_apply f x
  have hcard : Nat.card Ω * Nat.card (Module.End R S)ˣ =
      Nat.card {h : S →ₗ[R] M // h ≠ 0} := by
    rw [← Nat.card_prod]
    exact Nat.card_eq_of_bijective Φ ⟨hinjΦ, hsurjΦ⟩
  rw [hcard]
  exact card_ne_zero_add_one

theorem card_coatom_mul_card_units [Finite M] [Finite S] [IsSimpleModule R S]
    [IsSemisimpleModule R M] (hM : IsIsotypicOfType R M S) :
    Nat.card {N : Submodule R M // IsCoatom N} * Nat.card (Module.End R S)ˣ + 1 =
      Nat.card (M →ₗ[R] S) := by
  classical
  have hHfin : Finite (M →ₗ[R] S) :=
    Finite.of_injective (fun f : M →ₗ[R] S => (f : M → S)) DFunLike.coe_injective
  let Ω := {N : Submodule R M // IsCoatom N}
  have hex : ∀ N : Ω, ∃ _e : (M ⧸ N.1) ≃ₗ[R] S, True := fun N =>
    have : IsSimpleModule R (M ⧸ N.1) := isSimpleModule_iff_isCoatom.2 N.2
    ⟨(nonempty_linearEquiv_of_isSimpleModule
      (SmithD39Two.isIsotypicOfType_quotient hM N.1)).some, trivial⟩
  choose e _ using hex
  have hu_bij : ∀ u : (Module.End R S)ˣ, Function.Bijective (u : Module.End R S) :=
    fun u => (Module.End.isUnit_iff _).1 u.isUnit
  let F : Ω × (Module.End R S)ˣ → (M →ₗ[R] S) := fun p =>
    ((p.2 : Module.End R S) ∘ₗ (e p.1).toLinearMap) ∘ₗ p.1.1.mkQ
  have hFapply : ∀ p x, F p x = (p.2 : Module.End R S) (e p.1 (p.1.1.mkQ x)) :=
    fun p x => rfl
  have hker : ∀ p, LinearMap.ker (F p) = p.1.1 := by
    intro p
    ext x
    rw [LinearMap.mem_ker, hFapply]
    constructor
    · intro hx
      have h1 : e p.1 (p.1.1.mkQ x) = 0 := (hu_bij p.2).1 (by rw [hx, map_zero])
      have h2 : p.1.1.mkQ x = 0 := (e p.1).injective (by rw [h1, map_zero])
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    · intro hx
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero, map_zero]
  have hFne : ∀ p, F p ≠ 0 := by
    intro p hp
    have h1 := hker p
    rw [hp, LinearMap.ker_zero] at h1
    exact p.1.2.1 h1.symm
  let Φ : Ω × (Module.End R S)ˣ → {h : M →ₗ[R] S // h ≠ 0} := fun p => ⟨F p, hFne p⟩
  have hinjΦ : Function.Injective Φ := by
    rintro ⟨N, u⟩ ⟨N', u'⟩ h
    have hf : F (N, u) = F (N', u') := congrArg Subtype.val h
    have hN : N = N' := Subtype.ext (by rw [← hker (N, u), ← hker (N', u'), hf])
    subst hN
    have huu : u = u' := by
      apply Units.ext
      apply LinearMap.ext
      intro s
      obtain ⟨y, rfl⟩ := (e N).surjective s
      obtain ⟨x, rfl⟩ := N.1.mkQ_surjective y
      exact congrArg (fun f : M →ₗ[R] S => f x) hf
    rw [huu]
  have hsurjΦ : Function.Surjective Φ := by
    rintro ⟨f, hne⟩
    have hfs : Function.Surjective f := LinearMap.surjective_of_ne_zero hne
    let N : Ω := ⟨LinearMap.ker f, LinearMap.isCoatom_ker_of_surjective hfs⟩
    let g : S ≃ₗ[R] S := (e N).symm.trans (f.quotKerEquivOfSurjective hfs)
    have hgunit : IsUnit (g : Module.End R S) := (Module.End.isUnit_iff _).2 g.bijective
    refine ⟨(N, hgunit.unit), Subtype.ext (LinearMap.ext fun x => ?_)⟩
    change f.quotKerEquivOfSurjective hfs ((e N).symm (e N (N.1.mkQ x))) = f x
    rw [LinearEquiv.symm_apply_apply]
    exact f.quotKerEquivOfSurjective_apply_mk hfs x
  have hcard : Nat.card Ω * Nat.card (Module.End R S)ˣ =
      Nat.card {h : M →ₗ[R] S // h ≠ 0} := by
    rw [← Nat.card_prod]
    exact Nat.card_eq_of_bijective Φ ⟨hinjΦ, hsurjΦ⟩
  rw [hcard]
  exact card_ne_zero_add_one

end Modules

section XModCount

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem toSubmod_ofSubmod {Λ : Subgroup Γ} (N : Submodule ↥(XMod.opRing ↥Λ Q) (Additive Q)) :
    XMod.toSubmod (XMod.isInv_ofSubmod N) = N :=
  Submodule.ext fun _ => Iff.rfl

theorem ofSubmod_toSubmod {Λ : Subgroup Γ} {J : Subgroup Q} (hJ : XMod.IsInv ↥Λ J) :
    XMod.ofSubmod (XMod.toSubmod hJ) = J :=
  Subgroup.ext fun _ => Iff.rfl

theorem ofSubmod_map_le {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    (N : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY)) :
    XMod.ofSubmod (N.map (XMod.toSubmod hY).subtype) ≤ Y :=
  fun _ hq => Submodule.map_subtype_le _ N hq

theorem ofSubmod_map_le_iff {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    {N N' : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY)} :
    XMod.ofSubmod (N.map (XMod.toSubmod hY).subtype) ≤
        XMod.ofSubmod (N'.map (XMod.toSubmod hY).subtype) ↔ N ≤ N' :=
  Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) N N'

theorem ofSubmod_map_top {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y) :
    XMod.ofSubmod ((⊤ : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY)).map
      (XMod.toSubmod hY).subtype) = Y := by
  rw [Submodule.map_subtype_top, ofSubmod_toSubmod]

theorem ofSubmod_map_comap {Λ : Subgroup Γ} {Y J : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    (hJ : XMod.IsInv ↥Λ J) (hJY : J ≤ Y) :
    XMod.ofSubmod (((XMod.toSubmod hJ).comap (XMod.toSubmod hY).subtype).map
      (XMod.toSubmod hY).subtype) = J := by
  rw [Submodule.map_comap_subtype,
    inf_eq_right.2 (XMod.toSubmod_le_iff (hL := hJ) (hL' := hY) |>.2 hJY), ofSubmod_toSubmod]

theorem comap_map_ofSubmod {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    (N : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY)) :
    (XMod.toSubmod (XMod.isInv_ofSubmod (N.map (XMod.toSubmod hY).subtype))).comap
      (XMod.toSubmod hY).subtype = N := by
  rw [toSubmod_ofSubmod, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]

theorem isIrr_ofSubmod_map_iff {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    (N : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY)) :
    XMod.IsIrr ↥Λ (XMod.ofSubmod (N.map (XMod.toSubmod hY).subtype)) ↔
      IsSimpleModule ↥(XMod.opRing ↥Λ Q) ↥N := by
  rw [XMod.isIrr_iff (XMod.isInv_ofSubmod _), toSubmod_ofSubmod]
  have e := Submodule.equivMapOfInjective (XMod.toSubmod hY).subtype
    (Submodule.injective_subtype _) N
  exact ⟨fun _ => IsSimpleModule.congr e, fun _ => IsSimpleModule.congr (N := ↥N) e.symm⟩

theorem isIrrSec_ofSubmod_map_iff {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    (N : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY)) :
    XMod.IsIrrSec ↥Λ (XMod.ofSubmod (N.map (XMod.toSubmod hY).subtype)) Y ↔ IsCoatom N := by
  have htop := ofSubmod_map_top hY
  constructor
  · rintro ⟨hlt, hmax⟩
    refine ⟨fun h => ?_, fun N' hN' => ?_⟩
    · rw [h, htop] at hlt
      exact lt_irrefl _ hlt
    · rcases hmax _ (XMod.isInv_ofSubmod _) ((ofSubmod_map_le_iff hY).2 hN'.le)
        (ofSubmod_map_le hY N') with h | h
      · exact absurd (le_antisymm ((ofSubmod_map_le_iff hY).1 h.le) hN'.le) hN'.ne'
      · exact eq_top_iff.2 ((ofSubmod_map_le_iff hY).1 (h.trans htop.symm).ge)
  · rintro ⟨hne, hmax⟩
    refine ⟨lt_of_le_of_ne (ofSubmod_map_le hY N) fun h => hne ?_, fun J hJ hNJ hJY => ?_⟩
    · exact eq_top_iff.2 ((ofSubmod_map_le_iff hY).1 (h.trans htop.symm).ge)
    · obtain ⟨N', hN'⟩ : ∃ N' : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY),
          XMod.ofSubmod (N'.map (XMod.toSubmod hY).subtype) = J :=
        ⟨_, ofSubmod_map_comap hY hJ hJY⟩
      subst hN'
      rcases ((ofSubmod_map_le_iff hY).1 hNJ).lt_or_eq with h | h
      · right
        rw [hmax N' h, htop]
      · left
        rw [h]

theorem card_isSimpleModule_eq {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y) :
    Nat.card {N : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY) //
        IsSimpleModule ↥(XMod.opRing ↥Λ Q) ↥N} =
      Nat.card {J : Subgroup Q // J ≤ Y ∧ XMod.IsIrr ↥Λ J} :=
  Nat.card_congr
    { toFun := fun N => ⟨XMod.ofSubmod (N.1.map (XMod.toSubmod hY).subtype),
        ofSubmod_map_le hY N.1, (isIrr_ofSubmod_map_iff hY N.1).2 N.2⟩
      invFun := fun J => ⟨(XMod.toSubmod J.2.2.1).comap (XMod.toSubmod hY).subtype, by
        rw [← isIrr_ofSubmod_map_iff hY, ofSubmod_map_comap hY J.2.2.1 J.2.1]
        exact J.2.2⟩
      left_inv := fun N => Subtype.ext (comap_map_ofSubmod hY N.1)
      right_inv := fun J => Subtype.ext (ofSubmod_map_comap hY J.2.2.1 J.2.1) }

theorem card_isCoatom_eq {Λ : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y) :
    Nat.card {N : Submodule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hY) // IsCoatom N} =
      Nat.card {J : Subgroup Q // J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y} :=
  Nat.card_congr
    { toFun := fun N => ⟨XMod.ofSubmod (N.1.map (XMod.toSubmod hY).subtype),
        ofSubmod_map_le hY N.1, XMod.isInv_ofSubmod _, (isIrrSec_ofSubmod_map_iff hY N.1).2 N.2⟩
      invFun := fun J => ⟨(XMod.toSubmod J.2.2.1).comap (XMod.toSubmod hY).subtype, by
        rw [← isIrrSec_ofSubmod_map_iff hY, ofSubmod_map_comap hY J.2.2.1 J.2.1]
        exact J.2.2.2⟩
      left_inv := fun N => Subtype.ext (comap_map_ofSubmod hY N.1)
      right_inv := fun J => Subtype.ext (ofSubmod_map_comap hY J.2.2.1 J.2.1) }

theorem card_toSubmod_eq_pow [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c) :
    Nat.card ↥(XMod.toSubmod hY.1) = Nat.card ↥(XMod.toSubmod hI.1) ^ c := by
  rw [card_toSubmod, card_toSubmod, card_eq_two_pow hQ, card_eq_two_pow hQ, hY.2.2, ← pow_mul,
    mul_comm]

theorem card_irr_mul_card_units [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c) :
    Nat.card {J : Subgroup Q // J ≤ Y ∧ XMod.IsIrr ↥Λ J} *
        Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1))ˣ + 1 =
      Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) ^ c := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have hIle : I ≤ isoComp ↥Λ I := le_isoComp hI (XMod.Iso.refl I)
  have := isSemisimpleModule_toSubmod hI hI.1 hIle
  have := isSemisimpleModule_toSubmod hI hY.1 hY.2.1
  have hMiso := isIsotypicOfType_toSubmod hI hY.1 hY.2.1
  have h1 := card_simple_mul_card_units hMiso
  rw [card_linearMap_eq (isIsotypicOfType_toSubmod hI hI.1 hIle) hMiso (pow_one _).symm
    (card_toSubmod_eq_pow hQ hI hY), one_mul, card_isSimpleModule_eq hY.1] at h1
  exact h1

theorem card_max_mul_card_units [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c) :
    Nat.card {J : Subgroup Q // J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y} *
        Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1))ˣ + 1 =
      Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) ^ c := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have hIle : I ≤ isoComp ↥Λ I := le_isoComp hI (XMod.Iso.refl I)
  have := isSemisimpleModule_toSubmod hI hI.1 hIle
  have := isSemisimpleModule_toSubmod hI hY.1 hY.2.1
  have hMiso := isIsotypicOfType_toSubmod hI hY.1 hY.2.1
  have h1 := card_coatom_mul_card_units hMiso
  rw [card_linearMap_eq hMiso (isIsotypicOfType_toSubmod hI hI.1 hIle)
    (card_toSubmod_eq_pow hQ hI hY) (pow_one _).symm, mul_one, card_isCoatom_eq hY.1] at h1
  exact h1

theorem even_card_end [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ} {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) :
    Even (Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1))) := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have := IsSimpleModule.nontrivial ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)
  have : Finite (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) :=
    Finite.of_injective (fun f : Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1) =>
      (f : ↥(XMod.toSubmod hI.1) → ↥(XMod.toSubmod hI.1))) DFunLike.coe_injective
  have hM : ∀ m : Additive Q, m + m = 0 := fun m => by
    have h := hQ (Additive.toMul m)
    rw [sq] at h
    exact h
  have hE2 : ∀ f : Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1), f + f = 0 :=
    fun f => LinearMap.ext fun x => Subtype.ext (hM _)
  obtain ⟨k, hk⟩ := Twist.odd_card_sub_one
    (G := Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) hE2 inferInstance
  have hpos : 0 < Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) :=
    Nat.card_pos
  exact ⟨k + 1, by omega⟩

theorem odd_card_max [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c)
    (hc : 1 ≤ c) :
    Odd (Nat.card {J : Subgroup Q // J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y}) := by
  have hE := Nat.even_pow.2 ⟨even_card_end hQ hI, (by omega : c ≠ 0)⟩
  rw [← card_max_mul_card_units hQ hI hY, Nat.even_add_one, Nat.not_even_iff_odd] at hE
  exact (Nat.odd_mul.1 hE).1

theorem isIrrSec_smul {B T : Type*} [Group B] [Group T] [MulDistribMulAction B Q]
    [MulDistribMulAction T Q] (h : XMod.Normalizes B T Q) (t : T) {C L : Subgroup Q}
    (hCL : XMod.IsIrrSec B C L) : XMod.IsIrrSec B (t • C) (t • L) := by
  refine ⟨lt_of_le_of_ne (Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hCL.1.le)
    fun he => hCL.1.ne (MulAction.injective t he), fun J hJ hCJ hJL => ?_⟩
  have h1 : C ≤ t⁻¹ • J := by
    rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t), smul_inv_smul]
    exact hCJ
  have h2 : t⁻¹ • J ≤ L := by
    rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t), smul_inv_smul]
    exact hJL
  rcases hCL.2 _ (XMod.isInv_smul_of_normalizes h t⁻¹ hJ) h1 h2 with h3 | h3
  · left
    rw [← h3, smul_inv_smul]
  · right
    rw [← h3, smul_inv_smul]

theorem exists_max_fixed [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c)
    (hc : 1 ≤ c) {A : Subgroup Γ} (hA2 : IsPGroup 2 ↥A)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) (hAY : ∀ a ∈ A, ∀ q ∈ Y, a • q ∈ Y) :
    ∃ J : Subgroup Q, J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y ∧
      ∀ a ∈ A, ∀ q ∈ J, a • q ∈ J := by
  classical
  have hN : XMod.Normalizes ↥Λ ↥A Q := normalizes_of_conj Λ A hAΛ
  have hle : ∀ b : ↥A, b • Y ≤ Y := by
    rintro b _ ⟨y, hy, rfl⟩
    exact hAY b b.2 y hy
  have hYeq : ∀ b : ↥A, b • Y = Y := by
    intro b
    have h1 := Subgroup.pointwise_smul_subset_iff.1 (hle b⁻¹)
    rw [inv_inv] at h1
    exact le_antisymm (hle b) h1
  let Ω := {J : Subgroup Q // J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y}
  have hsm : ∀ (b : ↥A) (J : Ω),
      b • J.1 ≤ Y ∧ XMod.IsInv ↥Λ (b • J.1) ∧ XMod.IsIrrSec ↥Λ (b • J.1) Y := by
    intro b J
    refine ⟨(Subgroup.pointwise_smul_le_pointwise_smul_iff.2 J.2.1).trans_eq (hYeq b),
      XMod.isInv_smul_of_normalizes hN b J.2.2.1, ?_⟩
    have h1 : XMod.IsIrrSec ↥Λ (b • J.1) (b • Y) := isIrrSec_smul hN b J.2.2.2
    rwa [hYeq b] at h1
  let act : MulAction ↥A Ω :=
    { smul := fun b J => ⟨b • J.1, hsm b J⟩
      one_smul := fun J => Subtype.ext (one_smul ↥A J.1)
      mul_smul := fun b b' J => Subtype.ext (mul_smul b b' J.1) }
  have hΩodd : Odd (Nat.card Ω) := odd_card_max hQ hI hY hc
  have hmod := @IsPGroup.card_modEq_card_fixedPoints 2 ↥A _ hA2 _ Ω act _
  have hfixodd : Nat.card ↑(@MulAction.fixedPoints ↥A Ω _ act) % 2 = 1 := by
    have h1 : Nat.card Ω % 2 = 1 := Nat.odd_iff.1 hΩodd
    have h2 : Nat.card Ω % 2 = Nat.card ↑(@MulAction.fixedPoints ↥A Ω _ act) % 2 := hmod
    omega
  have hnonempty : Nonempty ↑(@MulAction.fixedPoints ↥A Ω _ act) := by
    rw [← Finite.card_pos_iff]
    omega
  obtain ⟨⟨J, hJ⟩⟩ := hnonempty
  have hJfix : ∀ b : ↥A, b • J.1 = J.1 := fun b =>
    congrArg Subtype.val ((@MulAction.mem_fixedPoints ↥A Ω _ act J).1 hJ b)
  refine ⟨J.1, J.2.1, J.2.2.1, J.2.2.2, fun a ha q hq => ?_⟩
  have h1 : (⟨a, ha⟩ : ↥A) • q ∈ (⟨a, ha⟩ : ↥A) • J.1 := Subgroup.smul_mem_pointwise_smul _ _ _ hq
  rw [hJfix] at h1
  exact h1

theorem card_irr_eq [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c)
    (hE : Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) = 2) :
    Nat.card {J : Subgroup Q // J ≤ Y ∧ XMod.IsIrr ↥Λ J} = 2 ^ c - 1 := by
  classical
  have := (XMod.isIrr_iff hI.1).1 hI
  let : DivisionRing (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) :=
    Module.End.instDivisionRing
  have hU : Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1))ˣ = 1 := by
    rw [Nat.card_units, hE]
  have h := card_irr_mul_card_units hQ hI hY
  rw [hU, mul_one, hE] at h
  exact Nat.eq_sub_of_add_eq h

theorem isotypicOfLength_of_max [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c)
    {J : Subgroup Q} (hJY : J ≤ Y) (hJ : XMod.IsInv ↥Λ J) (hJmax : XMod.IsIrrSec ↥Λ J Y) :
    IsotypicOfLength ↥Λ J I (c - 1) := by
  refine ⟨hJ, hJY.trans hY.2.1, ?_⟩
  have := (XMod.isIrr_iff hI.1).1 hI
  have := isSemisimpleModule_toSubmod hI hY.1 hY.2.1
  have hMiso := isIsotypicOfType_toSubmod hI hY.1 hY.2.1
  have hNmax : IsCoatom ((XMod.toSubmod hJ).comap (XMod.toSubmod hY.1).subtype) := by
    rw [← isIrrSec_ofSubmod_map_iff hY.1, ofSubmod_map_comap hY.1 hJ hJY]
    exact hJmax
  have := isSimpleModule_iff_isCoatom.2 hNmax
  obtain ⟨e⟩ := nonempty_linearEquiv_of_isSimpleModule (isIsotypicOfType_quotient hMiso
    ((XMod.toSubmod hJ).comap (XMod.toSubmod hY.1).subtype))
  have hcardN : Nat.card ↥((XMod.toSubmod hJ).comap (XMod.toSubmod hY.1).subtype) =
      Nat.card ↥J := by
    rw [← card_toSubmod hJ]
    exact Nat.card_congr
      { toFun := fun p => ⟨p.1.1, p.2⟩
        invFun := fun t => ⟨⟨t.1, hJY t.2⟩, t.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((XMod.toSubmod hJ).comap (XMod.toSubmod hY.1).subtype)
  rw [Nat.card_congr e.toEquiv, hcardN, card_toSubmod, card_toSubmod, card_eq_two_pow hQ Y,
    card_eq_two_pow hQ I, card_eq_two_pow hQ J, ← pow_add, hY.2.2] at h1
  have h2 := Nat.pow_right_injective le_rfl h1
  rw [Nat.sub_one_mul]
  omega

end XModCount

section HomCount

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] noncomputable def smulLin {Λ : Subgroup Γ} {y : Γ} (hyΛ : ∀ l ∈ Λ, l * y = y * l)
    {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y) (hyY : ∀ q ∈ Y, y • q ∈ Y) :
    ↥(XMod.toSubmod hY) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥(XMod.toSubmod hY) where
  toFun m := ⟨Additive.ofMul (y • Additive.toMul m.1), hyY _ m.2⟩
  map_add' a b := by
    apply Subtype.ext
    show Additive.ofMul (y • Additive.toMul (a.1 + b.1)) =
      Additive.ofMul (y • Additive.toMul a.1) + Additive.ofMul (y • Additive.toMul b.1)
    rw [toMul_add, smul_mul', ofMul_mul]
  map_smul' r m := by
    apply Subtype.ext
    show Additive.ofMul (y • Additive.toMul (r.1 m.1)) =
      r.1 (Additive.ofMul (y • Additive.toMul m.1))
    rw [opRing_apply_ofMul_smul hyΛ r.2 (Additive.toMul m.1), ofMul_toMul]

theorem smulLin_apply {Λ : Subgroup Γ} {y : Γ} (hyΛ : ∀ l ∈ Λ, l * y = y * l)
    {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y) (hyY : ∀ q ∈ Y, y • q ∈ Y)
    (m : ↥(XMod.toSubmod hY)) :
    ((smulLin hyΛ hY hyY m : ↥(XMod.toSubmod hY)) : Additive Q) =
      Additive.ofMul (y • Additive.toMul m.1) := rfl

theorem card_end_pow_modEq [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c)
    {y : Γ} (hyΛ : ∀ l ∈ Λ, l * y = y * l) (hyY : ∀ q ∈ Y, y • q ∈ Y)
    {p : ℕ} [Fact p.Prime] (hyp : ∀ q ∈ Y, y ^ p • q = q) {c' : ℕ}
    (hc' : IsotypicOfLength ↥Λ (Y ⊓ XMod.fixed ↥(Subgroup.zpowers y) ⊤) I c') :
    Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) ^ c ≡
      Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) ^ c' [MOD p] := by
  classical
  have := (XMod.isIrr_iff hI.1).1 hI
  have hIle : I ≤ isoComp ↥Λ I := le_isoComp hI (XMod.Iso.refl I)
  have := isSemisimpleModule_toSubmod hI hI.1 hIle
  have := isSemisimpleModule_toSubmod hI hY.1 hY.2.1
  have := isSemisimpleModule_toSubmod hI hc'.1 hc'.2.1
  have hIiso := isIsotypicOfType_toSubmod hI hI.1 hIle
  have hYiso := isIsotypicOfType_toSubmod hI hY.1 hY.2.1
  have hCiso := isIsotypicOfType_toSubmod hI hc'.1 hc'.2.1
  have h1 := card_linearMap_eq hIiso hYiso (pow_one _).symm (card_toSubmod_eq_pow hQ hI hY)
  have h2 := card_linearMap_eq hIiso hCiso (pow_one _).symm (card_toSubmod_eq_pow hQ hI hc')
  rw [one_mul] at h1 h2
  rw [← h1, ← h2]
  set MY := XMod.toSubmod hY.1 with hMY
  set MC := XMod.toSubmod hc'.1 with hMC
  have hCY : MC ≤ MY := XMod.toSubmod_le_iff.2 inf_le_left
  set Ly := smulLin hyΛ hY.1 hyY with hLy
  have hfinH : Finite (↥(XMod.toSubmod hI.1) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥MY) :=
    Finite.of_injective (fun f => (f : ↥(XMod.toSubmod hI.1) → ↥MY)) DFunLike.coe_injective
  have := Fintype.ofFinite (↥(XMod.toSubmod hI.1) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥MY)
  let f : Function.End (↥(XMod.toSubmod hI.1) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥MY) := fun φ => Ly ∘ₗ φ
  have hfk : ∀ k : ℕ, ∀ φ s, (((f ^ k) φ s : ↥MY) : Additive Q) =
      Additive.ofMul (y ^ k • Additive.toMul ((φ s : ↥MY) : Additive Q)) := by
    intro k
    induction k with
    | zero => intro φ s; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ k ih =>
      intro φ s
      rw [pow_succ', pow_succ', mul_smul]
      show ((Ly ((f ^ k) φ s) : ↥MY) : Additive Q) = _
      rw [smulLin_apply, ih, toMul_ofMul]
  have hf : f ^ p ^ 1 = 1 := by
    funext φ
    refine LinearMap.ext fun s => Subtype.ext ?_
    rw [pow_one, hfk]
    have h1 : y ^ p • Additive.toMul ((φ s : ↥MY) : Additive Q) =
        Additive.toMul ((φ s : ↥MY) : Additive Q) := hyp _ (φ s).2
    rw [h1, ofMul_toMul]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have heq : Nat.card ↑(Function.fixedPoints f) =
      Nat.card (↥(XMod.toSubmod hI.1) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥MC) := by
    refine Nat.card_congr
      { toFun := fun φ => LinearMap.codRestrict MC (MY.subtype ∘ₗ φ.1) fun s => ?_
        invFun := fun ψ => ⟨(Submodule.inclusion hCY) ∘ₗ ψ, ?_⟩
        left_inv := fun φ => ?_
        right_inv := fun ψ => ?_ }
    · refine ⟨(φ.1 s).2, (mem_fixed_zpowers_iff (b := y)).2 ?_⟩
      have h1 : ((Ly (φ.1 s) : ↥MY) : Additive Q) = ((φ.1 s : ↥MY) : Additive Q) :=
        congrArg (fun g => ((g s : ↥MY) : Additive Q)) φ.2
      rw [smulLin_apply] at h1
      have h2 := congrArg Additive.toMul h1
      rw [toMul_ofMul] at h2
      exact h2
    · show Ly ∘ₗ ((Submodule.inclusion hCY) ∘ₗ ψ) = (Submodule.inclusion hCY) ∘ₗ ψ
      refine LinearMap.ext fun s => Subtype.ext ?_
      show ((Ly (Submodule.inclusion hCY (ψ s)) : ↥MY) : Additive Q) = ((ψ s : ↥MC) : Additive Q)
      rw [smulLin_apply]
      have h1 := (mem_fixed_zpowers_iff (b := y)).1 (ψ s).2.2
      show Additive.ofMul (y • Additive.toMul ((ψ s : ↥MC) : Additive Q)) = _
      rw [h1, ofMul_toMul]
    · exact Subtype.ext (LinearMap.ext fun s => Subtype.ext rfl)
    · exact LinearMap.ext fun s => Subtype.ext rfl
  rw [heq] at hmod
  exact hmod

end HomCount

section NatEnd

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
  CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp L : Subgroup (MulAut W)}

theorem card_end_eq_two_of_nat (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hLM : L ≤ M) {V : Subgroup W} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1)
    {π : ↥(StatedSL 3 K) →* ↥L}
    (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia L V (V ⊓ fixV Mp) π)
    (hirr : letI := qAct hMp; XMod.IsIrr ↥(L.subgroupOf M) (tilde Mp ⊤ V)) :
    letI := qAct hMp
    Nat.card (Module.End ↥(XMod.opRing ↥(L.subgroupOf M) (W ⧸ modFix Mp (⊤ : Subgroup W)))
      ↥(XMod.toSubmod hirr.1)) = 2 := by
  let _i := qAct hMp
  let ψ : ↥L →* ↥(L.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hψ : Function.Surjective ψ := (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  let f : ↥V →* ↥(tilde Mp ⊤ V) :=
    (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap V
  have hf : Function.Surjective f :=
    (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap_surjective V
  have hfker : ∀ u : ↥V, f u = 1 ↔ (u : W) ∈ V ⊓ fixV Mp := by
    intro u
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk (u : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq] at h2
      exact ⟨u.2, h2⟩
    · intro h1
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq]
      exact h1.2
  have hR' := realizesVia_actAut hirr.1 hR ψ hψ f hf hfker (fun h u hu => rfl)
  have h1 := SmithD310U.card_eqv_le hR'
  rw [hK, pow_one] at h1
  have h2 := card_end_le hirr.1
  have := (XMod.isIrr_iff hirr.1).1 hirr
  have hfin : Finite (Module.End ↥(XMod.opRing ↥(L.subgroupOf M)
      (W ⧸ modFix Mp (⊤ : Subgroup W))) ↥(XMod.toSubmod hirr.1)) :=
    Finite.of_injective (fun g => (g : ↥(XMod.toSubmod hirr.1) → ↥(XMod.toSubmod hirr.1)))
      DFunLike.coe_injective
  have : Nontrivial ↥(XMod.toSubmod hirr.1) := IsSimpleModule.nontrivial
    ↥(XMod.opRing ↥(L.subgroupOf M) (W ⧸ modFix Mp (⊤ : Subgroup W))) _
  have h3 : 1 < Nat.card (Module.End ↥(XMod.opRing ↥(L.subgroupOf M)
      (W ⧸ modFix Mp (⊤ : Subgroup W))) ↥(XMod.toSubmod hirr.1)) := Finite.one_lt_card
  omega

end NatEnd

section EndSimple

variable {R : Type*} [Ring R] {S : Type*} [AddCommGroup S] [Module R S]

theorem injective_apply_of_ne_zero [IsSimpleModule R S] {v : S} (hv : v ≠ 0) :
    Function.Injective fun e : Module.End R S => e v := by
  intro e e' h
  have h1 : (e - e') v = 0 := by
    rw [LinearMap.sub_apply]
    exact sub_eq_zero.2 h
  rcases LinearMap.bijective_or_eq_zero (e - e') with hb | h0
  · exact absurd (hb.1 (h1.trans (map_zero _).symm)) hv
  · exact sub_eq_zero.1 h0

theorem card_end_le_card_of_isSimpleModule [Finite S] [IsSimpleModule R S] :
    Nat.card (Module.End R S) ≤ Nat.card S := by
  have := IsSimpleModule.nontrivial R S
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  exact Nat.card_le_card_of_injective _ (injective_apply_of_ne_zero hv)

theorem exists_card_eq_card_end_pow_of_isSimpleModule [Finite S] [IsSimpleModule R S] :
    ∃ m : ℕ, Nat.card S = Nat.card (Module.End R S) ^ m := by
  classical
  let : DivisionRing (Module.End R S) := Module.End.instDivisionRing
  exact ⟨_, Module.natCard_eq_pow_finrank⟩

theorem smul_comm_of_card_end_eq [Finite S] [IsSimpleModule R S]
    (h : Nat.card (Module.End R S) = Nat.card S) (r r' : R) (v : S) :
    r • r' • v = r' • r • v := by
  classical
  let : DivisionRing (Module.End R S) := Module.End.instDivisionRing
  have : Finite (Module.End R S) :=
    Finite.of_injective (fun f : Module.End R S => (f : S → S)) DFunLike.coe_injective
  have hcomm : ∀ a b : Module.End R S, a * b = b * a := by
    let : Field (Module.End R S) := littleWedderburn _
    exact mul_comm
  have := IsSimpleModule.nontrivial R S
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : S)
  have hbij := (injective_apply_of_ne_zero hv₀).bijective_of_nat_card_le h.ge
  have hact : ∀ r : R, ∃ e : Module.End R S, ∀ v : S, r • v = e v := by
    intro r
    obtain ⟨e, he⟩ := hbij.2 (r • v₀)
    refine ⟨e, fun v => ?_⟩
    obtain ⟨f, rfl⟩ := hbij.2 v
    calc r • f v₀ = f (r • v₀) := (map_smul f r v₀).symm
      _ = f (e v₀) := by rw [← he]
      _ = (f * e) v₀ := rfl
      _ = (e * f) v₀ := by rw [hcomm]
      _ = e (f v₀) := rfl
  obtain ⟨e, he⟩ := hact r
  obtain ⟨e', he'⟩ := hact r'
  calc r • r' • v = e (e' v) := by rw [he', he]
    _ = (e * e') v := rfl
    _ = (e' * e) v := by rw [hcomm]
    _ = e' (e v) := rfl
    _ = r' • r • v := by rw [he, he']

end EndSimple

section XModEnd

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem card_end_lt_card [Finite Q] {Λ : Subgroup Γ} (hΛ : ⁅Λ, Λ⁆ = Λ) {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) (hIc : XMod.commOf ↥Λ I = I) :
    Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) < Nat.card ↥I := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have : Finite (Additive Q) := ‹Finite Q›
  rw [← card_toSubmod hI.1]
  refine lt_of_le_of_ne card_end_le_card_of_isSimpleModule fun h => hI.2.1.ne' ?_
  have hcomm : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ q ∈ I, l • l' • q = l' • l • q := by
    intro l hl l' hl' q hq
    have h1 := smul_comm_of_card_end_eq h
      (⟨XMod.actEnd ↥Λ Q ⟨l, hl⟩, XMod.actEnd_mem_opRing _⟩ : ↥(XMod.opRing ↥Λ Q))
      ⟨XMod.actEnd ↥Λ Q ⟨l', hl'⟩, XMod.actEnd_mem_opRing _⟩ ⟨Additive.ofMul q, hq⟩
    exact congrArg (fun w : ↥(XMod.toSubmod hI.1) => Additive.toMul w.1) h1
  have hle : ⁅Λ, Λ⁆ ≤ fixingSubgroup Γ (I : Set Q) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [mem_fixingSubgroup_iff]
    intro q hq
    have hp : g₁⁻¹ • g₂⁻¹ • q ∈ I :=
      hI.1 ⟨g₁⁻¹, inv_mem hg₁⟩ _ (hI.1 ⟨g₂⁻¹, inv_mem hg₂⟩ _ hq)
    rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, hcomm g₁ hg₁ g₂ hg₂ _ hp,
      smul_inv_smul, smul_inv_smul]
  rw [← hIc, ← le_bot_iff, XMod.commOf_le_iff]
  intro a q hq
  rw [Subgroup.mem_bot, mul_inv_eq_one]
  exact (mem_fixingSubgroup_iff Γ).1 (hle (hΛ.ge a.2)) q hq

theorem exists_card_eq_card_end_pow [Finite Q] {Λ : Subgroup Γ} {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) :
    ∃ m : ℕ,
      Nat.card ↥I = Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1)) ^ m := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have : Finite (Additive Q) := ‹Finite Q›
  rw [← card_toSubmod hI.1]
  exact exists_card_eq_card_end_pow_of_isSimpleModule

end XModEnd

section NoTrivial

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem commOf_eq_of_le_isoComp [Finite Q] {Λ : Subgroup Γ} {I R : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) (hIc : XMod.commOf ↥Λ I = I) (hR : XMod.IsInv ↥Λ R)
    (hRI : R ≤ isoComp ↥Λ I) : XMod.commOf ↥Λ R = R := by
  classical
  have := isSemisimpleModule_toSubmod hI hR hRI
  set C := XMod.commOf ↥Λ R with hCdef
  have hC : XMod.IsInv ↥Λ C := XMod.isInv_commOf R
  have hCR : C ≤ R := XMod.commOf_le_of_isInv hR
  set NC := (XMod.toSubmod hC).comap (XMod.toSubmod hR).subtype with hNC
  obtain ⟨D₀, hD₀⟩ := exists_isCompl NC
  set Dg := XMod.ofSubmod (D₀.map (XMod.toSubmod hR).subtype) with hDg
  have hDginv : XMod.IsInv ↥Λ Dg := XMod.isInv_ofSubmod _
  have hDgR : Dg ≤ R := ofSubmod_map_le hR D₀
  have hDgC : ∀ q ∈ Dg, q ∈ C → q = 1 := by
    intro q hq hqC
    obtain ⟨x, hx, hxq⟩ := hq
    have hxC : x ∈ NC := by
      show ((x : Additive Q)) ∈ XMod.toSubmod hC
      rw [show ((x : Additive Q)) = Additive.ofMul q from hxq]
      exact hqC
    have h0 : x ∈ D₀ ⊓ NC := ⟨hx, hxC⟩
    rw [hD₀.symm.inf_eq_bot, Submodule.mem_bot] at h0
    have h1 : Additive.ofMul q = 0 := by rw [← hxq, h0]; rfl
    exact h1
  have hDgfix : Dg ≤ XMod.fixed ↥Λ ⊤ := by
    intro d hd
    refine ⟨trivial, fun a => ?_⟩
    have h1 : (a • d) * d⁻¹ ∈ C := XMod.mem_commOf_of_mem a (hDgR hd)
    have h2 : (a • d) * d⁻¹ ∈ Dg := Dg.mul_mem (hDginv a d hd) (Dg.inv_mem hd)
    exact mul_inv_eq_one.1 (hDgC _ h2 h1)
  have hDgbot : Dg = ⊥ := by
    by_contra hne
    obtain ⟨J, hJD, hJ⟩ := SmithD391.exists_isIrr_le hDginv hne
    have hJI : XMod.Iso ↥Λ J I := iso_of_le_isoComp hJ ((hJD.trans hDgR).trans hRI)
    have h1 : XMod.commOf ↥Λ J = J := XMod.commOf_eq_of_iso hI hJ hJI hIc
    have h2 : XMod.commOf ↥Λ J = ⊥ := XMod.commOf_eq_bot_iff.2 (hJD.trans hDgfix)
    exact hJ.2.1.ne (h2.symm.trans h1)
  have hD₀bot : D₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : Additive.toMul (x : Additive Q) ∈ Dg := ⟨x, hx, rfl⟩
    rw [hDgbot, Subgroup.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact Subtype.ext h1
  have hNCtop : NC = ⊤ := by
    have := hD₀.sup_eq_top
    rwa [hD₀bot, sup_bot_eq] at this
  refine le_antisymm hCR fun r hr => ?_
  have h1 : (⟨Additive.ofMul r, hr⟩ : ↥(XMod.toSubmod hR)) ∈ NC := by
    rw [hNCtop]
    exact Submodule.mem_top
  exact h1

end NoTrivial

section PElement

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem exists_pElement_of_factorization [Finite Γ] {G Λ P : Subgroup Γ} {V Y : Subgroup Q}
    (hΛG : ∀ g ∈ G, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hPG : P ≤ G) (hP2 : IsPGroup 2 ↥P)
    (hodd : Odd (P.subgroupOf G).index) (hYG : ∀ g ∈ G, ∀ q ∈ Y, g • q ∈ Y) (hVY : V ≤ Y)
    (hΛV : ∀ l ∈ Λ, l • V = V) (hPV : ∀ p ∈ P, p • V = V)
    (hfac : ∀ g ∈ G, ∃ l ∈ Λ, ∃ c ∈ G, (∀ x ∈ Λ, c * x = x * c) ∧ ∃ τ ∈ P, g = l * c * τ)
    (hgen : Y ≤ ⨆ g ∈ G, g • V) (hne : ¬ Y ≤ V) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ y ∈ G, (∀ x ∈ Λ, y * x = x * y) ∧
      (∃ n : ℕ, y ^ (p ^ n) = 1) ∧ (∀ q ∈ Y, y ^ p • q = q) ∧ ∃ q ∈ Y, y • q ≠ q := by
  classical
  set C : Subgroup Γ := G ⊓ Subgroup.centralizer (Λ : Set Γ) with hC
  set φ := resJ G Y hYG with hφ
  set φ' : ↥G →* ↥φ.range := φ.rangeRestrict with hφ'
  have hφ's : Function.Surjective φ' := φ.rangeRestrict_surjective
  set C' : Subgroup ↥G := C.subgroupOf G with hC'
  have hC'n : C'.Normal := by
    refine ⟨fun c hc g => ?_⟩
    have hc' : (c : Γ) ∈ C := hc
    refine Subgroup.mem_subgroupOf.2 ⟨G.mul_mem (G.mul_mem g.2 hc'.1) (G.inv_mem g.2), ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hx' : (g : Γ)⁻¹ * x * (g : Γ)⁻¹⁻¹ ∈ Λ := hΛG _ (G.inv_mem g.2) x hx
    rw [inv_inv] at hx'
    have h1 := Subgroup.mem_centralizer_iff.1 hc'.2 _ hx'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * ((g : Γ) * (c : Γ) * (g : Γ)⁻¹)
        = (g : Γ) * (((g : Γ)⁻¹ * x * (g : Γ)) * (c : Γ)) * (g : Γ)⁻¹ := by group
      _ = (g : Γ) * ((c : Γ) * ((g : Γ)⁻¹ * x * (g : Γ))) * (g : Γ)⁻¹ := by rw [h1]
      _ = (g : Γ) * (c : Γ) * (g : Γ)⁻¹ * x := by group
  have : Finite ↥φ.range := Finite.of_surjective φ' hφ's
  set N : Subgroup ↥φ.range := C'.map φ' with hN
  have hNn : N.Normal := hC'n.map φ' hφ's
  by_cases h2 : IsPGroup 2 ↥N
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP2' : IsPGroup 2 ↥(P.subgroupOf G) :=
      hP2.of_injective ((Subgroup.subgroupOfEquivOfLe hPG).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPG).injective
    have hidx : ¬ 2 ∣ (P.subgroupOf G).index := fun h => (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 h)
    set S := (hP2'.toSylow hidx).mapSurjective hφ's with hS
    have hNS : N ≤ S := h2.le_sylow_of_normal S
    have hcP : ∀ c ∈ C, ∃ τ ∈ P, ∀ q ∈ Y, c • q = τ • q := by
      intro c hc
      have h1 : φ' ⟨c, hc.1⟩ ∈ N := ⟨⟨c, hc.1⟩, hc, rfl⟩
      obtain ⟨τ, hτ, hτc⟩ := hNS h1
      refine ⟨τ, hτ, fun q hq => ?_⟩
      have h3 := congrArg (fun z : ↥φ.range => (((z : MulAut ↥Y) ⟨q, hq⟩ : ↥Y) : Q)) hτc
      exact h3.symm
    have hcV : ∀ c ∈ C, c • V = V := by
      intro c hc
      obtain ⟨τ, hτ, hτc⟩ := hcP c hc
      have h1 : c • V = τ • V := by
        ext q
        simp only [Subgroup.mem_smul_pointwise_iff_exists]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v, hv, (hτc v (hVY hv)).symm⟩
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v, hv, hτc v (hVY hv)⟩
      rw [h1, hPV τ hτ]
    have hgV : ∀ g ∈ G, g • V = V := by
      intro g hg
      obtain ⟨l, hl, c, hcG, hcΛ, τ, hτ, rfl⟩ := hfac g hg
      have hcC : c ∈ C := ⟨hcG, Subgroup.mem_centralizer_iff.2 fun x hx => (hcΛ x hx).symm⟩
      rw [mul_smul, mul_smul, hPV τ hτ, hcV c hcC, hΛV l hl]
    exact hne (hgen.trans (iSup₂_le fun g hg => (hgV g hg).le))
  ·
    obtain ⟨p, hp, hpN, hp2⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card ↥N ∧ p ≠ 2 := by
      by_contra hcon
      push Not at hcon
      apply h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := (Nat.card ↥N).primeFactorsList.length) ?_
      exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdN => hcon _ hd hdN
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpN
    obtain ⟨c, hc, hcx⟩ := x.2
    let f : ↥C' →* ↥φ.range := φ'.comp C'.subtype
    have hfc : f ⟨c, hc⟩ = (x : ↥φ.range) := hcx
    have hxp' : (x : ↥φ.range) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]; rfl
    obtain ⟨k, n, hkn, hfk⟩ : ∃ k n : ℕ, ((⟨c, hc⟩ : ↥C') ^ k) ^ (p ^ n) = 1 ∧
        f ((⟨c, hc⟩ : ↥C') ^ k) = (x : ↥φ.range) := by
      obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd
        (orderOf_pos (⟨c, hc⟩ : ↥C')).ne' p hp.one_lt.ne'
      have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb).symm
      obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
      refine ⟨b * e, a, ?_, ?_⟩
      · rw [← pow_mul, show b * e * p ^ a = p ^ a * b * e by ring, pow_mul, ← hab,
          pow_orderOf_eq_one, one_pow]
      · rw [map_pow, hfc, pow_eq_pow_mod _ hxp', he, pow_one]
    set y : Γ := (((⟨c, hc⟩ : ↥C') ^ k).1 : ↥G).1 with hy
    have hyC : y ∈ C := ((⟨c, hc⟩ : ↥C') ^ k).2
    have hφy : (φ (((⟨c, hc⟩ : ↥C') ^ k : ↥C') : ↥G) : MulAut ↥Y) = ((x : ↥φ.range) : MulAut ↥Y) :=
      congrArg Subtype.val hfk
    have hxp : ((x : ↥φ.range) : MulAut ↥Y) ^ p = 1 := by
      have h1 : x ^ p = 1 := by rw [← hx, pow_orderOf_eq_one]
      have h2 := congrArg (fun z : ↥N => ((z : ↥φ.range) : MulAut ↥Y)) h1
      simpa using h2
    have hx1 : ((x : ↥φ.range) : MulAut ↥Y) ≠ 1 := by
      intro h1
      have h2 : x = 1 := Subtype.ext (Subtype.ext h1)
      rw [h2, orderOf_one] at hx
      exact hp.one_lt.ne hx
    refine ⟨p, hp, hp2, y, hyC.1, fun z hz => (Subgroup.mem_centralizer_iff.1 hyC.2 z hz).symm,
      ⟨n, ?_⟩, fun q hq => ?_, ?_⟩
    · have h1 := congrArg (fun z : ↥C' => ((z : ↥G) : Γ)) hkn
      simpa [hy] using h1
    · have h1 : (φ ((((⟨c, hc⟩ : ↥C') ^ k : ↥C') : ↥G) ^ p) : MulAut ↥Y) = 1 := by
        rw [map_pow, hφy, hxp]
      have h2 := congrArg (fun e : MulAut ↥Y => ((e ⟨q, hq⟩ : ↥Y) : Q)) h1
      have h3 : y ^ p = (((((⟨c, hc⟩ : ↥C') ^ k : ↥C') : ↥G) ^ p : ↥G) : Γ) := by
        rw [Subgroup.coe_pow]
      rw [h3]
      exact h2
    · by_contra hcon
      push Not at hcon
      apply hx1
      rw [← hφy]
      refine MulEquiv.ext fun q => Subtype.ext ?_
      exact hcon q.1 q.2

end PElement

section Arith

theorem prime_of_two_pow_modEq {k c' p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 4)
    (hc : c' < k) (h : 2 ^ k ≡ 2 ^ c' [MOD p]) : p = 3 ∨ p = 7 ∨ (p = 5 ∧ k = 4 ∧ c' = 0) := by
  have hle : 2 ^ c' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc.le
  have hd := (Nat.modEq_iff_dvd' hle).1 h.symm
  have hpos : 0 < 2 ^ k - 2 ^ c' := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) hc)
  have hple : p ≤ 2 ^ k - 2 ^ c' := Nat.le_of_dvd hpos hd
  have h16 : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk
  have hp1 := hp.two_le
  have hp16 : p ≤ 16 := hple.trans ((Nat.sub_le _ _).trans (h16.trans (by norm_num)))
  clear h hle hpos hple h16
  interval_cases k <;> interval_cases c' <;> interval_cases p <;> revert hp hp2 hd <;> decide

theorem prime_of_end_pow_two_modEq {e c' p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : e = 2 ∨ e = 4) (hc : c' < 2) (h : e ^ 2 ≡ e ^ c' [MOD p]) : p = 3 ∨ p = 5 := by
  have he1 : 1 < e := by rcases he with rfl | rfl <;> norm_num
  have hle : e ^ c' ≤ e ^ 2 := Nat.pow_le_pow_right he1.le hc.le
  have hd := (Nat.modEq_iff_dvd' hle).1 h.symm
  have hpos : 0 < e ^ 2 - e ^ c' := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right he1 hc)
  have hple : p ≤ e ^ 2 - e ^ c' := Nat.le_of_dvd hpos hd
  have h16 : e ^ 2 ≤ 16 := by rcases he with rfl | rfl <;> norm_num
  have hp1 := hp.two_le
  have hp16 : p ≤ 16 := hple.trans ((Nat.sub_le _ _).trans h16)
  clear h hle hpos hple h16 he1
  rcases he with rfl | rfl <;> interval_cases c' <;> interval_cases p <;> revert hp hp2 hd <;>
    decide

theorem eq_two_or_four_of_pow {e m : ℕ} (he : Even e) (hlt : e < 16) (hm : 16 = e ^ m) :
    e = 2 ∨ e = 4 := by
  have h2 : 2 ≤ e := by
    by_contra hcon
    have h1 : e ^ m ≤ 1 := pow_le_one₀ (Nat.zero_le e) (by omega)
    omega
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have h1 : 2 ^ m ≤ e ^ m := Nat.pow_le_pow_left h2 m
    have h3 : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m <;> interval_cases e <;> revert he hm <;> decide

end Arith

end CFSG.Quasithin.SmithD321
