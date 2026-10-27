module

public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin CFSG.Open

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
variable {W : Type*} [CommGroup W]

structure IsCoord (LM : LinModel D K M) (H : Subgroup (MulAut W)) (Z : Subgroup W)
    (π : D.Gam →* ↥H) (f : W → M) : Prop where
  map_mul : ∀ u u' : W, f (u * u') = f u + f u'
  ker : ∀ u : W, f u = 0 ↔ u ∈ Z
  surj : Function.Surjective f
  act : ∀ (γ : D.Gam) (u : W), f (((π γ : ↥H) : MulAut W) u) = LM.lin γ (f u)
  onto : Function.Surjective π

variable {LM : LinModel D K M} {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : D.Gam →* ↥H}

theorem exists_isCoord (LM : LinModel D K M) (h : D.RealizesVia H ⊤ Z π) :
    ∃ f : W → M, IsCoord LM H Z π f := by
  obtain ⟨f, hmul, hker, hsurj, hact⟩ := exists_coord LM h
  exact ⟨f, ⟨fun u u' => hmul u trivial u' trivial, fun u => hker u trivial,
    fun m => (hsurj m).imp fun u hu => hu.2, fun γ u => hact γ u trivial, h.1⟩⟩

namespace IsCoord

variable {f : W → M} (hf : IsCoord LM H Z π f)
include hf

theorem map_one : f 1 = 0 := by
  have h := hf.map_mul 1 1
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

theorem map_inv (u : W) : f u⁻¹ = - f u := by
  have h := hf.map_mul u u⁻¹
  rw [mul_inv_cancel, hf.map_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem map_mul_inv (u v : W) : f (u * v⁻¹) = f u - f v := by
  rw [hf.map_mul, hf.map_inv, sub_eq_add_neg]

theorem eq_iff (u v : W) : f u = f v ↔ u * v⁻¹ ∈ Z := by
  rw [← hf.ker, hf.map_mul_inv, sub_eq_zero]

theorem exists_lin (h : ↥H) : ∃ γ : D.Gam, ∀ u : W, f ((h : MulAut W) u) = LM.lin γ (f u) := by
  obtain ⟨γ, rfl⟩ := hf.onto h
  exact ⟨γ, hf.act γ⟩

@[expose] def img (U : Subgroup W) : AddSubgroup M where
  carrier := f '' U
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, U.mul_mem hu hv, hf.map_mul u v⟩
  zero_mem' := ⟨1, U.one_mem, hf.map_one⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, U.inv_mem hu, hf.map_inv u⟩

theorem mem_img {U : Subgroup W} {x : M} : x ∈ hf.img U ↔ ∃ u ∈ U, f u = x := Iff.rfl

theorem mem_iff {U : Subgroup W} (hZU : Z ≤ U) (w : W) : w ∈ U ↔ f w ∈ hf.img U := by
  refine ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩
  rintro ⟨u, hu, hfu⟩
  have h1 : w * u⁻¹ ∈ U := hZU ((hf.eq_iff w u).mp hfu.symm)
  have h2 := U.mul_mem h1 hu
  rwa [inv_mul_cancel_right] at h2

theorem card_img {U : Subgroup W} : Nat.card (hf.img U) = Z.relIndex U := by
  let φ : ↥U →* Multiplicative M :=
    { toFun := fun u => Multiplicative.ofAdd (f u)
      map_one' := congrArg Multiplicative.ofAdd hf.map_one
      map_mul' := fun u v => congrArg Multiplicative.ofAdd (hf.map_mul u v) }
  have hker : φ.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hf.ker]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  symm
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, ?_⟩
      invFun := fun y => ⟨Multiplicative.ofAdd y.1, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · obtain ⟨u, hu⟩ := x.2
    exact ⟨u, u.2, by rw [← hu]; rfl⟩
  · obtain ⟨u, hu, hfu⟩ := y.2
    exact ⟨⟨u, hu⟩, by rw [← hfu]; rfl⟩

@[expose] def toHom : W →* Multiplicative M where
  toFun w := Multiplicative.ofAdd (f w)
  map_one' := congrArg Multiplicative.ofAdd hf.map_one
  map_mul' u v := congrArg Multiplicative.ofAdd (hf.map_mul u v)

theorem exists_section (hW : ∀ w : W, w ^ 2 = 1) :
    ∃ σ : Multiplicative M →* W, ∀ x, f (σ x) = Multiplicative.toAdd x := by
  have : IsElementaryAbelian 2 W := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := IsElementaryAbelian.exists_isCompl 2 W Z
  have hinj : Function.Injective (hf.toHom.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h0 : f s = 0 := congrArg Multiplicative.toAdd hs
    have h1 : (s : W) ∈ Z ⊓ S := ⟨(hf.ker s).mp h0, s.2⟩
    rw [disjoint_iff.mp hS.disjoint, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective (hf.toHom.comp S.subtype) := by
    intro x
    obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd x)
    have hw' : w ∈ Z ⊔ S := by rw [codisjoint_iff.mp hS.codisjoint]; exact Subgroup.mem_top w
    obtain ⟨z, hz, t, ht, rfl⟩ := Subgroup.mem_sup.mp hw'
    refine ⟨⟨t, ht⟩, ?_⟩
    change Multiplicative.ofAdd (f t) = x
    rw [hf.map_mul, (hf.ker z).mpr hz, zero_add] at hw
    rw [hw]
    rfl
  let e := MulEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨S.subtype.comp e.symm.toMonoidHom, fun x => ?_⟩
  have := congrArg Multiplicative.toAdd (e.apply_symm_apply x)
  exact this

theorem exists_scalarLift (hW : ∀ w : W, w ^ 2 = 1) (c : K) :
    ∃ φ : W →* W, (∀ z ∈ Z, φ z ∈ Z) ∧
      (∀ h ∈ H, ∀ w : W, φ (h w) * (h (φ w))⁻¹ ∈ Z) ∧ ∀ w, f (φ w) = c • f w := by
  obtain ⟨σ, hσ⟩ := hf.exists_section hW
  let sc : Multiplicative M →* Multiplicative M :=
    { toFun := fun x => Multiplicative.ofAdd (c • Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' := fun x y => by simp [smul_add] }
  have hφ : ∀ w, f ((σ.comp (sc.comp hf.toHom)) w) = c • f w := fun w =>
    hσ (sc (hf.toHom w))
  refine ⟨σ.comp (sc.comp hf.toHom), fun z hz => ?_, fun h hh w => ?_, hφ⟩
  · rw [← hf.ker, hφ, (hf.ker z).mpr hz, smul_zero]
  · obtain ⟨γ, hγ⟩ := hf.exists_lin ⟨h, hh⟩
    rw [← hf.ker, hf.map_mul_inv, hφ, hγ, hγ, hφ, LinearMap.map_smul, sub_self]

theorem map_eq_of_eq {φ : W →* W} (hφ : ∀ z ∈ Z, φ z ∈ Z) {a b : W} (h : f a = f b) :
    f (φ a) = f (φ b) := by
  rw [hf.eq_iff] at h ⊢
  have := hφ _ h
  rwa [_root_.map_mul, _root_.map_inv] at this

@[expose] noncomputable def inducedMap (φ : W →* W) (hφ : ∀ z ∈ Z, φ z ∈ Z) : M →+ M where
  toFun x := f (φ (Function.surjInv hf.surj x))
  map_zero' := by
    rw [hf.map_eq_of_eq hφ ((Function.surjInv_eq hf.surj 0).trans hf.map_one.symm),
      _root_.map_one, hf.map_one]
  map_add' x y := by
    have h : f (Function.surjInv hf.surj (x + y)) =
        f (Function.surjInv hf.surj x * Function.surjInv hf.surj y) := by
      rw [hf.map_mul, Function.surjInv_eq hf.surj, Function.surjInv_eq hf.surj,
        Function.surjInv_eq hf.surj]
    rw [hf.map_eq_of_eq hφ h, _root_.map_mul, hf.map_mul]

theorem inducedMap_apply (φ : W →* W) (hφ : ∀ z ∈ Z, φ z ∈ Z) (w : W) :
    hf.inducedMap φ hφ (f w) = f (φ w) :=
  hf.map_eq_of_eq hφ (Function.surjInv_eq hf.surj (f w))

theorem inducedMap_comm (φ : W →* W) (hφ : ∀ z ∈ Z, φ z ∈ Z)
    (hc : ∀ h ∈ H, ∀ w : W, φ (h w) * (h (φ w))⁻¹ ∈ Z) (γ : D.Gam) (x : M) :
    hf.inducedMap φ hφ (LM.lin γ x) = LM.lin γ (hf.inducedMap φ hφ x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, hf.inducedMap_apply, hf.inducedMap_apply, ← hf.act]
  exact (hf.eq_iff _ _).mpr (hc _ (π γ).2 w)

theorem endStableW_iff (hW : ∀ w : W, w ^ 2 = 1)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {U : Subgroup W} (hZU : Z ≤ U) :
    Ch11.SecA.EndStableW H Z U ↔ ∀ (c : K), ∀ x ∈ hf.img U, c • x ∈ hf.img U := by
  constructor
  · rintro hst c _ ⟨u, hu, rfl⟩
    obtain ⟨φ, hφZ, hφc, hφ⟩ := hf.exists_scalarLift hW c
    exact ⟨φ u, hst φ hφZ hφc u hu, hφ u⟩
  · intro hsc φ hφZ hφc u hu
    obtain ⟨c, hc⟩ := hcomm (hf.inducedMap φ hφZ) (hf.inducedMap_comm φ hφZ hφc)
    rw [hf.mem_iff hZU, ← hf.inducedMap_apply φ hφZ, hc]
    exact hsc c _ ⟨u, hu, rfl⟩

theorem mem_stabW_iff {U : Subgroup W} (hZU : Z ≤ U) (γ : D.Gam) :
    ((π γ : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U ↔
      ∀ x : M, x ∈ hf.img U ↔ LM.lin γ x ∈ hf.img U := by
  rw [Ch11.SecA.mem_stabW]
  constructor
  · intro h x
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [← hf.mem_iff hZU, ← hf.act, ← hf.mem_iff hZU]
    exact h w
  · intro h u
    rw [hf.mem_iff hZU, hf.mem_iff hZU, hf.act]
    exact h (f u)

end IsCoord

end CFSG.Quasithin.Vol2.KGNat
