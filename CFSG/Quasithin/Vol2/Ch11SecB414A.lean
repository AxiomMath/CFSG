module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open Subgroup

section Section

variable {G : Type} [Group G] (V Z : Subgroup G)

structure IsElem : Prop where
  le : Z ≤ V
  sq : ∀ v ∈ V, v ^ 2 ∈ Z
  comm : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ Z

variable [hE : Fact (IsElem V Z)]

instance normal_subgroupOf : (Z.subgroupOf V).Normal where
  conj_mem z hz v := by
    rw [mem_subgroupOf] at hz ⊢
    have h := hE.out.comm v v.2 z (hE.out.le hz)
    have e : ((v * z * v⁻¹ : ↥V) : G) = (v * z * v⁻¹ * z⁻¹ : G) * z := by
      simp only [coe_mul, coe_inv]
      group
    rw [e]
    exact Z.mul_mem h hz

instance secCommGroup : CommGroup (↥V ⧸ Z.subgroupOf V) :=
  { (inferInstance : Group (↥V ⧸ Z.subgroupOf V)) with
    mul_comm := fun u w => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have h := hE.out.comm _ (inv_mem y.2) _ (inv_mem x.2)
      simp only [inv_inv] at h
      simpa [mul_assoc] using h }

abbrev SecU : Type := Additive (↥V ⧸ Z.subgroupOf V)

@[expose] def secπ (v : ↥V) : SecU V Z := Additive.ofMul (v : ↥V ⧸ Z.subgroupOf V)

omit hE in
theorem secπ_surjective : Function.Surjective (secπ V Z) := fun u =>
  QuotientGroup.mk_surjective (Additive.toMul u)

theorem secπ_mul (v w : ↥V) : secπ V Z (v * w) = secπ V Z v + secπ V Z w := rfl

theorem secπ_inv (v : ↥V) : secπ V Z v⁻¹ = -secπ V Z v := rfl

theorem secπ_one : secπ V Z 1 = 0 := rfl

theorem secπ_eq_zero_iff (v : ↥V) : secπ V Z v = 0 ↔ (v : G) ∈ Z := by
  change (v : ↥V ⧸ Z.subgroupOf V) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem secπ_eq_iff (v w : ↥V) : secπ V Z v = secπ V Z w ↔ (v : G) * (w : G)⁻¹ ∈ Z := by
  rw [← sub_eq_zero, sub_eq_add_neg, ← secπ_inv, ← secπ_mul, secπ_eq_zero_iff, coe_mul,
    coe_inv]

theorem two_nsmul_secU (u : SecU V Z) : 2 • u = 0 := by
  obtain ⟨v, rfl⟩ := secπ_surjective V Z u
  rw [two_nsmul, ← secπ_mul, secπ_eq_zero_iff, coe_mul, ← pow_two]
  exact hE.out.sq _ v.2

instance : Module (ZMod 2) (SecU V Z) := AddCommGroup.zmodModule (two_nsmul_secU V Z)

instance [Finite G] : Finite (SecU V Z) :=
  Finite.of_surjective (secπ V Z) (secπ_surjective V Z)

@[expose] def conjV (γ : G) (hγ : γ ∈ normalizer (V : Set G)) : ↥V →* ↥V where
  toFun v := ⟨γ * v * γ⁻¹, (mem_normalizer_iff.mp hγ v).mp v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by
    simp only [coe_mul]
    group)

omit hE in
theorem conjV_coe (γ : G) (hγ : γ ∈ normalizer (V : Set G)) (v : ↥V) :
    (conjV V γ hγ v : G) = γ * v * γ⁻¹ := rfl

omit hE in
theorem le_comap_conjV (γ : G) (hV : γ ∈ normalizer (V : Set G))
    (hZ : γ ∈ normalizer (Z : Set G)) : Z.subgroupOf V ≤ (Z.subgroupOf V).comap (conjV V γ hV) := by
  intro z hz
  rw [mem_comap, mem_subgroupOf, conjV_coe]
  exact (mem_normalizer_iff.mp hZ z).mp hz

@[expose] noncomputable def conjU (γ : G) (hV : γ ∈ normalizer (V : Set G))
    (hZ : γ ∈ normalizer (Z : Set G)) : SecU V Z →+ SecU V Z :=
  MonoidHom.toAdditive (QuotientGroup.map _ _ (conjV V γ hV) (le_comap_conjV V Z γ hV hZ))

variable (Γ : Subgroup G) (hΓV : Γ ≤ normalizer (V : Set G)) (hΓZ : Γ ≤ normalizer (Z : Set G))

@[expose] noncomputable def secRep : Representation (ZMod 2) ↥Γ (SecU V Z) where
  toFun γ := (conjU V Z γ (hΓV γ.2) (hΓZ γ.2)).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := secπ_surjective V Z u
    show secπ V Z (conjV V _ _ v) = secπ V Z v
    congr 1
    exact Subtype.ext (by simp [conjV_coe])
  map_mul' γ δ := by
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := secπ_surjective V Z u
    show secπ V Z (conjV V _ _ v) = secπ V Z (conjV V _ _ (conjV V _ _ v))
    congr 1
    refine Subtype.ext ?_
    simp only [conjV_coe, coe_mul]
    group

theorem secRep_secπ (γ : ↥Γ) (v : ↥V) :
    secRep V Z Γ hΓV hΓZ γ (secπ V Z v) = secπ V Z (conjV V γ (hΓV γ.2) v) := rfl

theorem secRep_eq_one_iff (γ : ↥Γ) :
    secRep V Z Γ hΓV hΓZ γ = 1 ↔ ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z := by
  constructor
  · intro h v hv
    have h1 := congrArg (fun f => f (secπ V Z ⟨v, hv⟩)) h
    simp only [secRep_secπ, Module.End.one_apply] at h1
    rw [secπ_eq_iff, conjV_coe] at h1
    exact h1
  · intro h
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := secπ_surjective V Z u
    rw [secRep_secπ, Module.End.one_apply, secπ_eq_iff, conjV_coe]
    exact h v v.2

@[expose] def secPre (W : AddSubgroup (SecU V Z)) : Subgroup G where
  carrier := {g | ∃ h : g ∈ V, secπ V Z ⟨g, h⟩ ∈ W}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨V.mul_mem ha hb, W.add_mem ha' hb'⟩
  one_mem' := ⟨V.one_mem, W.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨V.inv_mem ha, W.neg_mem ha'⟩

theorem le_secPre (W : AddSubgroup (SecU V Z)) : Z ≤ secPre V Z W := fun z hz =>
  ⟨hE.out.le hz, by rw [(secπ_eq_zero_iff V Z ⟨z, hE.out.le hz⟩).mpr hz]; exact W.zero_mem⟩

theorem secPre_le (W : AddSubgroup (SecU V Z)) : secPre V Z W ≤ V := fun _ ⟨h, _⟩ => h

theorem secPre_le_secPre_iff {W₁ W₂ : AddSubgroup (SecU V Z)} :
    secPre V Z W₁ ≤ secPre V Z W₂ ↔ W₁ ≤ W₂ := by
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := secπ_surjective V Z u
    obtain ⟨_, h2⟩ := h ⟨v.2, hu⟩
    exact h2
  · rintro h g ⟨hg, hg'⟩
    exact ⟨hg, h hg'⟩

theorem secPre_injective : Function.Injective (secPre V Z) := fun _ _ h =>
  le_antisymm ((secPre_le_secPre_iff V Z).mp h.le) ((secPre_le_secPre_iff V Z).mp h.ge)

theorem secPre_bot : secPre V Z ⊥ = Z := by
  refine le_antisymm ?_ (le_secPre V Z ⊥)
  rintro g ⟨hg, hg'⟩
  exact (secπ_eq_zero_iff V Z ⟨g, hg⟩).mp ((AddSubgroup.mem_bot).mp hg')

theorem secPre_top : secPre V Z ⊤ = V :=
  le_antisymm (secPre_le V Z ⊤) fun _ hg => ⟨hg, AddSubgroup.mem_top _⟩

@[expose] def secImg (J : Subgroup G) : AddSubgroup (SecU V Z) where
  carrier := {u | ∃ v : ↥V, (v : G) ∈ J ∧ secπ V Z v = u}
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v * w, J.mul_mem hv hw, rfl⟩
  zero_mem' := ⟨1, J.one_mem, rfl⟩
  neg_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v⁻¹, J.inv_mem hv, rfl⟩

theorem secPre_secImg {J : Subgroup G} (hZJ : Z ≤ J) (hJV : J ≤ V) :
    secPre V Z (secImg V Z J) = J := by
  refine le_antisymm ?_ fun g hg => ⟨hJV hg, ⟨g, hJV hg⟩, hg, rfl⟩
  rintro g ⟨hg, w, hw, hwg⟩
  have h1 := (secπ_eq_iff V Z w ⟨g, hg⟩).mp hwg
  have e : g = ((w : G) * g⁻¹)⁻¹ * w := by group
  rw [e]
  exact J.mul_mem (J.inv_mem (hZJ h1)) hw

theorem secImg_secPre (W : AddSubgroup (SecU V Z)) : secImg V Z (secPre V Z W) = W := by
  ext u
  constructor
  · rintro ⟨v, ⟨_, hv⟩, rfl⟩
    exact hv
  · intro hu
    obtain ⟨v, rfl⟩ := secπ_surjective V Z u
    exact ⟨v, ⟨v.2, hu⟩, rfl⟩

variable {Γ} in
theorem le_normalizer_secPre {K : Subgroup G} (hK : K ≤ Γ) {W : AddSubgroup (SecU V Z)}
    (hW : ∀ γ : ↥Γ, (γ : G) ∈ K → ∀ u ∈ W, secRep V Z Γ hΓV hΓZ γ u ∈ W) :
    K ≤ normalizer (secPre V Z W : Set G) := by
  have key : ∀ k ∈ K, ∀ g ∈ secPre V Z W, k * g * k⁻¹ ∈ secPre V Z W := by
    rintro k hk g ⟨hg, hg'⟩
    have h1 := hW ⟨k, hK hk⟩ hk _ hg'
    rw [secRep_secπ] at h1
    exact ⟨_, h1⟩
  intro k hk
  refine mem_normalizer_iff.mpr fun g => ⟨key k hk g, fun h => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ h
  simpa [mul_assoc] using this

variable {Γ} in
theorem secImg_stable {J : Subgroup G} {γ : ↥Γ} (hγ : (γ : G) ∈ normalizer (J : Set G))
    {u : SecU V Z} (hu : u ∈ secImg V Z J) : secRep V Z Γ hΓV hΓZ γ u ∈ secImg V Z J := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, (mem_normalizer_iff.mp hγ v).mp hv, rfl⟩

end Section

end CFSG.Quasithin.H13.Ch4.B414
