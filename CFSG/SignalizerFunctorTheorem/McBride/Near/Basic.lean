module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.ClassNear

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type u} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_assoc_iff {X : Subgroup G} : X ∈ assoc p A θ ↔
    A ≤ Subgroup.normalizer (X : Set G) ∧ Nat.Coprime p (Nat.card X) ∧
      (∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a) ∧ NearASolvable p A X :=
  Iff.rfl

theorem mem_mhat_iff {X : Subgroup G} : X ∈ mhat p A θ ↔
    X ∈ assoc p A θ ∧ dsub A θ ≤ Subgroup.normalizer (X : Set G) :=
  Iff.rfl

theorem mem_mtil_iff {X : Subgroup G} : X ∈ mtil p A θ ↔ X ∈ assoc p A θ ∧ dsub A θ ≤ X :=
  Iff.rfl

theorem admits_dsub_of_le {X : Subgroup G} (h : dsub A θ ≤ X) : Admits (dsub A θ) X :=
  fun d hd => Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => X.mul_mem (X.mul_mem (h hd) hx) (X.inv_mem (h hd)),
      fun hx => by
        have := X.mul_mem (X.mul_mem (X.inv_mem (h hd)) hx) (h hd)
        simpa [mul_assoc] using this⟩

theorem mtil_subset_mhat : mtil p A θ ⊆ mhat p A θ :=
  fun _ hX => ⟨hX.1, admits_dsub_of_le hX.2⟩

theorem mhat_subset_assoc : mhat p A θ ⊆ assoc p A θ :=
  fun _ hX => hX.1

theorem mtil_subset_assoc : mtil p A θ ⊆ assoc p A θ :=
  fun _ hX => hX.1

theorem dsub_le_apply {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : dsub A θ ≤ θ a :=
  thetaOf_le_apply ha ha1

theorem dsub_le_centralizer_of_isFunctor (hθ : IsFunctor p A θ) :
    dsub A θ ≤ Subgroup.centralizer (A : Set G) :=
  hθ.thetaOf_le_centralizer le_rfl

theorem admits_dsub_of_isFunctor (hθ : IsFunctor p A θ) : Admits A (dsub A θ) :=
  hθ.normalizes_thetaOf le_rfl

theorem nearASolvable_of_isSolvable {W : Subgroup G} (hW : Group.IsSolvable W)
    (hcop : Nat.Coprime p (Nat.card W)) : NearASolvable p A W := by
  refine ⟨⟨hcop, fun K L _ _ hsimple hnonab => ?_⟩, ?_⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hsolK : Group.IsSolvable (K ⧸ L.subgroupOf K) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := K ⧸ L.subgroupOf K)).mpr hsolK a b)
  · exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : W ⊓ Subgroup.centralizer (A : Set G) ≤ W))

theorem nearASolvable_of_le [Finite G] (hp : p.Prime) {X Y : Subgroup G}
    (hX : NearASolvable p A X) (hYX : Y ≤ X) (hAY : Admits A Y) : NearASolvable p A Y :=
  (isSigClass_nearClass.{u} hp).mono G hYX hAY hX

theorem mem_assoc_of_le [Finite G] (hp : p.Prime) {X Y : Subgroup G} (hX : X ∈ assoc p A θ)
    (hYX : Y ≤ X) (hAY : Admits A Y) : Y ∈ assoc p A θ :=
  mem_signalizers_of_le hX hYX hAY (fun h => nearASolvable_of_le hp h hYX hAY)

theorem cenIn_le_dsub {X : Subgroup G} (hX : X ∈ assoc p A θ) : cenIn X A ≤ dsub A θ :=
  inf_centralizer_le_thetaOf hX le_rfl

theorem mem_mhat_of_le_mtil [Finite G] (hp : p.Prime) {X Y : Subgroup G}
    (hX : X ∈ mtil p A θ) (hYX : Y ≤ X) (hY : Admits (dsub A θ ⊔ A) Y) : Y ∈ mhat p A θ :=
  ⟨mem_assoc_of_le hp hX.1 hYX (le_trans le_sup_right hY), le_trans le_sup_left hY⟩

theorem mem_mhat_of_le_mhat [Finite G] (hp : p.Prime) {X Y : Subgroup G}
    (hX : X ∈ mhat p A θ) (hYX : Y ≤ X) (hY : Admits (dsub A θ ⊔ A) Y) : Y ∈ mhat p A θ :=
  ⟨mem_assoc_of_le hp hX.1 hYX (le_trans le_sup_right hY), le_trans le_sup_left hY⟩

section Functor

variable (hθ : NearFunctor p A θ)

include hθ

theorem dsub_le_centralizer : dsub A θ ≤ Subgroup.centralizer (A : Set G) :=
  dsub_le_centralizer_of_isFunctor hθ.isFunctor

theorem admits_dsub : Admits A (dsub A θ) :=
  admits_dsub_of_isFunctor hθ.isFunctor

theorem exists_mem_ne_one : ∃ a ∈ A, a ≠ 1 := by
  obtain ⟨⟨a, ha⟩, h⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hθ.ne_bot
  exact ⟨a, ha, fun h' => h (Subtype.ext h')⟩

theorem isSolvable_dsub : Group.IsSolvable (dsub A θ) := by
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hθ
  have h1 : dsub A θ ≤ θ a ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf (dsub_le_apply ha ha1) (dsub_le_centralizer hθ)
  have := (hθ.near a ha ha1).2
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)

variable [Finite G]

omit [Finite G] in
theorem apply_mem_assoc {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : θ a ∈ assoc p A θ :=
  hθ.isFunctor.apply_mem_signalizers ha ha1 (hθ.near a ha ha1)

theorem thetaOf_mem_assoc {B : Subgroup G} (hB : B ≤ A) (hB1 : B ≠ ⊥) :
    thetaOf θ B ∈ assoc p A θ := by
  obtain ⟨⟨b, hb⟩, h⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
  have hb1 : b ≠ 1 := fun h' => h (Subtype.ext h')
  exact hθ.isFunctor.thetaOf_mem_signalizers hB hB1
    (nearASolvable_of_le hθ.prime (hθ.near b (hB hb) hb1) (thetaOf_le_apply hb hb1)
      (hθ.isFunctor.normalizes_thetaOf hB))

theorem dsub_mem_assoc : dsub A θ ∈ assoc p A θ :=
  thetaOf_mem_assoc hθ le_rfl hθ.ne_bot

theorem dsub_mem_mtil : dsub A θ ∈ mtil p A θ :=
  ⟨dsub_mem_assoc hθ, le_rfl⟩

omit [Finite G] in
theorem apply_mem_mtil {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : θ a ∈ mtil p A θ :=
  ⟨apply_mem_assoc hθ ha ha1, dsub_le_apply ha ha1⟩

theorem thetaOf_mem_mtil {B : Subgroup G} (hB : B ≤ A) (hB1 : B ≠ ⊥) :
    thetaOf θ B ∈ mtil p A θ :=
  ⟨thetaOf_mem_assoc hθ hB hB1, thetaOf_anti hB⟩

omit [Finite G] in
theorem cenIn_eq_dsub {X : Subgroup G} (hX : X ∈ mtil p A θ) : cenIn X A = dsub A θ :=
  le_antisymm (cenIn_le_dsub hX.1) (le_inf hX.2 (dsub_le_centralizer hθ))

end Functor

end CFSG.SignalizerFunctorTheorem.McBride.Near
