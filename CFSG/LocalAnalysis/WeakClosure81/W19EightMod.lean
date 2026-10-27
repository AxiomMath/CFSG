module

public import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure ModData (H E F : Subgroup G) where
  W : Type
  [addCommGroup : AddCommGroup W]
  [module : Module (ZMod 2) W]
  [finite : Finite W]
  ρ : ↥H →* LGL 2 W
  ι : G → W
  ι_mul : ∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e'
  ι_surj : ∀ w : W, ∃ e ∈ E, ι e = w
  ι_eq_zero : ∀ e ∈ E, (ι e = 0 ↔ e ∈ F)
  ρ_ι : ∀ h : ↥H, ∀ e ∈ E, ρ h (ι e) = ι ((h : G) * e * (h : G)⁻¹)
  irreducible : ∀ U : Submodule (ZMod 2) W, (∀ h : ↥H, ∀ u ∈ U, ρ h u ∈ U) → U = ⊥ ∨ U = ⊤
  ρ_eq_one : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ centralizerQuot H E F
  ρ_pCoreOf : ∀ n : ↥H, (n : G) ∈ pCoreOf 2 H → ρ n = 1

attribute [instance] ModData.addCommGroup ModData.module ModData.finite

theorem commutator_mem_of_le_normalizer {H E : Subgroup G} (hEn : H ≤ normalizer (E : Set G))
    {h : G} (hh : h ∈ H) {e : G} (he : e ∈ E) : ⁅h, e⁆ ∈ E := by
  rw [commutatorElement_def]
  exact E.mul_mem ((Subgroup.mem_normalizer_iff.1 (hEn hh) e).1 he) (E.inv_mem he)

namespace ModData

variable {H E F : Subgroup G} (M : ModData H E F)

theorem nontrivial (hFE : F < E) : Nontrivial M.W := by
  obtain ⟨e, he, heF⟩ := SetLike.exists_of_lt hFE
  exact ⟨⟨M.ι e, 0, fun h => heF ((M.ι_eq_zero e he).1 h)⟩⟩

theorem ρ_sub_ι (hEn : H ≤ normalizer (E : Set G)) (h : ↥H) {e : G} (he : e ∈ E) :
    M.ρ h (M.ι e) - M.ι e = M.ι ⁅(h : G), e⁆ := by
  have hmul : (h : G) * e * (h : G)⁻¹ = ⁅(h : G), e⁆ * e := by
    rw [commutatorElement_def]
    group
  rw [M.ρ_ι h e he, hmul, M.ι_mul _ (commutator_mem_of_le_normalizer hEn h.2 he) e he]
  abel

theorem ρ_ι_eq_iff (hEn : H ≤ normalizer (E : Set G)) (h : ↥H) {e : G} (he : e ∈ E) :
    M.ρ h (M.ι e) = M.ι e ↔ ⁅(h : G), e⁆ ∈ F := by
  rw [← sub_eq_zero, M.ρ_sub_ι hEn h he,
    M.ι_eq_zero _ (commutator_mem_of_le_normalizer hEn h.2 he)]

@[expose] def img (S : Subgroup G) : Subgroup (LGL 2 M.W) :=
  (S.subgroupOf H).map M.ρ

theorem mem_img {S : Subgroup G} {r : LGL 2 M.W} :
    r ∈ M.img S ↔ ∃ h : ↥H, (h : G) ∈ S ∧ M.ρ h = r := by
  unfold img
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩, fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩⟩

theorem exists_hyperplane_of_two_orbit {A : Subgroup G} (hAH : A ≤ H) (hA : IsElemAbelian 2 A)
    {a₁ : ↥H} (ha₁ : (a₁ : G) ∈ A) {w : M.W} (hmv : M.ρ a₁ w ≠ w)
    (horb : ∀ b : ↥H, (b : G) ∈ A → M.ρ b w = w ∨ M.ρ b w = M.ρ a₁ w) :
    ∃ B : Subgroup G, B ≤ A ∧ (B.subgroupOf A).index = 2 ∧
      ∀ b : ↥H, (b : G) ∈ B → M.ρ b w = w := by
  let B : Subgroup G :=
    { carrier := {b | ∃ hb : b ∈ H, b ∈ A ∧ M.ρ ⟨b, hb⟩ w = w}
      one_mem' := ⟨H.one_mem, A.one_mem, by
        change M.ρ 1 w = w
        rw [map_one]
        rfl⟩
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨hxH, hxA, hxw⟩ := hx
        obtain ⟨hyH, hyA, hyw⟩ := hy
        refine ⟨H.mul_mem hxH hyH, A.mul_mem hxA hyA, ?_⟩
        change M.ρ (⟨x, hxH⟩ * ⟨y, hyH⟩) w = w
        rw [map_mul, LinearEquiv.mul_apply, hyw, hxw]
      inv_mem' := fun {x} hx => by
        obtain ⟨hxH, hxA, hxw⟩ := hx
        refine ⟨H.inv_mem hxH, A.inv_mem hxA, ?_⟩
        change M.ρ (⟨x, hxH⟩ : ↥H)⁻¹ w = w
        rw [map_inv]
        calc (M.ρ ⟨x, hxH⟩)⁻¹ w = (M.ρ ⟨x, hxH⟩)⁻¹ (M.ρ ⟨x, hxH⟩ w) := by rw [hxw]
          _ = w := LinearEquiv.symm_apply_apply _ _ }
  have hBmem : ∀ b : ↥H, (b : G) ∈ A → ((b : G) ∈ B ↔ M.ρ b w = w) := fun b hbA =>
    ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨b.2, hbA, h⟩⟩
  have hinv : ∀ g : LGL 2 M.W, g w = w → g⁻¹ w = w := fun g hg =>
    calc g⁻¹ w = g⁻¹ (g w) := by rw [hg]
      _ = w := LinearEquiv.symm_apply_apply g w
  refine ⟨B, fun b hb => ?_, ?_, fun b hb => ?_⟩
  · obtain ⟨_, hbA, _⟩ := hb
    exact hbA
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a₁, ha₁⟩, fun ⟨b, hbA⟩ => ?_⟩
    let β : ↥H := ⟨b, hAH hbA⟩
    have hβA : (β : G) ∈ A := hbA
    have hbB : (⟨b, hbA⟩ : ↥A) ∈ B.subgroupOf A ↔ M.ρ β w = w := hBmem β hβA
    have hbaB : (⟨b, hbA⟩ : ↥A) * ⟨a₁, ha₁⟩ ∈ B.subgroupOf A ↔ M.ρ (β * a₁) w = w :=
      hBmem (β * a₁) (A.mul_mem hbA ha₁)
    have hββ : β * β = 1 := Subtype.ext (hA.mul_self_eq_one hbA)
    rcases horb β hβA with h | h
    · right
      refine ⟨hbB.2 h, fun hba => hmv ?_⟩
      have h2 : M.ρ β (M.ρ a₁ w) = w := by
        have := hbaB.1 hba
        rwa [map_mul, LinearEquiv.mul_apply] at this
      calc M.ρ a₁ w = (M.ρ β)⁻¹ (M.ρ β (M.ρ a₁ w)) :=
          (LinearEquiv.symm_apply_apply _ _).symm
        _ = (M.ρ β)⁻¹ w := by rw [h2]
        _ = w := hinv _ h
    · left
      refine ⟨hbaB.2 ?_, fun hb' => hmv ?_⟩
      · rw [map_mul, LinearEquiv.mul_apply, ← h, ← LinearEquiv.mul_apply, ← map_mul, hββ, map_one]
        rfl
      · have := hbB.1 hb'
        rw [h] at this
        exact this
  · have hb' := hb
    obtain ⟨_, hbA, _⟩ := hb'
    exact (hBmem b hbA).1 hb

end ModData

end CFSG.LocalAnalysis.WeakClosure81

end
