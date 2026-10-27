module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightMod
public import CFSG.LocalAnalysis.WeakClosure81.W19EightAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_le_normalizer_centralizer {D : Type} [Group D] {S : Subgroup D} :
    Subgroup.normalizer (S : Set D) ≤
      Subgroup.normalizer ((Subgroup.centralizer (S : Set D) : Subgroup D) : Set D) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff] at ht ⊢
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hts : t⁻¹ * s * t ∈ S := by
      refine (ht (t⁻¹ * s * t)).2 ?_
      have : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
      rwa [this]
    have key := hc (t⁻¹ * s * t) hts
    calc s * (t * c * t⁻¹) = t * ((t⁻¹ * s * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * s * t)) * t⁻¹ := by rw [key]
      _ = (t * c * t⁻¹) * s := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hts : t * s * t⁻¹ ∈ S := (ht s).1 hs
    have key := hc (t * s * t⁻¹) hts
    calc s * c = t⁻¹ * (t * s * t⁻¹) * (t * c * t⁻¹) * t := by group
      _ = t⁻¹ * ((t * s * t⁻¹) * (t * c * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * c * t⁻¹) * (t * s * t⁻¹)) * t := by rw [key]
      _ = c * s := by group

namespace ModData

variable {H E F : Subgroup G} (M : ModData H E F)

theorem card_img {S : Subgroup G} (hSH : S ≤ H) :
    Nat.card (M.img S) = ((S ⊓ centralizerQuot H E F).subgroupOf S).index := by
  let f : ↥S →* LGL 2 M.W := M.ρ.comp (Subgroup.inclusion hSH)
  have hrange : f.range = M.img S := by
    change (M.ρ.comp (Subgroup.inclusion hSH)).range = M.img S
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : f.ker = (S ⊓ centralizerQuot H E F).subgroupOf S := by
    change (M.ρ.comp (Subgroup.inclusion hSH)).ker =
      (S ⊓ centralizerQuot H E F).subgroupOf S
    ext x
    rw [MonoidHom.mem_ker]
    change M.ρ (Subgroup.inclusion hSH x) = 1 ↔
      x ∈ (S ⊓ centralizerQuot H E F).subgroupOf S
    rw [M.ρ_eq_one, Subgroup.coe_inclusion, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [← hrange, ← Subgroup.index_ker f, hker]

private theorem img_sup_pCoreOf_eq {X : Subgroup G} (hXH : X ≤ H) :
    M.img (X ⊔ pCoreOf 2 H) = M.img X := by
  have hpbot : ((pCoreOf 2 H).subgroupOf H).map M.ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro n hn
    rw [MonoidHom.mem_ker]
    exact M.ρ_pCoreOf n (Subgroup.mem_subgroupOf.mp hn)
  change ((X ⊔ pCoreOf 2 H).subgroupOf H).map M.ρ = (X.subgroupOf H).map M.ρ
  rw [Subgroup.subgroupOf_sup hXH (CFSG.LieType.BorelTits.pCoreOf_le 2 H),
    Subgroup.map_sup, hpbot]
  simp

theorem range_le_normalizer_img {X : Subgroup G} (hXH : X ≤ H)
    (hXn : H ≤ normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G)) :
    M.ρ.range ≤ normalizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
  intro r hr
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hr
  have conj : ∀ (k : ↥H) {s : LGL 2 M.W},
      s ∈ M.img X → M.ρ k * s * (M.ρ k)⁻¹ ∈ M.img X := by
    intro k s hs
    obtain ⟨x, hxX, rfl⟩ := M.mem_img.1 hs
    have hmem : ((k * x * k⁻¹ : ↥H) : G) ∈ X ⊔ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.1 (hXn k.2) (x : G)).1 (Subgroup.mem_sup_left hxX)
    have hmem' : M.ρ (k * x * k⁻¹) ∈ M.img X := by
      rw [← img_sup_pCoreOf_eq M hXH]
      exact M.mem_img.2 ⟨k * x * k⁻¹, hmem, rfl⟩
    rw [show M.ρ k * M.ρ x * (M.ρ k)⁻¹ = M.ρ (k * x * k⁻¹) by
      simp only [← map_mul, ← map_inv]]
    exact hmem'
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => conj h hs, fun hs => ?_⟩
  have h2 := conj h⁻¹ hs
  rw [map_inv] at h2
  have heq : (M.ρ h)⁻¹ * (M.ρ h * s * (M.ρ h)⁻¹) * ((M.ρ h)⁻¹)⁻¹ = s := by group
  rwa [heq] at h2

theorem odd_card_img {X : Subgroup G} (hX : Odd (Nat.card X)) : Odd (Nat.card (M.img X)) := by
  have hcard : Nat.card (X.subgroupOf H) = Nat.card ↥(X ⊓ H) := by
    have hEq : X.subgroupOf H = (X ⊓ H).subgroupOf H := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine Odd.of_dvd_nat hX ?_
  calc Nat.card (M.img X) ∣ Nat.card (X.subgroupOf H) :=
        Subgroup.card_map_dvd (X.subgroupOf H) M.ρ
    _ = Nat.card ↥(X ⊓ H) := hcard
    _ ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left

theorem img_inf_centralizer_eq_bot {X T : Subgroup G} (hFE : F < E) (hTH : T ≤ H)
    (hXH : X ≤ H) (hXT : X ⊔ T = H) (hT : IsPGroup 2 T)
    (hn : M.ρ.range ≤ normalizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) :
    M.img T ⊓ centralizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥ := by
  let C : Subgroup (LGL 2 M.W) :=
    centralizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))
  let N : Subgroup (LGL 2 M.W) := M.img T ⊓ C
  change N = ⊥
  haveI : Nontrivial M.W := M.nontrivial hFE
  have hirr : ∀ U : Submodule (ZMod 2) M.W,
      (∀ k ∈ M.ρ.range, ∀ u ∈ U, k u ∈ U) → U = ⊥ ∨ U = ⊤ := fun U hU =>
    M.irreducible U fun h u hu =>
      hU (M.ρ h) (MonoidHom.mem_range.mpr ⟨h, rfl⟩) u hu
  have hK : M.ρ.range = M.img X ⊔ M.img T := by
    have htop : (⊤ : Subgroup ↥H) = (X ⊔ T).subgroupOf H := by
      rw [hXT, Subgroup.subgroupOf_self]
    rw [MonoidHom.range_eq_map, htop, Subgroup.subgroupOf_sup hXH hTH, Subgroup.map_sup]
    rfl
  have hImgT : IsPGroup 2 (M.img T) := (hT.comap_subtype (K := H)).map M.ρ
  have hN : IsPGroup 2 N := hImgT.to_le inf_le_left
  have hnorm : M.ρ.range ≤ normalizer (N : Set (LGL 2 M.W)) := by
    rw [hK]
    refine sup_le ?_ ?_
    · exact (Subgroup.le_centralizer_iff.2 inf_le_right).trans
        (Subgroup.centralizer_le_normalizer (N : Set (LGL 2 M.W)))
    · refine (le_inf Subgroup.le_normalizer ?_).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := M.img T) (K := C))
      exact (Subgroup.map_le_range M.ρ (T.subgroupOf H)).trans
        (hn.trans normalizer_le_normalizer_centralizer)
  exact eq_bot_of_normal_isPGroup_irreducible (K := M.ρ.range) hirr
    (inf_le_left.trans (Subgroup.map_le_range M.ρ (T.subgroupOf H))) hnorm hN

theorem img_commutator_ne_bot {X A : Subgroup G} (hXH : X ≤ H) (hAH : A ≤ H)
    (hcomm : ¬ ⁅X, A⁆ ≤ centralizerQuot H E F) : ⁅M.img X, M.img A⁆ ≠ ⊥ := by
  intro hbot
  apply hcomm
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hxH : x ∈ H := hXH hx
  have haH : a ∈ H := hAH ha
  have hmemX : M.ρ ⟨x, hxH⟩ ∈ M.img X := M.mem_img.2 ⟨⟨x, hxH⟩, hx, rfl⟩
  have hmemA : M.ρ ⟨a, haH⟩ ∈ M.img A := M.mem_img.2 ⟨⟨a, haH⟩, ha, rfl⟩
  have h1 : ⁅M.ρ ⟨x, hxH⟩, M.ρ ⟨a, haH⟩⁆ = 1 := by
    have hmem := Subgroup.commutator_mem_commutator hmemX hmemA
    rw [hbot] at hmem
    simpa using hmem
  have h2 : M.ρ ⁅(⟨x, hxH⟩ : ↥H), ⟨a, haH⟩⁆ = 1 := by
    rw [map_commutatorElement, h1]
  exact (M.ρ_eq_one (⁅(⟨x, hxH⟩ : ↥H), ⟨a, haH⟩⁆)).1 h2

end ModData

end CFSG.LocalAnalysis.WeakClosure81

end
