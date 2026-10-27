module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16Transport
public import CFSG.RankThree.PartTwo.Sec21.Hering233iExcModel

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG

variable {G : Type} [Group G] {K : Type} [Group K] {I : Subgroup G}

theorem map_top_equiv (Φ : I ≃* K) : (⊤ : Subgroup I).map Φ.toMonoidHom = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr Φ.surjective

@[expose] def pull (Φ : I ≃* K) (S : Subgroup K) : Subgroup G :=
  (S.map Φ.symm.toMonoidHom).map I.subtype

theorem mem_pull {Φ : I ≃* K} {S : Subgroup K} {x : G} :
    x ∈ pull Φ S ↔ ∃ hx : x ∈ I, Φ ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨(Φ.symm k).2, ?_⟩
    simpa using hk
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, ⟨Φ ⟨x, hx⟩, h, by simp⟩, rfl⟩

theorem pull_le (Φ : I ≃* K) (S : Subgroup K) : pull Φ S ≤ I := Subgroup.map_subtype_le _

theorem pull_mono {Φ : I ≃* K} {S T : Subgroup K} (h : S ≤ T) :
    pull Φ S ≤ pull Φ T := fun x hx => by
  obtain ⟨hxI, hS⟩ := mem_pull.mp hx
  exact mem_pull.mpr ⟨hxI, h hS⟩

theorem pull_map (Φ : I ≃* K) (S : Subgroup K) :
    ((pull Φ S).subgroupOf I).map Φ.toMonoidHom = S := by
  ext k
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyI, hS⟩ := mem_pull.mp (Subgroup.mem_subgroupOf.mp hy)
    exact hS
  · intro hk
    refine ⟨Φ.symm k, Subgroup.mem_subgroupOf.mpr (mem_pull.mpr ⟨(Φ.symm k).2, ?_⟩), by simp⟩
    simpa using hk

theorem eq_pull_of_map {Φ : I ≃* K} {T : Subgroup G} (hTI : T ≤ I) {S : Subgroup K}
    (h : (T.subgroupOf I).map Φ.toMonoidHom = S) : T = pull Φ S := by
  ext x
  rw [mem_pull]
  constructor
  · intro hx
    refine ⟨hTI hx, ?_⟩
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨⟨x, hTI hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  · rintro ⟨hxI, hS⟩
    rw [← h] at hS
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hS
    have : y = ⟨x, hxI⟩ := Φ.injective hyx
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy

@[expose] def gOf (Φ : I ≃* K) (m : K) : G := ((Φ.symm m : I) : G)

theorem gOf_mem (Φ : I ≃* K) (m : K) : gOf Φ m ∈ I := (Φ.symm m).2

theorem Φ_gOf (Φ : I ≃* K) (m : K) : Φ ⟨gOf Φ m, gOf_mem Φ m⟩ = m := by
  have : (⟨gOf Φ m, gOf_mem Φ m⟩ : I) = Φ.symm m := rfl
  rw [this]
  simp

theorem gOf_Φ (Φ : I ≃* K) {x : G} (hx : x ∈ I) : gOf Φ (Φ ⟨x, hx⟩) = x := by
  simp [gOf]

theorem gOf_injective (Φ : I ≃* K) : Function.Injective (gOf Φ : K → G) := by
  intro m n h
  have h1 : Φ ⟨gOf Φ m, gOf_mem Φ m⟩ = Φ ⟨gOf Φ n, gOf_mem Φ n⟩ := by
    congr 1
    exact Subtype.ext h
  rwa [Φ_gOf, Φ_gOf] at h1

theorem gOf_mul (Φ : I ≃* K) (m n : K) : gOf Φ (m * n) = gOf Φ m * gOf Φ n := by
  simp [gOf]

theorem gOf_pow (Φ : I ≃* K) (m : K) (k : ℕ) : gOf Φ (m ^ k) = gOf Φ m ^ k := by
  simp [gOf]

theorem gOf_inv (Φ : I ≃* K) (m : K) : gOf Φ m⁻¹ = (gOf Φ m)⁻¹ := by
  simp [gOf]

theorem gOf_one (Φ : I ≃* K) : gOf Φ 1 = 1 := by
  simp [gOf]

theorem gOf_eq_one_iff (Φ : I ≃* K) {m : K} : gOf Φ m = 1 ↔ m = 1 := by
  rw [← gOf_one Φ]
  exact (gOf_injective Φ).eq_iff

theorem zpowers_eq_pull (Φ : I ≃* K) {r : G} (hr : r ∈ I) :
    Subgroup.zpowers r = pull Φ (Subgroup.zpowers (Φ ⟨r, hr⟩)) :=
  eq_pull_of_map (Subgroup.zpowers_le.mpr hr) (map_subgroupOf_zpowers hr Φ)

theorem layerCent_eq_pull (Φ : I ≃* K) {r : G} (hr : r ∈ I) :
    layerCent I (Subgroup.zpowers r) =
      pull Φ (layerCent (⊤ : Subgroup K) (Subgroup.zpowers (Φ ⟨r, hr⟩))) := by
  have hBI : (Subgroup.zpowers r : Subgroup G) ≤ I := Subgroup.zpowers_le.mpr hr
  have hmap : (layerCent (⊤ : Subgroup I) ((Subgroup.zpowers r).subgroupOf I)).map
      Φ.toMonoidHom = layerCent (⊤ : Subgroup K) (Subgroup.zpowers (Φ ⟨r, hr⟩)) := by
    rw [map_layerCent Φ, map_top_equiv, map_subgroupOf_zpowers hr Φ]
  have hid : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id I := by
    ext x
    simp
  have hL : ∀ L : Subgroup I, (L.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = L := fun L => by
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  rw [← map_layerCent_subgroupOf hBI, pull, ← hmap, hL]

@[expose] def UniqueSixtyAt {K : Type} [Group K] (c : K) : Prop :=
  ∃ Y : Subgroup (Subgroup.centralizer ({c} : Set K)), CFSG.IsComponent Y ∧
    (∀ Y', CFSG.IsComponent Y' → Y' = Y) ∧ Nat.card Y = 60

theorem uniqueSixtyAt_of_data (Φ : I ≃* K) {r : G} (hr : r ∈ I)
    (X : Subgroup (I ⊓ Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) : Set G) :
      Subgroup G))
    (hX : CFSG.IsComponent X) (huniq : ∀ X', CFSG.IsComponent X' → X' = X)
    (h60 : Nat.card X = 60) : UniqueSixtyAt (Φ ⟨r, hr⟩) := by
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hΦH := map_inf_centralizer_zpowers Φ hr
  set θ := thetaK hHI Φ hΦH with hθ
  have hinj : Function.Injective θ.toMonoidHom := θ.injective
  refine ⟨X.map θ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv θ hX, fun Y' hY' => ?_, ?_⟩
  · have h1 : CFSG.IsComponent (Y'.map θ.symm.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv θ.symm hY'
    have h2 := huniq _ h1
    have h3 := CFSG.LocalCores.map_map_symm θ.symm Y'
    rw [MulEquiv.symm_symm, h2] at h3
    exact h3.symm
  · rw [Subgroup.card_map_of_injective hinj]
    exact h60

theorem excFree_of_model (Φ : I ≃* K) {r : G} (hr : r ∈ I)
    (h : ¬ UniqueSixtyAt (Φ ⟨r, hr⟩)) : ExcFree I (Subgroup.zpowers r) :=
  fun X hX hu => h (uniqueSixtyAt_of_data Φ hr X hX hu.1 hu.2)

theorem ncard_invSet_le [Finite K] (Φ : I ≃* K) {Y : Subgroup G} (hYI : Y ≤ I) {S : Subgroup K}
    (hS : (Y.subgroupOf I).map Φ.toMonoidHom = S) {b : G} (hb : b ∈ I) :
    (invSet Y b).ncard ≤ (invSet S (Φ ⟨b, hb⟩)).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (fun y => if h : y ∈ I then Φ ⟨y, h⟩ else 1) ?_ ?_
    (Set.toFinite _)
  · intro y hy
    obtain ⟨hyY, hy2, hyb⟩ := hy
    have hyI : y ∈ I := hYI hyY
    simp only [dif_pos hyI]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hS]
      exact Subgroup.mem_map.mpr ⟨⟨y, hyI⟩, Subgroup.mem_subgroupOf.mpr hyY, rfl⟩
    · rw [← map_mul, show (⟨y, hyI⟩ : I) * ⟨y, hyI⟩ = 1 from Subtype.ext hy2, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul,
        show (⟨y, hyI⟩ : I) * ⟨b, hb⟩ * (⟨y, hyI⟩ : I)⁻¹ = (⟨b, hb⟩ : I)⁻¹ from Subtype.ext hyb,
        map_inv]
  · intro y₁ hy₁ y₂ hy₂ h12
    have hI₁ := hYI hy₁.1
    have hI₂ := hYI hy₂.1
    simp only [dif_pos hI₁, dif_pos hI₂] at h12
    exact congrArg Subtype.val (Φ.injective h12)

end CFSG.RankThree.PartTwo.Sec21.Hering233i
