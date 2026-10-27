module

public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

variable {Γ : Type} [Group Γ]

noncomputable abbrev starMap (M H : Subgroup Γ) : ↥H →* E2.StarQuot M H :=
  QuotientGroup.mk' ((kerIn M H).subgroupOf H)

theorem star_def (M H X : Subgroup Γ) :
    E2.star M H X = (X.subgroupOf H).map (starMap M H) := rfl

theorem starMap_surjective (M H : Subgroup Γ) : Function.Surjective (starMap M H) :=
  QuotientGroup.mk'_surjective _

theorem ker_starMap (M H : Subgroup Γ) : (starMap M H).ker = (kerIn M H).subgroupOf H :=
  QuotientGroup.ker_mk' _

theorem star_top (M H : Subgroup Γ) : E2.star M H H = ⊤ := by
  rw [star_def, Subgroup.subgroupOf_self, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr (starMap_surjective M H)]

theorem ker_starMap_le_subgroupOf (M H : Subgroup Γ) : (starMap M H).ker ≤ M.subgroupOf H := by
  rw [ker_starMap]
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (kerIn_le (Subgroup.mem_subgroupOf.mp hx))

theorem kerIn_star (M H : Subgroup Γ) : kerIn (E2.star M H M) ⊤ = ⊥ := by
  rw [star_def, kerIn_map_top (starMap_surjective M H) (ker_starMap_le_subgroupOf M H),
    kerIn_subgroupOf_top, Subgroup.map_eq_bot_iff, ker_starMap]

section Finite

variable [Finite Γ] {H T M : Subgroup Γ}

theorem finite_starQuot (M H : Subgroup Γ) : Finite (E2.StarQuot M H) :=
  Finite.of_surjective _ (starMap_surjective M H)

theorem minParabolic_star (h : MinParabolic H T M) :
    MinParabolic (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H T) (E2.star M H M) :=
  h.subgroupOf.map_of_surjective (starMap_surjective M H) (ker_starMap_le_subgroupOf M H)

theorem isSolvable_ker_starMap (h : MinParabolic H T M) : Group.IsSolvable (starMap M H).ker := by
  have hs := h.subgroupOf.isSolvable_kerIn
  rw [kerIn_subgroupOf_top, ← ker_starMap] at hs
  exact hs

theorem not_isSolvable_star (h : MinParabolic H T M) (hns : ¬ Group.IsSolvable ↥H) :
    ¬ Group.IsSolvable (E2.StarQuot M H) := by
  intro hs
  have := isSolvable_ker_starMap h
  exact hns (Group.isSolvable_of_ker_le_range (starMap M H).ker.subtype (starMap M H)
    (by rw [Subgroup.range_subtype]))

end Finite

section Sylow

theorem isSylowTwoOf_inf_of_subnormal [Finite Γ] {H T K : Subgroup Γ} (hT : IsSylowTwoOf T H)
    (hK : CFSG.Open.IsSubnormal K H) : IsSylowTwoOf (T ⊓ K) K := by
  induction hK with
  | refl H => rwa [inf_eq_left.mpr hT.1]
  | @step K₁ M₁ H₁ hKM hn _ ih =>
    have h1 := isSylowTwoOf_inf_normal (ih hT) hKM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hn)
    rwa [inf_assoc, inf_eq_right.mpr hKM] at h1

theorem isSylowTwoOf_map_hom {Q : Type*} [Group Q] {K S : Subgroup Γ}
    (hS : IsSylowTwoOf S K) (ρ : ↥K →* Q) : IsSylowTwoOf ((S.subgroupOf K).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf K) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf K).map ρ).subgroupOf ρ.range =
      (S.subgroupOf K).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem eq_of_isSylowTwoOf_le [Finite Γ] {K S P : Subgroup Γ} (hS : IsSylowTwoOf S K)
    (hP : IsPGroup 2 P) (hSP : S ≤ P) (hPK : P ≤ K) : P = S := by
  have hS' := toSylow2_coe hS
  have hP' : IsPGroup 2 (P.subgroupOf K) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  have hle : ((toSylow2 hS : Sylow 2 ↥K) : Subgroup ↥K) ≤ P.subgroupOf K := by
    rw [hS']
    exact Subgroup.subgroupOf_mono K hSP
  have heq := (toSylow2 hS).is_maximal' hP' hle
  rw [hS'] at heq
  have := congrArg (Subgroup.map K.subtype) heq
  rwa [Subgroup.map_subgroupOf_eq_of_le hPK, Subgroup.map_subgroupOf_eq_of_le hS.1] at this

end Sylow

section Inter

variable {H T M : Subgroup Γ}

theorem star_inf_M (K : Subgroup Γ) :
    E2.star M H (M ⊓ K) = E2.star M H M ⊓ E2.star M H K := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left))
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_right))
  · rintro x ⟨⟨m, hm, rfl⟩, ⟨k, hk, hkm⟩⟩
    refine ⟨k, ⟨?_, hk⟩, hkm⟩
    have hker : m⁻¹ * k ∈ (starMap M H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkm, inv_mul_cancel]
    have h1 := ker_starMap_le_subgroupOf M H hker
    have h2 : m * (m⁻¹ * k) ∈ M.subgroupOf H := Subgroup.mul_mem _ hm h1
    rwa [mul_inv_cancel_left] at h2

theorem star_inf_T [Finite Γ] {K : Subgroup Γ} (hT : IsSylowTwoOf T H)
    (hK : CFSG.Open.IsSubnormal K H) (hKH : K ≤ H) :
    E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K := by
  have hS := isSylowTwoOf_inf_of_subnormal hT hK
  set ρ : ↥K →* E2.StarQuot M H := (starMap M H).comp (Subgroup.inclusion hKH) with hρ
  have hrange : ρ.range = E2.star M H K := by
    rw [hρ, MonoidHom.range_comp, star_def]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have himage : ((T ⊓ K).subgroupOf K).map ρ = E2.star M H (T ⊓ K) := by
    rw [hρ, star_def, ← Subgroup.map_map]
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx, rfl⟩
  have hSyl := isSylowTwoOf_map_hom hS ρ
  rw [himage, hrange] at hSyl
  have hle : E2.star M H (T ⊓ K) ≤ E2.star M H T ⊓ E2.star M H K :=
    le_inf (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left))
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_right))
  have : Finite (E2.StarQuot M H) := finite_starQuot M H
  have hT2 : IsPGroup 2 (E2.star M H T) := by
    have hT2' : IsPGroup 2 (T.subgroupOf H) :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact hT2'.map _
  exact (eq_of_isSylowTwoOf_le hSyl (hT2.to_le inf_le_left) hle inf_le_right).symm

end Inter

end E2P

end CFSG.Quasithin
