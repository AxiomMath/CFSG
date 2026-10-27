module

public import CFSG.Quasithin.EmptyFaithful.SBd8Mod

public section

namespace CFSG.Quasithin.S151S8C2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B6

section Abstract

variable {X Y : Type} [Group X] [Group Y] {φ : X →* Y}

theorem minParabolic_comap_of_surjective [Finite Y] (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 ↥φ.ker) {T M : Subgroup Y} (h : MinParabolic (⊤ : Subgroup Y) T M) :
    MinParabolic (⊤ : Subgroup X) (T.comap φ) (M.comap φ) := by
  refine ⟨⟨le_top, ?_, ?_⟩, ?_, ?_⟩
  · intro x
    obtain ⟨m, hm⟩ := h.isSylow.2.1 ⟨φ (x : X), x.2⟩
    have hm' : φ (x : X) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hk : (x : X) ^ 2 ^ m ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hm'
    obtain ⟨n, hn⟩ := hker ⟨(x : X) ^ 2 ^ m, hk⟩
    have hn' : ((x : X) ^ 2 ^ m) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    exact ⟨m + n, Subtype.ext (by simpa [pow_add, pow_mul] using hn')⟩
  · have e1 : ((T.comap φ).subgroupOf ⊤).index = (T.comap φ).index :=
      Subgroup.relIndex_top_right _
    have e2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rw [e1, Subgroup.index_comap_of_surjective T hφ]
    have := h.isSylow.2.2
    rwa [e2] at this
  · intro hnorm
    apply h.not_normal
    have hN : (T.comap φ).Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
    have hTn : T.Normal := by
      have := hN.map φ hφ
      rwa [Subgroup.map_comap_eq_self_of_surjective hφ] at this
    exact (Subgroup.normalizer_eq_top_iff.mpr hTn).ge
  · rw [isUniqueMaxOver_iff]
    refine ⟨isMaxSubgroupIn_top_iff.mpr (Subgroup.isCoatom_comap_of_surjective hφ
      (isMaxSubgroupIn_top_iff.mp h.maximal)), Subgroup.comap_mono h.le, fun N hN hTN => ?_⟩
    have hNc := isMaxSubgroupIn_top_iff.mp hN
    have hkerN : φ.ker ≤ N := by
      refine le_trans ?_ hTN
      intro x hx
      exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact T.one_mem)
    have hcN : IsCoatom (N.map φ) := isCoatom_map_of_surjective hφ hkerN hNc
    have hTle : T ≤ N.map φ := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hφ T]
      exact Subgroup.map_mono hTN
    have := h.eq_of_maximal (isMaxSubgroupIn_top_iff.mpr hcN) hTle
    rw [← comap_map_eq_of_ker_le hkerN, this]

theorem exists_minParabolic_of_isMinParabolicOf [Finite Y]
    (h : IsMinParabolicOf (⊤ : Subgroup Y) ⊤) : ∃ T M : Subgroup Y, MinParabolic (⊤ : Subgroup Y) T M := by
  obtain ⟨T, hT, ⟨⟨hHH, hlt, hcard⟩, hnn⟩⟩ := h
  obtain ⟨M, hM⟩ := Set.ncard_eq_one.mp hcard
  exact ⟨T, M, minParabolic_iff.mpr ⟨⟨T, hT, ⟨hHH, hlt, hcard⟩, hnn⟩, hT, hM⟩⟩

end Abstract

section Ambient

variable {G Gb : Type} [Group G] [Group Gb] [Finite G] [Finite Gb] (π : G →* Gb)

omit [Finite G] [Finite Gb] in
theorem isMinParabolicOf_self_iff (H : Subgroup G) :
    IsMinParabolicOf H H ↔ IsMinParabolicOf (⊤ : Subgroup H) ⊤ := by
  have := SBd8.isMinParabolicOf_map_iff (H := H) (⊤ : Subgroup H)
  rwa [Subgroup.map_top, Subgroup.range_subtype] at this

@[expose] def restrictTo (H : Subgroup G) : ↥H →* ↥(H.map π) :=
  (π.comp H.subtype).codRestrict (H.map π) fun h => ⟨h, h.2, rfl⟩

omit [Finite G] [Finite Gb] in
theorem restrictTo_surjective (H : Subgroup G) : Function.Surjective (restrictTo π H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] [Finite Gb] in
theorem isPGroup_ker_restrictTo (hK : IsPGroup 2 ↥π.ker) (H : Subgroup G) :
    IsPGroup 2 ↥(restrictTo π H).ker := by
  rintro ⟨⟨x, hxH⟩, hx⟩
  have hxk : x ∈ π.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  obtain ⟨n, hn⟩ := hK ⟨x, hxk⟩
  exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩

theorem isMinParabolicOf_of_map (hK : IsPGroup 2 ↥π.ker) {H : Subgroup G}
    (h : IsMinParabolicOf (H.map π) (H.map π)) : IsMinParabolicOf H H := by
  have h1 : IsMinParabolicOf (⊤ : Subgroup ↥(H.map π)) ⊤ := (isMinParabolicOf_self_iff _).mp h
  obtain ⟨T, M, hTM⟩ := exists_minParabolic_of_isMinParabolicOf h1
  have h2 := minParabolic_comap_of_surjective (restrictTo_surjective π H)
    (isPGroup_ker_restrictTo π hK H) hTM
  exact (isMinParabolicOf_self_iff H).mpr (minParabolic_iff.mp h2).1

end Ambient

end CFSG.Quasithin.S151S8C2
