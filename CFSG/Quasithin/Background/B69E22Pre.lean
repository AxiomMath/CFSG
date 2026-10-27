module

public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace B69

variable {H₀ Y : Type*} [Group H₀] [Finite H₀] [Group Y] [Finite Y]

omit [Finite Y] in
theorem isSylowTwoOf_map_of_map_eq_top {φ : H₀ →* Y} {H₁ T : Subgroup H₀} (hH : H₁.map φ = ⊤)
    (hT : IsSylowTwoOf T H₁) : IsSylowTwoOf (T.map φ) ⊤ := by
  have hsurj : Function.Surjective (φ.comp H₁.subtype) := by
    intro y
    have : y ∈ H₁.map φ := by rw [hH]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hT' : IsSylowTwoOf (T.subgroupOf H₁) (⊤ : Subgroup ↥H₁) := by
    refine ⟨le_top, hT.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hT.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT.1).injective, ?_⟩
    have e : ((T.subgroupOf H₁).subgroupOf ⊤).index = (T.subgroupOf H₁).index :=
      Subgroup.relIndex_top_right (T.subgroupOf H₁)
    rw [e]
    exact hT.2.2
  have := isSylowTwoOf_map_top (φ := φ.comp H₁.subtype) hsurj hT'
  have e2 : (T.subgroupOf H₁).map (φ.comp H₁.subtype) = T.map φ := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hT.1]
  rwa [e2] at this

theorem exists_minParabolic_preimage (φ : H₀ →* Y) (hφ : Function.Surjective φ) {S M : Subgroup Y}
    (h : MinParabolic (⊤ : Subgroup Y) S M) :
    ∃ H T M' : Subgroup H₀, MinParabolic H T M' ∧ H.map φ = ⊤ ∧ T.map φ = S ∧ M'.map φ = M ∧
      φ.ker ⊓ H ≤ M' := by
  classical
  let 𝒮 : Set (Subgroup H₀) := {H' | H'.map φ = ⊤}
  have h𝒮 : (⊤ : Subgroup H₀) ∈ 𝒮 := by
    show (⊤ : Subgroup H₀).map φ = ⊤
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hφ]
  obtain ⟨H, hH, hmin⟩ := Set.exists_min_image 𝒮 (fun H' => Nat.card H') (Set.toFinite 𝒮) ⟨⊤, h𝒮⟩
  have hHmap : H.map φ = ⊤ := hH
  have hminle : ∀ H' : Subgroup H₀, H'.map φ = ⊤ → H' ≤ H → H' = H := fun H' hH' hle =>
    Subgroup.eq_of_le_of_card_ge hle (hmin H' hH')
  have hsurjH : ∀ y : Y, ∃ x ∈ H, φ x = y := by
    intro y
    have : y ∈ H.map φ := by rw [hHmap]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, hx, rfl⟩
  obtain ⟨T₀, hT₀, -⟩ := exists_isSylowTwoOf_ge (X := (⊥ : Subgroup H₀)) (J := H)
    (fun x => ⟨0, Subtype.ext (by simpa using Subgroup.mem_bot.mp x.2)⟩) bot_le
  have hT₀S : IsSylowTwoOf (T₀.map φ) ⊤ := isSylowTwoOf_map_of_map_eq_top hHmap hT₀
  obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hT₀S h.isSylow
  obtain ⟨x, hxH, hxg⟩ := hsurjH g
  let T : Subgroup H₀ := conjSub x T₀
  have hHn : conjSub x H = H := conjSub_eq_self (Subgroup.le_normalizer hxH)
  have hTSyl : IsSylowTwoOf T H := by
    have := isSylowTwoOf_conjSub hT₀ x
    rwa [hHn] at this
  have hTS : T.map φ = S := by
    have hcomm : φ.comp (MulAut.conj x).toMonoidHom = (MulAut.conj (φ x)).toMonoidHom.comp φ := by
      ext z
      simp [map_mul, map_inv]
    have : T.map φ = conjSub (φ x) (T₀.map φ) := by
      show (T₀.map (MulAut.conj x).toMonoidHom).map φ =
        (T₀.map φ).map (MulAut.conj (φ x)).toMonoidHom
      rw [Subgroup.map_map, Subgroup.map_map, hcomm]
    rw [this, hxg, hg]
  let M' : Subgroup H₀ := H ⊓ M.comap φ
  have hMM' : M'.map φ = M := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · intro m hm
      obtain ⟨z, hzH, hzm⟩ := hsurjH m
      exact ⟨z, ⟨hzH, by simpa [hzm] using hm⟩, hzm⟩
  have hTM' : T ≤ M' := by
    intro z hz
    refine ⟨hTSyl.1 hz, ?_⟩
    show φ z ∈ M
    exact h.le (by rw [← hTS]; exact Subgroup.mem_map_of_mem φ hz)
  have hM'lt : M' < H := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have : H.map φ ≤ M := by
      rw [← heq]
      exact hMM'.le
    rw [hHmap] at this
    exact absurd (lt_of_le_of_lt this h.maximal.1) (lt_irrefl _)
  have hK : ∀ X' : Subgroup H₀, T ≤ X' → X' < H → X' ≤ M' := by
    intro X' hTX hXH
    have hmapX : X'.map φ ≠ ⊤ := by
      intro htop
      exact absurd (hminle X' htop hXH.le) hXH.ne
    have hSX : S ≤ X'.map φ := by
      rw [← hTS]
      exact Subgroup.map_mono hTX
    have hlt : X'.map φ < ⊤ := lt_top_iff_ne_top.mpr hmapX
    have hXM : X'.map φ ≤ M := h.le_of_lt hSX hlt
    exact fun z hz => ⟨hXH.le hz, hXM (Subgroup.mem_map_of_mem φ hz)⟩
  have hnn : ¬ H ≤ Subgroup.normalizer (T : Set H₀) := by
    intro hn
    apply h.not_normal
    intro y _
    obtain ⟨z, hzH, rfl⟩ := hsurjH y
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hz := Subgroup.mem_normalizer_iff.mp (hn hzH)
    constructor
    · intro hw
      rw [← hTS] at hw ⊢
      obtain ⟨t, ht, rfl⟩ := hw
      exact ⟨z * t * z⁻¹, (hz t).1 ht, by simp [map_mul, map_inv]⟩
    · intro hw
      rw [← hTS] at hw ⊢
      obtain ⟨t', ht', ht'e⟩ := hw
      refine ⟨z⁻¹ * t' * z, (hz (z⁻¹ * t' * z)).2 (by simpa [mul_assoc] using ht'), ?_⟩
      rw [map_mul, map_mul, map_inv, ht'e]
      group
  have hmax : IsMaxSubgroupIn H M' := by
    refine ⟨hM'lt, fun X' hKX hXH => ?_⟩
    by_contra hne
    exact absurd (hK X' (hTM'.trans hKX.le) (lt_of_le_of_ne hXH hne)) (not_le_of_gt hKX)
  refine ⟨H, T, M', ⟨hTSyl, hnn, isUniqueMaxOver_iff.mpr ⟨hmax, hTM', fun N hN hTN => ?_⟩⟩,
    hHmap, hTS, hMM', fun z hz => ⟨hz.2, ?_⟩⟩
  · have hNM : N ≤ M' := hK N hTN hN.1
    by_contra hne
    have hlt : N < M' := lt_of_le_of_ne hNM hne
    exact absurd (hN.2 M' hlt hM'lt.le) (ne_of_lt hM'lt)
  · show φ z ∈ M
    rw [(MonoidHom.mem_ker.mp hz.1)]
    exact M.one_mem

end B69

end CFSG.Quasithin
