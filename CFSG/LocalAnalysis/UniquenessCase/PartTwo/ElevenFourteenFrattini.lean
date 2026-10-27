module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

namespace ElevenFourteen

theorem exists_noncyclic_pSubgroup_normalizer {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {H K T₀ P S₀ : Subgroup G} (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hT₀ : IsSylowOf q T₀ K) (hP : IsPGroup p P) (hPH : P ≤ H) (hS₀ : P ⊓ K = S₀)
    [(S₀.subgroupOf P).Normal] (hnc : ¬ IsCyclic (↥P ⧸ S₀.subgroupOf P)) :
    ∃ X : Subgroup G, X ≤ H ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧ X ≤ normalizer (T₀ : Set G) := by
  classical
  haveI hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  obtain ⟨hTK, hTp, hTidx⟩ := isSylowOf_iff.1 hT₀
  have hTH : T₀ ≤ H := hTK.trans hKH
  have hT' : IsSylowOf q (T₀.subgroupOf H) (K.subgroupOf H) := by
    refine isSylowOf_iff.2 ⟨fun x hx => hTK hx, hTp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf hKH]
  obtain ⟨T₁, hT₁⟩ := hT'
  have hF : normalizer ((T₀.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔ K.subgroupOf H = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top T₁
    rw [hT₁] at h
    exact h
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  set N : Subgroup ↥H := normalizer ((T₀.subgroupOf H : Subgroup ↥H) : Set ↥H) with hN
  set π : ↥H →* ↥H ⧸ K' := QuotientGroup.mk' K' with hπ
  set P' : Subgroup ↥H := P.subgroupOf H with hP'
  have hP'p : IsPGroup p ↥P' := hP.comap_subtype
  set Q : Subgroup (↥H ⧸ K') := P'.map π with hQ
  set W : Subgroup ↥H := N ⊓ Q.comap π with hW
  have hπW : W.map π = Q := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ N ⊔ K' := hF ▸ Subgroup.mem_top y
      obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy'
      have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      have hπ1 : π (n * k) = π n := by
        rw [map_mul, hk1, mul_one]
      refine ⟨n, ⟨hn, ?_⟩, hπ1.symm⟩
      show π n ∈ Q
      rw [← hπ1]
      exact Subgroup.mem_map_of_mem _ hy
  obtain ⟨X₀⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥W))
  set X' : Subgroup ↥H := (X₀ : Subgroup ↥W).map W.subtype with hX'
  have hXW : X' ≤ W := Subgroup.map_subtype_le _
  have hQp : IsPGroup p ↥Q := hP'p.map π
  have hWQ : ∀ w : ↥W, π (w : ↥H) ∈ Q := fun w => w.2.2
  let f : ↥W →* ↥Q := (π.comp W.subtype).codRestrict Q hWQ
  have hf : Function.Surjective f := by
    rintro ⟨q', hq'⟩
    rw [← hπW] at hq'
    obtain ⟨w, hw, hwq⟩ := hq'
    exact ⟨⟨w, hw⟩, Subtype.ext hwq⟩
  have htop : ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) = ⊤ := by
    symm
    exact (X₀.mapSurjective hf).is_maximal' (hQp.of_equiv Subgroup.topEquiv.symm) le_top
  have hsurj : ∀ q' ∈ Q, ∃ x ∈ X', π x = q' := by
    intro q' hq'
    have h1 : (⟨q', hq'⟩ : ↥Q) ∈ ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) := by
      rw [htop]; trivial
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨x, hx, hxq⟩ := h1
    exact ⟨(x : ↥H), ⟨x, hx, rfl⟩, congrArg Subtype.val hxq⟩
  refine ⟨X'.map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact (X₀.isPGroup'.map W.subtype).map H.subtype
  · intro hXc
    apply hnc
    have hX'c : IsCyclic ↥X' :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective X' H.subtype H.subtype_injective).symm.toMonoidHom
        (Subgroup.equivMapOfInjective X' H.subtype H.subtype_injective).symm.surjective
    let g : ↥X' →* ↥Q := (π.comp X'.subtype).codRestrict Q (fun x => (hXW x.2).2)
    have hg : Function.Surjective g := by
      rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hxq⟩ := hsurj q' hq'
      exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
    haveI : IsCyclic ↥Q := isCyclic_of_surjective g hg
    let h : ↥P →* ↥Q :=
      (π.comp (Subgroup.inclusion hPH)).codRestrict Q
        (fun x => Subgroup.mem_map.2 ⟨Subgroup.inclusion hPH x, x.2, rfl⟩)
    have hh : Function.Surjective h := by
      rintro ⟨q', hq'⟩
      obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.1 hq'
      exact ⟨⟨(y : G), hy⟩, Subtype.ext hyq⟩
    have hker : h.ker = S₀.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hS₀]
      constructor
      · intro hx
        have hx' : π (Subgroup.inclusion hPH x) = 1 := congrArg Subtype.val hx
        have hxK : Subgroup.inclusion hPH x ∈ K' := (QuotientGroup.eq_one_iff _).1 hx'
        exact ⟨x.2, hxK⟩
      · rintro ⟨-, hxK⟩
        refine Subtype.ext ?_
        show π (Subgroup.inclusion hPH x) = 1
        exact (QuotientGroup.eq_one_iff _).2 hxK
    have hPc : IsCyclic (↥P ⧸ h.ker) :=
      (QuotientGroup.quotientKerEquivOfSurjective h hh).isCyclic.2 ‹IsCyclic ↥Q›
    exact (QuotientGroup.quotientMulEquivOfEq hker).isCyclic.1 hPc
  · rintro _ ⟨x', hx', rfl⟩
    have hx'N : x' ∈ N := (hXW hx').1
    rw [Subgroup.mem_normalizer_iff] at hx'N ⊢
    intro h
    constructor
    · intro hh
      exact (hx'N ⟨h, hTH hh⟩).1 hh
    · intro hh
      have hhH : h ∈ H := by
        have h1 : (x' : G) * h * (x' : G)⁻¹ ∈ H := hTH hh
        have := H.mul_mem (H.mul_mem (H.inv_mem x'.2) h1) x'.2
        simpa [mul_assoc] using this
      exact (hx'N ⟨h, hhH⟩).2 hh

end ElevenFourteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
