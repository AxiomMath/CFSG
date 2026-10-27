module

public import CFSG.Quasithin.Background.B69Swap
public import CFSG.Quasithin.Background.B69E22Main
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace B69

theorem map_conjSub {Y Q : Type*} [Group Y] [Group Q] (q : Y →* Q) (t : Y) (L : Subgroup Y) :
    (conjSub t L).map q = conjSub (q t) (L.map q) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_conjSub] at hy
    exact ⟨t⁻¹ * y * t, hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨t * z * t⁻¹, ?_, ?_⟩
    · rw [mem_conjSub]
      simpa [mul_assoc] using hz
    · have : x = q t * q z * (q t)⁻¹ := by
        rw [hzx]
        group
      rw [this]
      simp

theorem mem_normalizer_of_image {Y Q : Type} [Group Y] [Finite Y] [Group Q] (q : Y →* Q)
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) (hLf : ¬ L ≤ q.ker) {t : Y}
    (ht : q t ∈ Subgroup.normalizer ((L.map q : Subgroup Q) : Set Q)) :
    t ∈ Subgroup.normalizer (L : Set Y) := by
  have hL' : CFSG.GorensteinWalter.IsComponentOf L ⊤ := (CFSG.Adapters.isComponentOf_top_iff L).1 hL
  have hLsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).1 hL.2.1
  have hsn : (conjSub t L).IsSubnormal :=
    Subgroup.IsSubnormal.map (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).surjective hLsn
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hL.2.2.1)
  have himage : (conjSub t L).map q = L.map q := by
    rw [map_conjSub]
    exact conjSub_eq_self ht
  rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot hL' hsn with hle | hcomm
  · have hcard : Nat.card ↥(conjSub t L) ≤ Nat.card ↥L :=
      (Nat.card_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective).toEquiv).symm.le
    have heq : L = conjSub t L := Subgroup.eq_of_le_of_card_ge hle hcard
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  · exfalso
    have h1 : ⁅L.map q, (conjSub t L).map q⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
    rw [himage, ← Subgroup.map_commutator, hLperf] at h1
    exact hLf ((Subgroup.map_eq_bot_iff L).mp h1)

theorem ker_eq_center_of_surj {L G₀ : Type*} [Group L] [Group G₀] (hL : CFSG.Open.IsQuasisimple L)
    [Nontrivial G₀] (hZ : Subgroup.center G₀ = ⊥) (π : L →* G₀) (hπ : Function.Surjective π) :
    π.ker = Subgroup.center L := by
  apply le_antisymm
  · have hne : π.ker ≠ ⊤ := by
      intro htop
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial G₀).exists_pair_ne
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      apply hab
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
    exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL π.ker hne
  · intro z hz
    rw [MonoidHom.mem_ker]
    have : π z ∈ Subgroup.center G₀ := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hπ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this

theorem exists_swap {Y : Type} [Group Y] [Finite Y] {S M : Subgroup Y} {G₀ : Type} [Group G₀]
    {TP : MulAut G₀ → Prop} (hgeo : SwapGeo G₀ TP) (hev : Even (Nat.card G₀))
    (h : MinParabolic (⊤ : Subgroup Y) S M) {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤)
    (π : ↥L →* G₀) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center ↥L) :
    ∃ t ∈ S, t ∈ Subgroup.normalizer (L : Set Y) ∧ ∀ φ : MulAut G₀,
      (∀ l l' : ↥L, (l' : Y) = t * l * t⁻¹ → φ (π l) = π l') → ¬ TP φ := by
  classical
  set J : Subgroup Y := kerIn M ⊤ with hJ
  let q : Y →* Y ⧸ J := QuotientGroup.mk' J
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective J
  have hkerq : q.ker = J := QuotientGroup.ker_mk' J
  have hkerM : q.ker ≤ M := by
    rw [hkerq]
    exact kerIn_le
  have hmpq := h.map_of_surjective hqs hkerM
  have hJq : kerIn (M.map q) ⊤ = ⊥ := by
    rw [kerIn_map_top hqs hkerM, Subgroup.map_eq_bot_iff, hkerq]
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hJs : Group.IsSolvable ↥J := h.isSolvable_kerIn
  have hLf : ¬ L ≤ q.ker := by
    intro hle
    rw [hkerq] at hle
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥L this
  have hLb := isComponentOf_map_top q hqs hL hLf
  obtain ⟨hsimp, hnc, -⟩ := component_is_factor hmpq hJq hLb
  let πb : ↥L →* ↥(L.map q) := q.subgroupMap L
  have hπb : Function.Surjective πb := q.subgroupMap_surjective L
  have : IsSimpleGroup ↥(L.map q) := hsimp
  have : Group.IsPerfect ↥(L.map q) := Group.IsPerfect.ofSurjective hπb
  have hZb : Subgroup.center ↥(L.map q) = ⊥ := center_eq_bot_of_perfect_simple
  have hkerb : πb.ker = Subgroup.center ↥L :=
    ker_eq_center_of_surj hLq hZb πb hπb
  let ι₀ : ↥(L.map q) →* G₀ := πb.liftOfSurjective hπb ⟨π, by rw [hkerb, hπk]⟩
  have hι₀ : ∀ l, ι₀ (πb l) = π l := fun l => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
  have hι_inj : Function.Injective ι₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨l, rfl⟩ := hπb x
    rw [hι₀] at hx
    have hl : l ∈ π.ker := hx
    rw [hπk, ← hkerb] at hl
    exact hl
  have hι_surj : Function.Surjective ι₀ := fun g => by
    obtain ⟨l, rfl⟩ := hπ g
    exact ⟨πb l, hι₀ l⟩
  let ι : ↥(L.map q) ≃* G₀ := MulEquiv.ofBijective ι₀ ⟨hι_inj, hι_surj⟩
  have hιπ : ∀ l, ι (πb l) = π l := hι₀
  obtain ⟨tb, htb, htbN, hnot⟩ := exists_swap_quot hgeo hev hmpq hJq hLb ι
  obtain ⟨t, htS, rfl⟩ := Subgroup.mem_map.1 htb
  have htN : t ∈ Subgroup.normalizer (L : Set Y) := mem_normalizer_of_image q hL hLf htbN
  refine ⟨t, htS, htN, fun φ hφ => ?_⟩
  have hφeq : φ = MulAut.congr ι (indAut (L.map q) (q t)) := by
    ext g
    obtain ⟨l, rfl⟩ := hπ g
    have hlmem : t * (l : Y) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htN l).mp l.2
    have h1 : indAut (L.map q) (q t) (πb l) = πb ⟨t * (l : Y) * t⁻¹, hlmem⟩ := by
      apply Subtype.ext
      rw [coe_indAut_apply htbN]
      simp [πb, map_mul, map_inv]
    have h2 : ι.symm (π l) = πb l := by
      rw [MulEquiv.symm_apply_eq]
      exact (hιπ l).symm
    show φ (π l) = ι (indAut (L.map q) (q t) (ι.symm (π l)))
    rw [h2, h1, hιπ]
    exact hφ l ⟨t * (l : Y) * t⁻¹, hlmem⟩ rfl
  rw [hφeq]
  exact hnot

end B69

end CFSG.Quasithin
