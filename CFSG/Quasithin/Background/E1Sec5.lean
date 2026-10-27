module

public import CFSG.Quasithin.Background.E1Sections
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open

universe u

theorem ten_five {G : Type u} [Group G] [Finite G] {T X Y K : Subgroup G} [Y.Normal]
    (hXY : IsChiefFactor X Y) (hK : K ∈ sFamily T X Y) :
    ∃ (L : Type u) (_ : Group L), IsSimpleGroup L ∧ IsCompositionFactor G L ∧
      ∃ n : ℕ, Nonempty (↥((K ⊓ X).map (QuotientGroup.mk' Y)) ≃* (Fin n → L)) := by
  have hXn := hXY.normal_left
  have hYn : Y.Normal := inferInstance
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t _ => by
    have : Subgroup.normalizer (X : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hXn
    rw [this]
    exact Subgroup.mem_top t
  have hYX : Y ≤ X := hXY.lt.le
  obtain ⟨-, hmapeq, -⟩ := ten_one hTX hYX hK
  set N : Subgroup (G ⧸ Y) := X.map π with hN
  have hNn : N.Normal := Subgroup.Normal.map hXn π hπs
  have hN1 : N ≠ ⊥ := by
    intro h
    rw [hN, Subgroup.map_eq_bot_iff, hker] at h
    exact absurd h (not_le_of_gt hXY.lt)
  have hmin : ∀ M : Subgroup (G ⧸ Y), M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hM hle
    have hM' : (M.comap π).Normal := Subgroup.normal_comap π
    have hYM : Y ≤ M.comap π := fun y hy => by
      show π y ∈ M
      have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      rw [h1]
      exact Subgroup.one_mem _
    have hMX : M.comap π ≤ X := by
      intro x hx
      obtain ⟨x', hx', hxx⟩ := hle (show π x ∈ M from hx)
      have : x'⁻¹ * x ∈ Y := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxx]
        simp
      have h2 : x = x' * (x'⁻¹ * x) := by group
      rw [h2]
      exact X.mul_mem hx' (hYX this)
    rcases hXY.minimal (M.comap π) hM' hYM hMX with h | h
    · left
      calc M = (M.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs M).symm
        _ = Y.map π := by rw [h]
        _ = ⊥ := (Subgroup.map_eq_bot_iff Y).mpr hker.ge
    · right
      calc M = (M.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs M).symm
        _ = N := by rw [h]
  obtain ⟨r, S, hr, hSN, hSsimple, hconj, hSnorm, e, -⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hmin
  let i₀ : Fin r := ⟨0, hr⟩
  have hS₀ : IsSimpleGroup (S i₀) := hSsimple i₀
  choose g hg using fun i => hconj i₀ i
  let φ : ∀ i : Fin r, ↥(S i₀) ≃* ↥(S i) := fun i =>
    (Subgroup.equivMapOfInjective (S i₀) (MulAut.conj (g i)⁻¹).toMonoidHom
      (MulAut.conj (g i)⁻¹).injective).trans (MulEquiv.subgroupCongr (hg i).symm)
  let e' : (Fin r → ↥(S i₀)) ≃* ((i : Fin r) → ↥(S i)) := MulEquiv.piCongrRight φ
  refine ⟨↥(S i₀), inferInstance, hS₀, ?_, r,
    ⟨(MulEquiv.subgroupCongr hmapeq).trans (e.symm.trans e'.symm)⟩⟩
  have hS₀sub : (S i₀).IsSubnormal :=
    Subgroup.IsSubnormal.step (S i₀) N (hSN i₀) hNn.isSubnormal (hSnorm i₀)
  have hYM : Y ≤ (S i₀).comap π := fun y hy => by
    show π y ∈ S i₀
    have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [h1]
    exact Subgroup.one_mem _
  let f : ↥((S i₀).comap π) →* ↥(S i₀) :=
    (π.domRestrict ((S i₀).comap π)).codRestrict (S i₀) (fun m => m.2)
  have hfs : Function.Surjective f := by
    intro s
    obtain ⟨x, hx⟩ := hπs (s : G ⧸ Y)
    exact ⟨⟨x, show π x ∈ S i₀ by rw [hx]; exact s.2⟩, Subtype.ext hx⟩
  have hfker : f.ker = Y.subgroupOf ((S i₀).comap π) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : π (m : G) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr h
  let eq : (↥((S i₀).comap π) ⧸ Y.subgroupOf ((S i₀).comap π)) ≃* ↥(S i₀) :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  unfold IsCompositionFactor
  exact ⟨Y, (S i₀).comap π, inferInstance, hYM, hYn.isSubnormal,
    Subgroup.IsSubnormal.comap π hS₀sub, MulEquiv.isSimpleGroup eq, ⟨eq⟩⟩

end E1

end CFSG.Quasithin
