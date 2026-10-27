module

public import CFSG.Quasithin.Background.RonanE111Wr
public import CFSG.Quasithin.EmptyFaithful.E111RMain

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem solvable_conj_sup {X₀ T J X : Subgroup G} (hR : E111Reduced G X₀ T) (hJ : IsComp X₀ J)
    (hXJ : X ≤ J) (hXs : Group.IsSolvable ↥X)
    (hSX : ∀ s ∈ T ⊓ Subgroup.normalizer (J : Set G), ∀ x ∈ X, s * x * s⁻¹ ∈ X) :
    Group.IsSolvable ↥((⨆ t ∈ T, A1b.conjSub t X) ⊔ T) := by
  classical
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hSdef
  set N₁ : Subgroup G := ⨆ t ∈ T, A1b.conjSub t X with hN₁
  have hpair : ∀ t ∈ T, ∀ t' ∈ T, A1b.conjSub t X ≠ A1b.conjSub t' X →
      ∀ x ∈ A1b.conjSub t X, ∀ y ∈ A1b.conjSub t' X, x * y = y * x := by
    intro t ht t' ht' hne
    rcases (hJ.conj hR.1 t).eq_or_commute (hJ.conj hR.1 t') with heq | hcomm
    · exfalso
      apply hne
      set m : G := t⁻¹ * t' with hm
      have hmN : m ∈ Subgroup.normalizer (J : Set G) := by
        apply E111R.mem_normalizer_of_conjSub_eq
        rw [hm, A1b.conjSub_mul, ← heq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
      have hmT : m ∈ T := T.mul_mem (T.inv_mem ht) ht'
      have hmX : A1b.conjSub m X = X := by
        apply E111R.conjSub_eq_of_mem_normalizer
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => hSX m ⟨hmT, hmN⟩ x hx, fun hx => ?_⟩
        have := hSX m⁻¹ ⟨T.inv_mem hmT, Subgroup.inv_mem _ hmN⟩ _ hx
        simpa [mul_assoc] using this
      have : t' = t * m := by rw [hm]; group
      rw [this, A1b.conjSub_mul, hmX]
    · intro x hx y hy
      exact hcomm x (A1b.conjSub_mono t hXJ hx) y (A1b.conjSub_mono t' hXJ hy)
  have hN₁sol : Group.IsSolvable ↥N₁ := by
    have h𝒱 := wr_isSolvable_sSup (𝒱 := Set.range fun t : T => A1b.conjSub (t : G) X)
      (by rintro _ ⟨t, rfl⟩; exact wr_isSolvable_conj _ hXs)
      (by
        rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ hne x hx y hy
        exact hpair t t.2 t' t'.2 hne x hx y hy)
    have hsup : sSup (Set.range fun t : T => A1b.conjSub (t : G) X) = N₁ := by
      rw [hN₁, sSup_range]
      apply le_antisymm
      · exact iSup_le fun t => le_iSup₂_of_le (f := fun k (_ : k ∈ T) => A1b.conjSub k X)
          (t : G) t.2 le_rfl
      · exact iSup₂_le fun k hk => le_iSup_of_le (⟨k, hk⟩ : T) le_rfl
    rwa [hsup] at h𝒱
  have hTN : T ≤ Subgroup.normalizer (N₁ : Set G) := fun t ht => wr_mem_normalizer ht
  set H : Subgroup G := N₁ ⊔ T with hH
  have hN₁H : N₁ ≤ H := le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (N₁ : Set G) := sup_le Subgroup.le_normalizer hTN
  haveI hn₁ : (N₁.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁H).mpr hHN
  have hTsol : Group.IsSolvable ↥T := by
    have := (hT.2.1 : IsPGroup 2 ↥T).isNilpotent
    infer_instance
  let φ : ↥T →* ↥H ⧸ N₁.subgroupOf H :=
    (QuotientGroup.mk' (N₁.subgroupOf H)).comp (Subgroup.inclusion hTH)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, t, ht, hnt⟩ := exists_mul_of_mem_sup hTN h.2
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hTH ⟨t, ht⟩) : ↥H ⧸ N₁.subgroupOf H) =
      QuotientGroup.mk h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show t⁻¹ * (h : G) ∈ N₁
    have e : t⁻¹ * (h : G) = t⁻¹ * n * (t⁻¹)⁻¹ := by rw [hnt]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) n).mp hn
  haveI : Group.IsSolvable (↥H ⧸ N₁.subgroupOf H) := by
    haveI := hTsol
    exact Group.isSolvable_of_surjective hφ
  haveI : Group.IsSolvable ↥(N₁.subgroupOf H) := by
    haveI := hN₁sol
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hN₁H).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hN₁H).symm.surjective
  refine solvable_of_ker_le_range (N₁.subgroupOf H).subtype (QuotientGroup.mk' (N₁.subgroupOf H)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

end CFSG.Quasithin.RonanE111
