module

public import CFSG.Quasithin.Vol2.Ch11SecBHBOne
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.Vol2.Ch10SecQ3CG

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

noncomputable abbrev starMk (X H : Subgroup G) : ↥H →* E2.StarQuot X H :=
  QuotientGroup.mk' ((kerIn X H).subgroupOf H)

theorem star_cjSub {X H Y : Subgroup G} {g : G} (hg : g ∈ H) :
    E2.star X H (cjSub g Y) = cjSub (starMk X H ⟨g, hg⟩) (E2.star X H Y) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_cjSub] at hy
    rw [mem_cjSub]
    refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simpa using hy
  · intro hz
    rw [mem_cjSub] at hz
    obtain ⟨y, hy, hye⟩ := hz
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_cjSub]
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      simpa [mul_assoc] using hy
    · show starMk X H (⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹) = z
      rw [map_mul, map_mul, map_inv, show starMk X H y = _ from hye]
      group

theorem star_sup {X H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    E2.star X H (A ⊔ B) = E2.star X H A ⊔ E2.star X H B := by
  rw [E2.star, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

theorem star_self (X H : Subgroup G) : E2.star X H H = ⊤ := by
  rw [E2.star, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

theorem star_mono {X H A B : Subgroup G} (h : A ≤ B) : E2.star X H A ≤ E2.star X H B :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem star_inf_le {X H T K : Subgroup G} (hJT : kerIn X H ≤ T) :
    E2.star X H T ⊓ E2.star X H K ≤ E2.star X H (T ⊓ K) := by
  rintro z ⟨⟨t, ht, rfl⟩, ⟨k, hk, hke⟩⟩
  have h1 : t⁻¹ * k ∈ (kerIn X H).subgroupOf H := by
    rw [← QuotientGroup.ker_mk' ((kerIn X H).subgroupOf H), MonoidHom.mem_ker, map_mul,
      map_inv, inv_mul_eq_one]
    exact hke.symm
  have hkT : (k : G) ∈ T := by
    have := T.mul_mem (Subgroup.mem_subgroupOf.mp ht) (hJT (Subgroup.mem_subgroupOf.mp h1))
    simpa using this
  exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hkT, Subgroup.mem_subgroupOf.mp hk⟩, hke⟩

variable [Finite G]

theorem kerIn_eq_solvRad {H T X : Subgroup G} (hU : IsUniqueMaxOver H T X) (hT2 : IsPGroup 2 T)
    (hns : ¬ Group.IsSolvable ↥H) (hJ : kerIn X H = pCoreOf 2 H) : kerIn X H = solvRad H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (Ch11.SecB.solvRad_le_kerIn hU hT2 hns)
  rw [hJ]
  refine le_solvRad (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) ?_
  have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
  infer_instance

theorem subgroupOf_kerIn_eq {H X : Subgroup G} (h : kerIn X H = solvRad H) :
    (kerIn X H).subgroupOf H = CFSG.solvableRadical ↥H := by
  rw [h, solvRad_eq_map_solvableRadical]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem solvableRadical_star_eq_bot {H X : Subgroup G}
    (h : (kerIn X H).subgroupOf H = CFSG.solvableRadical ↥H) :
    CFSG.solvableRadical (E2.StarQuot X H) = ⊥ := by
  rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv
    (QuotientGroup.quotientMulEquivOfEq h.symm), A3.solvableRadical_quotient_eq_bot,
    Subgroup.map_bot]

theorem mem_cComp_star {H X L : Subgroup G}
    (hker : Group.IsSolvable ↥((kerIn X H).subgroupOf H)) (hL : L ∈ cComp H) :
    E2.star X H L ∈ cComp (⊤ : Subgroup (E2.StarQuot X H)) :=
  map_mem_cComp_top _ (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hker)
    (subgroupOf_mem_cComp hL)

omit [Finite G] in
theorem cjSub_mem_cComp' {H L : Subgroup G} (hL : L ∈ cComp H) {g : G} (hg : g ∈ H) :
    cjSub g L ∈ cComp H := by
  have := cComp_map_mulEquiv (MulAut.conj g) hL
  rwa [Ch11.SecB.map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)] at this

theorem star_ne {H X L L' : Subgroup G}
    (hker : Group.IsSolvable ↥((kerIn X H).subgroupOf H)) (hL : L ∈ cComp H)
    (hL' : L' ∈ cComp H) (hne : L ≠ L') : E2.star X H L ≠ E2.star X H L' := by
  intro h
  apply hne
  have hker' : Group.IsSolvable (QuotientGroup.mk' ((kerIn X H).subgroupOf H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hker
  have h1 := map_injOn_cComp_top _ hker' (subgroupOf_mem_cComp hL) (subgroupOf_mem_cComp hL') h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left (le_of_mem_cComp hL),
    inf_of_le_left (le_of_mem_cComp hL')] at h1
  exact h1

theorem not_dvd_card_star {H T X B : Subgroup G} (hXH : X ≤ H) (hT : IsSylowTwoOf T X)
    (hB : Lin2.IsHallTwoPrimeOf B X) (hB9 : Nat.card B = 9) :
    ¬ 27 ∣ Nat.card (E2.star X H X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h27
  have h1 : Nat.card (E2.star X H X) ∣ Nat.card X := by
    have := Subgroup.card_map_dvd (H := X.subgroupOf H)
      (QuotientGroup.mk' ((kerIn X H).subgroupOf H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv] at this
  rw [card_eq_card_mul_card hT hB, hB9] at h1
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hT.2.1
  rw [ha] at h1
  have h3 : 3 ∣ 2 ^ a := by
    have := h27.trans h1
    rw [show 27 = 3 * 9 by norm_num] at this
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
