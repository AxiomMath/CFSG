module

public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.Quasithin.Background.RonanF13CoverAux
public import CFSG.Quasithin.Background.RonanF13Section
public import CFSG.Quasithin.Background.F1Cartan

public section

namespace CFSG.Quasithin.RonanF13

theorem twist_of_quotient {Lg K : Type*} [Group Lg] [Group K] (π : Lg →* K)
    (hπ : Function.Surjective π) (hK : RankOneTwist K) (T D : Subgroup Lg) (β : MulAut Lg)
    (hT : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.index) (hker : π.ker ≤ T)
    (hTD : T ⊔ D = Subgroup.normalizer (T : Set Lg)) (hDodd : Odd (Nat.card D))
    (hβT : ∀ x, β x ∈ T ↔ x ∈ T) (hβD : ∀ x, β x ∈ D ↔ x ∈ D)
    (hβk : ∀ x, β x ∈ π.ker ↔ x ∈ π.ker) (hβodd : Odd (orderOf β))
    (hcomm : ∀ x ∈ D, β (x⁻¹ * β x) = x⁻¹ * β x) :
    ∀ x ∈ D, x⁻¹ * β x ∈ π.ker := by
  obtain ⟨β', hβ'⟩ := exists_induced_aut π hπ β hβk
  have hodd' := odd_orderOf_induced π hπ β β' hβ' hβodd
  have hmapT : (T.map π).comap π = T := Subgroup.comap_map_eq_self hker
  have hmemT : ∀ y, π y ∈ T.map π ↔ y ∈ T := by
    intro y
    rw [← Subgroup.mem_comap, hmapT]
  have hmemD : ∀ y, π y ∈ D.map π ↔ ∃ d ∈ D, d⁻¹ * y ∈ π.ker := by
    intro y
    constructor
    · intro hy
      obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy
      refine ⟨d, hd, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdy, inv_mul_cancel]
    · rintro ⟨d, hd, hk⟩
      refine Subgroup.mem_map.mpr ⟨d, hd, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
      exact hk
  have hnorm : Subgroup.normalizer ((T.map π : Subgroup K) : Set K) =
      (Subgroup.normalizer (T : Set Lg)).map π := by
    have h1 : (Subgroup.normalizer ((T.map π : Subgroup K) : Set K)).comap π =
        Subgroup.normalizer (T : Set Lg) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective _ hπ, hmapT]
    conv_rhs => rw [← h1]
    exact (Subgroup.map_comap_eq_self_of_surjective hπ _).symm
  have hmain := hK (T.map π) (D.map π) β' (hT.map π) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have h1 := hmain (π x) (Subgroup.mem_map_of_mem π hx)
    rw [hβ'] at h1
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h1, inv_mul_cancel]
  · rw [Subgroup.index_map_eq (f := π) (H := T) hπ hker]
    exact hTodd
  · rw [← Subgroup.map_sup, hTD, hnorm]
  · exact Odd.of_dvd_nat hDodd (Subgroup.card_map_dvd D π)
  · intro x
    obtain ⟨y, rfl⟩ := hπ x
    rw [hβ', hmemT, hmemT, hβT]
  · intro x
    obtain ⟨y, rfl⟩ := hπ x
    rw [hβ', hmemD, hmemD]
    constructor
    · rintro ⟨d, hd, hk⟩
      refine ⟨β⁻¹ d, (hβD (β⁻¹ d)).mp (by simpa using hd), (hβk _).mp ?_⟩
      have : β ((β⁻¹ d)⁻¹ * y) = d⁻¹ * β y := by simp [map_mul, map_inv]
      rw [this]
      exact hk
    · rintro ⟨d, hd, hk⟩
      refine ⟨β d, (hβD d).mpr hd, ?_⟩
      have : (β d)⁻¹ * β y = β (d⁻¹ * y) := by simp
      rw [this, hβk]
      exact hk
  · exact hodd'
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : (π d)⁻¹ * β' (π d) = π (d⁻¹ * β d) := by rw [hβ', map_mul, map_inv]
    rw [h1, hβ', hcomm d hd]

section Commute

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type*} [Group G]

theorem conjAut_pow_eq_one (H : Subgroup G) (d : G) (hd : d ∈ Subgroup.normalizer (H : Set G))
    (m : ℕ) (hm : d ^ m = 1) : conjAut H d hd ^ m = 1 := by
  have key : ∀ j : ℕ, ∀ x : ↥H, (((conjAut H d hd ^ j) x : ↥H) : G) = d ^ j * x * (d ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, conjAut_apply, ih]
      simp [pow_succ', mul_assoc]
  ext x
  rw [key, hm]
  simp

theorem twist_commute {L T B Di : Subgroup G} (hTL : T ≤ L) (hT2 : IsPGroup 2 T)
    (hT3 : ¬ 2 ∣ T.relIndex L) (hB : B = L ⊓ Subgroup.normalizer (T : Set G))
    (hBD : B = T ⊔ Di) (hDodd : Odd (Nat.card Di))
    (hK : RankOneTwist (↥L ⧸ pCore 2 ↥L)) (hpcT : pCoreOf 2 L ≤ T)
    {d : G} (hdL : d ∈ Subgroup.normalizer (L : Set G)) (hdT : d ∈ Subgroup.normalizer (T : Set G))
    (hdD : d ∈ Subgroup.normalizer (Di : Set G))
    (hdpc : d ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G))
    (hdodd : Odd (orderOf d))
    (hcomm : ∀ x ∈ Di, d * (x⁻¹ * (d * x * d⁻¹)) * d⁻¹ = x⁻¹ * (d * x * d⁻¹)) :
    ∀ x ∈ Di, d * x * d⁻¹ = x := by
  classical
  have hDiB : Di ≤ B := hBD ▸ le_sup_right
  have hBL : B ≤ L := hB ▸ inf_le_left
  have hDiL : Di ≤ L := hDiB.trans hBL
  have hTB : T ≤ B := hBD ▸ le_sup_left
  let π : ↥L →* (↥L ⧸ pCore 2 ↥L) := QuotientGroup.mk' (pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerE : ∀ x : ↥L, x ∈ π.ker ↔ (x : G) ∈ pCoreOf 2 L := by
    intro x
    rw [QuotientGroup.ker_mk']
    exact F1.mem_pCore_iff_coe x
  let T' : Subgroup ↥L := T.subgroupOf L
  let D' : Subgroup ↥L := Di.subgroupOf L
  let β : MulAut ↥L := conjAut L d hdL
  have hT' : IsPGroup 2 T' := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hker : π.ker ≤ T' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hpcT ((hkerE x).mp hx)
  have hTD' : T' ⊔ D' = Subgroup.normalizer (T' : Set ↥L) := by
    have h1 := F1.normalizer_subgroupOf_eq (Li := L) (S := T)
    rw [inf_eq_left.mpr hTL] at h1
    have h2 : (borelOf L T).subgroupOf L = B.subgroupOf L := by
      rw [hB]
      show (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)).subgroupOf L = _
      rw [inf_eq_left.mpr hTL]
    show T.subgroupOf L ⊔ Di.subgroupOf L = _
    rw [← Subgroup.subgroupOf_sup hTL hDiL, ← hBD, h1, h2]
  have hDodd' : Odd (Nat.card D') := by
    have : Nat.card D' = Nat.card Di := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDiL).toEquiv
    rw [this]
    exact hDodd
  have hβT : ∀ x, β x ∈ T' ↔ x ∈ T' := by
    intro x
    show d * (x : G) * d⁻¹ ∈ T ↔ (x : G) ∈ T
    exact ((Subgroup.mem_normalizer_iff.mp hdT x).symm)
  have hβD : ∀ x, β x ∈ D' ↔ x ∈ D' := by
    intro x
    show d * (x : G) * d⁻¹ ∈ Di ↔ (x : G) ∈ Di
    exact ((Subgroup.mem_normalizer_iff.mp hdD x).symm)
  have hβk : ∀ x, β x ∈ π.ker ↔ x ∈ π.ker := by
    intro x
    rw [hkerE, hkerE]
    show d * (x : G) * d⁻¹ ∈ pCoreOf 2 L ↔ (x : G) ∈ pCoreOf 2 L
    exact ((Subgroup.mem_normalizer_iff.mp hdpc x).symm)
  have hβodd : Odd (orderOf β) := by
    refine Odd.of_dvd_nat hdodd (orderOf_dvd_of_pow_eq_one ?_)
    exact conjAut_pow_eq_one L d hdL (orderOf d) (pow_orderOf_eq_one d)
  have hβcomm : ∀ x ∈ D', β (x⁻¹ * β x) = x⁻¹ * β x := by
    intro x hx
    apply Subtype.ext
    exact hcomm (x : G) (Subgroup.mem_subgroupOf.mp hx)
  have hmain := twist_of_quotient π hπ hK T' D' β hT' hT3 hker hTD' hDodd' hβT hβD hβk hβodd hβcomm
  intro x hx
  have hxL : x ∈ L := hDiL hx
  have h1 := hmain ⟨x, hxL⟩ (Subgroup.mem_subgroupOf.mpr hx)
  have h2 : x⁻¹ * (d * x * d⁻¹) ∈ pCoreOf 2 L := by
    have := (hkerE _).mp h1
    simpa [β, conjAut_apply] using this
  have h3 : x⁻¹ * (d * x * d⁻¹) ∈ Di :=
    Di.mul_mem (Di.inv_mem hx) ((Subgroup.mem_normalizer_iff.mp hdD x).mp hx)
  have h4 : x⁻¹ * (d * x * d⁻¹) ∈ T ⊓ Di := ⟨hpcT h2, h3⟩
  rw [inf_eq_bot_of_odd hT2 hDodd, Subgroup.mem_bot] at h4
  calc d * x * d⁻¹ = x * (x⁻¹ * (d * x * d⁻¹)) := by group
    _ = x := by rw [h4, mul_one]

end Commute

end CFSG.Quasithin.RonanF13
