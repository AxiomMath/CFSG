module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K]

section Torus

variable (hK : Nat.card K = 2 ^ (2 * a + 1))

include hK

theorem exists_SD {g : suzukiGroup a K} (hg : g ∈ suzukiB a K) :
    ∃ (l : Kˣ) (u v : K), g = suzukiSElt a K u v * suzukiDElt a K l := by
  obtain ⟨p, hp, -⟩ := (suzuki_borel_structure hK).2.2.2.2.2.2.1 g hg
  exact ⟨p.2, p.1.1, p.1.2, hp⟩

omit [Finite K] hK in
theorem SD_mem (u v : K) (l : Kˣ) :
    suzukiSElt a K u v * suzukiDElt a K l ∈ suzukiB a K :=
  mul_mem (suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K u v))
    (suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K l))

theorem SD_unique {u v c d : K} {l m : Kˣ}
    (h : suzukiSElt a K u v * suzukiDElt a K l = suzukiSElt a K c d * suzukiDElt a K m) :
    u = c ∧ v = d ∧ l = m := by
  obtain ⟨p, hp, hu⟩ := (suzuki_borel_structure hK).2.2.2.2.2.2.1 _ (SD_mem u v l)
  have h1 := hu ((u, v), l) rfl
  have h2 := hu ((c, d), m) h
  have h3 := h1.trans h2.symm
  simp only [Prod.mk.injEq] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

@[expose] noncomputable def torusPart (g : suzukiB a K) : Kˣ :=
  Classical.choose (exists_SD hK g.2)

theorem torusPart_spec (g : suzukiB a K) :
    ∃ u v : K, (g : suzukiGroup a K) =
      suzukiSElt a K u v * suzukiDElt a K (torusPart hK g) := by
  obtain ⟨u, v, h⟩ := Classical.choose_spec (exists_SD hK g.2)
  exact ⟨u, v, h⟩

theorem torusPart_eq {g : suzukiB a K} {u v : K} {l : Kˣ}
    (h : (g : suzukiGroup a K) = suzukiSElt a K u v * suzukiDElt a K l) : torusPart hK g = l := by
  obtain ⟨u', v', h'⟩ := torusPart_spec hK g
  exact (SD_unique hK (h'.symm.trans h)).2.2

@[expose] noncomputable def torusHom : suzukiB a K →* Kˣ where
  toFun := torusPart hK
  map_one' := by
    refine torusPart_eq hK (u := 0) (v := 0) ?_
    rw [suzukiSElt_zero_zero hK, suzukiDElt_one, mul_one]
    rfl
  map_mul' g g' := by
    obtain ⟨u, v, h⟩ := torusPart_spec hK g
    obtain ⟨c, d, h'⟩ := torusPart_spec hK g'
    set l := torusPart hK g
    set m := torusPart hK g'
    refine torusPart_eq hK (u := u + (l⁻¹ : Kˣ) * c)
      (v := v + ((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * d + u ^ 2 ^ (a + 1) * ((l⁻¹ : Kˣ) * c))
      ?_
    rw [Subgroup.coe_mul, h, h']
    calc suzukiSElt a K u v * suzukiDElt a K l * (suzukiSElt a K c d * suzukiDElt a K m)
        = suzukiSElt a K u v * (suzukiDElt a K l * suzukiSElt a K c d * (suzukiDElt a K l)⁻¹) *
            (suzukiDElt a K l * suzukiDElt a K m) := by group
      _ = _ := by
        rw [suzukiDElt_conj' hK, suzukiDElt_mul, suzukiSElt_mul hK]

theorem torusHom_apply (g : suzukiB a K) : torusHom hK g = torusPart hK g := rfl

theorem torusHom_eq_one_iff (g : suzukiB a K) :
    torusHom hK g = 1 ↔ (g : suzukiGroup a K) ∈ suzukiU a K := by
  constructor
  · intro h1
    obtain ⟨u, v, h⟩ := torusPart_spec hK g
    rw [torusHom_apply] at h1
    rw [h, h1, suzukiDElt_one, mul_one]
    exact suzukiSElt_mem_suzukiU a K u v
  · intro hU
    obtain ⟨u, v, hg⟩ := (mem_suzukiU_iff hK).1 hU
    rw [torusHom_apply]
    refine torusPart_eq hK (u := u) (v := v) ?_
    rw [suzukiDElt_one, mul_one, hg]

theorem conj_suzukiSElt_zero (g : suzukiB a K) (z : K) :
    (g : suzukiGroup a K) * suzukiSElt a K 0 z * (g : suzukiGroup a K)⁻¹ =
      suzukiSElt a K 0 ((((torusPart hK g)⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * z) := by
  obtain ⟨u, v, h⟩ := torusPart_spec hK g
  set l := torusPart hK g
  rw [h]
  have hc := suzukiSElt_zero_commute hK
  calc suzukiSElt a K u v * suzukiDElt a K l * suzukiSElt a K 0 z *
        (suzukiSElt a K u v * suzukiDElt a K l)⁻¹
      = suzukiSElt a K u v * (suzukiDElt a K l * suzukiSElt a K 0 z * (suzukiDElt a K l)⁻¹) *
          (suzukiSElt a K u v)⁻¹ := by group
    _ = suzukiSElt a K u v *
          suzukiSElt a K 0 ((((l⁻¹ : Kˣ)) : K) ^ (2 ^ (a + 1) + 1) * z) *
          (suzukiSElt a K u v)⁻¹ := by
        rw [suzukiDElt_conj' hK]
        simp
    _ = _ := by
        rw [← hc ((((l⁻¹ : Kˣ)) : K) ^ (2 ^ (a + 1) + 1) * z) u v]
        group

theorem mem_suzukiU_of_pow_two {g : suzukiGroup a K} (hg : g ∈ suzukiB a K) {m : ℕ}
    (hm : g ^ 2 ^ m = 1) : g ∈ suzukiU a K := by
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact CFSG.ShultStronglyClosedTI.SuzukiModel.odd_two_pow_sub_one _ (by omega)
  have h1 : (torusHom hK ⟨g, hg⟩) ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : suzukiB a K) ^ 2 ^ m = 1 := Subtype.ext hm
    rw [this, map_one]
  have h2 : orderOf (torusHom hK ⟨g, hg⟩) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (torusHom hK ⟨g, hg⟩) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ m) (Nat.card Kˣ) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
  have h4 : orderOf (torusHom hK ⟨g, hg⟩) = 1 := (hcop.coprime_dvd_left h2).eq_one_of_dvd h3
  exact (torusHom_eq_one_iff hK ⟨g, hg⟩).1 (orderOf_eq_one_iff.1 h4)

end Torus

end CFSG.RankThree.PartOne.SEITZ10
