module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.A3Structure36ABasic

public section

namespace CFSG.Quasithin.F146Field.Case1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem mem_normalizer_iff_cjSub_eq {g : G} {A : Subgroup G} :
    g ∈ Subgroup.normalizer (A : Set G) ↔ cjSub g A = A := by
  rw [Subgroup.mem_normalizer_iff'']
  constructor
  · intro h
    ext x
    rw [mem_cjSub]
    exact (h x).symm
  · intro h x
    have hx := SetLike.ext_iff.mp h x
    rw [mem_cjSub] at hx
    exact hx.symm

theorem cjSub_injective (g : G) : Function.Injective (cjSub g : Subgroup G → Subgroup G) := by
  intro A B h
  have := congrArg (cjSub g⁻¹) h
  rwa [cjSub_inv_cjSub, cjSub_inv_cjSub] at this

theorem cjSub_cjSub_mul (s t : G) (K : Subgroup G) : cjSub s (cjSub t K) = cjSub (s * t) K := by
  ext x
  simp [mem_cjSub, mul_assoc]

variable [Finite G]

omit [Finite G] in
theorem cjSub_mem_cComp_of_mem {H K : Subgroup G} (hK : K ∈ cComp H) {g : G} (hg : g ∈ H) :
    cjSub g K ∈ cComp H :=
  map_conj_mem_cComp hK hg

theorem oTwoUpper_le_conjClosure {K T H : Subgroup G} (hT : IsPGroup 2 T) (hHK : H = K ⊔ T) :
    oTwoUpper H ≤ conjClosure K T := by
  refine oTwoUpper_le_of_pow_mem ?_
  have hnorm : H ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
    rw [hHK]
    exact sup_le ((le_conjClosure K T).trans Subgroup.le_normalizer)
      (le_normalizer_conjClosure K T)
  have hsup : T ⊔ conjClosure K T = H := by
    rw [hHK]
    exact le_antisymm (sup_le le_sup_right (A3.conjClosure_le_sup K T))
      (sup_le (le_sup_of_le_right (le_conjClosure K T)) le_sup_left)
  exact B6.isTwoQuotient_of_sup_eq hT hnorm hsup

theorem conjClosure_le_normalizer {K T H : Subgroup G} (hK : K ∈ cComp H) (hTH : T ≤ H) :
    conjClosure K T ≤ Subgroup.normalizer (K : Set G) := by
  refine conjClosure_le fun h hh z hz => ?_
  have h1 : cjSub h K ∈ cComp H := cjSub_mem_cComp_of_mem hK (hTH hh)
  refine le_normalizer_of_mem_cComp hK h1 ?_
  rw [mem_cjSub]
  have : h⁻¹ * (h * z * h⁻¹) * h = z := by group
  rw [this]
  exact hz

theorem oTwoUpper_le_normalizer {K T H : Subgroup G} (hK : K ∈ cComp H) (hT : IsPGroup 2 T)
    (hHK : H = K ⊔ T) : oTwoUpper H ≤ Subgroup.normalizer (K : Set G) :=
  (oTwoUpper_le_conjClosure hT hHK).trans
    (conjClosure_le_normalizer hK (by rw [hHK]; exact le_sup_right))

theorem le_oTwoUpper {K H : Subgroup G} (hK : K ∈ cComp H) : K ≤ oTwoUpper H :=
  B1Red.perfect_le_oTwoUpper' (le_of_mem_cComp hK) (A36A.isPerfect_of_mem_cComp hK)

theorem isSylowTwoOf_inf_cComp {K T H : Subgroup G} (hT : IsSylowTwoOf T H) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ T) : IsSylowTwoOf (T ⊓ K) K := by
  have hKΩ : K ≤ oTwoUpper H := le_oTwoUpper hK
  have hΩN : oTwoUpper H ≤ Subgroup.normalizer (K : Set G) :=
    oTwoUpper_le_normalizer hK hT.2.1 hHK
  have h1 : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hT (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have h2 := A4.isSylowTwoOf_inf_normal h1 hKΩ hΩN
  rwa [inf_assoc, inf_of_le_right hKΩ] at h2

omit [Finite G] in
theorem eq_sup_cjSub {K T H : Subgroup G} (hK : K ∈ cComp H) (hHK : H = K ⊔ T) {s : G}
    (hs : s ∈ T) : H = cjSub s K ⊔ T := by
  have hTH : T ≤ H := by rw [hHK]; exact le_sup_right
  apply le_antisymm
  · rw [hHK]
    refine sup_le (fun k hk => ?_) le_sup_right
    have h1 : s * k * s⁻¹ ∈ cjSub s K := by
      rw [mem_cjSub]
      have : s⁻¹ * (s * k * s⁻¹) * s = k := by group
      rw [this]
      exact hk
    have h2 := (cjSub s K ⊔ T).mul_mem ((cjSub s K ⊔ T).mul_mem
      (Subgroup.mem_sup_right (T.inv_mem hs)) (Subgroup.mem_sup_left h1))
      (Subgroup.mem_sup_right hs)
    have h3 : s⁻¹ * (s * k * s⁻¹) * s = k := by group
    rwa [h3] at h2
  · exact sup_le (le_of_mem_cComp (cjSub_mem_cComp_of_mem hK (hTH hs))) hTH

end CFSG.Quasithin.F146Field.Case1
