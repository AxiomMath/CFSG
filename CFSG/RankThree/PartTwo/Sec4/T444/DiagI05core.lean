module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem ys03_I05_zpow_of_card_three {G : Type} [Group G] (K : Subgroup G) (hK : Nat.card K = 3)
    {c : G} (hcK : c ∈ K) (hc1 : c ≠ 1) : ∀ w ∈ K, ∃ k : ℤ, c ^ k = w := by
  have hord : orderOf c = 3 := by
    have hdvd : orderOf c ∣ 3 := by
      rw [← hK]
      exact Subgroup.orderOf_dvd_natCard K hcK
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hle : Subgroup.zpowers c ≤ K := Subgroup.zpowers_le.mpr hcK
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have heq : Subgroup.zpowers c = K :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [Nat.card_zpowers, hord, hK]))
  intro w hw
  have hw' : w ∈ Subgroup.zpowers c := by
    rw [heq]
    exact hw
  exact Subgroup.mem_zpowers_iff.mp hw'

theorem ys03_I05_le_of_card_three {Y : Type} [Group Y] {S J' : Subgroup Y} {K : Subgroup ↥S}
    (hK : Nat.card K = 3) {c : ↥S} (hcK : c ∈ K) (hc1 : c ≠ 1) (hcJ : (c : Y) ∈ J') :
    ∀ w ∈ K, (w : Y) ∈ J' := by
  intro w hw
  obtain ⟨k, rfl⟩ := ys03_I05_zpow_of_card_three K hK hcK hc1 w hw
  rw [Subgroup.coe_zpow]
  exact zpow_mem hcJ k

theorem ys03_I05core {Y : Type} [Group Y] {A' L' J' S : Subgroup Y} {z : Y}
    (hLJ : ∀ x ∈ L', ∀ y ∈ J', Commute x y) (hAJ : A' ≤ Subgroup.normalizer (J' : Set Y))
    (hA'S : A' ≤ S) (hL'S : L' ≤ S) (hS : S ≤ A' ⊔ L')
    {U V : Subgroup ↥S} (hUV : U ⊔ V = ⊤) (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hU : IsHeisThree U)
    (hVe : Nonempty (↥V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup ↥S) = 3) (hVL : V.map S.subtype = L')
    (hz : z ∈ A' ⊓ J') (hz1 : z ≠ 1) :
    (Subgroup.center ↥L').map L'.subtype ≤ J' := by
  have hcommLJ : ∀ x ∈ L', ∀ y ∈ J', x * y * x⁻¹ = y := by
    intro x hx y hy
    rw [(hLJ x hx y hy).eq, mul_inv_cancel_right]
  have hLN : L' ≤ Subgroup.normalizer (J' : Set Y) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcommLJ x hx h hh]
      exact hh
    · intro hh
      have h1 := hcommLJ x⁻¹ (inv_mem hx) (x * h * x⁻¹) hh
      have h2 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rw [h2] at h1
      rw [← h1] at hh
      exact hh
  have hSN : S ≤ Subgroup.normalizer (J' : Set Y) := hS.trans (sup_le hAJ hLN)
  have hzJ : z ∈ J' := hz.2
  have hzS : z ∈ S := hA'S hz.1
  obtain ⟨zS, hzSval⟩ : ∃ zS : ↥S, (zS : Y) = z := ⟨⟨z, hzS⟩, rfl⟩
  have hzSV : ∀ v ∈ V, v * zS = zS * v := by
    intro v hv
    apply Subtype.ext
    have hvL : ((v : ↥S) : Y) ∈ L' := by
      rw [← hVL]
      exact Subgroup.mem_map_of_mem S.subtype hv
    have hc := hLJ _ hvL z hzJ
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzSval]
    exact hc.eq
  have hzU : zS ∈ U := by
    rw [← KFacts.L34.centralizer_eq_of_isHeisSL hUV hcomm hVe h3, Subgroup.mem_centralizer_iff]
    exact hzSV
  obtain ⟨zU, hzUval⟩ : ∃ zU : ↥U, (zU : ↥S) = zS := ⟨⟨zS, hzU⟩, rfl⟩
  have hUVc := KFacts.L34.inf_eq_map_center_left hcomm hU h3
  have key : ∀ w ∈ U ⊓ V, ((w : ↥S) : Y) ∈ J' := by
    by_cases hZ : zU ∈ Subgroup.center ↥U
    ·
      have hzUV : zS ∈ U ⊓ V := by
        rw [hUVc]
        exact ⟨zU, hZ, hzUval⟩
      have hzne : zS ≠ 1 := by
        intro h
        apply hz1
        have h' := congrArg Subtype.val h
        rw [hzSval] at h'
        exact h'
      exact ys03_I05_le_of_card_three h3 hzUV hzne (by rw [hzSval]; exact hzJ)
    ·
      rw [Subgroup.mem_center_iff, not_forall] at hZ
      obtain ⟨g, hg⟩ := hZ
      have hcomm_mem : ⁅g, zU⁆ ∈ Subgroup.center ↥U := by
        rw [← hU.1.2.1]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top zU)
      have hne : ⁅g, zU⁆ ≠ 1 := by
        intro h
        exact hg (commutatorElement_eq_one_iff_mul_comm.mp h)
      have hcUV : ((⁅g, zU⁆ : ↥U) : ↥S) ∈ U ⊓ V := by
        rw [hUVc]
        exact ⟨⁅g, zU⁆, hcomm_mem, rfl⟩
      have hcne : ((⁅g, zU⁆ : ↥U) : ↥S) ≠ 1 := by
        intro h
        exact hne (Subtype.ext h)
      have hgN : ∀ h : Y, h ∈ J' ↔ ((g : ↥S) : Y) * h * ((g : ↥S) : Y)⁻¹ ∈ J' :=
        fun h => Subgroup.mem_normalizer_iff.mp (hSN (g : ↥S).2) h
      have hzUY : ((zU : ↥S) : Y) = z := by
        rw [hzUval, hzSval]
      have hcJ : (((⁅g, zU⁆ : ↥U) : ↥S) : Y) ∈ J' := by
        have hval : (((⁅g, zU⁆ : ↥U) : ↥S) : Y) =
            ((g : ↥S) : Y) * z * ((g : ↥S) : Y)⁻¹ * z⁻¹ := by
          rw [commutatorElement_def]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzUY]
        rw [hval]
        exact mul_mem ((hgN z).mp hzJ) (inv_mem hzJ)
      exact ys03_I05_le_of_card_three h3 hcUV hcne hcJ
  have hUVr := KFacts.L34.inf_eq_map_center_right hcomm hVe h3
  rintro _ ⟨a, ha, rfl⟩
  have haV : ((a : ↥L') : Y) ∈ V.map S.subtype := by
    rw [hVL]
    exact a.2
  obtain ⟨v, hv, hva⟩ := Subgroup.mem_map.mp haV
  have hva' : ((v : ↥S) : Y) = ((a : ↥L') : Y) := hva
  have hvc : (⟨v, hv⟩ : ↥V) ∈ Subgroup.center ↥V := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply Subtype.ext
    have hwL : ((w : ↥S) : Y) ∈ L' := by
      rw [← hVL]
      exact Subgroup.mem_map_of_mem S.subtype w.2
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨((w : ↥S) : Y), hwL⟩)
    show ((w : ↥S) : Y) * ((v : ↥S) : Y) = ((v : ↥S) : Y) * ((w : ↥S) : Y)
    rw [hva']
    exact hc
  have hvU : v ∈ U ⊓ V := by
    rw [hUVr]
    exact ⟨⟨v, hv⟩, hvc, rfl⟩
  have hfin := key v hvU
  rw [hva'] at hfin
  exact hfin

end CFSG.RankThree.PartTwo.Sec4

end
