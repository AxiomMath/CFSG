module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSplit
public import CFSG.LocalAnalysis.StandardType.GGHalfCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

theorem centralizer_closure_pair_eq_inf {G : Type*} [Group G] (x z : G) :
    Subgroup.centralizer (Subgroup.closure ({x, z} : Set G)) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext w
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem ggQ2Lin_exists_z (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) :
    ∃ z : G, z ∈ D ∧ z ∉ Subgroup.zpowers x ∧ D = Subgroup.closure ({x, z} : Set G) := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  obtain ⟨hDleB, hElemD, hcardD, hxD, -, -, -⟩ := hDJ.1
  have hcardD9 : Nat.card D = 9 := by rw [hcardD, hp]; norm_num
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hcfg.orderOf_x, hp]
  have hzpxD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
  have hne : D ≠ Subgroup.zpowers x := by
    intro heq
    rw [heq, hxcard] at hcardD9
    omega
  obtain ⟨z, hzD, hzx⟩ : ∃ z : G, z ∈ D ∧ z ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hzpxD)
  refine ⟨z, hzD, hzx, ?_⟩
  have hxD' : x ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hzD' : z ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hle : Subgroup.closure ({x, z} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hxD
    · exact hzD
  have hlt : Subgroup.zpowers x < Subgroup.closure ({x, z} : Set G) := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hxD') ?_
    intro heq
    exact hzx (heq ▸ hzD')
  have hdvd : Nat.card (Subgroup.closure ({x, z} : Set G)) ∣ 9 := by
    simpa [hcardD9] using Subgroup.card_dvd_of_le hle
  have h3dvd : 3 ∣ Nat.card (Subgroup.closure ({x, z} : Set G)) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxD')
    rwa [hxcard] at h
  have hgt : 3 < Nat.card (Subgroup.closure ({x, z} : Set G)) := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hxcard] at this
  have hcard : Nat.card (Subgroup.closure ({x, z} : Set G)) = 9 := by
    have hle9 : Nat.card (Subgroup.closure ({x, z} : Set G)) ≤ 9 :=
      Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card (Subgroup.closure ({x, z} : Set G)) <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardD9])).symm

theorem ggQ2Lin_exists_t {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ) :
    ∃ (z : G) (t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) (a : ℤ),
      t ∈ GGHalf.halfTorus n ∧ t ≠ 1 ∧ z ∈ D ∧ z ∉ Subgroup.zpowers x ∧
        z = x ^ a * ψ t := by
  obtain ⟨z, hzD, hzx, -⟩ := ggQ2Lin_exists_z hS hp
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hDleBs : D ≤ Bs := hDJ.1.1.trans hcfg.2.1.1
  have hcent : Subgroup.zpowers x ≤
      Subgroup.centralizer (((GGHalf.halfTorus n).map ψ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
    have hbtL : ψ t ∈ L := by rw [← hF.range]; exact ⟨t, rfl⟩
    have hcomm : Commute x (ψ t) := by
      rw [Commute]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLx hbtL)).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk]
    exact (hcomm.zpow_left k).symm
  have hnormal : Subgroup.zpowers x ≤
      Subgroup.normalizer (((GGHalf.halfTorus n).map ψ : Subgroup G) : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hzmem : z ∈ (((Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ : Subgroup G)) :
      Set G) := by
    rw [← hBs]
    exact hDleBs hzD
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x)
    ((GGHalf.halfTorus n).map ψ) hnormal, Set.mem_mul] at hzmem
  obtain ⟨a, ha, b, hb, hzab⟩ := hzmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
  refine ⟨z, t, k, ht, ?_, hzD, hzx, ?_⟩
  · intro h1
    apply hzx
    rw [← hzab, ← hk, h1, map_one, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  · rw [← hzab, ← hk]

theorem ggQ2Lin_inf_centralizer_eq_map {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) :
    L ⊓ Subgroup.centralizer ({z} : Set G) =
      (Subgroup.centralizer ({t} :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))).map ψ := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  ext l
  constructor
  · rintro ⟨hlL, hlC⟩
    rw [← hF.range] at hlL
    obtain ⟨s, rfl⟩ := hlL
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hzs : Commute (ψ s) z := Subgroup.mem_centralizer_singleton_iff.mp hlC
    have hxs : Commute x (ψ s) :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (hLx (by rw [← hF.range]; exact ⟨s, rfl⟩))).symm
    have hpsi_t : ψ t = x ^ (-a) * z := by
      rw [hz]
      group
    have hmain : Commute (ψ s) (ψ t) := by
      rw [hpsi_t]
      exact (hxs.symm.zpow_right (-a)).mul_right hzs
    change s * t = t * s
    exact hF.inj (by rw [map_mul, map_mul]; exact hmain.eq)
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hF.range]
      exact ⟨s, rfl⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hst : Commute s t := Subgroup.mem_centralizer_singleton_iff.mp hs
      have hxs : Commute x (ψ s) :=
        (Subgroup.mem_centralizer_singleton_iff.mp
          (hLx (by rw [← hF.range]; exact ⟨s, rfl⟩))).symm
      have hpsi : Commute (ψ s) (ψ t) := by
        change ψ s * ψ t = ψ t * ψ s
        rw [← map_mul, ← map_mul]
        exact congrArg ψ hst.eq
      have hxsa : Commute (ψ s) (x ^ a) := hxs.symm.zpow_right a
      rw [hz]
      exact hxsa.mul_right hpsi

theorem ggQ2Lin_layer_eq {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t)
    (hDclos : D = Subgroup.closure ({x, z} : Set G)) :
    J = (LargeEvenLayer (Subgroup.centralizer ({t} :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)))).map ψ ∧
      IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))))
        (Subgroup.centralizer ({t} :
          Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))) := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  obtain ⟨-, -, -, -, hKlayer, hKcomp, -⟩ := hDJ.1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [hDclos, centralizer_closure_pair_eq_inf]
  have hCDL : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx]
  have hJlayer : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [hKlayer, hCDL]
  have hmapC : L ⊓ Subgroup.centralizer ({z} : Set G) =
      (Subgroup.centralizer ({t} :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))).map ψ :=
    ggQ2Lin_inf_centralizer_eq_map hS hF hz
  have hJmap : J = (LargeEvenLayer (Subgroup.centralizer ({t} :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)))).map ψ := by
    rw [hJlayer, hmapC, largeEvenLayer_map_of_injective ψ hF.inj]
  have hKcomp' : IsComponentOf J (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hCDL]
    exact hKcomp
  have hcomp : IsComponentOf J ((Subgroup.centralizer ({t} :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))).map ψ) := by
    rw [← hmapC]
    exact hKcomp'
  obtain ⟨hcomp0, -⟩ := isComponentOf_comap_of_injective ψ hF.inj hcomp
  have hJ0 : J.comap ψ = LargeEvenLayer (Subgroup.centralizer ({t} :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))) := by
    rw [hJmap]
    exact Subgroup.comap_map_eq_self_of_injective hF.inj _
  refine ⟨hJmap, ?_⟩
  rw [← hJ0]
  exact hcomp0

theorem ggQ2Lin_J_card_or {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n) (ht1 : t ≠ 1)
    (hDclos : D = Subgroup.closure ({x, z} : Set G)) :
    Nat.card J = Nat.card (Matrix.SpecialLinearGroup
        (Fin (GGHalf.supp t / 2)) (GaloisField 2 2)) ∨
      Nat.card J = Nat.card (Matrix.SpecialLinearGroup
        (Fin (n + 1 - GGHalf.supp t)) GGHalf.F2) := by
  obtain ⟨hJ, hcomp⟩ := ggQ2Lin_layer_eq hS hF hz hDclos
  have hcard : Nat.card J = Nat.card (LargeEvenLayer (Subgroup.centralizer ({t} :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)))) := by
    rw [hJ, Subgroup.card_map_of_injective hF.inj]
  rcases GGHalf.card_component_centralizer ht ht1 hcomp with h | h
  · exact Or.inl (hcard.trans h)
  · exact Or.inr (hcard.trans h)

end CFSG.StandardType

end
