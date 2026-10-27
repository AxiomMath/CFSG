module

public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ8
public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ6

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_fsuM_of_cComp (hK : LocalSQTK G) (h36 : Vol2Native.A36CoreForSQTKCat)
    (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {VK K K1 D : Subgroup G} {z : G}
    (hL0T1 : fsuL0 T L ⊔ Ch10.T1 T L ≤ Subgroup.normalizer (VK : Set G))
    (hH2 : pCoreOf 2 (Subgroup.normalizer (VK : Set G)) ≠ ⊥)
    (hS : IsSylowTwoOf (Ch10.T1 T L) (Subgroup.normalizer (VK : Set G)))
    (hK1 : K1 ∈ cComp (Subgroup.normalizer (VK : Set G)))
    (hK1n : Subgroup.normalizer (VK : Set G) ≤ Subgroup.normalizer (K1 : Set G))
    (hKK1 : K ≤ K1) (hKp : ⁅K, K⁆ = K) (hKV : ¬ K ≤ Subgroup.centralizer (VK : Set G))
    (hDK1 : D ≤ K1) (hDC : D ≤ Subgroup.centralizer (VK : Set G)) (hDodd : Odd (Nat.card D))
    (hD3 : ¬ 3 ∣ Nat.card D) (hD1 : D ≠ ⊥) (hDD : ⁅D, Subgroup.zpowers z⁆ = D) (hzK : z ∈ K)
    (hz2 : z * z = 1) (hzQ : z ∉ pCoreOf 2 (Subgroup.normalizer (VK : Set G))) :
    D ≤ fsuM T L := by
  set H := Subgroup.normalizer (VK : Set G) with hHdef
  have hK1H : K1 ≤ H := le_of_mem_cComp hK1
  have hzK1 : z ∈ K1 := hKK1 hzK
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set Kb := modO2Image H K1 with hKb
  have hmemKb : ∀ {x : G} (hx : x ∈ K1), π ⟨x, hK1H hx⟩ ∈ Kb := fun hx =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have h36K := Vol2Native.lemma_1_2_1_four_core hK h36 hH2 hK1
  by_cases hq : CFSG.IsQuasisimple ↥Kb
  · exact (false_of_isQuasisimple hK1 hK1n hKK1 hKp hKV hDK1 hDC hDodd hD1 hDD hzK hq).elim
  obtain ⟨p, hp, hp2, ψ, hψs, hψk⟩ := exists_sl2_hom h36K hq
  obtain ⟨-, hFodd, -⟩ := fitting_facts h36K hq
  have : Fact p.Prime := ⟨hp⟩
  set zt : ↥Kb := ⟨π ⟨z, hK1H hzK1⟩, hmemKb hzK1⟩ with hzt
  have hzt2 : zt ^ 2 = 1 := by
    apply Subtype.ext
    rw [hzt, Subgroup.coe_pow, Subgroup.coe_mk, ← map_pow, sq]
    have : (⟨z, hK1H hzK1⟩ : ↥H) * ⟨z, hK1H hzK1⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
    rfl
  have hψz1 : ψ zt ≠ 1 := by
    intro h
    have hzF : zt ∈ CFSG.fittingSubgroup ↥Kb := hψk ▸ (MonoidHom.mem_ker.mpr h)
    have h1 : orderOf zt ∣ Nat.card (CFSG.fittingSubgroup ↥Kb) := by
      have := orderOf_dvd_natCard (⟨zt, hzF⟩ : ↥(CFSG.fittingSubgroup ↥Kb))
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf zt ∣ 2 := orderOf_dvd_of_pow_eq_one hzt2
    have h3 : orderOf zt = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at h1
        exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hFodd)
    have h4 : π ⟨z, hK1H hzK1⟩ = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
    exact hzQ (mem_pCoreOf_of_mk_eq_one h4)
  have hψz : ψ zt = -1 := C10E4.sl2_eq_neg_one (by omega) _ (by rw [← map_pow, hzt2, map_one])
    hψz1
  set Fb := (CFSG.fittingSubgroup ↥Kb).map Kb.subtype with hFb
  have hKbN : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have h1 := SecB.modO2Image_le_normalizer' (H := H) (A := H) (B := K1) hK1n
    have h2 : modO2Image H H = ⊤ := by
      rw [modO2Image, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rwa [h2] at h1
  have hFn : Fb.Normal := by
    refine ⟨fun f hf g => ?_⟩
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Kb) (CFSG.fittingSubgroup ↥Kb) (hKbN (Subgroup.mem_top g))
    exact (Subgroup.mem_normalizer_iff.mp h1 f).mp hf
  have hFnil : Group.IsNilpotent ↥Fb :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ Kb.subtype_injective)
  have hFF : Fb ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hFn, hFnil⟩
  have hDF : D ≤ oTwoFIn H := by
    rw [← hDD, Subgroup.commutator_le]
    intro d hd y hy
    have hdK1 := hDK1 hd
    have hyK1 : y ∈ K1 := (Subgroup.zpowers_le.mpr hzK1) hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    set dt : ↥Kb := ⟨π ⟨d, hK1H hdK1⟩, hmemKb hdK1⟩ with hdt
    set yt : ↥Kb := ⟨π ⟨z ^ n, hK1H hyK1⟩, hmemKb hyK1⟩ with hyt
    have hyzt : yt = zt ^ n := by
      apply Subtype.ext
      rw [hyt, hzt, Subgroup.coe_zpow, Subgroup.coe_mk, Subgroup.coe_mk, ← map_zpow]
      rfl
    have h1 : ψ ⁅dt, yt⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hyzt, map_zpow, hψz]
      exact ((sl2_commute_neg_one (ψ dt)).zpow_right n).eq
    have h2 : ⁅dt, yt⁆ ∈ CFSG.fittingSubgroup ↥Kb := hψk ▸ (MonoidHom.mem_ker.mpr h1)
    have h3 : π ⟨⁅d, z ^ n⁆, H.mul_mem (H.mul_mem (H.mul_mem (hK1H hdK1) (hK1H hyK1))
        (H.inv_mem (hK1H hdK1))) (H.inv_mem (hK1H hyK1))⟩ ∈
        CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := by
      refine hFF ⟨⁅dt, yt⁆, h2, ?_⟩
      rw [show (⟨⁅d, z ^ n⁆, H.mul_mem (H.mul_mem (H.mul_mem (hK1H hdK1) (hK1H hyK1))
          (H.inv_mem (hK1H hdK1))) (H.inv_mem (hK1H hyK1))⟩ : ↥H) =
          ⁅(⟨d, hK1H hdK1⟩ : ↥H), ⟨z ^ n, hK1H hyK1⟩⁆ from rfl, map_commutatorElement]
      rfl
    exact C2Six.mem_oTwoFIn_iff.mpr h3
  intro d hd
  have hdF := hDF hd
  refine mem_fsuM_of_coprime_three' hK h331 h37 h38 hyp hL0T1 hH2 hS hdF ?_
  have h1 : orderOf (π ⟨d, C2Six.oTwoFIn_le hdF⟩) ∣ orderOf d :=
    (orderOf_map_dvd π _).trans (Subgroup.orderOf_mk d _).dvd
  have h2 : orderOf d ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
    rwa [Subgroup.orderOf_mk] at this
  exact Nat.Coprime.coprime_dvd_left (h1.trans h2)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3).symm

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
