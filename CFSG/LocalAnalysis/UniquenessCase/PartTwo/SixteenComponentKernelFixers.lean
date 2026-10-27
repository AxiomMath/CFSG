module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.GroupTheory.ComponentImageUniqueness
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
public import CFSG.Quasithin.EmptyFaithful.R3c2Base
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s168e3_false_of_faithful_component_fixers
    (c : S168e3Ctx D V₀ V L hV)
    (h3sig : 3 ∈ D.sig)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
      barHom V₀ V hV c.m_le_stabTil)
    (C : Subgroup (Bar2 D.M))
    (hC : CFSG.IsComponent C)
    (hinj : Function.Injective (ψ.comp C.subtype))
    (hrank : CFSG.Open.pRank 3 ψ.range ≤ 2)
    (hfix : ∀ w : Vtil V₀ V hV, w ≠ 1 →
      ∃ b ∈ C.map ψ, orderOf b = 3 ∧ b w = w) : False := by
  classical
  have hbar3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) = 3 := by
    rw [← CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M]
    exact c.std.pRank_eq_three (p := 3) h3sig
  have h3dvd : 3 ∣ Nat.card ψ.ker := by
    by_contra hk
    have heq := R3c2.pRank_three_range_eq ψ hk
    have hrange3 : CFSG.Open.pRank 3 (⊤ : Subgroup ψ.range) = 3 := by
      rw [heq, hbar3]
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ψ.range) ≤ 2 := by
      rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) ψ.range]
    omega
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (p := 3) (hp := ⟨Nat.prime_three⟩) h3dvd
  have hzord' : orderOf (z : Bar2 D.M) = 3 :=
    (orderOf_injective ψ.ker.subtype ψ.ker.subtype_injective z).trans hzord
  have hzpsi : ψ (z : Bar2 D.M) = 1 := MonoidHom.mem_ker.mp z.2
  have hz1 : (z : Bar2 D.M) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord'
    omega
  have hperfC : Group.IsPerfect ↥C := hC.1.1
  have hna : ∃ a ∈ C.map ψ, ∃ b ∈ C.map ψ, a * b ≠ b * a := by
    have hnc : ¬ IsMulCommutative ↥C := by
      let _ : Group.IsPerfect ↥C := hperfC
      let _ : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
      exact Group.IsPerfect.not_isMulCommutative (G := ↥C)
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨ψ a, Subgroup.mem_map_of_mem ψ a.2, ψ b, Subgroup.mem_map_of_mem ψ b.2, ?_⟩
    intro h
    apply hab
    apply hinj
    simpa [map_mul] using h
  have hzC : (z : Bar2 D.M) ∈ Subgroup.centralizer (C : Set (Bar2 D.M)) :=
    CFSG.ComponentImage.mem_centralizer_of_map_mem_centralizer ψ hC hna
      (x := (z : Bar2 D.M)) (by rw [hzpsi]; exact Subgroup.one_mem _)
  have hfixM : ∀ w : Vtil V₀ V hV, w ≠ 1 → ∃ B : Subgroup ↥D.M, IsPGroup 3 B ∧
      ¬ IsCyclic ↥B ∧ ∀ b ∈ B, barHom V₀ V hV c.m_le_stabTil b w = w := by
    intro w hw
    obtain ⟨bH, hbHmem, hbHord, hbHfix⟩ := hfix w hw
    obtain ⟨b, hbC, hbψ⟩ := Subgroup.mem_map.mp hbHmem
    let bC : C := ⟨b, hbC⟩
    have hbord : orderOf b = 3 := by
      have h1 : orderOf (ψ b) = orderOf b := by
        have h := orderOf_injective (ψ.comp C.subtype) hinj bC
        have hval : (ψ.comp C.subtype) bC = ψ b := rfl
        rw [hval] at h
        exact h.trans (orderOf_injective C.subtype C.subtype_injective bC).symm
      rw [hbψ] at h1
      exact h1.symm.trans hbHord
    have hb1 : b ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hbord
      omega
    have hbpsi : ψ b ≠ 1 := by
      intro h
      have h2 : bH = 1 := by rw [← hbψ, h]
      rw [h2, orderOf_one] at hbHord
      omega
    have hbnot : b ∉ Subgroup.zpowers (z : Bar2 D.M) := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h1 : ψ b = 1 := by
        rw [← hk, map_zpow, hzpsi, one_zpow]
      have h2 : bH = 1 := by rw [← hbψ, h1]
      rw [h2, orderOf_one] at hbHord
      omega
    have hcomm : (z : Bar2 D.M) * b = b * (z : Bar2 D.M) :=
      ((Subgroup.mem_centralizer_iff.mp hzC) b hbC).symm
    have hAb := CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair
      Nat.prime_three hzord' hbord hbnot hcomm
    have hzA : (z : Bar2 D.M) ∈ Subgroup.zpowers (z : Bar2 D.M) ⊔ Subgroup.zpowers b :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hbA : b ∈ Subgroup.zpowers (z : Bar2 D.M) ⊔ Subgroup.zpowers b :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hbHfix' : ψ b w = w := by rw [hbψ]; exact hbHfix
    obtain ⟨B, hBp, hBc, hBfix⟩ := s168e3_noncyclic_fix_of_conj ψ Nat.prime_three hAb.1
      hzA hz1 hzpsi hbA hbpsi (g := 1) (by simpa using hbHfix')
    have hEb : B ≤ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).range := by
      rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact le_top
    obtain ⟨B', hB'p, hB'c, hB'le⟩ := exists_noncyclic_pGroup_map_le
      (φ := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) Nat.prime_three hEb hBp hBc
    refine ⟨B', hB'p, hB'c, fun b hb => ?_⟩
    have h1 : ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b) w = w := hBfix _ (hB'le b hb)
    have hbar : barHom V₀ V hV c.m_le_stabTil b =
        ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) b) := by
      rw [← hψ]
      rfl
    rw [hbar]
    exact h1
  exact s168e3_false_of_fix_M c Nat.prime_three h3sig hfixM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
