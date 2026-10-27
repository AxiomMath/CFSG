module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge

public section

namespace CFSG.StandardType.FF81

private theorem cOdd_sylow_central_complement {G : Type*} [Group G] [Finite G] {b : G}
    (D : Subgroup G) (hbD : b ∈ D) (hord : orderOf b = 3)
    (hcenterD : D ≤ Subgroup.centralizer ({b} : Set G))
    (hsyl : ∀ Q : Subgroup G, Q ≤ D → IsPGroup 3 Q → Subgroup.zpowers b ≤ Q →
      Q = Subgroup.zpowers b) :
    ∃ (N : Subgroup ↥D) (P : Sylow 3 ↥D), (P : Subgroup ↥D).IsComplement' N ∧
      N.Normal ∧ Nat.card (P : Subgroup ↥D) = 3 ∧ Nat.card D = 3 * Nat.card N := by
  classical
  have hzD : Subgroup.zpowers b ≤ D := Subgroup.zpowers_le.mpr hbD
  have hP0p : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf D) := by
    have h : IsPGroup 3 (Subgroup.zpowers b) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hord, pow_one]
    exact h.comap_subtype
  have hsyl_max : ∀ Q : Subgroup ↥D, IsPGroup 3 Q →
      (Subgroup.zpowers b).subgroupOf D ≤ Q → Q = (Subgroup.zpowers b).subgroupOf D := by
    intro Q hQ hle
    have hQmap : IsPGroup 3 (Q.map D.subtype) := hQ.map D.subtype
    have hle' : Subgroup.zpowers b ≤ Q.map D.subtype := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hzD hx⟩, hle hx, rfl⟩
    have hEq : Q.map D.subtype = Subgroup.zpowers b :=
      hsyl (Q.map D.subtype) (Subgroup.map_subtype_le Q) hQmap hle'
    calc Q = (Q.map D.subtype).comap D.subtype :=
          (Subgroup.comap_map_eq_self (f := D.subtype) (H := Q) (by simp)).symm
      _ = (Subgroup.zpowers b).comap D.subtype := by rw [hEq]
      _ = (Subgroup.zpowers b).subgroupOf D := rfl
  obtain ⟨Q, hQle⟩ := hP0p.exists_le_sylow
  have hQP0 : Q = (Subgroup.zpowers b).subgroupOf D := hsyl_max Q Q.isPGroup' hQle
  have hP0index : ¬ 3 ∣ ((Subgroup.zpowers b).subgroupOf D).index := by
    rw [← hQP0]
    exact Q.not_dvd_index
  let P : Sylow 3 ↥D := hP0p.toSylow hP0index
  have hPcoe : (P : Subgroup ↥D) = (Subgroup.zpowers b).subgroupOf D := rfl
  have hPcard : Nat.card (P : Subgroup ↥D) = 3 := by
    rw [hPcoe, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzD).toEquiv, Nat.card_zpowers, hord]
  have hPcenter : (P : Subgroup ↥D) ≤ Subgroup.center ↥D := by
    rw [hPcoe]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : G) ∈ Subgroup.zpowers b := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
    ext
    show (y : G) * (x : G) = (x : G) * (y : G)
    rw [← hk]
    have hyb : Commute (y : G) b :=
      (Subgroup.mem_centralizer_iff.mp (hcenterD y.2) b (Set.mem_singleton b)).symm
    exact (hyb.zpow_right k).eq
  obtain ⟨N, hNnormal, hNcomp⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.exists_normal_complement_of_le_center P hPcenter
  have hcardD : Nat.card D = 3 * Nat.card N := by
    rw [← hNcomp.card_mul_card, hPcard]
  exact ⟨N, P, hNcomp, hNnormal, hPcard, hcardD⟩

private theorem cOdd_mem_iff_not_dvd_order {H : Type*} [Group H] [Finite H] {N : Subgroup H}
    (hN : N.Normal) (P : Sylow 3 H) (hcomp : (P : Subgroup H).IsComplement' N)
    (hPcard : Nat.card (P : Subgroup H) = 3) (d : H) : d ∈ N ↔ ¬ 3 ∣ orderOf d := by
  classical
  haveI : N.Normal := hN
  have hcard : Nat.card (H ⧸ N) = 3 := by
    rw [← Subgroup.index_eq_card (H := N), hcomp.index_eq_card, hPcard]
  have h3N : ¬ 3 ∣ Nat.card N := by
    rw [← hcomp.symm.index_eq_card]
    exact P.not_dvd_index
  constructor
  · intro hd h3
    exact h3N (h3.trans (Subgroup.orderOf_dvd_natCard N hd))
  · intro hd3
    have hq3 : (QuotientGroup.mk d : H ⧸ N) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := H ⧸ N) (x := QuotientGroup.mk d)
      rwa [hcard] at h
    have hdiv3 : orderOf (QuotientGroup.mk d : H ⧸ N) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr hq3
    have hdivd : orderOf (QuotientGroup.mk d : H ⧸ N) ∣ orderOf d :=
      orderOf_map_dvd (QuotientGroup.mk' N) d
    have hq1 : orderOf (QuotientGroup.mk d : H ⧸ N) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
      · exact h
      · rw [h] at hdivd
        exact absurd hdivd hd3
    exact (QuotientGroup.eq_one_iff d).mp (orderOf_eq_one_iff.mp hq1)

private theorem cOdd_normal_centralizer {G : Type*} [Group G] [Finite G] {b : G}
    {L D N' : Subgroup G}
    (hD : D = Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    (hnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hN'leD : N' ≤ D) (hN'order : ∀ d ∈ D, d ∈ N' ↔ ¬ 3 ∣ orderOf d) :
    (N'.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal := by
  constructor
  intro n hn g
  change ((g : G) * (n : G) * (g : G)⁻¹) ∈ N'
  have hnI : (n : G) ∈ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer ({b} : Set G) := by
    rw [← hD]
    exact hN'leD hn
  have hn3 : ¬ 3 ∣ orderOf (n : G) := (hN'order (n : G) (hN'leD hn)).mp hn
  have hgL : (g : G) * (n : G) * (g : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : (g : G)⁻¹ * l * (g : G) ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.inv_mem _ g.2)) l).mp hl
    have hnl : ((g : G)⁻¹ * l * (g : G)) * (n : G) =
        (n : G) * ((g : G)⁻¹ * l * (g : G)) :=
      Subgroup.mem_centralizer_iff.mp hnI.1 _ hl'
    calc l * ((g : G) * (n : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * l * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * l * (g : G))) * (g : G)⁻¹ := by rw [hnl]
      _ = ((g : G) * (n : G) * (g : G)⁻¹) * l := by group
  have hgC : (g : G) * (n : G) * (g : G)⁻¹ ∈
      Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hnI.2) (Subgroup.inv_mem _ g.2)
  have hgD : (g : G) * (n : G) * (g : G)⁻¹ ∈ D := by
    rw [hD]
    exact ⟨hgL, hgC⟩
  have hord : orderOf ((g : G) * (n : G) * (g : G)⁻¹) = orderOf (n : G) := by
    have h := orderOf_injective (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective (n : G)
    simpa [MulAut.conj_apply] using h
  exact (hN'order _ hgD).mpr (by rw [hord]; exact hn3)

theorem exists_normal_compl_centralizer_inf_centralizer {G : Type} [Group G] [Finite G] {n : ℕ}
    {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} (hA : HypA G n b L) (hloc : LocalFacts b L z) :
    ∃ N : Subgroup G,
      N ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) ∧
      (N.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card N ∧
      Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G)) =
        3 * Nat.card N := by
  classical
  let D : Subgroup G :=
    Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
  have hbD : b ∈ D := by
    refine ⟨?_, ?_⟩
    · change b ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hA.le hy) b (Set.mem_singleton b)).symm
    · change b ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      rfl
  have hsylD : ∀ Q : Subgroup G, Q ≤ D → IsPGroup 3 Q → Subgroup.zpowers b ≤ Q →
      Q = Subgroup.zpowers b := by
    intro Q hQD hQ hbQ
    exact hloc.syl Q (hQD.trans inf_le_left) (hQD.trans inf_le_right) hQ hbQ
  obtain ⟨N, P, hNcomp, hNnormal, hPcard, hcardD⟩ :=
    cOdd_sylow_central_complement D hbD hA.ord inf_le_right hsylD
  let N' : Subgroup G := N.map D.subtype
  have hN'leD : N' ≤ D := Subgroup.map_subtype_le N
  have hN'card : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective D.subtype_injective
  have hN'order : ∀ d ∈ D, d ∈ N' ↔ ¬ 3 ∣ orderOf d := by
    intro d hd
    have hmem : (⟨d, hd⟩ : ↥D) ∈ N ↔ d ∈ N' := by
      constructor
      · intro hn
        exact Subgroup.mem_map.mpr ⟨⟨d, hd⟩, hn, rfl⟩
      · intro hd'
        obtain ⟨m, hm, hmd⟩ := Subgroup.mem_map.mp hd'
        have hm' : m = ⟨d, hd⟩ := Subtype.ext hmd
        rw [hm'] at hm
        exact hm
    have h := cOdd_mem_iff_not_dvd_order hNnormal P hNcomp hPcard ⟨d, hd⟩
    rw [hmem] at h
    simpa [Subgroup.orderOf_mk] using h
  have hN'normal : (N'.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal :=
    cOdd_normal_centralizer rfl hA.nor hN'leD hN'order
  have h3N : ¬ 3 ∣ Nat.card N := hNcomp.symm.index_eq_card ▸ P.not_dvd_index
  refine ⟨N', fun x hx => ⟨(hN'leD hx).2, (hN'leD hx).1⟩, hN'normal, hN'card.symm ▸ h3N, ?_⟩
  rw [inf_comm, hcardD, hN'card]

theorem odd_card_centralizer_inf_centralizer {G : Type} [Group G] [Finite G] {n : ℕ} {b t : G}
    {L : Subgroup G} {K : ℕ → Subgroup G} (hA : HypA G n b L) (hU : Upstream n b L K t) :
    Odd (Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G))) := by
  obtain ⟨z, hz, hF⟩ := hU
  obtain ⟨N, hND, hNnormal, h3N, hcard⟩ :=
    exists_normal_compl_centralizer_inf_centralizer hA hz.loc
  rw [hcard]
  exact (by norm_num : Odd 3).mul (hF.odd_core N (hND.trans inf_le_left) hNnormal h3N)

end CFSG.StandardType.FF81

end
