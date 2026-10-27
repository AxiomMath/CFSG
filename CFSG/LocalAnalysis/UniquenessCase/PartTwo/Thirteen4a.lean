module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s13_exists_conj_into_M (D : Data G) {X : Subgroup G} (hXM : X ≤ D.M)
    (hX : X ∉ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M) :
    ∃ g : G, g ∉ D.M ∧ X.map (MulAut.conj g).toMonoidHom ≤ D.M := by
  rw [CFSG.LocalAnalysis.RankThreeUC.uniqueSet, Set.mem_setOf_eq, not_and] at hX
  have hq : ¬ (∀ h : G, X ≤ D.M.map (MulAut.conj h).toMonoidHom →
      D.M.map (MulAut.conj h).toMonoidHom = D.M) := hX hXM
  push_neg at hq
  obtain ⟨h, hXh, hMh⟩ := hq
  refine ⟨h⁻¹, ?_, ?_⟩
  · intro hinv
    have hh : h ∈ D.M := by simpa using D.M.inv_mem hinv
    exact hMh (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp (hXh hy)
    rw [← hmy]
    have hconj : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom m) = m := by
      change MulAut.conj h⁻¹ (MulAut.conj h m) = m
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hconj]
    exact hm

theorem s13_normalizer_map_conj_le {X M : Subgroup G} (g : G)
    (h : Subgroup.normalizer (X : Set G) ≤ M) :
    Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      M.map (MulAut.conj g).toMonoidHom := by
  rw [← Subgroup.map_equiv_normalizer_eq X (MulAut.conj g)]
  exact Subgroup.map_mono h

theorem s13_not_dvd_card_cent {M Y : Subgroup G} {q : ℕ} (hse : IsStronglyPEmbedded q M)
    {g : G} (hg : g ∉ M)
    (hN : Subgroup.normalizer (Y : Set G) ≤ M.map (MulAut.conj g).toMonoidHom) :
    ¬ q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (Y : Set G)) := by
  intro hq
  have hle : M ⊓ Subgroup.centralizer (Y : Set G) ≤
      M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    inf_le_inf_left M ((Subgroup.centralizer_le_normalizer (Y : Set G)).trans hN)
  have hdvd := Subgroup.card_dvd_of_le hle
  exact hse.2.2 g hg (hq.trans hdvd)

theorem s13_dvd_card_cent_self {M Y : Subgroup G} {r : ℕ} (hr : r.Prime) (hYM : Y ≤ M)
    (hY : Nat.card Y = r) : r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (Y : Set G)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsCyclic ↥Y := isCyclic_of_prime_card (α := ↥Y) hY
  have hcent : Y ≤ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    infer_instance
  have hle : Y ≤ M ⊓ Subgroup.centralizer (Y : Set G) := le_inf hYM hcent
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [hY] at hdvd

theorem s13_card_map_conj (X : Subgroup G) (g : G) :
    Nat.card ↥(X.map (MulAut.conj g).toMonoidHom) = Nat.card X := by
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem s13_barImage_le_sup_centralizer {M Y K : Subgroup G} (hKM : K ≤ M)
    (h : Y ≤ K ⊔ cMStar M K) :
    barImage M Y ≤ barImage M K ⊔ Subgroup.centralizer (barImage M K : Set (Bar2 M)) := by
  have hc : cMStar M K ≤ M := s13_barPreimage_le M (Subgroup.centralizer (barImage M K))
  have hsup : barImage M (K ⊔ cMStar M K) =
      barImage M K ⊔ Subgroup.centralizer (barImage M K : Set (Bar2 M)) := by
    rw [s13_barImage_sup hKM hc, s13_barImage_cMStar]
  exact (Subgroup.map_mono (Subgroup.subgroupOf_mono M h)).trans (le_of_eq hsup)

theorem s13_r_dvd_card_bar (D : Data G) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hse : IsStronglyPEmbedded p D.M) (hr : r.Prime) (hr2 : r ≠ 2) {Y : Subgroup G}
    (hYM : Y ≤ D.M) (hY : Nat.card Y = r) {g : G} (hg : g ∉ D.M)
    (hN : Subgroup.normalizer (Y : Set G) ≤ D.M.map (MulAut.conj g).toMonoidHom)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hin : Y ≤ K ⊔ cMStar D.M K)
    (hpK : p ∣ Nat.card ↥(barImage D.M K)) : r ∣ Nat.card ↥(barImage D.M K) := by
  by_contra hnr
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hin' : barImage D.M Y ≤ barImage D.M K ⊔
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) :=
    s13_barImage_le_sup_centralizer hKM hin
  have hpow : ∀ y ∈ barImage D.M Y, y ^ r = 1 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hzY : (z : G) ∈ Y := (Subgroup.mem_subgroupOf).mp hz
    have hzorder : orderOf (z : G) ∣ r := by
      have hdvd := Subgroup.orderOf_dvd_natCard Y hzY
      rwa [hY] at hdvd
    have hzrG : (z : G) ^ r = 1 := orderOf_dvd_iff_pow_eq_one.mp hzorder
    have hzr : z ^ r = 1 := Subtype.ext (by simpa using hzrG)
    rw [← map_pow, hzr, map_one]
  have hcentY : barImage D.M Y ≤
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) := by
    intro y hy
    by_contra hyc
    exact hnr (s13_prime_dvd_card_of_mem_sup_centralizer (barImage D.M K)
      (hin' hy) hyc hr (hpow y hy))
  obtain ⟨s, hsK, hs⟩ := s13_exists_element_of_dvd (barImage D.M K) hp hpK
  have hcent_s : barImage D.M Y ≤ Subgroup.centralizer ({s} : Set (Bar2 D.M)) :=
    hcentY.trans (Subgroup.centralizer_le (by
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      rwa [ht]))
  have hYp : IsPGroup r Y := IsPGroup.of_card (n := 1) (by simpa using hY)
  have hdvd : p ∣ Nat.card ↥(D.M ⊓ Subgroup.centralizer (Y : Set G)) :=
    s13_cop hp hp2 hr hr2 hYM hYp hs hcent_s
  exact s13_not_dvd_card_cent hse hg hN hdvd

theorem s13_thin_of_not_unitary (D : Data G) (hS : Setting13 D) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hnu : ¬ ∃ m : ℕ, IsU3 (Bar2 K) m) : Thin13 K := by
  rcases hS.hyp131.thinOrU3 K hK with h | ⟨n, _, hn⟩
  · exact h
  · exact absurd ⟨n, hn⟩ hnu

theorem s13_pRank_barImage_le_one {M K : Subgroup G} (hKM : K ≤ M) (hK : Thin13 K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (barImage M K) ≤ 1 := by
  rw [s13_pRank_barImage hp hp2 hKM]
  exact hK p hp hp2

theorem s13_hcomp (D : Data G) (hS : Setting13 D) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hse : IsStronglyPEmbedded p D.M) (hr : r.Prime) (hr2 : r ≠ 2) {Y : Subgroup G}
    (hYM : Y ≤ D.M) (hY : Nat.card Y = r) {g : G} (hg : g ∉ D.M)
    (hN : Subgroup.normalizer (Y : Set G) ≤ D.M.map (MulAut.conj g).toMonoidHom)
    (hall : ∀ K ∈ calC D.M, Y ≤ K ⊔ cMStar D.M K)
    (hnu : ∀ K ∈ calC D.M, ¬ ∃ m : ℕ, IsU3 (Bar2 K) m) :
    ∀ J : Subgroup (Bar2 D.M), CFSG.IsComponent J → p ∣ Nat.card J →
      CFSG.Open.pRank p J ≤ CFSG.Open.pRank r J := by
  intro J hJ hpJ
  obtain ⟨K, hK, rfl⟩ := s13_exists_calC_of_component D.M hJ
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hthin : Thin13 K := s13_thin_of_not_unitary D hS hK (hnu K hK)
  have h1 : CFSG.Open.pRank p (barImage D.M K) ≤ 1 :=
    s13_pRank_barImage_le_one hKM hthin hp hp2
  have hrd : r ∣ Nat.card ↥(barImage D.M K) :=
    s13_r_dvd_card_bar D hp hp2 hse hr hr2 hYM hY hg hN hK (hall K hK) hpJ
  have h2 : 1 ≤ CFSG.Open.pRank r (barImage D.M K) :=
    s13_one_le_pRank_of_dvd (barImage D.M K) hr hrd
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
