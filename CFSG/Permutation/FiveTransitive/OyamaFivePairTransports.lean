module

public import CFSG.Permutation.FiveTransitive.OyamaFiveNineDiagram
public import CFSG.Permutation.FiveTransitive.KleinFourNineToThirteen
public import CFSG.Permutation.FiveTransitive.OddDNormalization
public import CFSG.Permutation.FiveTransitive.OyamaFiveCrossPair

public section

namespace CFSG

namespace FiveTransitive.OyamaFivePairTransports

open MulAction CommutingFourSeed

theorem exists_cross_pair
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hsize : 10 ≤ Nat.card X) (hseed : Seed G X)
    (hmax : ∀ g : G, g * g = 1 → g ≠ 1 → (fixedBy X g).ncard ≤ 5)
    (a : G) (ha : a * a = 1) (hfixa : (fixedBy X a).ncard = 5)
    (t : Fin 4 ↪ X)
    (ha01 : a • t 0 = t 1) (ha10 : a • t 1 = t 0)
    (ha23 : a • t 2 = t 3) (ha32 : a • t 3 = t 2) :
    ∃ g : G, (∀ z ∈ fixedBy X a, g • z = z) ∧
      (g • t 0 = t 2 ∨ g • t 0 = t 3) := by
  obtain ⟨e, c, het, hc, hc1, hac, hAe, hCe, hACe, ha5, ha6, ha7, ha8,
    hc3, hc4, hc7, hc8⟩ := OyamaFiveNineDiagram.exists_diagram hseed hmax a ha hfixa t ha01 ha10 ha23 ha32
  obtain ⟨E, hE, ha9, ha10E, ha11, ha12, hc9, hc11, hc10, hc12⟩ :=
    KleinFourNineToThirteen.exists_extension hsize e a c ha hc hac hAe hCe hACe
  have hE0 : E 0 = e 0 := hE 0
  have hE1 : E 1 = e 1 := hE 1
  have hE2 : E 2 = e 2 := hE 2
  have hE3 : E 3 = e 3 := hE 3
  have hE4 : E 4 = e 4 := hE 4
  have hE5 : E 5 = e 5 := hE 5
  have hE6 : E 6 = e 6 := hE 6
  have hE7 : E 7 = e 7 := hE 7
  have hE8 : E 8 = e 8 := hE 8
  have hAE : fixedBy X a = {E 0, E 1, E 2, E 3, E 4} := by
    simpa only [hE0, hE1, hE2, hE3, hE4] using hAe
  have hCE : fixedBy X c = {E 0, E 1, E 2, E 5, E 6} := by
    simpa only [hE0, hE1, hE2, hE5, hE6] using hCe
  have hACE : fixedBy X (a * c) = {E 0, E 1, E 2, E 7, E 8} := by
    simpa only [hE0, hE1, hE2, hE7, hE8] using hACe
  let D : Set X := {E 9, E 10, E 11, E 12}
  have hD : D.ncard = 4 := by simp [D, E.injective.eq_iff]
  have haD : ∀ x ∈ D, a • x ∈ D := by
    intro x hx
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [ha9, ha10E, ha11, ha12] <;> simp [D]
  have hcD : ∀ x ∈ D, c • x ∈ D := by
    intro x hx
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [hc9, hc10, hc11, hc12] <;> simp [D]
  obtain ⟨d, hd, hd1, hdD, had, hcd⟩ := for_pair hseed D hD a c ha hc hac haD hcD
  obtain ⟨v, hv, hAv, hCv, hACv, hDv, hd0, hd1v, hd2v, hd3v, hd4v, hd5v, hd6v, hd7v, hd8v⟩ :=
    OddDNormalization.normalize_d E a c d hd (hmax d hd hd1) had hcd hAE hCE hACE
      (hdD _ (by simp [D])) (hdD _ (by simp [D]))
      (hdD _ (by simp [D])) (hdD _ (by simp [D]))
  have hv3 : v 3 = E 3 := hv 3 (by decide)
  have hv4 : v 4 = E 4 := hv 4 (by decide)
  have hv5 : v 5 = E 5 := hv 5 (by decide)
  have hv6 : v 6 = E 6 := hv 6 (by decide)
  have hv7 : v 7 = E 7 := hv 7 (by decide)
  have hv8 : v 8 = E 8 := hv 8 (by decide)
  have hv9 : v 9 = E 9 := hv 9 (by decide)
  have hv10 : v 10 = E 10 := hv 10 (by decide)
  have hv11 : v 11 = E 11 := hv 11 (by decide)
  have hv12 : v 12 = E 12 := hv 12 (by decide)
  have ha5v : a • v 5 = v 6 := by simpa only [hv5, hv6, hE5, hE6] using ha5
  have ha6v : a • v 6 = v 5 := by simpa only [hv5, hv6, hE5, hE6] using ha6
  have ha7v : a • v 7 = v 8 := by simpa only [hv7, hv8, hE7, hE8] using ha7
  have ha8v : a • v 8 = v 7 := by simpa only [hv7, hv8, hE7, hE8] using ha8
  have ha9v : a • v 9 = v 10 := by simpa only [hv9, hv10] using ha9
  have ha10v : a • v 10 = v 9 := by simpa only [hv9, hv10] using ha10E
  have hc3v : c • v 3 = v 4 := by simpa only [hv3, hv4, hE3, hE4] using hc3
  have hc4v : c • v 4 = v 3 := by simpa only [hv3, hv4, hE3, hE4] using hc4
  have hc7v : c • v 7 = v 8 := by simpa only [hv7, hv8, hE7, hE8] using hc7
  have hc8v : c • v 8 = v 7 := by simpa only [hv7, hv8, hE7, hE8] using hc8
  have ha1v : a • v 1 = v 1 := by change v 1 ∈ fixedBy X a; rw [hAv]; simp
  have ha2v : a • v 2 = v 2 := by change v 2 ∈ fixedBy X a; rw [hAv]; simp
  have hc0v : c • v 0 = v 0 := by change v 0 ∈ fixedBy X c; rw [hCv]; simp
  have hc1v : c • v 1 = v 1 := by change v 1 ∈ fixedBy X c; rw [hCv]; simp
  have hc2v : c • v 2 = v 2 := by change v 2 ∈ fixedBy X c; rw [hCv]; simp
  have hd9v : d • v 9 = v 9 := by change v 9 ∈ fixedBy X d; rw [hDv]; simp
  have hd10v : d • v 10 = v 10 := by change v 10 ∈ fixedBy X d; rw [hDv]; simp
  let F : Set X := {v 1, v 2, v 9, v 10}
  have hF : F.ncard = 4 := by simp [F, v.injective.eq_iff]
  have haF : ∀ x ∈ F, a • x ∈ F := by
    intro x hx
    simp only [F, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [ha1v, ha2v, ha9v, ha10v] <;> simp [F]
  have hdF : ∀ x ∈ F, d • x ∈ F := by
    intro x hx
    simp only [F, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [hd1v, hd2v, hd9v, hd10v] <;> simp [F]
  obtain ⟨f, hf, hf1, hfF, haf, hdf⟩ := for_pair hseed F hF a d ha hd had haF hdF
  obtain ⟨hfix, hcross⟩ := OyamaFiveCrossPair.cross_pair hmax v a c d f ha hd hf hf1
    had haf hdf hAv hDv ha5v ha6v ha7v ha8v hd3v hd5v hd6v hd7v hd8v
    hc0v hc1v hc2v hc3v hc4v hc7v hc8v
    (hfF _ (by simp [F])) (hfF _ (by simp [F]))
    (hfF _ (by simp [F])) (hfF _ (by simp [F]))
  have hv5t : v 5 = t 0 := (hv5.trans hE5).trans (het 0)
  have hv7t : v 7 = t 2 := (hv7.trans hE7).trans (het 2)
  have hv8t : v 8 = t 3 := (hv8.trans hE8).trans (het 3)
  exact ⟨c * f, hfix, by simpa only [hv5t, hv7t, hv8t] using hcross⟩

end FiveTransitive.OyamaFivePairTransports

end CFSG
