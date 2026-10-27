module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs
public import CFSG.LieType.Chevalley.IntrinsicDiagramPermutation

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

private theorem fsp_not_dvd_one (p : ℕ) (hp : p.Prime) : ¬ (p : ℤ) ∣ 1 := by
  intro h
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using h))

private theorem fsp_not_dvd_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have h' : p ∣ 2 := Int.natCast_dvd_natCast.mp (by simpa using h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h' with h1 | h1
  · exact hp.ne_one h1
  · exact hp2 h1

private theorem fsp_not_dvd_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) : ¬ (p : ℤ) ∣ 3 := by
  intro h
  have h' : p ∣ 3 := Int.natCast_dvd_natCast.mp (by simpa using h)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h' with h1 | h1
  · exact hp.ne_one h1
  · exact hp3 h1

private theorem fsp_det_F4
    (f : ℕ) : (ggU .F4 6 f).D.cartan.det = 1 := by
  change (Tag.cartan .F4).det = 1
  exact det_cartan_F4

private theorem fsp_det_E6
    (f : ℕ) : (ggU .E6 6 f).D.cartan.det = 3 := by
  change (Tag.cartan .E6).det = 3
  exact det_cartan_E6

private theorem fsp_det_E7
    (f : ℕ) : (ggU .E7 6 f).D.cartan.det = 2 := by
  change (Tag.cartan .E7).det = 2
  exact det_cartan_E7

private theorem fsp_det_E8
    (f : ℕ) : (ggU .E8 6 f).D.cartan.det = 1 := by
  change (Tag.cartan .E8).det = 1
  exact det_cartan_E8

private theorem fsp_E6_three_expl :
    ∀ abcd : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3, ∀ i : Fin 6,
      (![abcd.1, abcd.2.1, abcd.2.2.1, abcd.2.2.2, abcd.2.2.1, abcd.1] : Fin 6 → ZMod 3) i =
        ∑ j : Fin 6, (![-abcd.1 - abcd.2.1 + abcd.2.2.2, -abcd.1 - abcd.2.1 + abcd.2.2.1,
          abcd.2.1 - abcd.2.2.2, abcd.1 - abcd.2.2.1, 0, -abcd.1] : Fin 6 → ZMod 3) j *
          (((Tag.cartan .E6) j i : ℤ) : ZMod 3) := by
  decide +kernel

private theorem fsp_E6_three_core (g : Fin 6 → ZMod 3) (hg4 : g 4 = g 2) (hg5 : g 5 = g 0) :
    ∃ c : Fin 6 → ℤ, ∀ i : Fin 6,
      g i = ∑ j : Fin 6, (c j : ZMod 3) * (((Tag.cartan .E6) j i : ℤ) : ZMod 3) := by
  have hgv : g = ![g 0, g 1, g 2, g 3, g 2, g 0] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hg4
    · exact hg5
  choose c hc using fun j : Fin 6 => ZMod.intCast_surjective
    ((![-g 0 - g 1 + g 3, -g 0 - g 1 + g 2, g 1 - g 3, g 0 - g 2, 0, -g 0] :
      Fin 6 → ZMod 3) j)
  refine ⟨c, fun i => ?_⟩
  simp only [hc]
  exact (congrFun hgv i).trans (fsp_E6_three_expl (g 0, g 1, g 2, g 3) i)

private theorem fsp_E6_three_gamma
    (f : ℕ) (g : Fin 6 → ZMod 3)
    (hg : ∀ i, g ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i) = g i) :
    g ∈ LatCorootSpan (ggU .E6 6 f).D 3 := by
  obtain ⟨c, hc⟩ := fsp_E6_three_core g (hg 2) (hg 0)
  exact ⟨c, hc⟩

private theorem fsp_E6
    (f : ℕ) {p : ℕ} (hp : p.Prime) (π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E6 6 f).D π) (hnot : ¬ (p = 3 ∧ π = 1))
    {g : Fin (ggU .E6 6 f).D.rank → ZMod p} (hg : ∀ i, g (π i) = g i) :
    g ∈ LatCorootSpan (ggU .E6 6 f).D p := by
  by_cases hp3 : p = 3
  · subst hp3
    have hπ1 : π ≠ 1 := fun h => hnot ⟨rfl, h⟩
    rcases CFSG.LieType.Chevalley.perm_cases_of_cartanE6 π (fun i j => hπ i j) with h | h
    · exact absurd h hπ1
    · rw [h] at hg
      exact fsp_E6_three_gamma f g hg
  · apply latCorootSpan_eq_top _ p hp
    rw [fsp_det_E6 f]
    exact fsp_not_dvd_three p hp hp3

theorem ggFix_mem_latCorootSpan
    {t : StatedLieTag} (ht : GGExcFive t) {f p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)} (hπ : GGPiCond t p f π)
    (hnot : ¬ ((t = .E6 ∨ t = .twistedE6) ∧ p = 3 ∧ π = 1))
    {g : Fin (ggU (absTag t) 6 f).D.rank → ZMod p} (hg : ∀ i, g (π i) = g i) :
    g ∈ LatCorootSpan (ggU (absTag t) 6 f).D p := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · apply latCorootSpan_eq_top _ p hp
    have hd : (ggU (absTag .F4) 6 f).D.cartan.det = 1 := fsp_det_F4 f
    rw [hd]
    exact fsp_not_dvd_one p hp
  · exact fsp_E6 f hp π hπ.1 (fun h => hnot ⟨Or.inl rfl, h⟩) hg
  · apply latCorootSpan_eq_top _ p hp
    have hd : (ggU (absTag .E7) 6 f).D.cartan.det = 2 := fsp_det_E7 f
    rw [hd]
    exact fsp_not_dvd_two p hp hp2
  · apply latCorootSpan_eq_top _ p hp
    have hd : (ggU (absTag .E8) 6 f).D.cartan.det = 1 := fsp_det_E8 f
    rw [hd]
    exact fsp_not_dvd_one p hp
  · exact fsp_E6 f hp π hπ.1 (fun h => hnot ⟨Or.inr rfl, h⟩) hg

theorem ggKGModel_exceptional_of_inner_lt
    {t : StatedLieTag} {n f p : ℕ} (ht : GGExcFive t)
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGKGModel t n f p)
    (hlt : Nat.card ↥(M.Bfull ⊓ (ggPsiU t n f).range) < Nat.card M.Bfull) :
    (t = .E6 ∨ t = .twistedE6) ∧ p = 3 ∧ M.π = 1 := by
  by_contra hnot
  have hle : M.Bfull ≤ (ggPsiU t n f).range := by
    intro b hb
    have hfix := M.coord_fixed ⟨b, hb⟩
    obtain ⟨b', hb'r, hb'⟩ :=
      M.coord_surj_inner _ (ggFix_mem_latCorootSpan ht hp hp2 M.hπ hnot hfix) hfix
    have hbb : b' = ⟨b, hb⟩ := M.coord_inj (Multiplicative.toAdd.injective hb')
    rw [hbb] at hb'r
    exact hb'r
  rw [inf_eq_left.mpr hle] at hlt
  exact lt_irrefl _ hlt

end CFSG.StandardType
