module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem uc22s2112r34q35_orderOf_induced {L : Subgroup G} {b : G}
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hbr : orderOf b = r)
    (hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1) :
    orderOf (inducedBarInfAutHom L ⟨b, hb⟩) = r := by
  have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
  rw [Subgroup.orderOf_mk, hbr] at hd
  rcases (Nat.dvd_prime hr).1 hd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.1 h1) hθ1
  · exact h1

theorem uc22s2112r34q35_inner (hKF1 : KFieldAutOdd) {M L : Subgroup G} (hL : L ∈ calC M)
    {t : StatedLieTag} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p 1) (hX : LieModel (BarInf L) t n p 1)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2) {b : G}
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrg : ¬ r ∣ (genericOrders t n p 1).1)
    (hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1) :
    inducedBarInfAutHom L ⟨b, hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  by_contra hθ
  obtain ⟨h1, -⟩ := hKF1 (BarInf L) t n p 1 r hp hp2 hadm hX hA1 hRee hr hr5 hrg _
    (uc22s2112r34q35_orderOf_induced hb hr hbr hθ1) hθ
  exact hr.one_lt.ne' (Nat.dvd_one.1 h1)

theorem uc22s2112r34q35_exists_conj (hKF1 : KFieldAutOdd) {M L B₀ : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p 1) (hX : LieModel (BarInf L) t n p 1)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (hfaith : ∀ b ∈ B₀, CentralizesBar b L → b = 1) {b : G} (hbB : b ∈ B₀)
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrg : ¬ r ∣ (genericOrders t n p 1).1) :
    ∃ x : BarInf L, inducedBarInfAutHom L ⟨b, hb⟩ = MulAut.conj x ∧ orderOf x = r := by
  have hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1 := fun h1 => by
    have hb1 := hfaith b hbB (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 hb h1)
    rw [hb1, orderOf_one] at hbr
    exact hr.one_lt.ne hbr
  obtain ⟨x, hx⟩ := uc22s2112r34q35_inner hKF1 hL hp hp2 hadm hX hA1 hRee hb hr hr5 hbr hrg hθ1
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [center_barInf_eq_bot hL.2.2, mem_bot] at hzc
  refine ⟨x, hx.symm, ?_⟩
  rw [← orderOf_injective _ hinj x, hx]
  exact uc22s2112r34q35_orderOf_induced hb hr hbr hθ1

theorem uc22s2112r34q35_inner_of_mem (hKF1 : KFieldAutOdd) {M L B₀ : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p 1) (hX : LieModel (BarInf L) t n p 1)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (hBN : B₀ ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ B₀, CentralizesBar b L → b = 1)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrg : ¬ r ∣ (genericOrders t n p 1).1)
    {R : Subgroup G} (hRB : R ≤ B₀) (hRr : ∀ x ∈ R, x ≠ 1 → orderOf x = r) {x : G} (hx : x ∈ R) :
    inducedBarInfAutHom L ⟨x, hBN (hRB hx)⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  by_cases hx1 : x = 1
  · subst hx1
    exact ⟨1, by rw [map_one, ← map_one (inducedBarInfAutHom L)]; rfl⟩
  · refine uc22s2112r34q35_inner hKF1 hL hp hp2 hadm hX hA1 hRee _ hr hr5 (hRr x hx hx1) hrg
      fun h1 => hx1 ?_
    exact hfaith x (hRB hx)
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN (hRB hx)) h1)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
