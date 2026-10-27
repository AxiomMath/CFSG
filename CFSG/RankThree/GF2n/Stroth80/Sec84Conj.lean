module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem SpMNat_congr (hc : Ctx M Q Z B) {s t : G}
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) (m : ℕ) :
    SpMNat hc s m ↔ SpMNat hc t m := by
  unfold SpMNat
  rw [hc.CN_congr hR hV, hR, hV]

theorem Sec8Hyp.congr {hc : Ctx M Q Z B} {n : ℕ} {t s : G} (hs : Sec8Hyp hc n t)
    (hsL : s ∈ LB M Q B) (hsQ : s ∉ Q) (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) : Sec8Hyp hc n s where
  toSec5 := ⟨hs.toSec5.width, hs.toSec5.n_gt, hs.toSec5.noA2, hs.toSec5.gen, hsL, hsQ⟩
  sp := by
    obtain ⟨m, hm, h⟩ := hs.sp
    exact ⟨m, hm, (SpMNat_congr hc hR hV m).mpr h⟩

theorem conjMod_normalizer_of_sp (h56 : Stroth56SpStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B) (hx : ConjMod M Q t x) :
    ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * t * ν⁻¹)⁻¹ ∈ Q := by
  obtain ⟨hxM, g, hg, hQ⟩ := hx
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hgi : g⁻¹ ∈ M := M.inv_mem hg
  have hy : g * t * g⁻¹ ∈ LB M Q B := by
    have e : g * t * g⁻¹ = (x * (g * t * g⁻¹)⁻¹)⁻¹ * x := by group
    rw [e]
    exact (LB M Q B).mul_mem ((LB M Q B).inv_mem (sec39_Q_le_LB hQ)) hxL
  have htm : t ∈ conjSubgroup g⁻¹ (LB M Q B) := by
    rw [mem_conjSubgroup, inv_inv]
    exact hy
  have hsub : conjSubgroup g⁻¹ B ⊔ Z ≤ Vt M (LB M Q B) B Z t :=
    sup_le (sec39_conjB_le_Vt hgi htm) sec39_Z_le_Vt
  obtain ⟨r, hr, hreq⟩ := h56 G M Q Z B hc n t hs g⁻¹ hgi hsub
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hν'M : r⁻¹ * g⁻¹ ∈ M := M.mul_mem (M.inv_mem hrM) hgi
  have hν'BZ : r⁻¹ * g⁻¹ ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
    refine conjSubgroup_eq_self_iff.mp ?_
    have hZr : conjSubgroup r⁻¹ Z = Z := hc.conj_Z_eq (M.inv_mem hrM)
    have hrB : conjSubgroup r⁻¹ (conjSubgroup r B) = B := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [conjSubgroup_mul, conjSubgroup_sup', hc.conj_Z_eq hgi, hreq, conjSubgroup_sup', hrB, hZr]
  have hν'L : r⁻¹ * g⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (hc.mem_normalizer_LB_iff' h5.width h5.n_gt h5.noA2 hν'M).mpr hν'BZ
  refine ⟨g * r, M.mul_mem hg hrM, ?_, ?_⟩
  · have := Subgroup.inv_mem _ hν'L
    simpa [mul_assoc] using this
  · have hcomm : ⁅t, r⁆ ∈ Q := by
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hc.Rt_comm_mem_Q hr)
    have hconj : g * ⁅t, r⁆ * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) _).mp hcomm
    have e : x * (g * r * t * (g * r)⁻¹)⁻¹ =
        (x * (g * t * g⁻¹)⁻¹) * (g * ⁅t, r⁆ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hQ hconj

theorem sec86Conj_of_parts (h56 : Stroth56SpStatement) (hZt : Sec8ZtStatement)
    (h51 : Stroth51Statement) (hA : Sec8AExistsStatement) : Sec86ConjStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hs0 x hxL hx
  by_cases hsQ : s ∈ Q
  · refine ⟨1, M.one_mem, Subgroup.one_mem _, ?_⟩
    obtain ⟨hxM, g, hg, hQ⟩ := hx
    have hsM : s ∈ M := hc.hyp.Q_normal.1 hsQ
    have hgs : g * s * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) s).mp hsQ
    have hxQ : x ∈ Q := by
      have h1 := Q.mul_mem hQ hgs
      have e : x * (g * s * g⁻¹)⁻¹ * (g * s * g⁻¹) = x := by group
      rwa [e] at h1
    have h2 := Q.mul_mem hxQ (Q.inv_mem hsQ)
    have e2 : x * s⁻¹ = x * (1 * s * 1⁻¹)⁻¹ := by group
    rwa [← e2]
  · have hsL : s ∈ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0 hs0
    obtain ⟨hR, hV⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hs0 hsQ
    exact conjMod_normalizer_of_sp h56 (hs.congr hsL hsQ hR hV) hxL hx

end CFSG.RankThree.GF2n.Stroth80
