module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.CN_congr (hc : Ctx M Q Z B) {s t : G} (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) : hc.CN s = hc.CN t := by
  ext x
  rw [Ctx.mem_CN, Ctx.mem_CN, hR, hV]

theorem OmegaPlusNat_congr (hc : Ctx M Q Z B) {s t : G}
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) (m : ℕ) :
    OmegaPlusNat hc s m ↔ OmegaPlusNat hc t m := by
  unfold OmegaPlusNat
  rw [hc.CN_congr hR hV, hR, hV]

theorem OmegaMinusNat_congr (hc : Ctx M Q Z B) {s t : G}
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) (m : ℕ) :
    OmegaMinusNat hc s m ↔ OmegaMinusNat hc t m := by
  unfold OmegaMinusNat
  rw [hc.CN_congr hR hV, hR, hV]

theorem Sec7Hyp.congr {hc : Ctx M Q Z B} {n : ℕ} {t s : G} (hs : Sec7Hyp hc n t)
    (hsL : s ∈ LB M Q B) (hsQ : s ∉ Q) (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) : Sec7Hyp hc n s where
  toSec5 := ⟨hs.toSec5.width, hs.toSec5.n_gt, hs.toSec5.noA2, hs.toSec5.gen, hsL, hsQ⟩
  notPlus4 := fun h => hs.notPlus4 ((OmegaPlusNat_congr hc hR hV 2).mp h)
  orth := by
    obtain ⟨m, hm, h⟩ := hs.orth
    exact ⟨m, hm, h.imp (fun h => (OmegaPlusNat_congr hc hR hV m).mpr h)
      (fun h => (OmegaMinusNat_congr hc hR hV m).mpr h)⟩
  large := by
    rw [hc.CN_congr hR hV]
    exact hs.large

theorem conjMod_normalizer_of_nat (h56 : Stroth56NatStatement) {hc : Ctx M Q Z B} {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2) {x : G} (hxL : x ∈ LB M Q B)
    (hx : ConjMod M Q t x) :
    ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * t * ν⁻¹)⁻¹ ∈ Q := by
  obtain ⟨hxM, g, hg, hQ⟩ := hx
  have ht : t ∈ LB M Q B := hs.toSec5.mem
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
  obtain ⟨r, hr, hreq⟩ := h56 G M Q Z B hc n t hs hnom g⁻¹ hgi hsub
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hν'M : r⁻¹ * g⁻¹ ∈ M := M.mul_mem (M.inv_mem hrM) hgi
  have hν'BZ : r⁻¹ * g⁻¹ ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
    refine conjSubgroup_eq_self_iff.mp ?_
    have hZr : conjSubgroup r⁻¹ Z = Z := hc.conj_Z_eq (M.inv_mem hrM)
    have hrB : conjSubgroup r⁻¹ (conjSubgroup r B) = B := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [conjSubgroup_mul, conjSubgroup_sup', hc.conj_Z_eq hgi, hreq, conjSubgroup_sup', hrB, hZr]
  have hν'L : r⁻¹ * g⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (hc.mem_normalizer_LB_iff' hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hν'M).mpr hν'BZ
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

theorem Sec7Hyp.omegaNat {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) :
    OmegaNat hc t := by
  obtain ⟨m, hm, h | h⟩ := hs.orth
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs.notPlus4 h
    obtain ⟨K, fK, finK, hK, hrep⟩ := h
    exact ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hrep⟩⟩
  · obtain ⟨K, fK, finK, hK, b, c, hirr, hrep⟩ := h
    exact ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hrep⟩⟩

theorem sec7Conj_of_parts (h56 : Stroth56NatStatement) (hZ : Sec7CentreMpStatement)
    (hZt : Sec7ZtStatement) : Sec7ConjStatement := by
  intro G _ _ M Q Z B hc n t hs hnom Z0 hZ0 s hs0 x hxL hx
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
  · have hsL : s ∈ LB M Q B := (hZ G M Q Z B hc n t hs Z0 hZ0 s hs0).1
    obtain ⟨hR, hV⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hs0 hsQ
    exact conjMod_normalizer_of_nat h56 (hs.congr hsL hsQ hR hV)
      (fun h => hnom ((OmegaMinusNat_congr hc hR hV 2).mp h)) hxL hx

theorem sec7ZV_of_parts (hZt : Sec7ZtStatement) (hZ : Sec7CentreMpStatement)
    (h310 : Stroth310ChiStatement) : Sec7ZVStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 u hu huQ
  have huL : u ∈ LB M Q B := (hZ G M Q Z B hc n t hs Z0 hZ0 u hu).1
  obtain ⟨hR, hV⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 u hu huQ
  have hs' := hs.congr huL huQ hR hV
  have hom : OmegaNat hc u := hs'.omegaNat
  exact ((h310 G M Q Z B hc n u hs'.toSec5 (Or.inr hom)).1).symm.trans hV

theorem Fgen_conj_mem (hc : Ctx M Q Z B) {L Z0 : Subgroup G} {ν : G} (hνM : ν ∈ M)
    (hνL : ν ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ Fgen M Q L Z0) :
    ν * x * ν⁻¹ ∈ Fgen M Q L Z0 := by
  have hνQ : ∀ y ∈ Q, ν * y * ν⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hνM) y).mp hy
  have key : Fgen M Q L Z0 ≤ (Fgen M Q L Z0).comap (MulEquiv.toMonoidHom (MulAut.conj ν)) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    obtain ⟨hyL, s, hsZ, hyM, g, hgM, hq⟩ := hy
    refine Subgroup.subset_closure ⟨?_, s, hsZ, ?_, ν * g, M.mul_mem hνM hgM, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hνL y).mp hyL
    · exact M.mul_mem (M.mul_mem hνM hyM) (M.inv_mem hνM)
    · have e : ν * y * ν⁻¹ * (ν * g * s * (ν * g)⁻¹)⁻¹ =
          ν * (y * (g * s * g⁻¹)⁻¹) * ν⁻¹ := by
        group
      have h5 : ν * (y * (g * s * g⁻¹)⁻¹) * ν⁻¹ ∈ Q := hνQ _ hq
      rw [← e] at h5
      exact h5
  exact Subgroup.mem_comap.mp (key hx)

theorem stroth73bTrans_aux (h73b : Stroth73bStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hNCall : ∀ x ∈ LB M Q B, ConjMod M Q t x →
      ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * t * ν⁻¹)⁻¹ ∈ Q)
    (hne : Fgen M Q (LB M Q B) Z0 ≠ Z0) {a b : G} (ha : a ∈ Fgen M Q (LB M Q B) Z0)
    (hb : b ∈ Fgen M Q (LB M Q B) Z0) (haQ : a ∉ Q) (hbQ : b ∉ Q) :
    ∃ g ∈ M, g ∈ Subgroup.normalizer (Fgen M Q (LB M Q B) Z0 : Set G) ∧
      b * (g * a * g⁻¹)⁻¹ ∈ Q := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have htQ : t ∉ Q := hs.toSec5.notQ
  have htF : t ∈ Fgen M Q (LB M Q B) Z0 :=
    Subgroup.subset_closure ⟨ht, t, htZ0, ConjMod.of_mem htM⟩
  have haL : a ∈ LB M Q B := Fgen_le M Q (LB M Q B) Z0 ha
  have hbL : b ∈ LB M Q B := Fgen_le M Q (LB M Q B) Z0 hb
  have ht2 : t ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB ht
  have ha2 : a ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB haL
  have hb2 : b ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hbL
  rcases h73b G M Q Z B hc n t hs hno Z0 hZ0 with h | h
  · exact absurd h hne
  have hta : ConjMod M Q t a := h t htF a ha htQ haQ ht2 ha2
  have htb : ConjMod M Q t b := h t htF b hb htQ hbQ ht2 hb2
  obtain ⟨νa, hνaM, hνaN, hA⟩ := hNCall a haL hta
  obtain ⟨νb, hνbM, hνbN, hB⟩ := hNCall b hbL htb
  have hgM : νb * νa⁻¹ ∈ M := M.mul_mem hνbM (M.inv_mem hνaM)
  have hgN : νb * νa⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (Subgroup.normalizer (LB M Q B : Set G)).mul_mem hνbN
      ((Subgroup.normalizer (LB M Q B : Set G)).inv_mem hνaN)
  have hgF : νb * νa⁻¹ ∈ Subgroup.normalizer (Fgen M Q (LB M Q B) Z0 : Set G) :=
    Subgroup.mem_normalizer_fintype fun y hy =>
      Fgen_conj_mem (L := LB M Q B) (Z0 := Z0) hc hgM hgN (x := y) hy
  refine ⟨νb * νa⁻¹, hgM, hgF, ?_⟩
  have hgQ : ∀ q ∈ Q, νb * νa⁻¹ * q * (νb * νa⁻¹)⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) q).mp hq
  have hkey : b * (νb * νa⁻¹ * a * (νb * νa⁻¹)⁻¹)⁻¹ =
      b * (νb * t * νb⁻¹)⁻¹ * (νb * νa⁻¹ * (a * (νa * t * νa⁻¹)⁻¹) * (νb * νa⁻¹)⁻¹)⁻¹ := by
    group
  rw [hkey]
  exact Q.mul_mem hB (Q.inv_mem (hgQ _ hA))

theorem stroth73bTrans_of (h73b : Stroth73bStatement) (hNC : Sec7ConjStatement)
    (hNC4 : Sec7ConjOm4Statement) : Stroth73bTransStatement := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0 hne a ha b hb haQ hbQ
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.toSec5.mem hZ0
  refine stroth73bTrans_aux h73b hc hs hno hZ0 (fun x hx hcx => ?_) hne ha hb haQ hbQ
  by_cases hom : OmegaMinusNat hc t 2
  · exact hNC4 G M Q Z B hc n t hs hom Z0 hZ0 t htZ0 x hx hcx
  · exact hNC G M Q Z B hc n t hs hom Z0 hZ0 t htZ0 x hx hcx

end CFSG.RankThree.GF2n.Stroth80
