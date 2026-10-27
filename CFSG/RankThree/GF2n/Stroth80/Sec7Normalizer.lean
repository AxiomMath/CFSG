module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Z0_normalizes_of_ZV (h73a : Stroth73aStatement) (hZV : Sec7ZVStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
      (t : G),
      Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
        g ∈ Subgroup.normalizer (Z0 : Set G) := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0 g hg u hu huQ hgu
  have hgN : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 (M.inv_mem hg)
  have huQ' : g * u * g⁻¹ ∉ Q := by
    intro h
    apply huQ
    have h4 := (Subgroup.mem_normalizer_iff.mp hgN (g * u * g⁻¹)).mp h
    have h3 : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rwa [h3] at h4
  have hZu : Ut Q Z u = Vt M (LB M Q B) B Z t := hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ
  have hZu' : Ut Q Z (g * u * g⁻¹) = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 (g * u * g⁻¹) hgu huQ'
  have hconj := Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) u
  have hgV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    ((congrArg (conjSubgroup g) hZu).symm.trans hconj.symm).trans hZu'
  exact h73a G M Q Z B hc n t hs hno Z0 hZ0 g hg (conjSubgroup_eq_self_iff.mp hgV)

theorem stroth73c_first_aux (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (h73a : Stroth73aStatement) (hno : ¬ Conc71abcd hc n t) (hCV : Sec7CVStatement)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hNC : ∀ s ∈ Z0, ∀ x ∈ LB M Q B, ConjMod M Q s x →
      ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * s * ν⁻¹)⁻¹ ∈ Q)
    (hsc : StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B)) :
    StronglyClosedMod M Z0 (LB M Q B) := by
  intro z hz g hg hgL
  have htLB : t ∈ LB M Q B := hs.toSec5.mem
  have hnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := hZ0.Q_le (hc.Q_le_Rt htLB) hnorm
  have hzM : z ∈ M := hc.Rt_le_M t (hZ0.le hz)
  have hyM : g * z * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hzM) (M.inv_mem hg)
  obtain ⟨ν, hνM, hνN, hνQ⟩ := hNC z hz (g * z * g⁻¹) hgL ⟨hyM, g, hg, by simp⟩
  have hνinvM : ν⁻¹ ∈ M := M.inv_mem hνM
  have hνinvN : ν⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) := Subgroup.inv_mem _ hνN
  have hconjInv : ∀ w ∈ LB M Q B ⊓ hc.CN t, ν⁻¹ * w * ν ∈ LB M Q B ⊓ hc.CN t := by
    intro w hw
    have h2 : w ∈ LB M Q B := (Subgroup.mem_inf.mp hw).1
    have h1 : ν⁻¹ * w * ν⁻¹⁻¹ ∈ LB M Q B ⊓ hc.CN t :=
      hsc w hw ν⁻¹ hνinvM ((Subgroup.mem_normalizer_iff.mp hνinvN w).mp h2)
    rwa [inv_inv] at h1
  have hνV : ν ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have hvQ : v ∈ Q := hc.Vt_le_Q t hv
    have hνvQ : ν * v * ν⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hνM) v).mp hvQ
    refine (hCV G M Q Z B hc n t hs (ν * v * ν⁻¹) hνvQ).mpr fun y hy => ?_
    have hwv : ⁅ν⁻¹ * y * ν, v⁆ ∈ Z :=
      (hCV G M Q Z B hc n t hs v hvQ).mp hv (ν⁻¹ * y * ν) (hconjInv y hy)
    have e : ⁅y, ν * v * ν⁻¹⁆ = ν * ⁅ν⁻¹ * y * ν, v⁆ * ν⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hνM) _).mp hwv
  have hνZ0 : ν ∈ Subgroup.normalizer (Z0 : Set G) :=
    h73a G M Q Z B hc n t hs hno Z0 hZ0 ν hνM hνV
  have hνz : ν * z * ν⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hνZ0 z).mp hz
  have e2 : g * z * g⁻¹ * (ν * z * ν⁻¹)⁻¹ * (ν * z * ν⁻¹) = g * z * g⁻¹ := by
    group
  have key := Z0.mul_mem (hQZ0 hνQ) hνz
  rwa [e2] at key

theorem stroth73cNotOm4_of (h73a : Stroth73aStatement) (hNC : Sec7ConjStatement)
    (hCV : Sec7CVStatement) : Stroth73cNotOm4Statement := by
  intro G _ _ M Q Z B hc n t hs hno hnom Z0 hZ0 hsc
  exact stroth73c_first_aux hc hs h73a hno hCV hZ0 (hNC G M Q Z B hc n t hs hnom Z0 hZ0) hsc

theorem stroth73cOm4_of (h73a : Stroth73aStatement) (hCV : Sec7CVStatement)
    (hCard : Sec73CardStatement) (hNC4 : Sec7ConjOm4Statement) : Stroth73cOm4Statement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0
  obtain ⟨hα, hβ⟩ := hCard G M Q Z B hc n t hs hno hom
  have hsc : StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B) :=
    stronglyClosedMod_of_card hc (Nat.card Z ^ 8) hα fun y hy hyN =>
      hβ y hy fun hCN => hyN ⟨hy, hCN⟩
  exact ⟨hsc, stroth73c_first_aux hc hs h73a hno hCV hZ0
    (hNC4 G M Q Z B hc n t hs hom Z0 hZ0) hsc⟩

theorem stroth73aNotOm4_of (hNR : Sec7NormZ0Statement) :
    Stroth73aNotOm4Statement := fun G _ _ M Q Z B hc n t hs _ hnom Z0 hZ0 m hm hmV =>
  hNR G M Q Z B hc n t hs hnom Z0 hZ0 m hm hmV

theorem close71TI_of (h73a : Stroth73aStatement) (hZV : Sec7ZVStatement) :
    Close71TIStatement := by
  intro G _ _ M Q Z B hc n t hcl Z0 hZ0 g hg u hu huQ hgu
  exact Z0_normalizes_of_ZV h73a hZV G M Q Z B hc n t hcl.1 hcl.2.1 Z0 hZ0 g hg u hu huQ hgu

end CFSG.RankThree.GF2n.Stroth80
