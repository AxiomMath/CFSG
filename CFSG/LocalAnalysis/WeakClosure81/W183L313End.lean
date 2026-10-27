module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoB
public import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem w183l313_mem_centralizer_of_odd {V V₀ : Subgroup G} {z : G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hzV : ∀ v ∈ V, z * v * z⁻¹ * v⁻¹ ∈ V₀)
    (hzV₀ : ∀ w ∈ V₀, z * w = w * z) (hodd : Odd (orderOf z)) :
    z ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  set w : G := z * v * z⁻¹ * v⁻¹ with hwdef
  have hwV₀ : w ∈ V₀ := by rw [hwdef]; exact hzV v hv
  have hzw : z * w = w * z := hzV₀ w hwV₀
  have hzv : z * v * z⁻¹ = w * v := by rw [hwdef]; group
  have hzpow : ∀ j : ℕ, z * w ^ j = w ^ j * z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hzw, ← mul_assoc]
  have hzconj : ∀ j : ℕ, z * w ^ j * z⁻¹ = w ^ j := by
    intro j
    rw [hzpow j]
    group
  have hmain : ∀ j : ℕ, z ^ j * v * (z ^ j)⁻¹ = w ^ j * v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : z ^ (j + 1) * v * (z ^ (j + 1))⁻¹ =
          z * (z ^ j * v * (z ^ j)⁻¹) * z⁻¹ := by group
      rw [h1, ih]
      have h2 : z * (w ^ j * v) * z⁻¹ = (z * w ^ j * z⁻¹) * (z * v * z⁻¹) := by group
      rw [h2, hzconj j, hzv, pow_succ]
      group
  have hwj : w ^ orderOf z = 1 := by
    have h := hmain (orderOf z)
    rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h
    exact mul_right_cancel (by rw [h.symm, one_mul])
  have hw2 : w ^ 2 = 1 := hV.2 w (hV₀ hwV₀)
  obtain ⟨m, hm⟩ := hodd
  have hw1 : w = 1 := by
    rw [hm, pow_succ, pow_mul, hw2, one_pow, one_mul] at hwj
    exact hwj
  have hzv1 : z * v * z⁻¹ = v := by
    have h1 : z * v * z⁻¹ * v⁻¹ = 1 := by rw [← hwdef, hw1]
    calc z * v * z⁻¹ = z * v * z⁻¹ * v⁻¹ * v := by group
      _ = 1 * v := by rw [h1]
      _ = v := by rw [one_mul]
  have hcomm : z * v = v * z := by
    calc z * v = z * v * z⁻¹ * z := by group
      _ = v * z := by rw [hzv1]
  exact hcomm.symm

theorem w183l313_comm_of_mem_V_mul {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    {b v r : G} (hb : b ∈ F11.CTilde M V₀ V) (hv : v ∈ V) (hrM : r ∈ M)
    (hrMg : r ∈ conjSubgroup M g) (hbr : b = v * r) : ∀ d ∈ NOf M V g, ⁅d, b⁆ = 1 := by
  have hVM : V ≤ M := by rw [← h.normalizer_eq]; exact Subgroup.le_normalizer
  have hN : NOf M V g = V ⊓ conjSubgroup V g := NOf_eq M V g hVM
  have hVcT : V ≤ F11.CTilde M V₀ V := by
    intro x hx
    rw [FourteenTwo.mem_cTilde_iff_comm]
    refine ⟨hVM hx, h.le_normalizer₀ (hVM hx), fun u hu => ?_⟩
    have hcomm : x * u = u * x := IsElemAbelian.comm h.elemAbelian hx hu
    have hxu : x * u * x⁻¹ * u⁻¹ = 1 := by rw [hcomm]; group
    rw [hxu]
    exact V₀.one_mem
  have hrC : r ∈ F11.CTilde M V₀ V := by
    have hr_eq : r = v⁻¹ * b := by rw [hbr]; group
    rw [hr_eq]
    exact (F11.CTilde M V₀ V).mul_mem ((F11.CTilde M V₀ V).inv_mem (hVcT hv)) hb
  have hrNormV : r ∈ Subgroup.normalizer (V : Set G) := by
    rw [h.normalizer_eq]; exact hrM
  have hrNormVg : r ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V g, h.normalizer_eq]
    exact hrMg
  have hrNormN : r ∈ Subgroup.normalizer (NOf M V g : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    rw [hN, E3.conjSubgroup_inf, conjSubgroup_eq_iff_mem_normalizer.2 hrNormV,
      conjSubgroup_eq_iff_mem_normalizer.2 hrNormVg]
  intro d hd
  have hdV : d ∈ V := (hN ▸ hd).1
  have hrd : r * d⁻¹ * r⁻¹ ∈ NOf M V g :=
    (Subgroup.mem_normalizer_iff.1 hrNormN d⁻¹).1 ((NOf M V g).inv_mem hd)
  have hdrN : ⁅d, r⁆ ∈ NOf M V g := by
    rw [commutatorElement_def]
    have h : d * r * d⁻¹ * r⁻¹ = d * (r * d⁻¹ * r⁻¹) := by group
    rw [h]
    exact (NOf M V g).mul_mem hd hrd
  have hrdV₀ : r * d * r⁻¹ * d⁻¹ ∈ V₀ := (FourteenTwo.mem_cTilde_iff_comm.1 hrC).2.2 d hdV
  have hdrV₀ : ⁅d, r⁆ ∈ V₀ := by
    rw [commutatorElement_def]
    have h : d * r * d⁻¹ * r⁻¹ = (r * d * r⁻¹ * d⁻¹)⁻¹ := by group
    rw [h]
    exact V₀.inv_mem hrdV₀
  have hdr1 : ⁅d, r⁆ = 1 := by
    have hmem : ⁅d, r⁆ ∈ NOf M V g ⊓ V₀ := ⟨hdrN, hdrV₀⟩
    rw [NOf_inf_eq_bot h] at hmem
    simpa using hmem
  have hdr_comm : d * r = r * d := commutatorElement_eq_one_iff_mul_comm.1 hdr1
  have hdv_comm : d * v = v * d := IsElemAbelian.comm h.elemAbelian hdV hv
  rw [hbr, commutatorElement_eq_one_iff_mul_comm]
  calc d * (v * r) = (d * v) * r := by group
    _ = (v * d) * r := by rw [hdv_comm]
    _ = v * (d * r) := by group
    _ = v * (r * d) := by rw [hdr_comm]
    _ = (v * r) * d := by group

theorem w183l313_NOf_eq_of_mul {M V : Subgroup G} (hM : Subgroup.normalizer (V : Set G) = M)
    {p q c : G} (hc : c ∈ Subgroup.centralizer (V : Set G)) (hpqc : q * c * p⁻¹ ∈ M) :
    NOf M V p = NOf M V q := by
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  rw [NOf_eq M V p hVM, NOf_eq M V q hVM]
  have hcN : c ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hc
  have hconjc : conjSubgroup V c = V := conjSubgroup_eq_iff_mem_normalizer.2 hcN
  have hqcp : conjSubgroup V p = conjSubgroup V (q * c) := by
    have h1 : conjSubgroup V (q * c * p⁻¹) = V :=
      conjSubgroup_eq_iff_mem_normalizer.2 (by rw [hM]; exact hpqc)
    calc conjSubgroup V p = conjSubgroup (conjSubgroup V (q * c * p⁻¹)) p := by rw [h1]
      _ = conjSubgroup V ((q * c * p⁻¹) * p) := conjSubgroup_conjSubgroup V (q * c * p⁻¹) p
      _ = conjSubgroup V (q * c) := by rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hqcp, ← conjSubgroup_conjSubgroup]
  have hA : conjSubgroup (V ⊓ conjSubgroup V q) c = V ⊓ conjSubgroup (conjSubgroup V q) c := by
    rw [E3.conjSubgroup_inf, hconjc]
  have hfix : conjSubgroup (V ⊓ conjSubgroup V q) c = V ⊓ conjSubgroup V q := by
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun x hx => hx.1) hc)
  rw [← hA, hfix]

end CFSG.LocalAnalysis.WeakClosure81

end
