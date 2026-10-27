module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import TauCeti.GroupTheory.FrobeniusKernel
import CFSG.ClassicalGroups.SpecialLinear.TvModLinAlg
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import CFSG.LocalAnalysis.SteinbergCCDegreeTwoNormalizerSolvable
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.LargeExtraspecial.A2ModLines
import CFSG.LinearAlgebra.LinearGroups.Elations
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem eq_neg_of_isRefl_of_finrank_le_one [Module.Finite (ZMod p) U]
    (hU : Module.finrank (ZMod p) U ≤ 1) {x : U ≃ₗ[ZMod p] U} (hx : IsRefl p x) :
    x = LinearEquiv.neg (ZMod p) := by
  have hfin : Module.finrank (ZMod p) U = 1 := by
    have hx2 : Module.finrank (ZMod p)
        (LinearMap.range ((x : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 := hx.2
    have := Submodule.finrank_le (LinearMap.range ((x : U →ₗ[ZMod p] U) - LinearMap.id))
    rw [hx2] at this
    omega
  have htop : LinearMap.range ((x : U →ₗ[ZMod p] U) - LinearMap.id) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hx.2, hfin])
  refine LinearEquiv.ext fun v => ?_
  change x v = -v
  have hv : v ∈ LinearMap.range ((x : U →ₗ[ZMod p] U) - LinearMap.id) := by rw [htop]; trivial
  obtain ⟨w, hw⟩ := hv
  have hw' : x w - w = v := by simpa [LinearMap.sub_apply] using hw
  have hxx : x (x w) = w := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hx.1
    simpa [LinearEquiv.mul_apply] using h
  calc x v = x (x w - w) := by rw [← hw']
    _ = w - x w := by rw [map_sub, hxx]
    _ = -v := by rw [← hw']; abel

theorem isRefl_eq_of_finrank_le_one [Module.Finite (ZMod p) U]
    (hU : Module.finrank (ZMod p) U ≤ 1) {x y : U ≃ₗ[ZMod p] U} (hx : IsRefl p x)
    (hy : IsRefl p y) : x = y := by
  rw [eq_neg_of_isRefl_of_finrank_le_one hU hx, eq_neg_of_isRefl_of_finrank_le_one hU hy]

theorem tableFactsAt_of_le_one {m : ℕ} (hm : m ≤ 1) : TableFactsAt p m := by
  refine tableFactsAt_of_forall fun U _ _ _ J hdim hT => ?_
  obtain ⟨x, -, y, -, hx, hy, hxy⟩ := hT.dLarge
  have hxy_eq : x = y := isRefl_eq_of_finrank_le_one (by omega) hx hy
  rw [hxy_eq, hy.1] at hxy
  exact absurd hxy (by simp)

open scoped Pointwise in
private theorem isTISubgroup_centralizer {G : Type*} [Group G]
    (htrans : ∀ x y z : G, x ≠ 1 → Commute x y → Commute x z → Commute y z)
    (hsn : ∀ x g : G, x ≠ 1 → Commute x (g * x * g⁻¹) → Commute g x)
    {z : G} (hz : z ≠ 1) :
    TauCeti.IsTISubgroup (Subgroup.centralizer ({z} : Set G)) := by
  rw [TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot]
  intro g hg
  have key : ∀ y : G, y ∈ MulAut.conj g • (Subgroup.centralizer ({z} : Set G) : Set G) ↔
      g⁻¹ * y * g ∈ Subgroup.centralizer ({z} : Set G) := by
    intro y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyH, hysmul⟩ := hy
  have hgyH : g⁻¹ * y * g ∈ Subgroup.centralizer ({z} : Set G) := (key y).mp hysmul
  by_contra hy1
  have hz1 : g⁻¹ * y * g ≠ 1 := fun h => hy1 (by
    have hh := congrArg (fun t => g * t * g⁻¹) h
    simpa [mul_assoc] using hh)
  have hzy : Commute (g⁻¹ * y * g) z := Subgroup.mem_centralizer_singleton_iff.mp hgyH
  have hyz : Commute y z := Subgroup.mem_centralizer_singleton_iff.mp hyH
  have hzyc : Commute (g⁻¹ * y * g) (g⁻¹ * z * g) := by
    rw [Commute, SemiconjBy]
    calc (g⁻¹ * y * g) * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [hyz]
      _ = (g⁻¹ * z * g) * (g⁻¹ * y * g) := by group
  have hzcomm : Commute z (g⁻¹ * z * g) :=
    htrans (g⁻¹ * y * g) z (g⁻¹ * z * g) hz1 hzy hzyc
  have hginv : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hsn z g⁻¹ hz (by simpa using hzcomm))
  exact hg (by simpa using (Subgroup.centralizer ({z} : Set G)).inv_mem hginv)

private theorem centralizer_singleton_eq_of_commute {G : Type*} [Group G]
    (htrans : ∀ x y z : G, x ≠ 1 → Commute x y → Commute x z → Commute y z)
    {u x : G} (hu : u ≠ 1) (hx : x ≠ 1) (h : Commute u x) :
    Subgroup.centralizer ({u} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  apply le_antisymm
  · intro w hw
    have hwu : Commute w u := Subgroup.mem_centralizer_singleton_iff.mp hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (htrans u x w hu h hwu.symm).symm
  · intro w hw
    have hwx : Commute w x := Subgroup.mem_centralizer_singleton_iff.mp hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (htrans x u w hx h.symm hwx.symm).symm

open scoped Pointwise in
private theorem commute_conj_of_mem_centralizer_eq {G : Type*} [Group G]
    {x u g h z : G}
    (hu_eq : Subgroup.centralizer ({u} : Set G)
      = Subgroup.centralizer ({g * x * g⁻¹} : Set G))
    (hzhu : Commute u (h * z * h⁻¹)) :
    Commute (g⁻¹ * (h * z * h⁻¹) * g) x := by
  have hzh_mem : h * z * h⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    rw [← hu_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hzhu.symm
  have hcomm_c : Commute (h * z * h⁻¹) (g * x * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hzh_mem
  show (g⁻¹ * (h * z * h⁻¹) * g) * x = x * (g⁻¹ * (h * z * h⁻¹) * g)
  calc (g⁻¹ * (h * z * h⁻¹) * g) * x
      = g⁻¹ * ((h * z * h⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * x * g⁻¹) * (h * z * h⁻¹)) * g := by
          rw [show (h * z * h⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (h * z * h⁻¹)
            from hcomm_c]
    _ = x * (g⁻¹ * (h * z * h⁻¹) * g) := by group

open scoped Pointwise in
private theorem disjoint_compl_frobeniusKernel_centralizer {G : Type*} [Group G]
    (htrans : ∀ x y z : G, x ≠ 1 → Commute x y → Commute x z → Commute y z)
    {x z : G} (hx : x ≠ 1)
    (hzK : z ∈ TauCeti.frobeniusKernel (Subgroup.centralizer ({x} : Set G))) (hz1 : z ≠ 1) :
    Disjoint ((TauCeti.frobeniusKernel (Subgroup.centralizer ({x} : Set G)))ᶜ)
      ((TauCeti.frobeniusKernel (Subgroup.centralizer ({z} : Set G)))ᶜ) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro u ⟨huA, huB⟩
  rw [Set.mem_compl_iff, TauCeti.notMem_frobeniusKernel_iff] at huA huB
  obtain ⟨hu1, g, hgA⟩ := huA
  obtain ⟨-, h, hhB⟩ := huB
  have hxg1 : g * x * g⁻¹ ≠ 1 := fun hc => hx (conj_eq_one_iff.mp hc)
  have huxg : Commute u (g * x * g⁻¹) := by
    have h1 : (g⁻¹ * u * g) * x = x * (g⁻¹ * u * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hgA
    show u * (g * x * g⁻¹) = (g * x * g⁻¹) * u
    calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * u := by group
  have hu_eq : Subgroup.centralizer ({u} : Set G) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) :=
    centralizer_singleton_eq_of_commute htrans hu1 hxg1 huxg
  have hzhu : Commute u (h * z * h⁻¹) := by
    have h1 : (h⁻¹ * u * h) * z = z * (h⁻¹ * u * h) :=
      Subgroup.mem_centralizer_singleton_iff.mp hhB
    show u * (h * z * h⁻¹) = (h * z * h⁻¹) * u
    calc u * (h * z * h⁻¹) = h * ((h⁻¹ * u * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * u * h)) * h⁻¹ := by rw [h1]
      _ = (h * z * h⁻¹) * u := by group
  have htarget := commute_conj_of_mem_centralizer_eq hu_eq hzhu
  have hmem_smul : h * z * h⁻¹ ∈
      MulAut.conj g • (Subgroup.centralizer ({x} : Set G) : Set G) := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change g⁻¹ * (h * z * h⁻¹) * g ∈ Subgroup.centralizer ({x} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr htarget
  have hzK2 : h * z * h⁻¹ ∈
      TauCeti.frobeniusKernel (Subgroup.centralizer ({x} : Set G)) := by
    rw [TauCeti.conj_mem_frobeniusKernel_iff]
    exact hzK
  have hinter : h * z * h⁻¹ ∈ ({1} : Set G) := by
    rw [← TauCeti.frobeniusKernel_inter_conj_smul_eq_singleton
      (H := Subgroup.centralizer ({x} : Set G)) g]
    exact ⟨hzK2, hmem_smul⟩
  rw [Set.mem_singleton_iff] at hinter; exact hz1 (conj_eq_one_iff.mp hinter)

private theorem exists_ne_one_mem_frobeniusKernel {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) {A : Subgroup G} (hTIS : TauCeti.IsTISubgroup A)
    (hidx : A.index ≠ 1) : ∃ z, z ∈ TauCeti.frobeniusKernel A ∧ z ≠ 1 := by
  have hoddA : Odd A.index := hodd.of_dvd_nat ⟨Nat.card A, A.index_mul_card.symm⟩
  have hidxA3 : 3 ≤ A.index := by
    obtain ⟨k, hk⟩ := hoddA
    omega
  have hKcard : (TauCeti.frobeniusKernel A).ncard = A.index := hTIS.ncard_frobeniusKernel
  by_contra h
  push Not at h
  have hle : (TauCeti.frobeniusKernel A).ncard ≤ 1 := by
    calc (TauCeti.frobeniusKernel A).ncard ≤ ({1} : Set G).ncard :=
          Set.ncard_mono fun z hz => by rw [Set.mem_singleton_iff]; exact h z hz
      _ = 1 := by simp
  rw [hKcard] at hle
  omega

private theorem centralizer_ne_top_of_mem_frobeniusKernel {G : Type*} [Group G] {x z : G}
    (hzK : z ∈ TauCeti.frobeniusKernel (Subgroup.centralizer ({x} : Set G))) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro hB
  have hzA : z ∈ Subgroup.centralizer ({x} : Set G) := by
    have hxB : x ∈ Subgroup.centralizer ({z} : Set G) := by rw [hB]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hxB).symm
  have h1 : z = 1 := by
    have hmem : z ∈ TauCeti.frobeniusKernel (Subgroup.centralizer ({x} : Set G)) ∩
        (Subgroup.centralizer ({x} : Set G) : Set G) := ⟨hzK, hzA⟩
    rw [TauCeti.frobeniusKernel_inter_eq_singleton] at hmem
    simpa using hmem
  exact hz1 h1

private theorem frobenius_index_le {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAG : A.index * Nat.card A = Nat.card G)
    (hineq : A.index * (Nat.card A - 1) + B.index * (Nat.card B - 1) ≤ Nat.card G) :
    B.index * (Nat.card B - 1) ≤ A.index := by
  have hA1 : 1 ≤ Nat.card A := by
    have : 0 < Nat.card A := Nat.card_pos (α := A)
    omega
  have hAG' : A.index * Nat.card A = A.index * (Nat.card A - 1) + A.index := by
    conv_lhs => rw [← Nat.sub_add_cancel hA1]
    rw [Nat.mul_add, Nat.mul_one]
  have h : A.index * (Nat.card A - 1) + B.index * (Nat.card B - 1) ≤
      A.index * (Nat.card A - 1) + A.index := by
    calc A.index * (Nat.card A - 1) + B.index * (Nat.card B - 1) ≤ Nat.card G := hineq
      _ = A.index * Nat.card A := hAG.symm
      _ = A.index * (Nat.card A - 1) + A.index := hAG'
  exact Nat.le_of_add_le_add_left h

private theorem frobenius_card_key {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAG : A.index * Nat.card A = Nat.card G) (hBG : B.index * Nat.card B = Nat.card G)
    (hqa : B.index * (Nat.card B - 1) ≤ A.index) :
    Nat.card A * (Nat.card B - 1) ≤ Nat.card B := by
  have hqpos : 0 < B.index := by
    by_contra h0
    rw [not_lt] at h0
    rw [Nat.le_zero.mp h0, zero_mul] at hBG
    exact (Nat.card_pos (α := G)).ne' hBG.symm
  have hmul : B.index * (Nat.card A * (Nat.card B - 1)) ≤ B.index * Nat.card B := by
    calc B.index * (Nat.card A * (Nat.card B - 1))
        = Nat.card A * (B.index * (Nat.card B - 1)) := by ring
      _ ≤ Nat.card A * A.index := Nat.mul_le_mul_left _ hqa
      _ = Nat.card G := by rw [mul_comm, hAG]
      _ = B.index * Nat.card B := hBG.symm
  exact Nat.le_of_mul_le_mul_left hmul hqpos

private theorem frobenius_final_contradiction {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) {A B : Subgroup G} (hAne : A ≠ ⊥) (hBne : B ≠ ⊥)
    (hkey : Nat.card A * (Nat.card B - 1) ≤ Nat.card B) : False := by
  have hAcard_odd : Odd (Nat.card A) :=
    hodd.of_dvd_nat ⟨A.index, by rw [mul_comm]; exact A.index_mul_card.symm⟩
  have hAcard_ne1 : Nat.card A ≠ 1 := fun h => hAne (Subgroup.card_eq_one.mp h)
  have hA3 : 3 ≤ Nat.card A := by
    obtain ⟨k, hk⟩ := hAcard_odd
    have : 0 < Nat.card A := Nat.card_pos (α := A)
    omega
  have hB2 : 2 ≤ Nat.card B := by
    have : 0 < Nat.card B := Nat.card_pos (α := B)
    have hne1 : Nat.card B ≠ 1 := fun h => hBne (Subgroup.card_eq_one.mp h)
    omega
  set t : ℕ := Nat.card B - 1 with ht
  have ht1 : 1 ≤ t := by omega
  have hb_eq : Nat.card B = t + 1 := by omega
  have h3t : 3 * t ≤ t + 1 := by
    calc 3 * t ≤ Nat.card A * t := Nat.mul_le_mul_right t hA3
      _ ≤ Nat.card B := hkey
      _ = t + 1 := hb_eq
  omega

private theorem ncard_union_compl_frobeniusKernel_le {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G}
    (hdisj : Disjoint ((TauCeti.frobeniusKernel A)ᶜ) ((TauCeti.frobeniusKernel B)ᶜ))
    (hXA : ((TauCeti.frobeniusKernel A)ᶜ).ncard = A.index * (Nat.card A - 1))
    (hXB : ((TauCeti.frobeniusKernel B)ᶜ).ncard = B.index * (Nat.card B - 1)) :
    A.index * (Nat.card A - 1) + B.index * (Nat.card B - 1) ≤ Nat.card G := by
  have hle : (((TauCeti.frobeniusKernel A)ᶜ) ∪ ((TauCeti.frobeniusKernel B)ᶜ)).ncard ≤
      Nat.card G := by
    rw [← Set.ncard_univ (α := G)]
    exact Set.ncard_mono (Set.subset_univ _)
  rw [Set.ncard_union_eq hdisj, hXA, hXB] at hle
  exact hle

theorem commute_of_odd_card_of_commute_trans {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (htrans : ∀ x y z : G, x ≠ 1 → Commute x y → Commute x z → Commute y z)
    (hsn : ∀ x g : G, x ≠ 1 → Commute x (g * x * g⁻¹) → Commute g x) (x y : G) :
    Commute x y := by
  by_cases hxy : Commute x y
  · exact hxy
  · exfalso
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxy (Commute.one_left y)
    let A : Subgroup G := Subgroup.centralizer ({x} : Set G)
    have hxmemA : x ∈ A := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x)
    have hAne : A ≠ ⊥ := fun h => hx1 (Subgroup.mem_bot.mp (h ▸ hxmemA))
    have hyA : y ∉ A := by
      intro hy
      exact hxy (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
    have hAtop : A ≠ ⊤ := fun h => hyA (by rw [h]; trivial)
    have hTIS_A : TauCeti.IsTISubgroup A := isTISubgroup_centralizer htrans hsn hx1
    have hidxA : A.index ≠ 1 := fun h => hAtop (Subgroup.index_eq_one.mp h)
    have hAG : A.index * Nat.card A = Nat.card G := A.index_mul_card
    obtain ⟨z, hzK, hz1⟩ := exists_ne_one_mem_frobeniusKernel hodd hTIS_A hidxA
    let B : Subgroup G := Subgroup.centralizer ({z} : Set G)
    have hzmemB : z ∈ B := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl z)
    have hBne : B ≠ ⊥ := fun h => hz1 (Subgroup.mem_bot.mp (h ▸ hzmemB))
    have hTIS_B : TauCeti.IsTISubgroup B := isTISubgroup_centralizer htrans hsn hz1
    have hBtop : B ≠ ⊤ := centralizer_ne_top_of_mem_frobeniusKernel hzK hz1
    have hidxB : B.index ≠ 1 := fun h => hBtop (Subgroup.index_eq_one.mp h)
    have hBG : B.index * Nat.card B = Nat.card G := B.index_mul_card
    have hineq : A.index * (Nat.card A - 1) + B.index * (Nat.card B - 1) ≤ Nat.card G :=
      ncard_union_compl_frobeniusKernel_le
        (disjoint_compl_frobeniusKernel_centralizer htrans hx1 hzK hz1)
        hTIS_A.ncard_compl_frobeniusKernel hTIS_B.ncard_compl_frobeniusKernel
    have hqa : B.index * (Nat.card B - 1) ≤ A.index := frobenius_index_le hAG hineq
    have hkey : Nat.card A * (Nat.card B - 1) ≤ Nat.card B :=
      frobenius_card_key hAG hBG hqa
    exact frobenius_final_contradiction hodd hAne hBne hkey

section RankTwo

variable [Module.Finite (ZMod p) U]

omit [Module.Finite (ZMod p) U] in
private theorem range_le_ker_of_mul_self_eq_zero {N : U →ₗ[ZMod p] U} (hN2 : N * N = 0) :
    LinearMap.range N ≤ LinearMap.ker N := by
  rintro w ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  have h := congrArg (fun f : U →ₗ[ZMod p] U => f v) hN2
  simpa [Module.End.mul_apply] using h

private theorem mem_dilatransvections_of_square_zero (hU : Module.finrank (ZMod p) U = 2)
    {g : U ≃ₗ[ZMod p] U}
    (hN2 : ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) - 1) = 0) :
    g ∈ LinearEquiv.dilatransvections (ZMod p) U := by
  have hrank : Module.finrank (ZMod p) (LinearMap.range ((g : U →ₗ[ZMod p] U) - 1)) ≤ 1 := by
    have hle := range_le_ker_of_mul_self_eq_zero hN2
    have h1 := Submodule.finrank_mono hle
    have h2 := LinearMap.finrank_range_add_finrank_ker ((g : U →ₗ[ZMod p] U) - 1)
    omega
  rw [LinearEquiv.mem_dilatransvections_iff_finrank]
  change Module.finrank (ZMod p) (LinearMap.range ((g : U →ₗ[ZMod p] U) - 1)) ≤ 1
  exact hrank

omit [Module.Finite (ZMod p) U] in
private theorem transvection_fv_eq_zero {g : U ≃ₗ[ZMod p] U} {f : Module.Dual (ZMod p) U} {v : U}
    (hfv_eq : (g : U →ₗ[ZMod p] U) = LinearMap.transvection f v)
    (hN2 : ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) - 1) = 0)
    (hNne : (g : U →ₗ[ZMod p] U) - 1 ≠ 0) : f v = 0 := by
  have hT : LinearMap.transvection f v - 1 = (g : U →ₗ[ZMod p] U) - 1 := by rw [hfv_eq]
  have hsq : (LinearMap.transvection f v - 1) * (LinearMap.transvection f v - 1) = 0 := by
    rw [hT]; exact hN2
  have hsq' : (LinearMap.transvection f v - 1) * (LinearMap.transvection f v - 1)
      = (f v) • (LinearMap.transvection f v - 1) := by
    ext x
    show (LinearMap.transvection f v - 1) ((LinearMap.transvection f v - 1) x)
        = (f v) • ((LinearMap.transvection f v - 1) x)
    have h1 : (LinearMap.transvection f v - 1) x = f x • v := by
      rw [LinearMap.sub_apply, LinearMap.transvection.apply, Module.End.one_apply]
      abel
    rw [h1, LinearMap.sub_apply, LinearMap.transvection.apply, Module.End.one_apply,
      map_smul, smul_eq_mul, smul_smul]
    module
  have hcN : (f v) • ((g : U →ₗ[ZMod p] U) - 1) = 0 := by
    rw [← hT, ← hsq', hsq]
  obtain ⟨w, hw⟩ : ∃ w, ((g : U →ₗ[ZMod p] U) - 1) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hNne (LinearMap.ext h)
  have h := congrArg (fun f : U →ₗ[ZMod p] U => f w) hcN
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at h
  exact (smul_eq_zero.mp h).resolve_right hw

omit [Module.Finite (ZMod p) U] in
private theorem isTransvectionLin_of_transvection_eq {g : U ≃ₗ[ZMod p] U}
    {f : Module.Dual (ZMod p) U} {v : U}
    (hfv_eq : (g : U →ₗ[ZMod p] U) = LinearMap.transvection f v) (hgne : g ≠ 1)
    (hfv0 : f v = 0) : QTwoLin.IsTransvectionLin g := by
  refine ⟨v, f, ?_, ?_, hfv0, fun x => ?_⟩
  · intro hv0
    exact hgne (by
      refine LinearEquiv.ext fun x => ?_
      have h := congrArg (fun e : U →ₗ[ZMod p] U => e x) hfv_eq
      simpa [hv0, LinearMap.transvection.of_right_eq_zero] using h)
  · intro hf0
    exact hgne (by
      refine LinearEquiv.ext fun x => ?_
      have h := congrArg (fun e : U →ₗ[ZMod p] U => e x) hfv_eq
      simpa [hf0, LinearMap.transvection.of_left_eq_zero] using h)
  · have h := congrArg (fun e : U →ₗ[ZMod p] U => e x) hfv_eq
    simpa [LinearMap.transvection.apply] using h

private theorem isTransvectionLin_of_square_zero (hU : Module.finrank (ZMod p) U = 2)
    {g : U ≃ₗ[ZMod p] U}
    (hN2 : ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) - 1) = 0)
    (hNne : (g : U →ₗ[ZMod p] U) - 1 ≠ 0) (hgne : g ≠ 1) :
    QTwoLin.IsTransvectionLin g := by
  have hdil := mem_dilatransvections_of_square_zero hU (g := g) hN2
  obtain ⟨f, v, hfv_eq⟩ := hdil
  exact isTransvectionLin_of_transvection_eq (g := g) hfv_eq hgne
    (transvection_fv_eq_zero (g := g) hfv_eq hN2 hNne)

private theorem square_zero_sub_one_of_prime_order (hU : Module.finrank (ZMod p) U = 2)
    {g : U ≃ₗ[ZMod p] U} (hord : orderOf g = p) (hgne : g ≠ 1) :
    ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) - 1) = 0 ∧
      (g : U →ₗ[ZMod p] U) - 1 ≠ 0 := by
  have hpow : (g : U ≃ₗ[ZMod p] U) ^ p = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hord] at h
  set N : U →ₗ[ZMod p] U := (g : U →ₗ[ZMod p] U) - 1 with hN
  have : CharP (U →ₗ[ZMod p] U) p := by
    refine Module.charP_end (p := p) ?_
    have hpos : 0 < Module.finrank (ZMod p) U := by rw [hU]; norm_num
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨x, (Ideal.torsionOf_eq_bot_iff_of_isTorsionFree (ZMod p) x).mpr hx⟩
  have hgpow : ((g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ^ p = 1 := by
    ext x
    rw [Module.End.pow_apply, Module.End.one_apply]
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e x) hpow
    simpa [LinearEquiv.pow_apply] using h
  have hNp : N ^ p = 0 := by
    have h2 := sub_pow_char_of_commute (p := p) (x := (g : U →ₗ[ZMod p] U))
      (y := (1 : U →ₗ[ZMod p] U)) (Commute.one_right _)
    simpa [hN, hgpow, one_pow] using h2
  have hnil : IsNilpotent N := ⟨p, hNp⟩
  have hchar : N.charpoly = Polynomial.X ^ 2 := by
    rw [hnil.charpoly_eq_X_pow_finrank, hU]
  have hN2 : N * N = 0 := by
    have h := LinearMap.aeval_self_charpoly N
    rw [hchar] at h
    simpa [pow_two] using h
  have hNne : N ≠ 0 := by
    intro h0
    apply hgne
    refine LinearEquiv.ext fun v => ?_
    have h := congrArg (fun f : U →ₗ[ZMod p] U => f v) h0
    simpa [hN, LinearMap.sub_apply, sub_eq_zero] using h
  exact ⟨by simpa [hN] using hN2, by simpa [hN] using hNne⟩

private theorem isTransvectionLin_of_prime_order (hp : p.Prime)
    (hU : Module.finrank (ZMod p) U = 2) {g : U ≃ₗ[ZMod p] U} (hord : orderOf g = p) :
    QTwoLin.IsTransvectionLin g := by
  have hgne : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact hp.ne_one hord.symm
  obtain ⟨hN2, hNne⟩ := square_zero_sub_one_of_prime_order hU hord hgne
  exact isTransvectionLin_of_square_zero hU (g := g) hN2 hNne hgne

theorem coprime_card_of_finrank_two (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (htv : QTwoLin.TransvectionFree J) :
    Nat.Coprime (Nat.card J) p := by
  have hp : p.Prime := Fact.out
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpdvd
  have : Fintype U := by
    let b := Module.finBasisOfFinrankEq (ZMod p) U hU
    exact Fintype.ofEquiv (Fin 2 → ZMod p) b.equivFun.symm.toEquiv
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  have : Finite J := Subtype.finite
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpdvd
  have hord : orderOf (g : U ≃ₗ[ZMod p] U) = p := by
    rw [Subgroup.orderOf_coe g]; exact hgord
  exact htv (g : U ≃ₗ[ZMod p] U) g.2 (isTransvectionLin_of_prime_order hp hU hord)
theorem ker_sub_one_eq_bot_of_det_eq_one (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (htv : QTwoLin.TransvectionFree J) {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ J) (hdet : LinearEquiv.det a = 1) (ha1 : a ≠ 1) :
    LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥ := by
  by_contra hker
  have hrank : Module.finrank (ZMod p) (LinearMap.range ((a : U →ₗ[ZMod p] U) - 1)) ≤ 1 := by
    have hpos : 1 ≤ Module.finrank (ZMod p) (LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1)) :=
      Nat.one_le_iff_ne_zero.mpr fun h => hker (Submodule.finrank_eq_zero.mp h)
    have h2 := LinearMap.finrank_range_add_finrank_ker ((a : U →ₗ[ZMod p] U) - 1)
    omega
  have hdil : a ∈ LinearEquiv.dilatransvections (ZMod p) U := by
    rw [LinearEquiv.mem_dilatransvections_iff_finrank]
    exact hrank
  obtain ⟨f, v, hfv_eq⟩ := hdil
  have hdetL : LinearMap.det (a : U →ₗ[ZMod p] U) = 1 := by
    rw [← LinearEquiv.coe_det a, hdet]
    rfl
  have hfv0 : f v = 0 := by
    have h1 : (LinearMap.transvection f v).det = 1 + f v := LinearMap.transvection.det f v
    rw [← hfv_eq, hdetL] at h1
    exact (add_left_cancel (show (1 : ZMod p) + 0 = 1 + f v by rw [add_zero]; exact h1)).symm
  have htransv : QTwoLin.IsTransvectionLin a := by
    refine ⟨v, f, ?_, ?_, hfv0, fun x => ?_⟩
    · intro hv0
      exact ha1 (by
        refine LinearEquiv.ext fun x => ?_
        have h := congrArg (fun e : U →ₗ[ZMod p] U => e x) hfv_eq
        simpa [hv0, LinearMap.transvection.of_right_eq_zero] using h)
    · intro hf0
      exact ha1 (by
        refine LinearEquiv.ext fun x => ?_
        have h := congrArg (fun e : U →ₗ[ZMod p] U => e x) hfv_eq
        simpa [hf0, LinearMap.transvection.of_left_eq_zero] using h)
    · have h := congrArg (fun e : U →ₗ[ZMod p] U => e x) hfv_eq
      simpa [LinearMap.transvection.apply] using h
  exact (htv a ha) htransv

private theorem mul_neg_one_neg {R : Type*} [CommRing R] (a : R) : a * (-1) = -a := by ring

omit [Module.Finite (ZMod p) U] in
private theorem ker_add_one_eq_bot_of_odd_order (hp : p ≠ 2) {x : U ≃ₗ[ZMod p] U}
    (hodd : Odd (orderOf x)) :
    LinearMap.ker ((x : U →ₗ[ZMod p] U) + 1) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hv' : (x : U →ₗ[ZMod p] U) v = -v := by
    have h := hv
    simp only [LinearMap.add_apply, Module.End.one_apply] at h
    exact eq_neg_of_add_eq_zero_left h
  have hpow : ∀ n : ℕ,
      (((x ^ n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v) = (-1 : ZMod p) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        calc (((x ^ (k + 1) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v)
            = ((x ^ k : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
                (((x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v) := by
              change (((x ^ k : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
                  * ((x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) v
                = ((x ^ k : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
                  (((x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v)
              rw [Module.End.mul_apply]
          _ = ((x ^ k : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (-v) := by rw [hv']
          _ = - (((x ^ k : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v) := by rw [map_neg]
          _ = - ((-1 : ZMod p) ^ k • v) := by rw [ih]
          _ = (-1 : ZMod p) ^ (k + 1) • v := by
                rw [← neg_smul]
                congr 1
                rw [pow_succ]
                exact (mul_neg_one_neg ((-1 : ZMod p) ^ k)).symm
  have hm : v = (-1 : ZMod p) ^ orderOf x • v := by
    simpa using hpow (orderOf x)
  have hneg : (-1 : ZMod p) ^ orderOf x = -1 := hodd.neg_one_pow
  rw [hneg, show (-1 : ZMod p) • v = -v from neg_one_smul (ZMod p) v] at hm
  have h2v : (2 : ZMod p) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hm]
    rw [neg_add_cancel]
  exact (smul_eq_zero.mp h2v).resolve_left (ZMod.prime_ne_zero p 2 hp)

private theorem commute_of_conj_eq_inv_of_odd_order {G : Type*} [Group G] {g x : G}
    (hodd : Odd (orderOf g)) (h : g * x * g⁻¹ = x⁻¹) : Commute g x := by
  have hg2 : Commute (g * g) x := by
    have h2 : g * g * x * (g * g)⁻¹ = x := by
      rw [mul_inv_rev]
      calc g * g * x * (g⁻¹ * g⁻¹) = g * (g * x * g⁻¹) * g⁻¹ := by group
        _ = g * x⁻¹ * g⁻¹ := by rw [h]
        _ = (g * x * g⁻¹)⁻¹ := by group
        _ = x := by rw [h, inv_inv]
    calc g * g * x = (g * g * x * (g * g)⁻¹) * (g * g) := by group
      _ = x * (g * g) := by rw [h2]
  obtain ⟨m, hm⟩ := hodd
  have hodd2 : 2 * ((orderOf g + 1) / 2) = orderOf g + 1 := by omega
  have hgm : g = (g * g) ^ ((orderOf g + 1) / 2) := by
    rw [← pow_two, ← pow_mul, hodd2, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hgm]
  exact hg2.pow_left _

private theorem reflGen_ne_bot_of_irreducible (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    J ≠ ⊥ := by
  intro hbot
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (by rw [hU]; norm_num : 0 < Module.finrank (ZMod p) U)
  have hfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v}) = 1 :=
    finrank_span_singleton hv
  have hinv : ∀ g ∈ J, ∀ w ∈ Submodule.span (ZMod p) {v},
      g w ∈ Submodule.span (ZMod p) {v} := by
    intro g hg w hw
    rw [hbot, Subgroup.mem_bot] at hg
    subst hg
    simpa using hw
  rcases hirr _ hinv with h | h
  · rw [h, finrank_bot] at hfin; omega
  · rw [h, finrank_top, hU] at hfin; omega

omit [Module.Finite (ZMod p) U] in
private theorem exists_isRefl_of_ne_bot {J : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p J)
    (hnonbot : J ≠ ⊥) : ∃ r ∈ J, IsRefl p r := by
  by_contra h
  push Not at h
  have hset : {t : U ≃ₗ[ZMod p] U | t ∈ J ∧ IsRefl p t} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact h t
  exact hnonbot (by rw [hgen, hset]; simp)

omit [Module.Finite (ZMod p) U] in
private theorem fixedSpace_invariant_of_commute {J : Subgroup (U ≃ₗ[ZMod p] U)}
    {r : U ≃ₗ[ZMod p] U}
    (hJleC : J ≤ Subgroup.centralizer ({r} : Set (U ≃ₗ[ZMod p] U))) :
    ∀ g ∈ J, ∀ w ∈ LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1),
      g w ∈ LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1) := by
  intro g hg w hw
  have hcomm : g * r = r * g := Subgroup.mem_centralizer_singleton_iff.mp (hJleC hg)
  have hgr : r (g w) = g (r w) := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hcomm
    simpa using h.symm
  have hw' : r w = w := by
    have h := LinearMap.mem_ker.mp hw
    simpa [LinearMap.sub_apply, Module.End.one_apply] using sub_eq_zero.mp h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  show r (g w) = g w
  rw [hgr, hw']

private theorem exists_two_isRefl_of_reflGen (_hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p J)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ r ∈ J, ∃ r' ∈ J, IsRefl p r ∧ IsRefl p r' ∧ r ≠ r' := by
  have hnonbot : J ≠ ⊥ := reflGen_ne_bot_of_irreducible hU hirr
  obtain ⟨r, hrJ, hrr⟩ := exists_isRefl_of_ne_bot hgen hnonbot
  refine ⟨r, hrJ, ?_⟩
  by_contra h
  have h2r : ∀ t ∈ J, IsRefl p t → t = r := by
    intro t htJ ht
    by_contra hne
    exact h ⟨t, htJ, hrr, ht, fun hrt => hne hrt.symm⟩
  have hfix : Module.finrank (ZMod p) (LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1)) = 1 := by
    have h2 := LinearMap.finrank_range_add_finrank_ker ((r : U →ₗ[ZMod p] U) - 1)
    have hr2 : Module.finrank (ZMod p) (LinearMap.range ((r : U →ₗ[ZMod p] U) - 1)) = 1 := by
      simpa [Module.End.one_eq_id] using hrr.2
    rw [hr2, hU] at h2
    omega
  have hJleC : J ≤ Subgroup.centralizer ({r} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [hgen, Subgroup.closure_le]
    intro t ht
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [h2r t ht.1 ht.2]
  have hinv := fixedSpace_invariant_of_commute hJleC
  rcases hirr _ hinv with hbot | htop
  · rw [hbot, finrank_bot] at hfix; omega
  · have hr1 : r = 1 := by
      refine LinearEquiv.ext fun w => ?_
      have h : w ∈ LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1) := by rw [htop]; trivial
      exact sub_eq_zero.mp (LinearMap.mem_ker.mp h)
    have hr2 : Module.finrank (ZMod p) (LinearMap.range ((r : U →ₗ[ZMod p] U) - 1)) = 1 := by
      simpa [Module.End.one_eq_id] using hrr.2
    have h0 : Module.finrank (ZMod p) (LinearMap.range ((r : U →ₗ[ZMod p] U) - 1)) = 0 := by
      have hrsub : (r : U →ₗ[ZMod p] U) - 1 = 0 := by rw [hr1]; ext w; simp
      rw [hrsub]; simp
    rw [hr2] at h0; omega

theorem coprimeWitness_of_finrank_two (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p J) (htv : QTwoLin.TransvectionFree J)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    CoprimeWitness p J := by
  obtain ⟨r, hrJ, r', hr'J, hrr, hr'r, hrne⟩ := exists_two_isRefl_of_reflGen hp hU hgen hirr
  set D : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({r * r'} : Set (U ≃ₗ[ZMod p] U)) with hD
  have hrr'J : r * r' ∈ J := J.mul_mem hrJ hr'J
  have hDJ : D ≤ J := by
    rw [hD, Subgroup.closure_le]
    rintro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hrr'J
  have htvD : QTwoLin.TransvectionFree D := fun g hg => htv g (hDJ hg)
  have hcop : Nat.Coprime (Nat.card D) p := coprime_card_of_finrank_two hU htvD
  have hdet : LinearEquiv.det (r * r') = 1 := by
    have h1 : LinearEquiv.det r = -1 := det_eq_neg_one_of_isRefl hp hrr
    have h2 : LinearEquiv.det r' = -1 := det_eq_neg_one_of_isRefl hp hr'r
    rw [map_mul, h1, h2, neg_mul_neg, one_mul]
  have hne : r * r' ≠ 1 := by
    intro h
    have h2 : r' = r := by
      calc r' = 1 * r' := by rw [one_mul]
        _ = (r * r) * r' := by rw [hrr.1]
        _ = r * (r * r') := by rw [mul_assoc]
        _ = r * 1 := by rw [h]
        _ = r := by rw [mul_one]
    exact hrne h2.symm
  have hker : LinearMap.ker (((r * r' : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) = ⊥ :=
    ker_sub_one_eq_bot_of_det_eq_one hU htv hrr'J hdet hne
  have htop : HardMathSupport.Kantor79.movedSpace (r * r') = ⊤ := by
    have h2 := LinearMap.finrank_range_add_finrank_ker
      (((r * r' : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)
    rw [hker, finrank_bot, hU] at h2
    refine Submodule.eq_top_of_finrank_eq ?_
    change Module.finrank (ZMod p) (LinearMap.range
      (((r * r' : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)) = Module.finrank (ZMod p) U
    rw [hU, ← h2, add_zero]
    rfl
  refine ⟨D, hDJ, hcop, le_antisymm le_top ?_⟩
  rw [← htop]
  exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (Subgroup.subset_closure (by simp))

omit [Module.Finite (ZMod p) U] in
private theorem eq_neg_one_of_sq_eq_one_of_ker_sub_one_eq_bot
    {g : U ≃ₗ[ZMod p] U} (hg2 : g * g = 1)
    (hker : LinearMap.ker ((g : U →ₗ[ZMod p] U) - 1) = ⊥) :
    g = LinearEquiv.neg (ZMod p) := by
  have hgg : ((g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
      * ((g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = 1 := by
    ext v
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hg2
    simpa [Module.End.mul_apply, LinearEquiv.mul_apply] using h
  have hprod : ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) + 1) = 0 := by
    calc ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) + 1)
        = (g : U →ₗ[ZMod p] U) * (g : U →ₗ[ZMod p] U) - 1 := by
          rw [sub_mul, one_mul, mul_add, mul_one]; abel
      _ = 1 - 1 := by rw [hgg]
      _ = 0 := by rw [sub_self]
  have hsum : (g : U →ₗ[ZMod p] U) + 1 = 0 := by
    have hinj := LinearMap.ker_eq_bot.mp hker
    ext v
    have h : ((g : U →ₗ[ZMod p] U) - 1) * ((g : U →ₗ[ZMod p] U) + 1)
        = ((g : U →ₗ[ZMod p] U) - 1) * 0 := by rw [hprod, mul_zero]
    have h2 := congrArg (fun f : U →ₗ[ZMod p] U => f v) h
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at h2
    exact hinj h2
  refine LinearEquiv.ext fun v => ?_
  have h := congrArg (fun f : U →ₗ[ZMod p] U => f v) hsum
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply] at h
  simpa [LinearEquiv.neg_apply] using eq_neg_of_add_eq_zero_left h

theorem odd_card_ker_det_of_finrank_two (_hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (htv : QTwoLin.TransvectionFree J)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ J) :
    Odd (Nat.card ↥(J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ))) := by
  set K : Subgroup (U ≃ₗ[ZMod p] U) :=
    J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ) with hK
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2dvd : 2 ∣ Nat.card ↥K := even_iff_two_dvd.mp heven
  have : Fintype U := by
    let b := Module.finBasisOfFinrankEq (ZMod p) U hU
    exact Fintype.ofEquiv (Fin 2 → ZMod p) b.equivFun.symm.toEquiv
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  have : Finite ↥K := Subtype.finite
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2dvd
  have hord : orderOf (g : U ≃ₗ[ZMod p] U) = 2 := by
    rw [Subgroup.orderOf_coe g]; exact hgord
  have hgJ : (g : U ≃ₗ[ZMod p] U) ∈ J := g.2.1
  have hgdet : LinearEquiv.det (g : U ≃ₗ[ZMod p] U) = 1 :=
    MonoidHom.mem_ker.mp g.2.2
  have hg1 : (g : U ≃ₗ[ZMod p] U) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hker : LinearMap.ker (((g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) = ⊥ :=
    ker_sub_one_eq_bot_of_det_eq_one hU htv hgJ hgdet hg1
  have hg2 : (g : U ≃ₗ[ZMod p] U) * (g : U ≃ₗ[ZMod p] U) = 1 := by
    have h := pow_orderOf_eq_one (g : U ≃ₗ[ZMod p] U)
    rw [hord] at h
    simpa [pow_two] using h
  have hneg' := eq_neg_one_of_sq_eq_one_of_ker_sub_one_eq_bot hg2 hker
  exact hneg (hneg' ▸ hgJ)

omit [Module.Finite (ZMod p) U] in
theorem commute_of_commute_of_ne_smul (hU : Module.finrank (ZMod p) U = 2)
    {a g h : U ≃ₗ[ZMod p] U} (ha : ∀ c : ZMod p, (a : U →ₗ[ZMod p] U) ≠ c • LinearMap.id)
    (hg : Commute a g) (hh : Commute a h) : Commute g h := by
  have hg' : Commute (a : U →ₗ[ZMod p] U) (g : U →ₗ[ZMod p] U) := by
    ext v
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hg.eq
    simpa [LinearEquiv.mul_apply] using h
  have hh' : Commute (a : U →ₗ[ZMod p] U) (h : U →ₗ[ZMod p] U) := by
    ext v
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hh.eq
    simpa [LinearEquiv.mul_apply] using h
  have hgh : Commute (g : U →ₗ[ZMod p] U) (h : U →ₗ[ZMod p] U) :=
    CFSG.ClassicalGroups.SpecialLinear.TvMod.commute_of_commute_of_finrank_eq_two hU ha hg' hh'
  ext v
  have h := congrArg (fun f : U →ₗ[ZMod p] U => f v) hgh.eq
  simpa [LinearEquiv.mul_apply] using h

private theorem mul_self_eq_trace_smul_sub_det_smul_finrank_two
    (hU : Module.finrank (ZMod p) U = 2) (f : U →ₗ[ZMod p] U) :
    f * f = (LinearMap.trace (ZMod p) U f) • f - (LinearMap.det f) • 1 := by
  let b := Module.finBasisOfFinrankEq (ZMod p) U hU
  let ψ := LinearMap.toMatrixAlgEquiv b
  have hmat : (ψ f) * (ψ f) = (ψ f).trace • (ψ f) - (ψ f).det • 1 := by
    simpa [pow_two] using Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two (ψ f)
  have h := congrArg ψ.symm hmat
  simp only [map_mul, map_sub, map_smul, map_one, ψ.symm_apply_apply] at h
  have htrace : (ψ f).trace = LinearMap.trace (ZMod p) U f :=
    (LinearMap.trace_eq_matrix_trace (ZMod p) b f).symm
  have hdet : (ψ f).det = LinearMap.det f := LinearMap.det_toMatrix b f
  rw [htrace, hdet] at h
  exact h

private theorem one_sub_mul_one_add {R : Type*} [CommRing R] (y : R) :
    (1 - y) * (1 + y) = 1 - y ^ 2 := by ring

private theorem final_identity {R : Type*} [CommRing R] (x y T : R) :
    (1 - y ^ 2) * (T ^ 2 - 4) = -2 * (2 * x ^ 2 + 2 * x * y * T + y ^ 2 * (T ^ 2 - 2)
      - (T ^ 2 - 2)) + (2 * x + y * T + T) * ((2 * x + y * T) - T) := by ring

private theorem two_mul_add_neg_one_mul {R : Type*} [CommRing R] (a : R) :
    2 * a + (-1) * a = a := by ring

private theorem ne_smul_one_of_ker_and_det (_hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {a : U ≃ₗ[ZMod p] U} (hdet : LinearEquiv.det a = 1)
    (h1 : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥)
    (h2 : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) = ⊥) :
    ∀ k : ZMod p, (a : U →ₗ[ZMod p] U) ≠ k • LinearMap.id := by
  intro k hk
  have hdetL : LinearMap.det (a : U →ₗ[ZMod p] U) = 1 := by
    rw [← LinearEquiv.coe_det a, hdet]; rfl
  have hk2 : k ^ 2 = 1 := by
    rw [hk] at hdetL
    have h := LinearMap.det_smul k (LinearMap.id : U →ₗ[ZMod p] U)
    rw [LinearMap.det_id, mul_one, hU] at h
    rwa [h] at hdetL
  have hkpm : k = 1 ∨ k = -1 := by
    have h : (k - 1) * (k + 1) = 0 := by linear_combination hk2
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (eq_neg_of_add_eq_zero_left h')
  rcases hkpm with rfl | rfl
  · have hz : (a : U →ₗ[ZMod p] U) - 1 = 0 := by
      rw [hk, one_smul, Module.End.one_eq_id, sub_self]
    rw [hz, LinearMap.ker_zero] at h1
    have hs : Subsingleton U := ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule (ZMod p) U) := h1 ▸ Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule (ZMod p) U) := h1 ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy; rw [hx, hy]⟩
    have := hs
    rw [Module.finrank_zero_iff.mpr hs] at hU
    norm_num at hU
  · have hz : (a : U →ₗ[ZMod p] U) + 1 = 0 := by
      rw [hk]
      ext v
      rw [LinearMap.add_apply, LinearMap.smul_apply]
      change -1 • v + v = 0
      rw [show (-1 : ZMod p) • v = -v from neg_one_smul (ZMod p) v]
      abel
    rw [hz, LinearMap.ker_zero] at h2
    have hs : Subsingleton U := ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule (ZMod p) U) := h2 ▸ Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule (ZMod p) U) := h2 ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy; rw [hx, hy]⟩
    have := hs
    rw [Module.finrank_zero_iff.mpr hs] at hU
    norm_num at hU

private theorem false_of_trace_eq_two_and_ker_sub_one_eq_bot
    (hU : Module.finrank (ZMod p) U = 2) {a : U ≃ₗ[ZMod p] U} {T : ZMod p}
    (h1 : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥)
    (hT2 : T = 2)
    (haCH : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = T • (a : U →ₗ[ZMod p] U) - 1) :
    False := by
  have h := haCH
  rw [hT2] at h
  have hsq : ((a : U →ₗ[ZMod p] U) - 1) * ((a : U →ₗ[ZMod p] U) - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_one, one_mul, h, two_smul]
    abel
  have hinj := LinearMap.ker_eq_bot.mp h1
  have hzero : (a : U →ₗ[ZMod p] U) - 1 = 0 := by
    ext x
    exact hinj (by rw [← Module.End.mul_apply, hsq, LinearMap.zero_apply, map_zero])
  rw [hzero, LinearMap.ker_zero] at h1
  have hs : Subsingleton U := ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule (ZMod p) U) := h1 ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule (ZMod p) U) := h1 ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy; rw [hx, hy]⟩
  have := hs
  rw [Module.finrank_zero_iff.mpr hs] at hU
  norm_num at hU

private theorem false_of_trace_eq_neg_two_and_ker_add_one_eq_bot
    (hU : Module.finrank (ZMod p) U = 2) {a : U ≃ₗ[ZMod p] U} {T : ZMod p}
    (h2 : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) = ⊥)
    (hT2 : T = -2)
    (haCH : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = T • (a : U →ₗ[ZMod p] U) - 1) :
    False := by
  have h := haCH
  rw [hT2] at h
  have hsq : ((a : U →ₗ[ZMod p] U) + 1) * ((a : U →ₗ[ZMod p] U) + 1) = 0 := by
    rw [add_mul, mul_add, mul_one, one_mul, h]
    rw [show (-2 : ZMod p) • (a : U →ₗ[ZMod p] U)
        = -((2 : ZMod p) • (a : U →ₗ[ZMod p] U))
        from neg_smul (2 : ZMod p) (a : U →ₗ[ZMod p] U)]
    rw [two_smul]
    abel
  have hinj := LinearMap.ker_eq_bot.mp h2
  have hzero : (a : U →ₗ[ZMod p] U) + 1 = 0 := by
    ext x
    exact hinj (by rw [← Module.End.mul_apply, hsq, LinearMap.zero_apply, map_zero])
  rw [hzero, LinearMap.ker_zero] at h2
  have hs : Subsingleton U := ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule (ZMod p) U) := h2 ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule (ZMod p) U) := h2 ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy; rw [hx, hy]⟩
  have := hs
  rw [Module.finrank_zero_iff.mpr hs] at hU
  norm_num at hU

private theorem trace_sq_ne_four_of_ker_eq_bot (_hp : p ≠ 2)
    (hU : Module.finrank (ZMod p) U = 2) {a : U ≃ₗ[ZMod p] U} (hdet : LinearEquiv.det a = 1)
    (h1 : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥)
    (h2 : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) = ⊥) :
    (LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U)) ^ 2 ≠ 4 := by
  set T : ZMod p := LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U) with hTdef
  have hdetL : LinearMap.det (a : U →ₗ[ZMod p] U) = 1 := by
    rw [← LinearEquiv.coe_det a, hdet]; rfl
  have haCH : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = T • (a : U →ₗ[ZMod p] U) - 1 := by
    rw [mul_self_eq_trace_smul_sub_det_smul_finrank_two hU, hdetL, hTdef, one_smul]
  intro hT
  have hTm : T = 2 ∨ T = -2 := by
    have h : (T - 2) * (T + 2) = 0 := by linear_combination hT
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (eq_neg_of_add_eq_zero_left h')
  rcases hTm with hT2 | hT2
  · exact false_of_trace_eq_two_and_ker_sub_one_eq_bot hU h1 hT2 haCH
  · exact false_of_trace_eq_neg_two_and_ker_add_one_eq_bot hU h2 hT2 haCH

omit [Module.Finite (ZMod p) U] in
private theorem trace_conj (g : U ≃ₗ[ZMod p] U) (f : U →ₗ[ZMod p] U) :
    LinearMap.trace (ZMod p) U ((g : U →ₗ[ZMod p] U) * f * (g.symm : U →ₗ[ZMod p] U))
      = LinearMap.trace (ZMod p) U f := by
  have hg1 : (g.symm : U →ₗ[ZMod p] U) * (g : U →ₗ[ZMod p] U) = 1 := by
    ext w
    rw [Module.End.mul_apply, Module.End.one_apply]
    exact g.symm_apply_apply w
  calc LinearMap.trace (ZMod p) U ((g : U →ₗ[ZMod p] U) * f * (g.symm : U →ₗ[ZMod p] U))
      = LinearMap.trace (ZMod p) U
          (f * (g.symm : U →ₗ[ZMod p] U) * (g : U →ₗ[ZMod p] U)) := by
        rw [mul_assoc, LinearMap.trace_mul_comm]
    _ = LinearMap.trace (ZMod p) U f := by simp only [mul_assoc, hg1, mul_one]

private theorem trace_sq_of_eq_conj (hU : Module.finrank (ZMod p) U = 2)
    (T : ZMod p) {c a : U →ₗ[ZMod p] U} {g : U ≃ₗ[ZMod p] U}
    (hc : c = (g : U →ₗ[ZMod p] U) * a * (g.symm : U →ₗ[ZMod p] U))
    (hT : LinearMap.trace (ZMod p) U a = T) (haCH : a * a = T • a - 1) :
    LinearMap.trace (ZMod p) U (c * c) = T ^ 2 - 2 := by
  have hg1 : (g.symm : U →ₗ[ZMod p] U) * (g : U →ₗ[ZMod p] U) = 1 := by
    ext w
    rw [Module.End.mul_apply, Module.End.one_apply]
    exact g.symm_apply_apply w
  have heq : c * c = (g : U →ₗ[ZMod p] U) * (a * a) * (g.symm : U →ₗ[ZMod p] U) := by
    rw [hc]
    calc ((g : U →ₗ[ZMod p] U) * a * (g.symm : U →ₗ[ZMod p] U))
          * ((g : U →ₗ[ZMod p] U) * a * (g.symm : U →ₗ[ZMod p] U))
        = (g : U →ₗ[ZMod p] U) * a
            * ((g.symm : U →ₗ[ZMod p] U) * (g : U →ₗ[ZMod p] U))
            * a * (g.symm : U →ₗ[ZMod p] U) := by
          simp only [mul_assoc]
      _ = (g : U →ₗ[ZMod p] U) * (a * a) * (g.symm : U →ₗ[ZMod p] U) := by
          rw [hg1, mul_one]; simp only [mul_assoc]
  rw [heq, trace_conj, haCH]
  change (LinearMap.trace (ZMod p) U) (T • a - 1) = T ^ 2 - 2
  rw [map_sub (LinearMap.trace (ZMod p) U), map_smul (LinearMap.trace (ZMod p) U),
    LinearMap.trace_one, hU, smul_eq_mul, hT]
  change T * T - 2 = T ^ 2 - 2
  ring

private theorem coeff_trace_eq (hU : Module.finrank (ZMod p) U = 2)
    {c a : U →ₗ[ZMod p] U} {x y T : ZMod p}
    (hcxy : c = x • (1 : U →ₗ[ZMod p] U) + y • a)
    (hT : LinearMap.trace (ZMod p) U a = T) (htrace_c : LinearMap.trace (ZMod p) U c = T) :
    2 * x + y * T = T := by
  have htrace_eq : LinearMap.trace (ZMod p) U c = 2 * x + y * T := by
    rw [hcxy]
    simp only [map_add, map_smul, LinearMap.trace_one, hU, hT]
    ring
  rw [← htrace_eq, htrace_c]

private theorem coeff_eq_one_or_neg_one (hU : Module.finrank (ZMod p) U = 2)
    {c a : U →ₗ[ZMod p] U} {g : U ≃ₗ[ZMod p] U} {x y T : ZMod p}
    (hc_coe : c = (g : U →ₗ[ZMod p] U) * a * (g.symm : U →ₗ[ZMod p] U))
    (hcxy : c = x • (1 : U →ₗ[ZMod p] U) + y • a)
    (hT : LinearMap.trace (ZMod p) U a = T) (haCH : a * a = T • a - 1)
    (htrace_c : LinearMap.trace (ZMod p) U c = T) (hT2 : T ^ 2 ≠ 4) :
    y = 1 ∨ y = -1 := by
  have htτ : 2 * x + y * T = T := coeff_trace_eq hU hcxy hT htrace_c
  have htrace_c2 : LinearMap.trace (ZMod p) U (c * c) = T ^ 2 - 2 :=
    trace_sq_of_eq_conj hU T hc_coe hT haCH
  have hcc : c * c = (x ^ 2 - y ^ 2) • (1 : U →ₗ[ZMod p] U)
      + (2 * x * y + y ^ 2 * T) • a := by
    rw [hcxy, add_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, one_mul, mul_one]
    rw [haCH]
    module
  have htrace_c2' : LinearMap.trace (ZMod p) U (c * c)
      = 2 * x ^ 2 + 2 * x * y * T + y ^ 2 * (T ^ 2 - 2) := by
    rw [hcc]
    simp only [map_add, map_smul, LinearMap.trace_one, hU, hT]
    ring_nf
  have hkey : 2 * x ^ 2 + 2 * x * y * T + y ^ 2 * (T ^ 2 - 2) = T ^ 2 - 2 := by
    rw [← htrace_c2', htrace_c2]
  have hone : (1 - y) * (1 + y) = 0 := by
    have h1y : (1 - y ^ 2) * (T ^ 2 - 4) = 0 := by
      rw [final_identity x y T, sub_eq_zero.mpr hkey, sub_eq_zero.mpr htτ]
      ring
    rcases mul_eq_zero.mp h1y with h | h
    · rw [one_sub_mul_one_add y]; exact h
    · exact (hT2 (sub_eq_zero.mp h)).elim
  rcases mul_eq_zero.mp hone with h | h
  · exact Or.inl (sub_eq_zero.mp h).symm
  · exact Or.inr (eq_neg_of_add_eq_zero_left (by rwa [add_comm] at h))

private theorem eq_zero_of_two_mul_add_eq_self (h2ne : (2 : ZMod p) ≠ 0) {x T : ZMod p}
    (h : 2 * x + T = T) : x = 0 := by
  have h2x : 2 * x = 0 := by
    calc 2 * x = 2 * x + T - T := by abel
      _ = T - T := by rw [h]
      _ = 0 := by abel
  exact (mul_eq_zero.mp h2x).resolve_left h2ne

private theorem eq_of_two_mul_add_neg_eq (h2ne : (2 : ZMod p) ≠ 0) {x T : ZMod p}
    (h : 2 * x + (-1) * T = T) : x = T := by
  have h2 : 2 * x = 2 * T := by
    have h2' : 2 * T + (-1) * T = T := two_mul_add_neg_one_mul T
    exact add_right_cancel (by rw [h, h2'])
  exact mul_left_cancel₀ h2ne h2

omit [Module.Finite (ZMod p) U] in
private theorem coe_eq_symm_of_coeffs {a : U ≃ₗ[ZMod p] U} {c : U →ₗ[ZMod p] U} {x T : ZMod p}
    (hcxy : c = x • (1 : U →ₗ[ZMod p] U) + (-1 : ZMod p) • (a : U →ₗ[ZMod p] U))
    (hxT : x = T)
    (haCH : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)
      = T • (a : U →ₗ[ZMod p] U) - 1) :
    c = (a.symm : U →ₗ[ZMod p] U) := by
  have hc' : c = T • (1 : U →ₗ[ZMod p] U) - (a : U →ₗ[ZMod p] U) := by
    rw [hcxy, hxT]
    rw [show (-1 : ZMod p) • (a : U →ₗ[ZMod p] U) = -(a : U →ₗ[ZMod p] U)
        from neg_one_smul (ZMod p) (a : U →ₗ[ZMod p] U)]
    rw [sub_eq_add_neg]
  have hmul : (a : U →ₗ[ZMod p] U) * c = 1 := by
    rw [hc', mul_sub, mul_smul_comm, mul_one, haCH]
    abel
  have hsymm : ((a.symm : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = 1 := by
    ext w
    rw [Module.End.mul_apply]
    simp only [Module.End.one_apply]
    exact a.symm_apply_apply w
  calc c = 1 * c := by rw [one_mul]
    _ = (((a.symm : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)) * c := by
          rw [hsymm]
    _ = ((a.symm : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
          * ((a : U →ₗ[ZMod p] U) * c) := by rw [mul_assoc]
    _ = ((a.symm : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) * 1 := by rw [hmul]
    _ = ((a.symm : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by rw [mul_one]

omit [Module.Finite (ZMod p) U] in
private theorem conj_eq_of_coe_eq {a g : U ≃ₗ[ZMod p] U} {c : U →ₗ[ZMod p] U}
    (hc_coe : c = (g : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) * (g.symm : U →ₗ[ZMod p] U))
    (h : c = (a : U →ₗ[ZMod p] U)) : g * a * g⁻¹ = a := by
  refine LinearEquiv.ext fun w => ?_
  have h' := congrArg (fun f : U →ₗ[ZMod p] U => f w) h
  rw [hc_coe] at h'
  rw [Module.End.mul_apply, Module.End.mul_apply] at h'
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact h'

omit [Module.Finite (ZMod p) U] in
private theorem conj_eq_inv_of_coe_eq {a g : U ≃ₗ[ZMod p] U} {c : U →ₗ[ZMod p] U}
    (hc_coe : c = (g : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) * (g.symm : U →ₗ[ZMod p] U))
    (h : c = (a.symm : U →ₗ[ZMod p] U)) : g * a * g⁻¹ = a⁻¹ := by
  refine LinearEquiv.ext fun w => ?_
  have h' := congrArg (fun f : U →ₗ[ZMod p] U => f w) h
  rw [hc_coe] at h'
  rw [Module.End.mul_apply, Module.End.mul_apply] at h'
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact h'

private theorem exists_linearIndependent_pair_of_not_scalar
    {a : U →ₗ[ZMod p] U} (ha : ∀ k : ZMod p, a ≠ k • LinearMap.id) :
    ∃ v : U, LinearIndependent (ZMod p) ![v, a v] := by
  by_contra h
  push Not at h
  obtain ⟨k, hk⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
  exact ha k hk

theorem eq_or_eq_inv_of_commute_conj (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {a g : U ≃ₗ[ZMod p] U} (hdet : LinearEquiv.det a = 1)
    (h1 : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥)
    (h2 : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) = ⊥)
    (hc : Commute a (g * a * g⁻¹)) : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have haEnd := ne_smul_one_of_ker_and_det hp hU hdet h1 h2
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_not_scalar haEnd
  set c : U →ₗ[ZMod p] U := ((g * a * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) with hc_def
  have hc_comm : c * (a : U →ₗ[ZMod p] U) = (a : U →ₗ[ZMod p] U) * c := by
    ext w
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hc.eq
    simpa [hc_def, LinearEquiv.mul_apply] using h.symm
  obtain ⟨x, y, hcxy⟩ := CFSG.LocalAnalysis.eq_smul_one_add_smul_of_commute hU hv hc_comm
  have hc_coe : c = (g : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)
      * (g.symm : U →ₗ[ZMod p] U) := by
    rw [hc_def]; rfl
  have hdetL : LinearMap.det (a : U →ₗ[ZMod p] U) = 1 := by
    rw [← LinearEquiv.coe_det a, hdet]; rfl
  let T := LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U)
  have haCH : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)
      = T • (a : U →ₗ[ZMod p] U) - 1 := by
    have h := mul_self_eq_trace_smul_sub_det_smul_finrank_two hU (a : U →ₗ[ZMod p] U)
    rw [hdetL] at h
    simpa [T] using h
  have htrace_c : LinearMap.trace (ZMod p) U c = T := by rw [hc_coe, trace_conj]
  have hT2 : T ^ 2 ≠ 4 := trace_sq_ne_four_of_ker_eq_bot hp hU hdet h1 h2
  obtain hy := coeff_eq_one_or_neg_one hU hc_coe hcxy rfl haCH htrace_c hT2
  rcases hy with rfl | rfl
  · have hx0 : x = 0 := by
      have htτ : 2 * x + 1 * T = T := coeff_trace_eq hU hcxy rfl htrace_c
      exact eq_zero_of_two_mul_add_eq_self (x := x) (T := T) h2ne (by simpa using htτ)
    left
    exact conj_eq_of_coe_eq hc_coe (by rw [hcxy, hx0, zero_smul, zero_add, one_smul])
  · have hxT : x = T := by
      have htτ : 2 * x + (-1) * T = T := coeff_trace_eq hU hcxy rfl htrace_c
      exact eq_of_two_mul_add_neg_eq (x := x) (T := T) h2ne htτ
    right
    exact conj_eq_inv_of_coe_eq hc_coe (coe_eq_symm_of_coeffs hcxy hxT haCH)

private theorem commute_of_conj_of_odd_order {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2) (htv : QTwoLin.TransvectionFree J)
    (hker : ∀ y : ↥(J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)),
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) = ⊥)
    (hord : ∀ y : ↥(J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)),
      Odd (orderOf (y : U ≃ₗ[ZMod p] U)))
    {x g : ↥(J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ))}
    (hx : x ≠ 1) (hconj : Commute x (g * x * g⁻¹)) : Commute g x := by
  have hxdet : LinearEquiv.det (x : U ≃ₗ[ZMod p] U) = 1 := MonoidHom.mem_ker.mp x.2.2
  have hx1 : (x : U ≃ₗ[ZMod p] U) ≠ 1 := fun h1 => hx (Subtype.ext h1)
  have h1 : LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) = ⊥ :=
    ker_sub_one_eq_bot_of_det_eq_one hU htv x.2.1 hxdet hx1
  have hc : Commute (x : U ≃ₗ[ZMod p] U)
      ((g : U ≃ₗ[ZMod p] U) * (x : U ≃ₗ[ZMod p] U) * (g : U ≃ₗ[ZMod p] U)⁻¹) :=
    congrArg Subtype.val hconj.eq
  rcases eq_or_eq_inv_of_commute_conj hp hU hxdet h1 (hker x) hc with hh' | hh'
  · have hgx : (g : U ≃ₗ[ZMod p] U) * (x : U ≃ₗ[ZMod p] U)
        = (x : U ≃ₗ[ZMod p] U) * (g : U ≃ₗ[ZMod p] U) := by
      have h' := congrArg (fun e : U ≃ₗ[ZMod p] U => e * (g : U ≃ₗ[ZMod p] U)) hh'
      simpa [mul_assoc] using h'
    exact Subtype.ext hgx
  · exact Subtype.ext (commute_of_conj_eq_inv_of_odd_order (hord g) hh').eq

theorem commute_of_mem_ker_det_of_finrank_two (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (htv : QTwoLin.TransvectionFree J)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ J) {g h : U ≃ₗ[ZMod p] U}
    (hg : g ∈ J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ))
    (hh : h ∈ J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)) :
    Commute g h := by
  let K : Subgroup (U ≃ₗ[ZMod p] U) :=
    J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)
  have hodd : Odd (Nat.card ↥K) := odd_card_ker_det_of_finrank_two hp hU htv hneg
  have : Fintype U := by
    let b := Module.finBasisOfFinrankEq (ZMod p) U hU
    exact Fintype.ofEquiv (Fin 2 → ZMod p) b.equivFun.symm.toEquiv
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  have : Finite ↥K := Subtype.finite
  have hord : ∀ y : ↥K, Odd (orderOf (y : U ≃ₗ[ZMod p] U)) := by
    intro y
    have hdvd : orderOf (y : U ≃ₗ[ZMod p] U) ∣ Nat.card ↥K := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard y
    exact hodd.of_dvd_nat hdvd
  have hker : ∀ y : ↥K, LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) = ⊥ :=
    fun y => ker_add_one_eq_bot_of_odd_order hp (hord y)
  have htrans : ∀ x y z : ↥K, x ≠ 1 → Commute x y → Commute x z → Commute y z := by
    intro x y z hx hxy hxz
    have hxJ : (x : U ≃ₗ[ZMod p] U) ∈ J := x.2.1
    have hxdet : LinearEquiv.det (x : U ≃ₗ[ZMod p] U) = 1 := MonoidHom.mem_ker.mp x.2.2
    have hx1 : (x : U ≃ₗ[ZMod p] U) ≠ 1 := fun h1 => hx (Subtype.ext h1)
    have h1 : LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) = ⊥ :=
      ker_sub_one_eq_bot_of_det_eq_one hU htv hxJ hxdet hx1
    have ha := ne_smul_one_of_ker_and_det hp hU hxdet h1 (hker x)
    have hxy' : Commute (x : U ≃ₗ[ZMod p] U) (y : U ≃ₗ[ZMod p] U) :=
      congrArg Subtype.val hxy.eq
    have hxz' : Commute (x : U ≃ₗ[ZMod p] U) (z : U ≃ₗ[ZMod p] U) :=
      congrArg Subtype.val hxz.eq
    exact Subtype.ext (commute_of_commute_of_ne_smul hU ha hxy' hxz').eq
  have hsn : ∀ x g : ↥K, x ≠ 1 → Commute x (g * x * g⁻¹) → Commute g x :=
    fun x g hx hconj => commute_of_conj_of_odd_order hp hU htv hker hord hx hconj
  have hcomm := commute_of_odd_card_of_commute_trans hodd htrans hsn ⟨g, hg⟩ ⟨h, hh⟩
  exact congrArg Subtype.val hcomm.eq

private theorem eq_of_smul_one_add_smul_eq_lin {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Nontrivial V] {M : V →ₗ[k] V} (hM : ∀ c : k, M ≠ c • (1 : V →ₗ[k] V))
    {a b a' b' : k} (h : a • (1 : V →ₗ[k] V) + b • M = a' • 1 + b' • M) :
    a = a' ∧ b = b' := by
  have hb : b = b' := by
    by_contra hne
    have hsub : b - b' ≠ 0 := sub_ne_zero.2 hne
    apply hM ((a' - a) / (b - b'))
    have h' : (b - b') • M = (a' - a) • (1 : V →ₗ[k] V) := by
      linear_combination (norm := module) h
    calc M = ((b - b')⁻¹ * (b - b')) • M := by rw [inv_mul_cancel₀ hsub, one_smul]
      _ = (b - b')⁻¹ • ((b - b') • M) := by rw [mul_smul]
      _ = (b - b')⁻¹ • ((a' - a) • (1 : V →ₗ[k] V)) := by rw [h']
      _ = ((a' - a) / (b - b')) • (1 : V →ₗ[k] V) := by rw [smul_smul, div_eq_inv_mul]
  subst hb
  refine ⟨?_, rfl⟩
  have h1 : a • (1 : V →ₗ[k] V) = a' • (1 : V →ₗ[k] V) := add_right_cancel h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h2 := congrArg (fun f : V →ₗ[k] V => f v) h1
  simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
  have h3 : (a - a') • v = 0 := by rw [sub_smul, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv)

private theorem smul_one_add_smul_mul_lin {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {M : V →ₗ[k] V} {τ : k} (hsq : M * M = τ • M - 1) (a b a' b' : k) :
    (a • (1 : V →ₗ[k] V) + b • M) * (a' • 1 + b' • M) =
      (a * a' - b * b') • 1 + (a * b' + a' * b + b * b' * τ) • M := by
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    smul_smul, hsq, smul_sub]
  module

private theorem smul_one_add_smul_mul_conj {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {M : V →ₗ[k] V} {τ : k} (hsq : M * M = τ • M - 1) (α β : k) :
    (α • (1 : V →ₗ[k] V) + β • M) * ((α + β * τ) • 1 + (-β) • M)
      = (α ^ 2 + α * β * τ + β ^ 2) • (1 : V →ₗ[k] V) := by
  rw [smul_one_add_smul_mul_lin hsq]
  rw [show α * (α + β * τ) - β * (-β) = α ^ 2 + α * β * τ + β ^ 2 from by ring]
  rw [show α * (-β) + (α + β * τ) * β + β * (-β) * τ = 0 from by ring]
  simp

private theorem norm_eq_one_imp {k : Type*} [Field k] {τ μ α β : k}
    (hμ : μ ^ 2 - τ * μ + 1 = 0) (hx : α + β * μ = 1) (hn : α ^ 2 + α * β * τ + β ^ 2 = 1) :
    β * (τ - 2 * μ) = 0 := by
  have hα : α = 1 - β * μ := by linear_combination hx
  rw [hα] at hn
  linear_combination hn - β ^ 2 * hμ

private theorem sub_two_mul_ne_zero {k : Type*} [Field k] {τ μ : k}
    (hμ : μ ^ 2 - τ * μ + 1 = 0) (hτ : τ ^ 2 ≠ 4) : τ - 2 * μ ≠ 0 := by
  intro h0
  apply hτ
  linear_combination (τ - 2 * μ) * h0 - 4 * hμ

private theorem exists_extension_root' (τ : ZMod p) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra (ZMod p) K') (μ : K'),
      μ ^ 2 - algebraMap (ZMod p) K' τ * μ + 1 = 0 := by
  have hdeg : (Polynomial.C (1 : AlgebraicClosure (ZMod p)) * Polynomial.X ^ 2 +
      Polynomial.C (-(algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) τ)) * Polynomial.X +
        Polynomial.C 1).degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    norm_num
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, μ, ?_⟩
  simpa [Polynomial.IsRoot, sub_eq_add_neg] using hμ

private theorem trace_smul_one_add_smul_lin {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Module.Finite k V] (M : V →ₗ[k] V) (α β : k)
    (h : Module.finrank k V = 2) :
    LinearMap.trace k V (α • 1 + β • M) = 2 * α + β * LinearMap.trace k V M := by
  rw [map_add, map_smul, map_smul, LinearMap.trace_one, h, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

private theorem conj_eq_trace_sub {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (M : V →ₗ[k] V) (α β : k) (h : Module.finrank k V = 2) :
    (α + β * LinearMap.trace k V M) • (1 : V →ₗ[k] V) + (-β) • M
      = LinearMap.trace k V (α • 1 + β • M) • 1 - (α • 1 + β • M) := by
  rw [trace_smul_one_add_smul_lin M α β h]
  module

omit [Module.Finite (ZMod p) U] in
private theorem coord_exists (hU : Module.finrank (ZMod p) U = 2)
    {a : U ≃ₗ[ZMod p] U} {v : U}
    (hv : LinearIndependent (ZMod p) ![v, (a : U →ₗ[ZMod p] U) v])
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hcomm : ∀ x ∈ X, Commute x a) (x : ↥X) :
    ∃ α β : ZMod p, (x : U →ₗ[ZMod p] U) = α • 1 + β • (a : U →ₗ[ZMod p] U) := by
  have hcx : (x : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)
      = (a : U →ₗ[ZMod p] U) * (x : U →ₗ[ZMod p] U) := by
    ext w
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) (hcomm x x.2).eq
    simpa [LinearEquiv.mul_apply, Module.End.mul_apply] using h
  exact CFSG.LocalAnalysis.eq_smul_one_add_smul_of_commute hU hv hcx

omit [Module.Finite (ZMod p) U] in
private theorem coord_mul {a : U ≃ₗ[ZMod p] U} {τ : ZMod p}
    (hsq : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = τ • (a : U →ₗ[ZMod p] U) - 1)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {α β : ↥X → ZMod p}
    (hαβ : ∀ x : ↥X, (x : U →ₗ[ZMod p] U) = α x • 1 + β x • (a : U →ₗ[ZMod p] U))
    (huniq : ∀ (x : ↥X) (α' β' : ZMod p),
      (x : U →ₗ[ZMod p] U) = α' • 1 + β' • (a : U →ₗ[ZMod p] U) →
        α' = α x ∧ β' = β x) :
    ∀ x y : ↥X, α (x * y) = α x * α y - β x * β y ∧
      β (x * y) = α x * β y + α y * β x + β x * β y * τ := by
  intro x y
  have hxy : ((x * y : ↥X) : U →ₗ[ZMod p] U) =
      (α x * α y - β x * β y) • (1 : U →ₗ[ZMod p] U) +
        (α x * β y + α y * β x + β x * β y * τ) • (a : U →ₗ[ZMod p] U) := by
    change (x : U →ₗ[ZMod p] U) * (y : U →ₗ[ZMod p] U) =
      (α x * α y - β x * β y) • (1 : U →ₗ[ZMod p] U) +
        (α x * β y + α y * β x + β x * β y * τ) • (a : U →ₗ[ZMod p] U)
    rw [hαβ x, hαβ y, smul_one_add_smul_mul_lin hsq]
  have := huniq (x * y) _ _ hxy
  exact ⟨this.1.symm, this.2.symm⟩

omit [Module.Finite (ZMod p) U] in
private theorem coord_one {a : U ≃ₗ[ZMod p] U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {α β : ↥X → ZMod p}
    (huniq : ∀ (x : ↥X) (α' β' : ZMod p),
      (x : U →ₗ[ZMod p] U) = α' • 1 + β' • (a : U →ₗ[ZMod p] U) →
        α' = α x ∧ β' = β x) : α 1 = 1 ∧ β 1 = 0 := by
  have h1eq : ((1 : ↥X) : U →ₗ[ZMod p] U)
      = (1 : ZMod p) • (1 : U →ₗ[ZMod p] U) + (0 : ZMod p) • (a : U →ₗ[ZMod p] U) := by
    rw [one_smul, zero_smul, add_zero]
    rfl
  have h := huniq 1 1 0 h1eq
  exact ⟨h.1.symm, h.2.symm⟩

private theorem coord_norm_eq_one (hU : Module.finrank (ZMod p) U = 2) [Nontrivial U]
    {a : U ≃ₗ[ZMod p] U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hXdet : ∀ x ∈ X, LinearEquiv.det x = 1)
    {τ : ZMod p} (hτdef : τ = LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U))
    (hsq : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)
      = τ • (a : U →ₗ[ZMod p] U) - 1)
    {α β : ↥X → ZMod p}
    (hαβ : ∀ x : ↥X, (x : U →ₗ[ZMod p] U) = α x • 1 + β x • (a : U →ₗ[ZMod p] U))
    (x : ↥X) : (α x) ^ 2 + α x * β x * τ + (β x) ^ 2 = 1 := by
  have hdetx : LinearMap.det ((x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = 1 := by
    rw [← LinearEquiv.coe_det (x : U ≃ₗ[ZMod p] U), hXdet x x.2]; rfl
  have hCHx := mul_self_eq_trace_smul_sub_det_smul_finrank_two hU
    ((x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
  have hmain : ((x : U →ₗ[ZMod p] U))
      * ((α x + β x * τ) • (1 : U →ₗ[ZMod p] U)
          + (-(β x)) • (a : U →ₗ[ZMod p] U)) = 1 := by
    have hconj : (α x + β x * τ) • (1 : U →ₗ[ZMod p] U)
        + (-(β x)) • (a : U →ₗ[ZMod p] U)
        = LinearMap.trace (ZMod p) U ((x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) • 1
            - (x : U →ₗ[ZMod p] U) := by
      rw [hαβ x, hτdef]
      exact conj_eq_trace_sub (a : U →ₗ[ZMod p] U) (α x) (β x) hU
    rw [hconj, mul_sub, Algebra.mul_smul_comm, mul_one, hCHx, hdetx, one_smul]
    abel
  have hexp : ((x : U →ₗ[ZMod p] U))
      * ((α x + β x * τ) • (1 : U →ₗ[ZMod p] U)
          + (-(β x)) • (a : U →ₗ[ZMod p] U))
      = ((α x) ^ 2 + α x * β x * τ + (β x) ^ 2) • (1 : U →ₗ[ZMod p] U) := by
    rw [hαβ x]
    exact smul_one_add_smul_mul_conj hsq (α x) (β x)
  have hv1 : ((α x) ^ 2 + α x * β x * τ + (β x) ^ 2) • (1 : U →ₗ[ZMod p] U) = 1 := by
    rw [← hexp, hmain]
  obtain ⟨w, hw⟩ := exists_ne (0 : U)
  have h2 := congrArg (fun f : U →ₗ[ZMod p] U => f w) hv1
  simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
  have h3 : (((α x) ^ 2 + α x * β x * τ + (β x) ^ 2) - 1) • w = 0 := by
    rw [sub_smul, h2, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hw)

private theorem eq_one_of_embedding_eq_one (hU : Module.finrank (ZMod p) U = 2) [Nontrivial U]
    {a : U ≃ₗ[ZMod p] U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hXdet : ∀ x ∈ X, LinearEquiv.det x = 1)
    {τ : ZMod p} (hτdef : τ = LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U))
    (hsq : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U)
      = τ • (a : U →ₗ[ZMod p] U) - 1)
    {K' : Type} [Field K'] [Algebra (ZMod p) K'] {μ : K'}
    (hμ : μ ^ 2 - algebraMap (ZMod p) K' τ * μ + 1 = 0)
    (hτK : (algebraMap (ZMod p) K' τ) ^ 2 ≠ 4)
    {α β : ↥X → ZMod p}
    (hαβ : ∀ x : ↥X, (x : U →ₗ[ZMod p] U) = α x • 1 + β x • (a : U →ₗ[ZMod p] U))
    {x : ↥X} (hx' : algebraMap (ZMod p) K' (α x) + algebraMap (ZMod p) K' (β x) * μ = 1) :
    x = 1 := by
  have hnorm : (α x) ^ 2 + α x * β x * τ + (β x) ^ 2 = 1 :=
    coord_norm_eq_one hU hXdet hτdef hsq hαβ x
  have hne : algebraMap (ZMod p) K' τ - 2 * μ ≠ 0 := sub_two_mul_ne_zero hμ hτK
  have hbT : algebraMap (ZMod p) K' (β x) * (algebraMap (ZMod p) K' τ - 2 * μ) = 0 := by
    have hnK : (algebraMap (ZMod p) K' (α x)) ^ 2 + algebraMap (ZMod p) K' (α x)
        * algebraMap (ZMod p) K' (β x) * algebraMap (ZMod p) K' τ
        + (algebraMap (ZMod p) K' (β x)) ^ 2 = 1 := by
      have := congrArg (algebraMap (ZMod p) K') hnorm
      simpa only [map_add, map_mul, map_pow, map_one] using this
    exact norm_eq_one_imp hμ hx' hnK
  have hβ0 : β x = 0 := by
    have h1 : algebraMap (ZMod p) K' (β x) = 0 := (mul_eq_zero.1 hbT).resolve_right hne
    exact (map_eq_zero_iff _ (algebraMap (ZMod p) K').injective).1 h1
  have hα1 : α x = 1 := by
    apply (algebraMap (ZMod p) K').injective
    rw [map_one]
    simpa [hβ0] using hx'
  apply Subtype.ext
  exact LinearEquiv.ext fun w => by
    have hxmap : (x : U →ₗ[ZMod p] U) = 1 := by rw [hαβ x, hα1, hβ0]; simp
    have := congrArg (fun f : U →ₗ[ZMod p] U => f w) hxmap
    simpa [Module.End.one_apply] using this

private theorem exists_embedding_of_commute_lin (hU : Module.finrank (ZMod p) U = 2)
    {a : U ≃ₗ[ZMod p] U} (hns : ∀ c : ZMod p, (a : U →ₗ[ZMod p] U) ≠ c • 1)
    (hdet : LinearEquiv.det a = 1)
    (hτ : (LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U)) ^ 2 ≠ 4)
    (X : Subgroup (U ≃ₗ[ZMod p] U)) (hXdet : ∀ x ∈ X, LinearEquiv.det x = 1)
    (hcomm : ∀ x ∈ X, Commute x a) :
    ∃ (K' : Type) (_ : Field K') (ψ : ↥X →* K'), Function.Injective ψ := by
  classical
  have hdetL : LinearMap.det (a : U →ₗ[ZMod p] U) = 1 := by
    rw [← LinearEquiv.coe_det a, hdet]; rfl
  set τ : ZMod p := LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U) with hτdef
  have hsq : (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = τ • (a : U →ₗ[ZMod p] U) - 1 := by
    rw [mul_self_eq_trace_smul_sub_det_smul_finrank_two hU, hdetL, hτdef, one_smul]
  obtain ⟨v, hv⟩ : ∃ v : U, LinearIndependent (ZMod p) ![v, (a : U →ₗ[ZMod p] U) v] := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
    exact hns k hk
  have : Nontrivial U := ⟨v, 0, by simpa using hv.ne_zero 0⟩
  choose α β hαβ using fun x => coord_exists hU hv hcomm x
  have huniq : ∀ (x : ↥X) (α' β' : ZMod p),
      (x : U →ₗ[ZMod p] U) = α' • 1 + β' • (a : U →ₗ[ZMod p] U) →
        α' = α x ∧ β' = β x :=
    fun x α' β' h => eq_of_smul_one_add_smul_eq_lin hns (h.symm.trans (hαβ x))
  have hmulc := coord_mul hsq hαβ huniq
  obtain ⟨K', _, _, μ, hμ⟩ := exists_extension_root' τ
  let ψ₀ : ↥X → K' := fun x => algebraMap (ZMod p) K' (α x) + algebraMap (ZMod p) K' (β x) * μ
  have hone : α 1 = 1 ∧ β 1 = 0 := coord_one huniq
  have hψone : ψ₀ 1 = 1 := by simp [ψ₀, hone.1, hone.2]
  have hψmul : ∀ x y : ↥X, ψ₀ (x * y) = ψ₀ x * ψ₀ y := by
    intro x y
    obtain ⟨h1, h2⟩ := hmulc x y
    simp only [ψ₀, h1, h2, map_sub, map_mul, map_add]
    linear_combination (-(algebraMap (ZMod p) K' (β x) * algebraMap (ZMod p) K' (β y))) * hμ
  refine ⟨K', inferInstance, { toFun := ψ₀, map_one' := hψone, map_mul' := hψmul }, ?_⟩
  have hτK : (algebraMap (ZMod p) K' τ) ^ 2 ≠ 4 := by
    intro h0; apply hτ
    apply (algebraMap (ZMod p) K').injective
    simpa only [map_pow, map_ofNat] using h0
  rw [injective_iff_map_eq_one]
  intro x hx
  exact eq_one_of_embedding_eq_one hU hXdet hτdef hsq hμ hτK hαβ (by simpa [ψ₀] using hx)

theorem isCyclic_ker_det_of_finrank_two (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (htv : QTwoLin.TransvectionFree J)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ J) :
    IsCyclic ↥(J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)) := by
  let K : Subgroup (U ≃ₗ[ZMod p] U) :=
    J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)
  have : Fintype U := by
    let b := Module.finBasisOfFinrankEq (ZMod p) U hU
    exact Fintype.ofEquiv (Fin 2 → ZMod p) b.equivFun.symm.toEquiv
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  have : Finite ↥K := Subtype.finite
  have habel : ∀ x ∈ K, ∀ y ∈ K, Commute x y :=
    fun x hx y hy => commute_of_mem_ker_det_of_finrank_two hp hU htv hneg hx hy
  by_cases htriv : ∀ x : ↥K, x = 1
  · have : Subsingleton ↥K := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨1, Subsingleton.elim _ _⟩
  · push Not at htriv
    obtain ⟨a, ha1⟩ := htriv
    have haJ : (a : U ≃ₗ[ZMod p] U) ∈ J := a.property.1
    have hadet : LinearEquiv.det (a : U ≃ₗ[ZMod p] U) = 1 := MonoidHom.mem_ker.mp a.property.2
    have ha1' : (a : U ≃ₗ[ZMod p] U) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have h1 : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥ :=
      ker_sub_one_eq_bot_of_det_eq_one hU htv haJ hadet ha1'
    have h2 : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) = ⊥ := by
      have hodd := odd_card_ker_det_of_finrank_two hp hU htv hneg
      have hdvd : orderOf (a : U ≃ₗ[ZMod p] U) ∣ Nat.card ↥K := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard a
      exact ker_add_one_eq_bot_of_odd_order hp (hodd.of_dvd_nat hdvd)
    have hns : ∀ c : ZMod p, (a : U →ₗ[ZMod p] U) ≠ c • 1 :=
      ne_smul_one_of_ker_and_det hp hU hadet h1 h2
    have hτ2 : (LinearMap.trace (ZMod p) U (a : U →ₗ[ZMod p] U)) ^ 2 ≠ 4 :=
      trace_sq_ne_four_of_ker_eq_bot hp hU hadet h1 h2
    obtain ⟨K', _, ψ, hψ⟩ := exists_embedding_of_commute_lin hU hns hadet hτ2 K
      (fun x hx => MonoidHom.mem_ker.mp hx.2) (fun x hx => habel x hx a a.property)
    exact isCyclic_of_injective_ringHom ψ hψ

private theorem neg_one_sq_mul_one (k : Type*) [CommRing k] : (-1 : k) ^ 2 * 1 = 1 := by ring

private theorem sub_self_eq_neg_two_smul (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V]
    [Module k V] (w : V) : -w - w = (-2 : k) • w := by
  rw [sub_eq_add_neg, ← neg_add, ← two_smul k, ← neg_smul]

private theorem neg_inv_two_smul_neg_two (k : Type*) [Field k] (V : Type*) [AddCommGroup V]
    [Module k V] (h2 : (2 : k) ≠ 0) (w : V) : (-(2⁻¹ : k)) • ((-2 : k) • w) = w := by
  rw [smul_smul, neg_mul_neg, inv_mul_cancel₀ h2, one_smul]

omit [Module.Finite (ZMod p) U] in
private theorem range_sub_one_eq_ker_add_one_of_involution (hp : p ≠ 2)
    {t : U →ₗ[ZMod p] U} (ht2 : t * t = 1) :
    LinearMap.range (t - 1) = LinearMap.ker (t + 1) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.sub_apply, map_sub,
      Module.End.one_apply]
    rw [← Module.End.mul_apply, ht2, Module.End.one_apply]
    abel
  · intro w hw
    simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hw
    refine ⟨(-(2⁻¹ : ZMod p)) • w, ?_⟩
    have htw : t w = -w := eq_neg_of_add_eq_zero_left hw
    rw [map_smul, LinearMap.sub_apply, Module.End.one_apply, htw,
      sub_self_eq_neg_two_smul (ZMod p) U w]
    exact neg_inv_two_smul_neg_two (ZMod p) U (ZMod.prime_ne_zero p 2 hp) w

private theorem finrank_range_sub_one_of_involution (hU : Module.finrank (ZMod p) U = 2)
    {t : U →ₗ[ZMod p] U} (hne1 : t - 1 ≠ 0) (hne2 : t + 1 ≠ 0)
    (hrange : LinearMap.range (t - 1) = LinearMap.ker (t + 1)) :
    Module.finrank (ZMod p) (LinearMap.range (t - 1)) = 1 := by
  have h1 : 1 ≤ Module.finrank (ZMod p) (LinearMap.range (t - 1)) := by
    rw [Nat.one_le_iff_ne_zero]
    intro hbot
    exact hne1 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hbot))
  have h2 : Module.finrank (ZMod p) (LinearMap.range (t - 1)) ≤ 1 := by
    rw [hrange]
    have h := LinearMap.finrank_range_add_finrank_ker (t + 1)
    have htop : LinearMap.ker (t + 1) ≠ ⊤ := by
      intro h; exact hne2 (LinearMap.ker_eq_top.mp h)
    have hlt : Module.finrank (ZMod p) (LinearMap.ker (t + 1)) < 2 := by
      by_contra h
      exact htop (Submodule.eq_top_of_finrank_eq (by omega))
    omega
  omega

private theorem isRefl_of_sq_eq_one_of_det_eq_neg_one (hp : p ≠ 2)
    (hU : Module.finrank (ZMod p) U = 2) {t : U ≃ₗ[ZMod p] U} (ht2 : t * t = 1)
    (hdet : LinearEquiv.det t = -1) : IsRefl p t := by
  have hdetL : LinearMap.det (t : U →ₗ[ZMod p] U) = -1 := by
    rw [← LinearEquiv.coe_det t, hdet]; rfl
  have ht2L : (t : U →ₗ[ZMod p] U) * (t : U →ₗ[ZMod p] U) = 1 := by
    ext v
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) ht2
    simpa [LinearEquiv.mul_apply, Module.End.mul_apply] using h
  have hne1 : (t : U →ₗ[ZMod p] U) - 1 ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0, Module.End.one_eq_id, LinearMap.det_id] at hdetL
    have h2 : (2 : ZMod p) = 0 := by
      rw [← one_add_one_eq_two]
      exact eq_neg_iff_add_eq_zero.mp hdetL
    exact (ZMod.prime_ne_zero p 2 hp) h2
  have hne2 : (t : U →ₗ[ZMod p] U) + 1 ≠ 0 := by
    intro h0
    have ht : (t : U →ₗ[ZMod p] U) = -1 := eq_neg_of_add_eq_zero_left h0
    have hdet_neg : LinearMap.det (-1 : U →ₗ[ZMod p] U) = 1 := by
      rw [show (-1 : U →ₗ[ZMod p] U) = (-1 : ZMod p) • (1 : U →ₗ[ZMod p] U)
          from (neg_one_smul (ZMod p) (1 : U →ₗ[ZMod p] U)).symm,
        LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, hU]
      exact neg_one_sq_mul_one (ZMod p)
    rw [ht, hdet_neg] at hdetL
    have h2 : (2 : ZMod p) = 0 := by
      rw [← one_add_one_eq_two]
      exact eq_neg_iff_add_eq_zero.mp hdetL
    exact (ZMod.prime_ne_zero p 2 hp) h2
  have hrange := range_sub_one_eq_ker_add_one_of_involution hp ht2L
  refine ⟨ht2, ?_⟩
  simpa [Module.End.one_eq_id] using
    finrank_range_sub_one_of_involution hU hne1 hne2 hrange

omit [Module.Finite (ZMod p) U] in
private theorem closure_pair_eq_closure_mul {r a : U ≃ₗ[ZMod p] U} (hr : r * r = 1) :
    Subgroup.closure ({r, a} : Set (U ≃ₗ[ZMod p] U))
      = Subgroup.closure ({r, r * a} : Set (U ≃ₗ[ZMod p] U)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    refine Set.insert_subset_iff.mpr ⟨Subgroup.subset_closure (by simp), ?_⟩
    refine Set.singleton_subset_iff.mpr ?_
    have h : r * (r * a) ∈ Subgroup.closure ({r, r * a} : Set (U ≃ₗ[ZMod p] U)) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    rwa [← mul_assoc, hr, one_mul] at h
  · rw [Subgroup.closure_le]
    refine Set.insert_subset_iff.mpr ⟨Subgroup.subset_closure (by simp), ?_⟩
    refine Set.singleton_subset_iff.mpr ?_
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private theorem isRefl_mul_of_conj_eq_inv (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {r a : U ≃ₗ[ZMod p] U} (hrr : IsRefl p r) (hdet : LinearEquiv.det a = 1)
    (h : r * a * r = a⁻¹) : IsRefl p (r * a) := by
  have hra2 : (r * a) * (r * a) = 1 := by
    have h1 : (r * a) * (r * a) = (r * a * r) * a := by simp only [mul_assoc]
    rw [h1, h, inv_mul_cancel]
  have hdet_ra : LinearEquiv.det (r * a) = -1 := by
    rw [map_mul, det_eq_neg_one_of_isRefl hp hrr, hdet, mul_one]
  exact isRefl_of_sq_eq_one_of_det_eq_neg_one hp hU hra2 hdet_ra

private theorem not_mem_ker_det_of_refl (hp : p ≠ 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U} (hrr : IsRefl p r) :
    r ∉ J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ) := by
  intro hr
  have hdetr : LinearEquiv.det r = 1 := MonoidHom.mem_ker.mp hr.2
  have hneg1 : LinearEquiv.det r = -1 := det_eq_neg_one_of_isRefl hp hrr
  rw [hneg1] at hdetr
  have h3 : (-1 : ZMod p) = 1 := by
    have h4 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hdetr
    rwa [Units.val_neg, Units.val_one] at h4
  have h2 : (2 : ZMod p) = 0 := by
    rw [← one_add_one_eq_two]
    exact eq_neg_iff_add_eq_zero.mp h3.symm
  exact (ZMod.prime_ne_zero p 2 hp) h2

omit [Module.Finite (ZMod p) U] in
private theorem mem_zpowers_of_mem_ker_det {K : Subgroup (U ≃ₗ[ZMod p] U)} {a : ↥K}
    (ha : Subgroup.zpowers a = ⊤) {t : U ≃ₗ[ZMod p] U} (ht : t ∈ K) :
    t ∈ Subgroup.zpowers (a : U ≃ₗ[ZMod p] U) := by
  have h1' : (⟨t, ht⟩ : ↥K) ∈ Subgroup.zpowers a := by rw [ha]; trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1'
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
    simpa using congrArg (fun x : ↥K => (x : U ≃ₗ[ZMod p] U)) hn⟩

private theorem J_eq_closure_of_generators (hp : p ≠ 2)
    {J K : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p J)
    (hKdef : K = J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ))
    {r : U ≃ₗ[ZMod p] U} (hrJ : r ∈ J) (hrr : IsRefl p r)
    {a : U ≃ₗ[ZMod p] U} (hKle : K ≤ Subgroup.zpowers a) (haJ : a ∈ J) :
    J = Subgroup.closure ({r, a} : Set _) := by
  apply le_antisymm
  · intro g hg
    rw [hgen] at hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      by_cases htK : t ∈ K
      · have h1 : t ∈ Subgroup.zpowers a := hKle htK
        rw [Subgroup.zpowers_eq_closure] at h1
        exact Subgroup.closure_mono (by intro x hx; exact Set.mem_insert_of_mem r hx) h1
      · have hts_K : r⁻¹ * t ∈ K := by
          rw [hKdef]
          refine ⟨J.mul_mem (J.inv_mem hrJ) ht.1, ?_⟩
          change LinearEquiv.det (r⁻¹ * t) = 1
          rw [map_mul, map_inv, det_eq_neg_one_of_isRefl hp hrr,
            det_eq_neg_one_of_isRefl hp ht.2]
          simp
        have hts_cl : r⁻¹ * t ∈ Subgroup.closure ({r, a} : Set _) := by
          have h1 : r⁻¹ * t ∈ Subgroup.zpowers a := hKle hts_K
          rw [Subgroup.zpowers_eq_closure] at h1
          exact Subgroup.closure_mono (by intro x hx; exact Set.mem_insert_of_mem r hx) h1
        have hst : t = r * (r⁻¹ * t) := by group
        rw [hst]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hts_cl
    | one => exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx => exact Subgroup.inv_mem _ ihx
  · rw [Subgroup.closure_le]
    intro t ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hrJ
    · exact haJ

private theorem false_of_conj_eq_self (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} {r a : U ≃ₗ[ZMod p] U} (hrr : IsRefl p r) (hr1 : r⁻¹ = r)
    (hJ : J = Subgroup.closure ({r, a} : Set _))
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h : r * a * r⁻¹ = a) : False := by
  have hra_comm : Commute r a := by
    have h1' := congrArg (fun e : U ≃ₗ[ZMod p] U => e * r) h
    rw [mul_assoc, hr1, hrr.1, mul_one] at h1'
    exact h1'
  have hcomm_r : ∀ g ∈ Subgroup.closure ({r, a} : Set _), Commute g r := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with h | h
      · rw [h]
      · rw [h]; exact hra_comm.symm
    | one => exact Commute.one_left _
    | mul x y hx hy ihx ihy => exact ihx.mul_left ihy
    | inv x hx ihx => exact ihx.inv_left
  have hfix : ∀ g ∈ J, ∀ w ∈ LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1),
      g w ∈ LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1) := by
    intro g hg w hw
    rw [hJ] at hg
    have hgr := hcomm_r g hg
    have h1' := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hgr.eq
    simp only [LinearEquiv.mul_apply] at h1'
    have hw' : r w = w := by
      have hw2 := hw
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hw2
      exact sub_eq_zero.mp hw2
    rw [hw'] at h1'
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    exact sub_eq_zero.mpr h1'.symm
  have hdim : Module.finrank (ZMod p) (LinearMap.ker ((r : U →ₗ[ZMod p] U) - 1)) = 1 := by
    have h2' := LinearMap.finrank_range_add_finrank_ker ((r : U →ₗ[ZMod p] U) - 1)
    have hrk : Module.finrank (ZMod p)
        (LinearMap.range ((r : U →ₗ[ZMod p] U) - 1)) = 1 := by
      simpa [Module.End.one_eq_id] using hrr.2
    omega
  rcases hirr _ hfix with hbot | htop
  · rw [hbot, finrank_bot] at hdim; omega
  · rw [htop, finrank_top, hU] at hdim; omega

omit [Module.Finite (ZMod p) U] in
private theorem negOrGen_witness_of_eq_one {J : Subgroup (U ≃ₗ[ZMod p] U)}
    {r a : U ≃ₗ[ZMod p] U} (hrJ : r ∈ J) (hrr : IsRefl p r)
    (hJ : J = Subgroup.closure ({r, a} : Set _)) (ha1 : a = 1) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ 2 ∧
      (∀ x ∈ s, x ∈ J ∧ IsRefl p x) ∧ J = Subgroup.closure (s : Set _) := by
  classical
  refine ⟨{r}, ?_, ?_, ?_⟩
  · simp
  · intro x hx
    rw [Finset.mem_singleton] at hx; subst hx; exact ⟨hrJ, hrr⟩
  · rw [hJ, ha1]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro t ht
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
    · apply Subgroup.closure_mono
      intro t ht
      obtain rfl : t = r := by simpa using ht
      simp

private theorem negOrGen_witness_of_ne_one (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (htv : QTwoLin.TransvectionFree J)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ J)
    {r a : U ≃ₗ[ZMod p] U} (hrJ : r ∈ J) (hrr : IsRefl p r) (hr1 : r⁻¹ = r)
    (haJ : a ∈ J) (hadet : LinearEquiv.det a = 1) (ha1 : a ≠ 1)
    (hJ : J = Subgroup.closure ({r, a} : Set _))
    (hconj_comm : Commute a (r * a * r⁻¹))
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ 2 ∧
      (∀ x ∈ s, x ∈ J ∧ IsRefl p x) ∧ J = Subgroup.closure (s : Set _) := by
  have h1 : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = ⊥ :=
    ker_sub_one_eq_bot_of_det_eq_one hU htv haJ hadet ha1
  have h2 : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) = ⊥ := by
    have hodd := odd_card_ker_det_of_finrank_two hp hU htv hneg
    have hdvd : orderOf a ∣ Nat.card ↥(J ⊓ MonoidHom.ker
        (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)) :=
      Subgroup.orderOf_dvd_natCard _ ⟨haJ, MonoidHom.mem_ker.mpr hadet⟩
    exact ker_add_one_eq_bot_of_odd_order hp (hodd.of_dvd_nat hdvd)
  rcases eq_or_eq_inv_of_commute_conj hp hU hadet h1 h2 hconj_comm with h | h
  · exact (false_of_conj_eq_self hU hrr hr1 hJ hirr h).elim
  · have hrar : r * a * r = a⁻¹ := by rwa [hr1] at h
    have hra_refl : IsRefl p (r * a) := isRefl_mul_of_conj_eq_inv hp hU hrr hadet hrar
    have hraJ : r * a ∈ J := J.mul_mem hrJ haJ
    have hJra : J = Subgroup.closure ({r, r * a} : Set _) :=
      hJ.trans (closure_pair_eq_closure_mul hrr.1)
    classical
    refine ⟨({r, r * a} : Finset (U ≃ₗ[ZMod p] U)), ?_, ?_, ?_⟩
    · calc ({r, r * a} : Finset (U ≃ₗ[ZMod p] U)).card
          ≤ ({r * a} : Finset (U ≃ₗ[ZMod p] U)).card + 1 := Finset.card_insert_le _ _
        _ = 1 + 1 := by rw [Finset.card_singleton]
        _ ≤ 2 := by norm_num
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hrJ, hrr⟩
      · exact ⟨hraJ, hra_refl⟩
    · simpa using hJra

theorem negOrGen_of_finrank_two (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 2)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p J) (htv : QTwoLin.TransvectionFree J)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    NegOrGen p 2 J := by
  by_cases hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J
  · exact Or.inl hneg
  · right
    let K : Subgroup (U ≃ₗ[ZMod p] U) :=
      J ⊓ MonoidHom.ker (LinearEquiv.det : (U ≃ₗ[ZMod p] U) →* (ZMod p)ˣ)
    have hKabel : ∀ x ∈ K, ∀ y ∈ K, Commute x y :=
      fun x hx y hy => commute_of_mem_ker_det_of_finrank_two hp hU htv hneg hx hy
    obtain ⟨r, hrJ, r', hr'J, hrr, hr'r, hrne⟩ := exists_two_isRefl_of_reflGen hp hU hgen hirr
    have hrK : r ∉ K := not_mem_ker_det_of_refl hp hrr
    obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (isCyclic_ker_det_of_finrank_two hp hU htv hneg)
    have hr1 : r⁻¹ = r := (eq_inv_of_mul_eq_one_right hrr.1).symm
    have hKle : K ≤ Subgroup.zpowers (a : U ≃ₗ[ZMod p] U) :=
      fun _ ht => mem_zpowers_of_mem_ker_det ha ht
    have hJ : J = Subgroup.closure ({(r : U ≃ₗ[ZMod p] U), (a : U ≃ₗ[ZMod p] U)} : Set _) :=
      J_eq_closure_of_generators hp hgen rfl hrJ hrr hKle a.property.1
    have hconjK : r * (a : U ≃ₗ[ZMod p] U) * r⁻¹ ∈ K := by
      refine ⟨J.mul_mem (J.mul_mem hrJ a.property.1) (J.inv_mem hrJ), ?_⟩
      change LinearEquiv.det (r * (a : U ≃ₗ[ZMod p] U) * r⁻¹) = 1
      rw [map_mul, map_mul, map_inv, det_eq_neg_one_of_isRefl hp hrr,
        MonoidHom.mem_ker.mp a.property.2]
      simp
    have hconj_comm : Commute (a : U ≃ₗ[ZMod p] U) (r * (a : U ≃ₗ[ZMod p] U) * r⁻¹) :=
      hKabel a a.property _ hconjK
    by_cases ha1 : (a : U ≃ₗ[ZMod p] U) = 1
    · exact negOrGen_witness_of_eq_one hrJ hrr hJ ha1
    · exact negOrGen_witness_of_ne_one hp hU htv hneg hrJ hrr hr1 a.property.1
        (MonoidHom.mem_ker.mp a.property.2) ha1 hJ hconj_comm hirr

end RankTwo

theorem tableFactsAt_two (hp : p ≠ 2) : TableFactsAt p 2 := by
  refine tableFactsAt_of_forall fun U _ _ _ J hdim hhyp => ?_
  exact ⟨negOrGen_of_finrank_two hp hdim hhyp.reflGen hhyp.transvectionFree hhyp.irreducible,
    coprimeWitness_of_finrank_two hp hdim hhyp.reflGen hhyp.transvectionFree hhyp.irreducible,
    by simpa using throughRefl_one hp J⟩

end CFSG.StandardType.ZS
