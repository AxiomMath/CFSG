module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2PLeM

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

private theorem conjSubgroup_sup' (A B : Subgroup G) (x : G) :
    conjSubgroup (A ⊔ B) x = conjSubgroup A x ⊔ conjSubgroup B x :=
  Subgroup.map_sup A B _

private theorem le_normalizer_inf_centralizer_conjClosure {Z A : Subgroup G} :
    A ≤ normalizer ((A ⊓ centralizer (conjClosure Z A : Set G) : Subgroup G) : Set G) := by
  intro a ha
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
  have hA : conjSubgroup A a = A :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (H := A) ha)
  have hZ : conjSubgroup (conjClosure Z A) a = conjClosure Z A :=
    conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure Z A ha)
  rw [hA, hZ]

theorem le_conjSubgroup_of_relIndex_two_pow (h1 : W16One G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {X : Subgroup G}
    (hCX : H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) ≤ X) (hXH : X ≤ H)
    (hXn : (X.subgroupOf H).Normal)
    (hX2 : ∃ k : ℕ, (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).relIndex X = 2 ^ k)
    {h : G} (hh : h ∈ H) : X ≤ conjSubgroup M h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hCHM : H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) ≤ M := by
    intro x hx
    have hx' := c.cex.centralizer_conjClosure_le_conj hx.2 (Subgroup.one_mem H)
    rwa [conjSubgroup_one] at hx'
  obtain ⟨P, hP, hRP⟩ := exists_isSylowIn_ge 2 c.mem.1 c.sylow.isPGroup
  have hPM : P ≤ M := le_M_of_isSylowIn h1 h15 hS c hP hRP
  have hXM : X ≤ M := by
    obtain ⟨k, hk⟩ := hX2
    let C : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)
    let J : Subgroup G := (X ⊓ P) ⊔ C
    have hA2 : IsSylowIn 2 (X ⊓ P) X := by
      rw [inf_comm]
      exact hP.inf_normal hXH hXn
    have hJdvdA : J.relIndex X ∣ (X ⊓ P).relIndex X :=
      Subgroup.relIndex_dvd_of_le_left X le_sup_left
    have hJdvdC : J.relIndex X ∣ C.relIndex X :=
      Subgroup.relIndex_dvd_of_le_left X le_sup_right
    have hAodd : ¬ 2 ∣ (X ⊓ P).relIndex X := hA2.not_dvd_relIndex
    have hJodd : ¬ 2 ∣ J.relIndex X := fun hd => hAodd (hd.trans hJdvdA)
    have hJdvd : J.relIndex X ∣ 2 ^ k := hk ▸ hJdvdC
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hJdvd
    have hj0 : j = 0 := by
      by_contra hjne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjne
      rw [pow_succ] at hj
      exact hJodd ⟨2 ^ m, by rw [hj, mul_comm]⟩
    rw [hj0] at hj
    have hJ1 : J.relIndex X = 1 := by simpa using hj
    have hXJ : X ≤ J := Subgroup.relIndex_eq_one.1 hJ1
    exact hXJ.trans (sup_le (inf_le_right.trans hPM) hCHM)
  intro x hx
  rw [mem_conjSubgroup_iff]
  have hxH : x ∈ H := hXH hx
  have hconjX : h * x * h⁻¹ ∈ X := by
    have h1' : (⟨h, hh⟩ : H) * (⟨x, hxH⟩ : H) * (⟨h, hh⟩ : H)⁻¹ ∈ X.subgroupOf H :=
      hXn.conj_mem (⟨x, hxH⟩ : H) hx (⟨h, hh⟩ : H)
    rw [Subgroup.mem_subgroupOf] at h1'
    exact h1'
  exact hXM hconjX

theorem inf_eq_sup_of_relIndex_two_pow (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {X : Subgroup G}
    (hCX : H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) ≤ X) (hXH : X ≤ H)
    (hXn : (X.subgroupOf H).Normal)
    (hX2 : ∃ k : ℕ, (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).relIndex X = 2 ^ k) :
    V ⊓ X = U ⊔ V₀ := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hUV : U ≤ V := c.cex.le
  have hV₀V : V₀ ≤ V := c.cex.hyp.h6.le
  have hUV₀H : U ⊔ V₀ ≤ H := sup_le (hUV.trans hVH) (hV₀V.trans hVH)
  have hIH : conjClosure (U ⊔ V₀) H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hUV₀H hz)) (H.inv_mem hh)
  refine le_antisymm ?_ ?_
  · calc V ⊓ X ≤ V ⊓ conjSubgroup M g :=
        inf_le_inf_left V
          (le_conjSubgroup_of_relIndex_two_pow h1 h15 hS c hCX hXH hXn hX2 c.g_mem.1)
      _ = U ⊔ V₀ := c.cex.inf_conjSubgroup_eq h1 h5 h15 hS c.g_mem.2 c.g_not
  · refine le_inf (sup_le hUV hV₀V) ?_
    have hIleC : conjClosure (U ⊔ V₀) H ≤
        H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
      le_inf hIH fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hy hx
    exact (le_conjClosure (U ⊔ V₀) H).trans (hIleC.trans hCX)

theorem inf_centralizer_eq_sup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) :
    V ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) = U ⊔ V₀ := by
  have hXn : ((H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact le_normalizer_inf_centralizer_conjClosure (Z := U ⊔ V₀) (A := H)
  exact inf_eq_sup_of_relIndex_two_pow h1 h5 h15 hS c le_rfl inf_le_left hXn
    ⟨0, by rw [Subgroup.relIndex_self, pow_zero]⟩

theorem not_le_centralizer_conjClosure (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) :
    ¬ V ≤ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
  intro hle
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hinf := inf_centralizer_eq_sup h1 h5 h15 hS c
  have hVle : V ≤ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := le_inf hVH hle
  rw [inf_eq_left.2 hVle] at hinf
  have h0 : E3.mQuot V (U ⊔ V₀) = 0 := by rw [← hinf, E3.mQuot_self]
  have h1le := one_le_mQuot c
  omega

theorem conjSubgroup_le_sup_iff (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {y : G} (hy : y ∈ H) :
    conjSubgroup V y ≤ V ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) ↔ y ∈ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  let C : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)
  have hHnormC : H ≤ normalizer (C : Set G) :=
    le_normalizer_inf_centralizer_conjClosure (Z := U ⊔ V₀) (A := H)
  have hVnormC : V ≤ normalizer (C : Set G) := hVH.trans hHnormC
  change conjSubgroup V y ≤ V ⊔ C ↔ y ∈ M
  constructor
  · intro hle
    by_contra hyM
    have hIV_le : ⁅conjClosure (U ⊔ V₀) H, V⁆ ≤ V₀ := by
      calc ⁅conjClosure (U ⊔ V₀) H, V⁆ ≤ ⁅R, V⁆ :=
            Subgroup.commutator_mono (conjClosure_le_R h1 hS c) le_rfl
        _ = ⁅V, R⁆ := Subgroup.commutator_comm R V
        _ ≤ V₀ := comm_V_R_le c
    have hcomm_sup : ⁅conjClosure (U ⊔ V₀) H, V ⊔ C⁆ ≤ ⁅conjClosure (U ⊔ V₀) H, V⁆ := by
      rw [Subgroup.commutator_le]
      intro i hi x hx
      have hx' : x ∈ (V : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right V C hVnormC]
        exact hx
      rw [Set.mem_mul] at hx'
      obtain ⟨v, hv, cc, hcc, rfl⟩ := hx'
      have hcc' : cc ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := hcc
      have hccC : cc ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) := hcc'.2
      have hccomm : ⁅i, cc⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hccC i hi)
      simpa [commutatorElement_mul_right_eq_mul_conj, hccomm] using
        Subgroup.commutator_mem_commutator hi hv
    have hIy : conjSubgroup (conjClosure (U ⊔ V₀) H) y = conjClosure (U ⊔ V₀) H :=
      conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure (U ⊔ V₀) H hy)
    have hcommVy_eq : ⁅conjClosure (U ⊔ V₀) H, conjSubgroup V y⁆ =
        conjSubgroup ⁅conjClosure (U ⊔ V₀) H, V⁆ y := by
      have h' := (E3.conjSubgroup_commutator (conjClosure (U ⊔ V₀) H) V y).symm
      rwa [hIy] at h'
    have hcommVy_le : ⁅conjClosure (U ⊔ V₀) H, conjSubgroup V y⁆ ≤
        ⁅conjClosure (U ⊔ V₀) H, V⁆ :=
      (Subgroup.commutator_mono le_rfl hle).trans hcomm_sup
    have hcommVy_le_V₀y : ⁅conjClosure (U ⊔ V₀) H, conjSubgroup V y⁆ ≤ conjSubgroup V₀ y := by
      rw [hcommVy_eq]
      exact E3.conjSubgroup_mono_left y hIV_le
    have hIV_ne : ⁅conjClosure (U ⊔ V₀) H, V⁆ ≠ ⊥ := by
      intro hbot
      refine not_le_centralizer_conjClosure h1 h5 h15 hS c ?_
      have h2 : ⁅V, conjClosure (U ⊔ V₀) H⁆ = ⊥ := by
        rwa [Subgroup.commutator_comm] at hbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    have hne : ⁅conjClosure (U ⊔ V₀) H, conjSubgroup V y⁆ ≠ ⊥ := by
      rw [hcommVy_eq]
      intro hbot
      refine hIV_ne ?_
      have h2 := congrArg (fun A : Subgroup G => conjSubgroup A y⁻¹) hbot
      rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
        E3.conjSubgroup_bot] at h2
    have hlebot : ⁅conjClosure (U ⊔ V₀) H, conjSubgroup V y⁆ ≤ (⊥ : Subgroup G) := by
      rw [← c.cex.hyp.conj_inf_eq_bot hyM]
      exact le_inf hcommVy_le_V₀y (hcommVy_le.trans hIV_le)
    exact hne (le_bot_iff.mp hlebot)
  · intro hyM
    have hyN : y ∈ normalizer (V : Set G) := by
      rw [c.cex.hyp.h6.normalizer_eq]
      exact hyM
    have hconj : conjSubgroup V y = V := conjSubgroup_eq_iff_mem_normalizer.2 hyN
    rw [hconj]
    exact le_sup_left

theorem mem_sup_of_normalizes_conj (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {g' : G}
    (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) {v : G} (hv : v ∈ V)
    (hn : ∀ w ∈ conjSubgroup V g', v * w * v⁻¹ ∈
      conjSubgroup V g' ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) :
    v ∈ U ⊔ V₀ := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  let C : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)
  have hHnormC : H ≤ normalizer (C : Set G) :=
    le_normalizer_inf_centralizer_conjClosure (Z := U ⊔ V₀) (A := H)
  have hg'H : g' ∈ H := hg'.1
  have hconj : conjSubgroup (conjSubgroup V g') v⁻¹ ≤ conjSubgroup V g' ⊔ C := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [inv_inv] at hx
    have h := hn (v⁻¹ * x * v) hx
    have e : v * (v⁻¹ * x * v) * v⁻¹ = x := by group
    rwa [e] at h
  have hconj2 : conjSubgroup (conjSubgroup (conjSubgroup V g') v⁻¹) g'⁻¹ ≤
      conjSubgroup (conjSubgroup V g' ⊔ C) g'⁻¹ :=
    E3.conjSubgroup_mono_left g'⁻¹ hconj
  have hLHS : conjSubgroup (conjSubgroup (conjSubgroup V g') v⁻¹) g'⁻¹ =
      conjSubgroup V (g' * v⁻¹ * g'⁻¹) := by
    simp only [conjSubgroup_conjSubgroup]
  have hRHS : conjSubgroup (conjSubgroup V g' ⊔ C) g'⁻¹ = V ⊔ C := by
    rw [conjSubgroup_sup', conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hCg : conjSubgroup C g'⁻¹ = C :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hHnormC (H.inv_mem hg'H))
    rw [hCg]
  have hconjV : conjSubgroup V (g' * v⁻¹ * g'⁻¹) ≤ V ⊔ C := by
    have h := hconj2
    rw [hLHS, hRHS] at h
    exact h
  have hHmem : g' * v⁻¹ * g'⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hg'H (H.inv_mem (hVH hv))) (H.inv_mem hg'H)
  have hmemM : g' * v⁻¹ * g'⁻¹ ∈ M :=
    (conjSubgroup_le_sup_iff h1 h5 h15 hS c (y := g' * v⁻¹ * g'⁻¹) hHmem).1 hconjV
  have hmemM' : g' * v * g'⁻¹ ∈ M := by
    have h := M.inv_mem hmemM
    convert h using 1
    group
  have hvconj : v ∈ conjSubgroup M g' := mem_conjSubgroup_iff.2 hmemM'
  rw [← c.cex.inf_conjSubgroup_eq h1 h5 h15 hS hg'.2 hg'M]
  exact ⟨hv, hvconj⟩

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
