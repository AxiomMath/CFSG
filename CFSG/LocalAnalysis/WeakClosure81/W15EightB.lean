module

public import CFSG.LocalAnalysis.WeakClosure81.W15EightA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_pCoreOf_iff {H : Subgroup G} {g : G} (hg : g ∈ H) (y : G) :
    g * y * g⁻¹ ∈ pCoreOf 2 H ↔ y ∈ pCoreOf 2 H :=
  (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) y).symm

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem pCoreOf_le_S (h : Cex15 M V₀ V U S) : pCoreOf 2 (centralizer (U : Set G)) ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine h.isSylowIn_centralizer.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem pCoreOf_le_conj (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    pCoreOf 2 (centralizer (U : Set G)) ≤ conjSubgroup M g := by
  intro y hy
  rw [mem_conjSubgroup_iff]
  exact h.S_le_M (h.pCoreOf_le_S ((conj_mem_pCoreOf_iff hg y).2 hy))

theorem inf_centralizer_le_pCoreOf (hS : Std15 G) (h : Cex15 M V₀ V U S) :
    V₀ ⊓ centralizer (S : Set G) ≤ pCoreOf 2 (centralizer (U : Set G)) := by
  intro x hx
  obtain ⟨hxV₀, hxS⟩ := Subgroup.mem_inf.1 hx
  have hxC : x ∈ centralizer (pCoreOf 2 (centralizer (U : Set G)) : Set G) :=
    Subgroup.centralizer_le (fun y hy => h.pCoreOf_le_S hy) hxS
  exact h.charTwo_centralizer hS (Subgroup.mem_inf.2 ⟨h.V₀_le_centralizer hxV₀, hxC⟩)

theorem inf_conj_ne_bot (hS : Std15 G) (h : Cex15 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G)) :
    V₀ ⊓ conjSubgroup M g ≠ ⊥ ∧ conjSubgroup V₀ g ⊓ M ≠ ⊥ := by
  have hne : V₀ ⊓ centralizer (S : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot h.hyp.elemAbelian₀ h.hyp.ne_bot (h.isCalH hS) h.isSylowIn_inf
  obtain ⟨⟨w, hwmem⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hwV₀ : w ∈ V₀ := (Subgroup.mem_inf.1 hwmem).1
  have hwO : w ∈ pCoreOf 2 (centralizer (U : Set G)) := h.inf_centralizer_le_pCoreOf hS hwmem
  refine ⟨fun hbot => hw1' ?_, fun hbot => hw1' ?_⟩
  · have hmem : w ∈ V₀ ⊓ conjSubgroup M g :=
      Subgroup.mem_inf.2 ⟨hwV₀, h.pCoreOf_le_conj hg hwO⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  · have hx : g⁻¹ * w * g ∈ conjSubgroup V₀ g ⊓ M := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_conjSubgroup_iff, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
        exact hwV₀
      · have h1 := (conj_mem_pCoreOf_iff ((centralizer (U : Set G)).inv_mem hg) w).2 hwO
        rw [inv_inv] at h1
        exact h.S_le_M (h.pCoreOf_le_S h1)
    rw [hbot, Subgroup.mem_bot] at hx
    have hwe : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [hwe, hx]
    group

theorem oneFirst_conj (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    OneFirst M V₀ V g := by
  obtain ⟨hU1, -⟩ := h.U_le_inf_conj hg
  intro x hx
  obtain ⟨⟨-, hxM⟩, hxC⟩ := hx
  exact h.centralizer_le_cTilde (Subgroup.mem_inf.2 ⟨hxM,
    Subgroup.centralizer_le (fun y hy => hU1 hy) hxC⟩)

theorem oneDual_conj (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    OneDual M V₀ V g := by
  obtain ⟨-, hU2⟩ := h.U_le_inf_conj hg
  intro x hx
  obtain ⟨⟨-, hxMg⟩, hxC⟩ := hx
  have hxU : ∀ u ∈ U, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le (fun y hy => hU2 hy) hxC) u hu).symm
  have hxN : x ∈ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← E3.conjSubgroup_normalizer, h.hyp.normalizer₀]
    exact hxMg
  refine FourteenTwo.mem_cTilde_iff_comm.2 ⟨hxMg, hxN, fun v hv => ?_⟩
  rw [mem_conjSubgroup_iff] at hv
  obtain ⟨w, hw, u, hu, hwu⟩ := h.decomp hv
  have hve : v = (g⁻¹ * w * g) * u := by
    have hug : g⁻¹ * u * g = u := by
      have hcomm : u * g = g * u := Subgroup.mem_centralizer_iff.1 hg u hu
      calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
        _ = g⁻¹ * (g * u) := by rw [hcomm]
        _ = u := by group
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = g⁻¹ * (w * u) * g := by rw [hwu]
      _ = (g⁻¹ * w * g) * (g⁻¹ * u * g) := by group
      _ = (g⁻¹ * w * g) * u := by rw [hug]
  have hw' : g⁻¹ * w * g ∈ conjSubgroup V₀ g := by
    rw [mem_conjSubgroup_iff, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
    exact hw
  have hxw : x * (g⁻¹ * w * g) * x⁻¹ ∈ conjSubgroup V₀ g :=
    (Subgroup.mem_normalizer_iff.1 hxN _).1 hw'
  have hxu : x * u * x⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hxU u hu
  have e : x * v * x⁻¹ * v⁻¹ = (x * (g⁻¹ * w * g) * x⁻¹) * (g⁻¹ * w * g)⁻¹ := by
    rw [hve]
    calc x * ((g⁻¹ * w * g) * u) * x⁻¹ * ((g⁻¹ * w * g) * u)⁻¹
        = (x * (g⁻¹ * w * g) * x⁻¹) * (x * u * x⁻¹) * u⁻¹ * (g⁻¹ * w * g)⁻¹ := by group
      _ = (x * (g⁻¹ * w * g) * x⁻¹) * (g⁻¹ * w * g)⁻¹ := by rw [hxu]; group
  rw [e]
  exact (conjSubgroup V₀ g).mul_mem hxw ((conjSubgroup V₀ g).inv_mem hw')

theorem inCalO1_conj (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    InCalO1 (mSub V - 1) M V₀ V g :=
  ⟨⟨⟨h.not_conj_V_le_M hI hS hg hgM, (h.mQuot_conj_le hg).1,
      fun _ => (h.inf_conj_ne_bot hS hg).1⟩,
    ⟨h.not_V_le_conj_M hI hS hg hgM, (h.mQuot_conj_le hg).2,
      fun _ => (h.inf_conj_ne_bot hS hg).2⟩⟩, h.oneFirst_conj hg, h.oneDual_conj hg⟩

theorem not_commutator_conj_le (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hgM : g ∉ M) : ¬ ⁅conjSubgroup V₀ g, V ⊓ conjSubgroup M g⁆ ≤ V₀ := by
  intro hcomm
  have hH := h.hyp
  obtain ⟨hD, -⟩ := h.inf_conj_ne_bot hS hg
  obtain ⟨⟨d, hdmem⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  obtain ⟨hdV₀, hdMg⟩ := Subgroup.mem_inf.1 hdmem
  have hdN : d ∈ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← E3.conjSubgroup_normalizer, hH.normalizer₀]
    exact hdMg
  have hcent : conjSubgroup V₀ g ≤ centralizer ({d} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hc : ⁅y, d⁆ ∈ ⁅conjSubgroup V₀ g, V ⊓ conjSubgroup M g⁆ :=
      Subgroup.commutator_mem_commutator hy (Subgroup.mem_inf.2 ⟨hH.h6.le hdV₀, hdMg⟩)
    have h1 : ⁅y, d⁆ ∈ V₀ := hcomm hc
    have h2 : ⁅y, d⁆ ∈ conjSubgroup V₀ g := by
      have h3 := (Subgroup.mem_normalizer_iff.1 hdN y⁻¹).1 ((conjSubgroup V₀ g).inv_mem hy)
      have h4 : ⁅y, d⁆ = y * (d * y⁻¹ * d⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h4]
      exact (conjSubgroup V₀ g).mul_mem hy h3
    have h5 : ⁅y, d⁆ ∈ conjSubgroup V₀ g ⊓ V₀ := Subgroup.mem_inf.2 ⟨h2, h1⟩
    rw [hH.conj_inf_eq_bot hgM, Subgroup.mem_bot, commutatorElement_def] at h5
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h5)).symm
  exact h.not_conj_V₀_le_M hI hS hg hgM fun y hy => hH.centralizer_le hdV₀ hd1' (hcent hy)

theorem fourteen_five_conj (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    E3.mQuot V (conjSubgroup M g) = 1 ∧
      M ≤ normalizer ((V₀ ⊓ conjSubgroup M g : Subgroup G) : Set G) ∧
        ⁅F11.CTilde M V₀ V, V⁆ ≤ V₀ ⊓ conjSubgroup M g := by
  obtain ⟨⟨h1, -⟩, h2⟩ := hI.w145 M V₀ V h.hyp g (h.inCalO1_conj hI hS hg hgM)
    (h.not_commutator_conj_le hI hS hg hgM)
  exact ⟨h1, h2⟩

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
