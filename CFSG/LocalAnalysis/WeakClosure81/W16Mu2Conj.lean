module

public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem conj_V₀_le_cTilde (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    conjSubgroup V₀ g ≤ F11.CTilde M V₀ V := by
  intro x hx
  have hw : g * x * g⁻¹ ∈ V₀ := mem_conjSubgroup_iff.1 hx
  have hgi : g⁻¹ ∈ centralizer (U : Set G) := (centralizer (U : Set G)).inv_mem hg
  have hgiM : g⁻¹ ∉ M := fun hmem => hgM (by simpa using M.inv_mem hmem)
  have hinf := h.inf_conjSubgroup_eq h1 h5 h15 hS hgi hgiM
  have hxM : x ∈ M := by
    have hwM : g * x * g⁻¹ ∈ conjSubgroup M g⁻¹ := by
      have hmem : g * x * g⁻¹ ∈ V ⊓ conjSubgroup M g⁻¹ := by
        rw [hinf]
        exact Subgroup.mem_sup_right hw
      exact hmem.2
    have hmem' := mem_conjSubgroup_iff.1 hwM
    have e : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rwa [e] at hmem'
  have hxC : x ∈ centralizer (U : Set G) := by
    have hwC : g * x * g⁻¹ ∈ centralizer (U : Set G) :=
      h.V_le_centralizer (h.hyp.h6.le hw)
    have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxeq]
    exact (centralizer (U : Set G)).mul_mem
      ((centralizer (U : Set G)).mul_mem ((centralizer (U : Set G)).inv_mem hg) hwC) hg
  have hx2 : x ^ 2 = 1 := by
    have hw2 : (g * x * g⁻¹) ^ 2 = 1 :=
      h.hyp.h6.elemAbelian.2 (g * x * g⁻¹) (h.hyp.h6.le hw)
    have hconj : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hconj] at hw2
    have e : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
    rw [e, hw2]
    group
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  obtain ⟨k, -, hk⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf x ∣ 2 ^ 1 by simpa using hdvd)
  exact h.mem_cTilde_of_orderOf ⟨hxM, hxC⟩ ⟨k, hk⟩

private theorem exists_conj_not_mem_sup (h152 : Thm152 G) (h : Cex16 M V₀ V U S) {u : G}
    (hu : u ∈ V) (hu0 : u ∉ V₀) : ∃ m ∈ M, m * u * m⁻¹ ∉ U ⊔ V₀ := by
  by_contra hcon
  have hall : ∀ m ∈ M, m * u * m⁻¹ ∈ U ⊔ V₀ := by
    intro m hm
    by_contra hn
    exact hcon ⟨m, hm, hn⟩
  have hVA : V ≤ U ⊔ V₀ := by
    rw [h.hyp.h6.conjGenerated h.hyp.ne_bot u hu hu0]
    exact (Subgroup.closure_le (K := U ⊔ V₀)).2 fun x hx => by
      obtain ⟨m, hm, rfl⟩ := hx
      exact hall m hm
  exact h.sup_ne_top h152 (le_antisymm (sup_le h.le h.hyp.h6.le) hVA)

private theorem exists_mem_conj_comm_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hgM : g ∉ M) {v : G} (hv : v ∈ V) (hvU : v ∉ U ⊔ V₀) {w : G} (hw : w ∈ V₀) :
    ∃ x ∈ conjSubgroup V₀ g, x * v * x⁻¹ * v⁻¹ = w := by
  classical
  have hT : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V :=
    h.conj_V₀_le_cTilde h1 h5 h15 hS hg hgM
  have hcomm : ∀ x ∈ conjSubgroup V₀ g, x * v * x⁻¹ * v⁻¹ ∈ V₀ := fun x hx =>
    (FourteenTwo.mem_cTilde_iff_comm.1 (hT hx)).2.2 v hv
  let φ : ↥(conjSubgroup V₀ g) → ↥V₀ := fun x => ⟨x * v * x⁻¹ * v⁻¹, hcomm x x.2⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : (x : G) * v * (x : G)⁻¹ = (y : G) * v * (y : G)⁻¹ := by
      have hh : (x : G) * v * (x : G)⁻¹ * v⁻¹ = (y : G) * v * (y : G)⁻¹ * v⁻¹ :=
        congrArg Subtype.val hxy
      exact mul_right_cancel hh
    set z : G := (y : G)⁻¹ * (x : G) with hzdef
    have hzv : z * v * z⁻¹ = v := by
      rw [hzdef]
      calc (y : G)⁻¹ * (x : G) * v * ((y : G)⁻¹ * (x : G))⁻¹
          = (y : G)⁻¹ * ((x : G) * v * (x : G)⁻¹) * (y : G) := by group
        _ = (y : G)⁻¹ * ((y : G) * v * (y : G)⁻¹) * (y : G) := by rw [hxy']
        _ = v := by group
    have hzT : z ∈ conjSubgroup V₀ g := by
      rw [hzdef]
      exact (conjSubgroup V₀ g).mul_mem ((conjSubgroup V₀ g).inv_mem y.2) x.2
    by_cases hz1 : z = 1
    · exact Subtype.ext (by
        rw [hzdef] at hz1
        calc (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
          _ = (y : G) * 1 := by rw [hz1]
          _ = (y : G) := by group)
    · exfalso
      have hcen := h.inf_centralizer_eq h1 h5 h15 hS hg hgM hT hzT hz1
      have hzv' : z * v = v * z := by
        rw [mul_inv_eq_iff_eq_mul] at hzv
        exact hzv
      have hvmem : v ∈ V ⊓ centralizer ({z} : Set G) :=
        Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 hzv'.symm⟩
      rw [hcen] at hvmem
      exact hvU hvmem
  have hcard : Nat.card ↥(conjSubgroup V₀ g) = Nat.card ↥V₀ := E3.card_conjSubgroup V₀ g
  have hbij : Function.Bijective φ := hφinj.bijective_of_nat_card_le (le_of_eq hcard.symm)
  obtain ⟨x, hx⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨x, x.2, by
    have hval : (x : G) * v * (x : G)⁻¹ * v⁻¹ = w := congrArg Subtype.val hx
    exact hval⟩

theorem exists_mem_M_conj_eq_mul (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h152 : Thm152 G) (h : Cex16 M V₀ V U S) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    {w : G} (hw : w ∈ V₀) : ∃ c ∈ M, c * u * c⁻¹ = u * w := by
  have huV : u ∈ V := h.le hu
  have huV₀ : u ∉ V₀ := by
    intro hmem
    have hboth : u ∈ U ⊓ V₀ := ⟨hu, hmem⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at hboth
    exact hu1 hboth
  obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.1 h.not_le
  obtain ⟨m, hmM, hmv⟩ := exists_conj_not_mem_sup h152 h huV huV₀
  have hmN : m ∈ normalizer (V : Set G) := by
    rw [h.hyp.h6.normalizer_eq]
    exact hmM
  have hvV : m * u * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hmN u).1 huV
  have hw' : m * w * m⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.1 (h.hyp.h6.le_normalizer₀ hmM) w).1 hw
  obtain ⟨x, hxT, hxeq⟩ := exists_mem_conj_comm_eq h1 h5 h15 hS h hg hgM hvV hmv hw'
  have hxM : x ∈ M := cTilde_le_M M V₀ V (h.conj_V₀_le_cTilde h1 h5 h15 hS hg hgM hxT)
  refine ⟨m⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem hmM) hxM) hmM, ?_⟩
  have hxv : x * (m * u * m⁻¹) * x⁻¹ = (m * w * m⁻¹) * (m * u * m⁻¹) := by
    have hh := hxeq
    rw [mul_inv_eq_iff_eq_mul] at hh
    exact hh
  calc (m⁻¹ * x * m) * u * (m⁻¹ * x * m)⁻¹
      = m⁻¹ * (x * (m * u * m⁻¹) * x⁻¹) * m := by group
    _ = m⁻¹ * ((m * w * m⁻¹) * (m * u * m⁻¹)) * m := by rw [hxv]
    _ = (m⁻¹ * (m * w * m⁻¹) * m) * (m⁻¹ * (m * u * m⁻¹) * m) := by group
    _ = w * u := by
      have e1 : m⁻¹ * (m * w * m⁻¹) * m = w := by group
      have e2 : m⁻¹ * (m * u * m⁻¹) * m = u := by group
      rw [e1, e2]
    _ = u * w := B2F.isElemAbelian_comm h.hyp.h6.elemAbelian (h.hyp.h6.le hw) huV

theorem not_centralizer_le_of_mem_sup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h152 : Thm152 G) (h : Cex16 M V₀ V U S) {x : G} (hx : x ∈ U ⊔ V₀)
    (hx0 : x ∉ V₀) : ¬ centralizer ({x} : Set G) ≤ M := by
  obtain ⟨u, hu, w, hw, huw⟩ := h.exists_mul_of_mem_sup hx
  have hu1 : u ≠ 1 := by
    intro hu1
    apply hx0
    rw [← huw, hu1, one_mul]
    exact hw
  obtain ⟨c, hcM, hc⟩ := h.exists_mem_M_conj_eq_mul h1 h5 h15 hS h152 hu hu1 hw
  obtain ⟨y, hy, hyM⟩ := SetLike.not_le_iff_exists.1 h.not_le
  intro hle
  have hcx : c * u * c⁻¹ = x := hc.trans huw
  have hcyc : c * y * c⁻¹ ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have hyu : u * y = y * u := Subgroup.mem_centralizer_iff.1 hy u hu
    calc x * (c * y * c⁻¹) = (c * u * c⁻¹) * (c * y * c⁻¹) := by rw [hcx]
      _ = c * (u * y) * c⁻¹ := by group
      _ = c * (y * u) * c⁻¹ := by rw [hyu]
      _ = (c * y * c⁻¹) * (c * u * c⁻¹) := by group
      _ = (c * y * c⁻¹) * x := by rw [hcx]
  have hcyM : c * y * c⁻¹ ∈ M := hle hcyc
  exact hyM (by
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    rw [← e]
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) hcyM) hcM)

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
