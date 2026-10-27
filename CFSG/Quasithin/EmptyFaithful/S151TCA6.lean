module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.S151TC

namespace A6Aux

open Equiv Equiv.Perm

def dihedralPerms : List (Perm (Fin 6)) :=
  [1,
   swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5,
   swap 0 2 * swap 1 3,
   swap 4 5 * swap 2 3 * swap 1 2 * swap 0 1,
   swap 0 2 * swap 4 5,
   swap 0 1 * swap 2 3,
   swap 1 3 * swap 4 5,
   swap 0 3 * swap 1 2]

def centralInvolution : Perm (Fin 6) := swap 0 2 * swap 1 3

theorem mul_mem_dihedralPerms :
    ∀ a ∈ dihedralPerms, ∀ b ∈ dihedralPerms, a * b ∈ dihedralPerms := by
  have h : dihedralPerms.all
      (fun a => dihedralPerms.all (fun b => decide (a * b ∈ dihedralPerms))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem inv_mem_dihedralPerms : ∀ a ∈ dihedralPerms, a⁻¹ ∈ dihedralPerms := by
  have h : dihedralPerms.all (fun a => decide (a⁻¹ ∈ dihedralPerms)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem sign_eq_one_of_mem_dihedralPerms : ∀ a ∈ dihedralPerms, sign a = 1 := by
  have h : dihedralPerms.all (fun a => decide (sign a = 1)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem card_dihedralPerms : dihedralPerms.toFinset.card = 8 := by decide +kernel

theorem centralInvolution_mem : centralInvolution ∈ dihedralPerms := by decide +kernel

theorem centralInvolution_ne_one : centralInvolution ≠ 1 := by decide +kernel

theorem centralInvolution_mul_self : centralInvolution * centralInvolution = 1 := by
  decide +kernel

theorem centralInvolution_comm :
    ∀ d ∈ dihedralPerms, centralInvolution * d = d * centralInvolution := by
  have h : dihedralPerms.all
      (fun d => decide (centralInvolution * d = d * centralInvolution)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem eq_centralInvolution_of_central :
    ∀ x ∈ dihedralPerms, x ≠ 1 → x * x = 1 → (∀ d ∈ dihedralPerms, x * d = d * x) →
      x = centralInvolution := by
  have h : dihedralPerms.all (fun x => decide (x ≠ 1 → x * x = 1 →
      dihedralPerms.all (fun d => decide (x * d = d * x)) = true → x = centralInvolution)) =
        true := by
    decide +kernel
  intro x hx h1 h2 h3
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx h1 h2 (by simpa only [List.all_eq_true, decide_eq_true_eq] using h3)

theorem mem_dihedralPerms_of_commute_of_sign (σ : Perm (Fin 6))
    (hσ : σ * centralInvolution = centralInvolution * σ) (hs : sign σ = 1) :
    σ ∈ dihedralPerms := by
  have h : (Finset.univ.filter (fun σ : Perm (Fin 6) =>
      σ * centralInvolution = centralInvolution * σ ∧ sign σ = 1 ∧
        σ ∉ dihedralPerms)).card = 0 := by
    decide +kernel
  by_contra hn
  have h2 := Finset.card_eq_zero.1 h
  have h3 : σ ∈ Finset.univ.filter (fun σ : Perm (Fin 6) =>
      σ * centralInvolution = centralInvolution * σ ∧ sign σ = 1 ∧ σ ∉ dihedralPerms) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ σ, hσ, hs, hn⟩
  rw [h2] at h3
  exact absurd h3 (Finset.notMem_empty σ)

def dihedral : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | (x : Perm (Fin 6)) ∈ dihedralPerms}
  one_mem' := List.mem_cons_self
  mul_mem' := fun {_ _} ha hb => mul_mem_dihedralPerms _ ha _ hb
  inv_mem' := fun {_} ha => inv_mem_dihedralPerms _ ha

theorem mem_dihedral {x : alternatingGroup (Fin 6)} :
    x ∈ dihedral ↔ (x : Perm (Fin 6)) ∈ dihedralPerms :=
  Iff.rfl

theorem card_dihedral : Nat.card dihedral = 8 := by
  have h1 : Nat.card dihedral = (dihedral : Set (alternatingGroup (Fin 6))).ncard :=
    Nat.card_coe_set_eq (dihedral : Set (alternatingGroup (Fin 6)))
  have h2 : (dihedral : Set (alternatingGroup (Fin 6))) =
      Subtype.val ⁻¹' ((dihedralPerms.toFinset : Finset (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
    ext x
    simp only [SetLike.mem_coe, mem_dihedral, Set.mem_preimage, List.mem_toFinset]
  rw [h1, h2, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective,
    Set.ncard_coe_finset, card_dihedralPerms]
  intro σ hσ
  have hσ' : σ ∈ dihedralPerms := List.mem_toFinset.1 hσ
  exact ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_mem_dihedralPerms σ hσ')⟩, rfl⟩

theorem normalizer_dihedral :
    Subgroup.normalizer (dihedral : Set (alternatingGroup (Fin 6))) = dihedral := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  have hg' := Subgroup.mem_normalizer_iff.1 hg
  have h1 : ∀ d ∈ dihedralPerms,
      (g : Perm (Fin 6)) * d * (g : Perm (Fin 6))⁻¹ ∈ dihedralPerms := by
    intro d hd
    have hdA : (⟨d, Equiv.Perm.mem_alternatingGroup.2
        (sign_eq_one_of_mem_dihedralPerms d hd)⟩ : alternatingGroup (Fin 6)) ∈ dihedral := hd
    exact (hg' _).1 hdA
  have h2 : ∀ d ∈ dihedralPerms,
      (g : Perm (Fin 6))⁻¹ * d * (g : Perm (Fin 6)) ∈ dihedralPerms := by
    intro d hd
    set dA : alternatingGroup (Fin 6) := ⟨d, Equiv.Perm.mem_alternatingGroup.2
        (sign_eq_one_of_mem_dihedralPerms d hd)⟩ with hdAdef
    have hdA : dA ∈ dihedral := hd
    have e : g * (g⁻¹ * dA * g) * g⁻¹ = dA := by group
    exact (hg' (g⁻¹ * dA * g)).2 (by rw [e]; exact hdA)
  set σ : Perm (Fin 6) := (g : Perm (Fin 6)) with hσ
  have hx : σ * centralInvolution * σ⁻¹ ∈ dihedralPerms := h1 _ centralInvolution_mem
  have hx1 : σ * centralInvolution * σ⁻¹ ≠ 1 := by
    intro h
    apply centralInvolution_ne_one
    calc centralInvolution = σ⁻¹ * (σ * centralInvolution * σ⁻¹) * σ := by group
      _ = 1 := by rw [h]; group
  have hxx : (σ * centralInvolution * σ⁻¹) * (σ * centralInvolution * σ⁻¹) = 1 := by
    calc (σ * centralInvolution * σ⁻¹) * (σ * centralInvolution * σ⁻¹)
        = σ * (centralInvolution * centralInvolution) * σ⁻¹ := by group
      _ = 1 := by rw [centralInvolution_mul_self]; group
  have hxc : ∀ d ∈ dihedralPerms,
      (σ * centralInvolution * σ⁻¹) * d = d * (σ * centralInvolution * σ⁻¹) := by
    intro d hd
    have hc := centralInvolution_comm (σ⁻¹ * d * σ) (h2 d hd)
    calc σ * centralInvolution * σ⁻¹ * d
        = σ * (centralInvolution * (σ⁻¹ * d * σ)) * σ⁻¹ := by group
      _ = σ * ((σ⁻¹ * d * σ) * centralInvolution) * σ⁻¹ := by rw [hc]
      _ = d * (σ * centralInvolution * σ⁻¹) := by group
  have hxu := eq_centralInvolution_of_central _ hx hx1 hxx hxc
  have hcomm : σ * centralInvolution = centralInvolution * σ := mul_inv_eq_iff_eq_mul.1 hxu
  exact mem_dihedralPerms_of_commute_of_sign σ hcomm
    (Equiv.Perm.mem_alternatingGroup.1 g.2)

theorem exists_conj_of_card_eight (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : Nat.card D = 8) :
    ∃ g : alternatingGroup (Fin 6), ∀ x : alternatingGroup (Fin 6),
      x ∈ D ↔ g⁻¹ * x * g ∈ dihedral := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hidx : ∀ H : Subgroup (alternatingGroup (Fin 6)), Nat.card H = 8 → ¬ 2 ∣ H.index := by
    intro H hH h2
    have := H.card_mul_index
    rw [hH, hcard] at this
    omega
  have hp : ∀ H : Subgroup (alternatingGroup (Fin 6)), Nat.card H = 8 → IsPGroup 2 H :=
    fun H hH => IsPGroup.of_card (n := 3) (by rw [hH]; norm_num)
  let P : Sylow 2 (alternatingGroup (Fin 6)) := (hp D hD).toSylow (hidx D hD)
  let P₀ : Sylow 2 (alternatingGroup (Fin 6)) :=
    (hp dihedral card_dihedral).toSylow (hidx dihedral card_dihedral)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) P₀ P
  refine ⟨g, fun x => ?_⟩
  have h2 : ((g • P₀ : Sylow 2 (alternatingGroup (Fin 6))) :
      Subgroup (alternatingGroup (Fin 6))) = (P : Subgroup (alternatingGroup (Fin 6))) := by
    rw [hg]
  have h3 : x ∈ (P : Subgroup (alternatingGroup (Fin 6))) ↔
      g⁻¹ * x * g ∈ (P₀ : Subgroup (alternatingGroup (Fin 6))) := by
    rw [← h2, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  exact h3

end A6Aux

theorem alt6_normalizer_eq_of_card_eight (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : Nat.card D = 8) :
    Subgroup.normalizer (D : Set (alternatingGroup (Fin 6))) = D := by
  obtain ⟨g, hg⟩ := A6Aux.exists_conj_of_card_eight D hD
  refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
  rw [hg]
  have hxn : g⁻¹ * x * g ∈
      Subgroup.normalizer (A6Aux.dihedral : Set (alternatingGroup (Fin 6))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := hg (g * h * g⁻¹)
    have h2 := hg (x * (g * h * g⁻¹) * x⁻¹)
    have h3 := Subgroup.mem_normalizer_iff.1 hx (g * h * g⁻¹)
    have e1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    have e2 : g⁻¹ * (x * (g * h * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * h * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1] at h1
    rw [e2] at h2
    exact h1.symm.trans (h3.trans h2)
  rw [A6Aux.normalizer_dihedral] at hxn
  exact hxn

theorem eq_of_normal_of_inf_center_eq_bot {Γ : Type} [Group Γ]
    (e : Γ ⧸ Subgroup.center Γ ≃* alternatingGroup (Fin 6)) {D T : Subgroup Γ}
    (hD : Nat.card D = 8) (hDT : D ≤ T) (hTZ : T ⊓ Subgroup.center Γ = ⊥)
    (hN : (D.subgroupOf T).Normal) : T = D := by
  let π : Γ →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Γ))
  have hπ : ∀ x y : Γ, π x = π y → x⁻¹ * y ∈ Subgroup.center Γ := by
    intro x y hxy
    have h1 : (QuotientGroup.mk' (Subgroup.center Γ)) x =
        (QuotientGroup.mk' (Subgroup.center Γ)) y := e.injective hxy
    exact QuotientGroup.eq.1 h1
  have hinj : Set.InjOn π T := by
    intro x hx y hy hxy
    have h2 : x⁻¹ * y ∈ T ⊓ Subgroup.center Γ :=
      ⟨T.mul_mem (T.inv_mem hx) hy, hπ x y hxy⟩
    rw [hTZ, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  have hcard : Nat.card (D.map π) = 8 := by
    rw [← hD]
    exact Nat.card_image_of_injOn (hinj.mono hDT)
  have hnorm := alt6_normalizer_eq_of_card_eight (D.map π) hcard
  refine le_antisymm (fun t ht => ?_) hDT
  have hconj : ∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
    intro t ht d hd
    have := hN.conj_mem ⟨d, hDT hd⟩ (by simpa [Subgroup.mem_subgroupOf] using hd) ⟨t, ht⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hmem : π t ∈
      Subgroup.normalizer ((D.map π : Subgroup (alternatingGroup (Fin 6))) :
        Set (alternatingGroup (Fin 6))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨t * d * t⁻¹, hconj t ht d hd, by simp⟩
    · rintro ⟨d, hd, hdh⟩
      have hd' : t⁻¹ * d * t ∈ D := by
        simpa using hconj t⁻¹ (T.inv_mem ht) d hd
      refine ⟨t⁻¹ * d * t, hd', ?_⟩
      rw [map_mul, map_mul, map_inv, hdh]
      group
  rw [hnorm] at hmem
  obtain ⟨d, hd, hdt⟩ := hmem
  have : d = t := hinj (hDT hd) ht hdt
  rw [← this]
  exact hd

end CFSG.Quasithin.S151TC
