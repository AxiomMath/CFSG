module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20AGeo
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20AMod
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseD

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_cSecIn' {F L N : Subgroup G} (hFL : F ≤ Subgroup.normalizer (L : Set G)) {f : G}
    (hf : f ∈ cSecIn F L N) : f ∈ F ∧ ∀ x ∈ N, ⁅f, x⁆ ∈ L := by
  induction hf using Subgroup.closure_induction with
  | mem f hf => exact hf
  | one => exact ⟨F.one_mem, fun x _ => by simp [L.one_mem]⟩
  | mul f g _ _ hf hg =>
    refine ⟨F.mul_mem hf.1 hg.1, fun x hx => ?_⟩
    rw [comm_mul_left]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFL hf.1) _).mp (hg.2 x hx)) (hf.2 x hx)
  | inv f _ hf =>
    refine ⟨F.inv_mem hf.1, fun x hx => ?_⟩
    rw [comm_inv_left]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hFL (F.inv_mem hf.1)) _).mp
      (L.inv_mem (hf.2 x hx))
    rwa [inv_inv] at h1

omit [Finite G] in
theorem comm_conj (g f x : G) : ⁅g * f * g⁻¹, x⁆ = g * ⁅f, g⁻¹ * x * g⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

variable {α β : Geo H M}

theorem mem_Qgrp_iff (hA : F53Amalgam H M S) {g : G} :
    g ∈ Qgrp α β ↔ g ∈ stab α ⊓ stab β ∧ ∀ x ∈ Vst β, ⁅g, x⁆ ∈ Zv β :=
  ⟨mem_cSecIn' (inf_le_right.trans (stab_le_normalizer_Zv hA β)),
    fun h => Subgroup.subset_closure h⟩

theorem mem_Qv_of_triv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {g : G} (hg : g ∈ stab β) (htriv : ∀ x ∈ Vst β, ⁅g, x⁆ ∈ Zv β) :
    g ∈ Qv β := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hZn := stab_le_normalizer_Zv hA β
  have htriv' : ∀ x ∈ Vst β, ⁅g⁻¹, x⁆ ∈ Zv β := fun x hx => by
    rw [comm_inv_left]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hZn ((stab β).inv_mem hg)) _).mp
      ((Zv β).inv_mem (htriv x hx))
    rwa [inv_inv] at h1
  let g' : ↥(H ⊔ M) := ⟨g, stab_le β hg⟩
  have hfix : ∀ μ ∈ nbrs β, g' • μ = μ := by
    intro μ hμ
    by_contra hne
    have hμ' : g' • μ ∈ nbrs β := smul_mem_nbrs_of_mem_stab g' hg hμ
    have hle : ⁅Zv μ, Qv β⁆ ≤ Yv β := by
      rw [← hs.inf_Zv_eq_Yv hA h26 hβv hμ hμ' (Ne.symm hne)]
      refine le_inf (hs.comm_le_Zv hA h26 hβv hμ) fun x hx => ?_
      rw [Zv_smul, mem_conjSub]
      show g⁻¹ * x * g ∈ Zv μ
      have e : g⁻¹ * x * g = ⁅g⁻¹, x⁆ * x := by
        rw [commutatorElement_def]
        group
      rw [e]
      refine hs.comm_le_Zv hA h26 hβv hμ ((⁅Zv μ, Qv β⁆).mul_mem ?_ hx)
      exact hs.Yv_le_comm hA h26 hβv hμ (Zv_le_Yv hA h26 hs hβv (htriv' x (A_le_Vst hμ hx)))
    have := Subgroup.card_le_of_le hle
    rw [hs.card_comm_Qv hA h26 hβv hμ, hs.card_Yv hA h26 hβv] at this
    omega
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hβv
  obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hβv hl
  exact h29.mem_Qv_of_fixes g' hg hfix

theorem mem_stab_of_triv_Mab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {g : G} (hg : g ∈ Mab α β) (htriv : ∀ x ∈ Vst β, ⁅g, x⁆ ∈ Zv β) :
    g ∈ stab β := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have h4 := (Sit43.mem_Mab_iff D ⟨g, Mab_le_stab α β hg⟩).mp hg
  have hZ := hs.Zv_inf_centralizer hA h26 hβv (nbrs_symm hβ)
  have hcomm := hs.comm_Qv_eq hA h26 hβv (nbrs_symm hβ)
  have h1 := D5.mem_S_of_triv D h4 fun v hv => by
    rw [hZ]
    refine htriv v (A_le_Vst (nbrs_symm hβ) ?_)
    rw [hcomm]
    exact hv
  exact h1.2

theorem Mab_comm_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {g z : G} (hg : g ∈ Mab α β) (hz : z ∈ Zv β) : g * z = z * g := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have h4 := (Sit43.mem_Mab_iff D ⟨g, Mab_le_stab α β hg⟩).mp hg
  rw [← hs.Zv_inf_centralizer hA h26 hβv (nbrs_symm hβ)] at hz
  exact D5.comm_fix D h4 hz

theorem Mab_le_normalizer_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) : Mab α β ≤ Subgroup.normalizer (Zv β : Set G) :=
  Sit43.le_normalizer_of_conj_mem fun g hg z hz => by
    rw [Mab_comm_Zv hA h26 hs hβ hg hz, mul_inv_cancel_right]
    exact hz

theorem exists_Mab_not_normalizer_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (hβ : β ∈ nbrs α) :
    ∃ m ∈ Mab α β, m ∉ Subgroup.normalizer (Yv β : Set G) := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  obtain ⟨x, h4, hxS⟩ := D5.exists_not_mem_S D
  refine ⟨x, (Sit43.mem_Mab_iff D x).mpr h4, fun hN => hxS ?_⟩
  rw [hs.Yv_eq_comm_comm hA h26 hβv (nbrs_symm hβ)] at hN
  rw [← normalizer_Y (quot_stab_five hA hs.vα) (sylow_stab_inf_left hA hβ) hs.orth]
  exact ⟨x.2, hN⟩

theorem Qgrp_le_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) : Qgrp α β ≤ Qv β := fun g hg => by
  obtain ⟨hgE, htriv⟩ := (mem_Qgrp_iff hA).mp hg
  exact mem_Qv_of_triv hA h26 hs hβ hgE.2 htriv

theorem le_normalizer_of_triv (hA : F53Amalgam H M S) {N : Subgroup G}
    (hNV : N ≤ Subgroup.normalizer (Vst β : Set G))
    (hNZ : N ≤ Subgroup.normalizer (Zv β : Set G)) (hNE : stab α ⊓ stab β ≤ N)
    (htriv : ∀ g ∈ N, (∀ x ∈ Vst β, ⁅g, x⁆ ∈ Zv β) → g ∈ stab α ⊓ stab β) :
    N ≤ Subgroup.normalizer (Qgrp α β : Set G) ∧
      N ≤ Subgroup.normalizer
        ((stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) : Subgroup G) : Set G) := by
  have hVinv : ∀ g ∈ N, ∀ x ∈ Vst β, g⁻¹ * x * g ∈ Vst β := fun g hg x hx => by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNV (N.inv_mem hg)) x).mp hx
    rwa [inv_inv] at h1
  refine ⟨Sit43.le_normalizer_of_conj_mem fun g hg f hf => ?_,
    Sit43.le_normalizer_of_conj_mem fun g hg c hc => ?_⟩
  · obtain ⟨hfE, hft⟩ := (mem_Qgrp_iff hA).mp hf
    have ht : ∀ x ∈ Vst β, ⁅g * f * g⁻¹, x⁆ ∈ Zv β := fun x hx => by
      rw [comm_conj]
      exact (Subgroup.mem_normalizer_iff.mp (hNZ hg) _).mp (hft _ (hVinv g hg x hx))
    exact (mem_Qgrp_iff hA).mpr
      ⟨htriv _ (N.mul_mem (N.mul_mem hg (hNE hfE)) (N.inv_mem hg)) ht, ht⟩
  · obtain ⟨hcE, hcC⟩ := hc
    have hC : g * c * g⁻¹ ∈ Subgroup.centralizer (Vst β : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hcC _ (hVinv g hg x hx)
      calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * x := by group
    have ht : ∀ x ∈ Vst β, ⁅g * c * g⁻¹, x⁆ ∈ Zv β := fun x hx => by
      have h1 : ⁅g * c * g⁻¹, x⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hC x hx).symm
      rw [h1]
      exact (Zv β).one_mem
    exact ⟨htriv _ (N.mul_mem (N.mul_mem hg (hNE hcE)) (N.inv_mem hg)) ht, hC⟩

theorem stab_le_normalizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) :
    stab β ≤ Subgroup.normalizer (Qgrp α β : Set G) ∧
      stab β ≤ Subgroup.normalizer
        ((stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_triv hA (stab_le_normalizer_Vst β) (stab_le_normalizer_Zv hA β) inf_le_right
    fun _ hg ht => ⟨Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) (mem_Qv_of_triv hA h26 hs hβ hg ht),
      hg⟩

theorem Mab_le_normalizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) (hV : Mab α β ≤ Subgroup.normalizer (Vst β : Set G)) :
    Mab α β ≤ Subgroup.normalizer (Qgrp α β : Set G) ∧
      Mab α β ≤ Subgroup.normalizer
        ((stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_triv hA hV (Mab_le_normalizer_Zv hA h26 hs hβ) (hs.stab_inf_le_Mab hA hβ)
    fun _ hg ht => ⟨Mab_le_stab α β hg, mem_stab_of_triv_Mab hA h26 hs hβ hg ht⟩

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A
