module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private abbrev he42ke_c : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem he42ke_le_ker {Δ : Type*} [Group Δ] {L K A J R : Subgroup Δ}
    {ψ : ↥L →* Equiv.Perm (Fin 5)} (hP : PData L K A J ψ) (hRK : R ≤ K)
    (hRn : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) : R ≤ A := by
  have hψA : ∀ k : ↥L, ψ k ∈ alternatingGroup (Fin 5) := fun k => by
    rw [← hP.range]
    exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
  have hQ : (((R.subgroupOf L).map ψ).subgroupOf (alternatingGroup (Fin 5))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.mp hn
    have hg : (g : Equiv.Perm (Fin 5)) ∈ ψ.range := by
      rw [hP.range]
      exact g.2
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hg
    refine Subgroup.mem_map.mpr ⟨l * k * l⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact hRn _ l.2 _ (Subgroup.mem_subgroupOf.mp hk)
    · simp only [map_mul, map_inv, hl, hkn, Subgroup.coe_mul, Subgroup.coe_inv]
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  rcases hsimple.eq_bot_or_eq_top_of_normal
      (((R.subgroupOf L).map ψ).subgroupOf (alternatingGroup (Fin 5))) with hbot | htop
  ·
    intro r hr
    have hrL : r ∈ L := hP.KL (hRK hr)
    have hk : (⟨r, hrL⟩ : ↥L) ∈ R.subgroupOf L := Subgroup.mem_subgroupOf.mpr hr
    have hmem : (⟨ψ ⟨r, hrL⟩, hψA ⟨r, hrL⟩⟩ : ↥(alternatingGroup (Fin 5))) ∈
        ((R.subgroupOf L).map ψ).subgroupOf (alternatingGroup (Fin 5)) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨⟨r, hrL⟩, hk, rfl⟩)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : ψ ⟨r, hrL⟩ = 1 := congrArg Subtype.val hmem
    have h2 : (⟨r, hrL⟩ : ↥L) ∈ ψ.ker := MonoidHom.mem_ker.mpr h1
    rw [hP.ker] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  ·
    exfalso
    have hc : he42ke_c ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)
    have hc0 : he42ke_c 0 ≠ 0 := by decide
    have hc' : (⟨he42ke_c, hc⟩ : ↥(alternatingGroup (Fin 5))) ∈
        ((R.subgroupOf L).map ψ).subgroupOf (alternatingGroup (Fin 5)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkc⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hc')
    have h0 : ψ k 0 = 0 := (hP.stab k).mpr (hRK (Subgroup.mem_subgroupOf.mp hk))
    rw [hkc] at h0
    exact hc0 h0

private def he42ke_R (S : HeSetup G) : Subgroup G where
  carrier := {r | r ∈ S.L ∧ ∀ x ∈ S.L, x⁻¹ * r * x ∈ S.L1}
  mul_mem' := fun {a b} ha hb => ⟨S.L.mul_mem ha.1 hb.1, fun x hx => by
    rw [show x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) by group]
    exact S.L1.mul_mem (ha.2 x hx) (hb.2 x hx)⟩
  one_mem' := ⟨S.L.one_mem, fun x _ => by
    rw [show x⁻¹ * 1 * x = 1 by group]
    exact S.L1.one_mem⟩
  inv_mem' := fun {a} ha => ⟨S.L.inv_mem ha.1, fun x hx => by
    rw [show x⁻¹ * a⁻¹ * x = (x⁻¹ * a * x)⁻¹ by group]
    exact S.L1.inv_mem (ha.2 x hx)⟩

private theorem he42ke_mem_R (S : HeSetup G) (r : G) :
    r ∈ he42ke_R S ↔ r ∈ S.L ∧ ∀ x ∈ S.L, x⁻¹ * r * x ∈ S.L1 := Iff.rfl

private theorem he42ke_R_le_L1 (S : HeSetup G) : he42ke_R S ≤ S.L1 := by
  intro r hr
  have h := ((he42ke_mem_R S r).mp hr).2 1 S.L.one_mem
  simpa using h

private theorem he42ke_R_normal (S : HeSetup G) {l r : G} (hl : l ∈ S.L) (hr : r ∈ he42ke_R S) :
    l * r * l⁻¹ ∈ he42ke_R S := by
  obtain ⟨hrL, hrx⟩ := (he42ke_mem_R S r).mp hr
  refine (he42ke_mem_R S _).mpr ⟨S.L.mul_mem (S.L.mul_mem hl hrL) (S.L.inv_mem hl), fun x hx => ?_⟩
  have h := hrx (l⁻¹ * x) (S.L.mul_mem (S.L.inv_mem hl) hx)
  rwa [show x⁻¹ * (l * r * l⁻¹) * x = (l⁻¹ * x)⁻¹ * r * (l⁻¹ * x) by group]

theorem HeSetup.stepKer (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) (hSp : S.StepSpread)
    (hU : S.StepUniq) : S.StepKer := by
  unfold HeSetup.StepKer
  intro g hg hgx
  suffices hRB : he42ke_R S ≤ S.B from hRB ((he42ke_mem_R S g).mpr ⟨hg, hgx⟩)
  have hL1L : S.L1 ≤ S.L := le_sup_left
  have hL2L : S.L2 ≤ S.L := le_sup_right
  obtain ⟨g₀, hg₀2, hg₀1⟩ : ∃ g₀ ∈ S.L2, g₀ ∉ S.L1 := by
    by_contra hcon
    push Not at hcon
    have hle : S.L2 ≤ S.K := by
      rw [← hB.L1_inf_L2]
      exact le_inf (fun g h => hcon g h) le_rfl
    have hc := Subgroup.card_le_of_le hle
    rw [hB.card_L2, hB.card_K] at hc
    omega
  have hRK : he42ke_R S ≤ S.K := by
    intro r hr
    have hr1 : r ∈ S.L1 := he42ke_R_le_L1 S hr
    have hr2 : r ∈ S.L2 := by
      have hl : g₀⁻¹ * r * g₀ ∈ S.L1 := ((he42ke_mem_R S r).mp hr).2 g₀ (hL2L hg₀2)
      exact hU r hr1 g₀ hg₀2 hg₀1 (g₀⁻¹ * r * g₀) hl g₀ hg₀2 (by group)
    rw [← hB.L1_inf_L2]
    exact Subgroup.mem_inf.mpr ⟨hr1, hr2⟩
  obtain ⟨⟨ψ₁, hψ₁⟩, ⟨ψ₂, hψ₂⟩⟩ := hP
  have hRA : he42ke_R S ≤ S.A :=
    he42ke_le_ker hψ₁ hRK fun l hl r hr => he42ke_R_normal S (hL1L hl) hr
  have hRA' : he42ke_R S ≤ S.A' :=
    he42ke_le_ker hψ₂ hRK fun l hl r hr => he42ke_R_normal S (hL2L hl) hr
  obtain ⟨g₁, hg₁1, hg₁K⟩ : ∃ g₁ ∈ S.L1, g₁ ∉ S.K := by
    by_contra hcon
    push Not at hcon
    have hc := Subgroup.card_le_of_le (fun g h => hcon g h : S.L1 ≤ S.K)
    rw [hB.card_L1, hB.card_K] at hc
    omega
  intro r hr
  have hrZ : r ∈ S.Z := Subgroup.mem_inf.mpr ⟨hRA hr, hRA' hr⟩
  have hc : g₁ * r * g₁⁻¹ ∈ he42ke_R S := he42ke_R_normal S (hL1L hg₁1) hr
  exact hSp.1 g₁ hg₁1 hg₁K r hrZ (Subgroup.mem_inf.mpr ⟨hRA hc, hRA' hc⟩)

end CFSG.Quasithin.A94.He42
