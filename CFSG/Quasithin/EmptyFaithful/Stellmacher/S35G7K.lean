module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7K2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.K

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def commIn (W Q K : Subgroup G) (hK : W ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup G where
  carrier := {w | w ∈ W ∧ ∀ q ∈ Q, ⁅w, q⁆ ∈ K}
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨mul_mem ha hb, fun q hq => ?_⟩
    have h1 := conj_mem hK ha (hcb q hq)
    have h2 := mul_mem h1 (hca q hq)
    have : ⁅a * b, q⁆ = a * ⁅b, q⁆ * a⁻¹ * ⁅a, q⁆ := by
      simp only [commutatorElement_def]; group
    rw [this]; exact h2
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨inv_mem ha, fun q hq => ?_⟩
    have h1 := conj_mem hK (inv_mem ha) (inv_mem (hca q hq))
    have : ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]; exact h1

theorem kernelStruct : KernelStruct H M S := by
  intro hS β hβ E hEn hVE hEW ho y hy hyQ h1 h2
  have hinf := inf_smul_eq hS hβ hEn hVE hEW ho hy hyQ h1 h2
  obtain ⟨l1, hl1⟩ : ∃ l1, l1 ∈ nbrs β := exists_adj β
  have hK : ∀ l ∈ nbrs β, Wl l ⊓ E = Wl l1 ⊓ E := by
    intro l hl
    obtain ⟨g, hg, hgl⟩ := stab_transitive_on_nbrs hl1 hl
    have := hinf g hg l1 hl1
    change Wl (g • l1) ⊓ E = _ at this
    rwa [hgl] at this
  have hKn : stab β ≤ Subgroup.normalizer ((Wl l1 ⊓ E : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_conjSub_eq ?_
    have hE : conjSub g E = E := conjSub_eq_of_mem_normalizer (hEn hg)
    have := hinf g hg l1 hl1
    change Wl (toHM β hg • l1) ⊓ E = _ at this
    have e : Wl (toHM β hg • l1) = conjSub g (Wl l1) := Wl_smul _ _
    rw [conjSub_inf, hE, ← e]
    exact this
  have hWX : Wb β ≤ stab β := fun w hw => pCoreOf_le 2 (stab β) (Std.Wb_le_Qv hS β hw)
  have hKW : Wb β ≤ Subgroup.normalizer ((Wl l1 ⊓ E : Subgroup G) : Set G) := fun w hw =>
    hKn (hWX hw)
  refine ⟨Wl l1 ⊓ E, hKn, le_inf (Std.Vn_le_Wl (Std.mem_nbrs_symm.mp hl1)) hVE, inf_le_right,
    fun l hl => ⟨by rw [← hK l hl]; exact inf_le_left, hK l hl⟩, ?_⟩
  have hD : ∀ l ∈ nbrs β, Wl l ≤ commIn (Wb β) (Qv β) (Wl l1 ⊓ E) hKW := by
    intro l hl w hw
    refine ⟨Wl_le_Wb hS hβ hl hw, fun q hq => ?_⟩
    rw [← hK l hl]
    refine ⟨?_, ?_⟩
    · have hq' : q ∈ stab l := Std.Qv_le_stab hS hl hq
      have := mul_mem hw (conj_mem (Std.Wl_normal l) hq' (inv_mem hw))
      have e : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]; exact this
    · have := inv_mem (Qv_comm_mem hS hβ hEn ho q hq w (Wl_le_Wb hS hβ hl hw))
      have e : ⁅w, q⁆ = (q * w * q⁻¹ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]; exact this
  have hW : Wb β ≤ commIn (Wb β) (Qv β) (Wl l1 ⊓ E) hKW := by
    exact (Std.Wb_eq_iSup_Wl hS hβ).le.trans (iSup₂_le hD)
  intro w hw q hq
  exact (hW hw).2 q hq

end S35.G7.K

end F53.Stellmacher

end CFSG.Quasithin
