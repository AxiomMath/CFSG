module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Q7Moved

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem step72Split_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ∀ r : G, Sec7A hc t r →
      ∀ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ∀ α ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB B,
      ∀ β ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup r B),
        β ∉ Vt M (LB M Q B) B Z t →
      ∀ c ∈ Vt M (LB M Q B) B Z t,
        α * β * c ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) →
      (∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
          y ∈ Subgroup.normalizer (conjSubgroup g (Vt M (LB M Q B) B Z t) : Set G) ∧
          ⁅β, y⁆ ∉ Z) →
      conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs r hr g hg hgN α hα β hβ hβV c hcV hv hy
  obtain ⟨y, hyP, hyN, hβy⟩ := hy
  rcases sec7Q7Kernel_of_inputs h34 hRoot G M Q Z B hc n t hs g hg hgN with hK | hVeq
  swap
  · exact hVeq
  exfalso
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hyCN : y ∈ hc.CN t := hyP.2
  have hyL : y ∈ LB M Q (conjSubgroup r B) := hyP.1
  have hyR : y ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hyCN).1
  have hyM : y ∈ M := hc.Rt_le_M t hyR
  have hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z := (Ctx.mem_CN.mp hyCN).2
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  have hWQ : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), w ∈ Q := fun w hw => hw.1
  have hWcent : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ∀ v ∈ Vt M (LB M Q B) B Z t,
      w * v * w⁻¹ = v := fun w hw v hv => by
    have := Subgroup.mem_centralizer_iff.mp hw.2 v hv
    rw [← this]
    group
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := by
    intro x hx
    have hb : r⁻¹ * x * r ∈ B := mem_conjSubgroup.mp hx
    have hbV : r⁻¹ * x * r ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr.mem)
      (r⁻¹ * x * r)).mp hbV
    have e : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rwa [e] at h1
  have hBle : conjSubgroup y B ≤ B ⊔ Z := by
    intro x hx
    have hb : y⁻¹ * x * y ∈ B := mem_conjSubgroup.mp hx
    have hbV : y⁻¹ * x * y ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
    have e : x = ⁅y, y⁻¹ * x * y⁆ * (y⁻¹ * x * y) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hyV _ hbV)) (Subgroup.mem_sup_left hb)
  have hPres : ∀ q ∈ Q ⊓ QB B, y * q * y⁻¹ ∈ Q ⊓ QB B :=
    fun q hq => hc.conj_mem_inf_QB_of_le_sup_Z hyM hBle hq
  have hyα : ⁅y, α⁆ ∈ QB B := by
    rw [commutatorElement_def]
    exact (QB B).mul_mem (hPres α ⟨hWQ α hα.1, hα.2⟩).2 ((QB B).inv_mem hα.2)
  have hyαV : ⁅y, α⁆ ∈ Vt M (LB M Q B) B Z t := hWN y hyCN α hα.1
  have hyβ : ⁅y, β⁆ ∈ conjSubgroup r B ⊔ Z :=
    (hc.conj_of_mem hrM).comm_mem_sup_Z_of_mem_LB hyL ⟨hWQ β hβ.1, hβ.2⟩
  have hyβV : ⁅y, β⁆ ∈ Vt M (LB M Q B) B Z t :=
    (sup_le hCV sec39_Z_le_Vt) hyβ
  have hyc : ⁅y, c⁆ ∈ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt (hyV c hcV)
  have hαβW : α * β ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem hα.1 hβ.1
  have hexp : ⁅y, α * β * c⁆ = ⁅y, α⁆ * ⁅y, β⁆ * ⁅y, c⁆ := by
    rw [comm_mul_right_expand, comm_mul_right_expand, hWcent α hα.1 _ hyβV,
      hWcent (α * β) hαβW _ hyc]
  have hvV : ⁅y, α * β * c⁆ ∈ Vt M (LB M Q B) B Z t := by
    rw [hexp]
    exact (Vt M (LB M Q B) B Z t).mul_mem
      ((Vt M (LB M Q B) B Z t).mul_mem hyαV hyβV) hyc
  have hvg : ⁅y, α * β * c⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [commutatorElement_def]
    exact (conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hyN _).mp hv)
      ((conjSubgroup g (Vt M (LB M Q B) B Z t)).inv_mem hv)
  have hK' : ⁅y, α * β * c⁆ ∈ QB B := hK (Subgroup.mem_inf.mpr ⟨hvV, hvg⟩)
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hβQB : ⁅y, β⁆ ∈ QB B := by
    have e : ⁅y, β⁆ = ⁅y, α⁆⁻¹ * ⁅y, α * β * c⁆ * ⁅y, c⁆⁻¹ := by
      rw [hexp]
      group
    rw [e]
    exact (QB B).mul_mem ((QB B).mul_mem ((QB B).inv_mem hyα) hK')
      ((QB B).inv_mem (hZQB (hyV c hcV)))
  have hfin : ⁅y, β⁆ ∈ Z :=
    sec7_conj_sup_inf_QB_le_Z h34 hRoot hc hs hr.mem hr.plane
      (Subgroup.mem_inf.mpr ⟨hyβ, Subgroup.mem_inf.mpr ⟨hyβV, hβQB⟩⟩)
  apply hβy
  rw [← commutatorElement_inv]
  exact Z.inv_mem hfin

end CFSG.RankThree.GF2n.Stroth80
