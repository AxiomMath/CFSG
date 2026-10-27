module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem conjSubgroup_le_inf_cTilde (h1 : W16One G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) :
    conjSubgroup V₀ g ≤ R ⊓ (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) := by
  have hYI : conjSubgroup V₀ g ≤ conjClosure (U ⊔ V₀) H :=
    conjSubgroup_le_conjClosure_of_mem c.g_mem.1 le_sup_right
  have hIR : conjClosure (U ⊔ V₀) H ≤ R := conjClosure_le_R h1 hS c
  have hYR : conjSubgroup V₀ g ≤ R := hYI.trans hIR
  have hYC : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V := hYR.trans c.sylow.le
  have hYcent : conjSubgroup V₀ g ≤ centralizer (V₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex)
      (le_conjClosure (U ⊔ V₀) H (Subgroup.mem_sup_right hw)) (hYI hx)
  exact le_inf hYR (le_inf hYC hYcent)

theorem exists_comm_eq_of_conjSubgroup (h1 : W16One G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {v : G} (hv : v ∈ V) (hvU : v ∉ U ⊔ V₀) {w : G}
    (hw : w ∈ V₀) :
    ∃ x ∈ conjSubgroup V₀ g, x * v * x⁻¹ * v⁻¹ = w := by
  let Y : Subgroup G := conjSubgroup V₀ g
  have hYA : Y ≤ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) := by
    change conjSubgroup V₀ g ≤ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)
    exact (conjSubgroup_le_inf_cTilde h1 hS c).trans inf_le_right
  have hmem : ∀ x : ↥Y, (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ V₀ := fun x =>
    (FourteenTwo.mem_cTilde_iff_comm.1 (hYA x.2).1).2.2 v hv
  let f : ↥Y → ↥V₀ := fun x => ⟨(x : G) * v * (x : G)⁻¹ * v⁻¹, hmem x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1' : (x : G) * v * (x : G)⁻¹ * v⁻¹ = (y : G) * v * (y : G)⁻¹ * v⁻¹ :=
      congrArg Subtype.val hxy
    have h2 : (x : G) * v * (x : G)⁻¹ = (y : G) * v * (y : G)⁻¹ := by
      have := congrArg (fun t => t * v) h1'
      simpa [mul_assoc] using this
    have hz : (y : G)⁻¹ * (x : G) ∈ Y := Y.mul_mem (Y.inv_mem y.2) x.2
    have hz' : (y : G)⁻¹ * (x : G) ∈ conjSubgroup V₀ g := by
      change (y : G)⁻¹ * (x : G) ∈ Y
      exact hz
    have hzv : ((y : G)⁻¹ * (x : G)) * v * ((y : G)⁻¹ * (x : G))⁻¹ * v⁻¹ = 1 := by
      rw [show ((y : G)⁻¹ * (x : G)) * v * ((y : G)⁻¹ * (x : G))⁻¹ * v⁻¹ =
          (y : G)⁻¹ * ((x : G) * v * (x : G)⁻¹) * (y : G) * v⁻¹ by group, h2]
      group
    have hcomm : ((y : G)⁻¹ * (x : G)) * v = v * ((y : G)⁻¹ * (x : G)) := by
      calc ((y : G)⁻¹ * (x : G)) * v
          = ((y : G)⁻¹ * (x : G)) * v * ((y : G)⁻¹ * (x : G))⁻¹ * v⁻¹ *
              (v * ((y : G)⁻¹ * (x : G))) := by group
        _ = 1 * (v * ((y : G)⁻¹ * (x : G))) := by rw [hzv]
        _ = v * ((y : G)⁻¹ * (x : G)) := by group
    by_cases hz1 : (y : G)⁻¹ * (x : G) = 1
    · have hxyeq : (x : G) = (y : G) := by
        calc (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
          _ = (y : G) * 1 := by rw [hz1]
          _ = (y : G) := by group
      exact Subtype.ext hxyeq
    · exfalso
      have hv_mem : v ∈ V ⊓ centralizer ({(y : G)⁻¹ * (x : G)} : Set G) := by
        refine ⟨hv, Subgroup.mem_centralizer_iff.2 ?_⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hcomm
      rw [c.centralizer_eq ((y : G)⁻¹ * (x : G)) hz' hz1] at hv_mem
      exact hvU hv_mem
  have hcard : Nat.card ↥V₀ ≤ Nat.card ↥Y := by
    change Nat.card ↥V₀ ≤ Nat.card ↥(conjSubgroup V₀ g)
    exact (E3.card_conjSubgroup V₀ g).symm.le
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard
  obtain ⟨x, hx⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨x.1, x.2, by simpa [f] using congrArg Subtype.val hx⟩

theorem mem_of_forall_conj_mem_sup (c : Cfg1620 M V₀ V U S R H g B) {v : G} (hv : v ∈ V)
    (h : ∀ m ∈ M, m * v * m⁻¹ ∈ U ⊔ V₀) : v ∈ V₀ := by
  let W : Subgroup G := V ⊓ ⨅ m : ↥M, conjSubgroup (U ⊔ V₀) (m : G)
  have hWleV : W ≤ V := by
    change V ⊓ ⨅ m : ↥M, conjSubgroup (U ⊔ V₀) (m : G) ≤ V
    exact inf_le_left
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro m' hm' x hx
    change x ∈ V ⊓ ⨅ m : ↥M, conjSubgroup (U ⊔ V₀) (m : G) at hx
    change m' * x * m'⁻¹ ∈ V ⊓ ⨅ m : ↥M, conjSubgroup (U ⊔ V₀) (m : G)
    refine ⟨?_, ?_⟩
    · have hm'V : m' ∈ Subgroup.normalizer (V : Set G) := by
        rw [c.cex.hyp.h6.normalizer_eq]
        exact hm'
      exact (Subgroup.mem_normalizer_iff.1 hm'V x).1 hx.1
    · refine Subgroup.mem_iInf.2 fun m => ?_
      have hmem := (Subgroup.mem_iInf.1 hx.2) ⟨(m : G) * m', M.mul_mem m.2 hm'⟩
      rw [mem_conjSubgroup_iff] at hmem
      rw [mem_conjSubgroup_iff]
      rw [show (m : G) * (m' * x * m'⁻¹) * (m : G)⁻¹ =
          ((m : G) * m') * x * ((m : G) * m')⁻¹ by group]
      exact hmem
  have hWne : W ≠ V := by
    intro hWV
    have hVU : V ≤ U ⊔ V₀ := by
      intro x hx
      have hxW : x ∈ W := hWV.symm ▸ hx
      change x ∈ V ⊓ ⨅ m : ↥M, conjSubgroup (U ⊔ V₀) (m : G) at hxW
      have hx1 := (Subgroup.mem_iInf.1 hxW.2) (1 : ↥M)
      rw [mem_conjSubgroup_iff] at hx1
      simpa using hx1
    have hsup : U ⊔ V₀ = V :=
      le_antisymm (sup_le c.cex.le c.cex.hyp.h6.le) hVU
    have h1 := one_le_mQuot c
    rw [hsup, E3.mQuot_self] at h1
    omega
  have hgen : ConjGenerated M V₀ V := c.cex.hyp.h6.conjGenerated c.cex.hyp.ne_bot
  have hvW : v ∈ W := by
    change v ∈ V ⊓ ⨅ m : ↥M, conjSubgroup (U ⊔ V₀) (m : G)
    refine ⟨hv, Subgroup.mem_iInf.2 fun m => ?_⟩
    rw [mem_conjSubgroup_iff]
    exact h (m : G) m.2
  exact le_of_normalizer_of_ne_of_conjGenerated hgen hWleV hMW hWne hvW

theorem conjSubgroup_sup_eq (c : Cfg1620 M V₀ V U S R H g B) {b : G}
    (hb : b ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) :
    conjSubgroup (U ⊔ V₀) b = U ⊔ V₀ := by
  have hb_inv : b⁻¹ ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) :=
    ⟨(F11.CTilde M V₀ V).inv_mem hb.1, (centralizer (V₀ : Set G)).inv_mem hb.2⟩
  have hstep : ∀ {y : G}, y ∈ F11.CTilde M V₀ V → ∀ x ∈ U ⊔ V₀, y * x * y⁻¹ ∈ U ⊔ V₀ := by
    intro y hy x hx
    have hxV : x ∈ V := (sup_le c.cex.le c.cex.hyp.h6.le) hx
    have hcomm : y * x * y⁻¹ * x⁻¹ ∈ V₀ :=
      (FourteenTwo.mem_cTilde_iff_comm.1 hy).2.2 x hxV
    have hmem : (y * x * y⁻¹ * x⁻¹) * x ∈ U ⊔ V₀ :=
      (U ⊔ V₀).mul_mem (Subgroup.mem_sup_right hcomm) hx
    rw [show (y * x * y⁻¹ * x⁻¹) * x = y * x * y⁻¹ by group] at hmem
    exact hmem
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : b * x * b⁻¹ ∈ U ⊔ V₀ := mem_conjSubgroup_iff.1 hx
    have h := hstep hb_inv.1 (b * x * b⁻¹) hx'
    rw [show b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x by group] at h
    exact h
  · intro x hx
    rw [mem_conjSubgroup_iff]
    exact hstep hb.1 x hx

theorem inf_centralizer_conjSubgroup_L (c : Cfg1620 M V₀ V U S R H g B) {b : G}
    (hb : b ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) :
    (U ⊔ V₀) ⊓ centralizer (conjSubgroup (V ⊔ conjSubgroup V g) b : Set G) =
      conjSubgroup U b := by
  have hCL : (U ⊔ V₀) ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) = U := by
    refine le_antisymm ?_ ?_
    · calc (U ⊔ V₀) ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G)
          ≤ V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) :=
            inf_le_inf (sup_le c.cex.le c.cex.hyp.h6.le) le_rfl
        _ = U := c.centralizer_L
    · exact le_inf le_sup_left ((le_of_eq c.centralizer_L.symm).trans inf_le_right)
  have key := congrArg (fun A : Subgroup G => conjSubgroup A b) hCL
  rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, conjSubgroup_sup_eq c hb] at key
  exact key

theorem conjSubgroup_L_le_conjClosure (c : Cfg1620 M V₀ V U S R H g B) {b : G} (hb : b ∈ H) :
    conjSubgroup (V ⊔ conjSubgroup V g) b ≤ conjClosure V H := by
  intro x hx
  have hxL : b * x * b⁻¹ ∈ V ⊔ conjSubgroup V g := mem_conjSubgroup_iff.1 hx
  have hxK : b * x * b⁻¹ ∈ conjClosure V H := c.L_le_conjClosure hxL
  have hb' : b⁻¹ ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H (H.inv_mem hb)
  have h := (Subgroup.mem_normalizer_iff.1 hb' (b * x * b⁻¹)).1 hxK
  rw [show b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x by group] at h
  exact h

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
