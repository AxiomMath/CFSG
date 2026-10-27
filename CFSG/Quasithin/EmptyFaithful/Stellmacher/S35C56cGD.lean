module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cG
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cGC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cMB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cMD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim5b (hS : Sit H M S) (_hI : CaseI H M) : S35.Claim5b H M := by
  intro β l δ E F B hβ hl hlδ hδ hnE hnF hVE hEF hFW hO hZ hBV hBn hBL
  have hA := hS.glob.amalg
  have hq := quot_stab_five hA hβ
  have hl' : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hlδ' : δ ∈ nbrs l := Std.mem_nbrs_symm.mp hlδ
  have hvδ : vtype δ = false := (Std.vtype_eq_of_nbrs hlδ' hl').trans hβ
  have hWQ : Wb β ≤ pCoreOf 2 (stab β) := Std.Wb_le_Qv hS β
  have hXW : stab β ≤ Subgroup.normalizer (Wb β : Set G) := Std.Wb_normal β
  have hQX : pCoreOf 2 (stab β) ≤ stab β := pCoreOf_le 2 _
  have hLX : oTwoRes (stab β) ≤ stab β := oTwoRes_le _
  have hδW : Vn δ ≤ Wb β :=
    Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨l, hl, hlδ', hδ⟩)
  by_contra hBF
  obtain ⟨b, hbB, hbF⟩ := IsConcreteLE.not_le_iff_exists.mp hBF
  have hbW : b ∈ Wb β := hδW (hBV hbB)
  have hbX : b ∈ stab β := hQX (hWQ hbW)
  have hbL : ∀ x ∈ oTwoRes (stab β), x * b * x⁻¹ * b⁻¹ ∈ F := by
    intro x hx
    apply hBL
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hx hbB
  have hQl : Qv l ≤ stab β := Std.Qv_le_stab hS hl'
  have hQlδ : Qv l ≤ stab δ := Std.Qv_le_stab hS hlδ'
  have hEU : E ≤ E ⊔ (B ⊓ F) := le_sup_left
  have hUF : E ⊔ (B ⊓ F) ≤ F := sup_le hEF inf_le_right
  have hFX : F ≤ stab β := fun y hy => hQX (hWQ (hFW hy))
  have hBF_N : B ⊓ F ≤ Subgroup.normalizer (E : Set G) := fun y hy => hnE (hFX hy.2)
  have hc : ∀ a ∈ Qv l ⊓ Qv δ, ∀ u ∈ E ⊔ (B ⊓ F), a * u * a⁻¹ * u⁻¹ ∈ E := by
    intro a ha u hu
    obtain ⟨e, he, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBF_N).mp hu
    have hcomm : a * y * a⁻¹ * y⁻¹ ∈ E := by
      have h1 : y * a * y⁻¹ * a⁻¹ ∈ ⁅Vn δ, Qv δ⁆ :=
        Subgroup.commutator_mem_commutator (hBV hy.1) ha.2
      rw [Std.comm_Vn_Qv hS hvδ] at h1
      have h2 : a * y * a⁻¹ * y⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
      rw [h2]
      exact E.inv_mem (hVE (Std.Zv_le_Vn hl (Std.Zv_le_Zv_of_nbr hS hvδ hlδ h1)))
    have hae : a * e * a⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hnE (hQl ha.1)) e).mp he
    have e1 : a * (e * y) * a⁻¹ * (e * y)⁻¹ = (a * e * a⁻¹) * (a * y * a⁻¹ * y⁻¹) * e⁻¹ := by
      group
    rw [e1]
    exact E.mul_mem (E.mul_mem hae hcomm) (E.inv_mem he)
  have hAY : Qv l ≤ Subgroup.normalizer ((Qv l ⊓ Qv δ : Subgroup G) : Set G) :=
    le_normalizer_inf (fun x hx => le_normalizer_pCoreOf 2 (stab l) (pCoreOf_le 2 _ hx))
      (fun x hx => le_normalizer_pCoreOf 2 (stab δ) (hQlδ hx))
  have hsyl : IsSylowTwoOf (Qv l ⊔ pCoreOf 2 (stab β)) (stab β) := by
    have e : stab β ⊓ stab l = Qv l ⊔ pCoreOf 2 (stab β) := by
      rw [Std.stab_inf_eq hS hβ hl, sup_comm]
      rfl
    rw [← e]
    exact sylow_stab_inf_left hA hl
  have hUi : E.relIndex (E ⊔ (B ⊓ F)) ≤ 4 :=
    relIndex_le_four hq hO hQl inf_le_left hAY hsyl (not_inf_Qv_le hS hβ hl hlδ hδ) hEU hUF hc
  have hbQ := comm_mem_of_bound hq hO hEF hbL (Y := Qv l) hEU hUF hUi
    (fun x hx hxY => by
      have hxb : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hBn hxY) b).mp hbB
      have hmem : x * b * x⁻¹ * b⁻¹ ∈ B := B.mul_mem hxb (B.inv_mem hbB)
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hmem, hbL x hx.1⟩))
    (fun x hx t ht hxY htY => by
      have h2 := Std.relIndex_Qv hS hβ hl
      have := exists_mul_of_relIndex_two h2 ht.2 hx.2 (fun h => htY h.2) (fun h => hxY h.2)
      exact this.2)
  obtain ⟨f, hf, hfix⟩ := exists_fixed_mod hq hO hEF hbX hbL hbQ
  have hb'W : b * f ∈ Wb β := (Wb β).mul_mem hbW (hFW hf)
  have hb'F : b * f ∉ F := fun h => hbF (by simpa using F.mul_mem h (F.inv_mem hf))
  have hENW : Wb β ≤ Subgroup.normalizer (E : Set G) := fun y hy => hnE (hQX (hWQ hy))
  let D : Subgroup G := fixSecIn (oTwoRes (stab β)) E (Wb β)
  have hD : ∀ w, w ∈ D ↔ w ∈ Wb β ∧ ∀ a ∈ oTwoRes (stab β), a * w * a⁻¹ * w⁻¹ ∈ E :=
    fun w => mem_fixSecIn_iff hENW
  have hDstep : ∀ g ∈ stab β, ∀ w ∈ D, g * w * g⁻¹ ∈ D := by
    intro g hg w hw
    obtain ⟨hwW, hwc⟩ := (hD w).mp hw
    refine (hD _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXW hg) w).mp hwW, fun a ha => ?_⟩
    have hga : g⁻¹ * a * g ∈ oTwoRes (stab β) := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (stab β)
        ((stab β).inv_mem hg)) a).mp ha
      simpa using this
    have h1 := hwc _ hga
    have e : a * (g * w * g⁻¹) * a⁻¹ * (g * w * g⁻¹)⁻¹ =
        g * ((g⁻¹ * a * g) * w * (g⁻¹ * a * g)⁻¹ * w⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hnE hg) _).mp h1
  have hXD : stab β ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hDstep g hg w, fun hw => ?_⟩
    have := hDstep g⁻¹ ((stab β).inv_mem hg) _ hw
    simpa [mul_assoc] using this
  have hDW : D ≤ Wb β := fun w hw => ((hD w).mp hw).1
  have hb'D : b * f ∈ D := (hD _).mpr ⟨hb'W, hfix⟩
  have hne : ¬ D ≤ E := fun h => hb'F (hEF (h hb'D))
  have hsyl' := sylow_stab_inf_left hA hl
  have hgen : ∀ x ∈ stab β, ∃ a ∈ oTwoRes (stab β), ∃ p ∈ stab β ⊓ stab l, x = a * p := by
    intro x hx
    have hx' := le_oTwoRes_sup_of_isSylowTwoOf hsyl' hx
    exact (F1.mem_sup_iff_exists_mul_of_normalizes
      (fun p (hp : p ∈ stab β ⊓ stab l) => le_normalizer_oTwoRes (stab β) hp.1)).mp hx'
  obtain ⟨d, hdD, hdE, hd⟩ := exists_central_mod hnE hXD (fun w hw => hENW (hDW hw))
    inf_le_left hsyl'.2.1 (IsPGroup.to_le (pCoreOf_isPGroup 2 (stab β)) (hDW.trans hWQ)) hLX
    hgen hne
    (fun a ha w hw => ((hD w).mp hw).2 a ha)
  exact hdE (hZ d (hDW hdD) hd)

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
