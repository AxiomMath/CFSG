module

public import CFSG.Quasithin.Vol2.KGFactL52Mod10
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.KGC31

@[expose] def J4L5BlockNotSelfDual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B : Subgroup G), IsSporadic .J4 ↥K → B ≤ K →
    IsShort2 B → IsExt ↥B (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y) →
    SingerNoConj G B (pCoreOf 2 B)

theorem singerNoConj_of_quot {G : Type} [Group G] {L₁ L V : Subgroup G} (h1 : L₁ ≤ L)
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) (ι : ModO2 L₁ ≃* ModO2 L)
    (hι : ∀ x : ↥L₁, ι (x : ModO2 L₁) = (Subgroup.inclusion h1 x : ModO2 L))
    (hNC : SingerNoConj G L₁ V) : SingerNoConj G L V := by
  intro v hv hvV hLE e y hy U hU
  have hLE₁ : L₁ ≤ eNorm hv := h1.trans hLE
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk_surjective (ι.symm (y : ModO2 L))
  have hy₁' : (y₁ : ModO2 L₁) = (ι.trans e).symm singer5 := by
    rw [hy₁, MulEquiv.symm_trans_apply, ← hy]
  have hyo : (Subgroup.inclusion h1 y₁)⁻¹ * y ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq, ← hι, hy₁, MulEquiv.apply_symm_apply]
  have hcent : ∀ o : ↥L, o ∈ CFSG.pCore 2 ↥L → eGL hv (Subgroup.inclusion hLE o) = 1 := by
    intro o ho
    apply Units.ext
    rw [eGL_coe, Units.val_one, eMat_eq_one_iff, hvV]
    exact hO ((mem_pCore_iff_mem_pCoreOf o).mp ho)
  set o : ↥L := (Subgroup.inclusion h1 y₁)⁻¹ * y with ho
  have hy_eq : y = Subgroup.inclusion h1 y₁ * o := by rw [ho, mul_inv_cancel_left]
  have hinc : ∀ x : ↥L₁, Subgroup.inclusion hLE (Subgroup.inclusion h1 x) =
      Subgroup.inclusion hLE₁ x := fun x => rfl
  have hoi : o⁻¹ ∈ CFSG.pCore 2 ↥L := Subgroup.inv_mem _ hyo
  have h2 : eGL hv (Subgroup.inclusion hLE y) = eGL hv (Subgroup.inclusion hLE₁ y₁) := by
    rw [hy_eq, map_mul, map_mul, hcent o hyo, mul_one, hinc]
  have h3 : eGL hv (Subgroup.inclusion hLE y⁻¹) = eGL hv (Subgroup.inclusion hLE₁ y₁⁻¹) := by
    rw [hy_eq, mul_inv_rev, map_mul, map_mul, hcent o⁻¹ hoi, one_mul, ← map_inv, hinc]
  exact hNC v hv hvV hLE₁ (ι.trans e) y₁ hy₁' U (by rw [← h2, ← h3]; exact hU)

end CFSG.Quasithin.H13.Ch4
