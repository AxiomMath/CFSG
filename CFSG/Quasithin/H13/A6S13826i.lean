module

public import CFSG.Quasithin.H13.A6S13826h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

theorem relIndex_le_of_inf_le {G : Type} [Group G] [Finite G] {C C' X Y : Subgroup G}
    (hYX : Y ≤ X) (h : C ⊓ Y ≤ C') : C'.relIndex Y ≤ C.relIndex X := by
  calc C'.relIndex Y ≤ (C ⊓ Y).relIndex Y :=
        Subgroup.relIndex_le_of_le_left h (relIndex_ne_zero' _ _)
    _ = C.relIndex Y := Subgroup.inf_relIndex_right C Y
    _ ≤ C.relIndex X := Subgroup.relIndex_le_of_le_right hYX (relIndex_ne_zero' _ _)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace D826

variable {H K : Subgroup G} (hd : S.D826 H K)
include hd

theorem relIndex_DH_le_two (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ'))
    (hle : F8.Uγ V H (g : G) ≤ F8.Uγ S.V3 H (g : G) ⊔ pCoreOf 2 H) :
    (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) ≤ 2 := by
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have hUγH : F8.Uγ S.V3 H (g : G) ≤ H := hF.Uγ_le_H s
  have hUγQ : F8.Uγ S.V3 H (g : G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hUγH.trans (le_normalizer_pCoreOf 2 H)
  have heq : ⁅conjClosure S.V3 H, F8.Uγ S.V3 H (g : G)⁆ ⊔ fsuV1 T V =
      ⁅conjClosure S.V3 H, F8.Uγ V H (g : G)⁆ ⊔ fsuV1 T V := by
    refine le_antisymm (sup_le_sup_right (Subgroup.commutator_mono le_rfl hF.Uγ_le_Vγ) _) ?_
    refine sup_le ?_ le_sup_right
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hx' : x ∈ ((F8.Uγ S.V3 H (g : G) ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hle hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUγQ] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hx'
    have huq : u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V := by
      have := (fsuV1 T V).inv_mem (hF1.commutator_mem_V₁ hq hu)
      have e : (q * u * q⁻¹ * u⁻¹)⁻¹ = u * q * u⁻¹ * q⁻¹ := by group
      rwa [e] at this
    have hc := hF1.conj_eq_of_mem_V₁ (hUγH ha) huq
    have e : ⁅u, a * q⁆ = ⁅u, a⁆ * (a * (u * q * u⁻¹ * q⁻¹) * a⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [e, hc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu ha))
      (Subgroup.mem_sup_right huq)
  obtain ⟨-, hle2, -⟩ := S.comm_le_Uγ_sup_V1_of_gen hd.hS.hNS h13315 h1356two hd.hH hF h13314 s
    le_rfl hgen heq
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF.V₁_ne_bot
  have hV1z : ∀ w ∈ fsuV1 T V, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hF.card_V₁
    have hz' : (⟨z, hz⟩ : ↥(fsuV1 T V)) = y := huniq _ hz1
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      have hw' : (⟨w, hw⟩ : ↥(fsuV1 T V)) = y :=
        huniq _ (fun e => hw1 (by simpa using congrArg Subtype.val e))
      exact congrArg Subtype.val (hw'.trans hz'.symm)
  have hstab := S.stab_γ_eq hF s
  have hUH : conjClosure S.V3 H ≤ conjSub (g : G) H := by
    rw [← hstab]
    exact (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans
      ((pCoreOf_le 2 _).trans inf_le_right))
  set F := conjSub (g : G)⁻¹ (conjClosure S.V3 H) with hFdef
  have hFH : F ≤ H := by
    rw [hFdef, conjSub_le_iff, inv_inv]
    exact hUH
  have hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H := by
    intro f hf
    rw [hFdef, mem_conjSub, inv_inv] at hf
    have h2 := hF.F911_3.2 _ hf
    rw [pow_two] at h2
    have e : f * f = (g : G)⁻¹ * (((g : G) * f * (g : G)⁻¹) * ((g : G) * f * (g : G)⁻¹)) *
        (g : G) := by group
    rw [e, h2]
    have e1 : (g : G)⁻¹ * 1 * (g : G) = 1 := by group
    rw [e1]
    exact (pCoreOf 2 H).one_mem
  have hzF : ∀ f ∈ F, ∀ y ∈ conjClosure V H, f * y * f⁻¹ * y⁻¹ ∈ conjClosure S.V3 H ∨
      f * y * f⁻¹ * y⁻¹ * ((g : G)⁻¹ * z * (g : G))⁻¹ ∈ conjClosure S.V3 H := by
    intro f hf y hy
    rw [hFdef, mem_conjSub, inv_inv] at hf
    set u := (g : G) * f * (g : G)⁻¹ with hu
    have hfu : f = (g : G)⁻¹ * u * (g : G) := by rw [hu]; group
    rw [hfu]
    have hy' : (g : G) * y * (g : G)⁻¹ ∈ F8.Uγ V H (g : G) := by
      rw [F8.Uγ]; exact mul_mem_conjSub hy
    have h1 := hle2 (Subgroup.commutator_mem_commutator hf hy')
    rw [commutatorElement_def] at h1
    have hN : F8.Uγ S.V3 H (g : G) ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) :=
      hUγH.trans hF.H_normalizes_V₁
    have h1' : u * ((g : G) * y * (g : G)⁻¹) * u⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ ∈
        ((F8.Uγ S.V3 H (g : G) ⊔ fsuV1 T V : Subgroup G) : Set G) := h1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at h1'
    obtain ⟨a, ha, w, hw, hawe⟩ := Set.mem_mul.mp h1'
    have e₀ : ((g : G)⁻¹ * u * (g : G)) * y * ((g : G)⁻¹ * u * (g : G))⁻¹ * y⁻¹ =
        (g : G)⁻¹ * (u * ((g : G) * y * (g : G)⁻¹) * u⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹) *
          (g : G) := by group
    have ha₀ : (g : G)⁻¹ * a * (g : G) ∈ conjClosure S.V3 H := by
      have ha' : a ∈ F8.Uγ S.V3 H (g : G) := ha
      rwa [F8.Uγ, mem_conjSub] at ha'
    rcases hV1z w hw with rfl | rfl
    · left
      rw [e₀, ← hawe, mul_one]
      exact ha₀
    · right
      rw [e₀, ← hawe]
      have e₁ : (g : G)⁻¹ * (a * w) * (g : G) * ((g : G)⁻¹ * w * (g : G))⁻¹ =
          (g : G)⁻¹ * a * (g : G) := by group
      rw [e₁]
      exact ha₀
  have h2 := hd.relIndex_le_two_of_VH h13315 h1356two h13314 hαs hαk hFH hFs hzF
  have hc := F9.relIndex_conjSub (g : G) (F ⊓ pCoreOf 2 H) F
  rw [conjSub_inf, hFdef, conjSub_inv_conjSub, ← pCoreOf_conjSub, ← hstab] at hc
  have hD : F8.DH S.V3 (fsuV1 T V) H (g : G) = conjClosure S.V3 H ⊓ pCoreOf 2 (stab γ) := by
    rw [hF.pCoreOf_stab_eq_centralizerMod s]
    ext x
    simp only [F8.DH, Subgroup.mem_inf, mem_centralizerMod]
    constructor
    · rintro ⟨hx, hxN, hxc⟩
      exact ⟨hx, (hstab ▸ hUH) hx, hxN, hxc⟩
    · rintro ⟨hx, -, hxN, hxc⟩
      exact ⟨hx, hxN, hxc⟩
  rw [hD, hc]
  exact h2

end D826

end Setting4

end CFSG.Quasithin.H13.A6
