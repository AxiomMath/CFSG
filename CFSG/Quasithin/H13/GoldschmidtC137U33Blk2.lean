module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Blk1
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Vol2.Ch12Sec4G2Off

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
include h

theorem isG2Block_h13 (hG : CFSG.Quasithin.IsG2Block L)
    (hnat : G2NaturalDerived (autI h.hVe L) ⊤ (fixV (autI h.hVe L)) 1)
    (hcomm : commV (autI h.hVe L) = ⊤) : H13.IsG2Block L := by
  have hshort : IsShort2 L := hG.1
  have hLU := le_normalizer_blockU L
  have hQ : blockU L ≤ blockQ L ⊓ centralizer (blockQ L : Set G) := hshort.2.2.1.1
  have hcomm' : IsMulCommutative ↥(blockU L) := ⟨⟨fun a b => Subtype.ext
    ((Subgroup.mem_centralizer_iff.1 (hQ a.2).2 b (hQ b.2).1).symm)⟩⟩
  obtain ⟨K, hKf, hKfin, hK, hR⟩ := hnat
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : CharP K 2 := charP_two_of_natCard_two hK2
  obtain ⟨π, hπ⟩ := hR
  have hπ' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia (autI h.hVe L)
      (commV (autI h.hVe L)) (fixV (autI h.hVe L) ⊓ commV (autI h.hVe L)) π := by
    rw [hcomm, inf_top_eq]
    exact hπ
  have hVU : ⁅V, L⁆ ≤ blockU L := by
    rw [h.hVL]
    exact h.V_le_blockU
  have hU : blockU L = ⁅V, L⁆ ⊔ blockZ L := by
    rw [h.hVL]
    exact h.blockU_eq_sup hshort
  obtain ⟨β, hβs, hβk, hβe⟩ := C124.exists_blockHom h.hVe h.hLN hVU hU _ π hπ'
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ
  have hσs := C124.starHom_surjective h.hVe h.hLN
  have hker := C124.ker_starHom_eq_pCore h.hVe h.hLN h.hkerL
  refine ⟨hshort, ⟨K, hKf, hKfin, hK2, ⟨?_⟩⟩, hcomm', K, hKf, hKfin, hK, ?_⟩
  · exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hσs)).trans
      (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  · set φ := A6.autOnHom hLU with hφdef
    have hφs : Function.Surjective φ := A6.autOnHom_surjective hLU
    have hφv : ∀ (l : ↥L) (u : ↥(blockU L)),
        (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = l * u * (l : G)⁻¹ :=
      fun l u => conjAct_val _ _ _
    have hφk : (C124.starHom h.hVe L h.hLN).ker ≤ φ.ker := by
      intro l hl
      rw [hker] at hl
      rw [MonoidHom.mem_ker]
      refine Subtype.ext (MulEquiv.ext fun u => Subtype.ext ?_)
      show (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = (u : G)
      rw [hφv]
      have hlQ : (l : G) ∈ blockQ L := (mem_pCoreOf_iff_gc L l).2 hl
      have h1 := Subgroup.mem_centralizer_iff.1 (hQ u.2).2 l hlQ
      calc (l : G) * u * (l : G)⁻¹ = u * l * (l : G)⁻¹ := by rw [h1]
        _ = u := by group
    let eσ := QuotientGroup.quotientKerEquivOfSurjective (C124.starHom h.hVe L h.hLN) hσs
    let ψ : ↥(autI h.hVe L) →* ↥(autOn L (blockU L)) :=
      (QuotientGroup.lift (C124.starHom h.hVe L h.hLN).ker φ hφk).comp eσ.symm.toMonoidHom
    have hψ : ∀ l : ↥L, ψ (C124.starHom h.hVe L h.hLN l) = φ l := fun l => by
      have h1 : eσ (QuotientGroup.mk l) = C124.starHom h.hVe L h.hLN l := rfl
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← h1, MulEquiv.symm_apply_apply]
      rfl
    have hψs : Function.Surjective ψ := fun y => by
      obtain ⟨l, rfl⟩ := hφs y
      exact ⟨C124.starHom h.hVe L h.hLN l, hψ l⟩
    obtain ⟨hπsurj, -, hkersec, -, -, hsec, hkerinv, -⟩ := hπ'
    refine ⟨ψ.comp π, hψs.comp hπsurj, le_top, hkersec, fun _ _ _ => Subgroup.mem_top _, ?_,
      hsec, hkerinv, ?_⟩
    · intro h' z hz
      obtain ⟨l, rfl⟩ := hφs h'
      have hzc : (z : G) ∈ centralizer (L : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hz)).2
      have h1 := Subgroup.mem_centralizer_iff.1 hzc l l.2
      have h2 : (φ l : MulAut ↥(blockU L)) z = z := Subtype.ext (by
        rw [hφv]
        calc (l : G) * z * (l : G)⁻¹ = z * l * (l : G)⁻¹ := by rw [h1]
          _ = z := by group)
      rw [h2]
      exact hz
    · let τ : ↥(⊤ : Subgroup ↥(blockU L)) ≃* ↥(blockU L) := Subgroup.topEquiv
      refine ⟨β.comp τ.toMonoidHom,
        (hβs.comp τ.surjective : Function.Surjective (β.comp τ.toMonoidHom)), ?_, ?_⟩
      · intro u
        show β (τ u) = 1 ↔ _
        rw [← MonoidHom.mem_ker, hβk]
        rfl
      · intro γ u m hu hm hum
        obtain ⟨ℓ, hℓ⟩ := hσs (π γ)
        have h1 : (ψ.comp π) γ = φ ℓ := by
          rw [MonoidHom.comp_apply, ← hℓ, hψ]
        show β ((((ψ.comp π) γ : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) (τ u)) = _
        rw [h1]
        exact hβe ℓ γ hℓ.symm (τ u) (((φ ℓ : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) (τ u))
          m hm (hφv ℓ _) hum

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
