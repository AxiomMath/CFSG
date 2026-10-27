module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FS
public import CFSG.Quasithin.Background.C134Case4Fix
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318F

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}
  {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} [IsMulCommutative ↥(vPlus L T)]

theorem not_case4Corr_ext {I : Set ℕ} (hD : FData G T M L D α) (h : Hyp331 G T M L D)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U' Z₀ : Subgroup ↥(vPlus L T)} (hU' : ∀ v : ↥(vPlus L T), v ∈ U')
    (D₀ : FLc.VModel 4 ρ U' Z₀ (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)
    (hfix : ∀ b : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)),
      (∀ g ∈ (perfectCore (FLc.QI 4 I) : Set SL4), FLc.actW g b = b) → b = 1)
    (he : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hTY : T ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 I) : Set G))
    (h4 : CFSG.Quasithin.C134CorrLocal.IsC134Case4Corr (liftCore α (FLc.QI 4 I) ⊔ T) T
      (liftCore α (FLc.QI 4 I))) : False := by
  have hT : IsSylowTwoOf T (liftCore α (FLc.QI 4 I) ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hD.hyp.sylow le_sup_right
  have hQT : c134Q (liftCore α (FLc.QI 4 I) ⊔ T) (liftCore α (FLc.QI 4 I)) ≤ T :=
    MSY.c134Q_le_pCoreOf.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT)
  obtain ⟨c, hcCQ, hc1, hcZ⟩ :=
    CFSG.Quasithin.C134Case4Fix.exists_mem h4 hT.2.1 le_sup_right hTY hQT
  have hcV : c ∈ vPlus L T := le_conjClosure _ _ hcZ
  have hc0 : (⟨c, hcV⟩ : ↥(vPlus L T)) ∈ Z₀ :=
    mem_of_fix D₀ hfix (hU' _) (fix_of_mem_centralizer h hD.surj hαv ⟨hcV, hcCQ.2⟩)
  have hcL : c ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := D₀.Zfix (α ⟨l, hl⟩) _ hc0
    rw [hαv ⟨l, hl⟩] at h1
    have h2 : l * c * l⁻¹ = c := congrArg Subtype.val h1
    calc l * c = l * c * l⁻¹ * l := by group
      _ = c * l := by rw [h2]
  have hmem : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hcZ, hcL⟩
  rw [he, Subgroup.mem_bot] at hmem
  exact hc1 hmem

end CFSG.Quasithin.H13.L3321
