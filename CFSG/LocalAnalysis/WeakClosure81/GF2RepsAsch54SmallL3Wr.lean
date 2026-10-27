module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.GF2Type.Aschbacher1976Full.LeafBigCenterTI
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrLin
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrUni
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallAb
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallGL2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallWrGen
import CFSG.Quasithin.Background.GoldschmidtShultLink
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.KGroups.L3EpsUniSyl
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreQuaternion

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

open Subgroup

variable {Y : Type*} [Group Y]

theorem isCyclic_inf_centralizer_of_mulEquiv {T₀ : Subgroup Y} {m : ℕ} (hm : 1 ≤ m)
    (e : ↥T₀ ≃* CFSG.Open.WreathedTwoGroup m) :
    IsCyclic ↥(T₀ ⊓ centralizer (T₀ : Set Y)) := by
  have : IsCyclic (center (CFSG.Open.WreathedTwoGroup m)) :=
    CFSG.Wreathed.center_isCyclic (2 ^ m) (Nat.one_lt_two_pow (by omega))
  let f : ↥(T₀ ⊓ centralizer (T₀ : Set Y)) →* center ↥T₀ :=
    { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, mem_center_iff.2 fun y =>
        Subtype.ext ((mem_centralizer_iff.1 (mem_inf.1 x.2).2) y.1 y.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (congrArg (fun w : center ↥T₀ => ((w : ↥T₀) : Y)) h)
  exact isCyclic_of_injective ((Subgroup.centerCongr e).toMonoidHom.comp f)
    ((Subgroup.centerCongr e).injective.comp hf)

end CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.GH74.GLS.IVK (IsLnEps)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem asch54Case_l3EpsWr (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch54Case fun X _ => ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      ((r % 4 = 1 ∧ CFSG.Blueprint.LieModel X .PSL 3 r 1) ∨
        (r % 4 = 3 ∧ CFSG.Blueprint.LieModel X .PSU 3 r 1)) := by
  intro Q _ _ L T hKQ hLn hLs hLnab hC hPL _ hT _
  obtain ⟨r, hr, hr2, hcase⟩ := hPL
  have := hLn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : CFSG.Open.IsKGroup ↥L := hKQ.of_injective L.subtype L.subtype_injective
  have hcat := hKL.isCatalogGroup_of_surjective ⊤ hLnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer (hS _ hLs hLnab hcat))
  have hmem : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → ¬ HasCompFactor X IsCalL0 →
      X ≤ lGen IsCalL0 ⊤ T := fun X hTX hX hnot => le_iSup₂_of_le X ⟨hTX, hX, hnot⟩ le_rfl
  left
  have hTi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [relIndex_top_right] at h
  let S : Sylow 2 Q := hT.2.1.toSylow hTi
  obtain ⟨K, _, ⟨e⟩, hK, hLE, hwr⟩ : ∃ (K : Type) (_ : Group K), Nonempty (↥L ≃* K) ∧
      Asch80Wr.WrModel K ∧ (IsLnEps 3 ↥L 1 (r ^ 1) ∨ IsLnEps 3 ↥L (-1) (r ^ 1)) ∧
      ∀ P : Sylow 2 ↥L, ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥P ≃* CFSG.Open.WreathedTwoGroup m) := by
    rcases hcase with ⟨hr4, h⟩ | ⟨hr4, h⟩
    · have hq4 : r ^ 1 % 4 = 1 := by rwa [pow_one]
      have hst := h.statedClassicalModel (by decide)
      obtain ⟨F, _, _, hF, he⟩ := CFSG.GH74.KGroups.L3Eps.exists_projectiveSL_equiv hst
      obtain ⟨⟨-, -, -⟩, F', iF', hfin', hF', he'⟩ := hst
      have hLn' : IsLnEps 3 ↥L 1 (r ^ 1) := Or.inl ⟨rfl, F', iF', hfin', hF', he'⟩
      exact ⟨_, _, he, Asch80Wr.wrModel_projectiveSL (by omega) (by omega), Or.inl hLn',
        fun P => CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_wr hr hr2 hLn' hq4
          (by rw [pow_one]; exact hr.one_lt) P⟩
    · have hq4 : r ^ 1 % 4 = 3 := by rwa [pow_one]
      have hst := h.statedClassicalModel (by decide)
      obtain ⟨Fu, _, hU, he⟩ := CFSG.GH74.KGroups.L3Eps.exists_unitary_quotient_equiv hst
      obtain ⟨-, F', iF', hfin', hF', he'⟩ := hst
      have hLn' : IsLnEps 3 ↥L (-1) (r ^ 1) := Or.inr ⟨rfl, F', iF', hfin', hF', he'⟩
      exact ⟨_, _, he, Asch80Wr.wrModel_psu hU hr2 hq4, Or.inr hLn',
        fun P => CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_wr hr hr2 hLn' hq4 P⟩
  obtain ⟨hE2, A, hAT, hAc, hAi, hA1, hZ1, hNA, hgen⟩ := Asch80Wr.exists_abelian_of_model S e hK
  set T₀ := (S : Subgroup Q) ⊓ L with hT₀
  set Z := T₀ ⊓ centralizer (T₀ : Set Q) with hZ
  have hT₀syl : IsSylowIn 2 (T ⊓ L) L := CFSG.Quasithin.Shult.isSylowTwoOf_inf_normal hT
  have hT₀2 : IsPGroup 2 ↥T₀ := S.isPGroup'.to_inf_left
  have hTN : T ≤ normalizer (T₀ : Set Q) := Asch80Wr.le_normalizer_inf_of_normal
  have hlt : ∀ {C : Subgroup Q}, C ≤ T₀ → C ≠ ⊥ → normalizer (C : Set Q) < ⊤ := fun hC hC1 =>
    lt_top_iff_ne_top.2
      (Asch80Wr.normalizer_ne_top_of_le hLs hE2 (hC.trans inf_le_right) (hT₀2.to_le hC) hC1)
  have hZc : IsCyclic ↥Z := by
    obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq L S
    obtain ⟨m, hm, ⟨eP⟩⟩ := hwr P
    exact Asch80Wr.isCyclic_inf_centralizer_of_mulEquiv (by omega)
      ((MulEquiv.subgroupCongr (subgroupOf_map_subtype (S : Subgroup Q) L)).symm.trans
        ((Subgroup.equivMapOfInjective ((S : Subgroup Q).subgroupOf L) L.subtype
          L.subtype_injective).symm.trans ((MulEquiv.subgroupCongr hP.symm).trans eP)))
  obtain ⟨t, htZ, ht⟩ :=
    CFSG.ABGLocalTools.exists_mem_orderOf_eq_two (hT₀2.to_le inf_le_left) hZ1
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htT₀ : t ∈ T₀ := (mem_inf.1 htZ).1
  have hNZ : normalizer (Z : Set Q) ≤ centralizer ({t} : Set Q) :=
    CFSG.GF2Type.Aschbacher1976Full.LeafBigCenter.normalizer_le_centralizer_of_isCyclic hZc htZ ht
  have hTt : T ≤ centralizer ({t} : Set Q) :=
    hTN.trans ((Asch80Wr.normalizer_le_normalizer_inf_centralizer T₀).trans hNZ)
  have hCt : centralizer ({t} : Set Q) < ⊤ := by
    refine lt_of_le_of_lt ?_ (hlt (zpowers_le.2 htT₀) (zpowers_eq_bot.not.2 ht1))
    rw [zpowers_eq_closure, ← centralizer_closure]
    exact centralizer_le_normalizer _
  refine Asch80Wr.eq_top_of_le_of_normalizer_le (E := L) S ?_ ?_
  · refine hgen.trans (sup_le (hNZ.trans ?_) ?_)
    · exact hmem _ hTt hCt (not_hasCompFactor_centralizer_of_isLnEps
        isCalL0_nonabelian_not_sectionalTwoRankLE hq hr hr2 hLE (mem_inf.1 htT₀).2 ht2 ht1)
    · exact hmem _ (hTN.trans hNA) (hlt hAT hA1)
        (not_hasCompFactor_normalizer_of_relIndex_two isCalL0_nonabelian_not_sectionalTwoRankLE
          hq hT₀syl hAT hAc hAi)
  · exact hmem _ hTN (hlt le_rfl (ne_bot_of_le_ne_bot hZ1 inf_le_left))
      (not_hasCompFactor_normalizer_inf isCalL0_nonabelian_not_sectionalTwoRankLE hq hT₀syl)

end CFSG.LocalAnalysis.WeakClosure81

end
