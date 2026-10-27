module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xn
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B69E22Pre
public import CFSG.Quasithin.Background.B69Final
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.Quasithin.Background.B69Lift
public import CFSG.Quasithin.Background.B69Mod
public import CFSG.Quasithin.Background.B69Simple
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s

variable {G : Type} [Group G] [Finite G]

namespace P22s

theorem mem_normalizer_omegaZJ22 {P : Subgroup G} {g : G} (hg : g ∈ normalizer (P : Set G)) :
    g ∈ normalizer (omegaZJ22 P : Set G) := by
  have key : ∀ y ∈ normalizer (P : Set G), ∀ z ∈ omegaZJ22 P, y * z * y⁻¹ ∈ omegaZJ22 P := by
    intro y hy
    have hJ : ∀ y ∈ normalizer (P : Set G), ∀ x ∈ jOf P, y * x * y⁻¹ ∈ jOf P := fun y hy =>
      uc22p22e_conj_jOf fun x hx => (mem_normalizer_iff.1 hy x).1 (uc22p22e_jOf_le_self P hx)
    exact uc22p22e_conj_omegaZJ (hJ y hy) fun x hx => by
      simpa using hJ y⁻¹ (inv_mem hy) x hx
  exact le_normalizer_of_conj (K := normalizer (P : Set G)) key hg

end P22s

theorem uc22p22sk_proofEiHat_ne (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i j : Fin m} (hij : i ≠ j) :
    proofEiHat D (preN D (Nb i)) ≠ proofEiHat D (preN D (Nb j)) := by
  intro heq
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbar
  set Q : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (jOf D.T) with hQdef
  set W : Submodule (ZMod 2) Umod := commOn ρ Q (natIi ρ Nbar (Nb i)) with hW
  set C : Submodule (ZMod 2) Umod := natC ρ Nbar with hC
  have hQN : Q ≤ Nbar := mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hWj : W = commOn ρ Q (natIi ρ Nbar (Nb j)) := by
    rw [hW, ← bsub_proofEiHat D e ρ hc (d.le i), ← bsub_proofEiHat D e ρ hc (d.le j), heq]
  obtain ⟨y₀, hy₀W, hy₀I, hy₀C⟩ : ∃ y₀ ∈ W, y₀ ∈ natIi ρ Nbar (Nb i) ∧ y₀ ∉ C := by
    obtain ⟨A', hA'max, hne⟩ := NatDec.exists_isMax_proj_ne_bot D d i
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hbQ : (b : MBar D.M D.U) ∈ d.proj i Q :=
      d.proj_mono i (mbarImage_mono D.M D.U (le_jOf_of_isMax hA'max)) b.2
    have hbN : (b : MBar D.M D.U) ∈ Nb i := d.proj_le i _ b.2
    have hb1' : (b : MBar D.M D.U) ≠ 1 := fun h => hb1 (Subtype.ext h)
    by_contra hall
    push Not at hall
    apply hb1'
    refine d.faithful_modC (d.le i hbN) fun k y hy => ?_
    by_cases hki : k = i
    · subst hki
      obtain ⟨a, ha, hay⟩ := d.exists_act_of_proj k hbQ hy
      have hyW : ρ a y - y ∈ W := sub_mem_commOn ha hy
      have hyI : ρ a y - y ∈ natIi ρ Nbar (Nb k) :=
        (natIi ρ Nbar (Nb k)).sub_mem (d.inv_Ii (hQN ha) k y hy) hy
      rw [← hay]
      exact hall _ hyW hyI
    · rw [d.lemma21 (Ne.symm hki) hbN hy, sub_self]
      exact C.zero_mem
  have hy₀Ij : y₀ ∈ natIi ρ Nbar (Nb j) := by
    rw [hWj] at hy₀W
    exact commOn_le_of_invariant (fun b hb v hv => d.inv_Ii (hQN hb) j v hv) hy₀W
  exact hy₀C (d.sum.2 i ⟨Submodule.mem_sup_left hy₀I,
    Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Ne.symm hij) hy₀Ij))⟩)

theorem uc22p22sk_preN_eq (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (hm : m ≤ 1) (i : Fin m) : preN D (Nb i) = proofN D := by
  have hNbi : Nb i = mbarImage D.M D.U (proofN D) := by
    rw [← hNb.1.1]
    apply le_antisymm (le_iSup Nb i)
    refine iSup_le fun j => ?_
    have : j = i := Fin.ext (by omega)
    rw [this]
  rw [hNbi]
  refine le_antisymm (uc22p22v_preN_le D _) fun x hx => ⟨hx, ?_⟩
  have hxM : x ∈ D.M := uc22p22e_jOf_le_self D.M hx
  exact ⟨⟨x, hxM⟩, ⟨⟨x, hxM⟩, hx, rfl⟩, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
