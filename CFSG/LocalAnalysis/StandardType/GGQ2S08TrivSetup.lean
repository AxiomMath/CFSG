module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTrivial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

private noncomputable def ggQ2s08t1a_X {G : Type} [Group G] (p : ℕ) (u : G)
    (J : Subgroup G) : Subgroup G :=
  ggLayerClosure p (Subgroup.centralizer ({u} : Set G)) J

theorem ggQ2s08_triv_setup (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) {u : ↥Bs} (hu : (u : G) ∈ D)
    (hu1 : u ≠ 1) (htr : GGTrivialLine p B x D J u) :
    ∃ X : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X ∧
      J ≤ X ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ⁅X, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p X ∧
      ∀ b ∈ Bs, ⁅X, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p X →
        b ∈ Subgroup.centralizer (J : Set G) := by
  have hI : GGThmIHyp p B x L := hS.1.1.1
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hHyp : GGCorFiveTwentyHyp p B Bs x L D J := hS.1
  have hprime : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hprime⟩
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  have hPU : GGPumpupInput := ggPumpupInput_of_lBalance hLB
  have hSstar : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hSstar.2.1
  have hxp : x ^ p = 1 := hSstar.1.1.2 x hxB
  have hBle : B ≤ Bs := hBstar.1
  have huBs : (u : G) ∈ Bs := hBle (hDJ.1.1 hu)
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hHyp.2.2.1.1
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hBsC hBle hDJ.1 hBsL
  have hux : (u : G) ∉ Subgroup.zpowers x := by
    intro huz
    apply htr.1
    have hxu : x ∈ Subgroup.zpowers (u : G) :=
      mem_zpowers_of_mem_zpowers_of_ne_one hprime hxp huz (by simpa using hu1)
    exact le_antisymm (Subgroup.zpowers_le.mpr huz) (Subgroup.zpowers_le.mpr hxu)
  have hD : D = Subgroup.closure {x, (u : G)} := eq_closure_pair_of_mem hI hDJ hu hux
  have hpump := pumpup_of_stdSub (hPU := hPU) hI hDJ hpJ hD
  have hXcomp : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G))
      (ggQ2s08t1a_X p (u : G) J) := hpump.1
  have hJX : J ≤ ggQ2s08t1a_X p (u : G) J := hpump.2.1
  have hxNX : x ∈ Subgroup.normalizer (ggQ2s08t1a_X p (u : G) J : Set G) := hpump.2.2.1
  have hxc : (⁅ggQ2s08t1a_X p (u : G) J, Subgroup.zpowers x⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (ggQ2s08t1a_X p (u : G) J) := by
    rcases hpump.2.2.2 with h | h
    · exact absurd ⟨(u : G), ggQ2s08t1a_X p (u : G) J, h, rfl⟩ htr.2
    · exact h
  have hBsN : Bs ≤ Subgroup.normalizer (ggQ2s08t1a_X p (u : G) J : Set G) := by
    refine GGDichotomy.le_normalizer_of_pComponent (d := (u : G)) ?_ hXcomp hJX hJJ hpJ hBsJ
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hBsC b hb (u : G) huBs
  have hbJall : ∀ b ∈ Bs, (⁅ggQ2s08t1a_X p (u : G) J, Subgroup.zpowers b⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (ggQ2s08t1a_X p (u : G) J) →
      b ∈ Subgroup.centralizer (J : Set G) := by
    intro b hb hbO
    have hOcop : Nat.Coprime p
        (Nat.card (LargeEvenPPrimeCoreOf p (ggQ2s08t1a_X p (u : G) J))) := by
      rw [LargeEvenPPrimeCoreOf,
        Subgroup.card_map_of_injective (ggQ2s08t1a_X p (u : G) J).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact mem_centralizer_of_commutator_le_coprime hprime hDJ.1.2.2.2.2.2.1.2.2 hpJ hOcop
      (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJX hj)))
      (hBsJ hb) ((Subgroup.commutator_mono hJX le_rfl).trans hbO)
  exact ⟨ggQ2s08t1a_X p (u : G) J, hXcomp, hJX, hBsN, hxc, hbJall⟩

end CFSG.StandardType

end
