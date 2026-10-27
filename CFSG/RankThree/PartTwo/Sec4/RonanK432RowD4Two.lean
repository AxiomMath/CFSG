module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Refine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import CFSG.Quasithin.Recognition.CertD4Bridge
public import Certificates.Certificate428004

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Quasithin CFSG.AGLEmbedding.D4Two
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.RankThree.PartTwo.Sec4.Item434D42

set_option linter.unusedSectionVars false

attribute [local irreducible] d4GenA d4GenB

theorem d4WitData_gens_mem :
    ∀ k < d4WitData.gens.size, permOfArr d4WitData.n d4WitData.gens[k]! ∈ d4P := by
  intro k hk
  have hk2 : k < 2 := by simpa [d4WitData] using hk
  interval_cases k
  · show d4A ∈ d4P
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · show d4B ∈ d4P
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem d4WitData_pOrd : d4WitData.pOrd = 3 ^ 4 := rfl

theorem listRow_d4P :
    ListRow ↥d4P := by
  haveI : Finite ↥d4P := Nat.finite_of_card_ne_zero (by rw [card_d4P]; norm_num)
  obtain ⟨P, hPG, hPcard, hP⟩ := Certificates.certificate428004.apply
    d4P d4P d4WitData_gens_mem d4WitData_gens_mem
  refine listRow_of_wit3_sub (le_refl d4P) ?_
  exact wit3_all_of_sylow_sub d4P d4P P (le_refl _)
    (fun g hg y hy => d4P.mul_mem (d4P.mul_mem hg hy) (d4P.inv_mem hg)) hPG 4
    (hPcard.trans d4WitData_pOrd) (by rw [card_d4P]; decide) hP

theorem listRow_of_equiv_trialityGroup8
    {Y : Type} [Group Y] [Finite Y]
    (φ : Y ≃* trialityGroup8) (hY : Nat.card Y = 211341312) : ListRow Y := by
  let e : Y ≃* lineGroup := φ.trans (MulEquiv.subgroupCongr lineGroup_eq.symm)
  have hX : Nat.card lineGroup = 211341312 := by rw [← Nat.card_congr e.toEquiv, hY]
  have hinj : Function.Injective (d4Rho.comp e.toMonoidHom) :=
    (d4Rho_injective hX).comp e.injective
  let f : Y →* d4P := (d4Rho.comp e.toMonoidHom).codRestrict d4P (fun y => d4Rho_mem _)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · intro y
      have hy : (y : Equiv.Perm (Fin 2457)) ∈ d4Rho.range := by
        rw [d4Rho_range]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      obtain ⟨u, rfl⟩ := e.surjective x
      exact ⟨u, Subtype.ext hx⟩
  exact ListRow.of_mulEquiv (MulEquiv.ofBijective f hf).symm listRow_d4P

section Bridge


theorem listRowOf_trialityD4_two (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) (hq1 : q.exponent = 1) :
    ListRowOf (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro S _ _ _ _ ⟨e⟩
  have hm : ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide) e⟩
  rw [hq2, hq1] at hm
  have hcard : Nat.card S = 211341312 := by
    rw [Timmesfeld.card_chevalleyExceptionalModel_two hm]
    norm_num [CFSG.Open.ordTrialityD4]
  have hL : LieModel S .trialityD4 0 2 1 :=
    CFSG.RankThree.PartOne.Sec66T.lieModel_trialityD4_iff.mpr ⟨rfl, hm⟩
  obtain ⟨e2⟩ := trialityD4ModelBridge_of_lieModel _ hL
  have hk8 : Nat.card GF8 = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  obtain ⟨e3⟩ := d4bG8_equiv_quasithin GF8 hk8
  exact listRow_of_equiv_trialityGroup8 (e2.trans e3.symm) hcard

end Bridge

end CFSG.RankThree.PartTwo.Sec4.RonanK432
