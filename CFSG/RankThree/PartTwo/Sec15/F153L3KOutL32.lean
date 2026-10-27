module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutRed
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42SL3Base
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Factor
public import CFSG.Adapters.RankThreeOutcomesReverse

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7Sec
  CFSG.LocalAnalysis.ComponentInitial

theorem noOuterIrr_L32
    {Y : Type} [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1))) :
    NoOuterIrrFFOffender Y := by
  classical
  intro W _ _ hW L E hq hirr ⟨e⟩ hN hne hel hquad hEL h4
  by_contra hcon
  have hEboff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  have hV' : ∀ w : W, w * w = 1 := hW
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    Family.odd_card_center_of_irreducible hV' hirr.2
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 1 :=
    CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL (n := 3) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_refl 1, by norm_num, by simp, by simp⟩ (e.trans hY.some)
  obtain ⟨F, iF, iFin, φ₀, hFc, hcov⟩ := X7Sec.exists_cover_of_model hq.1 hodd (le_refl 1) hmodel
  haveI : Fintype F := Fintype.ofFinite F
  have hF2 : Fintype.card F = 2 := by
    rw [Fintype.card_eq_nat_card]
    simpa using hFc
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [← hcov.map_scalars, LinearFlag.scalars_eq_center, B42L2.center_sl3_eq_bot hF2,
      Subgroup.map_bot]
  obtain ⟨eL⟩ := B42L2.exists_gl32_of_model hZ hmodel
  obtain ⟨S, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hV'
  haveI : Nontrivial W := hirr.1
  haveI : Nontrivial S := (θ.toEquiv.trans Multiplicative.toAdd).symm.nontrivial
  let ι : MulAut W ≃* (Module.End (ZMod 2) S)ˣ :=
    (binPsi θ).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S).symm
  have hι : ∀ (g : MulAut W) (u : S),
      ((ι g : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) u = binPsi θ g u := by
    intro g u
    have h1 := LinearMap.congr_fun
      (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (R := ZMod 2) (M := S)
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S).symm (binPsi θ g))) u
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  set Yg : Subgroup (Module.End (ZMod 2) S)ˣ := L.map ι.toMonoidHom with hYg
  set A : Subgroup (Module.End (ZMod 2) S)ˣ := E.map ι.toMonoidHom with hAdef
  let eY : ↥Yg ≃* CFSG.QuasithinUnique.Setup.Family.GL32 :=
    (MulEquiv.subgroupMap ι L).symm.trans eL
  have hirr' : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Yg ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    refine B42L2.irr_map θ hirr.2 N ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h1 := hN (ι l) (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hl)) u hu
    rwa [hι] at h1
  have hAN : A ≤ Subgroup.normalizer (Yg : Set (Module.End (ZMod 2) S)ˣ) := by
    have h1 := Subgroup.map_mono (f := ι.toMonoidHom) hN
    refine h1.trans ?_
    rw [Subgroup.map_equiv_normalizer_eq L ι]
  have hA1 : A ≠ ⊥ := by
    rw [Ne, hAdef, Subgroup.map_eq_bot_iff_of_injective E ι.injective]
    exact hne
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    show ι g * ι g' = ι g' * ι g
    rw [← map_mul, ← map_mul, hel.1 g hg g' hg']
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    show (ι g) ^ 2 = 1
    rw [← map_pow, hel.2 g hg, map_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥A := Finite.of_equiv ↥E (MulEquiv.subgroupMap ι E).toEquiv
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 a a.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hAcard : Nat.card ↥A = Nat.card ↥E := by
    rw [hAdef, Subgroup.card_map_of_injective ι.injective]
  have hfix : Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub A) = Nat.card ↥(fixV E) := by
    rw [← B42SL3.card_fix_map θ E]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun u => ?_))
    constructor
    · intro hu a ha
      obtain ⟨g, hg, rfl⟩ := ha
      have h1 := hu (ι g) (Subgroup.mem_map_of_mem _ hg)
      rwa [hι] at h1
    · intro hu a ha
      obtain ⟨g, hg, rfl⟩ := ha
      exact (hι g u).trans (hu _ (Subgroup.mem_map_of_mem _ hg))
  have hcost : Module.finrank (ZMod 2) S ≤
      m + Module.finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A) := by
    have h1 : Nat.card S = Nat.card W := (Layer.Actor.natCard_eq θ).symm
    have h2 : 2 ^ Module.finrank (ZMod 2) S ≤
        2 ^ (m + Module.finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A)) := by
      rw [pow_add, ← Quasithin.H13.NQTerm.card_eq_two_pow_finrank, ← hm,
        ← Quasithin.H13.NQTerm.card_eq_two_pow_finrank, hfix, hAcard, h1]
      exact hEboff
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  obtain ⟨hAY, -⟩ := HardMathSupport.Meierfrankenfeld.AGL81.I542.l32_factor hirr' hAN eY hA1 hAc hA2
    hm hcost
  have hall : ∀ g ∈ E, g = 1 := by
    intro g hg
    obtain ⟨l, hl, hlg⟩ := hAY (Subgroup.mem_map_of_mem ι.toMonoidHom hg)
    have hgl : l = g := ι.injective hlg
    have hmem : g ∈ E ⊓ L := Subgroup.mem_inf.2 ⟨hg, hgl ▸ hl⟩
    rw [hEL] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact hne (eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (hall g hg))

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out
