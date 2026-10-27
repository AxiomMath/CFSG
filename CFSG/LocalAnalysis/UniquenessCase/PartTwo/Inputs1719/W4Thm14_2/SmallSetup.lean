module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutPowerMap
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGF2Rep417Diag.Cover
import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped MatrixGroups Matrix

theorem exists_rep_of_isSL3
    {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {X L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥) {e : ℕ} (hS : IsSL3 ↥L e)
    (hX : Even (Nat.card ↥X)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (U : Type) (_ : AddCommGroup U)
      (_ : Module (ZMod 2) U) (_ : Finite U) (θ : I ≃* Multiplicative U) (φ : SL(3, F) →* ↥L)
      (ρ : Representation (ZMod 2) SL(3, F) U),
      Fintype.card F = 2 ^ e ∧ X7Sec.Cover φ ∧ Odd (Nat.card φ.ker) ∧
      (∀ g u, ρ g u = Layer.binPsi θ ((φ g : ↥L) : MulAut I) u) ∧ ρ.IsIrreducible ∧
      (∀ y ∈ Subgroup.normalizer (L : Set (MulAut I)), ∀ s : SL(3, F),
        ∃ s' : SL(3, F), X7a.Intertwines ρ (Layer.binPsi θ y) s s') ∧
      ∃ t ∈ X, t * t = 1 ∧ t ≠ 1 ∧
        Module.finrank (ZMod 2) (LinearMap.range ((Layer.binPsi θ t).toLinearMap - 1)) =
          E3.mParam X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  obtain ⟨hq, hL3⟩ := hS
  obtain ⟨U, hUadd, hUmod, hUfin, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary (V := I)
      (fun v => by simpa [pow_two] using hI v)
  letI : AddCommGroup U := hUadd
  letI : Module (ZMod 2) U := hUmod
  letI : Finite U := hUfin
  have hirrSub : (subRep θ L).IsIrreducible := subRep_isIrreducible θ le_rfl hirr
  have hpCore : CFSG.pCore 2 ↥L = ⊥ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible 2
      (subRep θ L) (subRep_injective θ L) hirrSub
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥L)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.GF2Rep417Diag.odd_card_center_of_pCore_eq_bot hpCore
  obtain ⟨K, hKf, hKfin, hKchar, eK, α, hcardK, hαsurj, hαker, hαscal⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_cover_of_odd_center
      (Y := ↥L) hq hL3 hoddZ
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  letI : Fintype K := Fintype.ofFinite K
  let ρ : Representation (ZMod 2) SL(3, K) U := (subRep θ L).comp α
  have hρapply : ∀ g u, ρ g u = Layer.binPsi θ ((α g : ↥L) : MulAut I) u := fun g u => rfl
  have hρirr : ρ.IsIrreducible := by
    have hiff := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).1 hirrSub
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨hiff.1, fun W hW => hiff.2 W ?_⟩
    intro x u hu
    obtain ⟨g, rfl⟩ := hαsurj x
    exact hW g u hu
  have hinter : ∀ y ∈ Subgroup.normalizer (L : Set (MulAut I)), ∀ s : SL(3, K),
      ∃ s' : SL(3, K),
        X7a.Intertwines ρ (Layer.binPsi θ y) s s' := by
    intro y hy s
    have hconj : y * ((α s : ↥L) : MulAut I) * y⁻¹ ∈ L :=
      ((Subgroup.mem_normalizer_iff).1 hy ((α s : ↥L) : MulAut I)).1 (α s).2
    obtain ⟨s', hs'⟩ := hαsurj ⟨y * ((α s : ↥L) : MulAut I) * y⁻¹, hconj⟩
    have hval : ((α s' : ↥L) : MulAut I) = y * ((α s : ↥L) : MulAut I) * y⁻¹ := by
      simpa using congrArg (fun x : ↥L => (x : MulAut I)) hs'
    refine ⟨s', fun u => ?_⟩
    calc
      Layer.binPsi θ y (ρ s u) =
          Layer.binPsi θ (y * ((α s : ↥L) : MulAut I)) u := by
        rw [hρapply, map_mul, LinearEquiv.mul_apply]
      _ = Layer.binPsi θ (((α s' : ↥L) : MulAut I) * y) u := by
        rw [show y * ((α s : ↥L) : MulAut I) =
          ((α s' : ↥L) : MulAut I) * y by rw [hval]; group]
      _ = Layer.binPsi θ ((α s' : ↥L) : MulAut I) (Layer.binPsi θ y u) := by
        rw [map_mul, LinearEquiv.mul_apply]
  obtain ⟨t, htX, htord, htval⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hX
  have ht2 : t * t = 1 := by
    have h : t ^ 2 = 1 := by rw [← htord, pow_orderOf_eq_one]
    simpa [pow_two] using h
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    omega
  have htrank : Module.finrank (ZMod 2)
      (LinearMap.range ((Layer.binPsi θ t).toLinearMap - 1)) = E3.mParam X := by
    rw [← htval]
    change Module.finrank (ZMod 2)
        (LinearMap.range ((Layer.binPsi θ t).toLinearMap - 1)) =
      padicValNat 2 (fixV (Subgroup.zpowers t)).index
    rw [CFSG.Quasithin.B45Sz.index_fixV_zpowers_eq θ t, padicValNat.prime_pow]
  refine ⟨K, hKf, Fintype.ofFinite K, hKchar, U, hUadd, hUmod, hUfin, θ, α, ρ,
    ?_, ⟨hαsurj, hαker, hαscal⟩, ?_, hρapply, hρirr, hinter, ⟨t, htX, ht2, htne, htrank⟩⟩
  · rw [← Nat.card_eq_fintype_card]
    exact hcardK
  · exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.odd_card_ker_of_le_scalars
      (K := K) (n := 3) (by norm_num) hαker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
