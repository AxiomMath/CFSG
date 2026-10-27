module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitEmbed
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusLift_of_injective_adjointF4 {k R : Type} [Field k] [Finite k] [CharP k 2]
    [Group R] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card k - 1)
    (ι : CFSG.Blueprint.Chevalley.adjointGroup .F4 k →* R) (hι : Function.Injective ι) :
    GGTorusLift p 4 R := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := CFSG.StandardType.TableBSymp.exists_orderOf_eq_of_dvd (K := k) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hdet : IsUnit ((CFSG.Blueprint.Chevalley.Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [CFSG.LieType.Chevalley.det_cartan_F4, Int.cast_one]
    exact isUnit_one
  obtain ⟨U, hU, hU2, hTU⟩ :=
    CFSG.StandardType.TableBF4.exists_rootGroup_normalized_F4 (K := k) ζ hζ
  set e : Multiplicative (Fin CFSG.Blueprint.Chevalley.Tag.F4.rank → ZMod p) →* R :=
    ι.comp (CFSG.RankThree.CentralCover.chevTorus .F4 ζ hζ) with he
  set n : Fin CFSG.Blueprint.Chevalley.Tag.F4.rank → R :=
    fun i => ι ⟨CFSG.Blueprint.Chevalley.weylElt .F4 k i 1,
      CFSG.Blueprint.Chevalley.weylElt_mem_adjointGroup i 1⟩ with hn_def
  have hn : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ =
      e (.ofAdd (v - CFSG.RankThree.CentralCover.cartanFunctional .F4 p i v •
        Pi.single i 1)) := by
    intro i v
    rw [he, hn_def, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg ι (CFSG.RankThree.CentralCover.weylElt_conj_chevTorus ζ hζ i v)
  have hUb : U.map ι ≠ ⊥ := fun h => hU ((Subgroup.map_eq_bot_iff_of_injective U hι).mp h)
  have hU2b : IsPGroup 2 (U.map ι) := hU2.map ι
  have hTUb : ∀ v, ∀ u ∈ U.map ι, e v * u * (e v)⁻¹ ∈ U.map ι := by
    intro v u hu
    obtain ⟨u', hu', rfl⟩ := (Subgroup.mem_map (f := ι) (K := U)).mp hu
    rw [he, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem ι (hTU v u' hu')
  exact CFSG.StandardType.TableBF4.ggTorusLift_of_reflections
    (d := CFSG.Blueprint.Chevalley.Tag.F4.rank) hp hp2 e
    (hι.comp (CFSG.RankThree.CentralCover.chevTorus_injective (τ := .F4) hζo hζ hdet))
    (CFSG.RankThree.CentralCover.cartanFunctional .F4 p)
    (fun i => CFSG.RankThree.CentralCover.cartanFunctional_single i)
    n hn hUb hU2b hTUb

section Main

theorem ggTorusLift_twE6Dvd_holds {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusLift p 4 (TwE6Delta.RecipeR K n) := by
  obtain ⟨k, hfield, hfinite, hchar, ι, hk, hι⟩ := exists_injective_f4_recipeR hn hK
  letI : Field k := hfield
  letI : Finite k := hfinite
  letI : CharP k 2 := hchar
  have hpq : p ∣ Nat.card k - 1 := by
    rw [hk]
    exact hpn
  exact ggTorusLift_of_injective_adjointF4 hp hp2 hpq ι hι

end Main

end CFSG.StandardType

end
