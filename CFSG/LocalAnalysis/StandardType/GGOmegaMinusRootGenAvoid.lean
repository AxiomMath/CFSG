module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11C3D4
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11RootGen
import CFSG.LocalAnalysis.StandardType.GGSpRootGenAvoid
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenConj
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenGen
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenEichler

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative
open CFSG.Open CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticPilot

theorem ggTorusRootGenAvoidKG_statedOmegaMinus
    {K : Type} [Field K] [Finite K]
    {n m p : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 3 ≤ m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusRootGenAvoidKG p m (StatedOmega (StatedQuadMinus (m + 1) K b c))
      (Set.range (MulAut.conj : StatedOmega (StatedQuadMinus (m + 1) K b c) →*
        MulAut (StatedOmega (StatedQuadMinus (m + 1) K b c)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have : CharP K 2 := charP_two_of_card hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hshort : ∀ i j : Fin m, i ≠ j →
      (OmegaPilot.siegelBlockGL K (Equiv.swap i j).support).map
        (F4Pilot.coordEmbedGL (kOmMEmb m) kOmMEmb_injective) = omMinusShortBlock K i j := by
    intro i j hij
    rw [Equiv.Perm.support_swap hij]
    rfl
  have hW₁ : ∀ l : Fin m, ∃ w : StatedOmega (StatedQuadMinus (m + 1) K b c),
      (w : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ∈ omMinusLongBlock K b c l ∧
        ∀ x, w * omMinusTorus b c hζ x * w⁻¹ = omMinusTorus b c hζ (sgnAut l x) := by
    intro l
    obtain ⟨w, hw, hwx⟩ := exists_sgn_mem_omMinusLongBlock hirr hζ l
    exact ⟨⟨w, omMinusLongBlock_le hirr l hw⟩, hw, fun x => Subtype.ext (hwx x)⟩
  have hW₂ : ∀ σ : {σ : Equiv.Perm (Fin m) // σ.IsSwap},
      ∃ w : StatedOmega (StatedQuadMinus (m + 1) K b c),
        (w : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ∈
          (OmegaPilot.siegelBlockGL K σ.1.support).map
            (F4Pilot.coordEmbedGL (kOmMEmb m) kOmMEmb_injective) ∧
        ∀ x, w * omMinusTorus b c hζ x * w⁻¹ = omMinusTorus b c hζ (permAut σ.1 x) := by
    intro σ
    obtain ⟨i, j, hij, hσ⟩ := σ.2
    obtain ⟨w, hw, hwx⟩ := exists_swap_mem_omMinusShortBlock hζ i j
    refine ⟨⟨w, omMinusShortBlock_le h4 hij hw⟩, ?_, fun x => Subtype.ext ?_⟩
    · rw [hσ, hshort i j hij]
      exact hw
    · rw [hσ]
      exact hwx x
  choose w₁ hw₁ hw₁' using hW₁
  choose w₂ hw₂ hw₂' using hW₂
  have hτ : Function.Injective (omMinusTorus b c hζ :
      (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadMinus (m + 1) K b c)) := by
    intro x y h
    apply omMinusTorusGL_injective hζ hζo
    simpa only [coe_omMinusTorus] using congrArg Subtype.val h
  have hinj : ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* StatedOmega (StatedQuadMinus (m + 1) K b c)), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Function.Injective ψ := by
    intro L' _ _ ψ hψ hker hperf
    have h := rMinus_injective_of_cover hK hn hm hirr L'
      ((rMinusEquivStatedOmega K m b c).symm.toMonoidHom.comp ψ)
      ((rMinusEquivStatedOmega K m b c).symm.surjective.comp hψ)
      (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl)) hperf
    exact fun x y hxy => h (congrArg (rMinusEquivStatedOmega K m b c).symm hxy)
  have htop : ∀ X : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c)),
      StatedOmega (StatedQuadMinus (m + 1) K b c) ≤
        X.map (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype → X = ⊤ := by
    intro X hX
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hX x.2
    have hxy : y = x := Subtype.ext hyx
    rwa [← hxy]
  let S : Fin m ⊕ {σ : Equiv.Perm (Fin m) // σ.IsSwap} →
      Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c)) :=
    Sum.elim
      (fun l => (omMinusLongBlock K b c l).subgroupOf
        (StatedOmega (StatedQuadMinus (m + 1) K b c)))
      fun σ => ((OmegaPilot.siegelBlockGL K σ.1.support).map
        (F4Pilot.coordEmbedGL (kOmMEmb m) kOmMEmb_injective)).subgroupOf
          (StatedOmega (StatedQuadMinus (m + 1) K b c))
  have hS₂ : ∀ i j : Fin m, ∀ hij : i ≠ j,
      S (Sum.inr ⟨Equiv.swap i j, i, j, hij, rfl⟩) =
        (omMinusShortBlock K i j).subgroupOf (StatedOmega (StatedQuadMinus (m + 1) K b c)) := by
    intro i j hij
    show ((OmegaPilot.siegelBlockGL K (Equiv.swap i j).support).map
        (F4Pilot.coordEmbedGL (kOmMEmb m) kOmMEmb_injective)).subgroupOf
          (StatedOmega (StatedQuadMinus (m + 1) K b c)) =
      (omMinusShortBlock K i j).subgroupOf (StatedOmega (StatedQuadMinus (m + 1) K b c))
    rw [hshort i j hij]
  have : Nonempty (Fin m ⊕ {σ : Equiv.Perm (Fin m) // σ.IsSwap}) := ⟨Sum.inl ⟨0, by omega⟩⟩
  refine ggTorusRootGenAvoidKG_of_torusModel (ι := Fin m ⊕ {σ : Equiv.Perm (Fin m) // σ.IsSwap})
    hp hinj (center_statedOmega_quadMinus_eq_bot (by omega) hirr) (fun _ h => h)
    (omMinusTorus b c hζ) hτ
    (fun E hE hr _ => exists_mulEquiv_eq_map_omMinusTorus hp2 hirr hζ hζo hE hr)
    (Sum.elim w₁ w₂) (Sum.elim (fun i => sgnAut i) fun σ => permAut σ.1) S
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rintro (l | σ) x
    · exact hw₁' l x
    · exact hw₂' σ x
  ·
    rintro (i | ⟨σ, a, a', haa, rfl⟩)
    · change sgnAut i * sgnAut i = 1
      rw [← sq]
      exact sgnAut_sq i
    · change permAut (Equiv.swap a a') * permAut (Equiv.swap a a') = 1
      rw [← sq]
      exact permAut_swap_sq a a'
  ·
    rintro (i | ⟨σ, a, a', haa, rfl⟩)
    · exact card_fix_sgnAut hp hp2 i
    · exact card_fix_permAut_swap hp hp2 haa
  ·
    have hg1 : (ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := fun h => by
      have h1 := congrArg toAdd h
      rw [toAdd_ofAdd, toAdd_one] at h1
      exact one_ne_zero h1
    have hginv : (ofAdd (1 : ZMod p))⁻¹ ≠ ofAdd (1 : ZMod p) := fun h => by
      have h1 := congrArg toAdd h
      rw [toAdd_inv, toAdd_ofAdd] at h1
      exact ZMod.neg_one_ne_one h1
    have hsgn : ∀ i k : Fin m, sgnAut i (Pi.mulSingle k (ofAdd (1 : ZMod p))) k =
        if k = i then (ofAdd (1 : ZMod p))⁻¹ else ofAdd (1 : ZMod p) := by
      intro i k
      rw [sgnAut_apply]
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self, Pi.mulSingle_eq_same, if_pos rfl]
        rfl
      · rw [Function.update_of_ne hki, Pi.mulSingle_eq_same, if_neg hki]
    have hsp : ∀ (i : Fin m) (σ : Equiv.Perm (Fin m)), sgnAut i ≠
        (permAut σ : MulAut (Fin m → Multiplicative (ZMod p))) := by
      intro i σ h
      have h1 := congrFun (congrArg (fun φ : MulAut (Fin m → Multiplicative (ZMod p)) =>
        φ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) h) i
      rw [hsgn, if_pos rfl, permAut_mulSingle, Pi.mulSingle_apply] at h1
      split_ifs at h1
      · exact hginv h1
      · exact hg1 (inv_eq_one.mp h1)
    rintro (i | ⟨σ, hσ⟩) (i' | ⟨σ', hσ'⟩) h
    · change sgnAut i = sgnAut i' at h
      have h1 := congrFun (congrArg (fun φ : MulAut (Fin m → Multiplicative (ZMod p)) =>
        φ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) h) i
      rw [hsgn, hsgn, if_pos rfl] at h1
      by_cases hii : i = i'
      · rw [hii]
      · rw [if_neg hii] at h1
        exact absurd h1 hginv
    · exact absurd h (hsp i σ')
    · exact absurd h.symm (hsp i' σ)
    · change permAut σ = permAut σ' at h
      have hσσ : σ = σ' := Equiv.ext fun k => by
        have h1 := congrArg (fun φ : MulAut (Fin m → Multiplicative (ZMod p)) =>
          φ (Pi.mulSingle k (ofAdd (1 : ZMod p)))) h
        simp only [permAut_mulSingle] at h1
        exact (mulSingle_ofAdd_eq_iff one_ne_zero h1).1
      subst hσσ
      rfl
  ·
    rintro (l | σ)
    · exact Subgroup.mem_subgroupOf.mpr (hw₁ l)
    · exact Subgroup.mem_subgroupOf.mpr (hw₂ σ)
  ·
    rintro (l | ⟨σ, i, j, hij, rfl⟩)
    · exact isComponentOf_omMinusLongBlock h4 hirr hp hp2 hζ hζo l
    · have h := isComponentOf_omMinusShortBlock h4 hirr hp hp2 hζ hζo hij
      rw [← hshort i j hij] at h
      exact h
  ·
    rintro (l | ⟨σ, i, j, hij, rfl⟩)
    · exact dvd_card_omMinusLongBlock hirr hpq l
    · have h := dvd_card_omMinusShortBlock (b := b) (c := c) h4 hpq hij
      rw [← hshort i j hij] at h
      exact h
  ·
    intro j₀
    apply htop
    have hmemL : ∀ l : Fin m, Sum.inl l ≠ j₀ → ∀ g ∈ omMinusLongBlock K b c l,
        g ∈ (⨆ (x) (_ : x ≠ j₀), S x).map
          (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype :=
      fun l hl g hg => ⟨⟨g, omMinusLongBlock_le hirr l hg⟩,
        Subgroup.mem_iSup_of_mem (Sum.inl l)
          (Subgroup.mem_iSup_of_mem hl (Subgroup.mem_subgroupOf.mpr hg)), rfl⟩
    have hmemS : ∀ i j : Fin m, ∀ hij : i ≠ j,
        (Sum.inr ⟨Equiv.swap i j, i, j, hij, rfl⟩ :
          Fin m ⊕ {σ : Equiv.Perm (Fin m) // σ.IsSwap}) ≠ j₀ →
        ∀ g ∈ omMinusShortBlock K i j,
          g ∈ (⨆ (x) (_ : x ≠ j₀), S x).map
            (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype := by
      intro i j hij hne g hg
      have hgS : (⟨g, omMinusShortBlock_le h4 hij hg⟩ :
          StatedOmega (StatedQuadMinus (m + 1) K b c)) ∈
            S (Sum.inr ⟨Equiv.swap i j, i, j, hij, rfl⟩) := by
        rw [hS₂ i j hij]
        exact Subgroup.mem_subgroupOf.mpr hg
      exact ⟨_, Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hne hgS), rfl⟩
    have k₁ : Fin m := ⟨0, by omega⟩
    rcases j₀ with l | ⟨σ₀, a, a', haa, rfl⟩
    · obtain ⟨k₀, hk₀, -⟩ := SymplecticPilot.exists_ne_ne_of_three_le hm l l
      exact statedOmega_quadMinus_le_of_eichler hirr (by omega)
        (fun i j hij t => hmemS i j hij Sum.inr_ne_inl _
          (eichler_root_mem_omMinusShortBlock (b := b) (c := c) hij t)) k₀
        (fun u w hu hw => hmemL k₀ (fun h => hk₀ (Sum.inl_injective h)) _
          (eichler_plane_mem_omMinusLongBlock hirr k₀ hu hw))
    · refine statedOmega_quadMinus_le_of_eichler_avoid hirr hm haa
        (fun i j hij hne t => hmemS i j hij (fun h => hne ?_) _
          (eichler_root_mem_omMinusShortBlock (b := b) (c := c) hij t)) k₁
        (fun u w hu hw => hmemL k₁ Sum.inl_ne_inr _
          (eichler_plane_mem_omMinusLongBlock hirr k₁ hu hw))
      have h' : Equiv.swap i j = Equiv.swap a a' := congrArg Subtype.val (Sum.inr_injective h)
      rw [← Equiv.Perm.support_swap hij, ← Equiv.Perm.support_swap haa, h']

theorem ggTorusRootGenAvoidKG_omegaMinus
    {K : Type} [Field K] [Finite K]
    {n m p : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 3 ≤ m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusRootGenAvoidKG p m (OrthRest.RMinus K m b c)
      (LargeEvenInnSet (OrthRest.RMinus K m b c)) := by
  have : CharP K 2 := charP_two_of_card hK
  refine ggTorusRootGenAvoidKG_of_mulEquiv (rMinusEquivStatedOmega K m b c) (fun φ hφ => ?_)
    (ggTorusRootGenAvoidKG_statedOmegaMinus hK hn hm hp hp2 hpq hirr)
  obtain ⟨x, rfl⟩ := hφ
  refine ⟨rMinusEquivStatedOmega K m b c x, MulEquiv.ext fun y => ?_⟩
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem largeEvenLabelAll_rootGenAvoidKG_omegaMinus
    {p l n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) (hn : 2 ≤ n) (hl : 4 ≤ l) :
    LargeEvenLabelAll ⟨.twD, l, n⟩ fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  refine largeEvenLabelAll_omegaMinus rfl hl fun K _ _ _ hK b c hirr => ?_
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨l - 1, TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq (by omega) b c,
    ggTorusRootGenAvoidKG_omegaMinus hK hn (by omega) hp hp2 hpq hirr⟩

theorem ggRootGenKGAvoidOn_c3d4Seven :
    GGRootGenKGAvoidOn GGLabC3D4Seven := by
  rintro p lab hp hp2 - ⟨hlab | hlab, rfl⟩ <;> subst hlab
  · exact SpAvoid.largeEvenLabelAll_rootGenAvoidKG_symplectic (Or.inr rfl) hp hp2
      (by norm_num) (by norm_num) le_rfl
  · exact largeEvenLabelAll_rootGenAvoidKG_omegaMinus hp hp2 (by norm_num) (by norm_num) le_rfl

theorem ggCorFiveTwentyA11RootGenC3D4Input_holds :
    GGCorFiveTwentyA11RootGenC3D4Input :=
  ggCorFiveTwentyA11CfgRootGenNbrInputOn_of_row ggRootGenKGAvoidOn_c3d4Seven

end CFSG.StandardType

end
