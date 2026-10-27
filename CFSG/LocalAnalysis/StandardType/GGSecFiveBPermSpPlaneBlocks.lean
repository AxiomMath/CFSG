module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpPlaneBlocksTwoDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviOfComponent
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed)
open scoped MatrixGroups commutatorElement

section PlaneEmbedding

open Matrix CFSG.StandardType.SpJoin CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {F : Type} [Field F]

private theorem lam_eq_longBlock' {n : ℕ} (i : Fin n)
    (g : SpecialLinearGroup (Fin 2) F) :
    lam i g = CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock F n i g := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rfl

private theorem spEmbed_lam {m n : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (i : Fin m) (g : SpecialLinearGroup (Fin 2) F) :
    spEmbed (K := F) σ hσ (lam i g) = lam (σ i) g := by
  rw [lam_eq_longBlock' i g, CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed_longBlock]
  exact (lam_eq_longBlock' (σ i) g).symm

private noncomputable def piExtend {M : Type*} [CommMonoid M] {m n : ℕ}
    (σ : Fin m → Fin n) (hσ : Function.Injective σ) :
    (Fin m → M) →* (Fin n → M) where
  toFun w i := if h : ∃ l, σ l = i then w (Classical.choose h) else 1
  map_one' := by
    funext i
    by_cases h : ∃ l, σ l = i <;> simp [h]
  map_mul' w w' := by
    funext i
    by_cases h : ∃ l, σ l = i <;> simp [h, Pi.mul_apply]

private theorem piExtend_mulSingle {M : Type*} [CommMonoid M] {m n : ℕ}
    {σ : Fin m → Fin n} (hσ : Function.Injective σ) (l : Fin m) (a : M) :
    piExtend σ hσ (Pi.mulSingle l a) = Pi.mulSingle (σ l) a := by
  funext i
  change (if h : ∃ l', σ l' = i then
      (Pi.mulSingle (M := fun _ : Fin m => M) l a) (Classical.choose h) else 1) =
    (Pi.mulSingle (M := fun _ : Fin n => M) (σ l) a) i
  split_ifs with h
  · rw [Pi.mulSingle_apply]
    by_cases hi : i = σ l
    · have hch : Classical.choose h = l := by
        apply hσ
        rw [Classical.choose_spec h, hi]
      rw [if_pos hch, Pi.mulSingle_apply, if_pos hi]
    · have hch : Classical.choose h ≠ l := by
        intro h'
        apply hi
        rw [← Classical.choose_spec h, h']
      rw [if_neg hch, Pi.mulSingle_apply, if_neg (fun h' => hi h')]
  · rw [Pi.mulSingle_apply, if_neg]
    exact fun h' => h ⟨l, h'.symm⟩

private theorem spPlaneTorus_piExtend {p m n : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (w : Fin m → Multiplicative (ZMod p)) :
    SpJoin.spPlaneTorus n ζ (piExtend σ hσ w) =
      spEmbed (K := F) σ hσ (SpJoin.spPlaneTorus m ζ w) := by
  have hhom : (SpJoin.spPlaneTorus n ζ).comp (piExtend σ hσ) =
      (spEmbed (K := F) σ hσ).comp (SpJoin.spPlaneTorus m ζ) := by
    refine MonoidHom.pi_ext (fun l a => ?_)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, piExtend_mulSingle,
      SpJoin.spPlaneTorus_mulSingle, SpJoin.spPlaneTorus_mulSingle, spEmbed_lam]
  exact congrArg (fun f => f w) hhom

private theorem spPlaneTorus_mem_range_spEmbed {p m n : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    {v : Fin n → Multiplicative (ZMod p)}
    (hv : ∀ i, i ∉ Set.range σ → v i = 1) :
    SpJoin.spPlaneTorus n ζ v ∈ (spEmbed (K := F) σ hσ).range := by
  have hv' : piExtend σ hσ (fun l => v (σ l)) = v := by
    funext i
    change (if h : ∃ l', σ l' = i then v (σ (Classical.choose h)) else 1) = v i
    split_ifs with h
    · rw [Classical.choose_spec h]
    · exact (hv i (by rintro ⟨l, hl⟩; exact h ⟨l, hl⟩)).symm
  refine ⟨SpJoin.spPlaneTorus m ζ (fun l => v (σ l)), ?_⟩
  rw [← spPlaneTorus_piExtend ζ hσ, hv']

end PlaneEmbedding

private theorem exists_complement_embedding {m n : ℕ} {σ : Fin m → Fin n}
    (hσ : Function.Injective σ) :
    ∃ (a : ℕ) (τ : Fin a → Fin n), Function.Injective τ ∧
      Set.range τ = (Set.range σ)ᶜ := by
  classical
  let W : Finset (Fin n) := Finset.univ.filter fun i => i ∉ Set.range σ
  have hSf : Finset.univ.filter (fun i : Fin n => i ∈ Set.range σ) =
      Finset.univ.image σ := by
    ext i
    simp [Set.mem_range]
  have hcardS : (Finset.univ.image σ).card = m := by
    rw [Finset.card_image_of_injective _ hσ, Finset.card_univ, Fintype.card_fin]
  have hWcard : W.card = n - m := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => i ∈ Set.range σ)
    rw [hSf, hcardS, Finset.card_univ, Fintype.card_fin] at h
    dsimp only [W]
    omega
  refine ⟨n - m, W.orderEmbOfFin hWcard, (W.orderEmbOfFin hWcard).injective, ?_⟩
  rw [Finset.range_orderEmbOfFin]
  ext i
  simp [W]

section FrameCore

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.SpJoin

variable {G : Type} [Group G] {p n m k : ℕ} {F : Type} [Field F]

namespace GGSpPlaneFrameOn

@[expose] noncomputable def zetaTorus {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (ι : Fin m → Fin n)
    (ζ : Multiplicative (ZMod p) →* SL(2, F)) (b : ↥Bs) : StatedSp m F :=
  SpJoin.spPlaneTorus m ζ fun l => eta b (ι l)

theorem zetaFrame_conj {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin m → Fin n}
    {κ : StatedSp m F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (b : ↥Bs) (s : StatedSp m F) :
    (b : G) * κ s * (b : G)⁻¹ =
      κ (zetaTorus eta ι ζ b * s * (zetaTorus eta ι ζ b)⁻¹) :=
  hκ.2.2.2.2 b s

private theorem spPlaneTorus_commute (ζ : Multiplicative (ZMod p) →* SL(2, F))
    (v w : Fin m → Multiplicative (ZMod p)) :
    Commute (SpJoin.spPlaneTorus m ζ v) (SpJoin.spPlaneTorus m ζ w) := by
  show SpJoin.spPlaneTorus m ζ v * SpJoin.spPlaneTorus m ζ w =
    SpJoin.spPlaneTorus m ζ w * SpJoin.spPlaneTorus m ζ v
  rw [← map_mul, ← map_mul, mul_comm]

theorem zetaTorus_mem_Bs [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin m → Fin n}
    {κ : StatedSp m F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (v : Fin m → Multiplicative (ZMod p)) :
    κ (SpJoin.spPlaneTorus m ζ v) ∈ Bs := by
  have hcomm : κ (SpJoin.spPlaneTorus m ζ v) ∈
      Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hfr := zetaFrame_conj hκ ⟨b, hb⟩ (SpJoin.spPlaneTorus m ζ v)
    have hTc : Commute (zetaTorus eta ι ζ ⟨b, hb⟩) (SpJoin.spPlaneTorus m ζ v) :=
      spPlaneTorus_commute ζ _ _
    have hTeq : zetaTorus eta ι ζ ⟨b, hb⟩ * SpJoin.spPlaneTorus m ζ v *
          (zetaTorus eta ι ζ ⟨b, hb⟩)⁻¹ = SpJoin.spPlaneTorus m ζ v := by
      rw [hTc.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hTeq] at hfr
    calc b * κ (SpJoin.spPlaneTorus m ζ v)
        = (b * κ (SpJoin.spPlaneTorus m ζ v) * b⁻¹) * b := by group
      _ = κ (SpJoin.spPlaneTorus m ζ v) * b := by rw [hfr]
  have hpow : (κ (SpJoin.spPlaneTorus m ζ v)) ^ p = 1 := by
    rw [← map_pow, ← map_pow]
    have hv : v ^ p = 1 := by
      funext j
      have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by
        simp [ZMod.card]
      simpa [hcard] using pow_card_eq_one (x := v j)
    rw [hv, map_one, map_one]
  exact hBs _ hcomm hpow

theorem zetaTorus_eta [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin m → Fin n}
    {κ : StatedSp m F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (v : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    eta ⟨κ (SpJoin.spPlaneTorus m ζ v),
      zetaTorus_mem_Bs hκ hBs v⟩ (ι j) = v j := by
  let S : StatedSp m F := SpJoin.spPlaneTorus m ζ v
  let b : ↥Bs := ⟨κ S, zetaTorus_mem_Bs hκ hBs v⟩
  let T : StatedSp m F := zetaTorus eta ι ζ b
  have hb : (b : G) = κ S := rfl
  have harg : ∀ s : StatedSp m F, S * s * S⁻¹ = T * s * T⁻¹ := by
    intro s
    have h1 := zetaFrame_conj hκ b s
    refine hκ.2.1 ?_
    calc κ (S * s * S⁻¹) = (κ S * κ s) * (κ S)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = (b : G) * κ s * (b : G)⁻¹ := by rw [hb]
      _ = κ (T * s * T⁻¹) := h1
  have hc : S⁻¹ * T ∈ Subgroup.center (StatedSp m F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h := harg s
    calc s * (S⁻¹ * T) = S⁻¹ * (S * s * S⁻¹) * T := by group
      _ = S⁻¹ * (T * s * T⁻¹) * T := by rw [h]
      _ = (S⁻¹ * T) * s := by group
  have hc1 : S⁻¹ * T = 1 := by
    have hbot := CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) m
    exact Subgroup.mem_bot.mp (hbot ▸ hc)
  have hTS : T = S := by
    calc T = S * (S⁻¹ * T) := by group
      _ = S * 1 := by rw [hc1]
      _ = S := mul_one S
  have hfun : (fun l : Fin m => eta b (ι l)) = v := by
    apply CFSG.StandardType.TorC.spPlaneTorus_injective hκ.2.2.2.1 m
    exact hTS
  exact congrFun hfun j

theorem commute_spEmbed_of_coordZero {p a b k : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) (b' : ↥Bs)
    (hbS : ∀ c ∈ Set.range fun l => ι (σ l), eta b' c = 1)
    (s : StatedSp k F) :
    Commute (zetaTorus eta ι ζ b') (spEmbed (K := F) σ hσ s) := by
  classical
  obtain ⟨c, τ, hτinj, hτrange⟩ := exists_complement_embedding hσ
  have hv : ∀ i, i ∉ Set.range τ → (fun l => eta b' (ι l)) i = 1 := by
    intro i hi
    have hi' : i ∈ Set.range σ := by
      rw [hτrange] at hi
      simpa using hi
    obtain ⟨l, rfl⟩ := hi'
    exact hbS _ ⟨l, rfl⟩
  have hTrange : zetaTorus eta ι ζ b' ∈
      (spEmbed (K := F) τ hτinj).range :=
    spPlaneTorus_mem_range_spEmbed ζ hτinj hv
  have hTsupp : zetaTorus eta ι ζ b' ∈ suppGroup (Set.range (Sum.map τ τ)) := by
    rw [← range_spEmbed (K := F) hτinj]
    exact hTrange
  have hSsupp : spEmbed (K := F) σ hσ s ∈ suppGroup (Set.range (Sum.map σ σ)) := by
    rw [← range_spEmbed (K := F) hσ]
    exact ⟨s, rfl⟩
  have hmem : ∀ i, i ∈ Set.range τ ↔ ¬ i ∈ Set.range σ := by
    intro i
    rw [hτrange]
    exact Iff.rfl
  have hsupp : Set.range (Sum.map τ τ) = (Set.range (Sum.map σ σ))ᶜ := by
    ext z
    rcases z with i | i <;> simpa [Set.mem_range] using hmem i
  have hSsupp' : spEmbed (K := F) σ hσ s ∈
      suppGroup ((Set.range (Sum.map τ τ))ᶜ) := by
    rw [hsupp, compl_compl]
    exact hSsupp
  exact commute_suppGroup_compl hTsupp hSsupp'

theorem coordZero_commute {p a b k : ℕ} {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) (b' : ↥Bs)
    (hbS : ∀ c ∈ Set.range fun l => ι (σ l), eta b' c = 1)
    (s : StatedSp k F) :
    (b' : G) * κ (spEmbed (K := F) σ hσ s) * (b' : G)⁻¹ =
      κ (spEmbed (K := F) σ hσ s) := by
  have hcomm := commute_spEmbed_of_coordZero (eta := eta) (ι := ι) (ζ := ζ) σ hσ b' hbS s
  have hTeq : zetaTorus eta ι ζ b' * spEmbed (K := F) σ hσ s *
      (zetaTorus eta ι ζ b')⁻¹ = spEmbed (K := F) σ hσ s := by
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hfr := zetaFrame_conj hκ b' (spEmbed (K := F) σ hσ s)
  rw [hfr, hTeq]

theorem range_le_centralizer {p a b k : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) :
    (κ.comp (spEmbed (K := F) σ hσ)).range ≤
      Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
  classical
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [MonoidHom.mem_range] at hx
  obtain ⟨s, hs⟩ := hx
  have hhB : h ∈ Bs := ggBsCoordZeroOn_le _ _ _ hh
  have hhS : ∀ c ∈ Set.range (fun l => ι (σ l)), eta ⟨h, hhB⟩ c = 1 := by
    obtain ⟨h', hhS'⟩ := mem_ggBsCoordZeroOn.mp hh
    have heq : (⟨h, h'⟩ : ↥Bs) = ⟨h, hhB⟩ := Subtype.ext rfl
    simpa only [heq] using hhS'
  have hfr' := coordZero_commute hκ σ hσ ⟨h, hhB⟩ hhS s
  have hs' : κ (spEmbed (K := F) σ hσ s) = x := by
    simpa only [MonoidHom.comp_apply] using hs
  rw [hs'] at hfr'
  have hcalc : h * x * h⁻¹ = x := by
    simpa only [Subtype.coe_mk] using hfr'
  calc h * x = (h * x * h⁻¹) * h := by group
    _ = x * h := by rw [hcalc]

theorem zeta_trace_ne_zero {a b : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP F 2]
    {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) :
    ((ζ (Multiplicative.ofAdd (1 : ZMod p)) : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
  let x : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have hgne : ζ x ≠ 1 := by
    intro hx
    have hx1 : x = 1 := hκ.2.2.2.1 (by rw [hx, map_one])
    have hx0 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective hx1
    exact one_ne_zero hx0
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have ha_pow : x ^ p = 1 := by
    have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by simp [ZMod.card]
    simpa [hcard] using pow_card_eq_one (x := x)
  have hgpow : (ζ x) ^ p = 1 := by rw [← map_pow, ha_pow, map_one]
  exact trace_ne_zero_of_pow_eq_one hgne hpodd hgpow

theorem not_mem_centralizer_lam {a b : ℕ} [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {j : Fin a}
    {g : SL(2, F)} (hg : g ≠ 1) :
    κ (lam j g) ∉ Subgroup.centralizer (K : Set G) := by
  intro hcent
  have hlam_cent : lam j g ∈ Subgroup.center (StatedSp a F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hsK : κ s ∈ K := by
      rw [← hκ.2.2.1]
      exact ⟨s, rfl⟩
    have hcomm : κ (lam j g * s) = κ (s * lam j g) := by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp hcent (κ s) hsK).symm
    exact (hκ.2.1 hcomm).symm
  have hlam1 : lam j g = 1 := by
    have hbot := CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) a
    exact Subgroup.mem_bot.mp (hbot ▸ hlam_cent)
  exact hg (CFSG.StandardType.SpJoin.lam_injective j (by simpa using hlam1))

end GGSpPlaneFrameOn

end FrameCore

variable {G : Type} [Group G] {F : Type} [Field F]

theorem ggCommutator_centralizer_eq_of_mul {E H W N R : Subgroup G}
    (hgen : ∀ e ∈ E, ∃ h ∈ H, ∃ w ∈ W, e = h * w) (hWE : W ≤ E)
    (hN : Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (N : Set G)) (hWN : W ≤ N)
    (hNR : N ≤ R) (hRC : R ≤ Subgroup.centralizer (H : Set G)) (hRW : R ≤ ⁅R, W⁆) :
    ⁅Subgroup.centralizer (H : Set G), E⁆ = R := by
  refine le_antisymm ?_ (hRW.trans (Subgroup.commutator_mono hRC hWE))
  rw [Subgroup.commutator_le]
  intro c hc e he
  obtain ⟨h, hh, w, hw, rfl⟩ := hgen e he
  have hhc : h * c = c * h := Subgroup.mem_centralizer_iff.mp hc h hh
  have hcw : c * w * c⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hN hc) w).mp (hWN hw)
  have hr : ⁅c, w⁆ ∈ R := by
    rw [commutatorElement_def]
    exact hNR (N.mul_mem hcw (N.inv_mem (hWN hw)))
  have hhr : h * ⁅c, w⁆ = ⁅c, w⁆ * h := Subgroup.mem_centralizer_iff.mp (hRC hr) h hh
  have heq : ⁅c, h * w⁆ = h * ⁅c, w⁆ * h⁻¹ := by
    calc ⁅c, h * w⁆ = c * h * w * c⁻¹ * w⁻¹ * h⁻¹ := by
          simp only [commutatorElement_def, mul_inv_rev]; group
      _ = h * c * w * c⁻¹ * w⁻¹ * h⁻¹ := by rw [hhc]
      _ = h * ⁅c, w⁆ * h⁻¹ := by simp only [commutatorElement_def]; group
  rw [heq, hhr, mul_inv_cancel_right]
  exact hr

open Matrix CFSG.StandardType.SpJoin CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

private theorem coe_mem_ggBsCoordZeroOn {p n : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {S : Set (Fin n)} {b : ↥Bs} :
    (b : G) ∈ ggBsCoordZeroOn Bs eta S ↔ ∀ c ∈ S, eta b c = 1 :=
  mem_ggBsCoordZeroOn.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨b.2, h⟩⟩

private theorem ggSecFiveBPermZeta_eta_y_eq_one [Finite G] {p n r : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2]
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (m : Fin (r + 1)) :
    eta ⟨y, hyB⟩ (ι m) = 1 := by
  let b : ↥Bs := ⟨y, hyB⟩
  let T : StatedSp (r + 1) F := GGSpPlaneFrameOn.zetaTorus eta ι ζ b
  have hyK : ∀ s : StatedSp (r + 1) F, (y : G) * κ s * y⁻¹ = κ s := by
    intro s
    have hs : κ s ∈ K := by
      rw [← hκ.2.2.1]
      exact ⟨s, rfl⟩
    have hyc : κ s * y = y * κ s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hs)
    calc y * κ s * y⁻¹ = (κ s * y) * y⁻¹ := by rw [hyc]
      _ = κ s := mul_inv_cancel_right _ _
  have harg : ∀ s : StatedSp (r + 1) F, T * s * T⁻¹ = s := by
    intro s
    have h1 := GGSpPlaneFrameOn.zetaFrame_conj hκ b s
    rw [hyK s] at h1
    exact hκ.2.1 h1.symm
  have hTcent : T ∈ Subgroup.center (StatedSp (r + 1) F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    calc s * T = (T * s * T⁻¹) * T := by rw [harg s]
      _ = T * s := by group
  have hT1 : T = 1 := by
    have hbot := CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot
      (K := F) (r + 1)
    exact Subgroup.mem_bot.mp (hbot ▸ hTcent)
  have hfun : (fun m : Fin (r + 1) => eta b (ι m)) = 1 := by
    apply CFSG.StandardType.TorC.spPlaneTorus_injective hκ.2.2.2.1 (r + 1)
    simpa [T, GGSpPlaneFrameOn.zetaTorus] using hT1
  have := congrFun hfun m
  simpa [b] using this

private theorem ggSecFiveBPermZeta_range_perfect [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    (κ.comp (spEmbed (K := F) σ hσ)).range =
      ⁅(κ.comp (spEmbed (K := F) σ hσ)).range,
        (κ.comp (spEmbed (K := F) σ hσ)).range⁆ := by
  have hperf : Group.IsPerfect (StatedSp (k + 1) F) := by
    rcases hF with h4 | h3
    · exact CFSG.ClassicalInvolution.Models.SymplecticPairs.isPerfect_statedSp_of_four_le h4
    · let : Fintype F := Fintype.ofFinite F
      obtain ⟨m, -, hm⟩ := FiniteField.card F 2
      have hcard : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
      have hF' : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ k + 1) ∨
          (Nat.card F = 2 ∧ 3 ≤ k + 1) := by
        rcases Nat.lt_or_ge (m : ℕ) 2 with hm2 | hm2
        · have hm1 : (m : ℕ) = 1 := by have := m.pos; omega
          exact Or.inr (Or.inr ⟨by rw [hcard, hm1, pow_one], h3⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm2
      exact (CFSG.LieType.Universal.Symplectic.isQuasisimple (k + 1) F (by omega) hF').1
  have h := map_commutator_eq (G := ↥(StatedSp (k + 1) F))
    (κ.comp (spEmbed (K := F) σ hσ))
  rw [hperf.commutator_eq_top, Subgroup.map_top] at h
  exact h

private theorem ggSecFiveBPermZeta_coordTorus_eq_lam {p n r : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} (hι : Function.Injective ι)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (i : Fin (r + 1)) :
    let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
    GGSpPlaneFrameOn.zetaTorus eta ι ζ (eta.symm (Pi.mulSingle (ι i) a)) =
      lam i (ζ a) := by
  intro a
  dsimp only [GGSpPlaneFrameOn.zetaTorus]
  have hfun : (fun m => eta (eta.symm (Pi.mulSingle (ι i) a)) (ι m)) =
      Pi.mulSingle i a := by
    funext m
    rw [MulEquiv.apply_symm_apply]
    by_cases h : m = i
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have hne : ι m ≠ ι i := by
        intro he
        exact h (hι he)
      rw [Pi.mulSingle_eq_of_ne hne, Pi.mulSingle_eq_of_ne h]
  rw [hfun, SpJoin.spPlaneTorus_mulSingle]

private theorem ggSecFiveBPermZeta_coordTorus_mem_H {p n r k : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} (hι : Function.Injective ι)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (σ : Fin (k + 1) → Fin (r + 1)) (i : Fin (r + 1))
    (hi : i ∉ Set.range σ) :
    let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
    ((eta.symm (Pi.mulSingle (ι i) a) : ↥Bs) : G) ∈
      ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
  intro a
  rw [coe_mem_ggBsCoordZeroOn]
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  have hne : ι (σ l) ≠ ι i := by
    intro he
    exact hi ⟨l, hι he⟩
  rw [MulEquiv.apply_symm_apply]
  exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) hne a

private theorem ggSecFiveBPermZeta_commute_lam_coordTorus [Finite G] {p n r k : ℕ}
    [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (i : Fin (r + 1))
    (hi : i ∉ Set.range σ) :
    let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
    ∀ s ∈ (K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G)).comap κ,
      s * lam i (ζ a) = lam i (ζ a) * s := by
  intro a s hs
  let b : ↥Bs := eta.symm (Pi.mulSingle (ι i) a)
  have hbH : (b : G) ∈ ggBsCoordZeroOn Bs eta
      (Set.range fun l => ι (σ l)) :=
    ggSecFiveBPermZeta_coordTorus_mem_H (Bs := Bs) (eta := eta) (ι := ι)
      (ζ := ζ) hκ.1 σ i hi
  have hsM : κ s ∈ K ⊓ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := hs
  have hcomm : (b : G) * κ s = κ s * (b : G) :=
    Subgroup.mem_centralizer_iff.mp hsM.2 (b : G) hbH
  have hL : (b : G) * κ s * (b : G)⁻¹ = κ s := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfr := GGSpPlaneFrameOn.zetaFrame_conj hκ b s
  rw [hL] at hfr
  have harg : GGSpPlaneFrameOn.zetaTorus eta ι ζ b * s *
      (GGSpPlaneFrameOn.zetaTorus eta ι ζ b)⁻¹ = s := hκ.2.1 hfr.symm
  have hT : GGSpPlaneFrameOn.zetaTorus eta ι ζ b = lam i (ζ a) :=
    ggSecFiveBPermZeta_coordTorus_eq_lam (Bs := Bs) (eta := eta) (ι := ι)
      (ζ := ζ) hκ.1 i
  rw [hT] at harg
  have hTs : lam i (ζ a) * s = s * lam i (ζ a) := by
    calc lam i (ζ a) * s
        = (lam i (ζ a) * s * (lam i (ζ a))⁻¹) * lam i (ζ a) := by group
      _ = s * lam i (ζ a) := by rw [harg]
  exact hTs.symm

private theorem det_sub_one_eq_trace [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) :
    (M - 1).det = M.trace := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero, CharTwo.sub_eq_add, CharTwo.neg_eq]
  have hM' : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hM
    rw [CharTwo.sub_eq_add] at hM
    exact hM
  have h3 : M 0 0 * M 1 1 + M 0 1 * M 1 0 + 1 = 0 := by
    rw [hM']
    exact CharTwo.add_self_eq_zero 1
  linear_combination h3

private theorem vecMul_pairMat_apply_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (v ᵥ* pairMat a b g) a = v a * g 0 0 + v b * g 1 0 := by
  rw [Matrix.vecMul_apply_eq_sum,
    Fintype.sum_eq_add a b hab (fun x hx => by
      rw [pairMat_apply_of_ne hx.1 hx.2, one_apply_ne hx.1, mul_zero])]
  obtain ⟨h1, _, h3, _⟩ := pairMat_apply_pair hab g
  rw [h1, h3]

private theorem vecMul_pairMat_apply_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (v ᵥ* pairMat a b g) b = v a * g 0 1 + v b * g 1 1 := by
  rw [Matrix.vecMul_apply_eq_sum,
    Fintype.sum_eq_add a b hab (fun x hx => by
      rw [pairMat_apply_of_ne hx.1 hx.2, one_apply_ne hx.2, mul_zero])]
  obtain ⟨_, h2, _, h4⟩ := pairMat_apply_pair hab g
  rw [h2, h4]

private theorem vecMul_pairMat_apply_of_notMem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι}
    (g : Matrix (Fin 2) (Fin 2) R) {r : ι} (hra : r ≠ a) (hrb : r ≠ b) (v : ι → R) :
    (v ᵥ* pairMat a b g) r = v r := by
  rw [Matrix.vecMul_apply_eq_sum]
  rw [Finset.sum_eq_single r]
  · rw [pairMat_apply_of_ne' hra hrb, one_apply_eq, mul_one]
  · intro x _ hxr
    rw [pairMat_apply_of_ne' hra hrb, one_apply_ne hxr, mul_zero]
  · simp

private theorem eq_zero_of_vecMul_sub_one_eq_zero [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {x : Fin 2 → F} (hx : x ᵥ* ((g : Matrix (Fin 2) (Fin 2) F) - 1) = 0) : x = 0 :=
  Matrix.eq_zero_of_vecMul_eq_zero (by
    rw [det_sub_one_eq_trace _ (Matrix.SpecialLinearGroup.det_coe g)]
    exact htr) hx

private theorem eq_zero_of_mulVec_sub_one_eq_zero [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {y : Fin 2 → F} (hy : ((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ y = 0) : y = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero (by
    rw [det_sub_one_eq_trace _ (Matrix.SpecialLinearGroup.det_coe g)]
    exact htr) hy

private theorem eq_zero_pair_of_fixed_left [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {x₀ x₁ : F}
    (h₀ : x₀ * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + x₁ * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = x₀)
    (h₁ : x₀ * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + x₁ * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = x₁) :
    x₀ = 0 ∧ x₁ = 0 := by
  have hx : (![x₀, x₁] : Fin 2 → F) ᵥ* ((g : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
    rw [funext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, mul_add, mul_one, add_right_comm, h₀]
      exact CharTwo.add_self_eq_zero _
    · rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, mul_add, mul_one, ← add_assoc, h₁]
      exact CharTwo.add_self_eq_zero _
  have hzero := eq_zero_of_vecMul_sub_one_eq_zero htr hx
  exact ⟨by simpa using congrFun hzero 0, by simpa using congrFun hzero 1⟩

private theorem eq_zero_pair_of_fixed_right [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {y₀ y₁ : F}
    (h₀ : y₀ = (g : Matrix (Fin 2) (Fin 2) F) 0 0 * y₀ + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * y₁)
    (h₁ : y₁ = (g : Matrix (Fin 2) (Fin 2) F) 1 0 * y₀ + (g : Matrix (Fin 2) (Fin 2) F) 1 1 * y₁) :
    y₀ = 0 ∧ y₁ = 0 := by
  have hy : ((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ (![y₀, y₁] : Fin 2 → F) = 0 := by
    rw [funext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Pi.zero_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, add_mul, one_mul, add_right_comm, ← h₀]
      exact CharTwo.add_self_eq_zero _
    · rw [Pi.zero_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, add_mul, one_mul, ← add_assoc, ← h₁]
      exact CharTwo.add_self_eq_zero _
  have hzero := eq_zero_of_mulVec_sub_one_eq_zero htr hy
  exact ⟨by simpa using congrFun hzero 0, by simpa using congrFun hzero 1⟩

private theorem isSupp_iff_basic {n : ℕ} {A : Set (Fin n ⊕ Fin n)}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp A M ↔
      CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp A M := by
  constructor
  · intro h x y hxy
    exact h x y (not_and_or.mp hxy)
  · intro h x y hxy
    exact h x y (not_and_or.mpr hxy)

private theorem eq_plane_or_succAbove {n : ℕ} {i : Fin (n + 1)}
    {c : Fin (n + 1) ⊕ Fin (n + 1)} (hc : c ≠ Sum.inl i ∧ c ≠ Sum.inr i) :
    (∃ j : Fin n, c = Sum.inl (i.succAbove j)) ∨
      (∃ j : Fin n, c = Sum.inr (i.succAbove j)) := by
  rcases c with x | x
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (x := x) (y := i) (fun h => hc.1 (by rw [h]))
    exact Or.inl ⟨j, rfl⟩
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (x := x) (y := i) (fun h => hc.2 (by rw [h]))
    exact Or.inr ⟨j, rfl⟩

private noncomputable def cornerMat {n : ℕ} (u : StatedSp (n + 1) F) (i : Fin (n + 1)) :
    Matrix (Fin 2) (Fin 2) F :=
  !![mat (n + 1) F u (Sum.inl i) (Sum.inl i), mat (n + 1) F u (Sum.inl i) (Sum.inr i);
     mat (n + 1) F u (Sum.inr i) (Sum.inl i), mat (n + 1) F u (Sum.inr i) (Sum.inr i)]

private theorem cornerMat_det_eq_one {n : ℕ} {i : Fin (n + 1)} {u : StatedSp (n + 1) F}
    (hu : ∀ (j : Fin n) (a : Fin (n + 1) ⊕ Fin (n + 1)),
      a = Sum.inl i ∨ a = Sum.inr i →
        (mat (n + 1) F u (Sum.inl (i.succAbove j)) a = 0 ∧
          mat (n + 1) F u (Sum.inr (i.succAbove j)) a = 0 ∧
          mat (n + 1) F u a (Sum.inl (i.succAbove j)) = 0 ∧
          mat (n + 1) F u a (Sum.inr (i.succAbove j)) = 0)) :
    (cornerMat u i).det = 1 := by
  have hUU := congrFun (congrFun (mat_transpose_mul_gram_mul u) (Sum.inl i)) (Sum.inr i)
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
    par_inl, if_pos rfl, sgn_inl] at hUU
  rw [Fintype.sum_eq_add (Sum.inl i) (Sum.inr i) (by simp) (fun c hc => by
    rcases eq_plane_or_succAbove hc with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [(hu j (Sum.inl i) (Or.inl rfl)).1, zero_mul]
    · rw [(hu j (Sum.inl i) (Or.inl rfl)).2.1, zero_mul])] at hUU
  rw [sgn_inl, par_inl, sgn_inr, par_inr] at hUU
  rw [show (cornerMat u i).det = mat (n + 1) F u (Sum.inl i) (Sum.inl i) *
      mat (n + 1) F u (Sum.inr i) (Sum.inr i) -
      mat (n + 1) F u (Sum.inl i) (Sum.inr i) *
      mat (n + 1) F u (Sum.inr i) (Sum.inl i) by
    simp [cornerMat, det_fin_two]]
  linear_combination hUU

private theorem mat_mul_single_eq_lam_of_corner {n : ℕ} {i : Fin (n + 1)}
    {u : StatedSp (n + 1) F} {g : SpecialLinearGroup (Fin 2) F}
    (hu : ∀ (j : Fin n) (a : Fin (n + 1) ⊕ Fin (n + 1)),
      a = Sum.inl i ∨ a = Sum.inr i →
        (mat (n + 1) F u (Sum.inl (i.succAbove j)) a = 0 ∧
          mat (n + 1) F u (Sum.inr (i.succAbove j)) a = 0 ∧
          mat (n + 1) F u a (Sum.inl (i.succAbove j)) = 0 ∧
          mat (n + 1) F u a (Sum.inr (i.succAbove j)) = 0))
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = cornerMat u i) :
    ∀ t, t = Sum.inl i ∨ t = Sum.inr i →
      mat (n + 1) F u *ᵥ Pi.single t 1 =
        mat (n + 1) F (lam i g) *ᵥ Pi.single t 1 := by
  intro t ht
  funext r
  rw [mulVec_single_one_apply (mat (n + 1) F u) t r, mat_lam,
    mulVec_single_one_apply (pairMat (Sum.inl i) (Sum.inr i)
      ((g : Matrix (Fin 2) (Fin 2) F))) t r]
  by_cases hr : r = Sum.inl i ∨ r = Sum.inr i
  · rcases hr with rfl | rfl
    · rw [pairMat_apply_fst]
      rcases ht with rfl | rfl <;> simp [hg, cornerMat]
    · rw [pairMat_apply_snd (by simp : (Sum.inl i : Fin (n + 1) ⊕ Fin (n + 1)) ≠ Sum.inr i)]
      rcases ht with rfl | rfl <;> simp [hg, cornerMat]
  · simp only [not_or] at hr
    rw [pairMat_apply_of_ne hr.1 hr.2]
    have hrs := eq_plane_or_succAbove hr
    have hrt : r ≠ t := by
      rintro rfl
      rcases ht with h | h
      · exact hr.1 h
      · exact hr.2 h
    rcases hrs with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [(hu j t ht).1, one_apply_ne hrt]
    · rw [(hu j t ht).2.1, one_apply_ne hrt]

private theorem exists_lam_mul_spEmbed_succAbove_of_entries_zero {n : ℕ} {i : Fin (n + 1)}
    {u : StatedSp (n + 1) F}
    (hu : ∀ (j : Fin n) (a : Fin (n + 1) ⊕ Fin (n + 1)),
      a = Sum.inl i ∨ a = Sum.inr i →
        (mat (n + 1) F u (Sum.inl (i.succAbove j)) a = 0 ∧
          mat (n + 1) F u (Sum.inr (i.succAbove j)) a = 0 ∧
          mat (n + 1) F u a (Sum.inl (i.succAbove j)) = 0 ∧
          mat (n + 1) F u a (Sum.inr (i.succAbove j)) = 0)) :
    ∃ (g : SpecialLinearGroup (Fin 2) F) (h : StatedSp n F),
      u = lam i g * spEmbed (K := F) i.succAbove
        (Fin.succAbove_right_injective (p := i)) h := by
  classical
  let g : SpecialLinearGroup (Fin 2) F := ⟨cornerMat u i, cornerMat_det_eq_one hu⟩
  have hsame := mat_mul_single_eq_lam_of_corner hu (g := g) rfl
  let u₁ : StatedSp (n + 1) F := (lam i g)⁻¹ * u
  have hu₁ : CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp
      (Set.range (Sum.map (i.succAbove) (i.succAbove))) (mat (n + 1) F u₁) := by
    have hS : ParClosed (Set.range (Sum.map (i.succAbove) (i.succAbove))) := by
      rw [range_succAbove]
      exact (parClosed_coords i).compl
    refine isSupp_of_fix hS u₁ ?_
    intro t ht r
    have htA : t = Sum.inl i ∨ t = Sum.inr i := by
      have ht' : t ∈ coords i := by
        simpa [range_succAbove] using ht
      exact mem_coords.mp ht'
    have hcol : mat (n + 1) F u₁ *ᵥ Pi.single t 1 = Pi.single t 1 := by
      have hmat : mat (n + 1) F u₁ =
          mat (n + 1) F ((lam i g)⁻¹) * mat (n + 1) F u := by
        change mat (n + 1) F ((lam i g)⁻¹ * u) = _
        rw [map_mul]
      rw [hmat, ← Matrix.mulVec_mulVec, hsame t htA, Matrix.mulVec_mulVec,
        ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [← mulVec_single_one_apply (mat (n + 1) F u₁) t r, hcol]
    by_cases hrt : r = t
    · subst hrt; simp [one_apply]
    · rw [Pi.single_eq_of_ne hrt, one_apply_ne hrt]
  have hmem : u₁ ∈ (spEmbed (K := F) (σ := i.succAbove)
      (Fin.succAbove_right_injective (p := i))).range := by
    rw [range_spEmbed]
    exact hu₁
  obtain ⟨h, hh⟩ := hmem
  exact ⟨g, h, by
    calc u = lam i g * u₁ := (mul_inv_cancel_left _ _).symm
      _ = lam i g * spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) h := by rw [show u₁ = _ from hh.symm]⟩

private theorem lam_commute_spEmbed_succAbove {n : ℕ} (i : Fin (n + 1))
    (g : SpecialLinearGroup (Fin 2) F) (s : StatedSp n F) :
    Commute (lam i g) (spEmbed (K := F) i.succAbove
      (Fin.succAbove_right_injective (p := i)) s) := by
  refine CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_commute ?_
  have hlam : CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp
      ({Sum.inl i, Sum.inr i} : Set (Fin (n + 1) ⊕ Fin (n + 1)))
      (mat (n + 1) F (lam i g)) := by
    simpa only [mat_apply] using
      CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.isSupp_lam i g
  have hsp : CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp
      (Set.range (Sum.map (i.succAbove) (i.succAbove)))
      (mat (n + 1) F (spEmbed (K := F) i.succAbove
        (Fin.succAbove_right_injective (p := i)) s)) :=
    isSupp_iff_basic.mpr (isSupp_spEmbed _ s)
  have hdisj : Disjoint ({Sum.inl i, Sum.inr i} : Set (Fin (n + 1) ⊕ Fin (n + 1)))
      (Set.range (Sum.map (i.succAbove) (i.succAbove))) := by
    rw [range_succAbove, Set.disjoint_left]
    intro x hx hx'
    exact hx' hx
  exact hlam.commute hsp hdisj

private theorem mat_mul_comm_of_commute_lam {n : ℕ} {i : Fin (n + 1)}
    {g : SpecialLinearGroup (Fin 2) F} {u : StatedSp (n + 1) F}
    (hu : u * lam i g = lam i g * u) :
    mat (n + 1) F u * mat (n + 1) F (lam i g) =
      mat (n + 1) F (lam i g) * mat (n + 1) F u := by
  have h := congrArg (mat (n + 1) F) hu
  rw [map_mul, map_mul] at h
  exact h

private theorem row_zero_of_commute_lam [CharP F 2] {n : ℕ} {i : Fin (n + 1)}
    {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {u : StatedSp (n + 1) F}
    (hu : u * lam i g = lam i g * u) :
    ∀ r : Fin (n + 1) ⊕ Fin (n + 1), r ≠ Sum.inl i → r ≠ Sum.inr i →
      mat (n + 1) F u r (Sum.inl i) = 0 ∧ mat (n + 1) F u r (Sum.inr i) = 0 := by
  have hcommM := mat_mul_comm_of_commute_lam hu
  have hzero_plane : Sum.inl i ≠ (Sum.inr i : Fin (n + 1) ⊕ Fin (n + 1)) := Sum.inl_ne_inr
  intro r hra hrb
  have hrow : mat (n + 1) F u r ᵥ* mat (n + 1) F (lam i g) = mat (n + 1) F u r := by
    have h1 : mat (n + 1) F u r ᵥ* mat (n + 1) F (lam i g) =
        (mat (n + 1) F u * mat (n + 1) F (lam i g)) r :=
      (Matrix.mul_apply_eq_vecMul _ _ r).symm
    have h3 : (mat (n + 1) F (lam i g) * mat (n + 1) F u) r = mat (n + 1) F u r := by
      rw [Matrix.mul_apply_eq_vecMul]
      have hΓr : mat (n + 1) F (lam i g) r = (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1))
          (Fin (n + 1) ⊕ Fin (n + 1)) F) r := by
        funext x
        rw [mat_lam]
        exact pairMat_apply_of_ne hra hrb (g : Matrix (Fin 2) (Fin 2) F) x
      rw [hΓr, ← Matrix.mul_apply_eq_vecMul, Matrix.one_mul]
    rw [h1, hcommM, h3]
  refine eq_zero_pair_of_fixed_left htr ?_ ?_
  · have h := congrFun hrow (Sum.inl i)
    rw [mat_lam, vecMul_pairMat_apply_inl hzero_plane] at h
    exact h
  · have h := congrFun hrow (Sum.inr i)
    rw [mat_lam, vecMul_pairMat_apply_inr hzero_plane] at h
    exact h

private theorem col_zero_of_commute_lam [CharP F 2] {n : ℕ} {i : Fin (n + 1)}
    {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {u : StatedSp (n + 1) F}
    (hu : u * lam i g = lam i g * u) :
    ∀ c : Fin (n + 1) ⊕ Fin (n + 1), c ≠ Sum.inl i → c ≠ Sum.inr i →
      mat (n + 1) F u (Sum.inl i) c = 0 ∧ mat (n + 1) F u (Sum.inr i) c = 0 := by
  have hcommM := mat_mul_comm_of_commute_lam hu
  have hzero_plane : Sum.inl i ≠ (Sum.inr i : Fin (n + 1) ⊕ Fin (n + 1)) := Sum.inl_ne_inr
  intro c hca hcb
  have hL : (mat (n + 1) F u * mat (n + 1) F (lam i g)) (Sum.inl i) c =
      mat (n + 1) F u (Sum.inl i) c := by
    rw [Matrix.mul_apply_eq_vecMul, mat_lam,
      vecMul_pairMat_apply_of_notMem (g : Matrix (Fin 2) (Fin 2) F) hca hcb]
  have hR : (mat (n + 1) F (lam i g) * mat (n + 1) F u) (Sum.inl i) c =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * mat (n + 1) F u (Sum.inl i) c +
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * mat (n + 1) F u (Sum.inr i) c := by
    rw [Matrix.mul_apply_eq_vecMul, mat_lam, Matrix.vecMul_apply_eq_sum]
    rw [Fintype.sum_eq_add (Sum.inl i) (Sum.inr i) hzero_plane (fun x hx => by
      rw [pairMat_apply_fst_of_ne hx.1 hx.2, zero_mul])]
    obtain ⟨h1, h2, _, _⟩ := pairMat_apply_pair hzero_plane (g : Matrix (Fin 2) (Fin 2) F)
    rw [h1, h2]
  have hL' : (mat (n + 1) F u * mat (n + 1) F (lam i g)) (Sum.inr i) c =
      mat (n + 1) F u (Sum.inr i) c := by
    rw [Matrix.mul_apply_eq_vecMul, mat_lam,
      vecMul_pairMat_apply_of_notMem (g : Matrix (Fin 2) (Fin 2) F) hca hcb]
  have hR' : (mat (n + 1) F (lam i g) * mat (n + 1) F u) (Sum.inr i) c =
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 * mat (n + 1) F u (Sum.inl i) c +
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 * mat (n + 1) F u (Sum.inr i) c := by
    rw [Matrix.mul_apply_eq_vecMul, mat_lam, Matrix.vecMul_apply_eq_sum]
    rw [Fintype.sum_eq_add (Sum.inl i) (Sum.inr i) hzero_plane (fun x hx => by
      rw [pairMat_apply_snd_of_ne hzero_plane hx.1 hx.2, zero_mul])]
    obtain ⟨_, _, h3, h4⟩ := pairMat_apply_pair hzero_plane (g : Matrix (Fin 2) (Fin 2) F)
    rw [h3, h4]
  refine eq_zero_pair_of_fixed_right htr ?_ ?_
  · have h := congrFun (congrFun hcommM (Sum.inl i)) c
    rw [hL, hR] at h
    exact h
  · have h := congrFun (congrFun hcommM (Sum.inr i)) c
    rw [hL', hR'] at h
    exact h

private theorem commute_lam_of_eq_mul_spEmbed {n : ℕ} {i : Fin (n + 1)}
    {g h : SpecialLinearGroup (Fin 2) F} {s : StatedSp n F} {u : StatedSp (n + 1) F}
    (hu : u * lam i g = lam i g * u)
    (hus : u = lam i h * spEmbed (K := F) i.succAbove
      (Fin.succAbove_right_injective (p := i)) s) : h * g = g * h := by
  apply lam_injective i
  rw [map_mul, map_mul]
  exact mul_right_cancel (by
    calc lam i h * lam i g * spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) s
        = lam i h * (lam i g * spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) s) := by rw [mul_assoc]
      _ = lam i h * (spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) s * lam i g) := by
            rw [(lam_commute_spEmbed_succAbove i g s).eq]
      _ = lam i h * spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) s * lam i g := by rw [← mul_assoc]
      _ = u * lam i g := by rw [← hus]
      _ = lam i g * u := hu
      _ = lam i g * (lam i h * spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) s) := by rw [hus]
      _ = lam i g * lam i h * spEmbed (K := F) i.succAbove
            (Fin.succAbove_right_injective (p := i)) s := by rw [mul_assoc])

theorem exists_lam_mul_spEmbed_succAbove_of_commute [CharP F 2] {n : ℕ}
    {i : Fin (n + 1)} {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {u : StatedSp (n + 1) F}
    (hu : u * lam i g = lam i g * u) :
    ∃ (h : SpecialLinearGroup (Fin 2) F) (s : StatedSp n F),
      u = lam i h * spEmbed (K := F) i.succAbove
        (Fin.succAbove_right_injective (p := i)) s ∧ h * g = g * h := by
  have hplane : ∀ j : Fin n, Sum.inl (i.succAbove j) ≠ (Sum.inl i :
      Fin (n + 1) ⊕ Fin (n + 1)) := fun j h => Fin.succAbove_ne i j (Sum.inl_injective h)
  have hplane' : ∀ j : Fin n, Sum.inr (i.succAbove j) ≠ (Sum.inl i :
      Fin (n + 1) ⊕ Fin (n + 1)) := fun _ => Sum.inr_ne_inl
  have hplane'' : ∀ j : Fin n, Sum.inl (i.succAbove j) ≠ (Sum.inr i :
      Fin (n + 1) ⊕ Fin (n + 1)) := fun _ => Sum.inl_ne_inr
  have hplane3 : ∀ j : Fin n, Sum.inr (i.succAbove j) ≠ (Sum.inr i :
      Fin (n + 1) ⊕ Fin (n + 1)) := fun j h => Fin.succAbove_ne i j (Sum.inr_injective h)
  obtain ⟨h, s, hus⟩ := exists_lam_mul_spEmbed_succAbove_of_entries_zero (i := i) (u := u)
    (fun j a ha => by
    rcases ha with rfl | rfl
    · exact ⟨(row_zero_of_commute_lam htr hu (Sum.inl (i.succAbove j))
          (hplane j) (hplane'' j)).1,
        (row_zero_of_commute_lam htr hu (Sum.inr (i.succAbove j))
          (hplane' j) (hplane3 j)).1,
        (col_zero_of_commute_lam htr hu (Sum.inl (i.succAbove j))
          (hplane j) (hplane'' j)).1,
        (col_zero_of_commute_lam htr hu (Sum.inr (i.succAbove j))
          (hplane' j) (hplane3 j)).1⟩
    · exact ⟨(row_zero_of_commute_lam htr hu (Sum.inl (i.succAbove j))
          (hplane j) (hplane'' j)).2,
        (row_zero_of_commute_lam htr hu (Sum.inr (i.succAbove j))
          (hplane' j) (hplane3 j)).2,
        (col_zero_of_commute_lam htr hu (Sum.inl (i.succAbove j))
          (hplane j) (hplane'' j)).2,
        (col_zero_of_commute_lam htr hu (Sum.inr (i.succAbove j))
          (hplane' j) (hplane3 j)).2⟩)
  exact ⟨h, s, hus, commute_lam_of_eq_mul_spEmbed hu hus⟩

private theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {z₁ z₂ l₁ l₂ : G}
    (h₁₁ : Commute z₁ l₁) (h₁₂ : Commute z₁ l₂) (h₂₁ : Commute z₂ l₁) (h₂₂ : Commute z₂ l₂)
    (hz : Commute z₁ z₂) : ⁅z₁ * l₁, z₂ * l₂⁆ = ⁅l₁, l₂⁆ := by
  have e₁ : z₁ * l₁ = l₁ * z₁ := h₁₁.eq
  have e₂ : z₂ * l₂ = l₂ * z₂ := h₂₂.eq
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, _root_.mul_inv_rev]
  have c1 : Commute z₁ (l₁ * (z₂ * l₂) * l₁⁻¹) :=
    (h₁₁.mul_right (hz.mul_right h₁₂)).mul_right h₁₁.inv_right
  have c2 : Commute z₂ (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) :=
    ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  calc z₁ * l₁ * (z₂ * l₂) * (l₁⁻¹ * z₁⁻¹) * (l₂⁻¹ * z₂⁻¹)
      = (z₁ * (l₁ * (z₂ * l₂) * l₁⁻¹) * z₁⁻¹) * l₂⁻¹ * z₂⁻¹ := by group
    _ = l₁ * (z₂ * l₂) * l₁⁻¹ * l₂⁻¹ * z₂⁻¹ := by rw [c1.eq, mul_inv_cancel_right]
    _ = z₂ * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂⁻¹ := by
        rw [show l₁ * (z₂ * l₂) = z₂ * (l₁ * l₂) by
          rw [← mul_assoc, ← h₂₁.eq, mul_assoc]]
        group
    _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [c2.eq, mul_inv_cancel_right]

private theorem commutator_le_spEmbed_succAbove_of_commute [CharP F 2] {n : ℕ}
    {i : Fin (n + 1)} {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {J : Subgroup (StatedSp (n + 1) F)}
    (hc : ∀ j ∈ J, j * lam i g = lam i g * j) :
    ⁅J, J⁆ ≤ (spEmbed (K := F) i.succAbove
      (Fin.succAbove_right_injective (p := i))).range := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨h₁, s₁, rfl, hg₁⟩ := exists_lam_mul_spEmbed_succAbove_of_commute htr (hc a ha)
  obtain ⟨h₂, s₂, rfl, hg₂⟩ := exists_lam_mul_spEmbed_succAbove_of_commute htr (hc b hb)
  have hh : h₁ * h₂ = h₂ * h₁ := commute_of_commute_of_trace_ne_zero htr hg₁ hg₂
  have hz : Commute (lam i h₁) (lam i h₂) := by
    show lam i h₁ * lam i h₂ = lam i h₂ * lam i h₁
    rw [← map_mul, ← map_mul, hh]
  have hC : ⁅lam i h₁ * spEmbed (K := F) i.succAbove
        (Fin.succAbove_right_injective (p := i)) s₁,
      lam i h₂ * spEmbed (K := F) i.succAbove
        (Fin.succAbove_right_injective (p := i)) s₂⁆ =
      ⁅spEmbed (K := F) i.succAbove (Fin.succAbove_right_injective (p := i)) s₁,
        spEmbed (K := F) i.succAbove (Fin.succAbove_right_injective (p := i)) s₂⁆ :=
    commutator_mul_mul_of_commute (lam_commute_spEmbed_succAbove i h₁ s₁)
      (lam_commute_spEmbed_succAbove i h₁ s₂) (lam_commute_spEmbed_succAbove i h₂ s₁)
      (lam_commute_spEmbed_succAbove i h₂ s₂) hz
  rw [hC]
  refine ⟨⁅s₁, s₂⁆, ?_⟩
  simp only [commutatorElement_def, map_mul, map_inv]


private theorem zeta_ofAdd_one_ne_one {p : ℕ} [Fact p.Prime]
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hζ : Function.Injective ζ) :
    ζ (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
  intro h
  have ha_ne : Multiplicative.ofAdd (1 : ZMod p) ≠ 1 := by
    intro ha
    have h0 : Multiplicative.ofAdd (0 : ZMod p) = 1 := rfl
    have h10 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (ha.trans h0.symm)
    exact one_ne_zero h10
  exact ha_ne (hζ (by rw [h, map_one]))

private theorem supp_of_commutator_le_spEmbed [CharP F 2] {n : ℕ} {i : Fin (n + 1)}
    {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {J : Subgroup (StatedSp (n + 1) F)}
    (hc : ∀ j ∈ J, j * lam i g = lam i g * j) {u : StatedSp (n + 1) F}
    (hu : u ∈ ⁅J, J⁆) : u ∈ suppGroup ((coords i)ᶜ) := by
  have hmem := (commutator_le_spEmbed_succAbove_of_commute (i := i) htr hc) hu
  rwa [← range_succAbove,
    ← range_spEmbed (K := F) (Fin.succAbove_right_injective (p := i))]

private theorem commutator_le_spEmbed_of_commute_off [CharP F 2] {r k : ℕ}
    {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ)
    {J : Subgroup (StatedSp (r + 1) F)}
    (hlam : ∀ m, m ∉ Set.range σ → ∀ j ∈ J, j * lam m g = lam m g * j) :
    ⁅J, J⁆ ≤ (spEmbed (K := F) σ hσ).range := by
  rw [range_spEmbed (K := F) hσ]
  intro u hu
  have hpar : ParClosed (Set.range (Sum.map σ σ)) := by
    rintro z ⟨x, rfl⟩
    rcases x with l | l
    · exact ⟨Sum.inr l, rfl⟩
    · exact ⟨Sum.inl l, rfl⟩
  rw [mem_suppGroup_iff hpar]
  intro t ht r
  rcases t with m | m
  · have hm : m ∉ Set.range σ := by
      intro hm
      obtain ⟨l, rfl⟩ := hm
      exact ht ⟨Sum.inl l, rfl⟩
    have hsupp := supp_of_commutator_le_spEmbed (i := m) htr (hlam m hm) hu
    exact (mem_suppGroup.mp hsupp) r (Sum.inl m)
      (fun h => h.2 (mem_coords.mpr (Or.inl rfl)))
  · have hm : m ∉ Set.range σ := by
      intro hm
      obtain ⟨l, rfl⟩ := hm
      exact ht ⟨Sum.inr l, rfl⟩
    have hsupp := supp_of_commutator_le_spEmbed (i := m) htr (hlam m hm) hu
    exact (mem_suppGroup.mp hsupp) r (Sum.inr m)
      (fun h => h.2 (mem_coords.mpr (Or.inr rfl)))

private theorem ggSecFiveBPermZeta_commutator_le_range [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    ⁅K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G),
      K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G)⁆ ≤
      (κ.comp (spEmbed (K := F) σ hσ)).range := by
  classical
  let H : Subgroup G := ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  let M : Subgroup G := K ⊓ Subgroup.centralizer (H : Set G)
  let J : Subgroup (StatedSp (r + 1) F) := M.comap κ
  have hMle : M ≤ κ.range := fun x hx => by rw [hκ.2.2.1]; exact hx.1
  have hJM : J.map κ = M := Subgroup.map_comap_eq_self hMle
  have hN : ⁅M, M⁆ = (⁅J, J⁆).map κ := by
    rw [← hJM, Subgroup.map_commutator]
  rw [hN]
  have hJ : ⁅J, J⁆ ≤ (spEmbed (K := F) σ hσ).range :=
    commutator_le_spEmbed_of_commute_off (GGSpPlaneFrameOn.zeta_trace_ne_zero hp2 hκ) σ hσ
      (fun m hm j hj =>
        ggSecFiveBPermZeta_commute_lam_coordTorus (hκ := hκ) σ m hm j hj)
  calc (⁅J, J⁆).map κ ≤ (spEmbed (K := F) σ hσ).range.map κ := Subgroup.map_mono hJ
    _ = (κ.comp (spEmbed (K := F) σ hσ)).range := (MonoidHom.range_comp κ _).symm

theorem GGSpPlaneFrameOn.commutator_inf_centralizer_eq_range [Finite G]
    {p n r k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    ⁅K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G),
      K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G)⁆ =
      (κ.comp (spEmbed (K := F) σ hσ)).range := by
  refine le_antisymm (ggSecFiveBPermZeta_commutator_le_range hp2 hκ σ hσ) ?_
  have hRC : (κ.comp (spEmbed (K := F) σ hσ)).range ≤
      K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
    intro z hz
    refine ⟨?_, GGSpPlaneFrameOn.range_le_centralizer hκ σ hσ hz⟩
    rw [← hκ.2.2.1]
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
    exact ⟨spEmbed (K := F) σ hσ s, hs⟩
  calc (κ.comp (spEmbed (K := F) σ hσ)).range =
        ⁅(κ.comp (spEmbed (K := F) σ hσ)).range,
          (κ.comp (spEmbed (K := F) σ hσ)).range⁆ :=
      ggSecFiveBPermZeta_range_perfect hp2 hF hκ σ hσ
    _ ≤ _ := Subgroup.commutator_mono hRC hRC

theorem GGSecFiveBPermSpPlaneFrame.commutator_inf_centralizer_eq_range [Finite G]
    {p n r k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 2) ≃ Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    ⁅K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => π (σ l).succ) : Set G),
      K ⊓ Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => π (σ l).succ) : Set G)⁆ =
      (κ.comp (spEmbed (K := F) σ hσ)).range := by
  exact GGSpPlaneFrameOn.commutator_inf_centralizer_eq_range hp2 hF hκ.planeFrameOn σ hσ

private theorem ggSecFiveBPermZeta_gen [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    ∀ b : ↥Bs, ∃ h ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)),
      ∃ w ∈ Bs ⊓ (κ.comp (spEmbed (K := F) σ hσ)).range, (b : G) = h * w := by
  classical
  intro b
  let H : Subgroup G := ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  let R : Subgroup G := (κ.comp (spEmbed (K := F) σ hσ)).range
  let v : Fin (r + 1) → Multiplicative (ZMod p) :=
    fun m => if h : m ∈ Set.range σ then eta b (ι m) else 1
  let w : G := κ (SpJoin.spPlaneTorus (r + 1) ζ v)
  have hwB : w ∈ Bs := GGSpPlaneFrameOn.zetaTorus_mem_Bs hκ hBs v
  have hvsupp : ∀ i, i ∉ Set.range σ → v i = 1 := by
    intro i hi
    dsimp only [v]
    rw [dif_neg hi]
  have hmem : SpJoin.spPlaneTorus (r + 1) ζ v ∈
      (spEmbed (K := F) σ hσ).range :=
    spPlaneTorus_mem_range_spEmbed (ζ := ζ) hσ hvsupp
  have hwR : w ∈ R := by
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, by rw [MonoidHom.comp_apply, hs]⟩
  refine ⟨(b : G) * w⁻¹, ?_, w, ⟨hwB, hwR⟩, by group⟩
  have hhB : (b : G) * w⁻¹ ∈ Bs := Bs.mul_mem b.2 (Bs.inv_mem hwB)
  change ((⟨(b : G) * w⁻¹, hhB⟩ : ↥Bs) : G) ∈ H
  rw [coe_mem_ggBsCoordZeroOn]
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  have hh_eq : (⟨(b : G) * w⁻¹, hhB⟩ : ↥Bs) = b * ⟨w, hwB⟩⁻¹ := Subtype.ext rfl
  have hwcoord : eta ⟨w, hwB⟩ (ι (σ l)) = v (σ l) :=
    GGSpPlaneFrameOn.zetaTorus_eta hκ hBs v (σ l)
  have hv : v (σ l) = eta b (ι (σ l)) := by
    dsimp only [v]
    rw [dif_pos ⟨l, rfl⟩]
  calc eta ⟨(b : G) * w⁻¹, hhB⟩ (ι (σ l))
      = eta (b * ⟨w, hwB⟩⁻¹) (ι (σ l)) := by rw [hh_eq]
    _ = eta b (ι (σ l)) * (eta ⟨w, hwB⟩ (ι (σ l)))⁻¹ := by
        rw [map_mul, map_inv]
        rfl
    _ = eta b (ι (σ l)) * (eta b (ι (σ l)))⁻¹ := by rw [hwcoord, hv]
    _ = 1 := mul_inv_cancel _

private theorem normalizer_commutator_of_normalizer {A : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (A : Set G)) :
    c ∈ Subgroup.normalizer (⁅A, A⁆ : Subgroup G) := by
  have hmap : (⁅A, A⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom = ⁅A, A⁆ := by
    rw [Subgroup.map_commutator,
      CFSG.LocalAnalysis.ComponentInitial.map_conj_eq_of_mem_normalizer hc]
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  have hh := Subgroup.mem_map_equiv (f := MulAut.conj c) (K := (⁅A,A⁆ : Subgroup G)) (x := h)
  rw [hmap] at hh
  simpa [MulAut.conj_symm_apply] using hh

private theorem ggSecFiveBPermZeta_y_mem_H [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {y : G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (σ : Fin (k + 1) → Fin (r + 1)) :
    y ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
  change ((⟨y, hyB⟩ : ↥Bs) : G) ∈
    ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  rw [coe_mem_ggBsCoordZeroOn]
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  exact ggSecFiveBPermZeta_eta_y_eq_one hp2 hκ hyB hK (σ l)

private theorem ggSecFiveBPermZeta_spPlaneTorus_mem_H [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin (k + 1) → Fin (r + 1)) (v : Fin (r + 1) → Multiplicative (ZMod p))
    (hv : ∀ l, v (σ l) = 1) :
    κ (SpJoin.spPlaneTorus (r + 1) ζ v) ∈
      ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
  have hB : κ (SpJoin.spPlaneTorus (r + 1) ζ v) ∈ Bs :=
    GGSpPlaneFrameOn.zetaTorus_mem_Bs hκ hBs v
  change ((⟨κ (SpJoin.spPlaneTorus (r + 1) ζ v), hB⟩ : ↥Bs) : G) ∈
    ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  rw [coe_mem_ggBsCoordZeroOn]
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  rw [GGSpPlaneFrameOn.zetaTorus_eta hκ hBs v (σ l)]
  exact hv l

private theorem exists_mem_H_inf_K_not_mem_centralizer [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin (k + 1) → Fin (r + 1)) {m₀ : Fin (r + 1)} (hm₀ : m₀ ∉ Set.range σ) :
    ∃ r ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) ⊓ K,
      r ∉ Subgroup.centralizer (K : Set G) := by
  let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have hgne : ζ a ≠ 1 := zeta_ofAdd_one_ne_one hκ.2.2.2.1
  let v₀ : Fin (r + 1) → Multiplicative (ZMod p) := Pi.mulSingle m₀ a
  let rElt : G := κ (SpJoin.spPlaneTorus (r + 1) ζ v₀)
  have hrK : rElt ∈ K := by
    rw [← hκ.2.2.1]
    exact ⟨SpJoin.spPlaneTorus (r + 1) ζ v₀, rfl⟩
  have hrH : rElt ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
    apply ggSecFiveBPermZeta_spPlaneTorus_mem_H hp2 hF hκ hBs σ v₀
    intro l
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin (r + 1) =>
      Multiplicative (ZMod p)) (fun h => hm₀ ⟨l, h⟩) a
  have hrlam : rElt = κ (lam m₀ (ζ a)) := by
    dsimp only [rElt, v₀]
    rw [SpJoin.spPlaneTorus_mulSingle]
  refine ⟨rElt, ⟨hrH, hrK⟩, ?_⟩
  rw [hrlam]
  exact GGSpPlaneFrameOn.not_mem_centralizer_lam hκ hgne

private theorem ggSecFiveBPermZeta_centralizer_le_normalizer_commutator [Finite G]
    {p n r k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (σ : Fin (k + 1) → Fin (r + 1)) (hσs : ¬ Function.Surjective σ) :
    Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) ≤
      Subgroup.normalizer
        (⁅K ⊓ Subgroup.centralizer
            (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G),
          K ⊓ Subgroup.centralizer
            (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G)⁆ :
          Subgroup G) := by
  classical
  let H : Subgroup G := ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let M : Subgroup G := K ⊓ C
  have hyH : y ∈ H := ggSecFiveBPermZeta_y_mem_H hp2 hF hκ hyB hK σ
  have hex : ∃ m₀ : Fin (r + 1), m₀ ∉ Set.range σ := by
    by_contra h
    apply hσs
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨m₀, hm₀⟩ := hex
  obtain ⟨rElt, hrHK, hrnc⟩ :=
    exists_mem_H_inf_K_not_mem_centralizer hp2 hF hκ hBs σ hm₀
  have hCy : C ≤ Subgroup.centralizer ({y} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc y hyH).symm
  have hCnormK : C ≤ Subgroup.normalizer (K : Set G) := by
    intro c hc
    exact ggMem_normalizer_of_component
      (CFSG.Assembly.isComponentOf_iff_open.mpr hK) hrHK.2 hrnc
      (Subgroup.le_normalizer (hCy hc))
      (Subgroup.mem_centralizer_iff.mp hc rElt hrHK.1).symm
  have hCnormM : C ≤ Subgroup.normalizer (M : Set G) :=
    (le_inf hCnormK Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  intro c hc
  exact normalizer_commutator_of_normalizer (hCnormM hc)

private theorem center_range_sp_eq_bot {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {H : Type} [Group H] (φ : StatedSp n F →* H) (hinj : Function.Injective φ) :
    Subgroup.center φ.range = ⊥ := by
  have hZsp : Subgroup.center (StatedSp n F) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n
  have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
  rw [hZsp, Subgroup.map_bot] at he
  exact he.symm

theorem GGSecFiveBPermSpPlaneFrame.spPlaneTorus_eq_coordinate [Finite G]
    {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 2) ≃ Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (hBsEA : CFSG.Open.IsElemAbelian p Bs)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p (π 0))
    (v : Fin (r + 1) → Multiplicative (ZMod p)) :
    κ (SpJoin.spPlaneTorus (r + 1) ζ v) =
      (eta.symm ((Fin.cases 1 v) ∘ π.symm) : G) := by
  let b : ↥Bs := ⟨κ (SpJoin.spPlaneTorus (r + 1) ζ v),
    GGSpPlaneFrameOn.zetaTorus_mem_Bs hκ.planeFrameOn hBs v⟩
  have hbK : (b : G) ∈ K := by
    rw [← hκ.2.1]
    exact ⟨SpJoin.spPlaneTorus (r + 1) ζ v, rfl⟩
  have hZ : Subgroup.center K = ⊥ := by
    rw [← hκ.2.1]
    exact center_range_sp_eq_bot κ hκ.1
  have hb0 : eta b (π 0) = 1 :=
    (ggBs_mem_iff_coord_eq_one_of_bCoordinateBlock (Fact.out : p.Prime) hp2 hBsEA
      hyBs hy1 hKy hZ hN eta (π 0) hA b).mp hbK
  have hbη : eta b = (Fin.cases 1 v) ∘ π.symm := by
    funext j
    obtain ⟨i, rfl⟩ := π.surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact Fin.cases hb0 (fun m => GGSpPlaneFrameOn.zetaTorus_eta hκ.planeFrameOn hBs v m) i
  have hb : b = eta.symm ((Fin.cases 1 v) ∘ π.symm) :=
    eta.injective (hbη.trans (eta.apply_symm_apply _).symm)
  exact congrArg Subtype.val hb


theorem le_commutator_of_isSimpleGroup_of_ne_bot {R W : Subgroup G}
    (hWR : W ≤ R) [IsSimpleGroup ↥R] (hcenter : Subgroup.center ↥R = ⊥) (hWne : W ≠ ⊥) :
    R ≤ ⁅R, W⁆ := by
  have hHR : ⁅R, W⁆ ≤ R :=
    (Subgroup.commutator_mono le_rfl hWR).trans (Subgroup.commutator_le_self R)
  have hnormal : (⁅R, W⁆.subgroupOf R).Normal := by
    have hsup : R ⊔ W = R := sup_eq_left.mpr hWR
    have h := Subgroup.normal_subgroupOf_commutator_sup R W
    rwa [hsup] at h
  haveI : (⁅R, W⁆.subgroupOf R).Normal := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅R, W⁆.subgroupOf R) with hbot | htop
  · exfalso
    apply hWne
    have hbot' : ⁅R, W⁆ = ⊥ := by
      have hd : Disjoint ⁅R, W⁆ R := Subgroup.subgroupOf_eq_bot.mp hbot
      rw [disjoint_iff, inf_eq_left.mpr hHR] at hd
      exact hd
    have hle : R ≤ Subgroup.centralizer (W : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot'
    have hWcent : W ≤ ⊥ := by
      intro x hx
      have hxR : x ∈ R := hWR hx
      have hxcenter : (⟨x, hxR⟩ : ↥R) ∈ Subgroup.center ↥R := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (Subgroup.mem_centralizer_iff.mp (hle g.2) x hx).symm
      have hx1 : (⟨x, hxR⟩ : ↥R) = 1 := Subgroup.mem_bot.mp (hcenter ▸ hxcenter)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)
    exact le_bot_iff.mp hWcent
  · exact Subgroup.subgroupOf_eq_top.mp htop

private theorem ggSecFiveBPermZeta_W_ne_bot [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    Bs ⊓ (κ.comp (spEmbed (K := F) σ hσ)).range ≠ ⊥ := by
  classical
  intro hbot
  let a : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have ha_ne : a ≠ 1 := by
    intro ha
    have h0 : Multiplicative.ofAdd (0 : ZMod p) = 1 := rfl
    have h10 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (ha.trans h0.symm)
    exact one_ne_zero h10
  have hgne : ζ a ≠ 1 := by
    intro h
    apply ha_ne
    apply hκ.2.2.2.1
    rw [h, map_one]
  let m₀ : Fin (r + 1) := σ 0
  let v : Fin (r + 1) → Multiplicative (ZMod p) := Pi.mulSingle m₀ a
  let w0 : G := κ (SpJoin.spPlaneTorus (r + 1) ζ v)
  have hw0B : w0 ∈ Bs := GGSpPlaneFrameOn.zetaTorus_mem_Bs hκ hBs v
  have hw0R : w0 ∈ (κ.comp (spEmbed (K := F) σ hσ)).range := by
    have hv : ∀ i, i ∉ Set.range σ → v i = 1 := by
      intro i hi
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin (r + 1) =>
        Multiplicative (ZMod p)) (fun h => hi ⟨0, h.symm⟩) a
    obtain ⟨s, hs⟩ := spPlaneTorus_mem_range_spEmbed (ζ := ζ) hσ (v := v) hv
    exact ⟨s, by rw [MonoidHom.comp_apply, hs]⟩
  have hw0W : w0 ∈ Bs ⊓ (κ.comp (spEmbed (K := F) σ hσ)).range := ⟨hw0B, hw0R⟩
  have hw0ne : w0 ≠ 1 := by
    intro h1
    have hw0lam : w0 = κ (lam m₀ (ζ a)) := by
      dsimp only [w0, v]
      rw [SpJoin.spPlaneTorus_mulSingle]
    have hlam1 : lam m₀ (ζ a) = 1 := by
      apply hκ.2.1
      simpa [hw0lam] using h1
    exact hgne (by
      apply lam_injective m₀
      simpa using hlam1)
  have : w0 ∈ (⊥ : Subgroup G) := hbot ▸ hw0W
  exact hw0ne (Subgroup.mem_bot.mp this)

private theorem ggSecFiveBPermZeta_range_le_commutator_W [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ) :
    (κ.comp (spEmbed (K := F) σ hσ)).range ≤
      ⁅(κ.comp (spEmbed (K := F) σ hσ)).range,
        Bs ⊓ (κ.comp (spEmbed (K := F) σ hσ)).range⁆ := by
  let R : Subgroup G := (κ.comp (spEmbed (K := F) σ hσ)).range
  let W : Subgroup G := Bs ⊓ R
  have hWR : W ≤ R := fun x hx => hx.2
  have hφ : Function.Injective (κ.comp (spEmbed (K := F) σ hσ)) :=
    hκ.2.1.comp (spEmbed_injective hσ)
  haveI hSp : IsSimpleGroup (StatedSp (k + 1) F) :=
    hF.elim (fun h4 => CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le h4
      (by omega)) fun h3 => SpJoin.isSimpleGroup_statedSp_of_three_le h3
  haveI : IsSimpleGroup ↥R := (MonoidHom.ofInjective hφ).symm.isSimpleGroup
  have hcenter : Subgroup.center ↥R = ⊥ := center_range_sp_eq_bot _ hφ
  have hWne : W ≠ ⊥ := ggSecFiveBPermZeta_W_ne_bot hp2 hF hκ hBs σ hσ
  exact le_commutator_of_isSimpleGroup_of_ne_bot hWR hcenter hWne

theorem GGSpPlaneFrameOn.ggBlockComm_eq_range_of_or [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin (r + 1) → Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ)
    (hσs : ¬ Function.Surjective σ) :
    ggBlockComm Bs eta (Set.range fun l => ι (σ l)) = (κ.comp (spEmbed σ hσ)).range := by
  show ⁅Subgroup.centralizer (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) :
    Set G), Bs⁆ = _
  classical
  let H : Subgroup G := ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  let R : Subgroup G := (κ.comp (spEmbed (K := F) σ hσ)).range
  let W : Subgroup G := Bs ⊓ R
  let N : Subgroup G := ⁅K ⊓ Subgroup.centralizer (H : Set G),
    K ⊓ Subgroup.centralizer (H : Set G)⁆
  refine ggCommutator_centralizer_eq_of_mul (E := Bs) (H := H) (W := W) (N := N) (R := R)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨h, hhH, w, hwW, heq⟩ := ggSecFiveBPermZeta_gen hp2 hF hκ hBs σ hσ ⟨e, he⟩
    exact ⟨h, hhH, w, hwW, by simpa using heq⟩
  · intro x hx
    exact hx.1
  · exact ggSecFiveBPermZeta_centralizer_le_normalizer_commutator hp2 hF hκ hBs hyB hK σ hσs
  · intro x hx
    have hxR : x ∈ R := hx.2
    have hRperf : R = ⁅R, R⁆ := ggSecFiveBPermZeta_range_perfect hp2 hF hκ σ hσ
    have hxRR : x ∈ ⁅R, R⁆ := by
      rw [← hRperf]
      exact hxR
    have hRC : R ≤ Subgroup.centralizer (H : Set G) :=
      GGSpPlaneFrameOn.range_le_centralizer hκ σ hσ
    have hRM : R ≤ K ⊓ Subgroup.centralizer (H : Set G) := by
      intro z hz
      refine ⟨?_, hRC hz⟩
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
      rw [← hκ.2.2.1]
      exact ⟨spEmbed (K := F) σ hσ s, by rw [← hs, MonoidHom.comp_apply]⟩
    exact Subgroup.commutator_mono hRM hRM hxRR
  · exact ggSecFiveBPermZeta_commutator_le_range hp2 hκ σ hσ
  · exact GGSpPlaneFrameOn.range_le_centralizer hκ σ hσ
  · exact ggSecFiveBPermZeta_range_le_commutator_W hp2 hF hκ hBs σ hσ

theorem ggSecFiveBPermZeta_commutator_centralizer_eq_of_or [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ)
    (hσs : ¬ Function.Surjective σ) :
    ggBlockComm Bs eta (Set.range fun l => π (σ l).succ) = (κ.comp (spEmbed σ hσ)).range := by
  exact GGSpPlaneFrameOn.ggBlockComm_eq_range_of_or hp2 hF hBs hyB hK hκ.planeFrameOn
    σ hσ hσs

theorem ggSecFiveBPermZeta_commutator_centralizer_eq [Finite G] {p n r k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (σ : Fin (k + 1) → Fin (r + 1)) (hσ : Function.Injective σ)
    (hσs : ¬ Function.Surjective σ) :
    ggBlockComm Bs eta (Set.range fun l => π (σ l).succ) = (κ.comp (spEmbed σ hσ)).range :=
  GGSpPlaneFrameOn.ggBlockComm_eq_range_of_or hp2 (Or.inl hF) hBs hyB hK hκ.planeFrameOn
    σ hσ hσs

end CFSG.StandardType

end
