module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpPlaneBlocksTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import CFSG.LocalAnalysis.StandardType.GGSpJoinTwoElemCent
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUSp
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.SpJoin
open scoped MatrixGroups

variable {G : Type} [Group G] {p n m k : ℕ} {F : Type} [Field F]

namespace GGSpPlaneFrameOn

private theorem eta_apply_eq_one_of_isComponentOf [CharP F 2]
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin m → Fin n}
    {κ : StatedSp m F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (j : Fin m) :
    eta ⟨y, hyB⟩ (ι j) = 1 := by
  let b : ↥Bs := ⟨y, hyB⟩
  let T : StatedSp m F := zetaTorus eta ι ζ b
  have hyK : ∀ s : StatedSp m F, (y : G) * κ s * y⁻¹ = κ s := by
    intro s
    have hs : κ s ∈ K := by
      rw [← hκ.2.2.1]
      exact ⟨s, rfl⟩
    have hyc : κ s * y = y * κ s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hs)
    calc y * κ s * y⁻¹ = (κ s * y) * y⁻¹ := by rw [hyc]
      _ = κ s := mul_inv_cancel_right _ _
  have harg : ∀ s : StatedSp m F, T * s * T⁻¹ = s := by
    intro s
    have h1 := zetaFrame_conj hκ b s
    rw [hyK s] at h1
    exact hκ.2.1 h1.symm
  have hTcent : T ∈ Subgroup.center (StatedSp m F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    calc s * T = (T * s * T⁻¹) * T := by rw [harg s]
      _ = T * s := by group
  have hT1 : T = 1 := by
    have hbot := CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) m
    exact Subgroup.mem_bot.mp (hbot ▸ hTcent)
  have hfun : (fun l : Fin m => eta b (ι l)) = 1 := by
    apply CFSG.StandardType.TorC.spPlaneTorus_injective hκ.2.2.2.1 m
    simpa [T, zetaTorus] using hT1
  have := congrFun hfun j
  simpa [b] using this

private theorem mem_ggBsCoordZeroOn_of_isComponentOf [CharP F 2]
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin m → Fin n}
    {κ : StatedSp m F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (σ : Fin k → Fin m) :
    y ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
  change ((⟨y, hyB⟩ : ↥Bs) : G) ∈
    ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  rw [mem_ggBsCoordZeroOn]
  refine ⟨hyB, ?_⟩
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  exact eta_apply_eq_one_of_isComponentOf hκ hyB hK (σ l)

private theorem spEmbed_lam {a b : ℕ} {σ : Fin a → Fin b} (hσ : Function.Injective σ)
    (i : Fin a) (g : SL(2, F)) :
    spEmbed (K := F) σ hσ (lam i g) = lam (σ i) g := by
  rw [CFSG.StandardType.SympMinus.sympMinus_lam_eq_longBlock i g,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed_longBlock]
  exact (CFSG.StandardType.SympMinus.sympMinus_lam_eq_longBlock (σ i) g).symm

noncomputable def piExtend {M : Type*} [CommMonoid M] {a b : ℕ}
    (σ : Fin a → Fin b) : (Fin a → M) →* (Fin b → M) where
  toFun w i := if h : ∃ l, σ l = i then w (Classical.choose h) else 1
  map_one' := by
    funext i
    by_cases h : ∃ l, σ l = i <;> simp [h]
  map_mul' w w' := by
    funext i
    by_cases h : ∃ l, σ l = i <;> simp [h, Pi.mul_apply]

private theorem piExtend_mulSingle {M : Type*} [CommMonoid M] {a b : ℕ}
    {σ : Fin a → Fin b} (hσ : Function.Injective σ) (l : Fin a) (x : M) :
    piExtend σ (Pi.mulSingle l x) = Pi.mulSingle (σ l) x := by
  funext i
  change (if h : ∃ l', σ l' = i then
      (Pi.mulSingle (M := fun _ : Fin a => M) l x) (Classical.choose h) else 1) =
    (Pi.mulSingle (M := fun _ : Fin b => M) (σ l) x) i
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
      rw [if_neg hch, Pi.mulSingle_apply, if_neg hi]
  · rw [Pi.mulSingle_apply, if_neg]
    exact fun h' => h ⟨l, h'.symm⟩

private theorem spPlaneTorus_piExtend {p a b : ℕ}
    (ζ : Multiplicative (ZMod p) →* SL(2, F))
    {σ : Fin a → Fin b} (hσ : Function.Injective σ)
    (w : Fin a → Multiplicative (ZMod p)) :
    SpJoin.spPlaneTorus b ζ (piExtend σ w) =
      spEmbed (K := F) σ hσ (SpJoin.spPlaneTorus a ζ w) := by
  have hhom : (SpJoin.spPlaneTorus b ζ).comp (piExtend σ) =
      (spEmbed (K := F) σ hσ).comp (SpJoin.spPlaneTorus a ζ) := by
    refine MonoidHom.pi_ext (fun l x => ?_)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, piExtend_mulSingle hσ,
      SpJoin.spPlaneTorus_mulSingle, SpJoin.spPlaneTorus_mulSingle, spEmbed_lam]
  exact congrArg (fun f => f w) hhom

private theorem spPlaneTorus_mem_range_spEmbed {p a b : ℕ}
    (ζ : Multiplicative (ZMod p) →* SL(2, F))
    {σ : Fin a → Fin b} (hσ : Function.Injective σ)
    {v : Fin b → Multiplicative (ZMod p)}
    (hv : ∀ i, i ∉ Set.range σ → v i = 1) :
    SpJoin.spPlaneTorus b ζ v ∈ (spEmbed (K := F) σ hσ).range := by
  have hv' : piExtend σ (fun l => v (σ l)) = v := by
    funext i
    change (if h : ∃ l', σ l' = i then v (σ (Classical.choose h)) else 1) = v i
    split_ifs with h
    · rw [Classical.choose_spec h]
    · exact (hv i (by rintro ⟨l, hl⟩; exact h ⟨l, hl⟩)).symm
  refine ⟨SpJoin.spPlaneTorus a ζ (fun l => v (σ l)), ?_⟩
  rw [← spPlaneTorus_piExtend ζ hσ, hv']

private theorem zeta_ofAdd_one_ne_one [Fact p.Prime]
    {ζ : Multiplicative (ZMod p) →* SL(2, F)} (hζ : Function.Injective ζ) :
    ζ (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
  intro h
  exact CFSG.StandardType.StdSubSp.ofAdd_one_ne_one (Fact.out : p.Prime)
    (hζ (by rw [h, map_one]))

private theorem spPlaneTorus_mem_ggBsCoordZeroOn {a b : ℕ} [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin k → Fin a) (v : Fin a → Multiplicative (ZMod p))
    (hv : ∀ l, v (σ l) = 1) :
    κ (SpJoin.spPlaneTorus a ζ v) ∈
      ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
  have hB : κ (SpJoin.spPlaneTorus a ζ v) ∈ Bs :=
    zetaTorus_mem_Bs hκ hBs v
  change ((⟨κ (SpJoin.spPlaneTorus a ζ v), hB⟩ : ↥Bs) : G) ∈
    ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  rw [mem_ggBsCoordZeroOn]
  refine ⟨hB, ?_⟩
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  rw [zetaTorus_eta hκ hBs v (σ l)]
  exact hv l

private theorem exists_mem_ggBsCoordZeroOn_inf_range_not_mem_centralizer {a b : ℕ}
    [Fact p.Prime] [CharP F 2] {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin k → Fin a) {j : Fin a} (hj : j ∉ Set.range σ) :
    ∃ r ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) ⊓ K,
      r ∉ Subgroup.centralizer (K : Set G) := by
  let x : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have hgne : ζ x ≠ 1 := zeta_ofAdd_one_ne_one hκ.2.2.2.1
  let v₀ : Fin a → Multiplicative (ZMod p) := Pi.mulSingle j x
  let rElt : G := κ (SpJoin.spPlaneTorus a ζ v₀)
  have hrK : rElt ∈ K := by
    rw [← hκ.2.2.1]
    exact ⟨SpJoin.spPlaneTorus a ζ v₀, rfl⟩
  have hrH : rElt ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
    apply spPlaneTorus_mem_ggBsCoordZeroOn hκ hBs σ v₀
    intro l
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin a => Multiplicative (ZMod p))
      (fun h => hj ⟨l, h⟩) x
  have hrlam : rElt = κ (lam j (ζ x)) := by
    dsimp only [rElt, v₀]
    rw [SpJoin.spPlaneTorus_mulSingle]
  refine ⟨rElt, ⟨hrH, hrK⟩, ?_⟩
  rw [hrlam]
  exact not_mem_centralizer_lam hκ hgne

private theorem exists_mul_mem_ggBsCoordZeroOn_inf_range {a b : ℕ} [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) :
    ∀ b : ↥Bs, ∃ h ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)),
      ∃ w ∈ Bs ⊓ (κ.comp (spEmbed (K := F) σ hσ)).range, (b : G) = h * w := by
  classical
  intro b
  let H : Subgroup G := ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  let R : Subgroup G := (κ.comp (spEmbed (K := F) σ hσ)).range
  let v : Fin a → Multiplicative (ZMod p) :=
    fun j => if h : j ∈ Set.range σ then eta b (ι j) else 1
  let w : G := κ (SpJoin.spPlaneTorus a ζ v)
  have hwB : w ∈ Bs := zetaTorus_mem_Bs hκ hBs v
  have hvsupp : ∀ j, j ∉ Set.range σ → v j = 1 := by
    intro j hj
    dsimp only [v]
    rw [dif_neg hj]
  have hmem : SpJoin.spPlaneTorus a ζ v ∈
      (spEmbed (K := F) σ hσ).range :=
    spPlaneTorus_mem_range_spEmbed ζ hσ hvsupp
  have hwR : w ∈ R := by
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, by rw [MonoidHom.comp_apply, hs]⟩
  refine ⟨(b : G) * w⁻¹, ?_, w, ⟨hwB, hwR⟩, by group⟩
  have hhB : (b : G) * w⁻¹ ∈ Bs := Bs.mul_mem b.2 (Bs.inv_mem hwB)
  change ((⟨(b : G) * w⁻¹, hhB⟩ : ↥Bs) : G) ∈
    ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l))
  rw [mem_ggBsCoordZeroOn]
  refine ⟨hhB, ?_⟩
  intro c hc
  obtain ⟨l, rfl⟩ := hc
  have hh_eq : (⟨(b : G) * w⁻¹, hhB⟩ : ↥Bs) = b * ⟨w, hwB⟩⁻¹ := Subtype.ext rfl
  have hwcoord : eta ⟨w, hwB⟩ (ι (σ l)) = v (σ l) :=
    zetaTorus_eta hκ hBs v (σ l)
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

private theorem suppGroup_univ {n : ℕ} {F : Type} [Field F] :
    suppGroup (K := F) (Set.univ : Set (Fin n ⊕ Fin n)) = ⊤ := by
  ext x
  simp [mem_suppGroup, CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp]

private theorem spEmbed_surjective_of_surjective {a b : ℕ} {σ : Fin a → Fin b}
    (hσ : Function.Injective σ) (hσs : Function.Surjective σ) :
    Function.Surjective (spEmbed (K := F) σ hσ) := by
  rw [← MonoidHom.range_eq_top, range_spEmbed hσ]
  have hrange : Set.range (Sum.map σ σ) = Set.univ := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      rcases z with i | i
      · obtain ⟨j, rfl⟩ := hσs i
        exact ⟨Sum.inl j, rfl⟩
      · obtain ⟨j, rfl⟩ := hσs i
        exact ⟨Sum.inr j, rfl⟩
  rw [hrange, suppGroup_univ]

private theorem le_centralizer_of_surjective {a b k : ℕ} [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) (hσs : Function.Surjective σ) :
    K ≤ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
  have hsp := spEmbed_surjective_of_surjective (F := F) hσ hσs
  have hcomp : (κ.comp (spEmbed (K := F) σ hσ)).range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ hsp,
      Subgroup.map_top, hκ.2.2.1]
  rw [← hcomp]
  exact range_le_centralizer hκ σ hσ

private theorem exists_two_element_ne_one_statedSp {a : ℕ} (ha : 1 ≤ a)
    [CharP F 2] :
    ∃ s : StatedSp a F, s ≠ 1 ∧ ∃ e : ℕ, s ^ 2 ^ e = 1 := by
  classical
  let i : Fin a := ⟨0, ha⟩
  let g : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hg1 : g ≠ 1 := by
    intro h
    have h01 := congrArg (fun x : SL(2, F) =>
      (x : Matrix (Fin 2) (Fin 2) F) (0 : Fin 2) (1 : Fin 2)) h
    have h0 : ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) (0 : Fin 2) (1 : Fin 2) = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      simp
    rw [h0] at h01
    have h1 : (g : Matrix (Fin 2) (Fin 2) F) (0 : Fin 2) (1 : Fin 2) = 1 := rfl
    rw [h1] at h01
    exact one_ne_zero h01
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
    change (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [g, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hne : lam i g ≠ 1 := by
    intro h
    exact hg1 (CFSG.StandardType.SpJoin.lam_injective i (by simpa using h))
  have h2 : (lam i g) ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
  exact ⟨lam i g, hne, 1, by simpa using h2⟩

private theorem not_odd_orderOf_of_two_element {u : G}
    (hu : ∃ e : ℕ, u ^ 2 ^ e = 1) (hne : u ≠ 1) : ¬ Odd (orderOf u) := by
  rintro hodd
  obtain ⟨e, he⟩ := hu
  have hdvd : orderOf u ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one he
  have hcop : Nat.Coprime (orderOf u) (2 ^ e) :=
    ((Nat.coprime_two_left.mpr hodd).symm).pow_right e
  exact hne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd))

private theorem odd_orderOf_of_mem_centralizer_Bs [Finite G] {Bs : Subgroup G}
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G)))) {c : G}
    (hc : c ∈ Subgroup.centralizer (Bs : Set G)) : Odd (orderOf c) :=
  hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)

private theorem centralizer_Bs_of_centralizer_K_inf {a b k : ℕ} [Fact p.Prime]
    [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) {c : G}
    (hcC : c ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (hcK : c ∈ Subgroup.centralizer (K : Set G)) :
    c ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨h, hhH, w, hw, hb_eq⟩ :=
    exists_mul_mem_ggBsCoordZeroOn_inf_range hκ hBs σ hσ ⟨b, hb⟩
  have hwK : w ∈ K := by
    obtain ⟨s, hs⟩ := hw.2
    rw [← hκ.2.2.1]
    exact ⟨spEmbed (K := F) σ hσ s, by rw [← hs, MonoidHom.comp_apply]⟩
  have hch : h * c = c * h := Subgroup.mem_centralizer_iff.mp hcC h hhH
  have hcw : w * c = c * w := Subgroup.mem_centralizer_iff.mp hcK w hwK
  change ((⟨b, hb⟩ : ↥Bs) : G) * c = c * ((⟨b, hb⟩ : ↥Bs) : G)
  rw [hb_eq]
  calc h * w * c = h * (w * c) := by group
    _ = h * (c * w) := by rw [hcw]
    _ = (h * c) * w := by group
    _ = (c * h) * w := by rw [hch]
    _ = c * (h * w) := by group

private theorem exists_two_element_mem_map_conj {a b : ℕ} (ha : 1 ≤ a) [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {c : G} :
    ∃ x ∈ K.map (MulAut.conj c).toMonoidHom, x ≠ 1 ∧ ∃ e : ℕ, x ^ 2 ^ e = 1 := by
  obtain ⟨s, hsne, e, hse⟩ := exists_two_element_ne_one_statedSp (F := F) (a := a) ha
  let x : G := c * κ s * c⁻¹
  have hxKc : x ∈ K.map (MulAut.conj c).toMonoidHom := by
    refine ⟨κ s, ?_, rfl⟩
    rw [← hκ.2.2.1]
    exact ⟨s, rfl⟩
  have hxne : x ≠ 1 := by
    intro hx1
    have hκs1 : κ s = 1 := by
      calc κ s = c⁻¹ * x * c := by dsimp only [x]; group
        _ = 1 := by rw [hx1]; group
    exact hsne (hκ.2.1 (by simpa using hκs1))
  have hx2 : ∃ e : ℕ, x ^ 2 ^ e = 1 := by
    refine ⟨e, ?_⟩
    have hxpow : x ^ 2 ^ e = c * κ s ^ 2 ^ e * c⁻¹ := by
      dsimp only [x]
      change ((MulAut.conj c).toMonoidHom (κ s)) ^ 2 ^ e = _
      rw [← map_pow]
      rfl
    rw [hxpow, ← map_pow, hse, map_one, mul_one, mul_inv_cancel]
  exact ⟨x, hxKc, hxne, hx2⟩

private theorem false_of_ne_conj [Finite G] {a b k : ℕ} [Fact p.Prime] [CharP F 2]
    {Bs K H : Subgroup G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G)))) (ha : 1 ≤ a)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) {c : G}
    (hcC : c ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (hKleC : K ≤ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (hKc : CFSG.Assembly.IsComponentOf (K.map (MulAut.conj c).toMonoidHom) H)
    (hK : CFSG.Assembly.IsComponentOf K H)
    (hEq : K.map (MulAut.conj c).toMonoidHom ≠ K) : False := by
  have hcomm : ⁅K.map (MulAut.conj c).toMonoidHom, K⁆ = ⊥ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hKc hK with h | h
    · exact absurd h hEq
    · exact h
  have hKcK : K.map (MulAut.conj c).toMonoidHom ≤
      Subgroup.centralizer (K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hKcC : K.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC (hKleC hk)) (Subgroup.inv_mem _ hcC)
  obtain ⟨x, hxKc, hxne, hx2⟩ := exists_two_element_mem_map_conj (by omega) hκ (c := c)
  exact not_odd_orderOf_of_two_element hx2 hxne
    (odd_orderOf_of_mem_centralizer_Bs hodd
      (centralizer_Bs_of_centralizer_K_inf hκ hBs σ hσ (hKcC hxKc) (hKcK hxKc)))

private theorem centralizer_le_normalizer_K_of_surjective [Finite G] {a b k : ℕ}
    [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G)))) (ha : 1 ≤ a)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) (hσs : Function.Surjective σ) :
    Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  classical
  have hyH : y ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) :=
    mem_ggBsCoordZeroOn_of_isComponentOf hκ hyB hK σ
  have hKleC : K ≤ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) :=
    le_centralizer_of_surjective hκ σ hσ hσs
  intro c hc
  have hcY : c ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc y hyH).symm
  have hcy : c * y * c⁻¹ = y := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hcY, mul_assoc, mul_inv_cancel, mul_one]
  have hKc : CFSG.Assembly.IsComponentOf (K.map (MulAut.conj c).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj
      (CFSG.Assembly.isComponentOf_iff_open.mpr hK) c
    rwa [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hcy] at h
  by_cases hEq : K.map (MulAut.conj c).toMonoidHom = K
  · rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  · exfalso
    exact false_of_ne_conj hκ hBs hodd ha σ hσ hc hKleC hKc
      (CFSG.Assembly.isComponentOf_iff_open.mpr hK) hEq

theorem centralizer_ggBsCoordZeroOn_le_normalizer {a b : ℕ} [Finite G] [Fact p.Prime]
    [CharP F 2] {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G)))) (ha : 1 ≤ a)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) :
    Subgroup.centralizer
        (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  classical
  by_cases hσs : Function.Surjective σ
  · exact centralizer_le_normalizer_K_of_surjective hκ hBs hodd ha hyB hK σ hσ hσs
  · have hyH : y ∈ ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) :=
      mem_ggBsCoordZeroOn_of_isComponentOf hκ hyB hK σ
    have hex : ∃ j : Fin a, j ∉ Set.range σ := by
      by_contra h
      apply hσs
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hex
    obtain ⟨rElt, hrHK, hrnc⟩ :=
      exists_mem_ggBsCoordZeroOn_inf_range_not_mem_centralizer hκ hBs σ hj
    intro c hc
    have hCy : c ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc y hyH).symm
    exact ggMem_normalizer_of_component
      (CFSG.Assembly.isComponentOf_iff_open.mpr hK) hrHK.2 hrnc
      (Subgroup.le_normalizer hCy)
      (Subgroup.mem_centralizer_iff.mp hc rElt hrHK.1).symm

private theorem center_range_sp_eq_bot {a : ℕ} [CharP F 2]
    {H : Type} [Group H] (φ : StatedSp a F →* H) (hinj : Function.Injective φ) :
    Subgroup.center φ.range = ⊥ := by
  have hZsp : Subgroup.center (StatedSp a F) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot a
  have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
  rw [hZsp, Subgroup.map_bot] at he
  exact he.symm

private theorem conj_mem_range_of_mem_Bs {a b : ℕ} {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {h : G} (hhB : h ∈ Bs)
    {x : G} (hx : x ∈ K) :
    h * x * h⁻¹ ∈ K := by
  obtain ⟨s, rfl⟩ : ∃ s, κ s = x := by
    rw [← hκ.2.2.1] at hx
    exact hx
  rw [← hκ.2.2.1]
  exact ⟨_, (hκ.2.2.2.2 ⟨h, hhB⟩ s).symm⟩

private theorem ringEquiv_eq_refl_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2)
    (ρ : F ≃+* F) : ρ = RingEquiv.refl F := by
  have h : ∃! y : F, y ≠ 0 := (Nat.card_eq_two_iff' (0 : F)).mp hF
  obtain ⟨y, _, hyuniq⟩ := h
  have hy1 : y = 1 := (hyuniq 1 one_ne_zero).symm
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx1 : x = 1 := (hyuniq x hx).trans hy1
    rw [hx1]
    exact map_one ρ

private theorem mem_zpowers_of_odd_mul {Y : Type} [Group Y] [Finite Y] {a u : Y}
    (hcomm : a * u = u * a) (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (hodd : Odd (orderOf (a * u))) : u ∈ Subgroup.zpowers a := by
  obtain ⟨n, hn⟩ := hu
  set m : ℕ := orderOf (a * u) with hm
  have hmu : (a * u) ^ m = 1 := pow_orderOf_eq_one _
  have hc : Commute a u := hcomm
  rw [hc.mul_pow] at hmu
  have hum : u ^ m = (a ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hmu
  have hord : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (orderOf u) m :=
    Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd))
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := u) (n := m) hcop.symm
  rw [← hk, hum, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _

private theorem exists_mem_K_conj_eq [Finite F] {a b : ℕ} [CharP F 2]
    (hF : Nat.card F = 2) (ha : 3 ≤ a)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G)) :
    ∃ l ∈ K, ∀ x ∈ K, t * x * t⁻¹ = l * x * l⁻¹ := by
  classical
  let e : StatedSp a F ≃* K :=
    (MonoidHom.ofInjective hκ.2.1).trans (MulEquiv.subgroupCongr hκ.2.2.1)
  let cAut : MulAut K := Subgroup.normalizerMonoidHom (H := K) ⟨t, htN⟩
  let β : MulAut (StatedSp a F) := (e.trans cAut).trans e.symm
  obtain ⟨s, ρ, hβ⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp (K := F) (n := a) ha β
  have hρ : ρ = RingEquiv.refl F := ringEquiv_eq_refl_of_card_two hF ρ
  refine ⟨κ s, ?_, ?_⟩
  · rw [← hκ.2.2.1]
    exact ⟨s, rfl⟩
  · intro x hx
    obtain ⟨g, rfl⟩ : ∃ g, κ g = x := by
      rw [← hκ.2.2.1] at hx
      exact hx
    have he_apply : ∀ y, ((e y : K) : G) = κ y := fun y => rfl
    have hc : ((cAut (e g) : K) : G) = t * κ g * t⁻¹ := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp [he_apply]
    have heβ : e (β g) = cAut (e g) := by
      simp [β]
    calc t * κ g * t⁻¹ = ((cAut (e g) : K) : G) := hc.symm
      _ = ((e (β g) : K) : G) := by rw [heβ]
      _ = κ (β g) := he_apply (β g)
      _ = κ (s * g * s⁻¹) := by
          rw [show β g = s * g * s⁻¹ from by
            have hfield : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp a F)
                (RingEquiv.refl F) = 1 := map_one _
            rw [hβ g, hρ, hfield, MulAut.one_apply]]
      _ = κ s * κ g * (κ s)⁻¹ := by rw [map_mul, map_mul, map_inv]

private theorem conj_action_eq_of_mem_centralizer {a b : ℕ} [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {t l h : G}
    (hhB : h ∈ Bs) (hht : h * t = t * h) (hlK : l ∈ K)
    (hconj : ∀ x ∈ K, t * x * t⁻¹ = l * x * l⁻¹) :
    h * l * h⁻¹ ∈ K ∧
      ∀ x ∈ K, (h * l * h⁻¹) * x * (h * l * h⁻¹)⁻¹ = l * x * l⁻¹ := by
  have hhlK : h * l * h⁻¹ ∈ K := conj_mem_range_of_mem_Bs hκ hhB hlK
  refine ⟨hhlK, ?_⟩
  intro x hx
  have hx' : h⁻¹ * x * h ∈ K := by
    have h2 := conj_mem_range_of_mem_Bs hκ (Bs.inv_mem hhB) hx
    simpa only [inv_inv] using h2
  calc (h * l * h⁻¹) * x * (h * l * h⁻¹)⁻¹
      = h * l * (h⁻¹ * x * h) * l⁻¹ * h⁻¹ := by
          simp only [mul_inv_rev, inv_inv]
          group
    _ = h * (t * (h⁻¹ * x * h) * t⁻¹) * h⁻¹ := by
          rw [hconj _ hx']
          group
    _ = t * x * t⁻¹ := by
          have hht_inv : t⁻¹ * h⁻¹ = h⁻¹ * t⁻¹ :=
            (Commute.inv_left (Commute.inv_right (show Commute h t from hht))).symm.eq
          calc h * (t * (h⁻¹ * x * h) * t⁻¹) * h⁻¹
              = (h * t) * (h⁻¹ * x * h) * (t⁻¹ * h⁻¹) := by group
            _ = t * (h * (h⁻¹ * x * h) * h⁻¹) * t⁻¹ := by
                  rw [hht, hht_inv]
                  group
            _ = t * x * t⁻¹ := by group
    _ = l * x * l⁻¹ := hconj x hx

private theorem mem_centralizer_of_conj_eq {a b k : ℕ} [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) (σ : Fin k → Fin a) {t l : G}
    (htC : t ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (hlK : l ∈ K)
    (hconj : ∀ x ∈ K, t * x * t⁻¹ = l * x * l⁻¹) :
    l ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhB : h ∈ Bs := ggBsCoordZeroOn_le _ _ _ hh
  have hht : h * t = t * h := Subgroup.mem_centralizer_iff.mp htC h hh
  obtain ⟨hhlK, hconjK⟩ :=
    conj_action_eq_of_mem_centralizer hκ hhB hht hlK hconj
  let z : G := l⁻¹ * (h * l * h⁻¹)
  have hzK : z ∈ K := K.mul_mem (K.inv_mem hlK) hhlK
  have hzcent : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    change (x : G) * z = z * (x : G)
    have hzx : z * (x : G) * z⁻¹ = (x : G) := by
      dsimp only [z]
      calc l⁻¹ * (h * l * h⁻¹) * (x : G) * (l⁻¹ * (h * l * h⁻¹))⁻¹
          = l⁻¹ * ((h * l * h⁻¹) * (x : G) * (h * l * h⁻¹)⁻¹) * l := by group
        _ = l⁻¹ * (l * (x : G) * l⁻¹) * l := by rw [hconjK (x : G) x.2]
        _ = (x : G) := by group
    have hzx' : z * (x : G) = (x : G) * z := by
      calc z * (x : G) = (z * (x : G) * z⁻¹) * z := by group
        _ = (x : G) * z := by rw [hzx]
    exact hzx'.symm
  have hz1 : z = 1 := by
    have hbot : Subgroup.center K = ⊥ := by
      rw [← hκ.2.2.1]
      exact center_range_sp_eq_bot κ hκ.2.1
    have h1 := Subgroup.mem_bot.mp (hbot ▸ hzcent)
    simpa using congrArg (fun y : K => (y : G)) h1
  have hhl_eq : h * l * h⁻¹ = l := by
    dsimp only [z] at hz1
    calc h * l * h⁻¹ = l * (l⁻¹ * (h * l * h⁻¹)) := by group
      _ = l * 1 := by rw [hz1]
      _ = l := mul_one l
  calc h * l = (h * l * h⁻¹) * h := by group
    _ = l * h := by rw [hhl_eq]

private theorem centralizer_K_of_conj {K : Subgroup G} {t l : G}
    (hconj : ∀ x ∈ K, t * x * t⁻¹ = l * x * l⁻¹) :
    l⁻¹ * t ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' := hconj x hx
  calc x * (l⁻¹ * t) = l⁻¹ * (l * x * l⁻¹) * t := by group
    _ = l⁻¹ * (t * x * t⁻¹) * t := by rw [← hx']
    _ = (l⁻¹ * t) * x := by group

private theorem centralizer_H_of_conj {a b k : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} (σ : Fin k → Fin a) {t l : G}
    (htC : t ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (hlC : l ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G)) :
    l⁻¹ * t ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hl : h * l = l * h := Subgroup.mem_centralizer_iff.mp hlC h hh
  have ht : h * t = t * h := Subgroup.mem_centralizer_iff.mp htC h hh
  have hl' : h * l⁻¹ = l⁻¹ * h := (Commute.inv_right (show Commute h l from hl)).eq
  calc h * (l⁻¹ * t) = (h * l⁻¹) * t := by group
    _ = (l⁻¹ * h) * t := by rw [hl']
    _ = l⁻¹ * (h * t) := by group
    _ = l⁻¹ * (t * h) := by rw [ht]
    _ = (l⁻¹ * t) * h := by group

private theorem mem_range_of_zpowers {a b k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) {t l : G} (hlK : l ∈ K)
    (htC : t ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (hmem : t ∈ Subgroup.zpowers l) (he : ∃ e : ℕ, t ^ 2 ^ e = 1) :
    t ∈ (κ.comp (spEmbed (K := F) σ hσ)).range := by
  obtain ⟨e, he⟩ := he
  obtain ⟨s, hs⟩ : ∃ s, κ s = l := by
    rw [← hκ.2.2.1] at hlK
    exact hlK
  rw [← hs] at hmem
  rw [← MonoidHom.map_zpowers] at hmem
  obtain ⟨s₀, _, hs₀eq⟩ := Subgroup.mem_map.mp hmem
  have hs₀2 : s₀ ^ 2 ^ e = 1 := by
    apply hκ.2.1
    rw [map_pow, hs₀eq, he, map_one]
  let x : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have hlamH : ∀ j : Fin a, j ∉ Set.range σ →
      κ (lam j (ζ x)) ∈
        ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) := by
    intro j hj
    have hv : ∀ l, (Pi.mulSingle j x : Fin a → Multiplicative (ZMod p)) (σ l) = 1 := by
      intro l
      exact Pi.mulSingle_eq_of_ne
        (M := fun _ : Fin a => Multiplicative (ZMod p))
        (fun h => hj ⟨l, h⟩) x
    have hmemH := spPlaneTorus_mem_ggBsCoordZeroOn hκ hBs σ (Pi.mulSingle j x) hv
    rwa [spPlaneTorus_mulSingle] at hmemH
  have hcommlam : ∀ j, j ∉ Set.range σ → s₀ * lam j (ζ x) = lam j (ζ x) * s₀ := by
    intro j hj
    apply hκ.2.1
    rw [map_mul, map_mul, hs₀eq]
    exact (Subgroup.mem_centralizer_iff.mp htC _ (hlamH j hj)).symm
  have hmemR : s₀ ∈ (spEmbed (K := F) σ hσ).range :=
    mem_range_spEmbed_of_commute_lam (zeta_trace_ne_zero hp2 hκ) σ hσ hcommlam
      ⟨e, hs₀2⟩
  obtain ⟨s₁, hs₁⟩ := hmemR
  exact ⟨s₁, by rw [MonoidHom.comp_apply, hs₁, hs₀eq]⟩

private theorem mem_zpowers_of_conj [Finite G] {K : Subgroup G} {t l c : G}
    (hcK : c ∈ Subgroup.centralizer (K : Set G)) (hlK : l ∈ K)
    (hc : c = l⁻¹ * t) (he : ∃ e : ℕ, t ^ 2 ^ e = 1)
    (hcodd : Odd (orderOf c)) : t ∈ Subgroup.zpowers l := by
  have hct : Commute l c := Subgroup.mem_centralizer_iff.mp hcK l hlK
  have ht_eq : t = l * c := by rw [hc]; group
  have hcomm : l⁻¹ * t = t * l⁻¹ := by
    rw [ht_eq]
    calc l⁻¹ * (l * c) = c := by group
      _ = (l * c) * l⁻¹ := by rw [hct.eq]; group
  have hcodd' : Odd (orderOf (l⁻¹ * t)) := by rw [← hc]; exact hcodd
  have hmem : t ∈ Subgroup.zpowers (l⁻¹) :=
    mem_zpowers_of_odd_mul hcomm he hcodd'
  rwa [Subgroup.zpowers_inv] at hmem

private theorem range_le_ggBlockTwo {a b k : ℕ} [Fact p.Prime] [CharP F 2]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))}
    {ι : Fin a → Fin b} {κ : StatedSp a F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin k → Fin a) (hσ : Function.Injective σ) :
    (κ.comp (spEmbed (K := F) σ hσ)).range ≤
      ggBlockTwo Bs eta (Set.range fun l => ι (σ l)) := by
  rw [show (κ.comp (spEmbed (K := F) σ hσ)).range =
      (⊤ : Subgroup (StatedSp k F)).map (κ.comp (spEmbed (K := F) σ hσ)) by
    rw [Subgroup.map_top]]
  have hgen := CFSG.StandardType.RootCentSp.top_le_closure_statedSp (F := F) k
  calc (⊤ : Subgroup (StatedSp k F)).map (κ.comp (spEmbed (K := F) σ hσ))
      ≤ (Subgroup.closure {x | ∃ e : ℕ, x ^ 2 ^ e = 1}).map
          (κ.comp (spEmbed (K := F) σ hσ)) := Subgroup.map_mono hgen
    _ = Subgroup.closure ((κ.comp (spEmbed (K := F) σ hσ)) ''
          {x | ∃ e : ℕ, x ^ 2 ^ e = 1}) := MonoidHom.map_closure _ _
    _ ≤ ggBlockTwo Bs eta (Set.range fun l => ι (σ l)) := by
        rw [Subgroup.closure_le]
        rintro _ ⟨x, ⟨e, he⟩, rfl⟩
        refine Subgroup.subset_closure ⟨?_, ⟨e, ?_⟩⟩
        · exact range_le_centralizer hκ σ hσ (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
        · rw [← map_pow, he, map_one]

private theorem mem_range_of_two_element [Finite G] [Finite F] {a b k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) [CharP F 2] (hF : Nat.card F = 2) (ha : 3 ≤ a)
    {Bs K : Subgroup G} {y : G}
    {eta : ↥Bs ≃* (Fin b → Multiplicative (ZMod p))} {ι : Fin a → Fin b}
    {κ : StatedSp a F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G))))
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (σ : Fin k → Fin a) (hσ : Function.Injective σ)
    {t : G}
    (htC : t ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G))
    (he : ∃ e : ℕ, t ^ 2 ^ e = 1) :
    t ∈ (κ.comp (spEmbed (K := F) σ hσ)).range := by
  have htN : t ∈ Subgroup.normalizer (K : Set G) :=
    centralizer_ggBsCoordZeroOn_le_normalizer hκ hBs hodd (by omega) hyB hK σ hσ htC
  obtain ⟨l, hlK, hconj⟩ := exists_mem_K_conj_eq hF ha hκ htN
  have hlC : l ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) :=
    mem_centralizer_of_conj_eq hκ σ htC hlK hconj
  let c : G := l⁻¹ * t
  have hcK : c ∈ Subgroup.centralizer (K : Set G) := by
    dsimp only [c]
    exact centralizer_K_of_conj hconj
  have hcC : c ∈ Subgroup.centralizer
      (ggBsCoordZeroOn Bs eta (Set.range fun l => ι (σ l)) : Set G) := by
    dsimp only [c]
    exact centralizer_H_of_conj σ htC hlC
  have hcBs : c ∈ Subgroup.centralizer (Bs : Set G) :=
    centralizer_Bs_of_centralizer_K_inf hκ hBs σ hσ hcC hcK
  have hcodd : Odd (orderOf c) := odd_orderOf_of_mem_centralizer_Bs hodd hcBs
  have hmem : t ∈ Subgroup.zpowers l :=
    mem_zpowers_of_conj hcK hlK rfl he hcodd
  exact mem_range_of_zpowers hp2 hκ hBs σ hσ hlK htC hmem he

end GGSpPlaneFrameOn

open GGSpPlaneFrameOn

theorem ggBlockTwo_eq_range [Finite G] {p n m k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) (hm : 3 ≤ m)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G))))
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin m → Fin n}
    {κ : StatedSp m F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    (σ : Fin k → Fin m) (hσ : Function.Injective σ) :
    ggBlockTwo Bs eta (Set.range fun l => ι (σ l)) = (κ.comp (spEmbed (K := F) σ hσ)).range := by
  refine le_antisymm ?_ ?_
  · rw [ggBlockTwo, Subgroup.closure_le]
    rintro t ⟨htC, e, he⟩
    exact mem_range_of_two_element hp2 hF hm hκ hBs hodd hyB hK σ hσ htC ⟨e, he⟩
  · exact range_le_ggBlockTwo hκ σ hσ

theorem ggBlockTwo_eq_range_of_planeFrame [Finite G] {p n r k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) (hr : 2 ≤ r)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G))))
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (σ : Fin k → Fin (r + 1)) (hσ : Function.Injective σ) :
    ggBlockTwo Bs eta (Set.range fun l => π (σ l).succ) =
      (κ.comp (spEmbed (K := F) σ hσ)).range :=
  ggBlockTwo_eq_range hp2 hF (by omega) hBs hodd hyB hK hκ.planeFrameOn σ hσ

theorem ggBlockTwo_compl_eq_of_planeFrame [Finite G] {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) (hr : 2 ≤ r)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G))))
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ) :
    ggBlockTwo Bs eta {π 0}ᶜ = K := by
  have hrange : Set.range (fun l : Fin (r + 1) => π l.succ) = {π 0}ᶜ := by
    ext i
    constructor
    · rintro ⟨l, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact Fin.succ_ne_zero l (π.injective h)
    · intro hi
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hi
      obtain ⟨j, hj⟩ := π.surjective i
      have hj0 : j ≠ 0 := by
        intro h
        exact hi (by rw [← hj, h])
      obtain ⟨l, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
      exact ⟨l, hj⟩
  have hsp : Function.Surjective
      (spEmbed (K := F) (fun l : Fin (r + 1) => l) Function.injective_id) :=
    spEmbed_surjective_of_surjective (F := F) (σ := fun l : Fin (r + 1) => l)
      Function.injective_id Function.surjective_id
  have hcomp : (κ.comp (spEmbed (K := F) (fun l : Fin (r + 1) => l)
      Function.injective_id)).range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ hsp,
      Subgroup.map_top, hκ.2.1]
  have h := ggBlockTwo_eq_range_of_planeFrame hp2 hF hr hBs hodd hyB hK hκ
    (σ := fun l : Fin (r + 1) => l) (hσ := Function.injective_id)
  rw [hrange, hcomp] at h
  exact h

private theorem map_conj_centralizer (H : Subgroup G) (g : G) :
    (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨h, hh, rfl⟩
    show g * h * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * h * g⁻¹)
    calc g * h * g⁻¹ * (g * y * g⁻¹) = g * (h * y) * g⁻¹ := by group
      _ = g * (y * h) * g⁻¹ := by rw [hy' h hh]
      _ = g * y * g⁻¹ * (g * h * g⁻¹) := by group
  · intro hx
    have hx' := Subgroup.mem_centralizer_iff.mp hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      have hc := hx' (g * h * g⁻¹) ⟨h, hh, rfl⟩
      calc h * (g⁻¹ * x * g) = g⁻¹ * ((g * h * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * h * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * x * g * h := by group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem ggBlockTwo_map_conj {p n : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ) (S : Set (Fin n)) :
    (ggBlockTwo Bs eta S).map (MulAut.conj g).toMonoidHom = ggBlockTwo Bs eta (τ '' S) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hH : (ggBsCoordZeroOn Bs eta S).map (MulAut.conj g).toMonoidHom =
      ggBsCoordZeroOn Bs eta (τ '' S) := ggBsCoordZeroOn_map_conj hg hτ S
  have hC : (Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G)).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (ggBsCoordZeroOn Bs eta (τ '' S) : Set G) := by
    rw [map_conj_centralizer, hH]
  rw [ggBlockTwo, ggBlockTwo, MonoidHom.map_closure, ← hC]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, e, hy2⟩, rfl⟩
    exact ⟨⟨y, hyC, rfl⟩, e, by rw [← map_pow, hy2, map_one]⟩
  · rintro ⟨⟨y, hyC, rfl⟩, e, hy2⟩
    exact ⟨y, ⟨hyC, e, hinj (by rw [map_pow, hy2, map_one])⟩, rfl⟩

end CFSG.StandardType

end
