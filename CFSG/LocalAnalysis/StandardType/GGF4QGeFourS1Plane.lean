module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TorusPSp
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import CFSG.LieType.CurtisTits.Perfect
import CFSG.Timmesfeld.Transvection.PresSp
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.LieType.Universal.Symplectic (rootGroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.SymplecticPilot (complSp rootTorusSp rootTorusHom)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (shortBlock longBlock)

section Torus

variable {U : Type} [Group U] (D : UniversalRootDatum U)

theorem ggWeylLift_inv_conj_mem_ggTorus {ν : GGWeyl D →* U} (hν : GGWeylLift D ν) (u : GGWeyl D)
    {t : U} (ht : t ∈ ggTorus D) : (ν u)⁻¹ * t * ν u ∈ ggTorus D := by
  have key : ∀ s ∈ ggTorus D, ∀ γ ∈ D.roots, ∀ z ∈ D.rootGroup γ,
      (ν u)⁻¹ * s * ν u * z * ((ν u)⁻¹ * s * ν u)⁻¹ ∈ D.rootGroup γ := by
    intro s hs γ hγ z hz
    have huγ : weylAction D.isFiniteType u γ ∈ D.roots :=
      CFSG.LieType.CurtisTits.weylAction_mem_roots hγ u
    have h1 : ν u * z * (ν u)⁻¹ ∈ D.rootGroup (weylAction D.isFiniteType u γ) :=
      hν.conj_mem u γ hγ z hz
    have hsN : s ∈ Subgroup.normalizer (D.rootGroup (weylAction D.isFiniteType u γ) : Set U) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hs
      exact hs _ huγ
    have h2 : s * (ν u * z * (ν u)⁻¹) * s⁻¹ ∈ D.rootGroup (weylAction D.isFiniteType u γ) :=
      (Subgroup.mem_normalizer_iff.mp hsN _).mp h1
    have h3 := hν.conj_mem u⁻¹ _ huγ _ h2
    rw [weylAction_inv_apply_apply, map_inv] at h3
    have e : (ν u)⁻¹ * s * ν u * z * ((ν u)⁻¹ * s * ν u)⁻¹ =
        (ν u)⁻¹ * (s * (ν u * z * (ν u)⁻¹) * s⁻¹) * ((ν u)⁻¹)⁻¹ := by group
    rw [e]
    exact h3
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key t ht γ hγ z
  · intro hz
    have h := key t⁻¹ (inv_mem ht) γ hγ _ hz
    have e : (ν u)⁻¹ * t⁻¹ * ν u * ((ν u)⁻¹ * t * ν u * z * ((ν u)⁻¹ * t * ν u)⁻¹) *
        ((ν u)⁻¹ * t⁻¹ * ν u)⁻¹ = z := by group
    rwa [e] at h

end Torus

section Sp

variable {F : Type} [Field F]

theorem complSp_zero_eq_rankOne_sup :
    complSp F (0 : Fin 3) = rankOne (rootGroup 3 F) 1 ⊔ rankOne (rootGroup 3 F) 2 := by
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have e1 : rankOne (rootGroup 3 F) 1 = (shortBlock F h12).range :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.range_shortBlock_eq_rankOne
      (k := (1 : Fin 3)) (by decide)).symm
  have e2 : rankOne (rootGroup 3 F) 2 = (longBlock F 3 2).range :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.range_longBlock_eq_rankOne
      (k := (2 : Fin 3)) (by decide)).symm
  have hc : ((CFSG.ClassicalInvolution.Models.SymplecticPairs.coords (0 : Fin 3))ᶜ :
      Set (Fin 3 ⊕ Fin 3)) =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.coords 1 ∪
        CFSG.ClassicalInvolution.Models.SymplecticPairs.coords 2 := by
    ext a
    simp only [Set.mem_compl_iff, Set.mem_union,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.mem_coords]
    rcases a with i | i <;> fin_cases i <;> simp
  rw [e1, e2, CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_sup_longBlock h12,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.range_spEmbed,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.range_pairMap, ← hc]
  rfl

theorem commute_rootTorusHom_of_mem_ggTorus {t : StatedSp 3 F}
    (ht : t ∈ ggTorus (Symplectic.rootDatum 3 F)) (κ : Fˣ) :
    t * rootTorusHom F 3 0 κ = rootTorusHom F 3 0 κ * t := by
  apply mat_injective
  have hd : mat 3 F t = Matrix.diagonal fun a => mat 3 F t a a := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab, CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply]
      exact ClassicalPosition.ggTorus_apply_eq_zero_PSp 3 F ht hab
  rw [map_mul, map_mul, CFSG.SeitzReduction.SymplecticPilot.rootTorusHom_apply,
    CFSG.SeitzReduction.SymplecticPilot.mat_diagSp, hd, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

end Sp

theorem mem_ggHyperplane_of_mem_centralizer_ggRankOneIn {G : Type} [Group G] [Finite G]
    {X Bs : Subgroup G} {s : MulAut ↥Bs} (hs : s ∈ ggAutomizer X Bs) (hs2 : s ^ 2 = 1) {b : G}
    (hb : b ∈ Bs) (hbc : b ∈ Subgroup.centralizer (ggRankOneIn X Bs s : Set G)) :
    b ∈ ggHyperplane Bs s := by
  obtain ⟨g, hgS, -, hg⟩ := mem_ggAutomizer_iff.mp (mem_ggAutomizer_ggRankOneIn hs hs2)
  refine ⟨⟨b, hb⟩, ?_, rfl⟩
  change s ⟨b, hb⟩ = ⟨b, hb⟩
  apply Subtype.ext
  rw [hg ⟨b, hb⟩]
  have hgb : g * b = b * g := Subgroup.mem_centralizer_iff.mp hbc g hgS
  change g * b * g⁻¹ = b
  rw [hgb]
  group


section Plane

theorem exists_sp4Plane_of_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    {ψ : (ggU .PSp 3 f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .PSp 3 f).K)
    (hrange : ψ.range = X) (hpos : GGTableBPos p Bs X .PSp 3 f ψ)
    (htor : ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .PSp 3 f).D, ∀ z, b * ψ z * b⁻¹ = ψ (t * z * t⁻¹))
    (w : CoxeterMatrix.F₄.Group) {r u : MulAut ↥Bs}
    (hr : r = ((e (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hrX : r ∈ ggAutomizer X Bs) (huX : u ∈ ggAutomizer X Bs)
    (hDX : ¬ ggHyperplane Bs r ⊓ ggHyperplane Bs u ≤ Subgroup.centralizer (X : Set G)) :
    ∃ J' : Subgroup G,
      LargeEvenLayer (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) = J' ∧
      CFSG.Assembly.IsComponentOf J' (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) ∧
      Bs ⊓ Subgroup.centralizer (J' : Set G) = ggHyperplane Bs r ⊓ ggHyperplane Bs u ∧
      ggRankOneIn X Bs r ≤ J' ∧ ggRankOneIn X Bs u ≤ J' ∧
      Nonempty (↥J' ≃* StatedSp 2 (GaloisField 2 f)) := by
  set D' : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hD'
  have hf1 : 1 ≤ f := by omega
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have hr2 : r ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 ⟨w, 2, hr⟩).1
  have hu2 : u ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 ⟨w, 1, hu⟩).1
  obtain ⟨ν, v, c, d, hν, -, -, h4, hSi, hSj⟩ :=
    exists_simplePair_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hXA hf1 hpos w h21
      (hr ▸ hrX) (hu ▸ huX)
  rw [← hr] at hSi
  rw [← hu] at hSj
  have hcd : c = 2 ∧ d = 1 ∨ c = 1 ∧ d = 2 := h4 (by decide)
  set ψ' : (ggU .PSp 3 f).K →* G := (MulAut.conj (ψ (ν v))).toMonoidHom.comp ψ with hψ'
  have hψ'apply : ∀ z, ψ' z = ψ (ν v * z * (ν v)⁻¹) := fun z => by
    rw [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_mul, map_inv]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot
      (K := GaloisField 2 f) (n := 3) (by norm_num)).le
  have hinj' : Function.Injective ψ' := (MulAut.conj (ψ (ν v))).injective.comp hinj
  have hrange' : ψ'.range = X := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, (hψ'apply z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(ν v)⁻¹ * z * ν v, ?_⟩
      rw [hψ'apply]
      exact congrArg ψ (by group)
  have htor' : ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .PSp 3 f).D,
      ∀ z, b * ψ' z * b⁻¹ = ψ' (t * z * t⁻¹) := by
    intro b hb
    obtain ⟨t, ht, htz⟩ := htor b hb
    refine ⟨(ν v)⁻¹ * t * ν v, ggWeylLift_inv_conj_mem_ggTorus _ hν v ht, fun z => ?_⟩
    rw [hψ'apply, hψ'apply, htz]
    exact congrArg ψ (by group)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let φ : StatedSp 3 (GaloisField 2 f) →* G := ψ'
  have hφinj : Function.Injective φ := hinj'
  have hφrange : φ.range = X := hrange'
  have hφtor : ∀ b ∈ Bs, ∃ t : StatedSp 3 (GaloisField 2 f),
      t ∈ ggTorus (Symplectic.rootDatum 3 (GaloisField 2 f)) ∧
        ∀ z, b * φ z * b⁻¹ = φ (t * z * t⁻¹) := fun b hb => by
    obtain ⟨t, ht, htz⟩ := htor' b hb
    exact ⟨t, ht, htz⟩
  have hφSi : ggRankOneIn X Bs r = (rankOne (rootGroup 3 (GaloisField 2 f)) c).map φ := hSi
  have hφSj : ggRankOneIn X Bs u = (rankOne (rootGroup 3 (GaloisField 2 f)) d).map φ := hSj
  clear_value φ
  clear hSi hSj htor' hrange' hinj' hψ'apply
  set J' : Subgroup G := (complSp (GaloisField 2 f) (0 : Fin 3)).map φ with hJ'
  have hJ'eq : J' = ggRankOneIn X Bs r ⊔ ggRankOneIn X Bs u := by
    rw [hJ', complSp_zero_eq_rankOne_sup, Subgroup.map_sup, hφSi, hφSj]
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sup_comm _ _
    · rfl
  have hSrX : ggRankOneIn X Bs r ≤ X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    ggOTwoPrime_le _
  have hSuX : ggRankOneIn X Bs u ≤ X ⊓ Subgroup.centralizer (ggHyperplane Bs u : Set G) :=
    ggOTwoPrime_le _
  have hJX : J' ≤ X := by
    rw [hJ'eq]
    exact sup_le (hSrX.trans inf_le_left) (hSuX.trans inf_le_left)
  have hJD : J' ≤ Subgroup.centralizer (D' : Set G) := by
    rw [hJ'eq]
    exact sup_le (hSrX.trans (inf_le_right.trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))))
      (hSuX.trans (inf_le_right.trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))))
  have hDJ : D' ≤ Subgroup.centralizer (J' : Set G) := Subgroup.le_centralizer_iff.mp hJD
  have hDBs : D' ≤ Bs := by
    rintro b ⟨⟨c, -, rfl⟩, -⟩
    exact c.2
  have hcent : Bs ⊓ Subgroup.centralizer (J' : Set G) = D' := by
    refine le_antisymm ?_ (le_inf hDBs hDJ)
    rintro b ⟨hb, hbc⟩
    have hrJ : ggRankOneIn X Bs r ≤ J' := by rw [hJ'eq]; exact le_sup_left
    have huJ : ggRankOneIn X Bs u ≤ J' := by rw [hJ'eq]; exact le_sup_right
    exact ⟨mem_ggHyperplane_of_mem_centralizer_ggRankOneIn hrX hr2 hb
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hrJ) hbc),
      mem_ggHyperplane_of_mem_centralizer_ggRankOneIn huX hu2 hb
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr huJ) hbc)⟩
  obtain ⟨b0, hb0D, hb0X⟩ := Set.not_subset.mp hDX
  have hb0 : b0 ∈ Bs := hDBs hb0D
  obtain ⟨t0, ht0, ht0z⟩ := hφtor b0 hb0
  have ht0c : t0 ∈ Subgroup.centralizer
      (complSp (GaloisField 2 f) (0 : Fin 3) : Set (StatedSp 3 (GaloisField 2 f))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hb0J : b0 ∈ Subgroup.centralizer (J' : Set G) := hDJ hb0D
    have h1 : φ y * b0 = b0 * φ y := Subgroup.mem_centralizer_iff.mp hb0J (φ y) ⟨y, hy, rfl⟩
    have h2 : φ (t0 * y * t0⁻¹) = φ y := by
      rw [← ht0z, ← h1]
      group
    have h3 := hφinj h2
    calc y * t0 = t0 * y * t0⁻¹ * t0 := by rw [h3]
      _ = t0 * y := by group
  have ht0rt : t0 ∈ rootTorusSp (GaloisField 2 f) (0 : Fin 3) := by
    rw [← CFSG.SeitzReduction.SymplecticPilot.centralizer_rootTorusSp_inf_centralizer_complSp
      (m := 2) hK4 0]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, ht0c⟩
    rintro _ ⟨κ, rfl⟩
    exact (commute_rootTorusHom_of_mem_ggTorus ht0 κ).symm
  obtain ⟨κ, rfl⟩ := ht0rt
  have hκ : κ * κ ≠ 1 := by
    intro hκ1
    apply hb0X
    show b0 ∈ Subgroup.centralizer (X : Set G)
    have hκ' : κ = 1 := by
      have h2 : ((κ : GaloisField 2 f) + 1) * ((κ : GaloisField 2 f) + 1) = 0 := by
        have h1 := congrArg Units.val hκ1
        simp only [Units.val_mul, Units.val_one] at h1
        have h22 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
        linear_combination h1 + ((κ : GaloisField 2 f) + 1) * h22
      have h3 : (κ : GaloisField 2 f) + 1 = 0 := mul_self_eq_zero.mp h2
      apply Units.ext
      rw [Units.val_one]
      have h4 : (κ : GaloisField 2 f) = -1 := eq_neg_of_add_eq_zero_left h3
      rw [h4, CharTwo.neg_eq]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hφrange] at hx
    obtain ⟨z, rfl⟩ := hx
    have h1 := ht0z z
    rw [hκ', map_one, one_mul, inv_one, mul_one] at h1
    calc φ z * b0 = b0 * φ z * b0⁻¹ * b0 := by rw [h1]
      _ = b0 * φ z := by group
  have hfix : ∀ g ∈ X ⊓ Subgroup.centralizer (D' : Set G), ∃ z, φ z = g ∧
      z ∈ Subgroup.centralizer ((Subgroup.zpowers
        (rootTorusHom (GaloisField 2 f) 3 0 κ) : Subgroup (StatedSp 3 (GaloisField 2 f))) :
          Set (StatedSp 3 (GaloisField 2 f))) := by
    rintro g ⟨hgX, hgD⟩
    rw [← hφrange] at hgX
    obtain ⟨z, rfl⟩ := hgX
    refine ⟨z, rfl, ?_⟩
    have hc0 : b0 * φ z = φ z * b0 := Subgroup.mem_centralizer_iff.mp hgD b0 hb0D
    have h2 : φ (rootTorusHom (GaloisField 2 f) 3 0 κ * z *
        (rootTorusHom (GaloisField 2 f) 3 0 κ)⁻¹) = φ z := by
      rw [← ht0z, hc0]
      group
    have hz := hφinj h2
    have hcz : Commute (rootTorusHom (GaloisField 2 f) 3 0 κ) z := by
      change rootTorusHom (GaloisField 2 f) 3 0 κ * z = z * rootTorusHom (GaloisField 2 f) 3 0 κ
      calc rootTorusHom (GaloisField 2 f) 3 0 κ * z
          = rootTorusHom (GaloisField 2 f) 3 0 κ * z *
            (rootTorusHom (GaloisField 2 f) 3 0 κ)⁻¹ *
              rootTorusHom (GaloisField 2 f) 3 0 κ := by group
        _ = z * rootTorusHom (GaloisField 2 f) 3 0 κ := by rw [hz]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hcz.zpow_left k).eq
  have hcomm : ∀ g ∈ X ⊓ Subgroup.centralizer (D' : Set G),
      ∀ h ∈ X ⊓ Subgroup.centralizer (D' : Set G), g * h * g⁻¹ * h⁻¹ ∈ J' := by
    intro g hg h hh
    obtain ⟨z1, rfl, hz1⟩ := hfix g hg
    obtain ⟨z2, rfl, hz2⟩ := hfix h hh
    refine ⟨z1 * z2 * z1⁻¹ * z2⁻¹,
      CFSG.SeitzReduction.SymplecticPilot.commutator_mem_complSp_of_mem_centralizer hκ
        (Subgroup.mem_zpowers _) hz1 hz2, ?_⟩
    simp only [map_mul, map_inv]
  have hJq : CFSG.IsQuasisimple J' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((complSp (GaloisField 2 f) (0 : Fin 3)).equivMapOfInjective φ hφinj)
      (CFSG.SeitzReduction.SymplecticPilot.isQuasisimple_complSp (m := 2) hK4 (by norm_num) 0)
  obtain ⟨hlay, hcompJ⟩ :=
    TableBSymp.largeEvenLayer_eq_of_commutator_mem (le_inf hJX hJD) hcomm hJq
  refine ⟨J', hlay, hcompJ, hcent, ?_, ?_,
    ⟨((complSp (GaloisField 2 f) (0 : Fin 3)).equivMapOfInjective φ hφinj).symm.trans
      (CFSG.SeitzReduction.SymplecticPilot.complSpEquiv (K := GaloisField 2 f) (m := 2) 0).symm⟩⟩
  · rw [hJ'eq]; exact le_sup_left
  · rw [hJ'eq]; exact le_sup_right

end Plane

end CFSG.StandardType

end
