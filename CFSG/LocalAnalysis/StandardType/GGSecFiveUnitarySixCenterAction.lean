module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofRed
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcFrame
public import CFSG.LocalAnalysis.StandardType.GGNsq2U62
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.Phan.AutSU2

public section

namespace CFSG.StandardType

open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSecFiveBPermUniQTwoExc_fixed_free_b1_of_redFrame
    (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (eta' : ↥(Line63.H5.redMkB hN).range ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (heta' : ∀ b : ↥Bs, eta' ⟨Line63.H5.redMkB hN b, b, rfl⟩ = eta b)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : Nat.card K = 4)
    {ϕ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* Line63.H5.RedGrp L}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame (Line63.H5.redMkB hN).range
      (Line63.H5.redMkL L).range eta' 1 ϕ χ)
    (hLp : commutator L = ⊤) :
    ∀ z ∈ Line63.H5.twoCenter L,
      (eta.symm (Pi.mulSingle 0 (ofAdd (1 : ZMod 3))) : G) * z =
        z * (eta.symm (Pi.mulSingle 0 (ofAdd (1 : ZMod 3))) : G) → z = 1 := by
  classical
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK4
  have : Group.IsPerfect L := ⟨hLp⟩
  let Y := (Line63.H5.redMkL L).range
  let e₀ : Fin 6 → Multiplicative (ZMod 3) := Pi.mulSingle 0 (ofAdd (1 : ZMod 3))
  let b : Bs := eta.symm e₀
  let r := Line63.H5.redMkB hN b
  let bbar : (Line63.H5.redMkB hN).range := ⟨r, b, rfl⟩
  obtain ⟨D₀, hD₀N, hD₀mat, hact⟩ := hF.2.2.2 bbar
  have heb : eta' bbar = e₀ := (heta' b).trans (eta.apply_symm_apply e₀)
  have hDm : (D₀ : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal
      (fun i => (χ (e₀ i) : K)) := by
    simpa only [Equiv.Perm.one_apply, heb] using hD₀mat
  have hχcube : ∀ c : Multiplicative (ZMod 3), (χ c : K) ^ 3 = 1 := by
    intro c
    have hc : c ^ 3 = 1 := by
      simpa using (pow_card_eq_one' (x := c))
    have h : χ c ^ 3 = 1 := by rw [← map_pow, hc, map_one]
    exact congrArg Units.val h
  have hDunit : ggIsUnitaryMat (p := 2) (f := 1) D₀ := by
    rw [ggIsUnitaryMat, hDm, CFSG.LieType.Steinberg.conjTr_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    change (χ (e₀ i) : K) ^ 2 * (χ (e₀ i) : K) = 1
    rw [← pow_succ]
    exact hχcube (e₀ i)
  have hdetmat : (D₀ : Matrix (Fin 6) (Fin 6) K).det =
      (χ (ofAdd (1 : ZMod 3)) : K) := by
    rw [hDm, Matrix.det_diagonal]
    have hcoeff : ∀ i : Fin 6, (χ (e₀ i) : K) =
        if i = 0 then (χ (ofAdd (1 : ZMod 3)) : K) else 1 := by
      intro i
      by_cases hi : i = 0
      · subst i
        change (χ (ofAdd (1 : ZMod 3)) : K) = if (0 : Fin 6) = 0 then _ else _
        rw [if_pos rfl]
      · rw [if_neg hi]
        have he : e₀ i = 1 := Pi.mulSingle_eq_of_ne hi _
        rw [he, map_one]
        rfl
    calc
      (∏ i, (χ (e₀ i) : K)) = ∏ i : Fin 6,
          if i = 0 then (χ (ofAdd (1 : ZMod 3)) : K) else 1 :=
        Finset.prod_congr rfl (fun i _ => hcoeff i)
      _ = (χ (ofAdd (1 : ZMod 3)) : K) := by
        simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hχne : χ (ofAdd (1 : ZMod 3)) ≠ 1 := by
    intro h
    have h1 := hF.2.2.1 (h.trans (map_one χ).symm)
    exact one_ne_zero (show (1 : ZMod 3) = 0 from congrArg toAdd h1)
  have hDdet : Matrix.GeneralLinearGroup.det D₀ ≠ 1 := by
    intro h
    have hv : (Matrix.GeneralLinearGroup.det D₀ : K) = 1 := congrArg Units.val h
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hv
    apply hχne
    exact Units.ext (hdetmat.symm.trans hv)
  let π : L →* Y := (Line63.H5.redMkL L).rangeRestrict
  let ψU : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) →* Y :=
    ϕ.codRestrict Y (fun s => by
      change ϕ s ∈ (Line63.H5.redMkL L).range
      rw [← hF.1]
      exact ⟨s, rfl⟩)
  let eSU := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.suEquivUnitarySU K 2 1 hK 6
  let ψ₀ := ψU.comp eSU.toMonoidHom
  have hrN : r ∈ Subgroup.normalizer (Y : Set (Line63.H5.RedGrp L)) := by
    have : Y.Normal := Line63.H5.redL_normal L
    exact Subgroup.le_normalizer_of_normal (H := Y) (K := ⊤) (Subgroup.mem_top r)
  let τ : MulAut Y := Y.normalizerMonoidHom ⟨r, hrN⟩
  let β := ggGamma L hN b
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨l, hl⟩ := y.2
    exact ⟨l, Subtype.ext hl⟩
  have hπZ : ∀ l ∈ π.ker, ∀ l' : L, l' * l = l * l' := by
    intro l hl l'
    have h0 : Line63.H5.redMkL L l = 1 := congrArg Subtype.val hl
    have hz := (Line63.H5.redMkL_eq_one_iff L l).mp h0
    exact Subtype.ext (hz.2.1 l' l'.2).symm
  have hπ2 : ∀ l ∈ π.ker, ∃ k : ℕ, l ^ (2 ^ k) = 1 := by
    intro l hl
    have h0 : Line63.H5.redMkL L l = 1 := congrArg Subtype.val hl
    have hz := (Line63.H5.redMkL_eq_one_iff L l).mp h0
    exact ⟨Nat.card G, Subtype.ext hz.2.2⟩
  have hψUs : Function.Surjective ψU := by
    intro y
    have hy : (y : Line63.H5.RedGrp L) ∈ ϕ.range := by rw [hF.1]; exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext hs⟩
  have hψs : Function.Surjective ψ₀ := hψUs.comp eSU.surjective
  have hψZ : ψ₀.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K 2 1 6) := by
    intro s hs
    have hs0 : ϕ (eSU s) = 1 := congrArg Subtype.val hs
    obtain ⟨c, hc⟩ := hF.2.1 (eSU s) hs0
    rw [Subgroup.mem_center_iff]
    intro s'
    apply eSU.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    apply Units.ext
    change (((eSU s' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * (((eSU s : _) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (((eSU s : _) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (((eSU s' : _) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [hc]
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hπτ : ∀ l : L, π (β l) = τ (π l) := by
    intro l
    apply Subtype.ext
    change Line63.H5.redMkL L (ggGamma L hN b l) =
      r * Line63.H5.redMkL L l * r⁻¹
    exact (Line63.H5.redMk_conj (L := L) (Subgroup.inclusion hN b) l).symm
  have hτψ : ∀ s : CFSG.ClassicalInvolution.Phan.Su K 2 1 6,
      ∃ y : CFSG.ClassicalInvolution.Phan.Su K 2 1 6,
        (y : GL (Fin 6) K) = D₀ * (s : GL (Fin 6) K) * D₀⁻¹ ∧ τ (ψ₀ s) = ψ₀ y := by
    intro s
    let y := eSU.symm (LineU.conjN D₀ hD₀N (eSU s))
    refine ⟨y, ?_, ?_⟩
    · dsimp only [y, eSU]
      rw [CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_suEquivUnitarySU_symm]
      change D₀ * (eSU s : GL (Fin 6) K) * D₀⁻¹ = _
      rw [CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_suEquivUnitarySU]
    · apply Subtype.ext
      change r * ϕ (eSU s) * r⁻¹ = ϕ (eSU (eSU.symm (LineU.conjN D₀ hD₀N (eSU s))))
      rw [eSU.apply_symm_apply]
      exact hact (eSU s)
  have hfixed := hU62 K hK L Y π ψ₀ β τ D₀ inferInstance hπs hπZ hπ2 hψs hψZ hπτ
    hDunit hDdet hτψ
  intro z hz hcomm
  let zL : L := ⟨z, hz.1⟩
  have hzπ : zL ∈ π.ker := by
    change π zL = 1
    apply Subtype.ext
    exact (Line63.H5.redMkL_eq_one_iff L zL).mpr hz
  have hβz : β zL = zL := by
    apply Subtype.ext
    change (b : G) * z * (b : G)⁻¹ = z
    change (b : G) * z = z * (b : G) at hcomm
    rw [hcomm]
    group
  exact congrArg Subtype.val (hfixed zL hzπ hβz)

theorem ggSecFiveBPermUniQTwoExc_fixed_free_b1
    (hRig : GGLabelRigidInput) (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : Bs ≃* (Fin 6 → Multiplicative (ZMod p)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 p)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel 6 p lab ∧ lab.n ≤ 1)
      p Bs L) :
    ∀ z ∈ Line63.H5.twoCenter L,
      (eta.symm (Pi.mulSingle 0 (ofAdd (1 : ZMod p))) : G) * z =
        z * (eta.symm (Pi.mulSingle 0 (ofAdd (1 : ZMod p))) : G) → z = 1 := by
  classical
  obtain ⟨rfl, K, hField, hFinite, hChar, hN, eta', ϕ, χ, hK4, heta', hF⟩ :=
    exists_redUniLFrame_of_uniQTwoSix hRig hR eta hA hLab
  let : Field K := hField
  let : Finite K := hFinite
  let : CharP K 2 := hChar
  exact ggSecFiveBPermUniQTwoExc_fixed_free_b1_of_redFrame hU62 hN eta eta' heta' hK4 hF
    hLab.1

end CFSG.StandardType
