module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusCoord
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
import CFSG.Quasithin.Background.Harris.L2.OmegaMinusNat
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.Quasithin.Vol2.Ch6H11Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Open (StatedOmega StatedQuadMinus)
open CFSG.Quasithin.G11.Harris.L2 (QIdx hermToTwisted hermToTwisted_hermAct)
open CFSG.Quasithin.H13.H11M (VH LH SigInv rhoH)
open CFSG.Quasithin.JonesParshall (hermEquiv hermAct sig sig_apply)
open CFSG.Quasithin.SteinbergCB (frobFixed card_frobFixed exists_frob_ne twistedForm twistRep)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (NatOmegaMinus)
open CFSG.ClassicalInvolution.Upgrade (fieldIsoOfCard map_statedOmega_conj)
open CFSG.SeitzReduction.F4Pilot (exists_gl_isometry_statedQuadMinus)
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC (exists_natEquiv)
open Matrix

private noncomputable def mulEquivOfAddEquiv_A02 {G : Type*} [CommGroup G] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] (α : Additive G ≃+ (ι → K)) (g : GL ι K) :
    G ≃* Multiplicative (ι → K) where
  toFun v := Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ α (Additive.ofMul v))
  invFun w := Additive.toMul (α.symm (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w.toAdd))
  left_inv v := by
    dsimp only
    rw [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec, AddEquiv.symm_apply_apply, toMul_ofMul]
  right_inv w := by
    dsimp only
    rw [ofMul_toMul, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' v w := by
    rw [ofMul_mul, map_add, Matrix.mulVec_add, ofAdd_add]

private theorem conj_mulVec_A02 {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (g A : GL ι K) (v : ι → K) :
    (((MulAut.conj g) A : GL ι K) : Matrix ι ι K) *ᵥ v =
      (g : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ
        ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) := by
  rw [show (((MulAut.conj g) A : GL ι K) : Matrix ι ι K) =
      (g : Matrix ι ι K) * (A : Matrix ι ι K) *
        ((g⁻¹ : GL ι K) : Matrix ι ι K) by simp [MulAut.conj_apply, Units.val_mul]]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem inv_mulVec_mulVec_A02 {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (g : GL ι K) (v : ι → K) :
    ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem hermCoords_rhoH_A02 {k : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    {K : Type} [Field K] (hσ : SigInv k F) (M' : SL₂ F →* GL QIdx K)
    (ψ : twistedForm (sig (F := F) k) ≃+ (QIdx → K))
    (hψ : ∀ (g : SL₂ F) (X : twistedForm (sig (F := F) k)),
      ψ (twistRep (σ := sig (F := F) k) hσ g X) = (M' g : Matrix QIdx QIdx K) *ᵥ ψ X) :
    ∀ (g : SL₂ F) (v : VH k F),
      ((hermEquiv k F).trans ((hermToTwisted F k).trans ψ)) (Additive.ofMul (rhoH hσ g v)) =
        (M' g : Matrix QIdx QIdx K) *ᵥ
          (((hermEquiv k F).trans ((hermToTwisted F k).trans ψ)) (Additive.ofMul v)) := by
  intro g v
  change ψ (hermToTwisted F k (hermEquiv k F (Additive.ofMul (rhoH hσ g v)))) =
    (M' g : Matrix QIdx QIdx K) *ᵥ
      ψ (hermToTwisted F k (hermEquiv k F (Additive.ofMul v)))
  have h1 : hermEquiv k F (Additive.ofMul (rhoH hσ g v)) =
      hermAct k hσ g (hermEquiv k F (Additive.ofMul v)) := rfl
  rw [h1, hermToTwisted_hermAct, hψ]

private theorem congrHom_pi_A02 {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {k : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2] {K : Type} [Field K]
    {Q : (QIdx → K) → K} (hσ : SigInv k F)
    {π : ↥(StatedOmega Q) ≃* ↥H} {e : W ≃* Multiplicative (QIdx → K)}
    (hπe : ∀ (γ : ↥(StatedOmega Q)) (w : W),
      Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL QIdx K) : Matrix QIdx QIdx K) *ᵥ Multiplicative.toAdd (e w))
    {M : SL₂ F →* GL QIdx K} {Φ : VH k F ≃* Multiplicative (QIdx → K)}
    (hΦ : ∀ (g : SL₂ F) (v : VH k F), Multiplicative.toAdd (Φ (rhoH hσ g v)) =
      ((M g : GL QIdx K) : Matrix QIdx QIdx K) *ᵥ Multiplicative.toAdd (Φ v))
    (γ : ↥(StatedOmega Q)) (g : SL₂ F) (hg : M g = (γ : GL QIdx K)) :
    CFSG.Quasithin.H.congrHom (e.trans Φ.symm) ((π γ : ↥H) : MulAut W) = rhoH hσ g := by
  refine MulEquiv.ext fun v => ?_
  rw [CFSG.Quasithin.H.congrHom_apply, MulEquiv.symm_trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_symm]
  have h1 : e (((π γ : ↥H) : MulAut W) (e.symm (Φ v))) = Φ (rhoH hσ g v) := by
    apply Multiplicative.toAdd.injective
    rw [hπe γ (e.symm (Φ v)), MulEquiv.apply_symm_apply, ← hg, ← hΦ g v]
  rw [h1, MulEquiv.symm_apply_apply]

theorem one_le_of_natOmegaMinus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {k : ℕ}
    (h : NatOmegaMinus H ⊤ ⊥ 4 k) : 1 ≤ k := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, -, -⟩ := h
  letI : Field K := hField
  haveI : Finite K := hFinite
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  exact Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, pow_zero] at h1
    exact lt_irrefl 1 h1

theorem exists_field_card {k : ℕ} (hk : 1 ≤ k) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2),
      Fintype.card F = 2 ^ (2 * k) := by
  haveI : Fintype (GaloisField 2 (2 * k)) := Fintype.ofFinite _
  refine ⟨GaloisField 2 (2 * k), inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (2 * k) (by omega)

theorem exists_herm_coords {k : ℕ} (hk : 1 ≤ k) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * k)) (hσ : SigInv k F) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ k) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (M : SL₂ F →* GL QIdx K) (Φ : VH k F ≃* Multiplicative (QIdx → K)),
      Function.Injective M ∧ M.range = StatedOmega (StatedQuadMinus 2 K b c) ∧
      ∀ (s : SL₂ F) (v : VH k F), Multiplicative.toAdd (Φ (rhoH hσ s v)) =
        ((M s : GL QIdx K) : Matrix QIdx QIdx K) *ᵥ Multiplicative.toAdd (Φ v) := by
  have hF' : Nat.card F = (2 ^ k) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF]
    exact pow_mul' 2 2 k
  have hσ' : ∀ x : F, sig k x = x ^ 2 ^ k := sig_apply k
  obtain ⟨ω, hω⟩ := exists_frob_ne (F := F) hk hF' hσ'
  have hcard : Nat.card (frobFixed (sig (F := F) k)) = Nat.card K := by
    rw [card_frobFixed hk hF' hσ', hK]
  let e₀ : frobFixed (sig (F := F) k) ≃+* K := fieldIsoOfCard hcard
  obtain ⟨M', ψ, b', c', hirr', hinj', hrange', hψ, -⟩ :=
    CFSG.Quasithin.G11.Harris.L2.exists_omegaRep hk hF' hσ' e₀ hω
  obtain ⟨g, hg⟩ := exists_gl_isometry_statedQuadMinus 2 hirr' hirr
  have hconj : (StatedOmega (StatedQuadMinus 2 K b' c')).map (MulAut.conj g).toMonoidHom =
      StatedOmega (StatedQuadMinus 2 K b c) := map_statedOmega_conj g hg
  let α : Additive (VH k F) ≃+ (QIdx → K) :=
    (hermEquiv k F).trans ((hermToTwisted F k).trans ψ)
  have hα : ∀ (s : SL₂ F) (v : VH k F), α (Additive.ofMul (rhoH hσ s v)) =
      (M' s : Matrix QIdx QIdx K) *ᵥ α (Additive.ofMul v) :=
    hermCoords_rhoH_A02 hσ M' ψ hψ
  refine ⟨(MulAut.conj g).toMonoidHom.comp M', mulEquivOfAddEquiv_A02 α g, ?_, ?_, ?_⟩
  · exact fun a b h => hinj' ((MulAut.conj g).injective h)
  · rw [MonoidHom.range_comp, hrange', hconj]
  · intro s v
    change (g : Matrix QIdx QIdx K) *ᵥ α (Additive.ofMul (rhoH hσ s v)) =
      (((MulAut.conj g) (M' s) : GL QIdx K) : Matrix QIdx QIdx K) *ᵥ
        ((g : Matrix QIdx QIdx K) *ᵥ α (Additive.ofMul v))
    rw [hα s v, conj_mulVec_A02, inv_mulVec_mulVec_A02]

theorem exists_equiv_vh {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {k : ℕ}
    (h : NatOmegaMinus H ⊤ ⊥ 4 k) (hk : 1 ≤ k) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * k)) (hσ : SigInv k F) :
    ∃ E : W ≃* VH k F, H.map (CFSG.Quasithin.H.congrHom E) = LH hσ := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hreal⟩ := h
  letI : Field K := hKf
  haveI : Finite K := hKfin
  rw [show 4 / 2 = 2 by norm_num] at hreal
  obtain ⟨π, e, hπe⟩ := exists_natEquiv hreal
  obtain ⟨M, Φ, _, hMrange, hΦ⟩ := exists_herm_coords hk hF hσ hKcard hirr
  refine ⟨e.trans Φ.symm, ?_⟩
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ, hγ⟩ := π.surjective ⟨y, hy⟩
    have hγ' : ((π γ : ↥H) : MulAut W) = y := congrArg Subtype.val hγ
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (by rw [hMrange]; exact γ.2)
    rw [← hγ', congrHom_pi_A02 hσ hπe hΦ γ g hg]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  · intro hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    let γ : ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
      ⟨M g, by rw [← hMrange]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
    refine Subgroup.mem_map.mpr ⟨((π γ : ↥H) : MulAut W), (π γ).2, ?_⟩
    exact congrHom_pi_A02 hσ hπe hΦ γ g rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA
