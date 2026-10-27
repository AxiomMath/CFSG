module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rw
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBBA1
import CFSG.GH74.KGroups.L28
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxRed
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkSm
public import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.Quasithin.Recognition.CertF8

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups commutatorElement

theorem finL28_center_eq_bot {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hL : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 3) :
    Subgroup.center ↥L = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hF : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 3) 2 3
    (by norm_num) hF hL
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_center_eq_bot_of_center_quotient_psl2_eight
    ⟨hq.1.1, hq.2.1⟩ e

theorem finL28_exists_sl2_equiv {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hL : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 3) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2), Fintype.card F = 2 ^ 3 ∧
      Nonempty (SL(2, F) ≃* ↥L) := by
  have hL' : LieModel ↥L .PSL 2 2 3 := LieModel.of_quotient_center (finL28_center_eq_bot hq hL) hL
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := uc22p22r_rank8_sl2 (X := ↥L) hL'
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, ⟨e.symm⟩⟩

theorem finL28_aut_sq_eq_one_inner {K : Type} [Group K]
    (h : LieModel K .PSL 2 2 3) (α : MulAut K) (hα : α * α = 1) :
    ∃ k : K, α = MulAut.conj k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Subgroup.center K = ⊥ :=
    CFSG.ComponentClassification.CatFactsL4U4.IdxRed.center_eq_bot_of_psl2 h
  have hK : Nat.card K = 504 := by
    obtain ⟨e1⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GF8) 2 3 (by norm_num)
      CFSG.GH74.KGroups.L28.card_GF8 h
    rw [Nat.card_congr e1.toEquiv, CFSG.GH74.KGroups.L28.card_psl_GF8]
  have hAut : Nat.card (MulAut K) = 1512 := CFSG.GH74.KGroups.L28.card_mulAut h
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) = 3 := by
    have h2 := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkSm.card_mulAut (Y := K) hc
    rw [hAut, hK] at h2
    have h3 : 504 * Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)
        = 504 * 3 := by
      rw [← h2]
    exact Nat.mul_left_cancel (by norm_num : 0 < 504) h3
  let a : CFSG.ComponentClassification.OuterAutomorphisms.Outer K := QuotientGroup.mk α
  have haa : a * a = 1 := by
    dsimp only [a]
    rw [← QuotientGroup.mk_mul, hα, QuotientGroup.mk_one]
  have hdvd3 : orderOf a ∣ 3 := by
    simpa [hOut] using orderOf_dvd_natCard a
  have hdvd2 : orderOf a ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa)
  have hone : orderOf a = 1 :=
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3) hdvd2 hdvd3
  have ha1 : a = 1 := orderOf_eq_one_iff.mp hone
  have hmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
    (QuotientGroup.eq_one_iff
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner K) α).mp ha1
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, hk.symm⟩

theorem finL28_involution_mem {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hL : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 3) {g : MulAut W} (hgY : g ∈ Y)
    (hg2 : orderOf g = 2) : g ∈ L := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hq : CFSG.IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hZ : Subgroup.center ↥L = ⊥ := finL28_center_eq_bot hq hL
  have hL' : LieModel ↥L .PSL 2 2 3 := LieModel.of_quotient_center hZ hL
  have hLY : L ≤ Y := hctx.2.2.1
  have hN : (L.subgroupOf Y).Normal := w135_normal_of_ctx hctx
  let x : ↥Y := ⟨g, hgY⟩
  have hgg : g * g = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hg2, pow_two] at h
  have hx2 : x * x = 1 := Subtype.ext (by simpa [x] using hgg)
  have hconj_mem : ∀ l : ↥L, g * (l : MulAut W) * g⁻¹ ∈ L := by
    intro l
    have hlY : (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) ∈ L.subgroupOf Y :=
      Subgroup.mem_subgroupOf.mpr l.2
    have h := Subgroup.mem_subgroupOf.mp (hN.conj_mem (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) hlY x)
    simpa [x] using h
  have hinv_mem : ∀ l : ↥L, g⁻¹ * (l : MulAut W) * g ∈ L := by
    intro l
    have hlY : (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) ∈ L.subgroupOf Y :=
      Subgroup.mem_subgroupOf.mpr l.2
    have h := Subgroup.mem_subgroupOf.mp (hN.conj_mem' (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) hlY x)
    simpa [x] using h
  let α : MulAut ↥L :=
    { toFun := fun l => ⟨g * (l : MulAut W) * g⁻¹, hconj_mem l⟩
      invFun := fun l => ⟨g⁻¹ * (l : MulAut W) * g, hinv_mem l⟩
      left_inv := fun l => by
        apply Subtype.ext
        change g⁻¹ * (g * (l : MulAut W) * g⁻¹) * g = (l : MulAut W)
        group
      right_inv := fun l => by
        apply Subtype.ext
        change g * (g⁻¹ * (l : MulAut W) * g) * g⁻¹ = (l : MulAut W)
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        show g * ((a * b : ↥L) : MulAut W) * g⁻¹
          = (g * (a : MulAut W) * g⁻¹) * (g * (b : MulAut W) * g⁻¹)
        rw [Subgroup.coe_mul]
        group }
  have hαα : α * α = 1 := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change g * (g * (l : MulAut W) * g⁻¹) * g⁻¹ = (l : MulAut W)
    calc g * (g * (l : MulAut W) * g⁻¹) * g⁻¹
        = (g * g) * (l : MulAut W) * (g * g)⁻¹ := by group
      _ = (l : MulAut W) := by rw [hgg]; group
  obtain ⟨k, hk⟩ := finL28_aut_sq_eq_one_inner hL' α hαα
  have hglk : ∀ l ∈ L, g * l * g⁻¹ = (k : MulAut W) * l * (k : MulAut W)⁻¹ := by
    intro l hl
    have h1 : ((α ⟨l, hl⟩ : ↥L) : MulAut W) = g * l * g⁻¹ := rfl
    have h2 : ((MulAut.conj k ⟨l, hl⟩ : ↥L) : MulAut W)
        = (k : MulAut W) * l * (k : MulAut W)⁻¹ := by
      rw [MulAut.conj_apply]
      rfl
    rw [hk] at h1
    rw [h2] at h1
    exact h1.symm
  have hyY : (k : MulAut W)⁻¹ * g ∈ Y :=
    Y.mul_mem (Y.inv_mem (hLY k.2)) hgY
  have hcomm : ∀ l ∈ L, ⁅(k : MulAut W)⁻¹ * g, l⁆ ∈ Zc L := by
    intro l hl
    have hyl : ((k : MulAut W)⁻¹ * g) * l = l * ((k : MulAut W)⁻¹ * g) := by
      calc ((k : MulAut W)⁻¹ * g) * l
          = (k : MulAut W)⁻¹ * (g * l * g⁻¹) * g := by group
        _ = (k : MulAut W)⁻¹ * ((k : MulAut W) * l * (k : MulAut W)⁻¹) * g := by
              rw [hglk l hl]
        _ = l * ((k : MulAut W)⁻¹ * g) := by group
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hyl]
    exact (Zc L).one_mem
  have hZy : (k : MulAut W)⁻¹ * g ∈ Zc L := w135c2_mem_Zc_of_comm hctx hyY hcomm
  have hZc : Zc L = ⊥ := by rw [Zc, hZ, Subgroup.map_bot]
  have hy1 : (k : MulAut W)⁻¹ * g = 1 := by
    have h := hZy
    rw [hZc] at h
    exact Subgroup.mem_bot.mp h
  have hgk : g = (k : MulAut W) := by
    calc g = (k : MulAut W) * ((k : MulAut W)⁻¹ * g) := by group
      _ = (k : MulAut W) := by rw [hy1, mul_one]
  rw [hgk]
  exact k.2

theorem finL28_exists_irreducible_rep {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hirr : IsIrrOn L ⊤ ⊥)
    (hcard : Nat.card W = 2 ^ 8) {F : Type} [Field F] (e : SL(2, F) ≃* ↥L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (ρ : Representation (ZMod 2) SL(2, F) V) (θ : W ≃* Multiplicative V),
      ρ.IsIrreducible ∧ Nat.card V = 2 ^ 8 ∧ (∃ g, ρ g ≠ 1) ∧
        ∀ (s : SL(2, F)) (w : W),
          θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))) := by
  obtain ⟨V, _, _, _, ρ, θ, hsimp, hθ⟩ := cu_binModel hW hirr e
  have hρ : ρ.IsIrreducible := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).2 hsimp
  have hVW : Nat.card W = Nat.card V :=
    (Nat.card_congr θ.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  have hV : Nat.card V = 2 ^ 8 := by rw [← hVW]; exact hcard
  have hnt := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_rank8_exists_ne_one ρ hρ
    (by rw [hV]; norm_num)
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, θ, hρ, hV, hnt, hθ⟩

end CFSG.LocalAnalysis.WeakClosure81
