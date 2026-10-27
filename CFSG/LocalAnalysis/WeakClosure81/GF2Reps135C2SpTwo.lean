module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.RankThree.GF2n.Stroth78.Sec4SixWStruct
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.StandardType.GGSixJNotA6Inn
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Matrix

private theorem center_eq_bot_of_lieModel_psp
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    {n : ℕ} (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 1) :
    Subgroup.center ↥L = ⊥ := by
  obtain ⟨-, F, instF, instFin, hF, ⟨eZ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hlie (by decide)
  exact letI : Field F := instF;
        letI : Finite F := instFin;
        letI : Fintype F := Fintype.ofFinite F;
        letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
        letI : CharP F 2 :=
          charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF]; norm_num);
        letI : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1;
        CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic (n := n) (K := F)
          (hodd := w135_odd_card_center hctx) eZ

private theorem isSpn_two_mul_of_lieModel_psp {X : Type} [Group X] {n : ℕ}
    (hX : LieModel X .PSp n 2 1) : IsSpn X (2 * n) 1 := by
  obtain ⟨-, F, instF, instFin, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hX (by decide)
  refine letI : Field F := instF;
         letI : Finite F := instFin;
         letI : Fintype F := Fintype.ofFinite F;
         letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
         letI : CharP F 2 :=
           charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF]; norm_num);
         ?_
  let eProj : StatedSp n F ≃* StatedProj (StatedSp n F) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n) (K := F))).trans
        QuotientGroup.quotientBot).symm
  unfold IsSpn
  rw [show 2 * n / 2 = n by exact Nat.mul_div_cancel_left n (by norm_num)]
  exact ⟨⟨n, by omega⟩, F, instF, instFin, hF, ⟨e.trans eProj.symm⟩⟩

private theorem nonempty_equiv_statedSp_zmod_of_lieModel_psp {X : Type} [Group X] {n : ℕ}
    (hX : LieModel X .PSp n 2 1) : Nonempty (StatedSp n (ZMod 2) ≃* X) := by
  obtain ⟨-, F, instF, instFin, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hX (by decide)
  refine letI : Field F := instF;
         letI : Finite F := instFin;
         letI : Fintype F := Fintype.ofFinite F;
         letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
         let hc : Fintype.card F = 2 := (by rw [← Nat.card_eq_fintype_card, hF]; norm_num);
         letI : CharP F 2 := charP_of_card_eq_prime hc;
         ?_
  let eProj : StatedSp n F ≃* StatedProj (StatedSp n F) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n) (K := F))).trans
        QuotientGroup.quotientBot).symm
  let σ : ZMod 2 ≃+* F := ZMod.ringEquiv F hc
  exact ⟨(CFSG.SeitzReduction.F4Pilot.statedSpCongr σ n).trans (e.trans eProj.symm).symm⟩

private theorem three_le_of_lieModel_psp {X : Type} [Group X] {n : ℕ}
    (hX : LieModel X .PSp n 2 1) : 3 ≤ n := by
  have h2 : 2 ≤ n := (LieModel.admissible hX).2.2.1
  have hne : (n, 2 ^ 1) ≠ (2, 2) := (LieModel.admissible hX).2.2.2
  have hn2 : n ≠ 2 := fun hn => hne (by simp [hn])
  omega

theorem w135c2_mem_of_conj_eq_conj {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {g k : MulAut W}
    (hgY : g ∈ Y) (hkL : k ∈ L) (hconj : ∀ l ∈ L, g * l * g⁻¹ = k * l * k⁻¹)
    (hZ : Subgroup.center ↥L = ⊥) : g ∈ L := by
  have hLY : L ≤ Y := hctx.2.2.1
  have hyY : k⁻¹ * g ∈ Y := Y.mul_mem (Y.inv_mem (hLY hkL)) hgY
  have hcomm : ∀ l ∈ L, ⁅k⁻¹ * g, l⁆ ∈ Zc L := by
    intro l hl
    have hyl : (k⁻¹ * g) * l = l * (k⁻¹ * g) := by
      calc (k⁻¹ * g) * l = k⁻¹ * (g * l * g⁻¹) * g := by group
        _ = k⁻¹ * (k * l * k⁻¹) * g := by rw [hconj l hl]
        _ = l * (k⁻¹ * g) := by group
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hyl]
    exact (Zc L).one_mem
  have hZy : k⁻¹ * g ∈ Zc L := w135c2_mem_Zc_of_comm hctx hyY hcomm
  have hZc : Zc L = ⊥ := by rw [Zc, hZ, Subgroup.map_bot]
  have hy1 : k⁻¹ * g = 1 := by
    have h := hZy
    rw [hZc] at h
    exact Subgroup.mem_bot.mp h
  have hgk : g = k := by
    calc g = k * (k⁻¹ * g) := by group
      _ = k := by rw [hy1, mul_one]
  rw [hgk]
  exact hkL

private theorem sp_involution_mem
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {n : ℕ} (hn : 3 ≤ n)
    (hZ : Subgroup.center ↥L = ⊥) (e : StatedSp n (ZMod 2) ≃* ↥L) {g : MulAut W}
    (hgY : g ∈ Y) (_hg2 : orderOf g = 2) : g ∈ L := by
  have hLY : L ≤ Y := hctx.2.2.1
  have hnorm : g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx) hgY
  have hAut : ∀ φ : MulAut ↥L, ∃ l : ↥L, φ = MulAut.conj l :=
    CFSG.RankThree.GF2n.Stroth78.Sec4SixW.allInner_of_mulEquiv_statedSp_zmod (m := n)
      (by omega) e.symm
  obtain ⟨k, hkL, hk⟩ := CFSG.StandardType.exists_inner_of_mem_normalizer hAut hnorm
  exact w135c2_mem_of_conj_eq_conj hctx hgY hkL hk hZ

theorem natSpn_of_linearizes {W : Type} [CommGroup W] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {n : ℕ} {L : Subgroup (MulAut W)}
    {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (e : StatedSp n F ≃* ↥L)
    {ρ : Representation (ZMod 2) (StatedSp n F) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : StatedSp n F) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {β : V ≃+ (Fin n ⊕ Fin n → F)}
    (hβ : ∀ (g : StatedSp n F) (v : V),
      β (ρ g v) = CFSG.LieType.Universal.Symplectic.SpExtras.mat n F g *ᵥ β v) :
    NatSpn L ⊤ ⊥ (2 * n) f := by
  let ψ : W ≃* Multiplicative (Fin n ⊕ Fin n → F) :=
    θ.trans (AddEquiv.toMultiplicative β)
  have hψ : ∀ (l : ↥L) (s : W), ψ ((l : MulAut W) s) =
      Multiplicative.ofAdd ((((e.symm l : StatedSp n F) :
        GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Multiplicative.toAdd (ψ s)) := by
    intro l s
    have hl : (l : MulAut W) = (e (e.symm l) : MulAut W) := by
      rw [MulEquiv.apply_symm_apply]
    simp only [ψ, MulEquiv.trans_apply]
    rw [hl, hθ (e.symm l) s]
    change Multiplicative.ofAdd (β ((ρ (e.symm l)) (Multiplicative.toAdd (θ s)))) =
      Multiplicative.ofAdd ((((e.symm l : StatedSp n F) :
        GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          β (Multiplicative.toAdd (θ s)))
    rw [hβ (e.symm l) (Multiplicative.toAdd (θ s)),
      CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply]
  unfold NatSpn
  rw [Nat.mul_div_cancel_left n (by norm_num)]
  refine ⟨⟨n, by omega⟩, F, inferInstance, inferInstance, hF, ?_⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.realizes_nat_of_mulEquiv
      e.symm ψ hψ

theorem four_le_mQuot_of_rank {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {G : Type*} [Group G] {L : Subgroup (MulAut W)}
    (e : G ≃* ↥L)
    {ρ : Representation (ZMod 2) G V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : G) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {g : MulAut W} {y : G} (hge : ((e y : ↥L) : MulAut W) = g)
    (hrank : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1))) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
  have heq := finL28_two_pow_mQuot_eq_card_range θ g (ρ y) (fun w => by
    rw [← hge]
    exact hθ y w)
  have hcardR : Nat.card (LinearMap.range (ρ y - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
    refine letI : Module.Finite (ZMod 2) (LinearMap.range (ρ y - 1)) :=
      Module.Finite.of_finite;
      ?_
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardR] at heq
  have hm := Nat.pow_right_injective (le_refl 2) heq
  rw [hm]
  exact hrank

private theorem card_eq_two_pow_eight_of_equiv {W V : Type} [CommGroup W] [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] (θ : W ≃* Multiplicative V)
    (hfin : Module.finrank (ZMod 2) V = 8) : Nat.card W = 2 ^ 8 := by
  have hW : Nat.card W = Nat.card V :=
    (Nat.card_congr θ.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  rw [hW, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hfin]

theorem w135c2_sp_two_natural_or_four_le
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {g : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (hgY : g ∈ Y) (hg2 : orderOf g = 2) {n : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 1) :
    (IsSpn ↥L (2 * n) 1 ∧ NatSpn L ⊤ ⊥ (2 * n) 1) ∨ (IsSpn ↥L 6 1 ∧ Nat.card W = 2 ^ 8) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_lieModel_psp hctx hlie
  have hL' : LieModel ↥L .PSp n 2 1 := LieModel.of_quotient_center hZ hlie
  have hS : IsSpn ↥L (2 * n) 1 := isSpn_two_mul_of_lieModel_psp hL'
  obtain ⟨e⟩ := nonempty_equiv_statedSp_zmod_of_lieModel_psp hL'
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have h3 : 3 ≤ n := three_le_of_lieModel_psp hlie
  have hgL : g ∈ L := sp_involution_mem hctx h3 hZ e hgY hg2
  obtain ⟨V, _, _, _, ρ, θ, hρ, hθ⟩ := cu_binModel hW hirr e
  have hgg : g * g = 1 := by
    have h1 := pow_orderOf_eq_one g
    rwa [hg2, pow_two] at h1
  let y : StatedSp n (ZMod 2) := e.symm ⟨g, hgL⟩
  have hey : e y = ⟨g, hgL⟩ := e.apply_symm_apply _
  have hge : ((e y : ↥L) : MulAut W) = g := by rw [hey]
  have hy2 : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext hgg
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, map_one] at hey
    have hg1 : g = 1 := congrArg Subtype.val hey.symm
    rw [hg1, orderOf_one] at hg2
    omega
  have hρy : ρ y ≠ 1 := rho_ne_one_of_conj e hθ hge hg2
  rcases sp_two_natural_or_four_le (n := n) (V := V) (ρ := ρ) (y := y) h3 hρ ⟨y, hρy⟩ hy2 hy1
    with ⟨β, hβ⟩ | ⟨hn3, hfin8⟩ | hrank
  · exact Or.inl ⟨hS, natSpn_of_linearizes (F := ZMod 2)
      (by rw [Nat.card_zmod]; norm_num) e hθ (β := β.toAddEquiv) hβ⟩
  · subst hn3
    exact Or.inr (Or.inl ⟨hS, card_eq_two_pow_eight_of_equiv θ hfin8⟩)
  · exact Or.inr (Or.inr (four_le_mQuot_of_rank e hθ hge hrank))

theorem w135c2_sp_two
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 1) : W4Lem13_5Concl W Y L t := by
  rcases w135c2_sp_two_natural_or_four_le (g := t) hW hctx htY ht2 hlie with
    ⟨hS, hNat⟩ | ⟨hS6, hcardW⟩ | h4
  · exact w135c2_natural hctx htY ht2 hW
      (Or.inl ⟨2 * n, 1, Or.inr (Or.inl ⟨hS, hNat⟩)⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hS6, hcardW⟩))))))
  · exact absurd h4 (by omega)

end CFSG.LocalAnalysis.WeakClosure81
