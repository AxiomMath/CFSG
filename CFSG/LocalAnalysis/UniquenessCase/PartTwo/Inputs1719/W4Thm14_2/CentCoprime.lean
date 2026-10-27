module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.MinDegree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB
public import CFSG.Quasithin.Background.D2Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
public import CFSG.Quasithin.SteinbergBICommonNormalizerTools
public import CFSG.Quasithin.Background.SL3SmallNat
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups Matrix

private lemma ztriv_irreducible_eq_bot {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : SL(3, K) →* ↥L) (hα : Function.Surjective α)
    (hcen : (LinearFlag.scalars 3 K).map α = Subgroup.center ↥L)
    {z : MulAut W} (hzL : z ∈ L)
    (hzc : ∀ l ∈ L, z * l = l * z) (hz1 : z ≠ 1)
    {U : Subgroup W} (hU : IsIrrOn L U ⊥) (hUz : ∀ u ∈ U, z u = u)
    (hrkU : rk U ≤ 6) : U = ⊥ := by
  classical
  have hUne : U ≠ ⊥ := hU.1.ne'
  obtain ⟨U', hU'add, hU'mod, hU'fin, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary (V := U) (fun v => by
      apply Subtype.ext
      simpa [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using hW (v : W))
  letI : AddCommGroup U' := hU'add
  letI : Module (ZMod 2) U' := hU'mod
  letI : Finite U' := hU'fin
  have hmapU : ∀ l ∈ L, U.map l.toMonoidHom = U := by
    intro l hl
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u, hu, rfl⟩
      exact hU.2.1 l hl u hu
    · rw [Subgroup.card_map_of_injective l.injective]
  let actL : ↥L →* MulAut U :=
    CFSG.Quasithin.SteinbergBI.restrictAction L U hmapU
  have hnt' : Nontrivial U' := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    refine ⟨⟨Multiplicative.toAdd (θ u), 0, ?_⟩⟩
    intro h
    apply hu1
    apply θ.injective
    apply Multiplicative.toAdd.injective
    simpa using h
  have hirrU : ∀ J : Subgroup U,
      (∀ l ∈ actL.range, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hJ' : StableUnder L (J.map U.subtype) := by
      intro l hl w hw
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
      let lL : ↥L := ⟨l, hl⟩
      have hmem : actL lL v ∈ J := hJ (actL lL) ⟨lL, rfl⟩ v hv
      have hmem' : ((actL lL v : U) : W) ∈ J.map U.subtype :=
        Subgroup.mem_map_of_mem U.subtype hmem
      rw [CFSG.Quasithin.SteinbergBI.coe_restrictAction_apply L U hmapU lL v] at hmem'
      exact hmem'
    rcases hU.2.2.2 (J.map U.subtype) hJ' bot_le (Subgroup.map_subtype_le J) with h | h
    · left
      apply Subgroup.map_injective U.subtype_injective
      rw [h, Subgroup.map_bot]
    · right
      rw [eq_top_iff]
      intro u _
      have hu : (u : W) ∈ J.map U.subtype := by
        rw [h]
        exact u.2
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
      exact (Subtype.ext hvu) ▸ hv
  let ρL : Representation (ZMod 2) ↥L U' :=
    { toFun := fun l => (CFSG.QuasithinUnique.Setup.Layer.binPsi θ (actL l)).toLinearMap
      map_one' := by
        rw [map_one (actL)]
        exact congrArg (fun e : U' ≃ₗ[ZMod 2] U' => e.toLinearMap) (map_one (Layer.binPsi θ))
      map_mul' := fun l₁ l₂ => by
        rw [map_mul (actL)]
        exact congrArg (fun e : U' ≃ₗ[ZMod 2] U' => e.toLinearMap)
          (map_mul (Layer.binPsi θ) (actL l₁) (actL l₂)) }
  have hρLirr : ρL.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨hnt', fun V hV => ?_⟩
    refine CFSG.Quasithin.B42L2.irr_map (θ := θ) hirrU V ?_
    rintro x hx u hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨l, rfl⟩ := hy
    exact hV l u hu
  let ρ : Representation (ZMod 2) SL(3, K) U' := ρL.comp α
  have hρirr : ρ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff] at hρLirr ⊢
    refine ⟨hρLirr.1, fun V hV => hρLirr.2 V (fun l u hu => ?_)⟩
    obtain ⟨g, rfl⟩ := hα l
    exact hV g u hu
  have hzcenter : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact (hzc l l.2).symm
  have hzcenter_ne : (⟨z, hzL⟩ : ↥L) ≠ 1 := by
    intro h
    exact hz1 (congrArg Subtype.val h)
  have hzmem : (⟨z, hzL⟩ : ↥L) ∈ (LinearFlag.scalars 3 K).map α := by
    rw [hcen]
    exact hzcenter
  obtain ⟨A, hA, hAα⟩ := Subgroup.mem_map.mp hzmem
  obtain ⟨c, hc3, hAeq⟩ := LinearFlag.mem_scalars.mp hA
  have hAne : A ≠ 1 := by
    intro h
    apply hzcenter_ne
    rw [← hAα, h, map_one]
  letI : Fintype K := Fintype.ofFinite K
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let f := Module.finrank (ZMod 2) K
  have hF : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, ← FiniteField.pow_finrank_eq_natCard 2 K]
  have hcne : c ≠ 1 := by
    intro hc1
    apply hAne
    apply Subtype.ext
    rw [hAeq, hc1]
    ext i j
    simp [Matrix.scalar_apply]
  have hf2 : 2 ≤ f := by
    have hntK : Nontrivial Kˣ := ⟨1, c, hcne.symm⟩
    have h2 : 1 < Nat.card Kˣ := Finite.one_lt_card_iff_nontrivial.mpr hntK
    have h3 : 3 ≤ Nat.card K := by
      have h := Nat.card_units (K)
      omega
    have h4 : 3 ≤ 2 ^ f := by
      rwa [← hF, ← Nat.card_eq_fintype_card]
    by_contra h
    have hlt : f < 2 := not_le.mp h
    interval_cases f <;> norm_num at h4
  have hcardU : Nat.card U = 2 ^ rk U := card_eq_two_pow hW U
  have hcardU' : Nat.card U' = 2 ^ Module.finrank (ZMod 2) U' := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U')
  have hcards : Nat.card U' = Nat.card U :=
    Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd).symm
  have hfin_eq : Module.finrank (ZMod 2) U' = rk U := by
    apply Nat.pow_right_injective (by norm_num : 1 < 2)
    change 2 ^ Module.finrank (ZMod 2) U' = 2 ^ rk U
    rw [← hcardU', ← hcardU, hcards]
  have hdim : Module.finrank (ZMod 2) U' ≤ 3 * f + 1 := by
    rw [hfin_eq]
    omega
  have hntρ : ∃ x, ρ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have htriv : ∀ l : ↥L, ρL l = 1 := by
      intro l
      obtain ⟨g, hg⟩ := hα l
      simpa [ρ, hg] using hcon g
    have hUfix : U ≤ fixV L := by
      intro u hu
      rw [mem_fixV]
      intro l hl
      let lL : ↥L := ⟨l, hl⟩
      have h1 : actL lL ⟨u, hu⟩ = ⟨u, hu⟩ := by
        apply θ.injective
        apply Multiplicative.toAdd.injective
        have h2 := congrArg (fun T : U' →ₗ[ZMod 2] U' =>
          T (Multiplicative.toAdd (θ ⟨u, hu⟩))) (htriv lL)
        simpa [ρL, CFSG.QuasithinUnique.Setup.Layer.binPsi_apply] using h2
      have h3 := congrArg (fun x : U => (x : W)) h1
      rw [CFSG.Quasithin.SteinbergBI.coe_restrictAction_apply L U hmapU lL ⟨u, hu⟩] at h3
      exact h3
    rw [hfix] at hUfix
    exact hUne (le_bot_iff.mp hUfix)
  obtain ⟨w, hwne⟩ : ∃ w : U', w ≠ 0 := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    refine ⟨Multiplicative.toAdd (θ u), ?_⟩
    intro h
    apply hu1
    apply θ.injective
    apply Multiplicative.toAdd.injective
    simpa using h
  obtain ⟨ψ, hψ, E, hE⟩ :=
    CFSG.Quasithin.SL3Small.natural_of_irreducible hF hf2 ρ hρirr hntρ hdim
  have hψsurj : Function.Surjective ψ := fun g => ⟨ψ g, hψ g⟩
  have hAcent : A ∈ Subgroup.center (SL(3, K)) := by
    rw [← LinearFlag.scalars_eq_center]
    exact hA
  have hψAcent : ψ A ∈ Subgroup.center (SL(3, K)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨b, rfl⟩ := hψsurj g
    calc
      ψ b * ψ A = ψ (b * A) := (map_mul ψ b A).symm
      _ = ψ (A * b) := by rw [Subgroup.mem_center_iff.mp hAcent b]
      _ = ψ A * ψ b := map_mul ψ A b
  have hψAscal : ψ A ∈ LinearFlag.scalars 3 K := by
    rw [LinearFlag.scalars_eq_center]
    exact hψAcent
  obtain ⟨d, hd, hψAeq⟩ := LinearFlag.mem_scalars.mp hψAscal
  have hAtriv : ρ A = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ : ∃ u : U, Multiplicative.toAdd (θ u) = w :=
      ⟨θ.symm (Multiplicative.ofAdd w), by simp⟩
    have h1 : ρ A (Multiplicative.toAdd (θ u)) =
        Multiplicative.toAdd (θ (actL (α A) u)) := by
      show ρL (α A) (Multiplicative.toAdd (θ u)) = _
      simp [ρL, CFSG.QuasithinUnique.Setup.Layer.binPsi_apply]
    rw [h1]
    have h2 : actL (α A) u = u := by
      apply Subtype.ext
      rw [CFSG.Quasithin.SteinbergBI.coe_restrictAction_apply L U hmapU (α A) u]
      have hco : ((α A : ↥L) : MulAut W) = z := congrArg Subtype.val hAα
      rw [hco]
      exact hUz (u : W) u.2
    rw [h2]
    rfl
  have hfixE : ((ψ A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ (E w) = E w := by
    have h1 := hE A w
    rw [hAtriv] at h1
    simpa using h1.symm
  have hEwne : E w ≠ 0 := by
    intro h
    apply hwne
    apply E.injective
    rw [h, map_zero]
  obtain ⟨i, hi⟩ : ∃ i, (E w) i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hEwne (funext hcon)
  have hd1 : (d : K) = 1 := by
    have h2 : ((Matrix.scalar (Fin 3) (d : K)) *ᵥ E w) = (d : K) • (E w) := by
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have h3 : (d : K) • (E w) = E w := by
      rw [← h2, ← hψAeq]
      exact hfixE
    have h4 := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul, one_mul] at h4
    exact mul_right_cancel₀ hi (by simpa using h4)
  have hψAone : ψ A = 1 := by
    apply Subtype.ext
    rw [hψAeq, hd1]
    ext i j
    simp [Matrix.scalar_apply]
  exact False.elim (hAne (by
    have h1 := hψ A
    rw [hψAone, map_one] at h1
    exact h1.symm))

theorem fixV_zpowers_eq_bot_of_center {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsSL3 ↥L 2)
    (hrk : rk ↥(⊤ : Subgroup W) ≤ 12) (hfix : fixV L = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] (α : SL(3, K) →* ↥L)
    (hα : Function.Surjective α)
    (hcen : (LinearFlag.scalars 3 K).map α = Subgroup.center ↥L)
    {z : MulAut W} (hzL : z ∈ L)
    (hzc : ∀ l ∈ L, z * l = l * z) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    fixV (Subgroup.zpowers z) = ⊥ := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hcard3 : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hzord]
  obtain ⟨hsup, hinf, hrank, heven⟩ := commV_card_three (V := W) hW hcard3
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hzc b hb) n).eq
  have hmap : ∀ l ∈ L, (commV (Subgroup.zpowers z)).map l.toMonoidHom =
      commV (Subgroup.zpowers z) := by
    intro l hl
    rw [CFSG.Quasithin.SteinbergBI.map_eq_iff_forall]
    intro u
    constructor
    · intro hu
      have h := commV_apply_mem_of_commute (V := W) hcomm (L.inv_mem hl) hu
      simpa using h
    · intro hu
      exact commV_apply_mem_of_commute (V := W) hcomm hl hu
  let φ : ↥L →* MulAut ↥(commV (Subgroup.zpowers z)) :=
    CFSG.Quasithin.SteinbergBI.restrictAction L (commV (Subgroup.zpowers z)) hmap
  have hzwdata : ∃ w, z w ≠ w ∧ z w * w⁻¹ ∈ commV (Subgroup.zpowers z) ∧
      z w * w⁻¹ ≠ 1 := by
    have hzw' : ∃ w, z w ≠ w := by
      by_contra h
      push Not at h
      exact hz1 (MulEquiv.ext h)
    obtain ⟨w, hzw⟩ := hzw'
    refine ⟨w, hzw, Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, w, rfl⟩, ?_⟩
    intro h
    exact hzw (mul_inv_eq_one.mp h)
  have hAne : commV (Subgroup.zpowers z) ≠ ⊥ := by
    intro hbot
    obtain ⟨w, -, hmem, hne⟩ := hzwdata
    rw [hbot] at hmem
    exact hne (Subgroup.mem_bot.mp hmem)
  have hφ : φ ≠ 1 := by
    intro h1
    have h := congrArg (fun f : ↥L →* MulAut ↥(commV (Subgroup.zpowers z)) =>
      f ⟨z, hzL⟩) h1
    obtain ⟨w, -, hmem, hne⟩ := hzwdata
    have hfixA : (φ ⟨z, hzL⟩) ⟨z w * w⁻¹, hmem⟩ = ⟨z w * w⁻¹, hmem⟩ := by
      have h2 := congrArg
        (fun f : MulAut ↥(commV (Subgroup.zpowers z)) => f ⟨z w * w⁻¹, hmem⟩) h
      simpa using h2
    have h3 : z (z w * w⁻¹) = z w * w⁻¹ := by
      have := congrArg Subtype.val hfixA
      simpa [φ, CFSG.Quasithin.SteinbergBI.coe_restrictAction_apply] using this
    have h4 : z w * w⁻¹ ∈ fixV (Subgroup.zpowers z) := by
      rw [mem_fixV_zpowers_iff_apply]
      exact h3
    have h5 : z w * w⁻¹ ∈ commV (Subgroup.zpowers z) ⊓ fixV (Subgroup.zpowers z) :=
      ⟨hmem, h4⟩
    rw [hinf] at h5
    exact hne (Subgroup.mem_bot.mp h5)
  have hdmin : CFSG.LocalAnalysis.UniquenessCase.PartTwo.dMinDeg ↥L ≤
      rk ↥(commV (Subgroup.zpowers z)) := by
    refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.dMinDeg_le_rk_of_hom_ne_one
      (fun a b => mul_comm a b) ?_ φ hφ
    intro a
    apply Subtype.ext
    change (a : W) * (a : W) = 1
    rw [← pow_two]
    exact hW (a : W)
  have h5 : 5 ≤ rk ↥(commV (Subgroup.zpowers z)) :=
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_SL3MinDegree_holds ↥L
      (Or.inl hL)).trans hdmin
  have h6 : 6 ≤ rk ↥(commV (Subgroup.zpowers z)) := by
    rcases heven with ⟨k, hk⟩
    change 6 ≤ rk ↥(commV (Subgroup.zpowers z))
    omega
  have hrkW : rk W ≤ 12 := by
    rw [← rk_top]
    exact hrk
  have hrkC : rk ↥(fixV (Subgroup.zpowers z)) ≤ 6 := by
    have := hrank
    omega
  have hCstable : StableUnder L (fixV (Subgroup.zpowers z)) := by
    intro l hl u hu
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    calc z (l u) = (z * l) u := rfl
      _ = (l * z) u := by rw [hzc l hl]
      _ = l (z u) := rfl
      _ = l u := by rw [hu]
  rw [eq_bot_iff]
  intro w hw
  by_contra hw1
  have hCne : fixV (Subgroup.zpowers z) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hw
    exact hw1 hw
  obtain ⟨U, hUle, hUirr⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Three_exists_irr_le
    hCstable hCne
  have hUz : ∀ u ∈ U, z u = u := by
    intro u hu
    exact mem_fixV_zpowers_iff_apply.mp (hUle hu)
  have hrkU : rk U ≤ 6 := (rk_mono hUle).trans hrkC
  exact (bot_lt_iff_ne_bot.mp hUirr.1)
    (ztriv_irreducible_eq_bot hW hfix α hα hcen hzL hzc hz1 hUirr hUz hrkU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
