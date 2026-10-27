module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsEndMat
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsSelf
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TwE6RootKill


theorem ggFix_recipeConj {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {R : Type*} [Group R]
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* R)
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (h : (t : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ) :
    ggFix (TwE6Transport.recipeConj σ ε ⟨t, h⟩) =
      (Subgroup.centralizer ({t} : Set (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))).map
        ε.toMonoidHom := by
  ext r
  rw [mem_ggFix, TwE6Transport.recipeConj_apply, MulEquiv.apply_eq_iff_symm_apply,
    Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff,
    Subtype.ext_iff, RecipeExcLang.coe_twConj, mul_inv_eq_iff_eq_mul, eq_comm]
  rfl

theorem ggEndNodeRootAsSelf_of_datum (hRK : RootKill) (hCore : TwE6CorootCore) {n : ℕ}
    (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n) {R : Type} [Group R]
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* R) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n + 1) {I : Set (MulAut R)}
    (hI : ∀ φ, φ ∈ (TwE6Transport.recipeConj σ ε).range ↔ φ ∈ I)
    (hDat : ∀ A As : Subgroup (MulAut R), IsElemAbelian p A → A < As → IsElemAbelian p As →
      (As : Set (MulAut R)) ⊆ I → p ^ (if p = 3 then 4 else 5) ≤ Nat.card A →
      ∃ D : TwLangData K σ (2 ^ n) (TwE6Transport.recipeMat σ ε A), D.c = 1 ∧
        ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ) :
    GGEndNodeRootAsSelf p (if p = 3 then 4 else 5) R I := by
  intro A As hA hAAs hAs _ hAsI hr _ hV _
  obtain ⟨V, hV1, hV2, hAV⟩ := hV
  have h2 : ringChar K = 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    refine FiniteField.even_card_iff_char_two.2 ?_
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.even_iff.1 (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩)
  have hAr : A ≤ (TwE6Transport.recipeConj σ ε).range := fun φ hφ =>
    (hI φ).2 (hAsI (hAAs.le hφ))
  have hBcard := TwE6Transport.card_recipeMat σ ε hn hK hσ hAr
  obtain ⟨D, hc, hv⟩ := hDat A As hA hAAs hAs hAsI hr
  obtain ⟨t, htB, ht1, L, hL, hcomp, h7, hcent, u, huL, hu1, ⟨m, hum⟩, hucomm⟩ :=
    exists_endNode_of_datum hRK hCore hK hσ h2 hp hpn (TwE6Transport.recipeMat_le σ ε A)
      (TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hA) (by rw [hBcard]; exact hr)
      (TwE6Transport.twNormTwo_recipeMat σ ε hV1 hV2 hAV) D hc hv
  obtain ⟨hΓ, haA⟩ := (TwE6Transport.mem_recipeMat σ ε).1 htB
  set a := TwE6Transport.recipeConj σ ε ⟨t, hΓ⟩ with ha
  have hfix : ggFix a = (Subgroup.centralizer ({t} : Set _)).map ε.toMonoidHom :=
    ggFix_recipeConj σ ε t hΓ
  have hlay : LargeEvenLayer (ggFix a) = L.map ε.toMonoidHom := by
    rw [hfix, largeEvenLayer_map_of_injective ε.toMonoidHom ε.injective, hL]
  have ha1 : a ≠ 1 := fun h => ht1 (Subtype.ext (by
    simpa using congrArg Subtype.val (TwE6Transport.recipeConj_injective σ ε hn hK hσ
      (h.trans (map_one (TwE6Transport.recipeConj σ ε)).symm))))
  refine ⟨a, ⟨haA, ha1, ?_, ?_⟩, fun _ => ?_, Subgroup.zpowers (ε u), ?_, ?_, ?_, ?_⟩
  · rw [hlay, hfix]
    exact isComponentOf_map_of_injective ε.toMonoidHom ε.injective hcomp
  ·
    intro a' ha'
    rw [hlay]
    obtain ⟨w, rfl⟩ := hAr ha'
    have hwB : (w : ModGL TwistTag.E6.tag K) ∈ TwE6Transport.recipeMat σ ε A :=
      (TwE6Transport.mem_recipeMat σ ε).2 ⟨w.2, ha'⟩
    constructor
    · intro hj
      have hwL : ∀ d ∈ L, (w : ModGL TwistTag.E6.tag K) * (d : ModGL TwistTag.E6.tag K) =
          d * w := by
        intro d hd
        have h1 := hj (ε d) ⟨d, hd, rfl⟩
        rw [TwE6Transport.recipeConj_apply, MulEquiv.symm_apply_apply] at h1
        have hw2 := congrArg Subtype.val (ε.injective h1)
        rw [RecipeExcLang.coe_twConj] at hw2
        exact mul_inv_eq_iff_eq_mul.1 hw2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcent _ hwB hwL)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [ha, ← map_zpow]
      congr 1
      exact Subtype.ext (by simpa using hk)
    · intro hw j hj
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
      have haj : j ∈ ggFix a := by
        rw [hfix]
        obtain ⟨d, hd, rfl⟩ := hj
        exact ⟨d, hcomp.1 hd, rfl⟩
      have hst : a ∈ MulAction.stabilizer (MulAut R) j := haj
      have h1 := zpow_mem hst k
      rw [hk] at h1
      exact h1
  ·
    rw [hlay]
    exact Or.inl (by rw [Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective]; exact h7)
  · rw [hlay]
    exact Subgroup.zpowers_le.2 ⟨u, huL, rfl⟩
  · exact Subgroup.zpowers_ne_bot.2 fun h => hu1 (ε.injective (h.trans (map_one ε).symm))
  · refine IsPGroup.of_card_dvd_pow (n := m) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hum, map_one])
  ·
    intro a' ha' v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hfx : a' (ε u) = ε u :=
      TwE6Transport.apply_eq_of_forall_commute_recipeMat σ ε hAr u.2 hucomm ha'
    rw [map_zpow, hfx]
    exact Subgroup.zpow_mem_zpowers _ i

end CFSG.StandardType.TwE6RootAs

end
