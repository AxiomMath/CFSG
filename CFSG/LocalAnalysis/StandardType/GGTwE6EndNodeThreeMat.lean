module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6RootKill CFSG.StandardType.TwE6RootAs

section Plain

theorem conj_injective_of_center_bot {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut G => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * a = a * g * a⁻¹ * a := by rw [h]
      _ = a * g := by group
  rwa [hZ, Subgroup.mem_bot] at hc

theorem mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (c : G) :
    φ * MulAut.conj c * φ⁻¹ = MulAut.conj (φ c) := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

end Plain

section Mat


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem mem_twMatPre {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    {x : ModGL TwistTag.E6.tag K} :
    x ∈ twMatPre K σ S ↔
      ∃ h : x ∈ RecipeExcLang.twInndiagGroup K σ, RecipeExcLang.twConj K σ ⟨x, h⟩ ∈ S :=
  ⟨by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩, fun ⟨h, hS⟩ => ⟨⟨x, h⟩, hS, rfl⟩⟩

theorem twMatPre_le (S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) :
    twMatPre K σ S ≤ twistedE6InndiagGL K σ :=
  (Subgroup.map_subtype_le _).trans (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ)

theorem card_twMatPre {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hY : Y ≤ (RecipeExcLang.twConj K σ).range) : Nat.card (twMatPre K σ Y) = Nat.card Y := by
  rw [twMatPre, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    ← Subgroup.card_map_of_injective (NoOffTwE6Three.twConj_injective hn hK σ hσ),
    Subgroup.map_comap_eq, inf_eq_right.2 hY]

theorem isElemAbelian_twMatPre {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ} {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hY : IsElemAbelian p Y) : IsElemAbelian p (twMatPre K σ Y) :=
  (hY.comap (NoOffTwE6Three.twConj_injective hn hK σ hσ)).map _

theorem twistedE6InndiagConj_eq_twConj (w : RecipeExcLang.twInndiagGroup K σ)
    (hw : (w : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ) :
    twistedE6InndiagConj K σ ⟨w, hw⟩ = RecipeExcLang.twConj K σ w :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem range_twistedE6InndiagConj_le :
    (twistedE6InndiagConj K σ).range ≤ (RecipeExcLang.twConj K σ).range := by
  rintro _ ⟨⟨a, ha⟩, rfl⟩
  have hΓ := TwE6FieldCore.twistedE6InndiagGL_le_twInndiagGroup σ ha
  exact ⟨⟨a, hΓ⟩, (twistedE6InndiagConj_eq_twConj σ ⟨a, hΓ⟩ ha).symm⟩

theorem mem_range_conj_of_two_pow {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n}
    (hε : ∀ x : MulAut ↥(twistedE6RootGroup K σ),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {φ : MulAut ↥(twistedE6RootGroup K σ)} (hφ : φ ∈ (RecipeExcLang.twConj K σ).range)
    {k : ℕ} (hk : φ ^ 2 ^ k = 1) :
    φ ∈ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range := by
  set ψ : MulAut (TwE6Delta.RecipeR K n) := MulAut.congr ε φ with hψ
  have h3 := TwE6Delta.pow_three_mem_inn hn hK ((hε φ).2 hφ)
  have hψk : ψ ^ 2 ^ k = 1 := by rw [hψ, ← map_pow, hk, map_one]
  have hcop : Nat.Coprime 3 (orderOf ψ) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hψk)
      (Nat.Coprime.pow_right k (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hψc : ψ ∈ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
    rw [← hm]
    exact Subgroup.pow_mem _ h3 m
  obtain ⟨r, hr⟩ := hψc
  refine ⟨ε.symm r, MulEquiv.ext fun x => ?_⟩
  have h1 : r * ε x * r⁻¹ = ε (φ x) := by
    have h := congrArg (fun f : MulAut (TwE6Delta.RecipeR K n) => f (ε x)) hr
    simp only [MulAut.conj_apply] at h
    rw [h, hψ]
    change ε (φ (ε.symm (ε x))) = ε (φ x)
    rw [MulEquiv.symm_apply_apply]
  have h2 : φ x = ε.symm (r * ε x * r⁻¹) := by rw [h1, MulEquiv.symm_apply_apply]
  rw [h2, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem twNormTwo_of_inner (hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥)
    {Y V : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hVI : V ≤ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range)
    (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) : TwNormTwo K σ (twMatPre K σ Y) := by
  have hinj := conj_injective_of_center_bot hZ
  set U₀ : Subgroup ↥(twistedE6RootGroup K σ) :=
    V.comap (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) with hU₀
  refine ⟨U₀.map (twistedE6RootGroup K σ).subtype, Subgroup.map_subtype_le _, fun hbot => hV1 ?_,
    (hV2.comap_of_injective _ hinj).map _, ?_⟩
  · rw [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hbot
    refine (Subgroup.eq_bot_iff_forall V).2 fun v hv => ?_
    obtain ⟨c, rfl⟩ := hVI hv
    have hc : c ∈ U₀ := hv
    rw [hbot, Subgroup.mem_bot] at hc
    rw [hc, map_one]
  · rintro x hx _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨RecipeExcLang.twConj K σ w u, ?_, rfl⟩
    change MulAut.conj (RecipeExcLang.twConj K σ w u) ∈ V
    rw [← mul_conj_mul_inv]
    exact hYV _ hw _ hu

end Mat

end CFSG.StandardType.TwE6EndNode3

end
