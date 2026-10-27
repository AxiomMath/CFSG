module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloors
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5InnerL
public import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeTheta
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Inndiag
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Count

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open scoped commutatorElement

theorem rckExc_comap_pair {H M : Type} [Group H] [Group M] (Ψ : H →* M)
    (hΨ : Function.Injective Ψ) {E T : Subgroup M} (hE : E ≤ Ψ.range) (hT : T ≤ Ψ.range)
    (hTne : T ≠ ⊥) (hTp : IsPGroup 2 ↥T) (hEel : IsElemAbelian 3 E)
    (hEN : E ≤ Subgroup.normalizer (T : Set M)) :
    ∃ E' T' : Subgroup H, T' ≠ ⊥ ∧ IsPGroup 2 ↥T' ∧ IsElemAbelian 3 E' ∧
      Nat.card E' = Nat.card E ∧ E' ≤ Subgroup.normalizer (T' : Set H) := by
  refine ⟨E.comap Ψ, T.comap Ψ, ?_, ?_, ExcFrames.isElemAbelian_comap_frame Ψ hΨ hEel, ?_, ?_⟩
  · intro hbot
    apply hTne
    rw [← Subgroup.map_comap_eq_self hT, hbot, Subgroup.map_bot]
  · let ϕ : ↥(T.comap Ψ) →* ↥T :=
      { toFun := fun a => ⟨Ψ (a : H), Subgroup.mem_comap.mp a.2⟩
        map_one' := Subtype.ext (map_one Ψ)
        map_mul' := fun a b => Subtype.ext (map_mul Ψ (a : H) (b : H)) }
    refine IsPGroup.of_injective hTp ϕ ?_
    intro a b hab
    apply Subtype.ext
    exact hΨ (congrArg Subtype.val hab)
  · rw [← Subgroup.card_map_of_injective hΨ, Subgroup.map_comap_eq_self hE]
  · rw [Subgroup.le_normalizer_iff]
    intro e he t ht
    rw [Subgroup.mem_comap] at he ht ⊢
    have h2 : Ψ (e * t * e⁻¹) = Ψ e * Ψ t * (Ψ e)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp (hEN he) (Ψ t)).mp ht

theorem rckExc_card_le_pow_of_inj {H G : Type} [Group H] [Group G] [Finite G] (ι : H →* G)
    (hι : Function.Injective ι) {E T : Subgroup H} (hTne : T ≠ ⊥) (hTp : IsPGroup 2 ↥T)
    (hEel : IsElemAbelian 3 E) (hEN : E ≤ Subgroup.normalizer (T : Set H)) :
    Nat.card E ≤ 3 ^ LargeEvenTwoLocalRank 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : E.map ι ≤ Subgroup.normalizer ((T.map ι : Subgroup G) : Set G) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map ι)
  have hne : T.map ι ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι]
    exact hTne
  have h := GL83.PiGen.card_le_pow_twoLocalRank (p := 3) (hEel.map ι) (hTp.map ι) hne hnorm
  rw [Subgroup.card_map_of_injective hι] at h
  exact h

theorem rckExc_three_dvd_two_pow_succ_of_odd {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  have h := Odd.nat_add_dvd_pow_add_pow 2 1 hf
  simpa using h

theorem rckExc_twE6_facts
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .twistedE6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L) (hp3 : p = 3) (hf : 1 ≤ f) :
    Subgroup.center ↥G₀ = ⊥ ∧ Nonempty (TableCRes.TwE6Act G₀ A hf) := by
  have hZ := rckExc_center_bot_twE6_core h hp3
  refine ⟨hZ, ?_⟩
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, -⟩
  exact TableCRes.exists_act_twE6_of_facts hGG.2.1.2 hGG.2.2.1 hGG.2.1.1 hAc hAnorm
    (ggPsiInnerDiag_of_marking hGG hMarkG0 hAnorm) hf

theorem rckExc_floorsTwNine_holds
    : RCKExcFloorsTwNine := by
  intro X _ _ n f ψ p G₀ A B₁ D J L hcfg hp3 h9
  have hcfg' := hcfg
  unfold RCKCompCore at hcfg'
  rcases hcfg' with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, -⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  obtain ⟨hZ, ⟨act⟩⟩ := rckExc_twE6_facts hcfg hp3 hf
  subst hp3
  have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : GaloisField 2 (2 * f), (frobQEquiv hf) c = c ^ 2 ^ f := fun c =>
    CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  have h3 : 3 ∣ 2 ^ f + 1 := (by norm_num : 3 ∣ 9).trans h9
  obtain ⟨E, T, hEtw, hTtw, hEel, hEcard, hTp, hTne, hEnorm⟩ :=
    TableCRes.exists_twoLocal_rankFive_twE6 hf hcard (frobQEquiv hf) hσ h3
  obtain ⟨Y, hEY, -, -, -, hY9⟩ :=
    TwE6DD2.exists_cubeTorus hf hcard (frobQEquiv hf) hσ h3 hEel hEtw hEcard
  have hEinn := hEY.trans (hY9 h9).1
  have hTinn : T ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQEquiv hf).toRingHom) →* MulAut ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom)).range := by
    intro t ht
    obtain ⟨k, hk⟩ := hTp ⟨t, ht⟩
    have ht' : t ∈ LayerSixE.twInndiagAut f := by
      rw [twInndiagAut_eq_range_twConj hf]
      exact hTtw ht
    have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact LieKnownR2.twInndiagAut_two_mem_inner f ht' (n := k) hk'
  let φ₀ : ↥G₀ →* ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQEquiv hf).toRingHom) :=
    act.θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥G₀))
  have hφ₀inj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : act.θ (QuotientGroup.mk' (Subgroup.center ↥G₀) x) = 1 := hx
    have hx1 : (QuotientGroup.mk' (Subgroup.center ↥G₀) x) = 1 :=
      act.θ.injective (hx'.trans (map_one act.θ).symm)
    have hxc : x ∈ Subgroup.center ↥G₀ := (QuotientGroup.eq_one_iff x).mp hx1
    rw [hZ] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hφ₀surj : Function.Surjective φ₀ := fun c => by
    obtain ⟨q, hq⟩ := act.θ.surjective c
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥G₀) q
    refine ⟨x, ?_⟩
    show act.θ (QuotientGroup.mk' (Subgroup.center ↥G₀) x) = c
    rw [hx]
    exact hq
  have hCZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQEquiv hf).toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (frobQEquiv hf).surjective
  have hconjinj : Function.Injective (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom) →* MulAut ↥(graphFixedRootGroup
        TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQEquiv hf).toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro a
      have ha := congrArg (fun φ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQEquiv hf).toRingHom) => φ a) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at ha
      calc a * g = (g * a * g⁻¹) * g := by rw [ha]
        _ = g * a := by group
    rw [hCZ] at hgc
    exact Subgroup.mem_bot.mp hgc
  let Ψ : ↥G₀ →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQEquiv hf).toRingHom) := MulAut.conj.comp φ₀
  have hΨinj : Function.Injective Ψ := hconjinj.comp hφ₀inj
  have hΨrange : Ψ.range = (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom) →* MulAut ↥(graphFixedRootGroup
        TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom)).range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ₀ x, rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨x, rfl⟩ := hφ₀surj c
      exact ⟨x, rfl⟩
  obtain ⟨E', T', hT'ne, hT'p, hE'el, hE'card, hE'N⟩ :=
    rckExc_comap_pair Ψ hΨinj (by rw [hΨrange]; exact hEinn) (by rw [hΨrange]; exact hTinn)
      hTne hTp hEel hEnorm
  have hcardle := rckExc_card_le_pow_of_inj
    (Subgroup.inclusion (le_sup_right : G₀ ≤ A ⊔ G₀)) (Subgroup.inclusion_injective _)
    hT'ne hT'p hE'el hE'N
  calc 3 ^ 5 ≤ Nat.card E := hEcard
    _ = Nat.card E' := hE'card.symm
    _ ≤ 3 ^ LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) := hcardle
    _ ≤ Nat.card A := hrank2

theorem rckExc_floorsTwOut_holds
    : RCKExcFloorsTwOut := by
  intro X _ _ n f ψ p G₀ A B₁ D J L hcfg θ A' hfr hp3 hodd hnR
  have hcfg' := hcfg
  unfold RCKCompCore at hcfg'
  rcases hcfg' with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, -⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  obtain ⟨hZ, ⟨act⟩⟩ := rckExc_twE6_facts hcfg hp3 hf
  subst hp3
  obtain ⟨hθker, hθrange, hA'le, hA'el, hA'card, hfwd, hbwd⟩ := hfr
  have hcentR : ∀ z ∈ ggFixGp .twistedE6 f,
      (∀ r ∈ ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆, z * r = r * z) → z = 1 := by
    obtain ⟨θ₀, -, -, hθ₀range, hθ₀cent⟩ :=
      LieCore.ggLieBridge_theta (t := .twistedE6) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hf hGG
    intro z hz hc
    refine hθ₀cent z hz (fun x => hc (θ₀ x) ?_)
    rw [← hθ₀range]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  obtain ⟨a, haA', haR⟩ := SetLike.not_le_iff_exists.mp hnR
  obtain ⟨d, hdA, hdact⟩ := hbwd a haA'
  have hnoninn : ¬ ∃ g : ↥G₀, ∀ y : ↥G₀,
      (d : X) * (y : X) * (d : X)⁻¹ = (g : X) * (y : X) * (g : X)⁻¹ := by
    rintro ⟨g, hg⟩
    have hRΓ : ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ ≤ ggFixGp .twistedE6 f :=
      Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
          (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
    have hθgR : θ g ∈ ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ := by
      rw [← hθrange]
      exact MonoidHom.mem_range.2 ⟨g, rfl⟩
    have hz : a⁻¹ * θ g ∈ ggFixGp .twistedE6 f :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hA'le haA')) (hRΓ hθgR)
    have hz1 : a⁻¹ * θ g = 1 := by
      refine hcentR _ hz (fun r hr => ?_)
      rw [← hθrange] at hr
      obtain ⟨x, rfl⟩ := hr
      have hdn : (d : X) * (x : X) * (d : X)⁻¹ ∈ G₀ :=
        (Subgroup.mem_normalizer_iff.mp (hAnorm hdA) x).mp x.2
      have h1 := hdact x hdn
      have h2 : (⟨(d : X) * (x : X) * (d : X)⁻¹, hdn⟩ : ↥G₀) = g * x * g⁻¹ :=
        Subtype.ext (hg x)
      rw [h2, map_mul, map_mul, map_inv] at h1
      calc a⁻¹ * θ g * θ x = a⁻¹ * (θ g * θ x * (θ g)⁻¹) * θ g := by group
        _ = a⁻¹ * (a * θ x * a⁻¹) * θ g := by rw [h1]
        _ = θ x * (a⁻¹ * θ g) := by group
    apply haR
    rw [inv_mul_eq_one.mp hz1, ← hθrange]
    exact MonoidHom.mem_range.2 ⟨g, rfl⟩
  let φ₀ : ↥G₀ →* ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQEquiv hf).toRingHom) :=
    act.θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥G₀))
  have hφ₀inj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : act.θ (QuotientGroup.mk' (Subgroup.center ↥G₀) x) = 1 := hx
    have hx1 : (QuotientGroup.mk' (Subgroup.center ↥G₀) x) = 1 :=
      act.θ.injective (hx'.trans (map_one act.θ).symm)
    have hxc : x ∈ Subgroup.center ↥G₀ := (QuotientGroup.eq_one_iff x).mp hx1
    rw [hZ] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hφ₀surj : Function.Surjective φ₀ := fun c => by
    obtain ⟨q, hq⟩ := act.θ.surjective c
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥G₀) q
    refine ⟨x, ?_⟩
    show act.θ (QuotientGroup.mk' (Subgroup.center ↥G₀) x) = c
    rw [hx]
    exact hq
  let b : ↥A := ⟨d, hdA⟩
  have hlam_out : (act.lam b : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∉
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom := by
    intro hmem
    apply hnoninn
    obtain ⟨g, hgc⟩ := hφ₀surj ⟨_, hmem⟩
    refine ⟨g, fun y => ?_⟩
    have hdy : (d : X) * (y : X) * (d : X)⁻¹ ∈ G₀ :=
      (Subgroup.mem_normalizer_iff.mp (hAnorm hdA) y).mp y.2
    have hact := act.act b y ⟨_, hdy⟩ rfl
    have hφ : φ₀ ⟨_, hdy⟩ = φ₀ (g * y * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hgc]
      apply Subtype.ext
      exact hact
    exact congrArg Subtype.val (hφ₀inj hφ)
  have h3 : 3 ∣ 2 ^ f + 1 := rckExc_three_dvd_two_pow_succ_of_odd hodd
  have hB3 : ∀ x ∈ A, x ^ 3 = 1 := hAel.2
  obtain ⟨E, T, hTne, hT2, hEel, hEcard, hEN⟩ :=
    TableCRes.TwE6Act.exists_twoLocal_rankFive_of_outer hf hB3 hAnorm h3 hZ act b hlam_out
  have hHle : G₀ ⊔ Subgroup.zpowers (b : X) ≤ A ⊔ G₀ :=
    sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left b.2))
  have hcardle := rckExc_card_le_pow_of_inj (Subgroup.inclusion hHle)
    (Subgroup.inclusion_injective hHle) hTne hT2 hEel hEN
  calc 3 ^ 5 ≤ Nat.card E := hEcard
    _ ≤ 3 ^ LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) := hcardle
    _ ≤ Nat.card A := hrank2

theorem rckExcFloorsTwE6_frame
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ A B₁ D J L : Subgroup X} (h : RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L)
    {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL}
    {A' : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hfr : RCKBridgeFrame .twistedE6 f p G₀ A θ A') :
    CFSG.StandardType.RCKBand.StepZeroRankFloor .twistedE6 f p A' := by
  have hcard : Nat.card A' = Nat.card A := hfr.2.2.2.2.1
  refine ⟨fun hp3 => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro (h | h) <;> cases h
  · intro h; cases h
  · intro _ h9
    rw [hcard]
    exact rckExc_floorsTwNine_holds X n f ψ p G₀ A B₁ D J L h hp3 h9
  · intro _ hodd hnR
    rw [hcard]
    exact rckExc_floorsTwOut_holds X n f ψ p G₀ A B₁ D J L h θ A' hfr hp3 hodd hnR
  · intro h; cases h

theorem rckExcFloors_holds
    : RCKExcFloors :=
  rck_exc_floors_of_tw rckExc_floorsTwNine_holds rckExc_floorsTwOut_holds

theorem rckExcCaseVReduction_holds
    : RCKExcCaseVReduction :=
  rckExcCaseVReduction_of_floors rckExcFloors_holds

end CFSG.StandardType.RCKRP
