module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTriD4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover CFSG.SeitzReduction CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.HighestRoot
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

private theorem rckK1Ilat_map_conj_one {K : Type*} [Group K] (H : Subgroup K) :
    H.map (MulAut.conj (1 : K)).toMonoidHom = H := by
  ext y
  simp [MulAut.conj_apply]

private theorem rckK1Ilat_map_conj_mul {K : Type*} [Group K] (H : Subgroup K) (a b : K) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem rckK1Ilat_center_bot_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g) :
    Subgroup.center (triD4Universal F σ).K = ⊥ := by
  have hq : 2 ≤ 2 ^ g := Nat.le_self_pow (by have := hF.1; omega) 2
  exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (K := F) hq hF.2.1 hF.2.2

private theorem rckK1Ilat_longRootConj_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β β' : Fin (Tag.rank .G2) → ℤ}
    (hβ : GGLongRoot (triD4Universal F σ).D β) (hβ' : GGLongRoot (triD4Universal F σ).D β') :
    ∃ u : (triD4Universal F σ).K,
      (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) =
        (triD4Universal F σ).D.rootGroup β' := by
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hF.2.1 hF.2.2
  obtain ⟨m, hm⟩ := CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4_longRoot_conj σ hσ hβ
  obtain ⟨m', hm'⟩ := CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4_longRoot_conj σ hσ hβ'
  refine ⟨m' * m⁻¹, ?_⟩
  change ((twistedDatum σ).rootGroup β).map (MulAut.conj (m' * m⁻¹)).toMonoidHom = (twistedDatum σ).rootGroup β'
  rw [hm, hm', ← rckK1Ilat_map_conj_mul, inv_mul_cancel_right]

theorem rckK1I_lemmaA_triD4
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X)
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    (ψ : (triD4Universal F σ).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (triD4Universal F σ).K)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hβ : β ∈ (triD4Universal F σ).D.roots)
    (hlong : GGLongRoot (triD4Universal F σ).D β)
    {x₀ : (triD4Universal F σ).K} (hx₀ : x₀ ∈ (triD4Universal F σ).D.rootGroup β) (hx₀1 : ψ x₀ ≠ 1) (α : MulAut X)
    (hα : α (ψ x₀) = ψ x₀) :
    (((triD4Universal F σ).D.rootGroup β).map ψ).map α.toMonoidHom = ((triD4Universal F σ).D.rootGroup β).map ψ := by
  classical
  let D := (triD4Universal F σ).D
  let K := (triD4Universal F σ).K
  have hperfK : commutator K = ⊤ := by
    haveI : Group.IsPerfect K := by
      change Group.IsPerfect (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)
      exact CFSG.LieType.Steinberg.TwistedD4.twistedGroup_isPerfect_of_card (q := 2 ^ g)
        (Nat.le_self_pow (by have := hF.1; omega) 2) hF.2.1 hF.2.2
    exact Group.IsPerfect.commutator_eq_top
  haveI : Group.IsPerfect K := ⟨hperfK⟩
  have hperfX : Group.IsPerfect X := Group.IsPerfect.ofSurjective hψ
  have hcommX : commutator X = ⊤ := hperfX.commutator_eq_top
  have hnabX : ¬ IsMulCommutative X := by
    intro hcomm
    have hbot : commutator X = ⊥ := (commutator_eq_bot_iff X).mpr hcomm
    rw [hcommX] at hbot
    exact top_ne_bot hbot
  have hZX : Subgroup.center X = ⊥ := by
    rcases hX.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · rw [Subgroup.center_eq_top_iff] at h
      exact absurd h hnabX
  have hsimplequot : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hZX).trans (QuotientGroup.quotientBot (G := X)))
  have hQX : CFSG.Assembly.IsQuasisimple X := ⟨hcommX, hsimplequot⟩
  have hQtop : CFSG.Assembly.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hQX
  have hZoddTop : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup X))) := by
    have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup X)) =
        Nat.card (Subgroup.center X) :=
      Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv (G := X))).toEquiv
    rw [hcard, hZX, Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have hposα : GGRootPosJ (⊤ : Subgroup X)
      (((D.rootGroup β).map ψ).map α.toMonoidHom)
      (((D.rootGroup (-β)).map ψ).map α.toMonoidHom) := by
    refine Or.inr ⟨F, inferInstance, inferInstance, σ, g, β, hF, hlong, ?_⟩
    refine ⟨α.toMonoidHom.comp ψ, ?_, ?_, 1, ?_, ?_⟩
    · apply MonoidHom.range_eq_top_of_surjective
      intro x
      obtain ⟨k, hk⟩ := hψ (α.symm x)
      exact ⟨k, by
        change α (ψ k) = x
        rw [hk, MulEquiv.apply_symm_apply]⟩
    · intro k hk
      apply hker
      apply α.injective
      simpa using hk
    · rw [ggRootSub, rckK1Ilat_map_conj_one, Subgroup.map_map]
    · rw [ggRootSub, rckK1Ilat_map_conj_one, Subgroup.map_map]
  obtain ⟨γ, u, hγ, hlongγ, hαR, _hαRm⟩ :=
    (hIRG X ⊤ (((D.rootGroup β).map ψ).map α.toMonoidHom)
      (((D.rootGroup (-β)).map ψ).map α.toMonoidHom) hQtop hZoddTop hposα).2
      F σ g ψ hF (MonoidHom.range_eq_top_of_surjective ψ hψ) hker
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP F 2 := CFSG.StandardType.RCKC1.charP_two_of_triField hF
  have hrootP : ∀ δ ∈ D.roots, IsPGroup 2 (D.rootGroup δ) := by
    intro δ hδ
    exact isPGroup_twistedD4_rootGroup (K := F) σ (sigma_three_of_card hF.2.1 hF.2.2)
      (isRoot_of_mem_twistedDatum_roots σ hδ)
  have hx0R : ψ x₀ ∈ (D.rootGroup β).map ψ := Subgroup.mem_map_of_mem ψ hx₀
  have hx0αR : ψ x₀ ∈ ((D.rootGroup β).map ψ).map α.toMonoidHom :=
    ⟨ψ x₀, hx0R, hα⟩
  rw [hαR] at hx0αR
  rw [ggRootSub] at hx0αR
  obtain ⟨y, hy, hψy⟩ := Subgroup.mem_map.mp hx0αR
  have hPβ : IsPGroup 2 (D.rootGroup β) := hrootP β hβ
  have hPγ : IsPGroup 2 ((D.rootGroup γ).map (MulAut.conj u).toMonoidHom) :=
    (hrootP γ hγ).map _
  obtain ⟨a, ha⟩ := hPβ ⟨x₀, hx₀⟩
  obtain ⟨b, hb⟩ := hPγ ⟨y, hy⟩
  have ha' : x₀ ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : y ^ 2 ^ b = 1 := congrArg Subtype.val hb
  let z : K := x₀⁻¹ * y
  have hzker : ψ z = 1 := by
    change ψ (x₀⁻¹ * y) = 1
    rw [map_mul, map_inv, hψy, inv_mul_cancel]
  have hzcenter : z ∈ Subgroup.center K := hker hzker
  have hy_eq : y = x₀ * z := by
    change y = x₀ * (x₀⁻¹ * y)
    group
  have hcomm : Commute x₀ y := by
    rw [hy_eq]
    have hzc : Commute x₀ z := (Subgroup.mem_center_iff.mp hzcenter x₀)
    exact (Commute.refl x₀).mul_right hzc
  have hxapow : x₀ ^ 2 ^ (a + b) = 1 := by
    rw [pow_add, pow_mul, ha', one_pow]
  have hyapow : y ^ 2 ^ (a + b) = 1 := by
    rw [pow_add, mul_comm (2 ^ a) (2 ^ b), pow_mul, hb', one_pow]
  have hzpow : z ^ 2 ^ (a + b) = 1 := by
    change (x₀⁻¹ * y) ^ 2 ^ (a + b) = 1
    rw [hcomm.inv_left.mul_pow, inv_pow, hxapow, hyapow, inv_one, one_mul]
  have hZoddK : Odd (Nat.card (Subgroup.center K)) := by
    rw [rckK1Ilat_center_bot_triD4 hF, Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ 2 ^ (a + b) := orderOf_dvd_of_pow_eq_one hzpow
    have h2 : orderOf z ∣ Nat.card (Subgroup.center K) :=
      Subgroup.orderOf_dvd_natCard _ hzcenter
    have hcop : Nat.Coprime (2 ^ (a + b)) (Nat.card (Subgroup.center K)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZoddK)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hx0y : x₀ = y := by
    have h : x₀⁻¹ * y = 1 := hz1
    have hyx : y = x₀ := by
      rw [← mul_inv_cancel_left x₀ y, h, mul_one]
    exact hyx.symm
  have hmemγ : x₀ ∈ (D.rootGroup γ).map (MulAut.conj u).toMonoidHom := by
    rwa [hx0y]
  obtain ⟨v, hv⟩ := rckK1Ilat_longRootConj_triD4 hF hlongγ hlong
  have hγeq : D.rootGroup γ =
      (D.rootGroup β).map (MulAut.conj v⁻¹).toMonoidHom := by
    have h := congrArg (Subgroup.map (MulAut.conj v⁻¹).toMonoidHom) hv
    rw [← rckK1Ilat_map_conj_mul, inv_mul_cancel, rckK1Ilat_map_conj_one] at h
    exact h
  have hmemn : x₀ ∈ (D.rootGroup β).map (MulAut.conj (u * v⁻¹)).toMonoidHom := by
    rw [hγeq] at hmemγ
    rwa [← rckK1Ilat_map_conj_mul] at hmemγ
  obtain ⟨yβ, hyβ, hyβeq⟩ := Subgroup.mem_map.mp hmemn
  have hyβeq' : (u * v⁻¹) * yβ * (u * v⁻¹)⁻¹ = x₀ := by
    simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hyβeq
  have hconj_x : (u * v⁻¹)⁻¹ * x₀ * ((u * v⁻¹)⁻¹)⁻¹ = yβ := by
    calc (u * v⁻¹)⁻¹ * x₀ * ((u * v⁻¹)⁻¹)⁻¹
        = (u * v⁻¹)⁻¹ * ((u * v⁻¹) * yβ * (u * v⁻¹)⁻¹) *
            ((u * v⁻¹)⁻¹)⁻¹ := by rw [hyβeq']
      _ = yβ := by group
  have hx₀1K : x₀ ≠ 1 := by
    intro h; exact hx₀1 (by rw [h, map_one])
  have hTI := (rck_lemmaH_triD4 hF hlong).1
  have hN : u * v⁻¹ ∈ Subgroup.normalizer (D.rootGroup β : Set K) := by
    have hk : (u * v⁻¹)⁻¹ ∈ Subgroup.normalizer (D.rootGroup β : Set K) :=
      hTI x₀ hx₀ hx₀1K ((u * v⁻¹)⁻¹) (by rw [hconj_x]; exact hyβ)
    simpa using Subgroup.inv_mem _ hk
  have hγu : (D.rootGroup γ).map (MulAut.conj u).toMonoidHom = D.rootGroup β := by
    rw [hγeq, ← rckK1Ilat_map_conj_mul]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hN)
  calc ((D.rootGroup β).map ψ).map α.toMonoidHom
      = ggRootSub D ψ γ u := hαR
    _ = (D.rootGroup β).map ψ := by rw [ggRootSub, hγu]

end CFSG.StandardType.RCKK1I
