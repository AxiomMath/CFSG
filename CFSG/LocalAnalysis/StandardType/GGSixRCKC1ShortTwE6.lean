module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortTwE6Adj
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortTwE6Aux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortTwE6Sc
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Conj
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelInvolutions

public section

namespace CFSG.StandardType.RCKC1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType
  CFSG.StandardType.LieKnownR2.Short

private theorem rckTwE6Main_exists_pow_two_eq_one_of_mem_pCoreOf {X : Type*} [Group X]
    {H : Subgroup X} {k : X} (hk : k ∈ pCoreOf 2 H) :
    ∃ b : ℕ, k ^ 2 ^ b = 1 := by
  have hP : IsPGroup 2 (pCoreOf 2 H) := by
    change IsPGroup 2 ((pCore 2 ↥H).map H.subtype)
    exact (pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  obtain ⟨b, hb⟩ := hP ⟨k, hk⟩
  exact ⟨b, by simpa using congrArg (Subtype.val) hb⟩

private theorem rckTwE6Main_conj_pow_apply {G : Type*} [Group G] {k y z : G}
    (hz : z ∈ Subgroup.center G) (h : k * y * k⁻¹ = z * y) (n : ℕ) :
    ((MulAut.conj k) ^ n) y = z ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul]
    have hzpow : (MulAut.conj k) (z ^ n) = z ^ n := by
      rw [MulAut.conj_apply]
      have hzc : z ^ n ∈ Subgroup.center G := pow_mem hz n
      have hcomm := Subgroup.mem_center_iff.mp hzc k
      rw [hcomm]; group
    rw [hzpow, MulAut.conj_apply, h, pow_succ]
    group

section Core


theorem rckTwE6_core_xPair_one {f : ℕ} (hf : 1 ≤ f) :
    pCoreOf 2 (centralizer ({rckTwE6X (frobQ 2 f) (frobQ_frobQ 2 f hf) 1} :
        Set (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)))) ≤
      centralizer ((twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup twE6Alpha :
        Set (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f hf
  have hK : Nat.card k = (2 ^ f) ^ 2 := by
    show Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, θ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  let π : fixedGroup k θ →* graphFixedRootGroup TwistTag.E6 k θ :=
    F4Pilot.twistedIsogenyC hf hK θ hσ
  let x₁ : fixedGroup k θ := rckTwE6X θ hθ 1
  have hfinK : Finite (fixedGroup k θ) := by
    have := CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid k
    exact Subtype.finite
  have hfinC : Finite (graphFixedRootGroup TwistTag.E6 k θ) := by
    have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
    exact Subtype.finite
  have hsurj : Function.Surjective π := F4Pilot.twistedIsogenyC_surjective hf hK θ hσ
  have hker : π.ker = Subgroup.center (fixedGroup k θ) :=
    F4Pilot.ker_twistedIsogenyC hf hK θ hσ
  have hodd : Odd (Nat.card π.ker) :=
    CFSG.StandardType.RootDetectTwE6.odd_card_ker f π (fun _ => rfl)
  have hx₁sq : x₁ * x₁ = 1 := rckTwE6X_mul_self θ hθ 1
  have hx₁ne : x₁ ≠ 1 := rckTwE6X_one_ne_one θ hθ
  have horder : orderOf x₁ = 2 :=
    orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) (by simpa [pow_two] using hx₁sq) hx₁ne
  have hcent : (Subgroup.centralizer ({x₁} : Set (fixedGroup k θ))).map π =
      Subgroup.centralizer ({π x₁} : Set (graphFixedRootGroup TwistTag.E6 k θ)) :=
    CFSG.ComponentClassification.OddKernelInvolutions.image_centralizer π hsurj hodd x₁ horder
  have hM : π.ker ≤ Subgroup.centralizer ({x₁} : Set (fixedGroup k θ)) :=
    hker.le.trans (Subgroup.center_le_centralizer _)
  have hmapcore : (pCoreOf 2 (Subgroup.centralizer ({x₁} : Set (fixedGroup k θ)))).map π =
      pCoreOf 2 (Subgroup.centralizer ({π x₁} :
        Set (graphFixedRootGroup TwistTag.E6 k θ))) := by
    rw [CFSG.StandardType.LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hker.le hodd hM, hcent]
  have hstd : π x₁ = stdRepC (apply_apply_eq hK hσ) 1 :=
    rckTwE6_pi_xPair_one hf hK θ hσ hθ
  have hk : Nat.card (fixedSubfield θ) = 2 ^ f := card_fixedSubfield_of_card θ hK hσ
  have hle : pCoreOf 2 (Subgroup.centralizer ({π x₁} :
      Set (graphFixedRootGroup TwistTag.E6 k θ))) ≤
      (uRadical θ).subgroupOf (graphFixedRootGroup TwistTag.E6 k θ) := by
    rw [hstd]
    exact rckTwE6_pCoreOf_centralizer_stdRepC_one_le (k := fixedSubfield θ) hf hk hK hσ
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (rckTwE6_mem_rootGroup_iff θ hθ y).mp hy
  have htcore : π t ∈ pCoreOf 2 (Subgroup.centralizer ({π x₁} :
      Set (graphFixedRootGroup TwistTag.E6 k θ))) := by
    rw [← hmapcore]
    exact Subgroup.mem_map_of_mem π ht
  have htQ : π t ∈ (uRadical θ).subgroupOf (graphFixedRootGroup TwistTag.E6 k θ) := hle htcore
  have htP : ((π t : graphFixedRootGroup TwistTag.E6 k θ) : ModGL TwistTag.E6.tag k) ∈
      parabolicRadical TwistTag.E6.tag k E6Pilot.nodes16 := by
    have h1 := Subgroup.mem_subgroupOf.mp htQ
    rw [uRadical, Subgroup.mem_inf] at h1
    exact h1.1
  have hy'pi := rckTwE6_coe_pi_xPair (f := f) hf hK θ hσ hθ c
  have hπx : π (rckTwE6X θ hθ c) =
      F4Pilot.twistedIsogenyC hf hK θ hσ (rckTwE6X θ hθ c) := rfl
  have hcomm : ((π t : graphFixedRootGroup TwistTag.E6 k θ) : ModGL TwistTag.E6.tag k) *
      ((π (rckTwE6X θ hθ c) : graphFixedRootGroup TwistTag.E6 k θ) : ModGL TwistTag.E6.tag k) =
      ((π (rckTwE6X θ hθ c) : graphFixedRootGroup TwistTag.E6 k θ) : ModGL TwistTag.E6.tag k) *
        ((π t : graphFixedRootGroup TwistTag.E6 k θ) : ModGL TwistTag.E6.tag k) := by
    rw [hπx, hy'pi]
    exact Subgroup.mem_centralizer_singleton_iff.mp
      ((rckTwE6_parabolicRadical_le_centralizer (K := k) c (θ c)) htP)
  let z : fixedGroup k θ := t * rckTwE6X θ hθ c * t⁻¹ * (rckTwE6X θ hθ c)⁻¹
  have hzdef : z = t * rckTwE6X θ hθ c * t⁻¹ * (rckTwE6X θ hθ c)⁻¹ := rfl
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have hz : π z = π t * π (rckTwE6X θ hθ c) * (π t)⁻¹ *
        (π (rckTwE6X θ hθ c))⁻¹ := by
      rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hz]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hcomm]
    group
  have hzcenter : z ∈ Subgroup.center (fixedGroup k θ) := hker ▸ hzker
  have hzy : t * rckTwE6X θ hθ c * t⁻¹ = z * rckTwE6X θ hθ c := by
    rw [hzdef]; group
  obtain ⟨b, htb⟩ := rckTwE6Main_exists_pow_two_eq_one_of_mem_pCoreOf ht
  have hconj := rckTwE6Main_conj_pow_apply hzcenter hzy (2 ^ b)
  have htriv : ((MulAut.conj t) ^ 2 ^ b) (rckTwE6X θ hθ c) = rckTwE6X θ hθ c := by
    have hdvd : orderOf (MulAut.conj t) ∣ 2 ^ b :=
      (orderOf_map_dvd (MulAut.conj : fixedGroup k θ →* MulAut (fixedGroup k θ)) t).trans
        (orderOf_dvd_of_pow_eq_one htb)
    rw [orderOf_dvd_iff_pow_eq_one.mp hdvd]
    rfl
  have hzpow : z ^ 2 ^ b = 1 := by
    have h := hconj
    rw [htriv] at h
    exact (mul_right_cancel (show (1 : fixedGroup k θ) * rckTwE6X θ hθ c =
      z ^ 2 ^ b * rckTwE6X θ hθ c by simpa using h)).symm
  have hz1 : z = 1 := by
    have hdvd : orderOf z ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hzpow
    have hcard : orderOf z ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hzker
    have hcop : Nat.Coprime (2 ^ b) (Nat.card π.ker) :=
      (Nat.coprime_two_left.mpr hodd).pow_left b
    have h1 : orderOf z = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hdvd hcop) hcard
    exact orderOf_eq_one_iff.mp h1
  have h1 : t * rckTwE6X θ hθ c * t⁻¹ = rckTwE6X θ hθ c := by
    rw [hzy, hz1, one_mul]
  have h1t : t * rckTwE6X θ hθ c = rckTwE6X θ hθ c * t := (mul_inv_eq_iff_eq_mul.mp h1)
  exact h1t.symm

theorem rckTwE6_core_alpha {f : ℕ} (hf : 1 ≤ f) :
    ∀ x ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup twE6Alpha, x ≠ 1 →
      pCoreOf 2 (centralizer ({x} : Set (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)))) ≤
        centralizer ((twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup twE6Alpha :
          Set (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f hf
  intro x hx hx1
  obtain ⟨c, rfl⟩ := (rckTwE6_mem_rootGroup_iff θ hθ x).mp hx
  have hc : c ≠ 0 := by
    intro hc0
    apply hx1
    rw [hc0, rckTwE6X_zero θ hθ]
  obtain ⟨s, hs⟩ := rckTwE6_exists_conj_xPair θ hθ hc
  let X : Subgroup (fixedGroup k θ) := (twistedDatum k θ).rootGroup twE6Alpha
  have hmap_le : X.map (MulAut.conj s).toMonoidHom ≤ X := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨d, rfl⟩ := (rckTwE6_mem_rootGroup_iff θ hθ z).mp hz
    rw [show (MulAut.conj s).toMonoidHom (rckTwE6X θ hθ d) =
      rckTwE6X θ hθ (c * d) from hs d]
    exact (rckTwE6_mem_rootGroup_iff θ hθ _).mpr ⟨c * d, rfl⟩
  have hle_map : X ≤ X.map (MulAut.conj s).toMonoidHom := by
    intro y hy
    obtain ⟨d, rfl⟩ := (rckTwE6_mem_rootGroup_iff θ hθ y).mp hy
    refine Subgroup.mem_map.mpr ⟨rckTwE6X θ hθ (c⁻¹ * d), ?_, ?_⟩
    · exact (rckTwE6_mem_rootGroup_iff θ hθ _).mpr ⟨c⁻¹ * d, rfl⟩
    · rw [show (MulAut.conj s).toMonoidHom (rckTwE6X θ hθ (c⁻¹ * d)) =
          rckTwE6X θ hθ (c * (c⁻¹ * d)) from hs (c⁻¹ * d)]
      rw [mul_inv_cancel_left₀ hc d]
  have hXmap : X = X.map (MulAut.conj s).toMonoidHom := le_antisymm hle_map hmap_le
  have hxeq : rckTwE6X θ hθ c = s * rckTwE6X θ hθ 1 * s⁻¹ := by
    rw [hs 1, mul_one]
  have hrootmap : (twistedDatum k θ).rootGroup twE6Alpha =
      X.map (MulAut.conj s).toMonoidHom := hXmap
  rw [hxeq, hrootmap]
  exact rckTwE6_core_conj s (rckTwE6_core_xPair_one hf)

theorem rckLemmaHCore_twistedE6 {m g : ℕ} (hg : 1 ≤ g)
    {β : Fin (ggU .twistedE6 m g).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 m g).D.roots)
    (hL : ¬ GGLongRoot (ggU .twistedE6 m g).D β) : RCKLemmaHCore (ggU .twistedE6 m g) β :=
  rckSTwE6_core_of_alpha hg (rckTwE6_core_alpha hg) hβ hL

theorem rckK2NbrRootSubShortAt_twistedE6 : RCKK2NbrRootSubShortAt .twistedE6 := by
  intro X _ _ K R m g β ht hg hβ hL hS h2 hvia r hr hr1
  exact rckGL1_of_core ht hg (fun h => absurd h (by decide))
    (rckLemmaHCore_twistedE6 hg hβ hL) hvia hr hr1

end Core

end CFSG.StandardType.RCKC1
