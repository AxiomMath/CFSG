module

public import CFSG.LocalAnalysis.StandardType.GGKG87BTransDefs
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate13657
import all CFSG.LocalAnalysis.StandardType.GGKG87BTransRatAux
import CFSG.LocalAnalysis.StandardType.GGKG87BTransWeyl
import CFSG.LocalAnalysis.StandardType.GGKG87BTransCent
import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.TwistMap
import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType.KG87B

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem thirdWeyl_inv_conj_mem_kg87bRat
    {Ω : Type} [Field Ω] {s : ModGL Tag.E6 Ω} (hs : s ∈ thirdTorus Ω) :
    (thirdWeyl Ω)⁻¹ * s * thirdWeyl Ω ∈ thirdTorus Ω := by
  let P : (Fin Tag.E6.rank → Ωˣ) → Prop := fun a =>
    a ⟨0, by decide⟩ = 1 ∧ a ⟨2, by decide⟩ = 1 ∧ a ⟨4, by decide⟩ = 1 ∧ a ⟨5, by decide⟩ = 1
  have hshape : ∀ a, rootDiagUnit Tag.E6 a ∈ thirdTorus Ω → P a := by
    rintro a ⟨b, h0, h2, h4, h5, hab⟩
    obtain rfl := rootDiagUnit_injective hab
    exact ⟨h0, h2, h4, h5⟩
  have hstep : ∀ a, P a → P (weylTuple thirdCox a) := fun a ha => by
    have h := thirdWeyl_conj_mem_thirdTorus (Ω := Ω) (s := rootDiagUnit Tag.E6 a)
      ⟨a, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, rfl⟩
    rw [thirdWeyl, canonicalRep_conj_rootDiagUnit] at h
    exact hshape _ h
  have hpow : ∀ k : ℕ, ∀ a, P a → P (weylTuple (thirdCox ^ k) a) := by
    intro k
    induction k with
    | zero => intro a ha; rwa [pow_zero, weylTuple_one]
    | succ k ih =>
      intro a ha
      rw [pow_succ', ← weylTuple_weylTuple]
      exact hstep _ (ih a ha)
  have hinv : thirdCox⁻¹ = thirdCox ^ (orderOf thirdCox - 1) := by
    have hpos : 0 < orderOf thirdCox := (isOfFinOrder_of_finite thirdCox).orderOf_pos
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  obtain ⟨a, h0, h2, h4, h5, rfl⟩ := hs
  have hb : thirdWeyl Ω * rootDiagUnit Tag.E6 (weylTuple thirdCox⁻¹ a) * (thirdWeyl Ω)⁻¹ =
      rootDiagUnit Tag.E6 a := by
    rw [thirdWeyl, canonicalRep_conj_rootDiagUnit, weylTuple_weylTuple, mul_inv_cancel,
      weylTuple_one]
  have e : (thirdWeyl Ω)⁻¹ * rootDiagUnit Tag.E6 a * thirdWeyl Ω =
      rootDiagUnit Tag.E6 (weylTuple thirdCox⁻¹ a) := by
    rw [← hb]
    group
  rw [e]
  have hP := hpow (orderOf thirdCox - 1) a ⟨h0, h2, h4, h5⟩
  rw [← hinv] at hP
  exact ⟨_, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, rfl⟩

private theorem exists_mul_of_mem_sup_kg87bRat
    {Ω : Type} [Field Ω] {m : ModGL Tag.E6 Ω} (hm : m ∈ thirdTorus Ω ⊔ blockGroup Ω) :
    ∃ s ∈ thirdTorus Ω, ∃ g ∈ blockGroup Ω, m = s * g := by
  have hle : thirdTorus Ω ≤ Subgroup.normalizer (blockGroup Ω : Set (ModGL Tag.E6 Ω)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hc := commute_of_mem_thirdTorus hs
        (Subgroup.mem_sup_right hh : h ∈ thirdTorus Ω ⊔ blockGroup Ω)
      rwa [hc, mul_inv_cancel_right]
    · intro hh
      have hc := commute_of_mem_thirdTorus (inv_mem hs)
        (Subgroup.mem_sup_right hh : s * h * s⁻¹ ∈ thirdTorus Ω ⊔ blockGroup Ω)
      have e : h = s⁻¹ * (s * h * s⁻¹) * s := by group
      rwa [e, hc, mul_assoc, inv_mul_cancel, mul_one]
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (thirdTorus Ω) (blockGroup Ω) hle
  have hm' : m ∈ ((thirdTorus Ω ⊔ blockGroup Ω : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω)) := hm
  rw [h] at hm'
  obtain ⟨s, hs, g, hg, rfl⟩ := Set.mem_mul.1 hm'
  exact ⟨s, hs, g, hg, rfl⟩

private theorem exists_fixed_conj_core_kg87bRat
    {n d : ℕ} (hd : 1 ≤ d) (hnd : n = 3 * d) (h3 : 3 ∣ 2 ^ d + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {δ : K ≃+* K} (hδ : orderOf δ = 3) {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] {ω : Ωˣ} (hω : orderOf ω = 3) {Y : ModGL Tag.E6 Ω}
    (hY : Y ∈ adjointGroup Tag.E6 Ω) {h₀ u : ↥(twistedE6RootGroup K σ)}
    (hh₀δ : fieldActor (t := TwistTag.E6) σ δ h₀ = h₀) (huδ : fieldActor (t := TwistTag.E6) σ δ u = u)
    {h₀' u' : ModGL Tag.E6 Ω}
    (hh₀' : h₀' = baseChangeGL (algebraMap K Ω) (h₀ : ModGL TwistTag.E6.tag K))
    (hu' : u' = baseChangeGL (algebraMap K Ω) (u : ModGL TwistTag.E6.tag K))
    (hYh₀ : Y * h₀' * Y⁻¹ = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω))
    (hYu : Y * u' * Y⁻¹ = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2))) :
    ∃ w : ↥(twistedE6RootGroup K σ), fieldActor (t := TwistTag.E6) σ δ w = w ∧
      ∃ s ∈ thirdTorus Ω, (baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) :
        ModGL Tag.E6 Ω) = Y⁻¹ * (thirdWeyl Ω * s) * Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hn : 1 ≤ n := by omega
  obtain ⟨κ₁, hκ₁, -, hzp⟩ := exists_frobSq_zpowers_kg87bRat hd hnd hK hδ
  have hκδ : κ₁ ∈ Subgroup.zpowers δ := by rw [hzp]; exact Subgroup.mem_zpowers κ₁
  obtain ⟨Fr₀, hFr₀⟩ : ∃ Fr₀ : Ω →+* Ω, ∀ c, Fr₀ c = c ^ 2 ^ d :=
    ⟨iterateFrobenius Ω 2 d, fun c => iterateFrobenius_def 2 d c⟩
  obtain ⟨F₀, hF₀⟩ : ∃ F : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω,
      ∀ g, F g = twistHom TwistTag.E6 Ω Fr₀ g := ⟨twistHom TwistTag.E6 Ω Fr₀, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ g : ModGL Tag.E6 Ω, g = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ g : ModGL Tag.E6 Ω,
      g = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)) := ⟨_, rfl⟩
  rw [← hx] at hYh₀
  rw [← hy] at hYu
  obtain ⟨nw, hnw⟩ : ∃ g : ModGL Tag.E6 Ω, g = thirdWeyl Ω := ⟨_, rfl⟩
  have hFh₀ : F₀ h₀' = h₀' := by
    rw [hF₀, hh₀']
    exact twistHom_baseChange_kg87bRat hnd hn hK σ hσ hκ₁ hFr₀
      (fieldActor_fixed_of_mem_zpowers_kg87bRat σ hκδ hh₀δ)
  have hFu : F₀ u' = u' := by
    rw [hF₀, hu']
    exact twistHom_baseChange_kg87bRat hnd hn hK σ hσ hκ₁ hFr₀
      (fieldActor_fixed_of_mem_zpowers_kg87bRat σ hκδ huδ)
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have ex : x = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 1) := by
    rw [hx, Pi.mulSingle_one, mul_one]
  have hxS : x ∈ thirdTorus Ω := ex ▸ rootDiagUnit_mem_thirdTorus_kg87bRat ω 1
  have hyS : y ∈ thirdTorus Ω := hy ▸ rootDiagUnit_mem_thirdTorus_kg87bRat ω (ω ^ 2)
  have hx3 : x ^ 3 = 1 := by rw [ex]; exact rootDiagUnit_pow_three_kg87bRat hω3 (one_pow 3)
  have hy3 : y ^ 3 = 1 := by
    rw [hy]
    refine rootDiagUnit_pow_three_kg87bRat hω3 ?_
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hFS : ∀ s ∈ thirdTorus Ω, F₀ s = s ^ 2 ^ d := fun s hs =>
    twistHom_of_mem_thirdTorus_kg87bRat hFr₀ hF₀ hs
  have hinv3 : ∀ s : ModGL Tag.E6 Ω, s ^ 3 = 1 → s ^ 2 ^ d = s⁻¹ := by
    intro s hs3
    refine eq_inv_of_mul_eq_one_left ?_
    obtain ⟨k, hk⟩ := h3
    rw [← pow_succ, hk, pow_mul, hs3, one_pow]
  obtain ⟨c₀, hc₀⟩ : ∃ c : ModGL Tag.E6 Ω, c = Y * (F₀ Y)⁻¹ := ⟨_, rfl⟩
  have hc₀F : ∀ g, c₀ * F₀ g * c₀⁻¹ = Y * F₀ (Y⁻¹ * g * Y) * Y⁻¹ := fun g => by
    rw [hc₀, map_mul, map_mul, map_inv]
    group
  have hYx : Y⁻¹ * x * Y = h₀' := by rw [← hYh₀]; group
  have hYy : Y⁻¹ * y * Y = u' := by rw [← hYu]; group
  have hc₀x : c₀ * x⁻¹ * c₀⁻¹ = x := by
    rw [← hinv3 x hx3, ← hFS x hxS, hc₀F, hYx, hFh₀, hYh₀]
  have hc₀y : c₀ * y⁻¹ * c₀⁻¹ = y := by
    rw [← hinv3 y hy3, ← hFS y hyS, hc₀F, hYy, hFu, hYu]
  obtain ⟨ν, hνG, hνS, hνn⟩ := exists_inv_thirdTorus_commute_thirdWeyl Ω
  rw [← hnw] at hνn
  obtain ⟨m₀, hm₀⟩ : ∃ m : ModGL Tag.E6 Ω, m = c₀ * ν := ⟨_, rfl⟩
  have hc₀m : c₀ = m₀ * ν⁻¹ := by rw [hm₀, mul_inv_cancel_right]
  have hcomm_of : ∀ t ∈ thirdTorus Ω, c₀ * t⁻¹ * c₀⁻¹ = t → m₀ * t = t * m₀ := by
    intro t ht h
    have h1 : m₀ * t * m₀⁻¹ = t := by
      rw [hm₀, mul_inv_rev, show c₀ * ν * t * (ν⁻¹ * c₀⁻¹) = c₀ * (ν * t * ν⁻¹) * c₀⁻¹ by group,
        hνS t ht, h]
    calc m₀ * t = m₀ * t * m₀⁻¹ * m₀ := by group
      _ = t * m₀ := by rw [h1]
  have hFYG : F₀ Y ∈ adjointGroup Tag.E6 Ω := by
    rw [hF₀]
    exact twistHom_mem_adjointGroup TwistTag.E6 Ω Fr₀ hY
  have hm₀G : m₀ ∈ adjointGroup Tag.E6 Ω := by
    rw [hm₀, hc₀]
    exact mul_mem (mul_mem hY (inv_mem hFYG)) hνG
  have hm₀SB : m₀ ∈ thirdTorus Ω ⊔ blockGroup Ω :=
    mem_thirdTorus_sup_blockGroup_of_commute hω hm₀G (hx ▸ hcomm_of x hxS hc₀x)
      (hy ▸ hcomm_of y hyS hc₀y)
  have hFn : F₀ nw = nw := by
    rw [hF₀, hnw]
    exact twistHom_thirdWeyl Fr₀
  obtain ⟨s₀, hs₀, g₀, hg₀, hm₀e⟩ := exists_mul_of_mem_sup_kg87bRat hm₀SB
  have hng₀ : nw * g₀ = g₀ * nw := by
    rw [hnw]
    exact commute_thirdWeyl_of_mem_blockGroup hg₀
  have hs₁ : nw⁻¹ * s₀ * nw ∈ thirdTorus Ω := by
    rw [hnw]
    exact thirdWeyl_inv_conj_mem_kg87bRat hs₀
  have hs' : nw⁻¹ * s₀ * nw * s₀⁻¹ ∈ thirdTorus Ω := mul_mem hs₁ (inv_mem hs₀)
  have hF''n : c₀ * F₀ nw * c₀⁻¹ = nw * (nw⁻¹ * s₀ * nw * s₀⁻¹) := by
    have hνn' : ν⁻¹ * nw * ν = nw := by
      calc ν⁻¹ * nw * ν = ν⁻¹ * (ν * nw * ν⁻¹) * ν := by rw [hνn]
        _ = nw := by group
    calc c₀ * F₀ nw * c₀⁻¹ = m₀ * (ν⁻¹ * nw * ν) * m₀⁻¹ := by
          rw [hFn, hc₀m]
          group
      _ = s₀ * (g₀ * nw * g₀⁻¹) * s₀⁻¹ := by
          rw [hνn', hm₀e]
          group
      _ = nw * (nw⁻¹ * s₀ * nw * s₀⁻¹) := by
          rw [← hng₀, mul_inv_cancel_right]
          group
  have hF''S : ∀ t ∈ thirdTorus Ω, c₀ * F₀ t * c₀⁻¹ = (t ^ 2 ^ d)⁻¹ := by
    intro t ht
    have htq : t ^ 2 ^ d ∈ thirdTorus Ω := pow_mem ht _
    have hν' : ν⁻¹ * t ^ 2 ^ d * ν = (t ^ 2 ^ d)⁻¹ := by
      have h := hνS _ (inv_mem htq)
      rw [inv_inv] at h
      calc ν⁻¹ * t ^ 2 ^ d * ν = ν⁻¹ * (ν * (t ^ 2 ^ d)⁻¹ * ν⁻¹) * ν := by rw [h]
        _ = (t ^ 2 ^ d)⁻¹ := by group
    have hcm : (t ^ 2 ^ d)⁻¹ * m₀ = m₀ * (t ^ 2 ^ d)⁻¹ :=
      commute_of_mem_thirdTorus (inv_mem htq) hm₀SB
    calc c₀ * F₀ t * c₀⁻¹ = m₀ * (ν⁻¹ * t ^ 2 ^ d * ν) * m₀⁻¹ := by
          rw [hFS t ht, hc₀m]
          group
      _ = (t ^ 2 ^ d)⁻¹ := by rw [hν', ← hcm, mul_inv_cancel_right]
  obtain ⟨s, hs, hss⟩ := exists_pow_eq_of_mem_thirdTorus_kg87bRat (N := 2 ^ d + 1)
    (by positivity) hs'
  have hfix : F₀ (Y⁻¹ * (nw * s) * Y) = Y⁻¹ * (nw * s) * Y := by
    have h1 : c₀ * F₀ (nw * s) * c₀⁻¹ = nw * s := by
      calc c₀ * F₀ (nw * s) * c₀⁻¹ = (c₀ * F₀ nw * c₀⁻¹) * (c₀ * F₀ s * c₀⁻¹) := by
            rw [map_mul]
            group
        _ = nw * s := by
            rw [hF''n, hF''S s hs, ← hss, pow_succ', mul_assoc, mul_assoc, mul_inv_cancel,
              mul_one]
    have h2 := hc₀F (nw * s)
    rw [h1] at h2
    calc F₀ (Y⁻¹ * (nw * s) * Y) = Y⁻¹ * (Y * F₀ (Y⁻¹ * (nw * s) * Y) * Y⁻¹) * Y := by group
      _ = Y⁻¹ * (nw * s) * Y := by rw [← h2]
  have hgG : Y⁻¹ * (nw * s) * Y ∈ adjointGroup Tag.E6 Ω := by
    refine mul_mem (mul_mem (inv_mem hY) (mul_mem ?_
      (mem_adjointGroup_of_mem_thirdTorus_kg87bRat hs))) hY
    rw [hnw]
    exact thirdWeyl_mem_adjointGroup Ω
  obtain ⟨w, hwδ, hw⟩ := exists_fieldActor_fixed_of_twistHom_kg87bRat hd hnd h3 hK σ hσ hδ hFr₀
    hgG ((hF₀ _).symm.trans hfix)
  exact ⟨w, hwδ, s, hs, hw.trans (congrArg (fun z => Y⁻¹ * (z * s) * Y) hnw)⟩

theorem exists_fieldActor_fixed_conj_thirdWeyl
    {n d : ℕ} (hd : 1 ≤ d) (hnd : n = 3 * d) (h3 : 3 ∣ 2 ^ d + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {δ : K ≃+* K} (hδ : orderOf δ = 3)
    {ω : (AlgebraicClosure K)ˣ} (hω : orderOf ω = 3) {Y : ModGL Tag.E6 (AlgebraicClosure K)}
    (hY : Y ∈ adjointGroup Tag.E6 (AlgebraicClosure K)) {h₀ u : ↥(twistedE6RootGroup K σ)}
    (hh₀δ : fieldActor (t := TwistTag.E6) σ δ h₀ = h₀) (huδ : fieldActor (t := TwistTag.E6) σ δ u = u)
    (hYh₀ : Y * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) :
        ModGL Tag.E6 (AlgebraicClosure K)) * Y⁻¹ = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω))
    (hYu : Y * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) :
        ModGL Tag.E6 (AlgebraicClosure K)) * Y⁻¹ =
      rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2))) :
    ∃ w : ↥(twistedE6RootGroup K σ), fieldActor (t := TwistTag.E6) σ δ w = w ∧
      ∃ s ∈ thirdTorus (AlgebraicClosure K),
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (w : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 (AlgebraicClosure K)) = Y⁻¹ * (thirdWeyl (AlgebraicClosure K) * s) * Y :=
  exists_fixed_conj_core_kg87bRat hd hnd h3 hK σ hσ hδ hω hY hh₀δ huδ rfl rfl hYh₀ hYu

end CFSG.StandardType.KG87B

end
