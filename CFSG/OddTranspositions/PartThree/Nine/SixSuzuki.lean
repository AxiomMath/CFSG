module

public import CFSG.OddTranspositions.PartThree.Nine.WalesSz8
public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzuki
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
import CFSG.LieType.Chevalley.RootCommutatorData
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import Certificates.Certificate3951

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {D : Set G}

open CFSG.Quasithin (GF8)

section Coords

variable {R : Type*} [Group R] {c : GF8 × GF8 ≃ R}

private theorem gf8_add_self (a : GF8) : a + a = 0 := by
  revert a
  decide

private theorem gf8_eq_zero_of_pow_five {a : GF8} (h : a ^ 5 = 0) : a = 0 := by
  revert h
  revert a
  decide

private theorem gf8_eq_zero_of_forall {a : GF8} (h : ∀ a' : GF8, a * a' ^ 4 = a' * a ^ 4) :
    a = 0 := by
  revert h
  revert a
  decide

private theorem gf8_exists_pow_five (b : GF8) : ∃ a : GF8, a ^ 5 = b := by
  revert b
  decide

private theorem coords_zero_zero
    (hc : ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4)) :
    c (0, 0) = 1 := by
  simpa using hc 0 0 0 0

private theorem coords_mul_self
    (hc : ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4))
    (a b : GF8) : c (a, b) * c (a, b) = c (0, a ^ 5) := by
  rw [hc, gf8_add_self, gf8_add_self, zero_add]
  congr 2
  ring

private theorem coords_zero_mul
    (hc : ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4))
    (b b' : GF8) : c (0, b) * c (0, b') = c (0, b + b') := by
  rw [hc]
  simp

private theorem commute_coords_zero
    (hc : ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4))
    (b : GF8) (x : R) : Commute (c (0, b)) x := by
  obtain ⟨⟨a', b'⟩, rfl⟩ := c.surjective x
  show c (0, b) * c (a', b') = c (a', b') * c (0, b)
  rw [hc, hc]
  simp [add_comm]

omit [Group R] in
private theorem eq_coords_zero {x : R} (hx : (c.symm x).1 = 0) : x = c (0, (c.symm x).2) :=
  calc x = c (c.symm x) := (c.apply_symm_apply x).symm
    _ = c (0, (c.symm x).2) := congrArg c (Prod.ext hx rfl)

private theorem fst_eq_zero_of_commute
    (hc : ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4))
    {x : R} (hx : ∀ y, Commute x y) : (c.symm x).1 = 0 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := c.surjective x
  rw [Equiv.symm_apply_apply]
  refine gf8_eq_zero_of_forall fun a' => ?_
  have h := (hx (c (a', 0))).eq
  rw [hc, hc] at h
  have h' := congrArg Prod.snd (c.injective h)
  simp only [add_zero, zero_add] at h'
  exact add_left_cancel h'

private theorem fst_mul
    (hc : ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4))
    (x y : R) : (c.symm (x * y)).1 = (c.symm x).1 + (c.symm y).1 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := c.surjective x
  obtain ⟨⟨a', b'⟩, rfl⟩ := c.surjective y
  rw [hc]
  simp

end Coords

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

private theorem exists_coords_inf_of_sz (h3 : Conclusion9_3 D hC) (h5 : Conclusion9_5 D hC T S)
    (hU : DeltaSetup hC T S U)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.SzModel 1) :
    ∃ c : GF8 × GF8 ≃ ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G),
      ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  obtain ⟨R₀, hR⟩ := exists_sylow_pResidualOf T
  set e := eL.trans eH
  let P := R₀.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨c₁, hc₁⟩ := Wales.exists_coords_of_sylow P
  have hP := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R₀
  let e₂ : (R₀ : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) ≃*
      (P : Subgroup (BenderSuzuki.SzModel 1)) :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hP.symm)
  let e₃ : (R₀ : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) ≃*
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) :=
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr hR)
  refine ⟨(c₁.trans e₂.symm.toEquiv).trans e₃.toEquiv, fun a b a' b' => ?_⟩
  simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  rw [← map_mul, ← map_mul, hc₁]

theorem pow_fortyTwo_mem_centralizer_of_sz (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.SzModel 1) {n : G}
    (hn : n ∈ Subgroup.normalizer ((S : Set G) ∩ D)) :
    n ^ 42 ∈ Subgroup.centralizer ((S : Set G) ∩ D) := by
  classical
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hL
  obtain ⟨c, hc⟩ := exists_coords_inf_of_sz h3 h5 hU eH
  have huT : hC.d ∈ TG := d_mem_sylow_map hC h3 T
  have huL : hC.d ∉ L := fun h => hU.d_not_mem h3 (by
    have h1 := Subgroup.disjoint_def.mp h3.2.2.2 (Subgroup.mem_zpowers hC.d) h
    exact absurd h1 (hC.setup.oddT.ne_one hC.hd))
  have hcu : ∀ t ∈ TG, Commute hC.d t := fun t ht => commute_d_of_mem_sylow_map ht
  let ρ : G → G := fun t => if t ∈ L then t else hC.d * t
  have hρR : ∀ t ∈ TG, ρ t ∈ TG ⊓ L := by
    intro t ht
    by_cases htL : t ∈ L
    · simp only [ρ, if_pos htL]
      exact ⟨ht, htL⟩
    · simp only [ρ, if_neg htL]
      rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ ht) with h | h
      · exact absurd h htL
      · exact ⟨TG.mul_mem huT ht, h⟩
  have hρu : ∀ t ∈ TG, t = ρ t ∨ t = hC.d * ρ t := by
    intro t ht
    by_cases htL : t ∈ L
    · left
      simp only [ρ, if_pos htL]
    · right
      simp only [ρ, if_neg htL]
      rw [← mul_assoc, hu2, one_mul]
  have hρmul : ∀ s ∈ TG, ∀ t ∈ TG, ρ (s * t) = ρ s * ρ t := by
    intro s hs t ht
    have hst := (hcu s hs).eq
    by_cases hsL : s ∈ L <;> by_cases htL : t ∈ L
    · simp only [ρ, if_pos hsL, if_pos htL, if_pos (L.mul_mem hsL htL)]
    · have h : s * t ∉ L := fun h => htL (by simpa using L.mul_mem (L.inv_mem hsL) h)
      simp only [ρ, if_pos hsL, if_neg htL, if_neg h]
      rw [← mul_assoc, ← mul_assoc, ← hst]
    · have h : s * t ∉ L := fun h => hsL (by simpa using L.mul_mem h (L.inv_mem htL))
      simp only [ρ, if_neg hsL, if_pos htL, if_neg h]
      rw [mul_assoc]
    · have hus : hC.d * s ∈ L := by
        rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ hs) with h | h
        · exact absurd h hsL
        · exact h
      have hut : hC.d * t ∈ L := by
        rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ ht) with h | h
        · exact absurd h htL
        · exact h
      have heq : hC.d * s * (hC.d * t) = s * t := by
        calc hC.d * s * (hC.d * t) = hC.d * (s * hC.d) * t := by group
          _ = hC.d * (hC.d * s) * t := by rw [← hst]
          _ = s * t := by rw [← mul_assoc, hu2, one_mul]
      have hstL : s * t ∈ L := heq ▸ L.mul_mem hus hut
      simp only [ρ, if_neg hsL, if_neg htL, if_pos hstL]
      exact heq.symm
  have hρL : ∀ t ∈ L, ρ t = t := fun t ht => if_pos ht
  have hρT : ∀ t ∈ TG, ρ t ∈ TG := fun t ht => (hρR t ht).1
  have hρsq : ∀ t ∈ TG, t * t = ρ t * ρ t := by
    intro t ht
    by_cases htL : t ∈ L
    · simp only [ρ, if_pos htL]
    · simp only [ρ, if_neg htL]
      calc t * t = hC.d * (hC.d * t) * t := by rw [← mul_assoc, hu2, one_mul]
        _ = hC.d * (t * hC.d) * t := by rw [(hcu t ht).eq]
        _ = hC.d * t * (hC.d * t) := by group
  let p : G → GF8 := fun t => if h : ρ t ∈ TG ⊓ L then (c.symm ⟨ρ t, h⟩).1 else 0
  let q : G → GF8 := fun v => if h : v ∈ TG ⊓ L then (c.symm ⟨v, h⟩).2 else 0
  have hpt : ∀ t (ht : t ∈ TG), p t = (c.symm ⟨ρ t, hρR t ht⟩).1 := fun t ht =>
    dif_pos (hρR t ht)
  have hqv : ∀ v (hv : v ∈ TG ⊓ L), q v = (c.symm ⟨v, hv⟩).2 := fun v hv => dif_pos hv
  have hUR : U ≤ TG ⊓ L := le_inf hU.le_sylow_map hU.le_pResidualOf
  have hcU : ∀ b, ((c (0, b) : (TG ⊓ L : Subgroup G)) : G) ∈ U := by
    intro b
    by_cases hb : b = 0
    · subst hb
      rw [coords_zero_zero hc]
      exact U.one_mem
    · rw [hU.eq_closure]
      refine Subgroup.subset_closure ⟨(c (0, b)).2, ?_⟩
      have h2 : ((c (0, b) : (TG ⊓ L : Subgroup G)) : G) * (c (0, b) : G) = 1 := by
        have h := congrArg Subtype.val (coords_zero_mul hc b b)
        rw [gf8_add_self, coords_zero_zero hc] at h
        exact h
      have h1 : ((c (0, b) : (TG ⊓ L : Subgroup G)) : G) ≠ 1 := by
        intro h
        have h' : c (0, b) = c (0, 0) := by
          rw [coords_zero_zero hc]
          exact Subtype.ext h
        exact hb (congrArg Prod.snd (c.injective h'))
      exact orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  have hUfst : ∀ v (hv : v ∈ U), (c.symm ⟨v, hUR hv⟩).1 = 0 := by
    intro v hv
    have h2 : v * v = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
    have hx : (⟨v, hUR hv⟩ : (TG ⊓ L : Subgroup G)) * ⟨v, hUR hv⟩ = 1 := Subtype.ext h2
    have h := coords_mul_self hc (c.symm ⟨v, hUR hv⟩).1 (c.symm ⟨v, hUR hv⟩).2
    rw [Prod.mk.eta, c.apply_symm_apply, hx, ← coords_zero_zero hc] at h
    exact gf8_eq_zero_of_pow_five (congrArg Prod.snd (c.injective h)).symm
  have hUc : ∀ v (hv : v ∈ U), v = ((c (0, q v) : (TG ⊓ L : Subgroup G)) : G) := by
    intro v hv
    rw [hqv v (hUR hv)]
    exact congrArg Subtype.val (eq_coords_zero (hUfst v hv))
  have hp : ∀ s ∈ TG, ∀ t ∈ TG, p (s * t) = p s + p t := by
    intro s hs t ht
    rw [hpt _ (TG.mul_mem hs ht), hpt _ hs, hpt _ ht]
    have h : (⟨ρ (s * t), hρR _ (TG.mul_mem hs ht)⟩ : (TG ⊓ L : Subgroup G)) =
        ⟨ρ s, hρR s hs⟩ * ⟨ρ t, hρR t ht⟩ := Subtype.ext (hρmul s hs t ht)
    rw [h, fst_mul hc]
  have hps : ∀ a, ∃ t ∈ TG, p t = a := by
    intro a
    refine ⟨(c (a, 0) : G), (c (a, 0)).2.1, ?_⟩
    rw [hpt _ (c (a, 0)).2.1]
    have h : (⟨ρ (c (a, 0) : G), hρR _ (c (a, 0)).2.1⟩ : (TG ⊓ L : Subgroup G)) = c (a, 0) :=
      Subtype.ext (hρL _ (c (a, 0)).2.2)
    rw [h, Equiv.symm_apply_apply]
  have hpZ : ∀ t ∈ TG, p t = 0 ↔ ∀ s ∈ TG, Commute t s := by
    intro t ht
    rw [hpt _ ht]
    constructor
    · intro h s hs
      have hρc : Commute (ρ t) (ρ s) := by
        have h' := commute_coords_zero hc (c.symm ⟨ρ t, hρR t ht⟩).2 ⟨ρ s, hρR s hs⟩
        rw [← eq_coords_zero h] at h'
        exact congrArg Subtype.val h'
      have hut := hcu _ (hρT t ht)
      have hus := hcu _ (hρT s hs)
      rcases hρu t ht with h1 | h1 <;> rcases hρu s hs with h2 | h2 <;> rw [h1, h2]
      · exact hρc
      · exact hut.symm.mul_right hρc
      · exact hus.mul_left hρc
      · exact (hcu _ (TG.mul_mem huT (hρT s hs))).mul_left (hut.symm.mul_right hρc)
    · intro h
      apply fst_eq_zero_of_commute hc
      intro y
      apply Subtype.ext
      have hy : (y : G) ∈ TG := y.2.1
      show ρ t * y = y * ρ t
      by_cases htL : t ∈ L
      · simp only [ρ, if_pos htL]
        exact (h y hy).eq
      · simp only [ρ, if_neg htL]
        exact ((hcu y hy).mul_left (h y hy)).eq
  have hU' : ∀ t ∈ TG, t * t ∈ U := by
    intro t ht
    rw [hρsq t ht]
    have h := coords_mul_self hc (c.symm ⟨ρ t, hρR t ht⟩).1 (c.symm ⟨ρ t, hρR t ht⟩).2
    rw [Prod.mk.eta, c.apply_symm_apply] at h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul] at h'
    rw [h']
    exact hcU _
  have hUsq : ∀ v ∈ U, ∃ t ∈ TG, v = t * t := by
    intro v hv
    obtain ⟨a, ha⟩ := gf8_exists_pow_five (q v)
    refine ⟨(c (a, 0) : G), (c (a, 0)).2.1, ?_⟩
    rw [hUc v hv]
    have h := congrArg Subtype.val (coords_mul_self hc a 0)
    rw [Subgroup.coe_mul, ha] at h
    exact h.symm
  have hq : ∀ v ∈ U, ∀ w ∈ U, q (v * w) = q v + q w := by
    intro v hv w hw
    have h := congrArg Subtype.val (coords_zero_mul hc (q v) (q w))
    rw [Subgroup.coe_mul, ← hUc v hv, ← hUc w hw] at h
    rw [h, hqv _ (c (0, q v + q w)).2, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hqi : Set.InjOn q U := by
    intro v hv w hw h
    rw [hUc v hv, hUc w hw, h]
  have hsq : ∀ t ∈ TG, q (t * t) = p t ^ 5 := by
    intro t ht
    rw [hρsq t ht, hpt t ht]
    have h := coords_mul_self hc (c.symm ⟨ρ t, hρR t ht⟩).1 (c.symm ⟨ρ t, hρR t ht⟩).2
    rw [Prod.mk.eta, c.apply_symm_apply] at h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul] at h'
    rw [h', hqv _ (c _).2, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hnΔ : n ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ hn
  have hnT : n ∈ Subgroup.normalizer (TG : Set G) := by
    intro t
    constructor
    · exact fun ht => hU.conj_mem_sylow_map h5 hnΔ ht
    · intro ht
      have h := hU.conj_mem_sylow_map h5 (Subgroup.inv_mem _ hnΔ) ht
      have h' : n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t := by group
      rwa [h'] at h
  have h21 : ∀ v ∈ U, n ^ 21 * v * (n ^ 21)⁻¹ = v := fun v hv =>
    Wales.conj_pow_twentyOne_eq hp hps hpZ hU' hUsq hq hqi hsq hnT hv
  have hmN : n ^ 21 ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    Subgroup.pow_mem _ hnΔ 21
  obtain ⟨w, hw, hwu⟩ : n ^ 21 * hC.d * (n ^ 21)⁻¹ ∈ (fun v : G => hC.d * v) '' (U : Set G) :=
    (hmN hC.d).mp ⟨1, U.one_mem, mul_one _⟩
  have hwu' : hC.d * w = n ^ 21 * hC.d * (n ^ 21)⁻¹ := hwu
  have hw2 : w * w = 1 := by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian w hw
  have h42 : n ^ 42 = n ^ 21 * n ^ 21 := by rw [← pow_add]
  rw [Subgroup.mem_centralizer_iff, hU.sylow_inter]
  rintro _ ⟨v, hv, rfl⟩
  show hC.d * v * n ^ 42 = n ^ 42 * (hC.d * v)
  have key : n ^ 21 * n ^ 21 * (hC.d * v) * (n ^ 21 * n ^ 21)⁻¹ = hC.d * v := by
    calc n ^ 21 * n ^ 21 * (hC.d * v) * (n ^ 21 * n ^ 21)⁻¹ =
        n ^ 21 * ((n ^ 21 * hC.d * (n ^ 21)⁻¹) * (n ^ 21 * v * (n ^ 21)⁻¹)) * (n ^ 21)⁻¹ := by
          group
      _ = n ^ 21 * (hC.d * w * v) * (n ^ 21)⁻¹ := by rw [← hwu', h21 v hv]
      _ = (n ^ 21 * hC.d * (n ^ 21)⁻¹) * (n ^ 21 * w * (n ^ 21)⁻¹) *
          (n ^ 21 * v * (n ^ 21)⁻¹) := by group
      _ = hC.d * w * w * v := by rw [← hwu', h21 w hw, h21 v hv]
      _ = hC.d * v := by rw [mul_assoc hC.d w w, hw2, mul_one]
  rw [h42]
  calc hC.d * v * (n ^ 21 * n ^ 21) =
      n ^ 21 * n ^ 21 * (hC.d * v) * (n ^ 21 * n ^ 21)⁻¹ * (n ^ 21 * n ^ 21) := by rw [key]
    _ = n ^ 21 * n ^ 21 * (hC.d * v) := by group

theorem not_nonempty_mulEquiv_psl27_of_sz (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.SzModel 1) :
    ¬ Nonempty ((cosetNormalizerPerm ((S : Set G) ∩ D)).range ≃* PSL(2, ZMod 7)) := by
  rintro ⟨e⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := CFSG.AGLEmbedding.exists_orderOf_four_psl2_of_seven (F := ZMod 7) (by rfl)
  obtain ⟨⟨_, n, rfl⟩, hσ⟩ := e.surjective y
  have h42 : (⟨cosetNormalizerPerm _ n, n, rfl⟩ :
      (cosetNormalizerPerm ((S : Set G) ∩ D)).range) ^ 42 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ← map_pow]
    ext x
    rw [CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex.cosetNormalizerPerm_apply]
    have hc := hU.pow_fortyTwo_mem_centralizer_of_sz h3 h5 eH n.2
    have hx := Subgroup.mem_centralizer_iff.mp hc x x.2
    rw [Subgroup.coe_pow, ← hx, mul_inv_cancel_right]
    rfl
  have hy42 : y ^ 42 = 1 := by rw [← hσ, ← map_pow, h42, map_one]
  have h := orderOf_dvd_of_pow_eq_one hy42
  rw [hy] at h
  norm_num at h

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
