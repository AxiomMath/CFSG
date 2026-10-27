module

public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofL
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofL
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofCUL
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Aut
public import CFSG.RankThree.PartTwo.KFacts.PSLThreeGraphField
public import CFSG.RankThree.PartTwo.KFacts.PSLThreeHessian
import CFSG.Timmesfeld.Orders.BangField

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KS165LProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.KFacts.PSLThreeGraphField
open CFSG.RankThree.PartTwo.KFacts.PSLThreeHessian
open CFSG.Semidihedral.FixedFieldData
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.InnerNormalizedAutomorphisms
open Matrix

variable {K : Type} [Field K]

private lemma omega_ne_one_of_char_two [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h1 : (1 : K) + 1 + 1 = 0 := by simpa [h] using hω
  rw [h2, zero_add] at h1
  exact one_ne_zero h1

private lemma proj_diag_ne_one [CharP K 2] {v : Kˣ} (hv : v ≠ 1) :
    proj 3 K (uc22pwI3dSL K v) ≠ 1 := by
  intro h
  rw [proj_eq_one_iff] at h
  obtain ⟨c, -, hmat⟩ := (mem_scalars (n := 3) (K := K)).mp h
  have h00 : (v : K) = (c : K) := by
    have := congrFun (congrFun hmat 0) 0
    simpa [coe_uc22pwI3dSL, uc22pwI3dm] using this
  have h11 : (1 : K) = (c : K) := by
    have := congrFun (congrFun hmat 1) 1
    simpa [coe_uc22pwI3dSL, uc22pwI3dm] using this
  exact hv (Units.ext (h00.trans h11.symm))

private noncomputable def torusProj [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp ((MulAut.conj (changeOfBasis hω)).toMonoidHom.comp (uc22pwI3dSL K))

private theorem le_zpowers_of_fixes_hessE9 [Finite K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {n a m' : ℕ} (hK : Nat.card K = 2 ^ n) (hn : n = 2 ^ a * m') (hm : Odd m')
    {T : Subgroup (MulAut (projectiveSL 3 K))} (hT : IsPGroup 2 T)
    (hfix : ∀ t ∈ T, ∀ x ∈ hessE9 hω, t x = x) :
    T ≤ Subgroup.zpowers
      (fieldAut 3 K ((frobeniusAut 2 K) ^ m') * dualAut 3 K) := by
  intro t ht
  have hd_mem : proj 3 K (hessD hω) ∈ hessE9 hω := by
    rw [hessE9]
    exact Subgroup.subset_closure (by simp)
  have hP_mem : proj 3 K (hessP (K := K)) ∈ hessE9 hω := by
    rw [hessE9]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨b, hb, σ, ε, hε, hσω, ht_eq⟩ :=
    automorphisms_fixing_hessE9 (K := K) hω hω1 t
      (hfix t ht _ hd_mem) (hfix t ht _ hP_mem)
  let H : MulAut (projectiveSL 3 K) := fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K
  let h : MulAut (projectiveSL 3 K) := fieldAut 3 K σ * dualAut 3 K ^ ε
  have hh_mem : h ∈ Subgroup.zpowers H :=
    mem_zpowers_frobenius_mul_dualAut (K := K) hK hω hε hσω
  have hb3 : b ^ 3 = 1 := (hessE9_isElemAbelian (hω := hω)).2 b hb
  have hconj3 : (MulAut.conj b) ^ 3 = 1 := by
    rw [← map_pow, hb3, map_one]
  have hfixb : h b = b :=
    fieldAut_mul_dualAut_fixes_hessE9 (K := K) hω σ hε hσω b hb
  have hcomm : Commute (MulAut.conj b) h := by
    rw [Commute]
    have h1 : h * MulAut.conj b * h⁻¹ = MulAut.conj b := by
      rw [mul_conj_mul_inv_eq h b, hfixb]
    calc MulAut.conj b * h = (h * MulAut.conj b * h⁻¹) * h := by rw [h1]
      _ = h * MulAut.conj b := by group
  have ht3 : t ^ 3 = h ^ 3 := by
    rw [ht_eq, hcomm.mul_pow, hconj3, one_mul]
  have ht3_mem : t ^ 3 ∈ Subgroup.zpowers H := by
    rw [ht3]
    exact Subgroup.pow_mem (K := Subgroup.zpowers H) hh_mem 3
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have ht_mem_H : t ∈ Subgroup.zpowers H :=
    CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.mem_of_pow_mem_of_coprime
      (Subgroup.zpowers H) ((by norm_num : Nat.Coprime 3 2).pow_right k) ht3_mem
      (by rw [htk]; exact Subgroup.one_mem _)
  have ht_odd := mem_zpowers_pow_oddPart_of_pow_two_eq_one (K := K) hK hn hm ht_mem_H htk
  rwa [pow_oddPart_eq_fieldAut_mul_dualAut (K := K) hm] at ht_odd

end KS165LProof

open KS165LProof CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.PSLThreeGraphField
  CFSG.RankThree.PartTwo.KFacts.PSLThreeHessian
  CFSG.Semidihedral.FixedFieldData
  CFSG.InnerNormalizedAutomorphisms Matrix in
theorem ks165L : KS165L := by
  intro Q _ _ n hq h9 h2 hQ hZ3 hiso B hB hB9 T hT hT1 hTB
  classical
  obtain ⟨heven, hn3, hn4, hn6⟩ := arithmetic hq h9 h2
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hKcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by omega)
  obtain ⟨ω, hω⟩ := exists_omega hn0 hq
  have hω1 : ω ≠ 1 := omega_ne_one_of_char_two hω
  obtain ⟨φ⟩ := hiso
  have hZ : Subgroup.center Q = ⊥ := center_eq_bot hn4 hQ hZ3 φ
  let Ψ : Q ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ
  have hisoL : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi Q 2 n :=
    Or.inl ⟨hq, ⟨Ψ⟩⟩
  have hcent : ∀ b ∈ B, b ≠ 1 → ∀ y : Q, y * b = b * y →
      ∀ k : ℕ, y ^ 2 ^ k = 1 → y = 1 := by
    intro b hb hb1 y hyc k hyk
    exact CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.eq_one_of_commute_two_pow
      (n := n) hn1 hn3 hisoL (hB.2 b hb) hb1 hyc hyk
  have hfixedQ := fixed_of_mem (X := Q) (r := 3) Nat.prime_three
    (by norm_num : 3 ≠ 2) hB.1 hB.2 (by rw [hB9]; norm_num) hZ hcent hT hTB
  have hfixQ : ∀ t ∈ T, ∀ b ∈ B, t b = b := hfixedQ.2
  let Φ : Q ≃* projectiveSL 3 (GaloisField 2 n) := mulEquivProjectiveSL φ hZ
  let T₁ : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 n))) :=
    T.map (MulAut.congr Φ).toMonoidHom
  let B₁ : Subgroup (projectiveSL 3 (GaloisField 2 n)) :=
    B.map (Φ : Q →* projectiveSL 3 (GaloisField 2 n))
  have hB₁ : CFSG.Assembly.IsElemAbelian 3 B₁ :=
    CFSG.Open.IsElemAbelian.map hB (Φ : Q →* projectiveSL 3 (GaloisField 2 n))
  have hB₁9 : Nat.card B₁ = 9 := by
    dsimp [B₁]
    rw [Subgroup.card_map_of_injective Φ.injective, hB9]
  have hT₁2 : IsPGroup 2 T₁ := hT.map (MulAut.congr Φ).toMonoidHom
  have hfixB₁ : ∀ t ∈ T₁, ∀ b ∈ B₁, t b = b := by
    intro t ht b hb
    obtain ⟨t₀, ht₀, ht_eq⟩ := Subgroup.mem_map.mp ht
    obtain ⟨b₀, hb₀, hb_eq⟩ := Subgroup.mem_map.mp hb
    rw [← ht_eq, ← hb_eq]
    change (MulAut.congr Φ) t₀ (Φ b₀) = Φ b₀
    rw [MulAut.congr_apply]
    simp [hfixQ t₀ ht₀ b₀ hb₀]
  obtain ⟨g, hg⟩ := exists_conjAut_map_eq_hessE9 (K := GaloisField 2 n) hω hω1
    (n := n) hKcard hq h9 hB₁ hB₁9
  let α : MulAut (projectiveSL 3 (GaloisField 2 n)) := conjAut 3 (GaloisField 2 n) g
  let T₂ : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 n))) :=
    T₁.map (MulAut.conj α).toMonoidHom
  have hαmap : B₁.map α.toMonoidHom = hessE9 hω := hg
  have hT₂2 : IsPGroup 2 T₂ := hT₁2.map (MulAut.conj α).toMonoidHom
  have hfixH : ∀ t ∈ T₂, ∀ x ∈ hessE9 hω, t x = x := by
    intro t ht x hx
    obtain ⟨t₁, ht₁, ht_eq⟩ := Subgroup.mem_map.mp ht
    rw [← ht_eq]
    have hx' : x ∈ B₁.map α.toMonoidHom := by rw [hαmap]; exact hx
    obtain ⟨b, hb, hbα⟩ := Subgroup.mem_map.mp hx'
    have hbα' : α b = x := hbα
    have hpre : α⁻¹ x = b := by
      rw [← hbα']
      exact α.symm_apply_apply b
    calc (MulAut.conj α) t₁ x = α (t₁ (α⁻¹ x)) := by
          simp [MulAut.conj_apply]
      _ = α (t₁ b) := by rw [hpre]
      _ = α b := by rw [hfixB₁ t₁ ht₁ b hb]
      _ = x := hbα'
  obtain ⟨a, m', hm', hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  let σ : GaloisField 2 n ≃+* GaloisField 2 n := (frobeniusAut 2 (GaloisField 2 n)) ^ m'
  have hσω : σ ω = ω ^ 2 := by
    dsimp [σ]
    exact frobenius_pow_apply_omega (K := GaloisField 2 n) hω hm'
  let gfield : MulAut (projectiveSL 3 (GaloisField 2 n)) :=
    fieldAut 3 (GaloisField 2 n) σ * dualAut 3 (GaloisField 2 n)
  have hT₂_le : T₂ ≤ Subgroup.zpowers gfield := by
    have h := le_zpowers_of_fixes_hessE9 (K := GaloisField 2 n) hω hω1
      (n := n) (a := a) (m' := m') hKcard hn_eq hm' hT₂2 hfixH
    simpa [gfield, σ] using h
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor
    (k := n) (by omega : 2 ≤ n) hn6
  have hp3 : 3 < p := hp.three_lt_of_two_lt (by omega : 2 < n)
  have hp2 : ¬ p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  obtain ⟨u, huord⟩ :=
    CFSG.Timmesfeld.IsPrimitivePrimeDivisor.exists_orderOf_eq
      (K := GaloisField 2 n) (k := n) (p := p) hn0 hKcard hp
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [orderOf_zero (GaloisField 2 n)] at huord
    exact hp.prime.ne_zero huord.symm
  let u' : (GaloisField 2 n)ˣ := Units.mk0 u hu0
  have hu'ord : orderOf u' = p := by
    rw [← orderOf_units (y := u'), Units.val_mk0, huord]
  have hu'1 : u' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu'ord
    exact hp.prime.ne_one hu'ord.symm
  let f : (GaloisField 2 n)ˣ →* projectiveSL 3 (GaloisField 2 n) :=
    torusProj (K := GaloisField 2 n) hω
  let E : Subgroup (projectiveSL 3 (GaloisField 2 n)) :=
    (Subgroup.zpowers u').map f
  have hE : IsPGroup p E := by
    have hzp : IsPGroup p (Subgroup.zpowers u') := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hu'ord, pow_one]
    exact hzp.map f
  have hf_u' : f u' ≠ 1 := by
    have hDne : proj 3 (GaloisField 2 n) (uc22pwI3dSL (GaloisField 2 n) u') ≠ 1 :=
      proj_diag_ne_one (K := GaloisField 2 n) hu'1
    intro h
    apply hDne
    have hconj : (MulAut.conj (proj 3 (GaloisField 2 n) (changeOfBasis hω)))
        (proj 3 (GaloisField 2 n) (uc22pwI3dSL (GaloisField 2 n) u')) = 1 := by
      simpa [f, torusProj, MulAut.conj_apply] using h
    exact (MulAut.conj (proj 3 (GaloisField 2 n) (changeOfBasis hω))).injective (by
      rw [hconj, map_one])
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hmem : f u' ∈ E :=
      Subgroup.mem_map_of_mem f (Subgroup.mem_zpowers u')
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hf_u' hmem
  let σu : (GaloisField 2 n)ˣ →* (GaloisField 2 n)ˣ :=
    Units.map σ.toRingHom.toMonoidHom
  have hσu_u' : σu u' = u' ^ (2 ^ m') := by
    apply Units.ext
    simp only [σu, Units.coe_map, Units.val_pow_eq_pow_val]
    change σ (u' : GaloisField 2 n) = (u' : GaloisField 2 n) ^ (2 ^ m')
    rw [show σ = (frobeniusAut 2 (GaloisField 2 n)) ^ m' from rfl, frobenius_pow_apply]
  have hσu_mem : σu u' ∈ Subgroup.zpowers u' := by
    rw [hσu_u']
    exact Subgroup.npow_mem_zpowers u' (2 ^ m')
  have hzpmap : Subgroup.map σu (Subgroup.zpowers u') ≤ Subgroup.zpowers u' := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hσu_mem
  have hgtorus : ∀ v : (GaloisField 2 n)ˣ, gfield (f v) = f (σu v) := by
    intro v
    have hD : ((uc22pwI3dSL (GaloisField 2 n) v :
        SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) =
        diagonal ![(v : GaloisField 2 n), 1, (v : GaloisField 2 n)⁻¹] := by
      rw [coe_uc22pwI3dSL]
      simp [uc22pwI3dm]
    have hD' : ((uc22pwI3dSL (GaloisField 2 n) (σu v) :
        SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) =
        diagonal ![σ (v : GaloisField 2 n), 1, (σ (v : GaloisField 2 n))⁻¹] := by
      rw [coe_uc22pwI3dSL]
      simp [uc22pwI3dm, σu, Units.coe_map]
    have h := graphField_image_diag (K := GaloisField 2 n) (ω := ω) (σ := σ)
      hω hσω (lam := (v : GaloisField 2 n)) (Units.ne_zero v)
      (uc22pwI3dSL (GaloisField 2 n) v) (uc22pwI3dSL (GaloisField 2 n) (σu v)) hD hD'
    simpa [f, torusProj, gfield, MulAut.conj_apply, map_mul] using h
  have hmap_le : E.map gfield.toMonoidHom ≤ E := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp he
    change gfield (f v) ∈ E
    rw [hgtorus v]
    exact Subgroup.mem_map_of_mem f (hzpmap (Subgroup.mem_map_of_mem σu hv))
  have hmap : E.map gfield.toMonoidHom = E := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (f := gfield.toMonoidHom) gfield.injective]
  have hEinv : ∀ e : projectiveSL 3 (GaloisField 2 n), e ∈ E ↔ gfield e ∈ E := by
    intro e
    constructor
    · intro he
      exact hmap_le (Subgroup.mem_map_of_mem gfield.toMonoidHom he)
    · intro hge
      have hmem : gfield e ∈ E.map gfield.toMonoidHom := by rwa [hmap]
      obtain ⟨e', he', hge'⟩ := Subgroup.mem_map.mp hmem
      have heq : e' = e := gfield.injective hge'
      simpa [heq] using he'
  have hgen : ∀ e ∈ E, e ≠ 1 →
      Subgroup.closure ({x : projectiveSL 3 (GaloisField 2 n) | gfield x = x} ∪ {e}) = ⊤ := by
    intro e he he1
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp he
    have hv1 : v ≠ 1 := by
      intro h
      apply he1
      rw [h, map_one]
    have hvord : orderOf v = p := by
      have hdvd : orderOf v ∣ p := by
        have h := orderOf_dvd_natCard (⟨v, hv⟩ : Subgroup.zpowers u')
        rwa [Nat.card_zpowers, Subgroup.orderOf_mk, hu'ord] at h
      rcases (Nat.dvd_prime hp.prime).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hv1
      · exact h
    have hvordK : orderOf (v : GaloisField 2 n) = p := by
      rw [orderOf_units, hvord]
    have h2ord : orderOf ((v : GaloisField 2 n) ^ 2) = p :=
      hp.orderOf_pow_eq_of_not_dvd hvordK hp2
    have hclosure :
        Subfield.closure ({(v : GaloisField 2 n) ^ 2} : Set (GaloisField 2 n)) = ⊤ :=
      hp.subfield_closure_eq_top_of_orderOf hn0 hKcard h2ord
    have hD : ((uc22pwI3dSL (GaloisField 2 n) v :
        SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) =
        diagonal ![(v : GaloisField 2 n), 1, (v : GaloisField 2 n)⁻¹] := by
      rw [coe_uc22pwI3dSL]
      simp [uc22pwI3dm]
    have h := closure_fixed_union_diag_eq_top (K := GaloisField 2 n) (ω := ω) (σ := σ)
      hω hσω (lam := (v : GaloisField 2 n)) (Units.ne_zero v) hclosure
      (uc22pwI3dSL (GaloisField 2 n) v) hD
    simpa [f, torusProj, gfield, MulAut.conj_apply, map_mul] using h
  exact concl_of_mulEquiv Φ (concl_of_conj α
    (concl_of_le_zpowers (g := gfield) hT₂_le hp.prime hp3 hE hEne hEinv hgen))

end CFSG.RankThree.PartTwo.Sec16
