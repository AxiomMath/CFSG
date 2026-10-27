module

public import CFSG.RankThree.PartOne.KLC.TwistedTorusRank
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KF.D4Sylow
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Abstract

theorem two_le_pRank_triality_of_hom {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (n g0 : ModGL TwistTag.D4.tag L)
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hrat : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.D4.tag L)
    (hφ : Function.Injective φ)
    (hφT : φ.range ≤ twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hpL : (p : L) ≠ 0 := fun h0 => hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1
    ((CharP.cast_eq_zero_iff L ℓ p).1 h0)).symm
  have hcard : Nat.card ((rootsOfUnity p L) × (rootsOfUnity p L)) = p ^ 2 := by
    rw [Nat.card_prod, card_rootsOfUnity_eq hp hpL, sq]
  have hpow : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L), z ^ p = 1 := fun z =>
    Prod.ext (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 z.1.2))
      (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 z.2.2))
  exact le_pRank_of_twistedTorus (triEmb K σ L) triEmb_injective
    (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) n g0 hg0C hg0 hp
    (fun X _ hXC hXF P hPX _ => hPX.trans (hrat X hXC hXF)) (fun a b => mul_comm a b) hpow hcard
    φ hφ hφT

end Abstract

section Phi1

theorem card_rootsOfUnity_finite_field {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card Kˣ) : Nat.card (rootsOfUnity p K) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
  have hprim : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.2 hζ
  have h2 : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.2 hprim
  exact h2.card_rootsOfUnity

theorem two_le_pRank_triality_phi1 {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}
    (h : KFU.D4Param p f K σ) :
    2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ) := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ) := Subtype.finite
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 3 - 1 ^ 3 := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3
    rw [one_pow] at h1
    exact h.dvd.trans h1
  have hcμ := card_rootsOfUnity_finite_field h.prime hdvd
  have hA : Nat.card (Fin 2 → rootsOfUnity p K) = p ^ 2 := by
    rw [Nat.card_pi]
    simp only [hcμ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow : ∀ b : Fin 2 → rootsOfUnity p K, b ^ p = 1 := fun b =>
    funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (b i).2)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank_of_injective h.prime.one_lt (fun a b => mul_comm a b) hpow hA
    (KFU.tp3M h) (KFU.tp3M_injective h) (H := ⊤) le_top

end Phi1

section Tuples

variable {L : Type} [Field L]

@[expose] noncomputable def d4QTupleHom (q : ℕ) :
    Lˣ × Lˣ →* (Fin TwistTag.D4.tag.rank → Lˣ) where
  toFun z := d4Tuple z.2 (z.2 ^ q)⁻¹ z.1 (z.2 ^ (q * q))
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, one_pow, inv_one]
    exact vec4_one
  map_mul' z z' := by
    rw [vec4_mul]
    exact vec4_eq rfl (by simp [mul_pow, mul_inv_rev, mul_comm]) rfl (by simp [mul_pow])

@[expose] noncomputable def d4T36TupleHom (ε : ℤ) (q : ℕ) :
    Lˣ × Lˣ →* (Fin TwistTag.D4.tag.rank → Lˣ) where
  toFun z := d4Tuple z.2 ((z.1 ^ q) ^ ε) z.1 ((z.2 ^ q) ^ ε * z.1⁻¹)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, one_pow, one_zpow, inv_one, mul_one]
    exact vec4_one
  map_mul' z z' := by
    rw [vec4_mul]
    refine vec4_eq rfl (by simp [mul_pow, mul_zpow]) rfl ?_
    simp [mul_pow, mul_zpow, mul_inv_rev]
    ac_rfl

end Tuples

section Phi2

theorem two_le_pRank_triality_phi2 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1) :
    2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨g0, hg0C, hg0, hrat, -⟩ := d4Q_frame hf K hK σ hσ hp hp3 hpq (AlgebraicClosure K)
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpq' : p ∣ ℓ ^ f + 1 := Int.natCast_dvd_natCast.1 (by exact_mod_cast hpq)
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have := (Nat.dvd_add_right h1).1 hpq'
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hq3 : p ∣ (ℓ ^ f) ^ 3 + 1 := by
    have h1 : ℓ ^ f + 1 ∣ (ℓ ^ f) ^ 3 + 1 ^ 3 :=
      Odd.nat_add_dvd_pow_add_pow (ℓ ^ f) 1 (by decide)
    rw [one_pow] at h1
    exact hpq'.trans h1
  let Φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.D4.tag L :=
    (rootDiagUnitHom TwistTag.D4.tag L).comp ((d4QTupleHom (ℓ ^ f)).comp
      (MonoidHom.prodMap (rootsOfUnity p L).subtype (rootsOfUnity p L).subtype))
  have hΦ : ∀ z, Φ z = rootDiagUnit TwistTag.D4.tag (d4QTuple (ℓ ^ f) (z.1 : Lˣ) (z.2 : Lˣ)) :=
    fun z => rfl
  have hroot : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L),
      (z.1 : Lˣ) ^ p = 1 ∧ (z.2 : Lˣ) ^ p = 1 :=
    fun z => ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have h1 := congrArg d4QCoord hb
    rw [d4QTuple_coord, map_one] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e0)
  refine two_le_pRank_triality_of_hom σ hp hpℓ L (trialityOpposition L) g0 hg0C hg0 hrat Φ hinj ?_
  rintro _ ⟨z, rfl⟩
  rw [hΦ, d4Q_twistedTorus Fr]
  obtain ⟨hb, hc⟩ := hroot z
  refine ⟨_, d4QTuple_mem hFr ?_ ?_, rfl⟩
  · obtain ⟨k, hk⟩ := hpq'
    rw [hk, pow_mul, hb, one_pow]
  · obtain ⟨k, hk⟩ := hq3
    rw [hk, pow_mul, hc, one_pow]

end Phi2

section Phi36


theorem d4T36_lang_frame {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ n : ModGL TwistTag.D4.tag L,
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) =
        (fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f)).map
          (rootDiagUnitHom TwistTag.D4.tag L) ∧
      ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
        twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n ∧
        ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
          (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
            P ≤ (triEmb K σ L).range := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨w, hw⟩ := d4T36_weyl hε
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  have hnM : n ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : weylQuotientHom TwistTag.D4.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnC : n ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnM
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L n hnC
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hnM w hnW (d4T36M ε) hw
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨n, hT, g0, hg0C, hg0, fun P hPC hPF => ?_⟩
  rw [hrange]
  exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩

theorem two_le_pRank_triality_phi36 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨n, hT, g0, hg0C, hg0, hrat⟩ := d4T36_lang_frame hf hK σ hσ hε (AlgebraicClosure K)
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ 2 + ε * ((p ^ f : ℕ) : ℤ) := by
      have hq : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast dvd_pow_self p (by omega)
      exact dvd_add (dvd_pow hq (by norm_num)) (dvd_mul_of_dvd_right hq _)
    have h2 := (dvd_add_right h1).1 hpd
    have : p ∣ 1 := by exact_mod_cast h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  let Φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.D4.tag L :=
    (rootDiagUnitHom TwistTag.D4.tag L).comp ((d4T36TupleHom ε (ℓ ^ f)).comp
      (MonoidHom.prodMap (rootsOfUnity p L).subtype (rootsOfUnity p L).subtype))
  have hΦ : ∀ z, Φ z =
      rootDiagUnit TwistTag.D4.tag (d4T36Tuple ε (ℓ ^ f) (z.1 : Lˣ) (z.2 : Lˣ)) := fun z => rfl
  have hroot : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L),
      (z.1 : Lˣ) ^ p = 1 ∧ (z.2 : Lˣ) ^ p = 1 :=
    fun z => ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have h1 := congrArg d4QCoord hb
    rw [d4T36Tuple_coord, map_one] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e0)
  refine two_le_pRank_triality_of_hom σ hp hpℓ L n g0 hg0C hg0 hrat Φ hinj ?_
  rintro _ ⟨z, rfl⟩
  rw [hΦ, hT]
  obtain ⟨hb, hc⟩ := hroot z
  have hzp : ∀ x : Lˣ, x ^ p = 1 → x ^ (((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hpd
    rw [hk, zpow_mul, zpow_natCast, hx, one_zpow]
  exact ⟨_, d4T36Tuple_mem hε hFr (hzp _ hb) (hzp _ hc), rfl⟩

end Phi36

end CFSG.RankThree.PartOne.KLC
