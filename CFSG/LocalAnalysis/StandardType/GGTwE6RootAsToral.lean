module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCoreDefs
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Order
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
import CFSG.LieType.Chevalley.LangRootArithmeticDet
import CFSG.LieType.Chevalley.ToralCentralizerBruhat
import CFSG.LieType.Chevalley.WeylNormalizerQuotient
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoTorus
import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Sylow
import CFSG.LieType.SeitzGeneration.ExcTorusThreeTw
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveFix
import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
import CFSG.RankThree.PartOne.KE.CTLangData
import CFSG.LieType.SeitzGeneration.ExcHigh.Product

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Malle.E27Lie.ExcCross
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


private theorem e6HRReflProd_smul_permLattice (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    e6HRReflProd • permLattice TwistTag.E6.perm γ = -γ := by
  rw [e6HRReflProd_smul]
  congr 1
  funext i
  simp only [permLattice, Function.comp_apply, e6_perm_symm_apply, perm6_perm6]

private theorem isUnit_det_symmetrizedCartan_twE6_five :
    IsUnit ((TwistTag.E6.tag.symmetrizedCartan.det : ℤ) : ZMod 5) := by
  have h : TwistTag.E6.tag.symmetrizedCartan.det = 3 := by
    rw [Tag.symmetrizedCartan, Matrix.det_mul]
    change (1 : Matrix (Fin 6) (Fin 6) ℤ).det * Tag.E6.cartan.det = 3
    rw [Matrix.det_one, one_mul, det_cartan_E6]
  rw [h]
  exact isUnit_iff_ne_zero.2 (by decide)

private theorem le_twistedE6RootGroup_of_isPGroup {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ)
    (hA : IsPGroup p A) : A ≤ twistedE6RootGroup K σ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hAR : A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ≤
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    (Subgroup.map_mono hAI).trans
      (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr)
  have hrel := twisted_E6_relIndex_dvd_three hℓ hf K hK σ.toRingHom hσ' (AlgebraicClosure K) Fr
    hFr hAR
  haveI : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  haveI : Finite ↥(A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) :=
    Finite.of_equiv _ (A.equivMapOfInjective _ (baseChangeGL_injective _)).toEquiv
  obtain ⟨n, hn⟩ := (hA.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).index
    (((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
      (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))))
  have h1 : ((twistedE6RootGroup K σ).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).relIndex
        (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) = 1 := by
    rw [Subgroup.relIndex] at hrel ⊢
    rw [hn] at hrel ⊢
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero]
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        ((dvd_pow_self p h0.ne').trans hrel)) hp3
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.relIndex_eq_one.1 h1 (Subgroup.mem_map_of_mem _ hx)
  rw [← baseChangeGL_injective _ hyx]
  exact hy

private theorem not_dvd_index_X6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice TwistTag.E6.perm u)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    ¬ p ∣ ((X6 (AlgebraicClosure K) Fr w0).comap
      ((MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (twistedE6RootGroup K σ).subtype))).index := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  set J := twistedE6RootGroup K σ
  haveI : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  haveI hJfin : Finite J := inferInstance
  set X := X6 L Fr w0
  set R := twistedFixedGroup TwistTag.E6 L Fr
  set C' := J.map (baseChangeGL (algebraMap K L))
  let fc : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L := (MulAut.conj g0).toMonoidHom
  have hfc_apply : ∀ x, fc x = g0 * x * g0⁻¹ := fun x => rfl
  have hXR : ∀ x ∈ X, fc x ∈ R := by
    intro x hx
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨?_, ?_⟩
    · rw [hfc_apply]
      exact mul_mem (mul_mem hg0C (X6_le_adjoint Fr _ hx)) (inv_mem hg0C)
    · have h1 := X6_fix hw0 hx
      rw [hfc_apply, map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w0 *
            twistHom TwistTag.E6 L Fr x *
            (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)⁻¹ =
          g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0 *
            twistHom TwistTag.E6 L Fr x *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)⁻¹) * g0⁻¹ := by group
        _ = g0 * x * g0⁻¹ := by rw [h1]
  set Y : Subgroup (ModGL TwistTag.E6.tag L) := C'.comap fc
  have hrel : Y.relIndex X ∣ 3 := by
    have h := twisted_E6_relIndex_dvd_three hℓ hf K hK σ.toRingHom hσ' L Fr hFr
      (X := X.map fc) (by
        rintro _ ⟨x, hx, rfl⟩
        exact hXR x hx)
    rwa [← Subgroup.relIndex_comap] at h
  set ι' : ↥J →* ModGL TwistTag.E6.tag L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K L)).comp J.subtype)
  have hι'inj : Function.Injective ι' :=
    (MulAut.conj g0⁻¹).injective.comp
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))
  have hrange : ι'.range = Y := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨(z : ModGL TwistTag.E6.tag K), z.2, ?_⟩
      change baseChangeGL (algebraMap K L) (z : ModGL TwistTag.E6.tag K) =
        g0 * ((MulAut.conj g0⁻¹)
          (baseChangeGL (algebraMap K L) (z : ModGL TwistTag.E6.tag K))) * g0⁻¹
      rw [MulAut.conj_apply, inv_inv]
      group
    · rintro ⟨c, hc, hcy⟩
      refine ⟨⟨c, hc⟩, ?_⟩
      change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) c) = y
      rw [MulAut.conj_apply, inv_inv]
      change baseChangeGL (algebraMap K L) c = g0 * y * g0⁻¹ at hcy
      rw [hcy]
      group
  set Z := X.comap ι' with hZ
  have hcardZ : Nat.card Z = Nat.card ↥(Y ⊓ X) := by
    rw [← Subgroup.card_map_of_injective hι'inj, hZ, Subgroup.map_comap_eq, hrange]
  have hz0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  have hm0 : Nat.card ↥(Y ⊓ X) ≠ 0 := hcardZ ▸ hz0
  have hr0 : Y.relIndex X ≠ 0 := fun h => by
    rw [h] at hrel
    exact absurd (Nat.eq_zero_of_zero_dvd hrel) (by norm_num)
  have hcardX : Y.relIndex X * Nat.card ↥(Y ⊓ X) = Nat.card X := Subgroup.relIndex_mul_card Y X
  have hq_ne : (((ℓ ^ f + 1 : ℕ)) : L) ≠ 0 := by
    have hz : ((ℓ : ℕ) : L) = 0 := CharP.cast_eq_zero L ℓ
    have : (((ℓ ^ f + 1 : ℕ)) : L) = 1 := by
      push_cast
      rw [hz, zero_pow (by omega), zero_add]
    rw [this]
    exact one_ne_zero
  have hT := card_twistedTorus6 (L := L) hFr hq_ne hw0
  have hdvdX := twistedTorus6_card_mul_dvd (L := L) Fr w0
  rw [hT] at hdvdX
  have hn0 : Nat.card X ≠ 0 := by
    rw [← hcardX]
    exact mul_ne_zero hr0 hm0
  have hq0 : ℓ ^ f + 1 ≠ 0 := by omega
  have hvX : 6 * (ℓ ^ f + 1).factorization p + (51840 : ℕ).factorization p ≤
      (Nat.card X).factorization p := by
    have h1 := (Nat.factorization_le_iff_dvd (by positivity) hn0).2 hdvdX p
    rw [Nat.factorization_mul (pow_ne_zero 6 hq0) (by norm_num), Nat.factorization_pow] at h1
    simpa using h1
  have hvsplit : (Nat.card X).factorization p =
      (Y.relIndex X).factorization p + (Nat.card ↥(Y ⊓ X)).factorization p := by
    rw [← hcardX, Nat.factorization_mul hr0 hm0, Finsupp.add_apply]
  have hvr : (Y.relIndex X).factorization p = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd fun h => ?_
    have h3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h.trans hrel)
    omega
  have hvJ : (Nat.card J).factorization p ≤
      6 * (ℓ ^ f + 1).factorization p + (51840 : ℕ).factorization p := by
    rcases eq_or_lt_of_le hp5 with h5 | h7
    · have hJ : (Nat.card J).factorization 5 = 6 * (ℓ ^ f + 1).factorization 5 + 1 :=
        factorization_five_card_twistedE6_of_dvd_add_one hℓ hf K hK σ hσ (by rw [h5]; exact hpq)
      have h51 : 1 ≤ (51840 : ℕ).factorization 5 :=
        (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_five (by norm_num)).1 (by norm_num)
      rw [← h5]
      omega
    · have hp6 : p ≠ 6 := by
        rintro rfl
        exact absurd hp (by decide)
      have hJ : (Nat.card J).factorization p = 6 * (ℓ ^ f + 1).factorization p :=
        ExcHigh.factorization_card_twistedE6_of_seven_le_of_dvd_add_one hℓ hf K hK σ hσ hp
          (by omega) hpq
      omega
  have hidx : Z.index * Nat.card Z = Nat.card J := Subgroup.index_mul_card Z
  have hi0 : Z.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hvidx : (Nat.card J).factorization p =
      Z.index.factorization p + (Nat.card Z).factorization p := by
    rw [← hidx, Nat.factorization_mul hi0 hz0, Finsupp.add_apply]
  rw [hcardZ] at hvidx
  intro hdiv
  have h1 : 0 < Z.index.factorization p := hp.factorization_pos_of_dvd hi0 hdiv
  omega

private theorem le_torusGroup_of_monomial {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpL : ((p : ℕ) : L) ≠ 0)
    {E : Subgroup (ModGL TwistTag.E6.tag L)} (hEm : E ≤ monomialSubgroup TwistTag.E6.tag L)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (h4 : p ^ 4 ≤ Nat.card E) : E ≤ torusGroup TwistTag.E6.tag L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by
    have := pow_pos hp.pos 4
    omega)
  let ψ : ↥E →* WeylGroup TwistTag.E6.tag :=
    (weylQuotientHom TwistTag.E6.tag L).comp (Subgroup.inclusion hEm)
  have hψw : ∀ (x : ↥E) (w : WeylGroup TwistTag.E6.tag) (k : ModGL TwistTag.E6.tag L),
      k ∈ torusGroup TwistTag.E6.tag L →
        (x : ModGL TwistTag.E6.tag L) = k * canonicalRep (coxeterSystem TwistTag.E6.tag) L w →
          ψ x = w := by
    intro x w k hk hxk
    have h : weylQuotientHom TwistTag.E6.tag L ⟨x, hEm x.2⟩ = w := weylQuotientHom_eq (by
      change MapsRootLines (x : ModGL TwistTag.E6.tag L) w
      rw [hxk]
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w))
    exact h
  have htor : ∀ x : ↥E, ψ x = 1 → (x : ModGL TwistTag.E6.tag L) ∈ torusGroup TwistTag.E6.tag L := by
    intro x hx
    obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets (hEm x.2)
    have hw := hψw x w k hk hxk
    rw [hx] at hw
    rw [hxk, ← hw, canonicalRep_one, mul_one]
    exact hk
  have hEp' : ∀ y : ↥E, y ^ p = 1 := fun y =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hEp _ y.2)
  intro x hx
  refine htor ⟨x, hx⟩ ?_
  by_contra hne
  have hwp : ψ ⟨x, hx⟩ ^ p = 1 := by rw [← map_pow, hEp', map_one]
  have hwo : orderOf (ψ ⟨x, hx⟩) = p := orderOf_eq_prime hwp hne
  have hpW : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by
    have h := orderOf_dvd_natCard (ψ ⟨x, hx⟩)
    have hW : Nat.card (WeylGroup TwistTag.E6.tag) = 51840 := CFSG.RankThree.E6.card_weylGroup_E6
    rw [hwo, hW] at h
    norm_num
    exact h
  obtain rfl : p = 5 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpW with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((5 : ℕ) : L) := ⟨hpL⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Lˣ, IsPrimitiveRoot ζ 5 :=
    ⟨_, IsPrimitiveRoot.isUnit_unit (by norm_num) hζ0⟩
  have hζo : orderOf ζ = 5 := hζ.eq_orderOf.symm
  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hdet := isUnit_det_symmetrizedCartan_twE6_five
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets (hEm hx)
  have hw : ψ ⟨x, hx⟩ = w := hψw ⟨x, hx⟩ w k hk hxk
  have hfix : ∀ b : ψ.ker, ∃ s : Fin TwistTag.E6.tag.rank → ZMod 5,
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ5 s =
          ((b : ↥E) : ModGL TwistTag.E6.tag L) ∧
        TableBExc.torusAct TwistTag.E6.tag 5 w s = s := by
    intro b
    have hbT := htor b (MonoidHom.mem_ker.1 b.2)
    obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ5 hdet
      (v := ((b : ↥E) : ModGL TwistTag.E6.tag L)) ⟨hbT, hEp _ (b : ↥E).2⟩
    refine ⟨s, hs, ExcFrames.frameDiag_injective (τ := TwistTag.E6.tag) hζo hζ5 hdet ?_⟩
    rw [← ExcFrames.canonicalRep_conj_frameDiag, hs]
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hbT
    have hc := hEc x hx _ (b : ↥E).2
    rw [hxk, ha] at hc
    rw [ha]
    have hka := rootDiagUnit_mul_comm_of_mem_torusGroup a hk
    have h2 : canonicalRep (coxeterSystem TwistTag.E6.tag) L w * rootDiagUnit TwistTag.E6.tag a =
        rootDiagUnit TwistTag.E6.tag a * canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by
      refine mul_left_cancel (a := k) ?_
      calc k * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
            rootDiagUnit TwistTag.E6.tag a) =
          k * canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
            rootDiagUnit TwistTag.E6.tag a := (mul_assoc _ _ _).symm
        _ = rootDiagUnit TwistTag.E6.tag a *
            (k * canonicalRep (coxeterSystem TwistTag.E6.tag) L w) := hc
        _ = rootDiagUnit TwistTag.E6.tag a * k *
            canonicalRep (coxeterSystem TwistTag.E6.tag) L w := (mul_assoc _ _ _).symm
        _ = k * rootDiagUnit TwistTag.E6.tag a *
            canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by rw [hka]
        _ = k * (rootDiagUnit TwistTag.E6.tag a *
            canonicalRep (coxeterSystem TwistTag.E6.tag) L w) := mul_assoc _ _ _
    rw [h2, mul_inv_cancel_right]
  choose s hs1 hs2 using hfix
  let F : ψ.ker → {z : Fin Tag.E6.rank → ZMod 5 // TableBExc.torusAct .E6 5 w z = z} :=
    fun b => ⟨s b, hs2 b⟩
  have hF : Function.Injective F := by
    intro b b' hbb
    have h1 : s b = s b' := congrArg Subtype.val hbb
    have h2 : ((b : ↥E) : ModGL TwistTag.E6.tag L) = ((b' : ↥E) : ModGL TwistTag.E6.tag L) := by
      rw [← hs1 b, ← hs1 b', h1]
    exact Subtype.ext (Subtype.ext h2)
  have hker : Nat.card ψ.ker ≤ 5 ^ 2 :=
    (Nat.card_le_card_of_injective F hF).trans
      (ExcFrames.card_fix_torusAct_E6_five (hw ▸ hwo))
  have hrange : Nat.card ψ.range ≤ 5 := by
    have hpE : IsPGroup 5 ↥E := fun y => ⟨1, by rw [pow_one]; exact hEp' y⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1
      (hpE.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
    have hdvd : Nat.card ψ.range ∣ 51840 := by
      have hW : Nat.card (WeylGroup TwistTag.E6.tag) = 51840 :=
        CFSG.RankThree.E6.card_weylGroup_E6
      rw [← hW]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hn] at hdvd ⊢
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num
    · exact absurd ((Nat.pow_dvd_pow 5 h).trans hdvd) (by norm_num)
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hle : Nat.card ↥E ≤ 5 ^ 2 * 5 := by
    rw [← hcard]
    exact Nat.mul_le_mul hker hrange
  norm_num at h4 hle
  omega

theorem exists_twLangData_of_dvd_add_one {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ q + 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAI : A ≤ twistedE6InndiagGL K σ) (hA : IsElemAbelian p A) (h4 : p ^ 4 ≤ Nat.card A) :
    ∃ D : ExcWideThree.TwLangData K σ q A, D.c = 1 ∧
      ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  set ℓ := ringChar K
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hpq
      have := Nat.le_of_dvd (by norm_num) hpq
      omega
    · exact h0
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K ℓ := ringChar.charP K
  set L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hpA : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x.1 x.2)⟩
  have hAC := le_twistedE6RootGroup_of_isPGroup hℓ hf hK σ hσ Fr hFr hp (by omega) hAI hpA
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) hf L e6HRReflProd
  have hidx := not_dvd_index_X6 hℓ hf hK σ hσ Fr hFr e6HRReflProd_smul hg0C hg0 hp hp5 hpq
  haveI : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  haveI : Finite (twistedE6RootGroup K σ) := inferInstance
  have hE : IsPGroup p (A.subgroupOf (twistedE6RootGroup K σ)) :=
    hpA.comap_of_injective _ (Subgroup.subtype_injective _)
  obtain ⟨g, hg⟩ := ExcHighThree.exists_conj_le_of_not_dvd_index _ hidx hE
  set b : ModGL TwistTag.E6.tag L :=
    baseChangeGL (algebraMap K L) (g : ModGL TwistTag.E6.tag K)
  obtain ⟨-, hle, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf
    K hK σ.toRingHom hσ' L Fr hFr
  have hbR : b ∈ twistedFixedGroup TwistTag.E6 L Fr := hle ⟨g, g.2, rfl⟩
  obtain ⟨hbC, hbF⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hbR
  have hg0'C : b * g0 ∈ adjointGroup TwistTag.E6.tag L := mul_mem hbC hg0C
  have hg0' : twistHom TwistTag.E6 L Fr (b * g0) =
      b * g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd := by
    rw [map_mul, hbF, hg0, mul_assoc]
  have hmX : ∀ x ∈ A, (b * g0)⁻¹ * baseChangeGL (algebraMap K L) x * (b * g0) ∈
      X6 L Fr e6HRReflProd := by
    intro x hx
    have hm := hg ⟨x, hAC hx⟩ hx
    rw [Subgroup.mem_comap] at hm
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      MulAut.conj_apply, inv_inv] at hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at hm
    have key : ∀ a c d : ModGL TwistTag.E6.tag L,
        (c * a)⁻¹ * d * (c * a) = a⁻¹ * (c⁻¹ * d * c) * a := fun a c d => by group
    rw [key]
    exact hm
  set φ : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj (b * g0)⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K L)) with hφdef
  have hφ : ∀ x, φ x = (b * g0)⁻¹ * baseChangeGL (algebraMap K L) x * (b * g0) := fun x => by
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hφinj : Function.Injective φ :=
    (MulAut.conj (b * g0)⁻¹).injective.comp (baseChangeGL_injective _)
  have hpL : ((p : ℕ) : L) ≠ 0 := by
    intro h
    have h1 : ℓ ∣ p := (CharP.cast_eq_zero_iff L ℓ p).1 h
    have h2 : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 h1
    have h3 : p ∣ ℓ ^ f := by
      rw [← h2]
      exact dvd_pow_self ℓ (by omega)
    have h5 : p ∣ 1 := (Nat.dvd_add_right h3).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h5)
  have hT : A.map φ ≤ torusGroup TwistTag.E6.tag L := by
    refine le_torusGroup_of_monomial hp hp5 hpL ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [hφ]
      exact X6_le_monomial _ _ (hmX x hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcommA x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hA.2 x hx, map_one]
    · rw [Subgroup.card_map_of_injective hφinj]
      exact h4
  have hc : ∀ x ∈ A, baseChangeGL (algebraMap K L) (1 * x * 1⁻¹ : ModGL TwistTag.E6.tag K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd)
        (twistHom TwistTag.E6 L Fr)).map (MulAut.conj (b * g0)).toMonoidHom := by
    intro x hx
    rw [one_mul, inv_one, mul_one]
    refine ⟨φ x, mem_twistedTorusOf.2 ⟨hT ⟨x, hx, rfl⟩, ?_⟩, ?_⟩
    · rw [hφ]
      exact X6_fix e6HRReflProd_smul (hmX x hx)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφ]
      group
  exact ⟨⟨e6HRReflProd, Fr, hFr, b * g0, hg0'C, hg0', 1, one_mem _, hc⟩, rfl,
    e6HRReflProd_smul_permLattice⟩

theorem _root_.CFSG.StandardType.TwE6FieldCore.subfieldLangDatumFive_holds :
    TwE6FieldCore.SubfieldLangDatumFive :=
  fun K _ _ σ q hK hσ p hp hp5 hpq A hAI hA h4 =>
    exists_twLangData_of_dvd_add_one σ hK hσ hp hp5 hpq hAI hA h4

end CFSG.StandardType.TwE6RootAs

end
