module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


section Ambient

variable {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
  {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type} [Field L] [Algebra K L]
  [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n))

include hn hK hσ hFr

theorem baseChangeGL_mem_twistedFixed_of_mem_twInndiag {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ twInndiagGroup K σ) :
    baseChangeGL (algebraMap K L) w ∈ twistedFixedGroup TwistTag.E6 L Fr := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨-, hC, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hFr,
        map_pow]
  have hle : twInndiagGroup K σ ≤ (twistedFixedGroup TwistTag.E6 L Fr).comap
      (baseChangeGL (algebraMap K L)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hc | ⟨b, hb, rfl⟩)
    · exact hC (Subgroup.mem_map_of_mem _ hc)
    · exact baseChangeGL_rootDiagUnit_mem_twistedFixed hcomm hb
  exact hle hw

theorem conj_mem_C0_of_mem_twInndiag {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ twInndiagGroup K σ) {c : ModGL TwistTag.E6.tag K}
    (hc : c ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    w * c * w⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  obtain ⟨-, -, -, -, -, hN⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer
    TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr
  have h1 := (Subgroup.mem_normalizer_iff.1
    (hN (baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ hFr hw))
    (baseChangeGL (algebraMap K L) c)).1 (Subgroup.mem_map_of_mem _ hc)
  obtain ⟨c', hc', he⟩ := h1
  rw [← map_inv, ← map_mul, ← map_mul] at he
  rwa [baseChangeGL_injective (algebraMap K L) he] at hc'

theorem exists_decomp_of_mem_twInndiag {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ twInndiagGroup K σ) :
    ∃ b, IsCompatE6 σ.toRingHom b ∧ ∃ c ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      w = rootDiagUnit TwistTag.E6.tag b * c := by
  obtain ⟨hR, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr
  have h1 : baseChangeGL (algebraMap K L) w ∈ (twistedFixedGroup TwistTag.E6 L Fr :
      Set (ModGL TwistTag.E6.tag L)) := baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ
    hFr hw
  rw [hR] at h1
  obtain ⟨t, ht, _, ⟨c, hc, rfl⟩, htc⟩ := h1
  obtain ⟨b, hb, rfl⟩ := exists_compat_of_mem_graphFixedTorus hK σ hσ Fr hFr ht
  refine ⟨b, hb, c, hc, baseChangeGL_injective (algebraMap K L) ?_⟩
  rw [map_mul]
  exact htc.symm

theorem exists_mem_twInndiag_of_twist_fixed {h : ModGL TwistTag.E6.tag L}
    (hh : h ∈ adjointGroup TwistTag.E6.tag L) (hF : twistHom TwistTag.E6 L Fr h = h) :
    ∃ w ∈ twInndiagGroup K σ, baseChangeGL (algebraMap K L) w = h := by
  obtain ⟨hR, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr
  have h1 : h ∈ (twistedFixedGroup TwistTag.E6 L Fr : Set (ModGL TwistTag.E6.tag L)) := ⟨hh, hF⟩
  rw [hR] at h1
  obtain ⟨t, ht, _, ⟨c, hc, rfl⟩, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := exists_compat_of_mem_graphFixedTorus hK σ hσ Fr hFr ht
  exact ⟨_, mul_mem (rootDiagUnit_mem_twInndiag hb) (graphFixedRootGroup_le_twInndiag σ hc),
    map_mul _ _ _⟩

end Ambient

section Lang

variable {K : Type} [Field K] [Finite K]

theorem eq_one_of_commute_C0 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hq3 : 3 ≤ 2 ^ n) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ twInndiagGroup K σ)
    (hc : ∀ c ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, z * c = c * z) : z = 1 := by
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK2
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hinj, -, hC, -⟩ := diagram_fixed_ambient_centralizer_trivial_of_three_le TwistTag.E6
    Nat.prime_two hn hq3 K hK σ.toRingHom hσ L (algebraMap K L)
  apply hinj
  rw [map_one]
  refine hC _ (baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ
    (Fr := iterateFrobenius L 2 n) (fun c => by rw [iterateFrobenius_def]) hz).1 fun h hh => ?_
  obtain ⟨c, hc', rfl⟩ := hh
  rw [← map_mul, ← map_mul, hc c hc']

theorem center_twInndiag_eq_bot {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hq3 : 3 ≤ 2 ^ n) :
    Subgroup.center (twInndiagGroup K σ) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  rw [Subgroup.mem_bot]
  refine Subtype.ext (eq_one_of_commute_C0 hn hK hσ hq3 z.2 fun c hc => ?_)
  have := (Subgroup.mem_center_iff.1 hz) ⟨c, graphFixedRootGroup_le_twInndiag σ hc⟩
  exact (congrArg Subtype.val this).symm

theorem exists_conj_eq_twInndiagFieldAut_frob {n p e : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (φ : K ≃+* K)
    (hφ : ∀ c, φ c = c ^ 2) (hp : 1 ≤ p) (hpodd : Odd p) (he : 1 ≤ e) (hep : e * p = n)
    (hq3 : 3 ≤ 2 ^ n) (x : twInndiagGroup K σ)
    (hx : (MulAut.conj x * twInndiagFieldAut K σ (σ * φ ^ e)) ^ p = 1) :
    ∃ g : twInndiagGroup K σ, MulAut.conj g * (MulAut.conj x *
      twInndiagFieldAut K σ (σ * φ ^ e)) * (MulAut.conj g)⁻¹ =
        twInndiagFieldAut K σ (σ * φ ^ e) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK2
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hσφ : σ = φ ^ n := RingEquiv.ext fun c => by rw [hσ, ringEquiv_pow_sq_apply hφ]
  have hφ2n : φ ^ (2 * n) = 1 := RingEquiv.ext fun c => by
    rw [ringEquiv_pow_sq_apply hφ, RingAut.one_apply, show 2 ^ (2 * n) = (2 ^ n) ^ 2 by ring,
      ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hτp : (σ * φ ^ e) ^ p = 1 := by
    obtain ⟨k, hk⟩ := hpodd
    have hm : (n + e) * p = 2 * n * (k + 1) := by
      calc (n + e) * p = n * (p + 1) := by rw [← hep]; ring
        _ = 2 * n * (k + 1) := by rw [hk]; ring
    rw [hσφ, ← pow_add, ← pow_mul, hm, pow_mul, hφ2n, one_pow]
  obtain ⟨S, hLang, hSk⟩ := exists_lang_twist TwistTag.E6 (L := L) he 1
  have hFr : ∀ c : L, iterateFrobenius L 2 n c = c ^ (2 ^ n) := fun c => by
    rw [iterateFrobenius_def]
  have hmemL : ∀ {w : ModGL TwistTag.E6.tag K}, w ∈ twInndiagGroup K σ →
      baseChangeGL (algebraMap K L) w ∈ adjointGroup TwistTag.E6.tag L := fun hw =>
    (baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ hFr hw).1
  let ι : twInndiagGroup K σ →* adjointGroup TwistTag.E6.tag L :=
    ((baseChangeGL (algebraMap K L)).comp (twInndiagGroup K σ).subtype).codRestrict _ fun w =>
      hmemL w.2
  have hι : ∀ w : twInndiagGroup K σ,
      (ι w : ModGL TwistTag.E6.tag L) = baseChangeGL (algebraMap K L) w := fun _ => rfl
  have hιinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val hab))
  have hFrc : (iterateFrobenius L 2 e).comp (algebraMap K L) =
      (algebraMap K L).comp (φ ^ e).toRingHom := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def]
    change (algebraMap K L c) ^ 2 ^ e = algebraMap K L ((φ ^ e) c)
    rw [ringEquiv_pow_sq_apply hφ, map_pow]
  have heF₀ : ∀ w : twInndiagGroup K σ,
      ι (twInndiagFieldAut K σ (σ * φ ^ e) w) = S (ι w) := by
    intro w
    have hS1 := hSk 1 (ι w)
    simp only [pow_one, mul_one] at hS1
    have h1 : Units.map (entrywiseHom (iterateFrobenius L 2 e))
        (baseChangeGL (algebraMap K L) (w : ModGL TwistTag.E6.tag K)) =
          baseChangeGL (algebraMap K L)
            (Units.map (entrywiseHom (φ ^ e).toRingHom) (w : ModGL TwistTag.E6.tag K)) := by
      rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
        baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
    have h2 : diagramMap TwistTag.E6 L = baseChangeGL (algebraMap K L) (diagramMap TwistTag.E6 K) :=
      (baseChangeGL_diagramMap _ TwistTag.E6).symm
    apply Subtype.ext
    rw [hS1, hι, hι, coe_twInndiagFieldAut, h1, h2, ← map_inv, ← map_mul, ← map_mul,
      diagramMap_conj_E6 hK hσ (entrywise_mem_twInndiag (φ ^ e) w.2),
      units_map_entrywiseHom_comp]
    rfl
  have hP : diagramMap TwistTag.E6 L ^ (1 * p) = diagramMap TwistTag.E6 L := by
    obtain ⟨k, hk⟩ := hpodd
    rw [one_mul, hk, pow_add, pow_mul, show (2 : ℕ) = TwistTag.E6.order from rfl,
      diagramMap_pow_order, one_pow, one_mul, pow_one]
  have hFrn : (iterateFrobenius L 2 e) ^ p = iterateFrobenius L 2 n := RingHom.ext fun c => by
    rw [RingHom.coe_pow, iterateFrobenius_def]
    have hit : ∀ k : ℕ, (⇑(iterateFrobenius L 2 e))^[k] c = c ^ ((2 ^ e) ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep]
  have hmem : ∀ h : adjointGroup TwistTag.E6.tag L, (S ^ p) h = h → h ∈ ι.range := by
    intro h hh
    have hfix : twistHom TwistTag.E6 L (iterateFrobenius L 2 n) h = h := by
      rw [twistHom_apply, ← hFrn, ← hP, ← hSk p h, hh]
    obtain ⟨w, hw, hwι⟩ := exists_mem_twInndiag_of_twist_fixed hn hK hσ hFr h.2 hfix
    exact ⟨⟨w, hw⟩, Subtype.ext hwι⟩
  have hF₀p : twInndiagFieldAut K σ (σ * φ ^ e) ^ p = 1 := by rw [← map_pow, hτp, map_one]
  exact CFSG.RankThree.PartOne.KE.exists_inner_conj_eq_of_lang
    (center_twInndiag_eq_bot hn hK hσ hq3) _ hp hF₀p S hLang ι hιinj heF₀ hmem x hx

end Lang

end RecipeExcLang

end CFSG.StandardType
