module

public import CFSG.RankThree.PartOne.KGD.G2ThreeQPlus
public import CFSG.RankThree.Chevalley.SteinbergCAG2ThreeOddPowers

public section

namespace CFSG.RankThree.PartOne.KGD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
open CFSG.RankThree.Chevalley.SteinbergBN
open CFSG.LieType.Ree

theorem toral_or_monomial_neg_of_eq_mul_canonicalRep {L : Type} [Field L]
    {v h : ModGL .G2 L} (hh : h ∈ torusGroup .G2 L) {w : WeylGroup .G2}
    (hv : v = h * canonicalRep (coxeterSystem .G2) L w)
    (hw : w = 1 ∨ ∀ x : Fin Tag.G2.rank → ℤ, w • x = -x) :
    v ∈ torusGroup .G2 L ∨ ∃ hvN : v ∈ monomialSubgroup .G2 L,
      ∀ x : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 L ⟨v, hvN⟩ • x = -x := by
  have hvN : v ∈ monomialSubgroup .G2 L := hv ▸
    mul_mem (torusGroup_le_monomialSubgroup hh) (canonicalRep_mem_monomialSubgroup L w)
  have hπ : weylQuotientHom .G2 L ⟨v, hvN⟩ = w := by
    subst hv
    exact weylQuotientHom_eq (by
      simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w))
  rcases hw with rfl | hw
  · left
    rw [hv, canonicalRep_one, mul_one]
    exact hh
  · right
    exact ⟨hvN, fun x => by rw [hπ]; exact hw x⟩

theorem qplus_rootChar_eq_one {K K₂ : Type} [Field K] [Finite K] [Field K₂]
    [Algebra K K₂] (hKodd : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂}
    (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hzN : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hzN⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (F : adjointGroup .G2 K →* ModGL .G2 K₂)
    (y : adjointGroup .G2 K) {c : Fin Tag.G2.rank → K₂ˣ} (hc : F y = rootDiagUnit .G2 c)
    (hFyH : F y ∈ torusGroup .G2 K₂) {R : Subgroup (adjointGroup .G2 K)}
    (hR : R.map F = rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g)
    (hcommy : ∀ r ∈ R, y * r = r * y) : rootChar c α = 1 := by
  obtain ⟨_, -, hcent⟩ := rootSL2_comap_fixed_eq hKodd hdeg σ hσ hg hzdef hzN hw hα
  have hcomm := commute_rootSL2_of_commute_fixed hα hcent (y := F y)
    ⟨F y, hFyH, 1, one_mem _, mul_one _⟩ (fun A hA => by
      rw [Subgroup.mem_comap, ← hR] at hA
      obtain ⟨r, hr, hrA⟩ := hA
      rw [← hrA, ← map_mul, ← map_mul, hcommy r hr]) (uSL 1)
  have h1 : rootSL2 .G2 K₂ α (conjSL (diagUnitOne (rootChar c α)) (uSL 1)) =
      rootSL2 .G2 K₂ α (uSL 1) := by
    rw [← rootDiagUnit_conj_rootSL2 c hα, ← hc, hcomm, mul_inv_cancel_right]
  have h2 : sl2Upper K₂ ((rootChar c α : K₂) * 1) = sl2Upper K₂ 1 := by
    rw [← conjSL_sl2Upper]
    exact rootSL2_injective_of_field α h1
  have h3 := congrArg (fun Y : SL(2, K₂) => (Y : Matrix (Fin 2) (Fin 2) K₂) 0 1) h2
  simp [sl2Upper] at h3
  exact h3

theorem qplus_fixes_base {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]
    (hKodd : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hzN : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hzN⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (σ₂ : K₂ ≃+* K₂) {v : ModGL .G2 K₂}
    (hMex : v ∈ torusGroup .G2 K₂ ∨ ∃ hvN : v ∈ monomialSubgroup .G2 K₂,
      ∀ x : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨v, hvN⟩ • x = -x)
    (F : adjointGroup .G2 K →* ModGL .G2 K₂) {R : Subgroup (adjointGroup .G2 K)}
    (hR : R.map F = rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g)
    (s : adjointGroup .G2 K → adjointGroup .G2 K) (hsR : ∀ r ∈ R, s r = r)
    (hFs : ∀ h, F (s h) = twistedEntrywise v (σ₂ : K₂ →+* K₂) (F h)) :
    ∀ c : K, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ c := by
  obtain ⟨P₁, hP₁, -⟩ := rootSL2_comap_fixed_eq hKodd hdeg σ hσ hg hzdef hzN hw hα
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) K₂, ∀ A, rootSL2 .G2 K₂ α (semilinearConj M σ₂ A) =
      twistedEntrywise v (σ₂ : K₂ →+* K₂) (rootSL2 .G2 K₂ α A) := by
    rcases hMex with hvH | ⟨hvN, hvw⟩
    · obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvH
      refine ⟨diagUnitOne (rootChar c α), fun A => ?_⟩
      rw [twistedEntrywise_apply, entrywise_rootSL2_of_field, hc, rootDiagUnit_conj_rootSL2 c hα]
      rfl
    · exact exists_semilinearConj_rootSL2 hvN hvw σ₂ hα
  intro c
  obtain ⟨X, hX, htr⟩ := exists_trace_eq_algebraMap P₁ c
  rw [← hP₁, Subgroup.mem_comap, ← hR] at hX
  obtain ⟨r, hr, hrX⟩ := hX
  have h1 : twistedEntrywise v (σ₂ : K₂ →+* K₂) (rootSL2 .G2 K₂ α X) = rootSL2 .G2 K₂ α X := by
    rw [← hrX, ← hFs r, hsR r hr]
  have h2 : semilinearConj M σ₂ X = X := rootSL2_injective_of_field α (by rw [hM, h1])
  have h3 := congrArg (fun Y : SL(2, K₂) => Matrix.trace (Y : Matrix (Fin 2) (Fin 2) K₂)) h2
  rwa [trace_semilinearConj, htr] at h3

theorem qplus_three_frobenius_form {f : ℕ} (hf : 1 ≤ f) {K K₂ : Type} [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] [Field K₂] [Algebra K K₂] [Finite K₂]
    (hK : Nat.card K = 3 ^ f) (hK₂card : Nat.card K₂ = 3 ^ (2 * f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq₂ : p ∣ Nat.card K₂ - 1) {g u : ModGL .G2 K₂}
    (hg : g ∈ adjointGroup .G2 K₂) (hu : u ∈ adjointGroup .G2 K₂)
    (F : adjointGroup .G2 K →* ModGL .G2 K₂)
    (hFapp : ∀ h : adjointGroup .G2 K, F h = u *
      (g * baseChangeGL (algebraMap K K₂) (h : ModGL .G2 K) * g⁻¹) * u⁻¹)
    {P : Subgroup (adjointGroup .G2 K)} (hFP : P.map F = torusTorsion K₂ p)
    (s : MulAut (adjointGroup .G2 K)) (hsP : ∀ u' ∈ P, s u' = u') :
    ∃ (y : adjointGroup .G2 K) (σ' : K ≃+* K) (σ₂ : K₂ ≃+* K₂) (v : ModGL .G2 K₂),
      (∀ c, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ (σ' c)) ∧
      (∀ h : adjointGroup .G2 K, (s h : ModGL .G2 K) = (y : ModGL .G2 K) *
        Units.map (entrywiseHom σ'.toRingHom) (h : ModGL .G2 K) * (y : ModGL .G2 K)⁻¹) ∧
      (∀ h : adjointGroup .G2 K, F (s h) = twistedEntrywise v (σ₂ : K₂ →+* K₂) (F h)) ∧
      (v ∈ torusGroup .G2 K₂ ∨ ∃ hvN : v ∈ monomialSubgroup .G2 K₂,
        ∀ x : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨v, hvN⟩ • x = -x) := by
  classical
  have : CharP K₂ ReeTag.G2.prime :=
    charP_of_injective_algebraMap (algebraMap K K₂).injective ReeTag.G2.prime
  obtain ⟨-, hNF, -, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨y, a⟩, hya, -⟩ := hNF s
  dsimp only at hya
  obtain ⟨y', rfl⟩ : ∃ y' : adjointGroup .G2 K, y' = y := ⟨y, rfl⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : adjointGroup .G2 K₂, (w₀ : ModGL .G2 K₂) = u * g :=
    ⟨⟨_, mul_mem hu hg⟩, rfl⟩
  obtain ⟨Fa, hFacoe⟩ : ∃ Fa : adjointGroup .G2 K →* adjointGroup .G2 K₂,
      ∀ h, (Fa h : ModGL .G2 K₂) = F h :=
    ⟨F.codRestrict (adjointGroup .G2 K₂) fun h => by
      rw [hFapp h]
      exact mul_mem (mul_mem hu (mul_mem (mul_mem hg (baseChangeGL_mem_adjointGroup _ h.2))
        (inv_mem hg))) (inv_mem hu), fun h => rfl⟩
  have hFa : ∀ h, Fa h = w₀ * bcAdj (algebraMap K K₂) h * w₀⁻¹ := fun h =>
    Subtype.ext (by
      rw [hFacoe, hFapp h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw₀, coe_bcAdj]
      group)
  have hext := apply_conj_extension Fa (bcAdj (algebraMap K K₂)) w₀ hFa
    (ReeTag.G2.finiteExceptionalAut K ^ (a : ℕ)) (ReeTag.G2.finiteExceptionalAut K₂ ^ (a : ℕ))
    (fun h => finiteExceptionalAut_pow_bcAdj _ _ h) y'
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : adjointGroup ReeTag.G2.tag K₂, ∀ h, Fa (s h) =
      (MulAut.conj v₀ * ReeTag.G2.finiteExceptionalAut K₂ ^ (a : ℕ)) (Fa h) :=
    ⟨_, fun h => by rw [hya]; exact hext h⟩
  have hfixV : ∀ x : adjointGroup .G2 K₂, (x : ModGL .G2 K₂) ∈ torusTorsion K₂ p →
      (MulAut.conj v₀ * ReeTag.G2.finiteExceptionalAut K₂ ^ (a : ℕ)) x = x := by
    intro x hx
    rw [← hFP] at hx
    obtain ⟨u', hu', hux⟩ := hx
    have hxa : Fa u' = x := Subtype.ext (by rw [hFacoe]; exact hux)
    rw [← hxa, ← hv₀, hsP u' hu']
  obtain ⟨j, haj, hjf, hφj, h, hh, w', hvh, hw'⟩ :=
    (three_G2_toral_prime_plane_excludes_exceptional_odd_powers K₂ hK₂card hp hp3 hpq₂).1
      (MulAut.conj v₀ * ReeTag.G2.finiteExceptionalAut K₂ ^ (a : ℕ)) v₀ (a : ℕ)
      (by have := a.2; omega) rfl hfixV
  have hw'' : w' = 1 ∨ ∀ x : Fin Tag.G2.rank → ℤ, w' • x = -x :=
    hw'.imp (fun h => h.1) (fun h => h.1)
  obtain ⟨v₁, rfl⟩ : ∃ v₁ : adjointGroup .G2 K₂, v₁ = v₀ := ⟨v₀, rfl⟩
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
  obtain ⟨fr₂, hfr₂, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_three
    (by omega : 1 ≤ 2 * f) hK₂card
  set σ' : K ≃+* K := fr ^ j with hσ'def
  set σ₂ : K₂ ≃+* K₂ := fr₂ ^ j with hσ₂def
  have hσ' : ∀ c, σ' c = c ^ 3 ^ j := ringAut_pow_apply_of_frobenius hfr j
  have hσ₂ : ∀ c, σ₂ c = c ^ 3 ^ j := ringAut_pow_apply_of_frobenius hfr₂ j
  have hFr : ReeTag.G2.finiteFrobeniusAut K ^ j = entrywiseAdjointAut ReeTag.G2.tag σ' := by
    rw [← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := σ') (j := j) hσ',
      FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
  have hFr₂ : ReeTag.G2.finiteFrobeniusAut K₂ ^ j = entrywiseAdjointAut ReeTag.G2.tag σ₂ := by
    rw [← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := σ₂) (j := j) hσ₂,
      FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
  have hφKa : ReeTag.G2.finiteExceptionalAut K ^ (a : ℕ) =
      entrywiseAdjointAut ReeTag.G2.tag σ' := by
    rw [haj, finiteExceptionalAut_pow_two_mul, hFr]
  have hφ₂a : ReeTag.G2.finiteExceptionalAut K₂ ^ (a : ℕ) =
      entrywiseAdjointAut ReeTag.G2.tag σ₂ := by
    rw [hφj, hFr₂]
  obtain ⟨v, hv⟩ : ∃ v : ModGL .G2 K₂, v = (v₁ : ModGL .G2 K₂) := ⟨_, rfl⟩
  refine ⟨y', σ', σ₂, v, fun c => by rw [hσ₂, hσ', map_pow], fun h => ?_, fun h => ?_, ?_⟩
  · rw [hya, hφKa]
    show ((y' * entrywiseAdjointAut Tag.G2 σ' h * y'⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut]
  · have h1 := hv₀ h
    rw [hφ₂a] at h1
    have h2 : (Fa (s h) : ModGL .G2 K₂) = v *
        Units.map (entrywiseHom σ₂.toRingHom) (Fa h : ModGL .G2 K₂) * v⁻¹ := by
      rw [h1, hv]
      show (((v₁ * entrywiseAdjointAut Tag.G2 σ₂ (Fa h) * v₁⁻¹ : adjointGroup .G2 K₂)) :
        ModGL .G2 K₂) = _
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut]
    simp only [hFacoe] at h2
    exact h2
  · exact toral_or_monomial_neg_of_eq_mul_canonicalRep (L := K₂) (v := v) hh
      (by rw [hv]; exact hvh) hw''

theorem qplus_three_tail {K K₂ : Type} [Field K] [Finite K] [Field K₂]
    [Algebra K K₂] (hKodd : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂}
    (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hzN : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hzN⟩ • v = -v)
    (F : adjointGroup .G2 K →* ModGL .G2 K₂) (hF : Function.Injective F)
    {u₁ : adjointGroup .G2 K} {α₁ α₂ : Fin Tag.G2.rank → ℤ} (hα₁ : IsRoot .G2 α₁)
    (hα₂ : IsRoot .G2 α₂) (hα₁e : α₁ = Pi.single g2ia 1 ∨ α₁ = -Pi.single g2ia 1)
    (hα₂e : α₂ = Pi.single g2ir 1 ∨ α₂ = -Pi.single g2ir 1)
    {R₁ R₂ : Subgroup (adjointGroup .G2 K)}
    (hR₁ : R₁.map F = rootRankOneGroup .G2 K₂ α₁ ⊓ conjEntrywiseImage K g)
    (hR₂ : R₂.map F = rootRankOneGroup .G2 K₂ α₂ ⊓ conjEntrywiseImage K g)
    (hZ₁ : ∀ y ∈ centralizer ({u₁} : Set (adjointGroup .G2 K)), (∀ r ∈ R₁, y * r = r * y) →
      F y ∈ torusGroup .G2 K₂)
    (s : MulAut (adjointGroup .G2 K)) (hsu₁ : s u₁ = u₁) (hsR₁ : ∀ r ∈ R₁, s r = r)
    (hsR₂ : ∀ r ∈ R₂, s r = r) (y : adjointGroup .G2 K) (σ' : K ≃+* K) (σ₂ : K₂ ≃+* K₂)
    (v : ModGL .G2 K₂) (hcomm₂ : ∀ c, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ (σ' c))
    (hyσ : ∀ h : adjointGroup .G2 K, (s h : ModGL .G2 K) = (y : ModGL .G2 K) *
      Units.map (entrywiseHom σ'.toRingHom) (h : ModGL .G2 K) * (y : ModGL .G2 K)⁻¹)
    (hFs : ∀ h : adjointGroup .G2 K, F (s h) = twistedEntrywise v (σ₂ : K₂ →+* K₂) (F h))
    (hMex : v ∈ torusGroup .G2 K₂ ∨ ∃ hvN : v ∈ monomialSubgroup .G2 K₂,
      ∀ x : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨v, hvN⟩ • x = -x) :
    s = 1 := by
  have hfixK := qplus_fixes_base hKodd hdeg σ hσ hg hzdef hzN hw hα₁ σ₂ hMex F hR₁
    (fun h => s h) hsR₁ hFs
  have hσ'1 : σ' = 1 := RingEquiv.ext fun c => (algebraMap K K₂).injective (by
    rw [← hcomm₂, hfixK]
    rfl)
  have hsy : ∀ h : adjointGroup .G2 K, s h = y * h * y⁻¹ := by
    intro h
    apply Subtype.ext
    rw [hyσ h, hσ'1]
    have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL .G2 K) = h :=
      Units.ext (entrywise_id _)
    rw [e]
    rfl
  have hcommy : ∀ r : adjointGroup .G2 K, s r = r → y * r = r * y := fun r hr => by
    rw [hsy] at hr
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [hr]
  have hyu₁ : y ∈ centralizer ({u₁} : Set (adjointGroup .G2 K)) :=
    mem_centralizer_singleton_iff.2 (hcommy u₁ hsu₁)
  have hFyH : F y ∈ torusGroup .G2 K₂ := hZ₁ y hyu₁ fun r hr => hcommy r (hsR₁ r hr)
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hFyH
  have hci : ∀ (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ),
      (α = Pi.single i 1 ∨ α = -Pi.single i 1) → rootChar c α = 1 → c i = 1 := by
    intro i α hαe hcα
    rw [← rootChar_pi_single c i]
    rcases hαe with rfl | rfl
    · exact hcα
    · rw [rootChar_neg'] at hcα
      exact inv_eq_one.mp hcα
  have hc1 : c = 1 := funext fun i => by
    rcases fin_G2_cases i with rfl | rfl
    · exact hci _ _ hα₁e (qplus_rootChar_eq_one hKodd hdeg σ hσ hg hzdef hzN hw hα₁ F y hc hFyH hR₁
        fun r hr => hcommy r (hsR₁ r hr))
    · exact hci _ _ hα₂e (qplus_rootChar_eq_one hKodd hdeg σ hσ hg hzdef hzN hw hα₂ F y hc hFyH hR₂
        fun r hr => hcommy r (hsR₂ r hr))
  have hy1 : y = 1 := hF (by rw [hc, hc1, rootDiagUnit_one, map_one])
  exact MulEquiv.ext fun h => by rw [hsy h, hy1, one_mul, inv_one, mul_one]; rfl

theorem autThetaT_eq_bot_of_qplus_three {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (A : Subgroup (MulAut (adjointGroup .G2 K))) (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2)
    (hAinn : A ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    autThetaT p B A = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
    rw [ringChar.eq K 3]
    norm_num
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨P, hPmap, hPcard, hPp, hPpow⟩ := plane_comap_conj hinj hp hA hAcard hAinn
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius hK2
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpq₂ : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hK₂card : Nat.card K₂ = 3 ^ (2 * f) := by rw [hq2, hK, ← pow_mul, mul_comm]
  have : CharP K₂ ReeTag.G2.prime :=
    charP_of_injective_algebraMap (algebraMap K K₂).injective ReeTag.G2.prime
  obtain ⟨g, z, hg, -, hzdef, ⟨hzN, hw⟩, hΓfix, -, -, ⟨S₀, hS₀T⟩, ⟨V, hV, -, hVcard, -, -⟩,
    hroot, -, hcases⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hKodd hp hp3 hpq K₂ hdeg σ hσ
  have hVt : V = torusTorsion K₂ p := Subgroup.ext fun h => (hV h).trans mem_torusTorsion_iff.symm
  set ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  obtain ⟨u, hu⟩ : ∃ u : conjEntrywiseImage K g,
      (P.map ε.toMonoidHom).map (MulAut.conj u).toMonoidHom ≤ S₀ := by
    obtain ⟨Q', hQ'⟩ := (hPp.map ε.toMonoidHom).exists_le_sylow
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
    refine ⟨u, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 : MulAut.conj u • y ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' hy)
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 K₂ := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hFapp : ∀ h : adjointGroup .G2 K, F h = (u : ModGL .G2 K₂) *
      (g * baseChangeGL (algebraMap K K₂) (h : ModGL .G2 K) * g⁻¹) * (u : ModGL .G2 K₂)⁻¹ :=
    fun h => rfl
  have hFP : P.map F = torusTorsion K₂ p := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_torusTorsion_iff]
      refine ⟨(Subgroup.mem_subgroupOf.1 (hS₀T (hu ⟨ε y, ⟨y, hy, rfl⟩, rfl⟩))).1, ?_⟩
      rw [← map_pow, hPpow y hy, map_one]
    · rw [← hVt, hVcard, Subgroup.card_map_of_injective hF, hPcard]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := K₂ˣ) p
    (by rw [Nat.card_units]; exact hpq₂)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have key : ∀ i : Fin Tag.G2.rank, ∃ ui ∈ P, ui ≠ 1 ∧ ∃ α : Fin Tag.G2.rank → ℤ,
      IsRoot .G2 α ∧ (α = Pi.single i 1 ∨ α = -Pi.single i 1) ∧
      (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
          centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)).map F =
        rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
      CFSG.IsQuasisimple (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
        centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ∧
      ∀ y ∈ centralizer ({ui} : Set (adjointGroup .G2 K)),
        (∀ r ∈ (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
          centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)),
            y * r = r * y) → F y ∈ torusGroup .G2 K₂ := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      rcases fin_G2_cases i with rfl | rfl
      · exact ⟨g2ir, by decide⟩
      · exact ⟨g2ia, by decide⟩
    set c : Fin Tag.G2.rank → K₂ˣ := fun k => if k = i then 1 else ζ with hc
    have hcp : c ^ p = 1 := funext fun k => by
      by_cases hk : k = i <;> simp [hc, hk, hζp]
    have hc1 : c ≠ 1 := fun h => hζ1 (by simpa [hc, hji] using congrFun h j)
    have hci : c i = 1 := by simp [hc]
    have hdc : rootDiagUnit .G2 c ∈ P.map F := by
      rw [hFP]
      exact (rootDiagUnit_mem_torusTorsion_iff p c).2 hcp
    obtain ⟨ui, hui, hdu⟩ := hdc
    have hui1 : ui ≠ 1 := fun h => hc1 (rootDiagUnit_injective (by
      rw [← hdu, h, map_one, rootDiagUnit_one]))
    have hTc : rootDiagUnit .G2 c ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :=
      ⟨rootDiagUnit_mem_torusGroup_G2 c, hFrange ▸ ⟨ui, hdu⟩⟩
    have hco : orderOf c = p := orderOf_eq_prime hcp hc1
    have hao : orderOf (rootDiagUnit .G2 c) = p := by rw [orderOf_rootDiagUnit, hco]
    have hiker : (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ∈ rootCharKernel c :=
      ⟨isRoot_single .G2 i, by rw [rootChar_pi_single, hci]⟩
    have hne : rootCharKernel c ≠ ∅ := fun h => by
      rw [h] at hiker
      exact Set.notMem_empty _ hiker
    obtain ⟨α, hα, hkerα, hcomm, hZ, hZH, -⟩ := (hcases c hTc hao).2 hne
    obtain ⟨_, -, hQq⟩ := hroot α hα
    have hmapF : (centralizer ({ui} : Set (adjointGroup .G2 K))).map F =
        conjEntrywiseImage K g ⊓ centralizer {rootDiagUnit .G2 c} := by
      rw [map_centralizer_singleton_of_injective F hF ui, hFrange, hdu]
    obtain ⟨hRmap, hRq, -⟩ := derived_centralizer_data_of_map F hF hmapF hcomm hQq hZ hZH
    refine ⟨ui, hui, hui1, α, hα, ?_, hRmap, hRq, fun y hy hyR => ?_⟩
    · rw [hkerα] at hiker
      rcases hiker with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [show (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = -α from h, neg_neg])
    · refine hZH (hZ ▸ Subgroup.mem_inf.2 ⟨hmapF ▸ ⟨y, hy, rfl⟩,
        Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩)
      rw [← hRmap] at hw
      obtain ⟨r, hr, rfl⟩ := hw
      rw [← map_mul, ← map_mul, hyR r hr]
  obtain ⟨u₁, hu₁, hu₁1, α₁, hα₁, hα₁e, hR₁, hq₁, hZ₁⟩ := key g2ia
  obtain ⟨u₂, hu₂, hu₂1, α₂, hα₂, hα₂e, hR₂, hq₂, hZ₂⟩ := key g2ir
  have hbA : ∀ u ∈ P, (MulAut.conj u : MulAut (adjointGroup .G2 K)) ∈ A := fun u hu =>
    hPmap ▸ Subgroup.mem_map_of_mem _ hu
  have hb1 : ∀ u : adjointGroup .G2 K, u ≠ 1 →
      (MulAut.conj u : MulAut (adjointGroup .G2 K)) ≠ 1 := fun u hu h =>
    hu (hinj (by rw [h, map_one]))
  have hRY : ∀ u : adjointGroup .G2 K, (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
      centralizer ({u} : Set (adjointGroup .G2 K)) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨s₁, hs₁, hs₁eq⟩ := exists_mem_theta_of_mem_autThetaT hp B hs (hbA u₁ hu₁)
    (hb1 u₁ hu₁1) (hB ⟨u₁, rfl⟩)
  obtain ⟨s₂, hs₂, hs₂eq⟩ := exists_mem_theta_of_mem_autThetaT hp B hs (hbA u₂ hu₂)
    (hb1 u₂ hu₂1) (hB ⟨u₂, rfl⟩)
  have hsR₁ : ∀ r ∈ (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
      centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)),
      s r = r := fun r hr => by
    rw [← hs₁eq]
    exact hfix₁ s₁ hs₁ r hr
  have hsR₂ : ∀ r ∈ (⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
      centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)),
      s r = r := fun r hr => by
    rw [← hs₂eq]
    exact hfix₂ s₂ hs₂ r hr
  have hsP : ∀ u' ∈ P, s u' = u' := by
    intro u' hu'
    by_cases h1 : u' = 1
    · rw [h1, map_one]
    · obtain ⟨s', hs', hs'eq⟩ := exists_mem_theta_of_mem_autThetaT hp B hs (hbA u' hu')
        (hb1 u' h1) (hB ⟨u', rfl⟩)
      have hsC := Subgroup.map_subtype_le _ hs'
      rw [← hs'eq]
      exact apply_eq_of_commute_conj hinj
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hsC))
  have huC : (u : ModGL .G2 K₂) ∈ adjointGroup .G2 K₂ := (hΓfix.le u.2).1
  obtain ⟨y', σ', σ₂, v, hcomm₂, hyσ, hFs, hMex⟩ := qplus_three_frobenius_form hf hK hK₂card hp hp3
    hpq₂ hg huC F hFapp hFP s hsP
  rw [Subgroup.mem_bot]
  exact qplus_three_tail hKodd hdeg σ hσ hg hzdef hzN hw F hF hα₁ hα₂ hα₁e hα₂e hR₁ hR₂ hZ₁ s
    (hsP u₁ hu₁) hsR₁ hsR₂ y' σ' σ₂ v hcomm₂ hyσ hFs hMex

end CFSG.RankThree.PartOne.KGD
