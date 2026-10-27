module

public import CFSG.RankThree.PartOne.KE.SuzukiPlane
public import CFSG.RankThree.PartOne.KE.SuzukiDescentSp
public import CFSG.RankThree.PartOne.KE.LangDescent

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut
  szFieldAut_injective)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)

abbrev fixField {K : Type} [Field K] (σ : K ≃+* K) : Subfield K :=
  RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem mem_range_algebraMap_of_pow_card_eq {k L : Type} [Field k] [Finite k] [Field L]
    [Algebra k L] {c : L} (hc : c ^ Nat.card k = c) : c ∈ Set.range (algebraMap k L) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card] at hc
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hP0 : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq1
  have hroot : ∀ x : L, x ^ Fintype.card k = x →
      x ∈ (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L).roots.toFinset :=
    fun x hx => by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
  have hS : Finset.univ.image (algebraMap k L) ⊆
      (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L).roots.toFinset :=
    fun x hx => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hcard : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap k L)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k L).injective, Finset.card_univ]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq L hq1).le)
  have hc' := hroot c hc
  rw [← Finset.eq_of_subset_of_card_le hS hcard] at hc'
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hc'
  exact ⟨a, ha⟩

@[expose] def SuzukiLangStep : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (b : ℕ),
    ∃ S₀ : MulAut (antiSp L),
      (∀ g : antiSp L, glMat (S₀ g : GL (Fin 4) L) =
        (minorMap (glMat (g : GL (Fin 4) L))).map (fun x => x ^ 2 ^ b)) ∧
      ∀ x : antiSp L, ∃ h : antiSp L, x = h⁻¹ * S₀ h

section Fixed

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem pow_two_pow_mul_eq_self {k : Type} [Field k] [Finite k] {d : ℕ}
    (hk : Nat.card k = 2 ^ d) (z : k) (m : ℕ) : z ^ 2 ^ (d * m) = z := by
  have hz : z ^ 2 ^ d = z := by
    have : Fintype k := Fintype.ofFinite k
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add, mul_one, pow_add, pow_mul, ih, hz]

theorem glMap_injective {k K' : Type} [Field k] [Field K'] (f : k →+* K') :
    Function.Injective (Matrix.GeneralLinearGroup.map f : GL (Fin 4) k →* GL (Fin 4) K') :=
  fun _ _ h => Units.ext (Matrix.map_injective f.injective (congrArg Units.val h))

theorem glMat_szFieldAut {a : ℕ} {K : Type} [Field K] (σ : RingAut K) (g : suzukiGroup a K) :
    glMat (szFieldAut a K σ g : GL (Fin 4) K) = (glMat (g : GL (Fin 4) K)).map σ :=
  rfl

theorem map_powMap_comm {k K' : Type} [Field k] [Field K'] (f : k →+* K') {n m : ℕ}
    (h : ∀ c : k, c ^ n = c ^ m) (M : Matrix (Fin 4) (Fin 4) k) :
    (M.map (· ^ n)).map f = (M.map f).map (· ^ m) := by
  ext i j
  simp only [Matrix.map_apply]
  exact (congrArg f (h (M i j))).trans (map_pow f (M i j) m)

theorem fixed_szFieldAut_equiv (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : RingAut K} {b m : ℕ}
    (hk : Nat.card (fixField σ) = 2 ^ (2 * b + 1)) (hab : a = b + (2 * b + 1) * m) :
    Nonempty (↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _)) ≃*
      suzukiGroup b (fixField σ)) := by
  classical
  have hchar : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  set k := fixField σ with hkdef
  let ιk : ↥k →+* K := k.subtype
  have hkfin : Finite ↥k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hkchar : CharP ↥k 2 := inferInstance
  have hpowk : ∀ c : ↥k, c ^ 2 ^ (a + 1) = c ^ 2 ^ (b + 1) := by
    intro c
    have h1 : a + 1 = (b + 1) + (2 * b + 1) * m := by omega
    rw [h1, pow_add, pow_mul' c, pow_two_pow_mul_eq_self hk]
  set Fix := (szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _) with hFix
  set H1 : Subgroup (GL (Fin 4) K) :=
    (suzukiGroup b k).map (Matrix.GeneralLinearGroup.map ιk) with hH1
  set H2 : Subgroup (GL (Fin 4) K) := Fix.map (suzukiGroup a K).subtype with hH2
  have hH : H1 = H2 := by
    ext g
    constructor
    · rintro ⟨g₀, hg₀, rfl⟩
      have hg₀' : g₀ ∈ antiSp ↥k := suzukiGroup_le_antiSp hk hg₀
      set g₁ : antiSp K := antiSpMap ιk ⟨g₀, hg₀'⟩ with hg₁
      have hgl : glMat (g₁ : GL (Fin 4) K) = (glMat g₀).map ιk := rfl
      have hρ : minorMap (glMat g₀) = (glMat g₀).map (· ^ 2 ^ (b + 1)) :=
        (mem_suzukiGroup_iff_minorMap hk ⟨g₀, hg₀'⟩).1 hg₀
      have hmem : (g₁ : GL (Fin 4) K) ∈ suzukiGroup a K := by
        refine (mem_suzukiGroup_iff_minorMap hK g₁).2 ?_
        rw [hgl, minorMap_map_hom, hρ]
        exact map_powMap_comm ιk (fun c => (hpowk c).symm) (glMat g₀)
      refine ⟨⟨(g₁ : GL (Fin 4) K), hmem⟩, ?_, rfl⟩
      show szFieldAut a K σ ⟨(g₁ : GL (Fin 4) K), hmem⟩ = ⟨(g₁ : GL (Fin 4) K), hmem⟩
      refine Subtype.ext (Units.ext ?_)
      change glMat (szFieldAut a K σ ⟨(g₁ : GL (Fin 4) K), hmem⟩ : GL (Fin 4) K) = glMat g₁
      rw [glMat_szFieldAut]
      change ((glMat g₁).map σ) = glMat g₁
      rw [hgl, Matrix.map_map]
      ext i j
      simp only [Function.comp_apply, Matrix.map_apply]
      exact ((glMat g₀ i j).2 : σ _ = _)
    · rintro ⟨y, hy, rfl⟩
      have hyfix : szFieldAut a K σ y = y := hy
      have hentries : ∀ i j, (glMat (y : GL (Fin 4) K)) i j ∈ Set.range ιk := by
        intro i j
        have h1 := congrFun (congrFun (congrArg (fun z : suzukiGroup a K =>
          glMat (z : GL (Fin 4) K)) hyfix) i) j
        rw [glMat_szFieldAut] at h1
        exact ⟨⟨_, h1⟩, rfl⟩
      obtain ⟨g₀, hg₀⟩ := exists_glMap_eq_of_entries ιk (y : GL (Fin 4) K) hentries
      have hmap : (glMat g₀).map ιk = glMat (y : GL (Fin 4) K) := by
        rw [← hg₀]
        rfl
      have hyanti : (y : GL (Fin 4) K) ∈ antiSp K := suzukiGroup_le_antiSp hK y.2
      have hanti : g₀ ∈ antiSp ↥k := by
        rw [mem_antiSp]
        apply Matrix.map_injective ιk.injective
        dsimp only
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, minorJ_map, hmap]
        exact mem_antiSp.mp hyanti
      have hρy : minorMap (glMat (y : GL (Fin 4) K)) =
          (glMat (y : GL (Fin 4) K)).map (· ^ 2 ^ (a + 1)) :=
        (mem_suzukiGroup_iff_minorMap hK ⟨(y : GL (Fin 4) K), hyanti⟩).1 y.2
      have hsz : g₀ ∈ suzukiGroup b ↥k := by
        refine (mem_suzukiGroup_iff_minorMap hk ⟨g₀, hanti⟩).2 ?_
        apply Matrix.map_injective ιk.injective
        dsimp only
        have e1 : (minorMap (glMat g₀)).map ιk = minorMap (glMat (y : GL (Fin 4) K)) := by
          rw [← minorMap_map_hom, hmap]
        rw [e1, hρy, ← hmap]
        exact (map_powMap_comm ιk (fun c => (hpowk c).symm) (glMat g₀)).symm
      exact ⟨g₀, hsz, hg₀⟩
  let e1 : ↥Fix ≃* ↥H2 := Fix.equivMapOfInjective (suzukiGroup a K).subtype
    (suzukiGroup a K).subtype_injective
  let e2 : ↥H2 ≃* ↥H1 := MulEquiv.subgroupCongr hH.symm
  let e3 : ↥(suzukiGroup b k) ≃* ↥H1 := (suzukiGroup b k).equivMapOfInjective
    (Matrix.GeneralLinearGroup.map ιk) (glMap_injective ιk)
  exact ⟨(e1.trans e2).trans e3.symm⟩

end Fixed

theorem suzuki_prime_field_coset_descent_of_lang (hLang : SuzukiLangStep) :
    SuzukiPrimeFieldCosetDescent := by
  intro a ha K _ _ hK p hp hp2 α hα hαout
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hchar : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨σ₁, hσ₁, hσ₁ord, hσ₁top, hcardAut, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_two (by omega) hK
  have hcomm : ∀ u v : K ≃+* K, u * v = v * u := by
    intro u v
    have hu : u ∈ Subgroup.zpowers σ₁ := hσ₁top ▸ Subgroup.mem_top u
    have hv : v ∈ Subgroup.zpowers σ₁ := hσ₁top ▸ Subgroup.mem_top v
    obtain ⟨k, rfl⟩ := hu
    obtain ⟨l, rfl⟩ := hv
    exact zpow_mul_comm σ₁ k l
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₁, hσ₁top⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨-, ⟨e, he⟩, -, hinf, -, -, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  obtain ⟨⟨x, σ⟩, hxσ⟩ := e.surjective α
  have hα' : α = MulAut.conj x * szFieldAut a K σ := by rw [← hxσ, he]
  set σh := szFieldAut a K σ with hσh
  have hβ₁p : (MulAut.conj x * σh) ^ p = 1 := by
    rw [← hα']
    exact hα ▸ pow_orderOf_eq_one α
  have hσp : orderOf σ = p := by
    have h1 := hβ₁p
    rw [conj_mul_pow_aut] at h1
    have h2 : σh ^ p = (MulAut.conj ((List.range p).map fun i => (σh ^ i) x).prod)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    have h3 : szFieldAut a K (σ ^ p) ∈
        (szFieldAut a K).range ⊓ inner (suzukiGroup a K) := by
      refine ⟨⟨σ ^ p, rfl⟩, ?_⟩
      rw [map_pow]
      change σh ^ p ∈ inner (suzukiGroup a K)
      rw [h2]
      exact inv_mem ⟨_, rfl⟩
    rw [hinf, Subgroup.mem_bot] at h3
    have h4 : σ ^ p = 1 := szFieldAut_injective (h3.trans (map_one _).symm)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      apply hαout
      rw [hα', hσh, map_one, mul_one]
      exact ⟨x, rfl⟩
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h4) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hσ1
    · exact h
  have hpf : p ∣ 2 * a + 1 := by
    rw [← hσp, ← hcardAut]
    exact orderOf_dvd_natCard σ
  obtain ⟨d, hd⟩ := hpf
  have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ := hpodd
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  have hbp : (2 * b + 1) * p = 2 * a + 1 := by rw [← hb, hd, mul_comm]
  have hab : a = b + (2 * b + 1) * m := by
    have h1 := hbp
    rw [hm] at h1
    nlinarith [h1]
  have hbd : 2 * b + 1 = d := hb.symm
  have hσ₁pow : ∀ (n : ℕ) (c : K), (σ₁ ^ n) c = c ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hσ₁, ih, ← pow_mul, ← pow_succ']
  set e₀ := d * (m + 1) with he₀
  set τ₀ := σ₁ ^ e₀ with hτ₀def
  have hτ₀ord : orderOf τ₀ = p := by
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h, mul_zero] at hd
        omega
      · exact h
    have hcop : Nat.Coprime p (m + 1) := Nat.coprime_of_lt_prime (by omega) (by omega) hp
    have hg : Nat.gcd (p * d) (d * (m + 1)) = d := by
      rw [mul_comm p d, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    rw [hτ₀def, orderOf_pow' _ (by positivity), hσ₁ord, hd, hg, Nat.mul_div_cancel _ hd0]
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers σ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτ₀ord, hσp])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, σ ^ r = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers σ := hzz ▸ Subgroup.mem_zpowers τ₀
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, τ₀ ^ r' = σ := by
    have h : σ ∈ Subgroup.zpowers τ₀ := hzz ▸ Subgroup.mem_zpowers σ
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  set τh := szFieldAut a K τ₀ with hτh
  set x' := ((List.range r).map fun i => (σh ^ i) x).prod with hx'
  have hβ₂ : (MulAut.conj x * σh) ^ r = MulAut.conj x' * τh := by
    rw [conj_mul_pow_aut, hτh, ← hr]
    congr 1
    exact (map_pow (szFieldAut a K) σ r).symm
  have hβ₂p : (MulAut.conj x' * τh) ^ p = 1 := by
    rw [← hβ₂, ← pow_mul, mul_comm, pow_mul, hβ₁p, one_pow]
  have hτ₀p : τ₀ ^ p = 1 := by
    rw [← hτ₀ord]
    exact pow_orderOf_eq_one τ₀
  have hτhp : τh ^ p = 1 := by
    rw [hτh, ← map_pow, hτ₀p, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨S₀, hS₀, hLangS⟩ := hLang L b
  let ι : K →+* L := algebraMap K L
  have he₀eq : e₀ = a + 1 + b := by
    rw [he₀, ← hbd]
    nlinarith [hab]
  have hcτ : ∀ c : K, ι (τ₀ c) = (ι (c ^ 2 ^ (a + 1))) ^ 2 ^ b := by
    intro c
    rw [hτ₀def, hσ₁pow e₀, ← map_pow, ← pow_mul, ← pow_add, he₀eq]
  have heF₀ : ∀ g, szEmbed hK ι (τh g) = S₀ (szEmbed hK ι g) := by
    intro g
    apply antiSp_ext
    have hρ : minorMap (glMat (g : GL (Fin 4) K)) =
        (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ (a + 1)) :=
      (mem_suzukiGroup_iff_minorMap hK ⟨(g : GL (Fin 4) K), suzukiGroup_le_antiSp hK g.2⟩).1 g.2
    rw [hS₀, glMat_szEmbed, glMat_szEmbed, hτh, glMat_szFieldAut, minorMap_map_hom, hρ,
      Matrix.map_map, Matrix.map_map, Matrix.map_map]
    ext i j
    simp only [Function.comp_apply, Matrix.map_apply]
    exact hcτ _
  have hmem : ∀ h : antiSp L, (S₀ ^ p) h = h → h ∈ (szEmbed hK ι).range := by
    intro h hh
    rw [hm] at hh
    obtain ⟨h1, h2⟩ := fixed_of_S0_pow hS₀ (a := a) (m := m) (by linarith [hab]) hh
    have hf : ∀ x : L, x ^ 2 ^ (2 * a + 1) = x → x ∈ Set.range ι := fun x hx =>
      mem_range_algebraMap_of_pow_card_eq (k := K) (by rw [hK]; exact hx)
    obtain ⟨g, hg⟩ := mem_range_szEmbed hK ι hf h1 h2
    exact ⟨g, hg⟩
  obtain ⟨u, hu⟩ := exists_inner_conj_eq_of_lang (suzuki_center_eq_bot ha hK) τh (by omega)
    hτhp S₀ hLangS (szEmbed hK ι) (szEmbed_injective hK ι) heF₀ hmem x' hβ₂p
  have hrr : (MulAut.conj x * σh) ^ (r * r') = MulAut.conj x * σh := by
    have hσrr : σ ^ (r * r') = σ ^ 1 := by rw [pow_mul, hr, hr', pow_one]
    rw [pow_eq_pow_iff_modEq, hσp] at hσrr
    have hdvd : orderOf (MulAut.conj x * σh) ∣ p := orderOf_dvd_of_pow_eq_one hβ₁p
    have h2 := Nat.ModEq.of_dvd hdvd hσrr
    rw [← pow_eq_pow_iff_modEq, pow_one] at h2
    exact h2
  have hfinal : MulAut.conj u * α * (MulAut.conj u)⁻¹ = szFieldAut a K σ := by
    rw [hα', ← hrr, pow_mul, ← conj_pow, hβ₂, hu, hτh]
    rw [← map_pow, hr']
  obtain ⟨-, S, hS, hScard⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσp] at hScard
  have hSk : S = fixField σ := by
    refine SetLike.coe_injective (Set.ext fun c => ?_)
    rw [hS]
    constructor
    · intro hc
      exact hc σ (Subgroup.mem_zpowers σ)
    · intro hc τ hτ
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) c :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hc)
      exact MulAction.mem_stabilizer_iff.1 (hle hτ)
  have hk : Nat.card (fixField σ) = 2 ^ (2 * b + 1) := by
    rw [← hSk, hScard, hd', hbd]
  exact ⟨σ, u, b, fixField σ, inferInstance, inferInstance, hσp, hbp, hk, hfinal,
    fixed_szFieldAut_equiv hK hk hab⟩

end CFSG.RankThree.PartOne.KE
