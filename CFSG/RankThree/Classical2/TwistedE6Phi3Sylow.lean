module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Rational

variable (K : Type) [Field K] (σ : K →+* K) (Ω : Type) [Field Ω] [Algebra K Ω] (Fr : Ω →+* Ω)

@[expose] def phi3C : Subgroup (ModGL Tag.E6 Ω) :=
  (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω))

@[expose] def phi3CStar (g : ModGL Tag.E6 Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  (phi3C K σ Ω).map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def phi3TStar (g : ModGL Tag.E6 Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  phi3Torus Ω Fr ⊓ phi3CStar K σ Ω g

variable {K σ Ω Fr}

theorem phi3_rational_bridge {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K Ω]
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    Finite (phi3Rzero Ω Fr) ∧ ⁅phi3Rzero Ω Fr, phi3Rzero Ω Fr⁆ = phi3C K σ Ω ∧
    (∃ k : ℕ, (phi3C K σ Ω).relIndex (phi3Rzero Ω Fr) = 3 ^ k) ∧
    Nat.card (phi3C K σ Ω) = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) ∧
    Nat.card (phi3Rzero Ω Fr) =
      (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) ∧
    ∀ p : ℕ, p.Prime → 3 < p →
      ordProj[p] (Nat.card (phi3C K σ Ω)) = ordProj[p] (Nat.card (phi3Rzero Ω Fr)) := by
  obtain ⟨h1, -, h3, h4, -, h6, h7⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ hσ Ω Fr hFr
  exact ⟨h1, h3, h4, Subgroup.card_map_of_injective (baseChangeGL_injective _), h6, h7⟩

theorem phi3_rational_layer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K Ω]
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) :
    Finite (phi3FixedGroup Ω Fr) ∧
    ⁅phi3FixedGroup Ω Fr, phi3FixedGroup Ω Fr⁆ = phi3CStar K σ Ω g ∧
    phi3CStar K σ Ω g ≤ phi3FixedGroup Ω Fr ∧
    ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).Normal ∧
    (∃ k : ℕ, ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).index = 3 ^ k) ∧
    Nat.card (phi3CStar K σ Ω g) = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) ∧
    Nat.card (phi3FixedGroup Ω Fr) =
      (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) ∧
    ∀ p : ℕ, p.Prime → 3 < p →
      ordProj[p] (Nat.card (phi3CStar K σ Ω g)) = ordProj[p] (Nat.card (phi3FixedGroup Ω Fr)) := by
  obtain ⟨hfin, hder, ⟨k, hk⟩, hCcard, hRcard, hpp⟩ := phi3_rational_bridge hℓ hf hK hσ hFr
  have hR := phi3FixedGroup_eq_map hg hgn
  set φ := (MulAut.conj g⁻¹).toMonoidHom
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  have hCs : phi3CStar K σ Ω g = (phi3C K σ Ω).map φ := rfl
  have hRcard' : Nat.card (phi3FixedGroup Ω Fr) = Nat.card (phi3Rzero Ω Fr) := by
    rw [hR, Subgroup.card_map_of_injective hφinj]
  have hCcard' : Nat.card (phi3CStar K σ Ω g) = Nat.card (phi3C K σ Ω) := by
    rw [hCs, Subgroup.card_map_of_injective hφinj]
  have hder' : ⁅phi3FixedGroup Ω Fr, phi3FixedGroup Ω Fr⁆ = phi3CStar K σ Ω g := by
    rw [hR, ← Subgroup.map_commutator, hder, hCs]
  have hle : phi3CStar K σ Ω g ≤ phi3FixedGroup Ω Fr := by
    rw [← hder']
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).Normal := by
    have e : (phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr) =
        ⁅(⊤ : Subgroup (phi3FixedGroup Ω Fr)), ⊤⁆ := by
      have h1 : ⁅phi3FixedGroup Ω Fr, phi3FixedGroup Ω Fr⁆ =
          Subgroup.map (phi3FixedGroup Ω Fr).subtype
            ⁅(⊤ : Subgroup (phi3FixedGroup Ω Fr)), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map (phi3FixedGroup Ω Fr).subtype,
          Subgroup.range_subtype]
      rw [← hder', h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  refine ⟨?_, hder', hle, hnormal, ⟨k, ?_⟩, hCcard'.trans hCcard, hRcard'.trans hRcard,
    fun p hp hp3 => ?_⟩
  · rw [hR]
    exact Finite.of_surjective (fun x : phi3Rzero Ω Fr =>
      (⟨φ x, x, x.2, rfl⟩ : (phi3Rzero Ω Fr).map φ)) (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  · change (phi3CStar K σ Ω g).relIndex (phi3FixedGroup Ω Fr) = 3 ^ k
    rw [hCs, hR, Subgroup.relIndex_map_map_of_injective _ _ hφinj, hk]
  · rw [hCcard', hRcard']
    exact hpp p hp hp3

theorem phi3_sylow_layer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K Ω]
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) :
    (∃ S : Sylow p (phi3CStar K σ Ω g),
      ∀ x ∈ S, (x : ModGL Tag.E6 Ω) ∈ phi3TStar K σ Ω Fr g) ∧
    (∀ P : Subgroup (ModGL Tag.E6 Ω), P ≤ phi3C K σ Ω → IsPGroup p P →
      ∃ c ∈ phi3C K σ Ω, P.map (MulAut.conj c).toMonoidHom ≤
        (phi3TStar K σ Ω Fr g).map (MulAut.conj g).toMonoidHom) ∧
    phi3TorusTorsion Ω Fr p ≤ phi3TStar K σ Ω Fr g := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have hf0 : f ≠ 0 := by omega
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hf0]
  obtain ⟨hfin, -, hle, hnormal, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    phi3_rational_layer hℓ hf hK hσ hFr hg hgn
  set R := phi3FixedGroup Ω Fr
  set Cs := phi3CStar K σ Ω g
  set T₀ := phi3Torus Ω Fr
  set Ts := phi3TStar K σ Ω Fr g
  have : Finite Cs :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hT₀R : T₀ ≤ R := inf_le_right
  have : Finite T₀ := Finite.of_injective (Subgroup.inclusion hT₀R)
    (Subgroup.inclusion_injective hT₀R)
  have hTsT₀ : Ts ≤ T₀ := inf_le_left
  have hTsC : Ts ≤ Cs := inf_le_right
  have : Finite Ts := Finite.of_injective (Subgroup.inclusion hTsT₀)
    (Subgroup.inclusion_injective hTsT₀)
  have hrel : ∀ L : Subgroup (ModGL Tag.E6 Ω), L ≤ R → Cs.relIndex L ∣ 3 ^ k := by
    intro L hL
    have := hnormal
    rw [← Subgroup.relIndex_subgroupOf hL, ← hk]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hrel T₀ hT₀R)
  have hT₀card : 3 ^ j * Nat.card Ts = Nat.card T₀ := by
    rw [← hj, ← Subgroup.relIndex_mul_card (H := Cs) (K := T₀), inf_comm]
    rfl
  have hp3' : ¬ p ∣ 3 := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h) (by omega)
  have hTspos : Nat.card Ts ≠ 0 := Nat.card_pos.ne'
  have hfTs : (Nat.card Ts).factorization p = (Nat.card T₀).factorization p := by
    rw [← hT₀card, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hTspos,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hp3', smul_zero, zero_add]
  have hT₀val := (natCard_phi3Torus hFr hq0).1
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hfT₀ : (Nat.card T₀).factorization p = (Nat.card Cs).factorization p := by
    have h1 := hpp p hp hp3
    have h2 : (Nat.card Cs).factorization p = (Nat.card R).factorization p :=
      Nat.pow_right_injective hp.two_le h1
    rw [h2, hRcard, hT₀val, Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      padicValNat_phi3_torus_order hp hp3 hpq, padicValNat_twistedE6_order hp hp3 hpq hq1]
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p Ts))
  set S₁ : Subgroup Cs := ((S₀ : Subgroup Ts).map Ts.subtype).subgroupOf Cs with hS₁
  have hS₁le : (S₀ : Subgroup Ts).map Ts.subtype ≤ Cs := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact hTsC y.2
  have hS₁card : Nat.card S₁ = p ^ (Nat.card Cs).factorization p := by
    rw [hS₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₁le).toEquiv,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Sylow.card_eq_multiplicity,
      hfTs, hfT₀]
  set S : Sylow p Cs := Sylow.ofCard S₁ hS₁card
  have hSTs : ∀ x ∈ S, (x : ModGL Tag.E6 Ω) ∈ Ts := fun x hx => by
    obtain ⟨y, -, hy⟩ := (Subgroup.mem_subgroupOf.1 hx : (x : ModGL Tag.E6 Ω) ∈ _)
    rw [← hy]
    exact y.2
  refine ⟨⟨S, hSTs⟩, ?_, ?_⟩
  ·
    intro P hPC hP
    set C := phi3C K σ Ω
    have : Finite C := Finite.of_injective (fun x : C => (⟨(MulAut.conj g⁻¹) x, x, x.2, rfl⟩ : Cs))
      fun x y h => Subtype.ext ((MulAut.conj g⁻¹).injective (congrArg Subtype.val h))
    set S₂ : Subgroup (ModGL Tag.E6 Ω) :=
      ((S : Subgroup Cs).map Cs.subtype).map (MulAut.conj g).toMonoidHom with hS₂
    have hS₂C : S₂ ≤ C := by
      rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      obtain ⟨y, hy, hxy⟩ := x.2
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hxy]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    have hCcard : Nat.card C = Nat.card Cs :=
      (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    have hS₂card : Nat.card (S₂.subgroupOf C) = p ^ (Nat.card C).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₂C).toEquiv, hS₂,
        Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        Sylow.card_eq_multiplicity, hCcard]
    set S₃ : Sylow p C := Sylow.ofCard (S₂.subgroupOf C) hS₂card
    have hP' : IsPGroup p (P.subgroupOf C) := hP.comap_of_injective C.subtype
      (Subgroup.subtype_injective _)
    obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q S₃
    refine ⟨c, c.2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : (⟨x, hPC hx⟩ : C) ∈ (Q : Subgroup C) := hQ (Subgroup.mem_subgroupOf.2 hx)
    have hcx : MulAut.conj c • (⟨x, hPC hx⟩ : C) ∈ ((c • Q : Sylow p C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
    rw [hc] at hcx
    have hcx' := Subgroup.mem_subgroupOf.1 hcx
    obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hcx'
    exact ⟨y, hSTs y hy, hyx⟩
  ·
    have hTp : phi3TorusTorsion Ω Fr p ≤ T₀ := fun x hx => hx.1
    have h1 := hrel _ (hTp.trans hT₀R)
    have h2 : Cs.relIndex (phi3TorusTorsion Ω Fr p) ∣ p ^ 2 := by
      rw [← natCard_phi3TorusTorsion hFr hq0 hp hpq]
      exact Subgroup.relIndex_dvd_card _ _
    have hcop : Nat.Coprime (3 ^ k) (p ^ 2) :=
      Nat.Coprime.pow k 2 ((Nat.coprime_primes Nat.prime_three hp).2 (by omega))
    have h3 : Cs.relIndex (phi3TorusTorsion Ω Fr p) = 1 :=
      Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h1 h2)
    exact le_inf hTp (Subgroup.relIndex_eq_one.1 h3)

end Rational

section Torsion

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem eisensteinColumn_add {R : Type*} [CommRing R] (r a b a' b' : R) :
    eisensteinColumn r (a + a') (b + b') = eisensteinColumn r a b + eisensteinColumn r a' b' := by
  funext i
  revert i
  change ∀ i : Fin 6, (![-(a + a'), -r * (a + a') + (r - 1) * (b + b'), -(b + b'),
      (1 - r) * (b + b'), a + a', b + b'] : Fin 6 → R) i =
    (![-a, -r * a + (r - 1) * b, -b, (1 - r) * b, a, b] : Fin 6 → R) i +
      (![-a', -r * a' + (r - 1) * b', -b', (1 - r) * b', a', b'] : Fin 6 → R) i
  intro i
  fin_cases i <;> simp <;> ring

theorem nonempty_phi3TorusTorsion_mulEquiv [IsAlgClosed Ω] {q p : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : (q : Ω) = 0) (hp : p.Prime) (hpq : p ∣ q ^ 2 + q + 1) :
    Nonempty (phi3TorusTorsion Ω Fr p ≃* Multiplicative (ZMod p × ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpΩ : NeZero (p : Ω) := ⟨fun h => by
    obtain ⟨c, hc⟩ := hpq
    have h1 : ((q ^ 2 + q + 1 : ℕ) : Ω) = 0 := by rw [hc, Nat.cast_mul, h, zero_mul]
    push_cast at h1
    rw [hq] at h1
    norm_num at h1⟩
  have := IsSepClosed.hasEnoughRootsOfUnity Ω p
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  set ζ : Ωˣ := (hζ₀.isUnit hp.ne_zero).unit with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hζdef, IsUnit.unit_spec]
    exact hζ₀)
  set r : ZMod p := -(q : ZMod p) with hrdef
  have hr : r ^ 2 - r + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ p).mpr hpq
    push_cast at h
    rw [hrdef]
    linear_combination h
  set χ : ZMod p × ZMod p → (Fin Tag.E6.rank → Ωˣ) :=
    fun x i => ζ ^ (eisensteinColumn r x.1 x.2 i).val with hχ
  have hζmod : ∀ n : ℕ, ζ ^ (n % p) = ζ ^ n := fun n => by
    have h := pow_mod_orderOf ζ n
    rw [← hζ.eq_orderOf] at h
    exact h
  have hχadd : ∀ x y, χ (x + y) = χ x * χ y := fun x y => by
    funext i
    simp only [hχ, Prod.fst_add, Prod.snd_add, eisensteinColumn_add, Pi.add_apply, Pi.mul_apply,
      ZMod.val_add, hζmod, pow_add]
  have hχzero : χ 0 = 1 := by
    funext i
    simp only [hχ, Prod.fst_zero, Prod.snd_zero, eisensteinColumn_zero, Pi.zero_apply,
      ZMod.val_zero, pow_zero, Pi.one_apply]
  have hmem : ∀ x, rootDiagUnit Tag.E6 (χ x) ∈ phi3TorusTorsion Ω Fr p := fun x =>
    ⟨⟨rootDiagUnit_mem_torusGroup _,
      torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup _),
      (phi3Theta_rootDiagUnit_eq_iff hFr _).mpr
        ((zetaPow_mem_ker_monomialHom_iff hζ _ _).mpr
          ((phi3Matrix_transpose_mulVec_eq_zero_iff q _).mpr
            (dualMatrix_mulVec_eisensteinColumn hr x.1 x.2)))⟩, by
      change (rootDiagUnitHom Tag.E6 Ω (χ x)) ^ p = 1
      rw [← map_pow]
      change rootDiagUnit Tag.E6 _ = 1
      rw [show (χ x ^ p : Fin Tag.E6.rank → Ωˣ) = 1 by
        funext i
        rw [Pi.pow_apply, hχ, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply],
        rootDiagUnit_one]⟩
  let ψ : Multiplicative (ZMod p × ZMod p) →* phi3TorusTorsion Ω Fr p :=
    { toFun := fun x => ⟨rootDiagUnit Tag.E6 (χ (Multiplicative.toAdd x)),
        hmem (Multiplicative.toAdd x)⟩
      map_one' := Subtype.ext (by
        change rootDiagUnit Tag.E6 (χ 0) = 1
        rw [hχzero, rootDiagUnit_one])
      map_mul' := fun x y => Subtype.ext (by
        change rootDiagUnit Tag.E6 (χ (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
          rootDiagUnit Tag.E6 (χ (Multiplicative.toAdd x)) *
            rootDiagUnit Tag.E6 (χ (Multiplicative.toAdd y))
        rw [hχadd, rootDiagUnit_mul]) }
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 := rootDiagUnit_injective (congrArg Subtype.val hxy)
    have h2 : ∀ i, eisensteinColumn r (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 i =
        eisensteinColumn r (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2 i := fun i =>
      ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (congrFun h1 i))
    have h4 := h2 (e6Index 4)
    have h5 := h2 (e6Index 5)
    rw [eisensteinColumn_four, eisensteinColumn_four] at h4
    rw [eisensteinColumn_five, eisensteinColumn_five] at h5
    exact Multiplicative.toAdd.injective (Prod.ext h4 h5)
  have hcard := natCard_phi3TorusTorsion hFr hq hp hpq
  have : Finite (phi3TorusTorsion Ω Fr p) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ hp.ne_zero)
  have hbij : Function.Bijective ψ := (Nat.bijective_iff_injective_and_card ψ).2 ⟨hinj, by
    rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, sq]⟩
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

end Torsion

end CFSG.RankThree.Classical2
