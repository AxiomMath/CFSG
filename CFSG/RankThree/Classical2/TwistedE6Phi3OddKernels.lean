module

public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix
open scoped Matrix MatrixGroups Pointwise

section GroupTheory

variable {G : Type*} [Group G]

theorem odd_natCard_of_le_of_odd {D T : Subgroup G} (hDT : D ≤ T) (hT : Odd (Nat.card T))
    (V : Subgroup D) : Odd (Nat.card V) := by
  have hle : V.map D.subtype ≤ T := by
    rintro _ ⟨y, -, rfl⟩
    exact hDT y.2
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective D.subtype_injective] at h1
  exact Odd.of_dvd_nat hT h1

theorem odd_natCard_of_isSolvable_normal_of_centralizer_le {D P T : Subgroup G} [Finite D]
    (hPD : P ≤ D) (hPn : (P.subgroupOf D).Normal) (hP : CFSG.IsQuasisimple P)
    (hT : D ⊓ Subgroup.centralizer (P : Set G) ≤ T) (hTodd : Odd (Nat.card T))
    (V : Subgroup D) [V.Normal] (hV : Group.IsSolvable V) : Odd (Nat.card V) := by
  have hP' : CFSG.IsQuasisimple (P.subgroupOf D) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPD).symm hP
  have := hPn
  refine odd_card_of_isSolvable_normal hP' ?_ hV
  have hle : (Subgroup.centralizer ((P.subgroupOf D : Subgroup D) : Set D)).map D.subtype ≤
      T := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Subgroup.centralizer ((P.subgroupOf D : Subgroup D) : Set D) := hy
    refine hT ⟨y.2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy' ⟨z, hPD hz⟩ hz)
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective D.subtype_injective] at h1
  exact Odd.of_dvd_nat hTodd h1

theorem commutator_le_self' (D : Subgroup G) : ⁅D, D⁆ ≤ D :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutator_subgroupOf_normal (D : Subgroup G) : (⁅D, D⁆.subgroupOf D).Normal := by
  have e : ⁅D, D⁆.subgroupOf D = ⁅(⊤ : Subgroup D), ⊤⁆ := by
    have h1 : ⁅D, D⁆ = Subgroup.map D.subtype ⁅(⊤ : Subgroup D), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map D.subtype, Subgroup.range_subtype]
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [e]
  infer_instance

theorem map_perfectResidual_subgroupOf_normal (D : Subgroup G) :
    (((CFSG.perfectResidual D).map D.subtype).subgroupOf D).Normal := by
  have e : ((CFSG.perfectResidual D).map D.subtype).subgroupOf D = CFSG.perfectResidual D :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [e]
  refine ⟨fun n hn h => ?_⟩
  rw [CFSG.perfectResidual, Subgroup.mem_iInf] at hn ⊢
  exact fun i => (inferInstance : (derivedSeries D i).Normal).conj_mem n (hn i) h

end GroupTheory

theorem exists_eq_mul_eisLinePoint {p : ℕ} [Fact p.Prime] {r a b : ZMod p} {k : Fin 8}
    (h : eisensteinLineForm r a b k = 0) :
    ∃ m : ZMod p, a = m * (eisLinePoint r k).1 ∧ b = m * (eisLinePoint r k).2 := by
  have hne := eisLinePoint_ne_zero r k
  rw [eisensteinLineForm_eq] at h
  simp only [eisLinePoint] at hne ⊢
  set c := eisEval r (eisLine k).1
  set d := eisEval r (eisLine k).2
  by_cases hd : d = 0
  · have hc : c ≠ 0 := fun hc => hne (Prod.mk_eq_zero.2 ⟨hd, by simp [hc]⟩)
    have ha : a = 0 := by
      rw [hd, zero_mul, add_zero] at h
      exact (mul_eq_zero.1 h).resolve_left hc
    exact ⟨-b / c, by rw [ha, hd, mul_zero], by field_simp⟩
  · refine ⟨a / d, by field_simp, ?_⟩
    field_simp
    linear_combination h

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem exists_mem_phi3Line_of_twoA2 [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) {y : ModGL Tag.E6 Ω}
    (hy : y ∈ phi3TorusTorsion Ω Fr p) (hy1 : y ≠ 1)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) :
    ∃ k : Fin 8, k.val < 4 ∧ y ∈ phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi3TorusTorsion_iff hFr hζ hr y).1 hy
  have hab0 : (a, b) ≠ 0 := fun h => hy1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel y = rootKernel (eisensteinColumn (-(q : ZMod p)) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2A2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (-(q : ZMod p)) a b)).Nonempty := by
    have h1 : (parabolicRoots Tag.E6 supportA2A2).Nonempty := by
      rw [parabolicRoots_supportA2A2]
      exact ⟨_, Or.inl (chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide))⟩
    rw [← hw₀] at h1
    exact Set.image_nonempty.1 h1
  have hcard := ncard_rootKernel_of_image hw₀
  rw [ncard_parabolicRoots_supportA2A2] at hcard
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, hline, -, -, hA2'⟩ := h8 p hp3 _ hr
  obtain ⟨k, hk⟩ := (hline a b hab0).1 hne
  have hk4 : k.val < 4 := by
    by_contra h
    obtain ⟨w', hw', -⟩ := hA2' k (by omega)
    have := (hw' a b hab0 hk).2
    omega
  refine ⟨k, hk4, ?_⟩
  obtain ⟨m, hma, hmb⟩ := exists_eq_mul_eisLinePoint hk
  refine Subgroup.mem_zpowers_iff.2 ⟨(m.val : ℤ), ?_⟩
  rw [phi3TorsionHom_zpow, Int.cast_natCast, ZMod.natCast_zmod_val, ← hma, ← hmb]
  exact hab

section Node

variable {K : Type} [Field K] {σ : K →+* K} [Algebra K Ω]

theorem phi3_torus_layer [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) :
    7 ≤ p ∧
    (∀ y : Fin Tag.E6.rank → ℤ, phi3V • y = -(e6CoxeterSq • permLattice e6Rho y)) ∧
    (∃ g' ∈ adjointGroup Tag.E6 Ω,
      g'⁻¹ * twistE6 Ω Fr g' = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) ∧
    phi3FixedGroup Ω Fr = (phi3Rzero Ω Fr).map (MulAut.conj g⁻¹).toMonoidHom ∧
    Finite (phi3FixedGroup Ω Fr) ∧
    ⁅phi3FixedGroup Ω Fr, phi3FixedGroup Ω Fr⁆ = phi3CStar K σ Ω g ∧
    phi3CStar K σ Ω g ≤ phi3FixedGroup Ω Fr ∧
    ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).Normal ∧
    (∃ k : ℕ, ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).index = 3 ^ k) ∧
    Nat.card (phi3CStar K σ Ω g) = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) ∧
    Nat.card (phi3FixedGroup Ω Fr) =
      (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) ∧
    Nat.card (phi3Torus Ω Fr) = ((ℓ ^ f) ^ 2 + ℓ ^ f + 1) ^ 2 * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) ∧
    Odd (Nat.card (phi3Torus Ω Fr)) ∧
    (∃ S : Sylow p (phi3CStar K σ Ω g),
      ∀ y ∈ S, (y : ModGL Tag.E6 Ω) ∈ phi3TStar K σ Ω Fr g) ∧
    (∀ P : Subgroup (ModGL Tag.E6 Ω), P ≤ phi3C K σ Ω → IsPGroup p P →
      ∃ c ∈ phi3C K σ Ω, P.map (MulAut.conj c).toMonoidHom ≤
        (phi3TStar K σ Ω Fr g).map (MulAut.conj g).toMonoidHom) ∧
    Nonempty (phi3TorusTorsion Ω Fr p ≃* Multiplicative (ZMod p × ZMod p)) ∧
    phi3TorusTorsion Ω Fr p ≤ phi3TStar K σ Ω Fr g := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hfin, hder, hle, hnormal, hidx, hCcard, hRcard, -⟩ :=
    phi3_rational_layer hℓ hf hK hσ hFr hg hgn
  obtain ⟨hsyl, hconj, hTT⟩ := phi3_sylow_layer hℓ hf hK hσ hFr hp hp3 hpq hg hgn
  obtain ⟨hTcard, hTodd⟩ := natCard_phi3Torus hFr hq0
  exact ⟨(phi3_prime_facts hp hp3 hpq).2.2, phi3V_smul,
    exists_inv_mul_twistE6_eq hf hFr (canonicalRep_mem_adjointGroup _ Ω phi3V),
    phi3FixedGroup_eq_map hg hgn, hfin, hder, hle, hnormal, hidx, hCcard, hRcard, hTcard, hTodd,
    hsyl, hconj, nonempty_phi3TorusTorsion_mulEquiv hFr hq0 hp hpq, hTT⟩

theorem phi3_torus_centralizers [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3TStar K σ Ω Fr g) (hxp : orderOf x = p) :
    let Q := rootSpan Tag.E6 Ω (torusRootKernel x)
    let Qθ := Q ⊓ phi3FixedGroup Ω Fr
    let D := phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}
    let P := ⁅Qθ, Qθ⁆
    (torusRootKernel x = ∅ ∨
      (∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) ∧
    (torusRootKernel x = ∅ →
      adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ∧
        D ≤ phi3Torus Ω Fr) ∧
    ((∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) →
      adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ⊔ Q ∧
      P = Qθ ∧ ⁅D, D⁆ = Qθ ∧
      (∃ k : Subfield K, (∀ c, c ∈ k ↔ σ c = c) ∧ Nonempty (↥P ≃* SL(3, k))) ∧
      CFSG.IsQuasisimple ↥P ∧
      Nat.card (Subgroup.center ↥P) = Nat.gcd 3 (ℓ ^ f - 1) ∧
      P ≤ phi3CStar K σ Ω g ∧
      (torusGroup Tag.E6 Ω ⊔ Q) ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤
        torusGroup Tag.E6 Ω ∧
      D ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr) ∧
    ((∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) →
      adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ⊔ Q ∧
      (∃ k₂ : Subfield Ω, (∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
        ∃ ψ : SL(3, k₂) →* ModGL Tag.E6 Ω, ψ.range = P ∧
          (∀ A : SL(3, k₂), ψ A = 1 ↔ ∃ c : k₂, c ^ 3 = 1 ∧ c ^ (ℓ ^ f + 1) = 1 ∧
            (A : Matrix (Fin 3) (Fin 3) k₂) = scalar (Fin 3) c) ∧
          Nat.card ψ.ker = Nat.gcd 3 (ℓ ^ f + 1) ∧ Nonempty (SL(3, k₂) ⧸ ψ.ker ≃* ↥P)) ∧
      (∀ a ∈ Qθ, ∀ b ∈ Qθ, a * b * a⁻¹ * b⁻¹ ∈ P) ∧
      P.relIndex Qθ ∣ Nat.gcd 3 (ℓ ^ f + 1) ∧
      Nat.card (Subgroup.center ↥P) = Nat.gcd 3 ((ℓ ^ f) ^ 2 - 1) / Nat.gcd 3 (ℓ ^ f + 1) ∧
      CFSG.IsQuasisimple ↥P ∧ P ≤ phi3CStar K σ Ω g ∧
      (CFSG.perfectResidual ↥D).map D.subtype = P ∧
      (torusGroup Tag.E6 Ω ⊔ Q) ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤
        torusGroup Tag.E6 Ω ∧
      D ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr) ∧
    ∀ V : Subgroup ↥D, V.Normal → Group.IsSolvable V → Odd (Nat.card V) := by
  intro Q Qθ D P
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  obtain ⟨hfin, -, hCR, -, -, -, -, -⟩ := phi3_rational_layer hℓ hf hK hσ hFr hg hgn
  have hp7 := (phi3_prime_facts hp hp3 hpq).2.2
  have hxT0 : x ∈ phi3Torus Ω Fr := hx.1
  have hxH : x ∈ torusGroup Tag.E6 Ω := hxT0.1
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi3TorusTorsion Ω Fr p := ⟨hxT0, hxp'⟩
  have hCG : adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ⊔ Q :=
    centralizer_eq_sup_of_pow_eq_one (by omega : 5 < p) hpΩ hxH hxp'
  have hTodd := (natCard_phi3Torus hFr hq0).2
  have htri : torusRootKernel x = ∅ ∨
      (∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2 := by
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi3TorusTorsion_iff hFr hζ hr x).1 hxT
    have hab0 : (a, b) ≠ 0 := fun h => hx1 (by rw [← hab, h, ofAdd_zero, map_one])
    rw [← hab, torusRootKernel_phi3TorsionHom hζ _ a b]
    exact rootKernel_eisenstein_trichotomy hp3 hr hab0
  have hreg : torusRootKernel x = ∅ →
      adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ∧
        D ≤ phi3Torus Ω Fr := fun h =>
    centralizer_of_torusRootKernel_eq_empty (by omega) hpΩ hCR hx hxp' h
  have hA2 := fun h => phi3_A2_case hℓ hf hK hσ hFr hp hp3 hpq hg hgn hx hxp h
  have hA2A2 := fun h => phi3_A2A2_case hℓ hf hK hσ hFr hp hp3 hpq hg hgn hx hxp h
  have hA2' : (∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) →
      P = Qθ ∧ ⁅D, D⁆ = Qθ ∧
      (∃ k : Subfield K, (∀ c, c ∈ k ↔ σ c = c) ∧ Nonempty (↥P ≃* SL(3, k))) ∧
      CFSG.IsQuasisimple ↥P ∧
      Nat.card (Subgroup.center ↥P) = Nat.gcd 3 (ℓ ^ f - 1) ∧
      P ≤ phi3CStar K σ Ω g ∧
      (torusGroup Tag.E6 Ω ⊔ Q) ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤
        torusGroup Tag.E6 Ω ∧
      D ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr := by
    intro h
    obtain ⟨hk, hqs, hcen, hPC, hDD, hC6, hC⟩ := hA2 h
    have : Group.IsPerfect ↥Qθ := hqs.1
    have hPQ : P = Qθ := Subgroup.commutator_eq_self
    rw [hPQ]
    exact ⟨rfl, hDD, hk, hqs, hcen, hPC, hC6, hC⟩
  have hDR : D ≤ phi3FixedGroup Ω Fr := inf_le_left.trans hCR
  have : Finite D := Finite.of_injective (Subgroup.inclusion hDR)
    (Subgroup.inclusion_injective hDR)
  refine ⟨htri, hreg, fun h => ⟨hCG, hA2' h⟩, fun h => ⟨hCG, hA2A2 h⟩, fun V hVn hV => ?_⟩
  have := hVn
  rcases htri with h0 | h1 | h2
  · exact odd_natCard_of_le_of_odd (hreg h0).2 hTodd V
  · obtain ⟨-, hqs, -, -, hDD, -, hC⟩ := hA2 h1
    have hDD' : ⁅D, D⁆ = Qθ := hDD
    have hPD : Qθ ≤ D := hDD' ▸ commutator_le_self' D
    have hPn : (Qθ.subgroupOf D).Normal := hDD' ▸ commutator_subgroupOf_normal D
    exact odd_natCard_of_isSolvable_normal_of_centralizer_le hPD hPn hqs hC hTodd V hV
  · obtain ⟨-, -, -, -, hqs, -, hres, -, hC⟩ := hA2A2 h2
    have hres' : (CFSG.perfectResidual ↥D).map D.subtype = P := hres
    have hPD : P ≤ D := by
      rw [← hres']
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hPn : (P.subgroupOf D).Normal := hres' ▸ map_perfectResidual_subgroupOf_normal D
    exact odd_natCard_of_isSolvable_normal_of_centralizer_le hPD hPn hqs hC hTodd V hV

theorem phi3_torus_planes [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (g : ModGL Tag.E6 Ω) :
    (∀ E : Subgroup (ModGL Tag.E6 Ω), E ≤ phi3TStar K σ Ω Fr g → (∀ y ∈ E, y ^ p = 1) →
      Nat.card E = p ^ 2 → E = phi3TorusTorsion Ω Fr p) ∧
    ∃ L : Fin 4 → Subgroup (ModGL Tag.E6 Ω),
      (∀ k, L k ≤ phi3TorusTorsion Ω Fr p ∧ Nat.card (L k) = p ∧
        ∀ y ∈ L k, y ≠ 1 → ∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) ∧
      (∀ k k', k ≠ k' → L k ⊓ L k' = ⊥) ∧
      (∀ y ∈ phi3TorusTorsion Ω Fr p, y ≠ 1 → (∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) → ∃ k, y ∈ L k) ∧
      ∀ E : Subgroup (ModGL Tag.E6 Ω), E ≤ phi3TStar K σ Ω Fr g → (∀ y ∈ E, y ^ p = 1) →
        Nat.card E = p ^ 2 → ∀ k, ∃ y ∈ E, y ∈ L k ∧ y ≠ 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨-, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  have hTc := natCard_phi3TorusTorsion hFr hq0 hp hpq
  have : Finite (phi3TorusTorsion Ω Fr p) := Nat.finite_of_card_ne_zero (by
    rw [hTc]
    exact pow_ne_zero _ hp.ne_zero)
  have hplane : ∀ E : Subgroup (ModGL Tag.E6 Ω), E ≤ phi3TStar K σ Ω Fr g →
      (∀ y ∈ E, y ^ p = 1) → Nat.card E = p ^ 2 → E = phi3TorusTorsion Ω Fr p :=
    fun E hE hEp hEc => eq_phi3TorusTorsion hTc hE hEp hEc
  have hspec := fun k : Fin 4 => phi3Line_spec (Fr := Fr) hp3 hFr hζ hr
    (Fin.castLE (by norm_num) k)
  refine ⟨hplane, fun k => phi3Line ζ hζ.pow_eq_one (-((ℓ ^ f : ℕ) : ZMod p))
      (Fin.castLE (by norm_num) k),
    fun k => ⟨(hspec k).1, (hspec k).2.1, fun y hy hy1 =>
      phi3Line_twoA2 hp3 hFr hζ hr (k := Fin.castLE (by norm_num) k) k.isLt hy hy1⟩,
    fun k k' hkk' => (hspec k).2.2.2 _ fun h => hkk' (Fin.castLE_injective _ h),
    fun y hy hy1 hA2A2 => ?_, fun E hE hEp hEc k => ?_⟩
  · obtain ⟨k, hk4, hyk⟩ := exists_mem_phi3Line_of_twoA2 hp3 hFr hζ hr hy hy1 hA2A2
    exact ⟨⟨k.val, hk4⟩, hyk⟩
  · rw [hplane E hE hEp hEc]
    rcases Subgroup.bot_or_exists_ne_one (phi3Line ζ hζ.pow_eq_one (-((ℓ ^ f : ℕ) : ZMod p))
      (Fin.castLE (by norm_num) k)) with h | ⟨y, hy, hy1⟩
    · exfalso
      have h1 := (hspec k).2.1
      rw [h, Subgroup.card_bot] at h1
      exact hp.one_lt.ne h1
    · exact ⟨y, (hspec k).1 hy, hy, hy1⟩

theorem twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
    [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) :
    (7 ≤ p ∧
      (∀ y : Fin Tag.E6.rank → ℤ, phi3V • y = -(e6CoxeterSq • permLattice e6Rho y)) ∧
      (∃ g' ∈ adjointGroup Tag.E6 Ω,
        g'⁻¹ * twistE6 Ω Fr g' = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) ∧
      phi3FixedGroup Ω Fr = (phi3Rzero Ω Fr).map (MulAut.conj g⁻¹).toMonoidHom ∧
      Finite (phi3FixedGroup Ω Fr) ∧
      ⁅phi3FixedGroup Ω Fr, phi3FixedGroup Ω Fr⁆ = phi3CStar K σ Ω g ∧
      phi3CStar K σ Ω g ≤ phi3FixedGroup Ω Fr ∧
      ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).Normal ∧
      (∃ k : ℕ, ((phi3CStar K σ Ω g).subgroupOf (phi3FixedGroup Ω Fr)).index = 3 ^ k) ∧
      Nat.card (phi3CStar K σ Ω g) = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) ∧
      Nat.card (phi3FixedGroup Ω Fr) =
        (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
          ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) ∧
      Nat.card (phi3Torus Ω Fr) = ((ℓ ^ f) ^ 2 + ℓ ^ f + 1) ^ 2 * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) ∧
      Odd (Nat.card (phi3Torus Ω Fr)) ∧
      (∃ S : Sylow p (phi3CStar K σ Ω g),
        ∀ y ∈ S, (y : ModGL Tag.E6 Ω) ∈ phi3TStar K σ Ω Fr g) ∧
      (∀ P : Subgroup (ModGL Tag.E6 Ω), P ≤ phi3C K σ Ω → IsPGroup p P →
        ∃ c ∈ phi3C K σ Ω, P.map (MulAut.conj c).toMonoidHom ≤
          (phi3TStar K σ Ω Fr g).map (MulAut.conj g).toMonoidHom) ∧
      Nonempty (phi3TorusTorsion Ω Fr p ≃* Multiplicative (ZMod p × ZMod p)) ∧
      phi3TorusTorsion Ω Fr p ≤ phi3TStar K σ Ω Fr g) ∧
    (∀ x ∈ phi3TStar K σ Ω Fr g, orderOf x = p →
      let Q := rootSpan Tag.E6 Ω (torusRootKernel x)
      let Qθ := Q ⊓ phi3FixedGroup Ω Fr
      let D := phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}
      let P := ⁅Qθ, Qθ⁆
      (torusRootKernel x = ∅ ∨
        (∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) ∨
        ∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) ∧
      (torusRootKernel x = ∅ →
        adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ∧
          D ≤ phi3Torus Ω Fr) ∧
      ((∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) →
        adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ⊔ Q ∧
        P = Qθ ∧ ⁅D, D⁆ = Qθ ∧
        (∃ k : Subfield K, (∀ c, c ∈ k ↔ σ c = c) ∧ Nonempty (↥P ≃* SL(3, k))) ∧
        CFSG.IsQuasisimple ↥P ∧
        Nat.card (Subgroup.center ↥P) = Nat.gcd 3 (ℓ ^ f - 1) ∧
        P ≤ phi3CStar K σ Ω g ∧
        (torusGroup Tag.E6 Ω ⊔ Q) ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤
          torusGroup Tag.E6 Ω ∧
        D ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr) ∧
      ((∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) →
        adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ⊔ Q ∧
        (∃ k₂ : Subfield Ω, (∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
          ∃ ψ : SL(3, k₂) →* ModGL Tag.E6 Ω, ψ.range = P ∧
            (∀ A : SL(3, k₂), ψ A = 1 ↔ ∃ c : k₂, c ^ 3 = 1 ∧ c ^ (ℓ ^ f + 1) = 1 ∧
              (A : Matrix (Fin 3) (Fin 3) k₂) = scalar (Fin 3) c) ∧
            Nat.card ψ.ker = Nat.gcd 3 (ℓ ^ f + 1) ∧ Nonempty (SL(3, k₂) ⧸ ψ.ker ≃* ↥P)) ∧
        (∀ a ∈ Qθ, ∀ b ∈ Qθ, a * b * a⁻¹ * b⁻¹ ∈ P) ∧
        P.relIndex Qθ ∣ Nat.gcd 3 (ℓ ^ f + 1) ∧
        Nat.card (Subgroup.center ↥P) = Nat.gcd 3 ((ℓ ^ f) ^ 2 - 1) / Nat.gcd 3 (ℓ ^ f + 1) ∧
        CFSG.IsQuasisimple ↥P ∧ P ≤ phi3CStar K σ Ω g ∧
        (CFSG.perfectResidual ↥D).map D.subtype = P ∧
        (torusGroup Tag.E6 Ω ⊔ Q) ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤
          torusGroup Tag.E6 Ω ∧
        D ⊓ Subgroup.centralizer (P : Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr) ∧
      ∀ V : Subgroup ↥D, V.Normal → Group.IsSolvable V → Odd (Nat.card V)) ∧
    (∀ E : Subgroup (ModGL Tag.E6 Ω), E ≤ phi3TStar K σ Ω Fr g → (∀ y ∈ E, y ^ p = 1) →
      Nat.card E = p ^ 2 → E = phi3TorusTorsion Ω Fr p) ∧
    ∃ L : Fin 4 → Subgroup (ModGL Tag.E6 Ω),
      (∀ k, L k ≤ phi3TorusTorsion Ω Fr p ∧ Nat.card (L k) = p ∧
        ∀ y ∈ L k, y ≠ 1 → ∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) ∧
      (∀ k k', k ≠ k' → L k ⊓ L k' = ⊥) ∧
      (∀ y ∈ phi3TorusTorsion Ω Fr p, y ≠ 1 → (∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) → ∃ k, y ∈ L k) ∧
      ∀ E : Subgroup (ModGL Tag.E6 Ω), E ≤ phi3TStar K σ Ω Fr g → (∀ y ∈ E, y ^ p = 1) →
        Nat.card E = p ^ 2 → ∀ k, ∃ y ∈ E, y ∈ L k ∧ y ≠ 1 :=
  ⟨phi3_torus_layer hℓ hf hK hσ hFr hp hp3 hpq hg hgn,
    fun _ hx hxp => phi3_torus_centralizers hℓ hf hK hσ hFr hp hp3 hpq hg hgn hx hxp,
    phi3_torus_planes hℓ hf hK hFr hp hp3 hpq g⟩

end Node

end CFSG.RankThree.Classical2
