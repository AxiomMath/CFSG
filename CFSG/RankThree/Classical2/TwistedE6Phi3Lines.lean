module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Sylow
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

section Hom

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem pow_mod_eq_of_pow_eq_one {M : Type*} [Monoid M] {ζ : M} (hζ : ζ ^ p = 1) (n : ℕ) :
    ζ ^ (n % p) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hζ, one_pow, mul_one]

@[expose] def phi3TorsionHom (ζ : Ωˣ) (hζ : ζ ^ p = 1) (r : ZMod p) :
    Multiplicative (ZMod p × ZMod p) →* ModGL Tag.E6 Ω where
  toFun x := rootDiagUnit Tag.E6
    (fun i => ζ ^ (eisensteinColumn r (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 i).val)
  map_one' := by
    change rootDiagUnit Tag.E6 (fun i => ζ ^ (eisensteinColumn r 0 0 i).val) = 1
    rw [eisensteinColumn_zero]
    simp only [Pi.zero_apply, ZMod.val_zero, pow_zero]
    exact rootDiagUnit_one
  map_mul' x y := by
    change rootDiagUnit Tag.E6 (fun i => ζ ^ (eisensteinColumn r
        (Multiplicative.toAdd x + Multiplicative.toAdd y).1
        (Multiplicative.toAdd x + Multiplicative.toAdd y).2 i).val) = _
    rw [← rootDiagUnit_mul]
    congr 1
    funext i
    simp only [Prod.fst_add, Prod.snd_add, eisensteinColumn_add, Pi.add_apply, Pi.mul_apply,
      ZMod.val_add, pow_mod_eq_of_pow_eq_one hζ, pow_add]

theorem phi3TorsionHom_apply (ζ : Ωˣ) (hζ : ζ ^ p = 1) (r : ZMod p) (a b : ZMod p) :
    phi3TorsionHom ζ hζ r (Multiplicative.ofAdd (a, b)) =
      rootDiagUnit Tag.E6 (fun i => ζ ^ (eisensteinColumn r a b i).val) :=
  rfl

theorem phi3TorsionHom_injective {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p) (r : ZMod p) :
    Function.Injective (phi3TorsionHom ζ hζ.pow_eq_one r) := by
  intro x y hxy
  have h1 := rootDiagUnit_injective hxy
  have h2 : ∀ i, eisensteinColumn r (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 i =
      eisensteinColumn r (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2 i := fun i =>
    ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (congrFun h1 i))
  have h4 := h2 (e6Index 4)
  have h5 := h2 (e6Index 5)
  rw [eisensteinColumn_four, eisensteinColumn_four] at h4
  rw [eisensteinColumn_five, eisensteinColumn_five] at h5
  exact Multiplicative.toAdd.injective (Prod.ext h4 h5)

theorem torusRootKernel_phi3TorsionHom {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p) (r a b : ZMod p) :
    torusRootKernel (phi3TorsionHom ζ hζ.pow_eq_one r (Multiplicative.ofAdd (a, b))) =
      rootKernel (eisensteinColumn r a b) := by
  rw [phi3TorsionHom_apply, torusRootKernel_rootDiagUnit,
    rootCharKernel_zetaPow hζ (eisensteinColumn r a b)]

end Hom

section Torsion

variable [IsAlgClosed Ω] {q p : ℕ} [NeZero p]

theorem mem_phi3TorusTorsion_iff (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) (x : ModGL Tag.E6 Ω) :
    x ∈ phi3TorusTorsion Ω Fr p ↔
      ∃ ab : ZMod p × ZMod p,
        phi3TorsionHom ζ hζ.pow_eq_one (-(q : ZMod p)) (Multiplicative.ofAdd ab) = x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := exists_eq_rootDiagUnit_eisenstein hFr hζ hx hr
    exact ⟨(a, b), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨⟨rootDiagUnit_mem_torusGroup _,
      torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup _),
      (phi3Theta_rootDiagUnit_eq_iff hFr _).mpr
        ((zetaPow_mem_ker_monomialHom_iff hζ _ _).mpr
          ((phi3Matrix_transpose_mulVec_eq_zero_iff q _).mpr
            (dualMatrix_mulVec_eisensteinColumn hr a b)))⟩, ?_⟩
    rw [← map_pow, ← ofAdd_nsmul]
    have : p • (a, b) = (0 : ZMod p × ZMod p) := by
      rw [Prod.smul_mk, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, zero_mul]
      rfl
    rw [this, ofAdd_zero, map_one]

@[expose] def phi3Line (ζ : Ωˣ) (hζ : ζ ^ p = 1) (r : ZMod p) (k : Fin 8) :
    Subgroup (ModGL Tag.E6 Ω) :=
  Subgroup.zpowers (phi3TorsionHom ζ hζ r (Multiplicative.ofAdd (eisLinePoint r k)))

theorem eisensteinLineForm_smul {R : Type*} [CommRing R] (r m a b : R) (k : Fin 8) :
    eisensteinLineForm r (m * a) (m * b) k = m * eisensteinLineForm r a b k := by
  rw [eisensteinLineForm_eq, eisensteinLineForm_eq]
  ring

omit [IsAlgClosed Ω] in
theorem phi3TorsionHom_zpow (ζ : Ωˣ) (hζ : ζ ^ p = 1) (r : ZMod p) (P : ZMod p × ZMod p)
    (m : ℤ) : phi3TorsionHom ζ hζ r (Multiplicative.ofAdd P) ^ m =
      phi3TorsionHom ζ hζ r (Multiplicative.ofAdd ((m : ZMod p) * P.1, (m : ZMod p) * P.2)) := by
  rw [← map_zpow, ← ofAdd_zsmul]
  congr 2
  rw [Prod.smul_mk, zsmul_eq_mul, zsmul_eq_mul]

theorem phi3Line_spec [Fact p.Prime] (hp3 : 3 < p) (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0)
    (k : Fin 8) :
    phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k ≤ phi3TorusTorsion Ω Fr p ∧
    Nat.card (phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k) = p ∧
    (∀ y ∈ phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k, y ≠ 1 →
      ∃ ab : ZMod p × ZMod p, ab ≠ 0 ∧
        eisensteinLineForm (-(q : ZMod p)) ab.1 ab.2 k = 0 ∧
        torusRootKernel y = rootKernel (eisensteinColumn (-(q : ZMod p)) ab.1 ab.2)) ∧
    ∀ k' : Fin 8, k ≠ k' →
      phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k ⊓ phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k' =
        ⊥ := by
  set r : ZMod p := -(q : ZMod p)
  set ψ := phi3TorsionHom ζ hζ.pow_eq_one r
  have hpt : ∀ k : Fin 8, ψ (Multiplicative.ofAdd (eisLinePoint r k)) ∈ phi3TorusTorsion Ω Fr p :=
    fun k => (mem_phi3TorusTorsion_iff hFr hζ hr _).2 ⟨_, rfl⟩
  have hg1 : ∀ k : Fin 8, ψ (Multiplicative.ofAdd (eisLinePoint r k)) ≠ 1 := fun k h => by
    rw [← map_one ψ] at h
    exact eisLinePoint_ne_zero r k (Multiplicative.ofAdd.injective
      (phi3TorsionHom_injective hζ r h))
  have hmem : ∀ k : Fin 8, ∀ y ∈ phi3Line ζ hζ.pow_eq_one r k,
      ∃ ab : ZMod p × ZMod p, eisensteinLineForm r ab.1 ab.2 k = 0 ∧
        ψ (Multiplicative.ofAdd ab) = y := fun k y hy => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨((m : ZMod p) * (eisLinePoint r k).1, (m : ZMod p) * (eisLinePoint r k).2), ?_,
      (phi3TorsionHom_zpow ζ hζ.pow_eq_one r _ m).symm⟩
    rw [eisensteinLineForm_smul, eisensteinLineForm_eisLinePoint, mul_zero]
  refine ⟨Subgroup.zpowers_le.2 (hpt k), ?_, fun y hy hy1 => ?_, fun k' hkk' => ?_⟩
  · rw [phi3Line, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ (hg1 k)
    exact (hpt k).2
  · obtain ⟨ab, hab, rfl⟩ := hmem k y hy
    refine ⟨ab, fun h0 => hy1 (by rw [h0, ofAdd_zero, map_one]), hab, ?_⟩
    exact torusRootKernel_phi3TorsionHom hζ r ab.1 ab.2
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨ab, hab, rfl⟩ := hmem k y hy.1
    obtain ⟨ab', hab', hψ⟩ := hmem k' _ hy.2
    have he : ab' = ab := Multiplicative.ofAdd.injective (phi3TorsionHom_injective hζ r hψ)
    rw [he] at hab'
    by_contra h0
    have hab0 : (ab.1, ab.2) ≠ 0 := fun h => h0 (by
      change ψ (Multiplicative.ofAdd ab) ∈ (⊥ : Subgroup (ModGL Tag.E6 Ω))
      rw [show ab = 0 from h, ofAdd_zero, map_one]
      exact one_mem _)
    exact hkk' (eq_of_eisensteinLineForm_eq_zero hp3 hr hab0 hab hab')

theorem phi3Line_twoA2 [Fact p.Prime] (hp3 : 3 < p) (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0)
    {k : Fin 8} (hk : k.val < 4) {y : ModGL Tag.E6 Ω}
    (hy : y ∈ phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k) (hy1 : y ≠ 1) :
    ∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2 := by
  obtain ⟨-, -, hspec, -⟩ := phi3Line_spec (Fr := Fr) hp3 hFr hζ hr k
  obtain ⟨ab, hab, hline, hker⟩ := hspec y hy hy1
  obtain ⟨-, -, -, -, h⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, -, -, hA2A2, -⟩ := h p hp3 _ hr
  obtain ⟨w, hw, -⟩ := hA2A2 k hk
  refine ⟨w, ?_⟩
  rw [hker]
  exact (hw ab.1 ab.2 hab hline).1

end Torsion

section Planes

variable {K : Type} [Field K] {σ : K →+* K} [Algebra K Ω]

theorem centralizer_of_torusRootKernel_eq_empty [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 < p) (hpΩ : (p : Ω) ≠ 0) {g x : ModGL Tag.E6 Ω}
    (hCs : phi3CStar K σ Ω g ≤ phi3FixedGroup Ω Fr) (hx : x ∈ phi3TStar K σ Ω Fr g)
    (hxp : x ^ p = 1) (hker0 : torusRootKernel x = ∅) :
    adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω ∧
      phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x} ≤ phi3Torus Ω Fr := by
  have hxH : x ∈ torusGroup Tag.E6 Ω := hx.1.1
  have hC : adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} = torusGroup Tag.E6 Ω := by
    rw [centralizer_eq_sup_of_pow_eq_one hp5 hpΩ hxH hxp, hker0]
    have : rootSpan Tag.E6 Ω (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp only [rootSpan, Set.mem_empty_iff_false, iSup_false, iSup_bot]
    rw [this, sup_bot_eq]
  refine ⟨hC, fun y hy => ⟨?_, hCs hy.1⟩⟩
  have hyC : y ∈ adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} :=
    ⟨(hCs hy.1).1, hy.2⟩
  rw [hC] at hyC
  exact hyC

theorem eq_phi3TorusTorsion {p : ℕ} {g : ModGL Tag.E6 Ω} (hT : Nat.card (phi3TorusTorsion Ω Fr p) =
    p ^ 2) [Finite (phi3TorusTorsion Ω Fr p)] {E : Subgroup (ModGL Tag.E6 Ω)}
    (hE : E ≤ phi3TStar K σ Ω Fr g) (hEp : ∀ y ∈ E, y ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    E = phi3TorusTorsion Ω Fr p :=
  Subgroup.eq_of_le_of_card_ge (fun y hy => ⟨(hE hy).1, hEp y hy⟩) (by rw [hT, hEc])

end Planes

section Setup

theorem phi3_prime_setup [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) :
    (p : Ω) ≠ 0 ∧ (∃ ζ : Ωˣ, IsPrimitiveRoot ζ p) ∧
      (-((ℓ ^ f : ℕ) : ZMod p)) ^ 2 - -((ℓ ^ f : ℕ) : ZMod p) + 1 = 0 := by
  have hq0 : ((ℓ : Ω)) ^ f = 0 := by
    rw [CharP.cast_eq_zero, zero_pow (show f ≠ 0 by omega)]
  have hpΩ : (p : Ω) ≠ 0 := fun h => by
    obtain ⟨c, hc⟩ := hpq
    have h1 : (((ℓ ^ f) ^ 2 + ℓ ^ f + 1 : ℕ) : Ω) = 0 := by rw [hc, Nat.cast_mul, h, zero_mul]
    push_cast at h1
    rw [hq0] at h1
    norm_num at h1
  refine ⟨hpΩ, ?_, ?_⟩
  · have : NeZero (p : Ω) := ⟨hpΩ⟩
    have := IsSepClosed.hasEnoughRootsOfUnity Ω p
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
    refine ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp ?_⟩
    rw [IsUnit.unit_spec]
    exact hζ₀
  · have h := (ZMod.natCast_eq_zero_iff _ p).mpr hpq
    push_cast at h ⊢
    linear_combination h

end Setup

end CFSG.RankThree.Classical2
