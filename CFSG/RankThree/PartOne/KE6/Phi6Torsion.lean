module

public import CFSG.RankThree.PartOne.KE6.Phi6Torus
public import CFSG.RankThree.Classical2.TwistedE6Phi3Lines

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open scoped Matrix

variable {L : Type} [Field L] {Fr : L →+* L}

@[expose] def phi6TorusTorsion
    (L : Type) [Field L] (Fr : L →+* L) (p : ℕ) : Subgroup (ModGL Tag.E6 L) where
  carrier := {t | t ∈ twistedTorus (phi6N L) Fr ∧ t ^ p = 1}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (torusGroup_E6_comm hx.1.1 hy.1.1) p, hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_phi6TorusTorsion {p : ℕ}
    {t : ModGL Tag.E6 L} :
    t ∈ phi6TorusTorsion L Fr p ↔ t ∈ twistedTorus (phi6N L) Fr ∧ t ^ p = 1 :=
  Iff.rfl

theorem phi6Matrix_transpose_mulVec_eq_zero_iff {p : ℕ} (q : ℕ)
    (z : Fin Tag.E6.rank → ZMod p) :
    ((phi6Matrix q)ᵀ.map (Int.cast : ℤ → ZMod p)) *ᵥ z = 0 ↔
      (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = (q : ZMod p) • z := by
  have hM : (phi6Matrix q)ᵀ.map (Int.cast : ℤ → ZMod p) =
      dualMatrix (ZMod p) e6CoxeterSq - Matrix.scalar (Fin Tag.E6.rank) (q : ZMod p) := by
    rw [dualMatrix_e6CoxeterSq, phi6Matrix, Matrix.transpose_sub, Matrix.map_sub _ Int.cast_sub,
      Matrix.transpose_map]
    congr 1
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_transpose,
      Matrix.diagonal_map Int.cast_zero]
    simp only [Int.cast_natCast]
  rw [hM, Matrix.sub_mulVec, sub_eq_zero]
  have : Matrix.scalar (Fin Tag.E6.rank) (q : ZMod p) *ᵥ z = (q : ZMod p) • z := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this]

theorem phi6_prime_setup [IsAlgClosed L] {q : ℕ} (hq : (q : L) = 0) {p : ℕ} (hp : p.Prime)
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1) :
    (p : L) ≠ 0 ∧ (∃ ζ : Lˣ, IsPrimitiveRoot ζ p) ∧
      ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0 := by
  have hpL : (p : L) ≠ 0 := fun h => by
    obtain ⟨c, hc⟩ := hpq
    have h1 : (((q : ℤ) ^ 2 - (q : ℤ) + 1 : ℤ) : L) = 0 := by rw [hc]; push_cast; rw [h, zero_mul]
    push_cast at h1
    rw [hq] at h1
    norm_num at h1
  refine ⟨hpL, ?_, ?_⟩
  · have : NeZero (p : L) := ⟨hpL⟩
    have := IsSepClosed.hasEnoughRootsOfUnity L p
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
    refine ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp ?_⟩
    rw [IsUnit.unit_spec]
    exact hζ₀
  · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpq
    push_cast at h
    exact h

theorem natCard_phi6TorusTorsion [IsAlgClosed L] {q p : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : L) = 0) (hp : p.Prime)
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1) :
    Nat.card (phi6TorusTorsion L Fr p) = p ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq hp hpq
  set r : ZMod p := (q : ZMod p) with hrdef
  let ψ : {z : Fin Tag.E6.rank → ZMod p // (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = r • z} →
      phi6TorusTorsion L Fr p := fun z =>
    ⟨rootDiagUnit Tag.E6 (fun i => ζ ^ (z.1 i).val),
      ⟨(mem_twistedTorus_rootDiagUnit_iff hFr _).2
          ((zetaPow_mem_ker_monomialHom_iff hζ _ z.1).2
            ((phi6Matrix_transpose_mulVec_eq_zero_iff q z.1).2 z.2)), by
        change (rootDiagUnitHom Tag.E6 L (fun i => ζ ^ (z.1 i).val)) ^ p = 1
        rw [← map_pow]
        change rootDiagUnit Tag.E6 _ = 1
        rw [show ((fun i => ζ ^ (z.1 i).val) ^ p : Fin Tag.E6.rank → Lˣ) = 1 by
          funext i
          rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply],
          rootDiagUnit_one]⟩⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro z w h
      have h1 := rootDiagUnit_injective (congrArg Subtype.val h)
      apply Subtype.ext
      funext i
      have h2 := congrFun h1 i
      exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)
    · intro t
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup t.2.1.1
      have hbker : b ∈ (monomialHom (G := Lˣ) (phi6Matrix q)ᵀ).ker :=
        (mem_twistedTorus_rootDiagUnit_iff hFr b).1 (by rw [← hb]; exact t.2.1)
      have hbp : ∀ i, b i ^ p = 1 := by
        have h1 : rootDiagUnit Tag.E6 (b ^ p) = rootDiagUnit Tag.E6 1 := by
          rw [rootDiagUnit_one]
          change rootDiagUnitHom Tag.E6 L (b ^ p) = 1
          rw [map_pow]
          change rootDiagUnit Tag.E6 b ^ p = 1
          rw [← hb]
          exact t.2.2
        intro i
        exact congrFun (rootDiagUnit_injective h1) i
      have hmem : ∀ i, ∃ m : ℤ, ζ ^ m = b i := fun i => by
        have : b i ∈ rootsOfUnity p L := (mem_rootsOfUnity p (b i)).mpr (hbp i)
        rw [← hζ.zpowers_eq] at this
        obtain ⟨m, hm⟩ := this
        exact ⟨m, hm⟩
      choose m hm using hmem
      set z : Fin Tag.E6.rank → ZMod p := fun i => (m i : ZMod p) with hz
      have hzb : (fun i => ζ ^ (z i).val) = b := by
        funext i
        have h1 := zpow_mod_orderOf ζ (m i)
        rw [← hζ.eq_orderOf] at h1
        rw [← hm i, ← zpow_natCast, hz, ZMod.val_intCast, h1]
      have hzc : (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = r • z := by
        rw [← phi6Matrix_transpose_mulVec_eq_zero_iff q z,
          ← zetaPow_mem_ker_monomialHom_iff hζ, hzb]
        exact hbker
      refine ⟨⟨z, hzc⟩, Subtype.ext ?_⟩
      change rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val) = t
      rw [hzb, hb]
  rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), ← Nat.card_congr (eisensteinEquiv hr),
    Nat.card_prod, Nat.card_zmod, sq]

theorem exists_eq_rootDiagUnit_eisenstein [IsAlgClosed L] {q p : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) [NeZero p] {x : ModGL Tag.E6 L}
    (hx : x ∈ phi6TorusTorsion L Fr p) (hr : ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    ∃ a b : ZMod p,
      x = rootDiagUnit Tag.E6 (fun i => ζ ^ (eisensteinColumn (q : ZMod p) a b i).val) := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.1.1
  have hbker : b ∈ (monomialHom (G := Lˣ) (phi6Matrix q)ᵀ).ker :=
    (mem_twistedTorus_rootDiagUnit_iff hFr b).1 (by rw [← hb]; exact hx.1)
  obtain ⟨z, hz⟩ := exists_eq_rootDiagUnit_zetaPow hζ hx.1.1 hx.2
  have hbz : b = fun i => ζ ^ (z i).val := rootDiagUnit_injective (hb.symm.trans hz)
  have hzc : (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = (q : ZMod p) • z := by
    rw [← phi6Matrix_transpose_mulVec_eq_zero_iff q z, ← zetaPow_mem_ker_monomialHom_iff hζ,
      ← hbz]
    exact hbker
  refine ⟨z (e6Index 4), z (e6Index 5), ?_⟩
  rw [← eq_eisensteinColumn_of_dualMatrix_mulVec hr hzc, hz]

theorem mem_phi6TorusTorsion_iff [IsAlgClosed L] {q p : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) [NeZero p]
    (hr : ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) (x : ModGL Tag.E6 L) :
    x ∈ phi6TorusTorsion L Fr p ↔
      ∃ ab : ZMod p × ZMod p,
        phi3TorsionHom ζ hζ.pow_eq_one (q : ZMod p) (Multiplicative.ofAdd ab) = x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := exists_eq_rootDiagUnit_eisenstein hFr hζ hx hr
    exact ⟨(a, b), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨(mem_twistedTorus_rootDiagUnit_iff hFr _).2
        ((zetaPow_mem_ker_monomialHom_iff hζ _ _).2
          ((phi6Matrix_transpose_mulVec_eq_zero_iff q _).2
            (dualMatrix_mulVec_eisensteinColumn hr a b))), ?_⟩
    rw [← map_pow, ← ofAdd_nsmul]
    have : p • (a, b) = (0 : ZMod p × ZMod p) := by
      rw [Prod.smul_mk, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, zero_mul]
      rfl
    rw [this, ofAdd_zero, map_one]

theorem exists_twoA2_mem_phi6TorusTorsion [IsAlgClosed L] {q p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    ∃ t ∈ phi6TorusTorsion L Fr p, t ≠ 1 ∧ ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel t = parabolicRoots Tag.E6 supportA2A2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set r : ZMod p := (q : ZMod p)
  set t : ModGL Tag.E6 L :=
    phi3TorsionHom ζ hζ.pow_eq_one r (Multiplicative.ofAdd (eisLinePoint r 0)) with htdef
  have ht : t ∈ phi6TorusTorsion L Fr p := (mem_phi6TorusTorsion_iff hFr hζ hr t).2 ⟨_, rfl⟩
  have ht1 : t ≠ 1 := fun h => by
    rw [← map_one (phi3TorsionHom ζ hζ.pow_eq_one r)] at h
    exact eisLinePoint_ne_zero r 0 (Multiplicative.ofAdd.injective
      (phi3TorsionHom_injective hζ r h))
  refine ⟨t, ht, ht1, ?_⟩
  obtain ⟨-, -, -, -, h⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, -, -, hA2A2, -⟩ := h p hp3 r hr
  obtain ⟨w, hw, -⟩ := hA2A2 0 (by decide)
  refine ⟨w, ?_⟩
  have hker : torusRootKernel t = rootKernel (eisensteinColumn r (eisLinePoint r 0).1
      (eisLinePoint r 0).2) :=
    torusRootKernel_phi3TorsionHom hζ r (eisLinePoint r 0).1 (eisLinePoint r 0).2
  have hab : ((eisLinePoint r 0).1, (eisLinePoint r 0).2) ≠ 0 := eisLinePoint_ne_zero r 0
  rw [hker]
  exact (hw _ _ hab (eisensteinLineForm_eisLinePoint r 0)).1

end CFSG.RankThree.PartOne.KE6
