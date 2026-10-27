module

public import CFSG.RankThree.PartOne.KF4.QPlusFrame
public import CFSG.RankThree.PartOne.KLCE.FrameConj
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.G2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KF4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane (rootChar_neg_vec)

open CFSG.RankThree.PartOne.KE.CTE6
open CFSG.RankThree.PartOne.K128 (sq_sub_one_eq factorization_ordG2)

open CFSG.Timmesfeld.ExceptionalOrders (card_adjointGroup_G2)

open scoped Matrix Polynomial

section Sylow


theorem sigma_untwisted_sylow_G2 (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L ℓ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (n : ModGL .G2 L)
    (hnC : n ∈ adjointGroup .G2 L) (Z : Subgroup (ModGL .G2 L))
    (hZ : Z ≤ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {N : ℕ} (hN : N ≠ 0) (hZcard : Nat.card Z = N)
    (hord : p ^ (Nat.card (adjointGroup .G2 K)).factorization p = p ^ N.factorization p) :
    ∃ g0 : ModGL .G2 L, g0 ∈ adjointGroup .G2 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL .G2 L), Finite P → P ≤ adjointGroup .G2 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .G2 K L).range) ∧
      ∀ Q : Subgroup (adjointGroup .G2 K), IsPGroup p Q →
        ∃ c : adjointGroup .G2 K, ∀ q ∈ Q,
          c * q * c⁻¹ ∈ subtorusImage (adjEmb .G2 K L) g0 Z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL .G2 K) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen .G2 K hf L n hnC
  have hrat3 : ∀ (X : Subgroup (ModGL .G2 L)) [Finite X], X ≤ adjointGroup .G2 L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → (adjEmb .G2 K L).range.relIndex X ∣ 1 ∧
        (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL .G2 L), P ≤ X → IsPGroup p P →
          P ≤ (adjEmb .G2 K L).range) ∧
        ∀ P : Subgroup (ModGL .G2 L), P ≤ X → ⁅P, P⁆ = P → P ≤ (adjEmb .G2 K L).range := by
    intro X _ hXC hXF
    have hXle : X ≤ (adjEmb .G2 K L).range := by
      rw [adjEmb_range]
      intro x hx
      have : Algebra.IsAlgebraic K L := inferInstance
      rw [← (G2_F4_exact_finite_field_fixed_root_matrices Tag.G2 (Or.inl rfl) K L Fr hFr).1]
      exact ⟨hXC hx, hXF x hx⟩
    exact ⟨Nat.dvd_one.2 (Subgroup.relIndex_eq_one.2 hXle),
      fun _ _ _ P hPX _ => hPX.trans hXle, fun P hPX _ => hPX.trans hXle⟩
  have hrat2 : ∀ (X : Subgroup (ModGL .G2 L)) [Finite X], X ≤ adjointGroup .G2 L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → (adjEmb .G2 K L).range.relIndex X ∣ 1 ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL .G2 L), P ≤ X → IsPGroup p P →
          P ≤ (adjEmb .G2 K L).range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (adjEmb .G2 K L) adjEmb_injective
    (Units.map (entrywiseHom Fr)) n g0 hg0C hg0 hp hp3 hN hrat2 Z hZ hZcard hord
  exact ⟨g0, hg0C, hg0, fun P hP hPC hPF hPperf => (hrat3 P hPC hPF).2.2 P le_rfl hPperf, hconj⟩

end Sylow

section Frame

variable {K₀ K L : Type} [Field K₀] [Finite K₀] [Field K] [Finite K] [Field L]
  [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [IsScalarTower K₀ K L] [IsAlgClosure K₀ L]

omit [Finite K] in
theorem frame_conj_G2 [CharP L 2] {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (n₀ : ModGL Tag.G2 L) (hn₀C : n₀ ∈ adjointGroup Tag.G2 L)
    (Z : Subgroup (ModGL Tag.G2 L))
    (hZ : Z ≤ twistedTorusOf n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))))
    {N₀ : ℕ} (hN₀ : N₀ ≠ 0) (hZcard : Nat.card Z = N₀)
    (hord : p ^ (Nat.card (adjointGroup Tag.G2 K₀)).factorization p = p ^ N₀.factorization p) :
    ∃ g₀ : ModGL Tag.G2 L, g₀ ∈ adjointGroup Tag.G2 L ∧
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) g₀ = g₀ * n₀ ∧
      ∀ x : adjointGroup Tag.G2 K, orderOf x = p →
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (adjEmb Tag.G2 K L x) =
          adjEmb Tag.G2 K L x →
        ∃ c : adjointGroup Tag.G2 K,
          Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (adjEmb Tag.G2 K L c) =
            adjEmb Tag.G2 K L c ∧
            c * x * c⁻¹ ∈ subtorusImage (adjEmb Tag.G2 K L) g₀ Z := by
  classical
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : Finite (ModGL Tag.G2 K₀) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : Algebra.IsAlgebraic K₀ L := IsAlgClosure.isAlgebraic
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  have hFr : ∀ c, Φ₀ c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact iterateFrobenius_def 2 f₀ c
  obtain ⟨g₀, hg₀C, hg₀, -, hconj⟩ := sigma_untwisted_sylow_G2 K₀ hf₀ hK₀
    L hp hp3 n₀ hn₀C Z hZ hN₀ hZcard hord
  refine ⟨g₀, hg₀C, hg₀, fun x hx hxfix => ?_⟩
  have hordι : orderOf (adjEmb Tag.G2 K L x) = p := by
    rw [orderOf_injective (adjEmb Tag.G2 K L) adjEmb_injective x, hx]
  have hmem : adjEmb Tag.G2 K L x ∈ (adjEmb Tag.G2 K₀ L).range := by
    rw [adjEmb_range]
    rw [← (G2_F4_exact_finite_field_fixed_root_matrices Tag.G2
      (Or.inl rfl) K₀ L Φ₀ hFr).1]
    exact ⟨adjEmb_mem x, hxfix⟩
  obtain ⟨x₀, hx₀⟩ := hmem
  have hx₀ord : orderOf x₀ = p := by
    rw [← orderOf_injective (adjEmb Tag.G2 K₀ L) adjEmb_injective x₀, hx₀, hordι]
  have hQp : IsPGroup p (Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀ord, pow_one])
  obtain ⟨c₀, hc₀⟩ := hconj _ hQp
  have hc₀x := hc₀ x₀ (Subgroup.mem_zpowers _)
  refine ⟨towerHom Tag.G2 K₀ K c₀, ?_, ?_⟩
  · rw [adjEmb_towerHom]
    exact adjEmb_frobenius Φ₀ hFr c₀
  · rw [mem_subtorusImage_iff] at hc₀x ⊢
    have hxe : adjEmb Tag.G2 K L x = adjEmb Tag.G2 K₀ L x₀ := hx₀.symm
    rw [map_mul, map_mul, map_inv, adjEmb_towerHom, hxe]
    rw [map_mul, map_mul, map_inv] at hc₀x
    exact hc₀x

end Frame

section Torus

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

omit [CharP L 2] [IsAlgClosed L] in
theorem g2_mem_fixedCharTuples_iff {τ : Tag} {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (a : Fin τ.rank → Lˣ) :
    a ∈ fixedCharTuples (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) Fr ↔ ∀ i, a i ^ (q + 1) = 1 := by
  have hmap : ∀ y : Lˣ, Units.map Fr.toMonoidHom y = y ^ q := fun y => by
    apply Units.ext
    simp [hFr]
  rw [mem_fixedCharTuples_iff]
  constructor
  · intro h i
    have := h (Pi.single i 1)
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, rootChar_neg_vec, CTTorus.rootChar_single, hmap]
      at this
    rw [pow_succ]
    rw [← this, inv_mul_cancel]
  · intro h u
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, rootChar_neg_vec, hmap]
    have h1 : rootChar a u ^ (q + 1) = 1 := by
      rw [rootChar, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h i,
        _root_.one_zpow]
    rw [pow_succ] at h1
    exact inv_eq_of_mul_eq_one_left h1

theorem g2_card_fixedCharTuples {τ : Tag} {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : Even q) :
    Nat.card (fixedCharTuples (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) Fr) =
      (q + 1) ^ τ.rank := by
  have hodd : Odd (q + 1) := hq.add_one
  let e : fixedCharTuples (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) Fr ≃
      (Fin τ.rank → rootsOfUnity (q + 1) L) :=
    { toFun := fun a i => ⟨a.1 i, (mem_rootsOfUnity (q + 1) (a.1 i)).2
        ((g2_mem_fixedCharTuples_iff hFr a.1).1 a.2 i)⟩
      invFun := fun z => ⟨fun i => (z i : Lˣ), (g2_mem_fixedCharTuples_iff hFr _).2 fun i =>
        (mem_rootsOfUnity (q + 1) _).1 (z i).2⟩
      left_inv := fun a => rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [qp_card_rootsOfUnity_of_odd (L := L) hodd]

end Torus

section Order


theorem dvd_sq_sub_one_of_dvd_succ {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q + 1) : p ∣ q ^ 2 - 1 := by
  rw [sq_sub_one_eq q hq]
  exact Dvd.dvd.mul_left h _

theorem g2QPlus_ordProj (K₀ : Type) [Field K₀] [Finite K₀] [CharP K₀ 2] {f₀ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ f₀) (hf₀ : 1 ≤ f₀)
    (hΦ : ((Nat.card K₀ : ℕ) : ZMod p) + 1 = 0) :
    p ^ (Nat.card (adjointGroup .G2 K₀)).factorization p =
      p ^ ((Nat.card K₀ + 1) ^ 2).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K₀ := by
    rw [hK₀]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hdvd : p ∣ Nat.card K₀ + 1 := by
    have : ((Nat.card K₀ + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact hΦ
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  have hpq : ¬ p ∣ Nat.card K₀ := by
    rw [hK₀]
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hd : p ∣ Nat.card K₀ ^ 2 - 1 := dvd_sq_sub_one_of_dvd_succ (by omega) hdvd
  have : Finite (Module.End K₀ (RootModule .G2 K₀)) := Module.finite_of_finite K₀
  have hord := factorization_ordG2 hp hp5 hq2 hpq hd
  rw [card_adjointGroup_G2, hord]
  have hq1 : ¬ p ∣ Nat.card K₀ - 1 := by
    intro h1
    have h2 : p ∣ (Nat.card K₀ + 1) - (Nat.card K₀ - 1) := Nat.dvd_sub hdvd h1
    have h3 : (Nat.card K₀ + 1) - (Nat.card K₀ - 1) = 2 := by omega
    rw [h3] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  congr 1
  rw [Nat.factorization_pow, sq_sub_one_eq _ (by omega), Nat.factorization_mul (by omega)
    (by omega)]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.factorization_eq_zero_of_not_dvd hq1]
  ring

end Order

end CFSG.RankThree.PartOne.TCX.G2
