module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenHyper
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenRow
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Bridge
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative
open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ComponentClassification.CatLeafProof

theorem ggPhiTwoStep_conj_mul_conj {G : Type*} [Group G] (a x y : G) :
    a⁻¹ * ((a * x * a⁻¹) * y) * a = x * (a⁻¹ * y * a) := by group

theorem ggPhiTwoStep_conj_mul_assoc {G : Type*} [Group G] (a x y : G) :
    (a⁻¹ * x * a) * y = a⁻¹ * (x * (a * y * a⁻¹)) * a := by group

theorem ggPhiTwoStep_rootDiagUnit_pow_gen {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (n : ℕ) : rootDiagUnit τ (a ^ n) = rootDiagUnit τ a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, rootDiagUnit_mul, ih, pow_succ]

theorem ggPhiTwoStep_exists_rootDiagUnit_zetaVec_eq_of_pow_eq_one
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L) (hyp : y ^ p = 1) :
    ∃ t : Fin τ.rank → ZMod p, y = rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := τ) hy
  have hl1 : l ^ p = 1 := by
    have h : rootDiagUnit τ (l ^ p) = rootDiagUnit τ (1 : Fin τ.rank → Lˣ) := by
      rw [ggPhiTwoStep_rootDiagUnit_pow_gen, ← hl, hyp, rootDiagUnit_one]
    exact rootDiagUnit_injective h
  obtain ⟨t, ht⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hl1
  exact ⟨t, by rw [hl, ht]⟩

noncomputable def ggPhiTwoStep_linSum (p : ℕ) (α : Fin Tag.E7.rank → ZMod p) :
    (Fin Tag.E7.rank → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun t := ∑ j, α j * t j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem ggPhiTwoStep_card_ker_sum (p : ℕ) [Fact p.Prime]
    (α : Fin Tag.E7.rank → ZMod p) (hα : α ≠ 0) :
    Nat.card {t : Fin Tag.E7.rank → ZMod p // ∑ j, α j * t j = 0} = p ^ 6 := by
  classical
  set f := ggPhiTwoStep_linSum p α with hf
  have hmem : ∀ t : Fin Tag.E7.rank → ZMod p, f t = ∑ j, α j * t j := fun t => rfl
  have hf0 : f ≠ 0 := by
    intro h
    apply hα
    funext j
    have h1 := congrArg (fun g : (Fin Tag.E7.rank → ZMod p) →ₗ[ZMod p] ZMod p =>
      g (Pi.single j 1)) h
    rw [hmem] at h1
    simp only [LinearMap.zero_apply] at h1
    rwa [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun hc => absurd (Finset.mem_univ j) hc), Pi.single_eq_same, mul_one] at h1
  have hne : ∃ x, f x ≠ 0 := by
    by_contra h
    simp only [not_exists] at h
    exact hf0 (LinearMap.ext fun x => by simpa using h x)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := hne
    exact ⟨(z * (f x)⁻¹) • x, by
      rw [LinearMap.map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]⟩
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective (f := f.toAddMonoidHom) hsurj
  have h1 : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have h2 : Nat.card (Fin Tag.E7.rank → ZMod p) = p ^ 7 := by
    rw [Nat.card_fun]
    simp only [Nat.card_zmod, Nat.card_fin]
    rfl
  rw [h1, h2] at hcard
  have h3 : Nat.card {t : Fin Tag.E7.rank → ZMod p // ∑ j, α j * t j = 0}
      = Nat.card f.toAddMonoidHom.ker := Nat.card_congr (Equiv.refl _)
  rw [h3]
  rw [show p ^ 7 = p ^ 6 * p from by ring] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hcard

theorem ggPhiTwoStep_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)

theorem ggPhiTwoStep_theta_zero : e7Theta (0 : Fin Tag.E7.rank) = 2 := by decide

theorem ggPhiTwoStep_sum_single_theta (p : ℕ) (s : ZMod p) :
    ∑ j, (e7Theta j : ZMod p)
        * ((Pi.single (0 : Fin Tag.E7.rank) s : Fin Tag.E7.rank → ZMod p) j)
      = (2 : ZMod p) * s := by
  rw [Finset.sum_eq_single (0 : Fin Tag.E7.rank)]
  · rw [Pi.single_eq_same, ggPhiTwoStep_theta_zero]
    norm_num
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin Tag.E7.rank)) h

theorem ggPhiTwoStep_card_V
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V6 : Subgroup (Multiplicative (Fin Tag.E7.rank → ZMod p))}
    (hV6 : ∀ w : ↥V6, ∑ j, (e7Theta j : ZMod p) *
      (w.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd j = 0)
    (W : Subgroup ↥V6) :
    Nat.card {t : Fin Tag.E7.rank → ZMod p //
      ∃ w : ↥V6, w ∈ W ∧ ∃ s : ZMod p,
        t = (w.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
          + Pi.single (0 : Fin Tag.E7.rank) s} = Nat.card W * p := by
  classical
  have hbij : Function.Bijective
      (fun z : ↥W × ZMod p =>
        (⟨(z.1.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
            + Pi.single (0 : Fin Tag.E7.rank) z.2,
          ⟨z.1.1, z.1.2, z.2, rfl⟩⟩ :
          {t : Fin Tag.E7.rank → ZMod p // ∃ w : ↥V6, w ∈ W ∧ ∃ s : ZMod p,
            t = (w.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
              + Pi.single (0 : Fin Tag.E7.rank) s})) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨w1, hw1⟩, s1⟩ ⟨⟨w2, hw2⟩, s2⟩ heq
      have hvec : (w1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
            + Pi.single (0 : Fin Tag.E7.rank) s1
          = (w2 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
            + Pi.single (0 : Fin Tag.E7.rank) s2 :=
        congrArg Subtype.val heq
      have hf : (2 : ZMod p) * s1 = (2 : ZMod p) * s2 := by
        have h1 : (∑ j, (e7Theta j : ZMod p)
              * ((w1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd j
                + (Pi.single (0 : Fin Tag.E7.rank) s1 : Fin Tag.E7.rank → ZMod p) j))
            = (2 : ZMod p) * s1 := by
          rw [Finset.sum_congr rfl (fun j _ => mul_add _ _ _), Finset.sum_add_distrib,
            hV6 w1, zero_add, ggPhiTwoStep_sum_single_theta p s1]
        have h2 : (∑ j, (e7Theta j : ZMod p)
              * ((w2 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd j
                + (Pi.single (0 : Fin Tag.E7.rank) s2 : Fin Tag.E7.rank → ZMod p) j))
            = (2 : ZMod p) * s2 := by
          rw [Finset.sum_congr rfl (fun j _ => mul_add _ _ _), Finset.sum_add_distrib,
            hV6 w2, zero_add, ggPhiTwoStep_sum_single_theta p s2]
        rw [← h1, ← h2]
        exact congrArg (fun t => ∑ j, (e7Theta j : ZMod p) * t j) hvec
      have hs : s1 = s2 := mul_left_cancel₀ (ggPhiTwoStep_two_ne_zero hp2) hf
      have hw : (⟨w1, hw1⟩ : ↥W) = ⟨w2, hw2⟩ := by
        have hcancel : (w1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
            = (w2 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd := by
          have := hvec
          rw [hs] at this
          exact add_right_cancel this
        exact Subtype.ext (by simpa using hcancel)
      exact Prod.ext hw hs
    · rintro ⟨t, w, hw, s, rfl⟩
      exact ⟨(⟨w, hw⟩, s), Subtype.ext rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, Nat.card_zmod] at hcard
  exact hcard.symm

theorem ggPhiTwoStep_e7D6_le_centralizer_theta
    {K : Type} [Field K] :
    e7D6Group K ≤ Subgroup.centralizer (rootPairE7 K e7Theta : Set (adjointGroup .E7 K)) := by
  unfold e7D6Group
  refine iSup_le fun k => ?_
  intro y hy x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
  exact commutes_rootPair_of_noG2 (K := K) CFSG.LieType.Steinberg.Adjoint.noG2_E7
    isRoot_e7Theta (isRoot_single .E7 (e7D6Node k)) h1 h2 h3 h4 h5 x hx y hy

end CFSG.StandardType.PhiTwoRootGen

end
