module

public import CFSG.RankThree.Chevalley.SteinbergBID4WeylCert
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem isRoot_d4RootVec (k : Fin 24) : IsRoot Tag.D4 (d4RootVec k) := by
  obtain ⟨k', hk', h⟩ := d4RootVec_root k
  exact (RootCertificate.isRoot_iff Tag.D4.rootCertificate_check).2 ⟨k', hk', h⟩

theorem exists_mem_d4WeylTab (w : WeylGroup Tag.D4) :
    ∃ e ∈ d4WeylTab, ∀ i, w • (Pi.single i 1 : Fin Tag.D4.rank → ℤ) =
      d4RootVec (d4Dig i (d4TupCode e)) := by
  induction w using (coxeterSystem Tag.D4).simple_induction_left with
  | one =>
    obtain ⟨e, he, hc⟩ := List.mem_map.1 d4TupOne_mem
    exact ⟨e, he, fun i => by rw [one_smul, hc, d4RootVec_d4TupOne]⟩
  | mul_simple_left w j ih =>
    obtain ⟨e, he, hw⟩ := ih
    obtain ⟨e', he', hc⟩ := List.mem_map.1 (d4WeylTab_closed e he j)
    refine ⟨e', he', fun i => ?_⟩
    rw [mul_smul, hw i, simple_smul, d4RootVec_reflect, hc, d4Dig_d4TupRefl e he j i]

theorem smul_eq_sum_smul_single {τ : Tag} (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _

theorem exists_smul_sub_eq_two_smul_root {w : WeylGroup Tag.D4} (hw : w ≠ 1) :
    ∃ v α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α ∧ w • v - v = (2 : ℤ) • α := by
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hne : d4TupCode e ≠ d4TupOne := by
    intro h
    apply hw
    refine ext_single fun i => ?_
    rw [hwe i, h, d4RootVec_d4TupOne, one_smul]
  refine ⟨d4TupLam e, d4RootVec (d4TupRoot e), isRoot_d4RootVec _, ?_⟩
  rw [smul_eq_sum_smul_single, ← d4WeylTab_cert e he hne]
  simp only [hwe]

section Characters

variable {K : Type} [Field K]

theorem pow_eq_one_of_orderOf_rootDiagUnit {τ : Tag} {a : Fin τ.rank → Kˣ} {p : ℕ}
    (hord : orderOf (rootDiagUnit τ a) = p) (i : Fin τ.rank) : a i ^ p = 1 := by
  have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ (1 : Fin τ.rank → Kˣ) := by
    rw [← rootDiagUnit_pow, ← hord, pow_orderOf_eq_one, rootDiagUnit_one]
  have h2 := congrFun (rootDiagUnit_injective h1) i
  rwa [Pi.pow_apply, Pi.one_apply] at h2

theorem rootChar_pow_eq_one {τ : Tag} {a : Fin τ.rank → Kˣ} {p : ℕ}
    (ha : ∀ i, a i ^ p = 1) (v : Fin τ.rank → ℤ) : rootChar a v ^ p = 1 := by
  rw [← rootChar_pow]
  have h : a ^ p = 1 := funext ha
  rw [h]
  simp [rootChar]

theorem eq_one_of_sq_eq_one_of_pow_eq_one {G : Type*} [Group G] {x : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h2 : x ^ 2 = 1) (hpx : x ^ p = 1) : x = 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h1 : orderOf x ∣ Nat.gcd 2 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpx)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem eq_one_of_rootChar_smul {a : Fin Tag.D4.rank → Kˣ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : ∀ i, a i ^ p = 1) (hreg : ∀ α, IsRoot Tag.D4 α → rootChar a α ≠ 1)
    {u : WeylGroup Tag.D4} (hu : ∀ v : Fin Tag.D4.rank → ℤ, rootChar a (u • v) = rootChar a v) :
    u = 1 := by
  by_contra hne
  obtain ⟨v, α, hα, he⟩ := exists_smul_sub_eq_two_smul_root hne
  have h2 : rootChar a α ^ 2 = 1 := by
    have h := rootChar_zsmul a 2 α
    rw [← he, rootChar_sub, hu v, mul_inv_cancel] at h
    rw [← zpow_natCast]
    exact h.symm
  exact hreg α hα (eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 h2 (rootChar_pow_eq_one ha α))

end Characters

theorem D4_odd_prime_regular_root_character_centralizer (K : Type) [Field K] (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (_hpK : ringChar K ≠ p) (a : Fin Tag.D4.rank → Kˣ)
    (hord : orderOf (rootDiagUnit Tag.D4 a) = p)
    (hreg : ∀ α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α → rootChar a α ≠ 1) :
    (∀ u : WeylGroup Tag.D4,
      (∀ v : Fin Tag.D4.rank → ℤ, rootChar a (u • v) = rootChar a v) ↔ u = 1) ∧
    ∀ g : ModGL Tag.D4 K, (g ∈ adjointGroup Tag.D4 K ∧
      rootDiagUnit Tag.D4 a * g * (rootDiagUnit Tag.D4 a)⁻¹ = g) ↔ g ∈ torusGroup Tag.D4 K := by
  have ha := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hstab : ∀ u : WeylGroup Tag.D4,
      (∀ v : Fin Tag.D4.rank → ℤ, rootChar a (u • v) = rootChar a v) ↔ u = 1 := fun u =>
    ⟨eq_one_of_rootChar_smul hp hp2 ha hreg, fun h v => by rw [h, one_smul]⟩
  refine ⟨hstab, fun g => ?_⟩
  have hker : rootCharKernel a = ∅ :=
    Set.eq_empty_of_forall_notMem fun α hα => hreg α hα.1 hα.2
  have hW : rootCharStabilizer a = {1} := by
    ext u
    exact hstab u
  have hX := (Chevalley_toral_centralizer_Bruhat_factors Tag.D4 K a).2.2.2
  rw [hker, hW, Set.image_singleton, canonicalRep_one, Subgroup.closure_singleton_one,
    rootSpan, iSup_emptyset, sup_bot_eq, sup_bot_eq] at hX
  rw [← mem_toralCentralizer, hX]

end CFSG.RankThree.Chevalley
