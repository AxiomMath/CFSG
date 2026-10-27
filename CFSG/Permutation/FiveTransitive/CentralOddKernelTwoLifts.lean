module

public import CFSG.Permutation.FiveTransitive.OddKernelEqualImageConjugacy
public import CFSG.Permutation.FiveTransitive.EvenSixInvolutionConjugacy

public section

namespace CFSG

namespace FiveTransitive.CentralOddKernelTwoLifts

private theorem square_eq_one_of_odd_kernel
    {G A : Type*} [Group G] [Finite G] [Group A]
    (f : G →* A) (hodd : Odd (Nat.card f.ker))
    (x : G) (k : ℕ) (hx : x ^ (2 ^ k) = 1) (hfx : (f x) ^ 2 = 1) :
    x ^ 2 = 1 := by
  let y : f.ker := ⟨x ^ 2, by simpa only [MonoidHom.mem_ker, map_pow] using hfx⟩
  have hy : y ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    change (x ^ 2) ^ (2 ^ k) = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hx, one_pow]
  have hcop : (Nat.card f.ker).Coprime (2 ^ k) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat).symm).pow_right k
  have hord : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_natCard y) (orderOf_dvd_of_pow_eq_one hy)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp hord)

private theorem exists_ker_conjugator_mod_subgroup
    {G A : Type*} [Group G] [Finite G] [Group A]
    (f : G →* A) (Q : Subgroup G) [Q.Normal] (hQ : Q ≤ f.ker)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (x z : G) (k : ℕ) (hx : x ^ (2 ^ k) = 1) (hz : z ^ 2 = 1)
    (heq : f x = f z) (hfz : f z ≠ 1) :
    ∃ c : G, c ∈ f.ker ∧ (c * x * c⁻¹) * z⁻¹ ∈ Q := by
  let pi : G →* G ⧸ Q := QuotientGroup.mk' Q
  let rho : G ⧸ Q →* A := QuotientGroup.lift Q f hQ
  have hodd' : Odd (Nat.card rho.ker) := by
    simpa only [rho, QuotientGroup.ker_lift] using hodd
  have hx' : (pi x) ^ 2 = 1 := square_eq_one_of_odd_kernel rho hodd' (pi x) k
    (by rw [← map_pow, hx, map_one])
    (by change (f x) ^ 2 = 1; rw [heq, ← map_pow, hz, map_one])
  obtain ⟨cbar, hcbar, hc⟩ := OddKernelEqualImageConjugacy.exists_ker_conjugator
    rho hodd' (pi x) (pi z) hx' (by rw [← map_pow, hz, map_one]) heq hfz
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Q cbar
  refine ⟨c, hcbar, ?_⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change pi ((c * x * c⁻¹) * z⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel]

private theorem square_eq_one_of_conjugate_mod_central
    {G : Type*} [Group G] (Q : Subgroup G)
    (hcentral : ∀ q : Q, ∀ g : G, (q : G) * g = g * q)
    (hQsq : ∀ q : Q, q ^ 2 = 1)
    (x z c : G) (hz : z ^ 2 = 1) (hc : (c * x * c⁻¹) * z⁻¹ ∈ Q) :
    x ^ 2 = 1 := by
  let q : Q := ⟨(c * x * c⁻¹) * z⁻¹, hc⟩
  have heq : c * x * c⁻¹ = (q : G) * z := by dsimp [q]; group
  have hq : (q : G) ^ 2 = 1 := congrArg Subtype.val (hQsq q)
  have hcomm : Commute (q : G) z := hcentral q z
  have hs : (c * x * c⁻¹) ^ 2 = 1 := by
    rw [heq, hcomm.mul_pow, hq, hz, one_mul]
  apply (MulAut.conj c).injective
  change c * x ^ 2 * c⁻¹ = c * 1 * c⁻¹
  rw [← conj_pow, hs]
  group

theorem square_eq_one_of_even_six_image
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    (f : G →* Equiv.Perm X) (hX : Fintype.card X = 6)
    (hf : f.range = alternatingGroup X)
    (Q : Subgroup G) [Q.Normal] (hQ : Q ≤ f.ker)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (hcentral : ∀ q : Q, ∀ g : G, (q : G) * g = g * q)
    (hQsq : ∀ q : Q, q ^ 2 = 1)
    (z : G) (hz : z ^ 2 = 1) (hfz : f z ≠ 1)
    (x : G) (k : ℕ) (hx : x ^ (2 ^ k) = 1)
    (hfx : (f x) ^ 2 = 1) (hfxne : f x ≠ 1) : x ^ 2 = 1 := by
  have heven (g : G) : (f g).sign = 1 := by
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← hf]
    exact ⟨g, rfl⟩
  obtain ⟨d, hd, hdeq⟩ := EvenSixInvolutionConjugacy.exists_even_conjugator hX
    (f x) (f z) hfx (by rw [← map_pow, hz, map_one])
    (heven x) (heven z) hfxne hfz
  have hdmem : d ∈ f.range := by rw [hf]; exact Equiv.Perm.mem_alternatingGroup.mpr hd
  obtain ⟨g, hg⟩ := hdmem
  have heq : f (g * x * g⁻¹) = f z := by
    rw [map_mul, map_mul, map_inv, hg]
    exact hdeq
  have hpow : (g * x * g⁻¹) ^ (2 ^ k) = 1 := by rw [conj_pow, hx]; group
  obtain ⟨c, _, hc⟩ := exists_ker_conjugator_mod_subgroup f Q hQ hodd
    (g * x * g⁻¹) z k hpow hz heq hfz
  have hcg : ((c * g) * x * (c * g)⁻¹) * z⁻¹ ∈ Q := by
    have he : ((c * g) * x * (c * g)⁻¹) * z⁻¹ =
        (c * (g * x * g⁻¹) * c⁻¹) * z⁻¹ := by group
    rw [he]
    exact hc
  exact square_eq_one_of_conjugate_mod_central Q hcentral hQsq x z (c * g) hz hcg

end FiveTransitive.CentralOddKernelTwoLifts

end CFSG
