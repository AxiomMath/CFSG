module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem mem_of_pelt {P M : Subgroup G} (hP : IsPGroup p P) (hPM : P ≤ M)
    (hi : Nat.Coprime p (P.relIndex M)) {y : G} (hyM : y ∈ M) (hyN : y ∈ Nor P) {m : ℕ}
    (hy : y ^ (p ^ m) = 1) : y ∈ P := by
  have hz : IsPGroup p (Subgroup.zpowers y) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hy)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) := (Subgroup.zpowers_le).mpr hyN
  have hsup := IsPGroup.to_sup_of_normal_right' hz hP hle
  set H := Subgroup.zpowers y ⊔ P
  have hPH : P ≤ H := le_sup_right
  have hHM : H ≤ M := sup_le ((Subgroup.zpowers_le).mpr hyM) hPM
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hPH hHM
  have h2 : P.relIndex H ∣ Nat.card H := Subgroup.relIndex_dvd_card _ _
  obtain ⟨a, ha⟩ := hsup.exists_card_eq
  rw [ha] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    have : p ∣ P.relIndex M := by
      rw [← h1, hj]
      exact Dvd.dvd.mul_right (dvd_pow_self p hne) _
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp hi this
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))

theorem isSylowOf_mono {P H K : Subgroup G} (h : IsSylowOf p P H) (hPK : P ≤ K) (hKH : K ≤ H) :
    IsSylowOf p P K := by
  refine ⟨hPK, h.2.1, ?_⟩
  have := Subgroup.relIndex_mul_relIndex _ _ _ hPK hKH
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro _ this) h.2.2

theorem mem_nor_of_conjBy {g : G} {P : Subgroup G} (h : conjBy g P = P) : g ∈ Nor P :=
  L41.mem_nor_of_forall fun y hy => by
    rw [← h]; exact ⟨y, hy, rfl⟩

theorem conjBy_eq_of_mem_nor {g : G} {H : Subgroup G} (hg : g ∈ Nor H) : conjBy g H = H := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [L41.card_conjBy])
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy

theorem exists_sylowOf_le {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup p Q) :
    ∃ P : Subgroup G, IsSylowOf p P H ∧ Q ≤ P := by
  obtain ⟨P₀, hP₀⟩ := L41.exists_sylowOf_p (p := p) H
  obtain ⟨k, hk, hkQ⟩ := L41.exists_conj_le_sylowOf_p hP₀ hQH hQ
  refine ⟨conjBy k⁻¹ P₀, ?_, fun x hx => ⟨k * x * k⁻¹, hkQ x hx, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩⟩
  have := L41.isSylowOf_conjBy hP₀ k⁻¹
  rwa [conjBy_eq_of_mem_nor (Subgroup.le_normalizer (H.inv_mem hk))] at this

theorem exists_frattini {T P : Subgroup G} (hP : IsSylowOf p P T) {j : G} (hj : j ∈ Nor T) :
    ∃ k ∈ T, k * j ∈ Nor P := by
  have h1 := L41.isSylowOf_conjBy hP j
  rw [conjBy_eq_of_mem_nor hj] at h1
  obtain ⟨k, hk, hkP⟩ := L41.exists_conjBy_eq_sylowOf hP h1
  refine ⟨k, hk, mem_nor_of_conjBy ?_⟩
  rw [← L41.conjBy_conjBy, hkP]

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
