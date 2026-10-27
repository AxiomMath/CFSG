module

public import CFSG.RankThree.PartOne.FOC.ComponentFact
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG

section Lift

variable {S : Type} [Group S] (Zc : Subgroup S) [Zc.Normal]

omit [Zc.Normal] in
theorem eq_one_of_pow_eq_one_of_not_dvd_card {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card Zc)
    {z : S} (hz : z ∈ Zc) (hzp : z ^ p = 1) : z = 1 := by
  have hzs : ((⟨z, hz⟩ : Zc)) ^ p = 1 := Subtype.ext hzp
  have hdvd : orderOf (⟨z, hz⟩ : Zc) ∣ p := orderOf_dvd_of_pow_eq_one hzs
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  · exfalso
    apply hZ
    rw [← h1]
    exact orderOf_dvd_natCard _

theorem commute_of_mk_commute {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card Zc)
    (hZc : Zc ≤ Subgroup.center S) {A B : S} (hAp : A ^ p = 1)
    (hc : (A : S ⧸ Zc) * (B : S ⧸ Zc) = (B : S ⧸ Zc) * (A : S ⧸ Zc)) : A * B = B * A := by
  set z : S := B * A * B⁻¹ * A⁻¹ with hz
  have hzs : z ∈ Zc := by
    rw [← QuotientGroup.eq_one_iff, hz]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← hc]
    group
  have hzc : z ∈ Subgroup.center S := hZc hzs
  have hBA : B * A * B⁻¹ = z * A := by rw [hz]; group
  have hcomm : Commute z A := Subgroup.mem_center_iff.mp hzc A |>.symm
  have h1 : (z * A) ^ p = z ^ p := by
    rw [hcomm.mul_pow, hAp, mul_one]
  have h2 : (z * A) ^ p = 1 := by
    rw [← hBA, conj_pow, hAp]
    simp
  have hz1 : z = 1 := eq_one_of_pow_eq_one_of_not_dvd_card Zc hp hZ hzs (h1.symm.trans h2)
  rw [hz1, one_mul] at hBA
  exact (mul_inv_eq_iff_eq_mul.mp hBA).symm

theorem exists_mk_lift_pow_eq_one [Finite S] {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card Zc)
    {y : S ⧸ Zc} (hyp : y ^ p = 1) : ∃ A : S, (A : S ⧸ Zc) = y ∧ A ^ p = 1 := by
  obtain ⟨A₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hA0 : A₀ ^ p ∈ Zc := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hyp
  set z : ℕ := Nat.card Zc with hzdef
  have hcop : Nat.Coprime z p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨A₀ ^ (z * m), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow]
    have h1 : z * m = p * (z * m / p) + 1 := by
      have := Nat.div_add_mod (z * m) p
      rw [hm] at this
      omega
    rw [h1, pow_add, pow_mul, hyp, one_pow, one_mul, pow_one]
  · have h2 : (⟨A₀ ^ p, hA0⟩ : Zc) ^ z = 1 := pow_card_eq_one'
    have h3 : (A₀ ^ p) ^ z = 1 := congrArg Subtype.val h2
    calc (A₀ ^ (z * m)) ^ p = ((A₀ ^ p) ^ z) ^ m := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [h3, one_pow]

theorem centralizer_mk_eq_map {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card Zc)
    (hZc : Zc ≤ Subgroup.center S) {x : S} (hxp : x ^ p = 1) :
    Subgroup.centralizer ({(x : S ⧸ Zc)} : Set (S ⧸ Zc)) =
      (Subgroup.centralizer ({x} : Set S)).map (QuotientGroup.mk' Zc) := by
  ext w
  constructor
  · intro hw
    obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective w
    have := commute_of_mk_commute Zc hp hZ hZc hxp
      (Subgroup.mem_centralizer_singleton_iff.mp hw).symm
    exact ⟨G, Subgroup.mem_centralizer_singleton_iff.mpr this.symm, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (G : S ⧸ Zc) * (x : S ⧸ Zc) = (x : S ⧸ Zc) * (G : S ⧸ Zc)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp hG

theorem mem_sup_centralizer_of_central_factorization [Finite S] {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card Zc) (hZc : Zc ≤ Subgroup.center S) {x : S} (hxp : x ^ p = 1)
    {ι : Type*} (F : ι → Subgroup S) (hFq : ∀ i, CFSG.IsQuasisimple ↥(F i))
    (hFC : ∀ i, F i ≤ Subgroup.centralizer ({x} : Set S))
    (hFn : ∀ i, ∀ g ∈ Subgroup.centralizer ({x} : Set S), ∀ f ∈ F i, g * f * g⁻¹ ∈ F i)
    {Y z k : S} (hYzk : Y = z * k)
    (hzc : ∀ G ∈ Subgroup.centralizer ({x} : Set S), z * G = G * z) (hk : k ∈ ⨆ i, F i)
    {E : Subgroup (S ⧸ Zc)}
    (hE : IsComponentOf (Subgroup.centralizer ({(x : S ⧸ Zc)} : Set (S ⧸ Zc))) E) :
    (Y : S ⧸ Zc) ∈ E ⊔ Subgroup.centralizer (E : Set (S ⧸ Zc)) := by
  have hker : (QuotientGroup.mk' Zc).ker ≤ Subgroup.center S := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hN := centralizer_mk_eq_map Zc hp hZ hZc hxp
  refine mem_sup_centralizer_of_factorization (N := Subgroup.centralizer ({(x : S ⧸ Zc)} :
    Set (S ⧸ Zc))) (fun i => (F i).map (QuotientGroup.mk' Zc)) (fun i => Or.inr ?_)
    (z := (z : S ⧸ Zc)) (k := (k : S ⧸ Zc)) ?_ ?_ ?_ hE
  · exact isComponentOf_map_block (QuotientGroup.mk' Zc) (QuotientGroup.mk'_surjective Zc) hker x
      (F i) (hFq i) (hFC i) (hFn i)
  · rw [hYzk, QuotientGroup.mk_mul]
  · intro n hn
    rw [hN] at hn
    obtain ⟨G, hG, rfl⟩ := hn
    show (z : S ⧸ Zc) * (G : S ⧸ Zc) = (G : S ⧸ Zc) * (z : S ⧸ Zc)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hzc G hG]
  · have h1 : (k : S ⧸ Zc) ∈ (⨆ i, F i).map (QuotientGroup.mk' Zc) := ⟨k, hk, rfl⟩
    rwa [Subgroup.map_iSup] at h1

end Lift

end CFSG.RankThree.PartOne.FOC
