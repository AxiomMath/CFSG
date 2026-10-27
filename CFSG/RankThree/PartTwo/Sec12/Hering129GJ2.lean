module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

def kleinFour : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) where
  carrier := {q | q.1 = 1 ∧ q.2 ^ 2 = 1}
  one_mem' := ⟨rfl, by simp⟩
  mul_mem' := by
    intro p q hp hq
    refine ⟨by simp [hp.1, hq.1], ?_⟩
    have key : ∀ u v : alternatingGroup (Fin 4), u ^ 2 = 1 → v ^ 2 = 1 → (u * v) ^ 2 = 1 := by
      decide +kernel
    exact key _ _ hp.2 hq.2
  inv_mem' := by
    intro p hp
    refine ⟨by simp [hp.1], ?_⟩
    have key : ∀ u : alternatingGroup (Fin 4), u ^ 2 = 1 → u⁻¹ ^ 2 = 1 := by decide +kernel
    exact key _ hp.2

theorem mem_kleinFour {q : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)} :
    q ∈ kleinFour ↔ q.1 = 1 ∧ q.2 ^ 2 = 1 := Iff.rfl

theorem kleinFour_conj (g q : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) (hq : q ∈ kleinFour) :
    g * q * g⁻¹ ∈ kleinFour := by
  have key : ∀ g q : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4),
      q.1 = 1 ∧ q.2 ^ 2 = 1 → (g * q * g⁻¹).1 = 1 ∧ (g * q * g⁻¹).2 ^ 2 = 1 := by
    decide +kernel
  exact key g q hq

theorem kleinFour_isPGroup : IsPGroup 2 kleinFour := by
  intro q
  refine ⟨1, ?_⟩
  have h := q.2
  rw [mem_kleinFour] at h
  obtain ⟨h1, h2⟩ := h
  apply Subtype.ext
  show ((q : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ^ 2 ^ 1) = 1
  rw [pow_one, Prod.ext_iff]
  constructor
  · simp [h1]
  · simpa using h2

theorem s3a4_second : ∀ p : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4), p ≠ 1 → p ^ 3 = 1 →
    (∀ g, g * p * g⁻¹ = p ∨ g * p * g⁻¹ = p * p) → p.2 = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem s3a4_key : ∀ p u : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4), p ≠ 1 → p ^ 3 = 1 →
    p.2 = 1 → u * p = p * u → u ^ 8 = 1 → u.1 = 1 ∧ u.2 ^ 2 = 1 := by
  decide +kernel

theorem pow_eight_eq_one_of_pow_two_pow {u : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)}
    {k : ℕ} (hu : u ^ (2 ^ k) = 1) : u ^ 8 = 1 := by
  have h72 : Nat.card (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) = 72 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hdvd : orderOf u ∣ 72 := h72 ▸ orderOf_dvd_natCard u
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have h16 : 2 ^ 4 ∣ 72 := (pow_dvd_pow 2 (by omega)).trans (hj ▸ hdvd)
    norm_num at h16
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3))

theorem j2_two_subgroup_le_pCore (h415 : Sec4.Item4_15) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {A9 : Subgroup X}
    (hAP : A9 ≤ P) (hA9 : Nat.card A9 = 9) {a : X} (haA : a ∈ A9)
    (haZ : a ∉ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X))
    {U : Subgroup X} (hU2 : IsPGroup 2 U) (hUC : U ≤ Subgroup.centralizer ({a} : Set X)) :
    U ≤ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, ⟨e⟩, -⟩ := h4 A9 ⟨hAP, hA9⟩ a haA haZ
  obtain ⟨-, -, hexp⟩ := hHeis
  set N : Subgroup X := Subgroup.normalizer (Subgroup.zpowers a : Set X) with hNdef
  set C : Subgroup X := Subgroup.centralizer ({a} : Set X) with hCdef
  have hCN : C ≤ N := by
    rw [hCdef, hNdef, ← KFacts.KS14.centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have ha3 : a ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨a, hAP haA⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ (Subgroup.one_mem _))
  have haN : a ∈ N := Subgroup.le_normalizer (Subgroup.mem_zpowers a)
  set aN : ↥N := ⟨a, haN⟩ with haNdef
  set p := e aN with hpdef
  have hp1 : p ≠ 1 := by
    intro h
    apply ha1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hp3 : p ^ 3 = 1 := by
    rw [hpdef, ← map_pow]
    have : aN ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hnorm : ∀ g, g * p * g⁻¹ = p ∨ g * p * g⁻¹ = p * p := by
    intro g
    obtain ⟨n, rfl⟩ := e.surjective g
    have hmem : (n : X) * a * (n : X)⁻¹ ∈ Subgroup.zpowers a :=
      (Subgroup.mem_normalizer_iff.mp n.2 a).mp (Subgroup.mem_zpowers a)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h3z : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
    have hkr : a ^ k = a ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
      rw [zpow_add, zpow_mul, h3z, one_zpow, mul_one]
    have key : n * aN * n⁻¹ = aN ∨ n * aN * n⁻¹ = aN * aN := by
      have h13 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h13 with h0 | h1 | h2
      · exfalso
        apply ha1
        have h1' : (n : X) * a * (n : X)⁻¹ = 1 := by rw [← hk, hkr, h0, zpow_zero]
        have h2' := congrArg (fun y => (n : X)⁻¹ * y * (n : X)) h1'
        simpa [mul_assoc] using h2'
      · left
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hk, hkr, h1, zpow_one]
      · right
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hk, hkr, h2, zpow_two]
    rcases key with h | h
    · left
      rw [hpdef, ← map_inv, ← map_mul, ← map_mul, h]
    · right
      rw [hpdef, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h]
  have hp2 : p.2 = 1 := s3a4_second p hp1 hp3 hnorm
  set V : Subgroup X := (kleinFour.comap e.toMonoidHom).map N.subtype with hVdef
  have hVC : V ≤ C := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hv
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    have hn' : e n ∈ kleinFour := hn
    have hcomm : e n * p = p * e n := by
      apply Prod.ext
      · simp [(mem_kleinFour.mp hn').1]
      · simp [hp2]
    have h2 : e (n * aN) = e (aN * n) := by rw [map_mul, map_mul]; exact hcomm
    exact congrArg Subtype.val (e.injective h2)
  set VC : Subgroup ↥C := V.subgroupOf C with hVCdef
  have hVCn : VC.Normal := by
    refine ⟨fun v hv g => ?_⟩
    rw [hVCdef, Subgroup.mem_subgroupOf] at hv ⊢
    obtain ⟨n, hn, hnv⟩ := Subgroup.mem_map.mp hv
    have hgN : (g : X) ∈ N := hCN g.2
    refine Subgroup.mem_map.mpr ⟨⟨g, hgN⟩ * n * ⟨g, hgN⟩⁻¹, ?_, ?_⟩
    · show e (⟨g, hgN⟩ * n * ⟨g, hgN⟩⁻¹) ∈ kleinFour
      rw [map_mul, map_mul, map_inv]
      exact kleinFour_conj _ _ hn
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hnv ⊢
      rw [hnv]
  have hV2 : IsPGroup 2 V :=
    (kleinFour_isPGroup.comap_of_injective e.toMonoidHom e.injective).map N.subtype
  have hVC2 : IsPGroup 2 VC := IsPGroup.comap_subtype hV2
  have hVCle : VC ≤ CFSG.pCore 2 ↥C := le_sSup ⟨hVCn, hVC2⟩
  have hVle : V ≤ inSubgroup (CFSG.pCore 2) C := by
    intro v hv
    exact ⟨⟨v, hVC hv⟩, hVCle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  refine fun u hu => hVle ?_
  have huC : u ∈ C := hUC hu
  set uN : ↥N := ⟨u, hCN huC⟩ with huNdef
  have hcomm : e uN * p = p * e uN := by
    rw [hpdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp huC
  obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
  have huk : (e uN) ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : uN ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hmem := s3a4_key p (e uN) hp1 hp3 hp2 hcomm (pow_eight_eq_one_of_pow_two_pow huk)
  exact Subgroup.mem_map.mpr ⟨uN, show e uN ∈ kleinFour from hmem, rfl⟩

end CFSG.RankThree.PartTwo.Sec12.Hering129G
