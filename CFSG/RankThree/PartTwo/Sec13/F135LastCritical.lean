module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

universe u

open CFSG.OrderReductions.FrattiniAutomorphisms

theorem l8_map_eq {P : Type u} [Group P] (Q : Subgroup P) [Q.Characteristic] (σ : MulAut P) :
    Q.map (σ : P →* P) = Q :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance σ

@[expose] def l8_restrict {P : Type u} [Group P] (Q : Subgroup P) [Q.Characteristic]
    (σ : MulAut P) : MulAut Q :=
  (MulEquiv.subgroupMap σ Q).trans (MulEquiv.subgroupCongr (l8_map_eq Q σ))

theorem l8_restrict_coe {P : Type u} [Group P] (Q : Subgroup P) [Q.Characteristic]
    (σ : MulAut P) (x : Q) : ((l8_restrict Q σ x : Q) : P) = σ x :=
  rfl

@[expose] def l8_actHom {P K : Type u} [Group P] [Group K] (Q : Subgroup P) [Q.Characteristic]
    (φ : K →* MulAut P) : K →* MulAut Q :=
  MonoidHom.mk' (fun k => l8_restrict Q (φ k)) (fun a b => by
    show l8_restrict Q (φ (a * b)) = l8_restrict Q (φ a) * l8_restrict Q (φ b)
    ext x
    simp [l8_restrict_coe, map_mul, MulAut.mul_apply])

theorem l8_fix_of_one {P : Type u} [Group P] (Q : Subgroup P) [Q.Characteristic]
    {σ : MulAut P} (h : l8_restrict Q σ = 1) : ∀ x ∈ Q, σ x = x := by
  intro x hx
  have h2 := congrArg (fun τ : MulAut Q => ((τ ⟨x, hx⟩ : Q) : P)) h
  simpa [l8_restrict_coe] using h2

theorem l8_coprime_two {P : Type u} [Group P] (α : MulAut P) (n : ℕ)
    (h : α ^ (2 ^ n) = 1) : Nat.Coprime (orderOf α) 3 :=
  Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h)
    (Nat.Coprime.pow_left n (by norm_num))

theorem l8_act_eq_one {Q : Type u} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    {a : MulAut Q} (ha : quotientAutomorphism (frattini Q) a = 1) {n : ℕ}
    (hn : a ^ (2 ^ n) = 1) : a = 1 := by
  have hker : IsPGroup 3 (quotientAutomorphism (frattini Q)).ker :=
    (CFSG.GroupTheory.frattini_automorphism_kernel hQ).2
  obtain ⟨m, hm⟩ := hker ⟨a, MonoidHom.mem_ker.2 ha⟩
  have hm' : a ^ (3 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hg : a ^ Nat.gcd (3 ^ m) (2 ^ n) = 1 := pow_gcd_eq_one.2 ⟨hm', hn⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow m n (by norm_num : Nat.Coprime 3 2)),
    pow_one] at hg
  exact hg

theorem l8_odd_two_eq_one {K : Type u} [Group K] (N : Subgroup K) (hNodd : Odd (Nat.card N))
    {y : K} (hyN : y ∈ N) {n : ℕ} (hn : y ^ (2 ^ n) = 1) : y = 1 := by
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hNodd)
  have h1 : (⟨y, hyN⟩ : N) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hn)
  have h2 : (⟨y, hyN⟩ : N) ^ Nat.card N = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_natCard _)
  have h3 : (⟨y, hyN⟩ : N) ^ Nat.gcd (2 ^ n) (Nat.card N) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
  simpa using congrArg Subtype.val h3

theorem l8_phi_one {P : Type u} [Group P] {K : Type u} [Group K]
    (φ : K →* MulAut P)
    (hKgen : Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤)
    (h : ∀ z : K, (∃ n : ℕ, z ^ (2 ^ n) = 1) → φ z = 1) : φ = 1 := by
  have hsub : Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} ≤ φ.ker :=
    (Subgroup.closure_le _).2 fun z hz => MonoidHom.mem_ker.2 (h z hz)
  rw [hKgen] at hsub
  refine MonoidHom.ext fun k => ?_
  exact MonoidHom.mem_ker.1 (hsub (Subgroup.mem_top k))

theorem l8_main {P : Type u} [Group P] [Finite P] {K : Type u} [Group K] [Finite K]
    (φ : K →* MulAut P) (hφ : φ ≠ 1)
    (hKgen : Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤)
    (N : Subgroup K) [N.Normal] (hNodd : Odd (Nat.card N))
    (hdich : ∀ N₁ : Subgroup K, N₁.Normal → N₁ = ⊤ ∨ N₁ ≤ N)
    (Q : Subgroup P) [Q.Characteristic] (hQp : IsPGroup 3 Q) (hQexp : ∀ x ∈ Q, x ^ 3 = 1)
    (hQcomm : ⁅Q, (⊤ : Subgroup P)⁆ ≤ Q ⊓ Subgroup.centralizer (Q : Set P))
    (hstar : ∀ α : MulAut P, Nat.Coprime (orderOf α) 3 → (∀ x ∈ Q, α x = x) → α = 1) :
    ∃ ψ : K →* MulAut (Q ⧸ frattini Q),
      (∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ⁅⁅x, y⁆, z⁆ = 1) ∧
      (∀ k : K, ∀ x : Q, ∃ x' : Q, (x' : P) = φ k (x : P) ∧
        ψ k (QuotientGroup.mk x) = QuotientGroup.mk x') ∧
      (∀ y : K, (∃ n : ℕ, y ^ (2 ^ n) = 1) → ψ y = 1 → y = 1) := by
  refine ⟨quotientAction (frattini Q) (l8_actHom Q φ), ?_, ?_, ?_⟩
  · intro x hx y _ z hz
    have h1 : ⁅x, y⁆ ∈ ⁅Q, (⊤ : Subgroup P)⁆ :=
      commutator_mem_commutator hx (Subgroup.mem_top y)
    have h2 : ⁅x, y⁆ ∈ Subgroup.centralizer (Q : Set P) := (Subgroup.mem_inf.1 (hQcomm h1)).2
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 h2 z hz).symm
  · intro k x
    exact ⟨l8_actHom Q φ k x, l8_restrict_coe Q (φ k) x,
      quotientAction_apply (frattini Q) (l8_actHom Q φ) k x⟩
  · rintro y ⟨n, hn⟩ hψ
    have hψ' : quotientAutomorphism (frattini Q) (l8_actHom Q φ y) = 1 := hψ
    have hn' : (l8_actHom Q φ y) ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
    have hact : l8_actHom Q φ y = 1 := l8_act_eq_one hQp hψ' hn'
    rcases hdich (l8_actHom Q φ).ker inferInstance with htop | hle
    · exfalso
      apply hφ
      apply l8_phi_one φ hKgen
      rintro z ⟨m, hm⟩
      have hall : ∀ k : K, l8_actHom Q φ k = 1 := fun k => by
        have hk : k ∈ (l8_actHom Q φ).ker := by
          rw [htop]
          exact Subgroup.mem_top k
        exact MonoidHom.mem_ker.1 hk
      have hz1 : l8_restrict Q (φ z) = 1 := hall z
      have hφz : φ z ^ (2 ^ m) = 1 := by rw [← map_pow, hm, map_one]
      exact hstar (φ z) (l8_coprime_two _ m hφz) (l8_fix_of_one Q hz1)
    · exact l8_odd_two_eq_one N hNodd (hle (MonoidHom.mem_ker.2 hact)) hn

theorem exists_faithful_action {P : Type u} [Group P] [Finite P] (hP : IsPGroup 3 P)
    {K : Type u} [Group K] [Finite K] (φ : K →* MulAut P) (hφ : φ ≠ 1)
    (hKgen : Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤)
    (N : Subgroup K) [N.Normal] (hNodd : Odd (Nat.card N))
    (hdich : ∀ N₁ : Subgroup K, N₁.Normal → N₁ = ⊤ ∨ N₁ ≤ N) :
    ∃ (Q : Subgroup P) (ψ : K →* MulAut (Q ⧸ frattini Q)),
      (∀ x ∈ Q, x ^ 3 = 1) ∧ (∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ⁅⁅x, y⁆, z⁆ = 1) ∧
      (∀ k : K, ∀ x : Q, ∃ x' : Q, (x' : P) = φ k (x : P) ∧
        ψ k (QuotientGroup.mk x) = QuotientGroup.mk x') ∧
      (∀ y : K, (∃ n : ℕ, y ^ (2 ^ n) = 1) → ψ y = 1 → y = 1) := by
  obtain ⟨C, -, -, -, -, hQchar, -, hQcomm, hQexp, -, hstar⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (p := 3)
      (by norm_num) hP
  obtain ⟨ψ, h1, h2, h3⟩ := l8_main φ hφ hKgen N hNodd hdich
    (CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn 3 C) (hP.to_subgroup _) hQexp hQcomm hstar
  exact ⟨CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn 3 C, ψ, hQexp, h1, h2, h3⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
