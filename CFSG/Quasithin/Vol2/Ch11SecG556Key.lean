module

public import CFSG.Quasithin.Vol2.Ch11SecGTBar
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open

variable {G : Type} [Group G]

theorem mem_pCoreOf_iff_mem_pCore {K : Subgroup G} (k : ↥K) :
    (k : G) ∈ pCoreOf 2 K ↔ k ∈ CFSG.pCore 2 ↥K := CFSG.mem_openPCoreOf_iff k

theorem mem_pCoreOf_iff_mk_eq_one {K : Subgroup G} (k : ↥K) :
    (k : G) ∈ pCoreOf 2 K ↔ (k : Bar.KBar K) = 1 := by
  rw [mem_pCoreOf_iff_mem_pCore, QuotientGroup.eq_one_iff]

variable [Finite G]

theorem mem_pCoreOf_of_centralizes {K K₁ P T H₁ : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQP : pCoreOf 2 K ≤ P) (hPK₁ : P ≤ K₁) (hK₁K : K₁ ≤ K)
    (hPp : ∀ x ∈ P, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 K)
    (hH₁P : H₁ ≤ Subgroup.normalizer (P : Set G)) (hH₁K : H₁ ≤ Subgroup.normalizer (K : Set G))
    (hK₁H : K₁ ≤ H₁) (hHK₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G))
    (hT : QuasithinUnique.IsSylowTwoOf T H₁) (hKT : K₁ ⊔ T = H₁)
    (hF2 : ∀ y ∈ K₁, (∀ x ∈ P, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 K) → y ∈ P)
    {a : G} (ha : a ∈ H₁) {e : ℕ} (hae : a ^ 2 ^ e = 1)
    (hc : ∀ x ∈ P, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 K) : a ∈ pCoreOf 2 H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPK : P ≤ K := hPK₁.trans hK₁K
  have haK : a ∈ Subgroup.normalizer (K : Set G) := hH₁K ha
  have hcK : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx => (Subgroup.mem_normalizer_iff.mp haK x).mp hx
  set α := Bar.aut K ⟨a, haK⟩ with hα
  have hαk : ∀ k : ↥K, α (k : Bar.KBar K) = ((⟨a * k * a⁻¹, hcK k k.2⟩ : ↥K) : Bar.KBar K) :=
    fun k => by
      rw [hα, Bar.aut_mk]
      rfl
  have hαP : ∀ k : ↥K, (k : G) ∈ P → α (k : Bar.KBar K) = (k : Bar.KBar K) := by
    intro k hk
    rw [hαk]
    have h1 := (mem_pCoreOf_iff_mk_eq_one ((⟨a * k * a⁻¹, hcK k k.2⟩ : ↥K) * k⁻¹)).mp (hc k hk)
    rwa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h1
  have hαK₁ : ∀ y : ↥K, (y : G) ∈ K₁ → α (y : Bar.KBar K) = (y : Bar.KBar K) := by
    intro y hy
    have hayK₁ : a * y * a⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp (hHK₁ ha) y).mp hy
    set d : ↥K := y⁻¹ * ⟨a * y * a⁻¹, hcK y y.2⟩ with hd
    have hdK₁ : (d : G) ∈ K₁ := K₁.mul_mem (K₁.inv_mem hy) hayK₁
    have hdbar : (d : Bar.KBar K) = (y : Bar.KBar K)⁻¹ * α (y : Bar.KBar K) := by
      rw [hαk, hd, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hdC : ∀ x ∈ P, (d : G) * x * (d : G)⁻¹ * x⁻¹ ∈ pCoreOf 2 K := by
      intro x hx
      set kx : ↥K := ⟨x, hPK hx⟩ with hkx
      have hyx : ((y * kx * y⁻¹ : ↥K) : G) ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hH₁P (hK₁H hy)) x).mp hx
      have h1 := hαP _ hyx
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
        map_inv, hαP kx hx] at h1
      apply (mem_pCoreOf_iff_mk_eq_one (d * kx * d⁻¹ * kx⁻¹)).mpr
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hdbar]
      calc (y : Bar.KBar K)⁻¹ * α y * (kx : Bar.KBar K) * ((y : Bar.KBar K)⁻¹ * α y)⁻¹ *
            (kx : Bar.KBar K)⁻¹
          = (y : Bar.KBar K)⁻¹ * (α y * (kx : Bar.KBar K) * (α y)⁻¹) * (y : Bar.KBar K) *
            (kx : Bar.KBar K)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hdP : (d : G) ∈ P := hF2 d hdK₁ hdC
    have hαδ : α (d : Bar.KBar K) = (d : Bar.KBar K) := hαP d hdP
    have hαy : α (y : Bar.KBar K) = (y : Bar.KBar K) * (d : Bar.KBar K) := by
      rw [hdbar]; group
    have hpow : ∀ m : ℕ, (α ^ m) (y : Bar.KBar K) = (y : Bar.KBar K) * (d : Bar.KBar K) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαy, hαδ, pow_succ', mul_assoc]
    have hαe : α ^ 2 ^ e = 1 := by
      have h1 : (⟨a, haK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ e = 1 :=
        Subtype.ext (by simpa using hae)
      rw [hα, ← map_pow, h1, map_one]
    have hδe : (d : Bar.KBar K) ^ 2 ^ e = 1 := by
      have h1 := hpow (2 ^ e)
      rw [hαe, MulAut.one_apply] at h1
      exact mul_eq_left.mp h1.symm
    obtain ⟨k, hk⟩ := hPp d hdP
    have hδk : (d : Bar.KBar K) ^ p ^ k = 1 := by
      have h1 := (mem_pCoreOf_iff_mk_eq_one (d ^ p ^ k)).mp (by simpa using hk)
      rwa [QuotientGroup.mk_pow] at h1
    have hcop : Nat.Coprime (2 ^ e) (p ^ k) :=
      Nat.Coprime.pow e k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have hδ1 : (d : Bar.KBar K) = 1 := by
      have h2 : (d : Bar.KBar K) ^ (2 ^ e).gcd (p ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hδe, hδk⟩
      rwa [hcop.gcd_eq_one, pow_one] at h2
    rw [hαy, hδ1, mul_one]
  have hQK₁ : pCoreOf 2 K ≤ K₁ := hQP.trans hPK₁
  have hQ2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hQO : pCoreOf 2 K ≤ (CFSG.pCore 2 ↥K₁).map K₁.subtype := by
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf 2 hQK₁
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQK₁).mpr
        (hK₁K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))) hQ2
    have h2 : pCoreOf 2 K₁ = (CFSG.pCore 2 ↥K₁).map K₁.subtype := by
      unfold pCoreOf
      try with_reducible rfl
    rwa [h2] at h1
  refine mem_pCoreOf_of_comm_mem hK₁H hHK₁ hT hKT ha hae fun y hy => hQO ?_
  set ky : ↥K := ⟨y, hK₁K hy⟩ with hky
  have h1 := hαK₁ ky hy
  rw [hαk] at h1
  apply (mem_pCoreOf_iff_mk_eq_one ((⟨a * ky * a⁻¹, hcK ky ky.2⟩ : ↥K) * ky⁻¹)).mpr
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]

theorem le_pCoreOf_of_centralizes {K K₁ P T H₁ : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQP : pCoreOf 2 K ≤ P) (hPK₁ : P ≤ K₁) (hK₁K : K₁ ≤ K)
    (hPp : ∀ x ∈ P, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 K)
    (hH₁P : H₁ ≤ Subgroup.normalizer (P : Set G)) (hH₁K : H₁ ≤ Subgroup.normalizer (K : Set G))
    (hK₁H : K₁ ≤ H₁) (hHK₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G))
    (hT : QuasithinUnique.IsSylowTwoOf T H₁) (hKT : K₁ ⊔ T = H₁)
    (hF2 : ∀ y ∈ K₁, (∀ x ∈ P, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 K) → y ∈ P)
    {X : Subgroup G} (hXH : X ≤ H₁) (hX2 : IsPGroup 2 X)
    (hc : ∀ a ∈ X, ∀ x ∈ P, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 K) : X ≤ pCoreOf 2 H₁ := by
  intro a ha
  obtain ⟨e, he⟩ := hX2 ⟨a, ha⟩
  exact mem_pCoreOf_of_centralizes hp hp2 hQP hPK₁ hK₁K hPp hH₁P hH₁K hK₁H hHK₁ hT hKT hF2
    (hXH ha) (e := e) (by simpa using congrArg Subtype.val he) (hc a ha)

end CFSG.Quasithin.Vol2.Ch11.SecG
