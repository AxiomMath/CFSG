module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem mem_oTwoPrime_iff {K : Subgroup G} {p : ℕ} (y : ↥K) :
    (y : G) ∈ oTwoPrime K p ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) y ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) := by
  constructor
  · rintro ⟨y', hy', hyy'⟩
    rwa [Subtype.ext hyy'] at hy'
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem oTwoPrime_le (K : Subgroup G) (p : ℕ) : oTwoPrime K p ≤ K :=
  Subgroup.map_subtype_le _

theorem pCoreOf_le_oTwoPrime (K : Subgroup G) (p : ℕ) : pCoreOf 2 K ≤ oTwoPrime K p := by
  rintro _ ⟨y, hy, rfl⟩
  show (y : G) ∈ oTwoPrime K p
  rw [mem_oTwoPrime_iff]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
  exact Subgroup.one_mem _

theorem exists_pow_mem_pCoreOf_of_mem_oTwoPrime {K : Subgroup G} {p : ℕ} {x : G}
    (hx : x ∈ oTwoPrime K p) : ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hy⟩
  refine ⟨k, y ^ p ^ k, ?_, by simp⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (y ^ p ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mem_pCoreOf_of_mem_oTwoPrime {K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} (hx : x ∈ oTwoPrime K p) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  set z : ↥(CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K)) := ⟨_, hy⟩ with hz
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup z
  have hk' : z ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simp only [hz, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    have : y ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hcop : Nat.Coprime (p ^ j) (2 ^ k) :=
    Nat.Coprime.pow j k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : z = 1 := by
    have h2 : z ^ (p ^ j).gcd (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hj, hk'⟩
    rwa [hcop.gcd_eq_one, pow_one] at h2
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) y = 1 := by
    simpa [hz] using congrArg Subtype.val h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact ⟨y, h3, rfl⟩

theorem normalizer_le_normalizer_oTwoPrime (K : Subgroup G) (p : ℕ) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (oTwoPrime K p : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oTwoPrime K p,
      g * x * g⁻¹ ∈ oTwoPrime K p := by
    intro g hg x hx
    have hgK : ∀ a ∈ K, g * a * g⁻¹ ∈ K := fun a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    have hgK' : ∀ a ∈ K, g⁻¹ * a * g ∈ K := fun a ha => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) a).mp ha
      simpa using this
    let c : ↥K ≃* ↥K :=
      { toFun := fun a => ⟨g * a * g⁻¹, hgK a a.2⟩
        invFun := fun a => ⟨g⁻¹ * a * g, hgK' a a.2⟩
        left_inv := fun a => Subtype.ext (by simp [mul_assoc])
        right_inv := fun a => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hc : (CFSG.pCore 2 ↥K).map c.toMonoidHom = CFSG.pCore 2 ↥K :=
      Subgroup.characteristic_iff_map_eq.mp
        (by exact CFSG.LieType.BorelTits.pCore_characteristic 2) c
    let cb := QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) c hc
    have hX : (CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K)).map cb.toMonoidHom =
        CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.pCore_map_iso p cb
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (c y) ∈
        CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [← hX]
      exact ⟨_, hy, rfl⟩
    exact (mem_oTwoPrime_iff (c y)).mpr hy'
  intro g hg
  refine mem_normalizer_of_conj (key g hg) (fun x hx => ?_)
  have := key g⁻¹ (Subgroup.inv_mem _ hg) x hx
  simpa using this

theorem le_normalizer_oTwoPrime (K : Subgroup G) (p : ℕ) :
    K ≤ Subgroup.normalizer (oTwoPrime K p : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoPrime K p)

end CFSG.Quasithin.Vol2.Ch11.SecD
