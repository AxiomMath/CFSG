module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecE9A
public import CFSG.Quasithin.Vol2.Ch10SecE9C
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

omit [Finite G] in
theorem eq_one_of_sq_cube {Q : Type*} [Group Q] {y : Q} (h2 : y * y = 1) (h3 : y ^ 3 = 1) :
    y = 1 := by
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, mul_one]


theorem le_normalizer_of_core {X T T₁ : Subgroup G} (hc : C10P34.PairCtx H K₁ K₂ φ) {p : ℕ}
    [Fact p.Prime] (h8 : p % 8 = 3 ∨ p % 8 = 5) (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hTH : T ≤ H) (hT₁T : T₁ ≤ T)
    (hST₁ : T ⊓ (K₁ ⊔ K₂) ≤ T₁) (hXK : X ≤ K₁ ⊔ K₂)
    (hbad : pCoreOf 2 X ≤ pCoreOf 2 (K₁ ⊔ K₂)) {x₁ : G} (hx₁ : x₁ ∈ X)
    (hx₁3 : x₁ ^ 3 ∈ pCoreOf 2 X) (hx₁O : x₁ ∉ pCoreOf 2 X)
    (hτ : ∀ τ ∈ T₁, τ * x₁ * τ⁻¹ * x₁⁻¹ ∈ pCoreOf 2 X ∨ τ * x₁ * τ⁻¹ * x₁ ∈ pCoreOf 2 X) :
    T₁ ≤ Subgroup.normalizer (K₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) := fun k hk => by
    have h1 : k ∈ φ.ker := hk
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hO : ∀ k : ↥(K₁ ⊔ K₂), (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) → φ k = 1 := fun k hk => by
    have h1 : k ∈ φ.ker := by rw [hc.ker, Subgroup.mem_subgroupOf]; exact hk
    exact h1
  have hx₁K := hXK hx₁
  set y := φ ⟨x₁, hx₁K⟩ with hy
  have hy1 : y ≠ 1 := by
    intro h
    apply hx₁O
    have h1 := hker _ h
    have hle : X ⊓ pCoreOf 2 (K₁ ⊔ K₂) ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
            (Subgroup.le_normalizer (hXK hx))⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hle ⟨hx₁, h1⟩
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← map_pow]
    exact hO _ (hbad hx₁3)
  have hact : ∀ τ ∈ T₁, ∀ hτK : τ * x₁ * τ⁻¹ ∈ K₁ ⊔ K₂,
      φ ⟨τ * x₁ * τ⁻¹, hτK⟩ = y ∨ φ ⟨τ * x₁ * τ⁻¹, hτK⟩ = y⁻¹ := by
    intro τ hτT hτK
    rcases hτ τ hτT with h | h
    · left
      have h1 : φ (⟨τ * x₁ * τ⁻¹, hτK⟩ * (⟨x₁, hx₁K⟩ : ↥(K₁ ⊔ K₂))⁻¹) = 1 := hO _ (hbad h)
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    · right
      have h1 : φ (⟨τ * x₁ * τ⁻¹, hτK⟩ * (⟨x₁, hx₁K⟩ : ↥(K₁ ⊔ K₂))) = 1 := hO _ (hbad h)
      rw [map_mul, mul_eq_one_iff_eq_inv] at h1
      exact h1
  obtain ⟨hSyl₁, hSyl₂, hSprod⟩ := map_sylow_eq_prod hc.surj hS
  have hy12 : y.1 = 1 ∨ y.2 = 1 := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    have hs : ∃ s ∈ ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ),
        s * y.2 * s⁻¹ ≠ y.2 := by
      by_contra hns
      simp only [not_exists, not_and, not_not] at hns
      have hcen : y.2 ∈ Subgroup.centralizer
          (((((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) :
            Subgroup _) : Set _) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs'
        have := hns s hs'
        calc s * y.2 = s * y.2 * s⁻¹ * s := by group
          _ = y.2 * s := by rw [this]
      rw [centralizer_sylow_eq h8 e₂ hSyl₂] at hcen
      obtain ⟨j, hj⟩ := hSyl₂.2.1 ⟨_, hcen⟩
      have hj' : y.2 ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have hy23 : y.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hy3
      have hord : orderOf y.2 ∣ Nat.gcd (2 ^ j) 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hy23)
      have hg : Nat.gcd (2 ^ j) 3 = 1 :=
        Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)
      rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hord
      exact hne2 hord
    obtain ⟨s, hsS, hsy⟩ := hs
    have hmem : ((1 : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁), s) ∈
        ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ := by
      rw [hSprod]
      exact ⟨Subgroup.one_mem _, hsS⟩
    obtain ⟨b, hbS, hbs⟩ := hmem
    have hbT₁ : (b : G) ∈ T₁ := hST₁ (Subgroup.mem_subgroupOf.mp hbS)
    have hbK : (b : G) * x₁ * (b : G)⁻¹ ∈ K₁ ⊔ K₂ :=
      (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).mul_mem b.2 hx₁K) ((K₁ ⊔ K₂).inv_mem b.2)
    have hφb : φ ⟨(b : G) * x₁ * (b : G)⁻¹, hbK⟩ = φ b * y * (φ b)⁻¹ := by
      rw [hy, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hbs] at hφb
    rcases hact _ hbT₁ hbK with h | h
    · rw [hφb] at h
      exact hsy (by simpa using congrArg Prod.snd h)
    · rw [hφb] at h
      have hinv : y.1 = y.1⁻¹ := by simpa using congrArg Prod.fst h
      have h13 : y.1 ^ 3 = 1 := by simpa using congrArg Prod.fst hy3
      exact hne1 (eq_one_of_sq_cube (mul_eq_one_iff_eq_inv.mpr hinv) h13)
  intro τ hτT
  rcases hc.fix_or_swap (hTH (hT₁T hτT)) with ⟨h1, -⟩ | ⟨h12, h21⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h1
  exfalso
  have hτK : τ * x₁ * τ⁻¹ ∈ K₁ ⊔ K₂ :=
    conj_mem_of_mem_normalizer (hc.normal (hTH (hT₁T hτT))) hx₁K
  have hsw := hc.app_conj_swap h12 h21 hx₁K hτK
  rw [← hy] at hsw
  rcases hy12 with hy1' | hy2'
  · have hy2 : y.2 ≠ 1 := fun h => hy1 (Prod.ext hy1' h)
    have h2 := congrArg Prod.snd hsw
    simp only at h2
    rw [hy1', map_one] at h2
    rcases hact τ hτT hτK with h | h
    · rw [h] at h2
      exact hy2 h2
    · rw [h, Prod.snd_inv, inv_eq_one] at h2
      exact hy2 h2
  · have hy1'' : y.1 ≠ 1 := fun h => hy1 (Prod.ext h hy2')
    have h2 := congrArg Prod.fst hsw
    simp only at h2
    rw [hy2', map_one] at h2
    rcases hact τ hτT hτK with h | h
    · rw [h] at h2
      exact hy1'' h2
    · rw [h, Prod.fst_inv, inv_eq_one] at h2
      exact hy1'' h2

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
