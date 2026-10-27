module

public import CFSG.Quasithin.Vol2.Ch10SecE9F
public import CFSG.Quasithin.Vol2.Ch10SecQ34LK

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}


theorem exists_inner_witness {T T₁ : Subgroup G} (hc : C10P34.PairCtx H K₁ K₂ φ) {p : ℕ}
    [Fact p.Prime] (h8 : p % 8 = 3 ∨ p % 8 = 5) (e₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hT2 : IsPGroup 2 T) (hTH : T ≤ H)
    (hT₁T : T₁ ≤ T) (hST₁ : T ⊓ (K₁ ⊔ K₂) ≤ T₁) {n : G} (hnH : n ∈ H)
    (hnT₁ : n ∈ Subgroup.normalizer (T₁ : Set G)) (hodd : Odd (orderOf n)) :
    ∃ y ∈ K₁ ⊔ K₂, y ∈ Subgroup.normalizer (T₁ : Set G) ∧
      ∀ z ∈ K₁ ⊔ K₂, n * y⁻¹ * z * (n * y⁻¹)⁻¹ * z⁻¹ ∈ pCoreOf 2 (K₁ ⊔ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) := fun k hk => by
    have h1 : k ∈ φ.ker := hk
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hO : ∀ k : ↥(K₁ ⊔ K₂), (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) → φ k = 1 := fun k hk => by
    have h1 : k ∈ φ.ker := by rw [hc.ker, Subgroup.mem_subgroupOf]; exact hk
    exact h1
  have hZ : Subgroup.center ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)) = ⊥ := by
    rw [Subgroup.center_prod, hc.center₁, hc.center₂, Subgroup.bot_prod_bot]
  obtain ⟨hSyl₁, hSyl₂, -⟩ := map_sylow_eq_prod hc.surj hS
  obtain ⟨hn₁, hn₂⟩ := hc.fix_of_odd hnH hodd
  have hnK := hc.normal hnH
  obtain ⟨a₁, ha₁, ha₁o⟩ :=
    C10P34.exists_inner_of_pow_eq_one e₁ hodd (C10P34.conjQuot_pow_orderOf hn₁)
  obtain ⟨a₂, ha₂, ha₂o⟩ :=
    C10P34.exists_inner_of_pow_eq_one e₂ hodd (C10P34.conjQuot_pow_orderOf hn₂)
  have hconj : ∀ (z : G) (hz : z ∈ K₁ ⊔ K₂) (hz' : n * z * n⁻¹ ∈ K₁ ⊔ K₂),
      φ ⟨n * z * n⁻¹, hz'⟩ = (a₁ * (φ ⟨z, hz⟩).1 * a₁⁻¹, a₂ * (φ ⟨z, hz⟩).2 * a₂⁻¹) := by
    intro z hz hz'
    rw [hc.app_conj_fix hn₁ hn₂ hz, ← ha₁, ← ha₂]
    rfl
  have hnS : ∀ w ∈ T ⊓ (K₁ ⊔ K₂), n * w * n⁻¹ ∈ T ⊓ (K₁ ⊔ K₂) := fun w hw =>
    ⟨hT₁T ((Subgroup.mem_normalizer_iff.mp hnT₁ w).mp (hST₁ hw)),
      conj_mem_of_mem_normalizer hnK hw.2⟩
  have ha₁S : a₁ ∈ Subgroup.normalizer
      (((((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) :
        Subgroup _) : Set _) := C10P34.mem_normalizer_of_forall_conj_mem fun u hu => by
    obtain ⟨⟨w, hwK⟩, hw, hwu⟩ := hu
    have hw' := conj_mem_of_mem_normalizer hnK hwK
    refine ⟨⟨n * w * n⁻¹, hw'⟩, hnS w (Subgroup.mem_subgroupOf.mp hw), ?_⟩
    rw [MonoidHom.comp_apply, hconj w hwK hw', ← hwu]
    simp
  have ha₂S : a₂ ∈ Subgroup.normalizer
      (((((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) :
        Subgroup _) : Set _) := C10P34.mem_normalizer_of_forall_conj_mem fun u hu => by
    obtain ⟨⟨w, hwK⟩, hw, hwu⟩ := hu
    have hw' := conj_mem_of_mem_normalizer hnK hwK
    refine ⟨⟨n * w * n⁻¹, hw'⟩, hnS w (Subgroup.mem_subgroupOf.mp hw), ?_⟩
    rw [MonoidHom.comp_apply, hconj w hwK hw', ← hwu]
    simp
  have ha₁3 := pow_three_eq_one_of_mem_normalizer h8 e₁ hSyl₁ ha₁S ha₁o
  have ha₂3 := pow_three_eq_one_of_mem_normalizer h8 e₂ hSyl₂ ha₂S ha₂o
  have h3 : (a₁, a₂) ^ 3 = 1 := Prod.ext (by simpa using ha₁3) (by simpa using ha₂3)
  obtain ⟨y₀, hy₀⟩ := hc.surj (a₁, a₂)
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K₁ ⊔ K₂)).exists_card_eq
  set y : G := (y₀ : G) ^ (2 ^ j * 2 ^ j) with hy
  have hyK : y ∈ K₁ ⊔ K₂ := Subgroup.pow_mem _ y₀.2 _
  have hφy : φ ⟨y, hyK⟩ = (a₁, a₂) := by
    have e : (⟨y, hyK⟩ : ↥(K₁ ⊔ K₂)) = y₀ ^ (2 ^ j * 2 ^ j) := Subtype.ext (by simp [hy])
    rw [e, map_pow, hy₀, pow_four_pow_eq h3]
  refine ⟨y, hyK, ?_, fun z hz => ?_⟩
  ·
    have hyN : y ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hyK
    have hact : Alike φ y n := by
      intro z hz hg hh
      rw [map_conj_of_mem hyK hz hg, hφy, hconj z hz hh]
      rfl
    refine C10P34.mem_normalizer_of_forall_conj_mem fun t ht => ?_
    have htK := hc.normal (hTH (hT₁T ht))
    have hcK : y * t * y⁻¹ * t⁻¹ ∈ K₁ ⊔ K₂ := by
      rw [show y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) by group]
      exact (K₁ ⊔ K₂).mul_mem hyK (conj_mem_of_mem_normalizer htK ((K₁ ⊔ K₂).inv_mem hyK))
    have hd : n * t * n⁻¹ * t⁻¹ ∈ T₁ :=
      T₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hnT₁ t).mp ht) (T₁.inv_mem ht)
    have hdN : n * t * n⁻¹ * t⁻¹ ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnK htK)
        (Subgroup.inv_mem _ hnK)) (Subgroup.inv_mem _ htK)
    obtain ⟨k, hk⟩ := hT2 ⟨_, hT₁T hd⟩
    have hk' : (n * t * n⁻¹ * t⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdS : ∀ x ∈ T ⊓ (K₁ ⊔ K₂), (n * t * n⁻¹ * t⁻¹) * x * (n * t * n⁻¹ * t⁻¹)⁻¹ ∈
        T ⊓ (K₁ ⊔ K₂) := fun x hx =>
      ⟨T.mul_mem (T.mul_mem (hT₁T hd) hx.1) (T.inv_mem (hT₁T hd)),
        conj_mem_of_mem_normalizer hdN hx.2⟩
    have hcd := Alike.comm hker hO hyN hnK htK hact
    have hdc : ∀ (z : G) (hz : z ∈ K₁ ⊔ K₂)
        (hz' : (n * t * n⁻¹ * t⁻¹) * z * (n * t * n⁻¹ * t⁻¹)⁻¹ ∈ K₁ ⊔ K₂),
        φ ⟨(n * t * n⁻¹ * t⁻¹) * z * (n * t * n⁻¹ * t⁻¹)⁻¹, hz'⟩ =
          φ ⟨y * t * y⁻¹ * t⁻¹, hcK⟩ * φ ⟨z, hz⟩ * (φ ⟨y * t * y⁻¹ * t⁻¹, hcK⟩)⁻¹ := by
      intro z hz hz'
      have hcz := conj_mem_of_mem_normalizer (Subgroup.le_normalizer hcK) hz
      rw [← hcd z hz hcz hz', map_conj_of_mem hcK hz hcz]
    have hcS := mem_of_conj_eq_inner hc.surj hker hZ hS
      (fun u hu k hk => mem_of_mem_normalizer_of_pow hSyl₁ hu hk)
      (fun u hu k hk => mem_of_mem_normalizer_of_pow hSyl₂ hu hk) hdN hk' hdS hcK hdc
    have e : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact T₁.mul_mem (hST₁ hcS) ht
  ·
    have hz' : y⁻¹ * z * y ∈ K₁ ⊔ K₂ :=
      (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).inv_mem hyK) hz) hyK
    have hz'' : n * (y⁻¹ * z * y) * n⁻¹ ∈ K₁ ⊔ K₂ := conj_mem_of_mem_normalizer hnK hz'
    have h1 := hconj _ hz' hz''
    have h2 : φ ⟨y⁻¹ * z * y, hz'⟩ = (φ ⟨y, hyK⟩)⁻¹ * φ ⟨z, hz⟩ * φ ⟨y, hyK⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e : n * y⁻¹ * z * (n * y⁻¹)⁻¹ * z⁻¹ = n * (y⁻¹ * z * y) * n⁻¹ * z⁻¹ := by group
    rw [e]
    have h3' : φ (⟨n * (y⁻¹ * z * y) * n⁻¹, hz''⟩ * (⟨z, hz⟩ : ↥(K₁ ⊔ K₂))⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, h2, hφy]
      exact Prod.ext (by simp; group) (by simp; group)
    exact hker _ h3'

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
