module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LK
public import CFSG.Quasithin.Vol2.Ch10SecQ34LF

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_odd_pair {H K₁ K₂ X T T₁ : Subgroup G}
    {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}
    (hc : PairCtx H K₁ K₂ φ) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hXK : X ≤ K₁ ⊔ K₂) (hXO : oTwoUpper X = X) (hX3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT₁T : T₁ ≤ T) (hW : pCoreOf 2 (X ⊔ T ⊓ (K₁ ⊔ K₂)) ≤ T₁ ⊓ (K₁ ⊔ K₂))
    (h8 : p % 8 = 3 ∨ p % 8 = 5 →
      pCoreOf 2 ((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) ≠ ⊥ ∧
      pCoreOf 2 ((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) ≠ ⊥)
    {n : G} (hnH : n ∈ H) (hnT₁ : n ∈ Subgroup.normalizer (T₁ : Set G))
    (hodd : Odd (orderOf n)) : n ∈ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) := fun k hk => by
    have h1 : k ∈ φ.ker := hk
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨hn₁, hn₂⟩ := hc.fix_of_odd hnH hodd
  have hnK : n ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hc.normal hnH
  obtain ⟨a₁, ha₁, ha₁o⟩ := exists_inner_of_pow_eq_one e₁ hodd (conjQuot_pow_orderOf hn₁)
  obtain ⟨a₂, ha₂, ha₂o⟩ := exists_inner_of_pow_eq_one e₂ hodd (conjQuot_pow_orderOf hn₂)
  have hconj : ∀ (z : G) (hz : z ∈ K₁ ⊔ K₂),
      φ ⟨n * z * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnK z).mp hz⟩ =
        (a₁ * (φ ⟨z, hz⟩).1 * a₁⁻¹, a₂ * (φ ⟨z, hz⟩).2 * a₂⁻¹) := by
    intro z hz
    rw [hc.app_conj_fix hn₁ hn₂ hz, ← ha₁, ← ha₂]
    rfl
  have hnR : ∀ r ∈ T₁ ⊓ (K₁ ⊔ K₂), n * r * n⁻¹ ∈ T₁ ⊓ (K₁ ⊔ K₂) := fun r hr =>
    ⟨(Subgroup.mem_normalizer_iff.mp hnT₁ r).mp hr.1,
      (Subgroup.mem_normalizer_iff.mp hnK r).mp hr.2⟩
  have hRS : ∀ k : ↥(K₁ ⊔ K₂), k ∈ (T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂) →
      k ∈ (T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂) := fun k hk => ⟨hT₁T hk.1, hk.2⟩
  have hWR : ∀ k : ↥(K₁ ⊔ K₂), k ∈ (pCoreOf 2 (X ⊔ T ⊓ (K₁ ⊔ K₂))).subgroupOf (K₁ ⊔ K₂) →
      k ∈ (T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂) := fun k hk => hW hk
  obtain ⟨hSyl₁, hSyl₂, -⟩ := map_sylow_eq_prod hc.surj hS
  have hSX : T ⊓ (K₁ ⊔ K₂) ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have ha₁Y := mem_normalizer_of_odd hp5 e₁ hSyl₁ (map_le_normalizer_map _ hSX hXK)
    (fst_ne_bot hp5 e₂ hker hXK hXO hX3 hPX hP hP3) (oTwoUpper_map_eq _ hXK hXO)
    (pow_three_mem_map _ hXK hX3) (Subgroup.map_mono hRS)
    ((pCoreOf_sup_le_map_fst hc.surj hker hS hXK).trans (Subgroup.map_mono hWR))
    (fun h => (h8 h).1) (a := a₁) (mem_normalizer_of_forall_conj_mem fun r hr => by
      obtain ⟨⟨w, hwK⟩, hw, rfl⟩ := hr
      refine ⟨⟨n * w * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnK w).mp hwK⟩, hnR w hw, ?_⟩
      rw [MonoidHom.comp_apply, hconj w hwK]
      rfl) ha₁o
  have ha₂Y := mem_normalizer_of_odd hp5 e₂ hSyl₂ (map_le_normalizer_map _ hSX hXK)
    (snd_ne_bot hp5 e₁ hker hXK hXO hX3 hPX hP hP3) (oTwoUpper_map_eq _ hXK hXO)
    (pow_three_mem_map _ hXK hX3) (Subgroup.map_mono hRS)
    ((pCoreOf_sup_le_map_snd hc.surj hker hS hXK).trans (Subgroup.map_mono hWR))
    (fun h => (h8 h).2) (a := a₂) (mem_normalizer_of_forall_conj_mem fun r hr => by
      obtain ⟨⟨w, hwK⟩, hw, rfl⟩ := hr
      refine ⟨⟨n * w * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnK w).mp hwK⟩, hnR w hw, ?_⟩
      rw [MonoidHom.comp_apply, hconj w hwK]
      rfl) ha₂o
  have hON : pCoreOf 2 (K₁ ⊔ K₂) ≤ Subgroup.normalizer (X : Set G) :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS).trans hSX
  have hXprod := map_eq_prod hp5 e₁ e₂ hker hXK hXO hX3 hPX hP hP3
  have hgen : ∀ x ∈ X, Odd (orderOf x) → n * x * n⁻¹ ∈ X := by
    intro x hx hxo
    have hxK := hXK hx
    refine mem_of_odd_of_mem_map hker hON hXO ((Subgroup.mem_normalizer_iff.mp hnK x).mp hxK)
      ?_ ?_
    · rw [show n * x * n⁻¹ = MulAut.conj n x from rfl, MulEquiv.orderOf_eq]
      exact hxo
    · rw [hconj x hxK, hXprod]
      exact ⟨(Subgroup.mem_normalizer_iff.mp ha₁Y _).mp ⟨⟨x, hxK⟩, hx, rfl⟩,
        (Subgroup.mem_normalizer_iff.mp ha₂Y _).mp ⟨⟨x, hxK⟩, hx, rfl⟩⟩
  have hle : X.map (MulAut.conj n).toMonoidHom ≤ X := by
    conv_lhs => rw [← hXO]
    rw [oTwoUpper, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨hx, hxo⟩, rfl⟩
    exact hgen x hx hxo
  exact mem_normalizer_of_forall_conj_mem fun x hx => hle ⟨x, hx, rfl⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
