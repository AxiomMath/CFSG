module

public import CFSG.Quasithin.Vol2.Ch10SecABasicProd
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_eq_of_normal {K X : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) : K ⊓ pCoreOf 2 X = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) ?_)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hKX hk)) z
    have h2 : z ∈ K ↔ k * z * k⁻¹ ∈ K := by
      constructor
      · intro hz
        exact K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk)
      · intro hz
        have := K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk
        simpa [mul_assoc] using this
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKX)
      (hXK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem exists_pair_prod (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {H K₁ K₂ : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (h₁ : K₁ ∈ cComp H) (h₂ : K₂ ∈ cComp H)
    (hne : K₁ ≠ K₂) (hc₁ : Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = ⊥)
    (hc₂ : Subgroup.center (↥K₂ ⧸ CFSG.pCore 2 ↥K₂) = ⊥) :
    ∃ φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂),
      Function.Surjective φ ∧ φ.ker = (pCoreOf 2 (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂) ∧
      (∀ (k : G) (hk : k ∈ K₁), φ ⟨k, Subgroup.mem_sup_left hk⟩ =
        (((⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁), 1)) ∧
      ∀ (k : G) (hk : k ∈ K₂), φ ⟨k, Subgroup.mem_sup_right hk⟩ =
        (1, ((⟨k, hk⟩ : ↥K₂) : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, -⟩ := Vol2Native.lemma_1_2_1_two hK h37 hH h₁ h₂ hne
  set O := pCoreOf 2 (K₁ ⊔ K₂) with hOdef
  have hOK : O ≤ K₁ ⊔ K₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hNO : K₁ ⊔ K₂ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have h21 : K₂ ≤ Subgroup.normalizer (K₁ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((hcomm.trans inf_le_left).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁))
  have h12 : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((hcomm.trans inf_le_right).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K₂))
  have hN₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer h21
  have hN₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set G) := sup_le h12 Subgroup.le_normalizer
  have hinf₁ := inf_pCoreOf_eq_of_normal le_sup_left hN₁
  have hinf₂ := inf_pCoreOf_eq_of_normal le_sup_right hN₂
  have hs₁ : K₁ ⊓ (K₂ ⊔ O) = pCoreOf 2 K₁ :=
    SecA.inf_sup_pCoreOf_eq hc₁ le_sup_left le_sup_right hOK hN₁ (le_sup_left.trans hNO)
      (hcomm.trans inf_le_left) hinf₁
  have hs₂ : K₂ ⊓ (K₁ ⊔ O) = pCoreOf 2 K₂ :=
    SecA.inf_sup_pCoreOf_eq hc₂ le_sup_right le_sup_left hOK hN₂ (le_sup_right.trans hNO)
      ((Subgroup.commutator_comm K₂ K₁).le.trans (hcomm.trans inf_le_right)) hinf₂
  obtain ⟨φ₁, hsj₁, hk₁, hK₁₁, hK₂₁⟩ := SecA.exists_proj le_sup_left le_sup_right hOK
    (sup_le le_sup_left (le_sup_left.trans le_sup_right)) (SecA.le_normalizer_sup hN₂ hNO) hs₁
  obtain ⟨φ₂, hsj₂, hk₂, hK₂₂, hK₁₂⟩ := SecA.exists_proj le_sup_right le_sup_left hOK
    (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (SecA.le_normalizer_sup hN₁ hNO) hs₂
  have hint : (K₂ ⊔ O) ⊓ (K₁ ⊔ O) = O := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_right)
    have hx2 : x ∈ ((K₁ ⊔ O : Subgroup G) : Set G) := hx.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ O (le_sup_left.trans hNO)] at hx2
    obtain ⟨l, hl, o, ho, rfl⟩ := hx2
    have hl' : l ∈ K₂ ⊔ O := by
      have := (K₂ ⊔ O).mul_mem hx.1 (Subgroup.mem_sup_right (O.inv_mem ho))
      simpa using this
    have hlO : l ∈ pCoreOf 2 K₁ := by
      rw [← hs₁]
      exact ⟨hl, hl'⟩
    rw [← hinf₁] at hlO
    exact O.mul_mem hlO.2 ho
  refine ⟨φ₁.prod φ₂, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rintro ⟨a, b⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨⟨l', hl'⟩, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨l, Subgroup.mem_sup_left hl⟩ * ⟨l', Subgroup.mem_sup_right hl'⟩, ?_⟩
    rw [map_mul, MonoidHom.prod_apply, MonoidHom.prod_apply, hK₁₁ l hl, hK₁₂ l hl, hK₂₁ l' hl',
      hK₂₂ l' hl']
    simp
  · rw [MonoidHom.ker_prod, hk₁, hk₂]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← Subgroup.mem_inf, hint]
  · rw [MonoidHom.prod_apply, hK₁₁ k hk, hK₁₂ k hk]
  · rw [MonoidHom.prod_apply, hK₂₁ k hk, hK₂₂ k hk]

end CFSG.Quasithin.Vol2.Ch10.SecB
