module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Clos
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Act

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T B : Subgroup G}

omit [Finite G] in
theorem le_perfectCore_of_lFamily (hB : B ∈ lFamily T) : B ≤ perfectCore (B ⊔ T) := by
  have hBM : B ∈ cComp (B ⊔ T) := hB
  calc B = perfectCore B := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hBM)).symm
    _ ≤ perfectCore (B ⊔ T) := perfectCore_mono (le_of_mem_cComp hBM)

omit [Finite G] in
theorem odd_mem_perfectCore (hT : IsPGroup 2 T) (hB : B ∈ lFamily T) {x : G}
    (hx : x ∈ B ⊔ T) {m : ℕ} (hm : m % 2 = 1) (hxm : x ^ m = 1) : x ∈ perfectCore (B ⊔ T) := by
  set Z := B ⊔ T with hZ
  set A := perfectCore Z with hA
  have hBA : B ≤ A := le_perfectCore_of_lFamily hB
  have hAZ : A ≤ Z := perfectCore_le Z
  have hTZ : T ≤ Z := le_sup_right
  have hBZ : B ≤ Z := le_sup_left
  have hAnorm : (A.subgroupOf Z).Normal := perfectCore_normal Z
  set N : Subgroup ↥Z := A.subgroupOf Z with hN
  have : N.Normal := hAnorm
  have hsup : B.subgroupOf Z ⊔ T.subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBZ hTZ, ← hZ, Subgroup.subgroupOf_self]
  have hBN : B.subgroupOf Z ≤ N := fun b hb => hBA hb
  have hmapB : (B.subgroupOf Z).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hBN
  have htop : (T.subgroupOf Z).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hsup
    rw [Subgroup.map_sup, hmapB, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1
  have hT' : IsPGroup 2 ↥(T.subgroupOf Z) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTZ).symm
  have hQ : IsPGroup 2 (↥Z ⧸ N) := by
    refine hT'.of_surjective ((QuotientGroup.mk' N).comp (T.subgroupOf Z).subtype) fun q => ?_
    have hq : q ∈ (T.subgroupOf Z).map (QuotientGroup.mk' N) := by
      rw [htop]
      exact Subgroup.mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hg : (⟨x, hx⟩ : ↥Z) ^ m = 1 := Subtype.ext (by simpa using hxm)
  exact mem_of_pow_eq_one_odd N hQ hm hg

omit [Finite G] in
theorem comm_mem_perfectCore {x u : G} (hx : x ∈ B ⊔ T) (hu : u ∈ perfectCore (B ⊔ T)) :
    ⁅x, u⁆ ∈ perfectCore (B ⊔ T) := by
  have hnorm : ((perfectCore (B ⊔ T)).subgroupOf (B ⊔ T)).Normal := perfectCore_normal _
  have h1 : (⟨x, hx⟩ : ↥(B ⊔ T)) * ⟨u, perfectCore_le _ hu⟩ * ⟨x, hx⟩⁻¹ ∈
      (perfectCore (B ⊔ T)).subgroupOf (B ⊔ T) :=
    hnorm.conj_mem _ hu _
  have h2 : x * u * x⁻¹ ∈ perfectCore (B ⊔ T) := h1
  rw [commutatorElement_def]
  have := Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hu)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_perfectCore_of_commutators (hT : IsPGroup 2 T) (hB : B ∈ lFamily T)
    {V : Subgroup G} (hVZ : V ≤ B ⊔ T) {u : G} (hu : u ∈ B ⊔ T) {m : ℕ} (hm : m % 2 = 1)
    (hum : u ^ m = 1) (hV : ∀ v ∈ V, ∃ x ∈ V, ⁅x, u⁆ = v) : V ≤ perfectCore (B ⊔ T) := by
  intro v hv
  obtain ⟨x, hxV, rfl⟩ := hV v hv
  exact comm_mem_perfectCore (hVZ hxV) (odd_mem_perfectCore hT hB hu hm hum)

omit [Finite G] in
theorem le_perfectCore_of_commutators_z (hT : IsPGroup 2 T) (hB : B ∈ lFamily T)
    {V : Subgroup G} (hVZ : V ≤ B ⊔ T) {u z c₁ c₂ : G} (hu : u ∈ B ⊔ T) {m : ℕ}
    (hm : m % 2 = 1) (hum : u ^ m = 1) (hc₁ : ∃ x ∈ V, ⁅x, u⁆ = c₁) (hc₂ : ∃ x ∈ V, ⁅x, u⁆ = c₂)
    (hz : ⁅c₁, c₂⁆ = z) (hV : ∀ v ∈ V, ∃ x ∈ V, ⁅x, u⁆ = v ∨ ⁅x, u⁆ = v * z) :
    V ≤ perfectCore (B ⊔ T) := by
  have hP : ∀ x ∈ V, ⁅x, u⁆ ∈ perfectCore (B ⊔ T) := fun x hx =>
    comm_mem_perfectCore (hVZ hx) (odd_mem_perfectCore hT hB hu hm hum)
  have hzP : z ∈ perfectCore (B ⊔ T) := by
    obtain ⟨x₁, hx₁, rfl⟩ := hc₁
    obtain ⟨x₂, hx₂, rfl⟩ := hc₂
    rw [← hz, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hP x₁ hx₁) (hP x₂ hx₂))
      (Subgroup.inv_mem _ (hP x₁ hx₁))) (Subgroup.inv_mem _ (hP x₂ hx₂))
  intro v hv
  obtain ⟨x, hx, h | h⟩ := hV v hv
  · rw [← h]
    exact hP x hx
  · have : v = ⁅x, u⁆ * z⁻¹ := by rw [h]; group
    rw [this]
    exact Subgroup.mul_mem _ (hP x hx) (Subgroup.inv_mem _ hzP)

end CFSG.Quasithin.A312M24
