module

public import CFSG.Milestones.ASVolI.F411.Ident
public import CFSG.Milestones.ASVolI.F411.Trans
public import CFSG.Milestones.ASVolI.F4TISets

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.F7

section Sylow

variable {E : Type} [Group E]

theorem burnsideF411_exists_conj_mem_sylow [Finite E] {p : ℕ} [Fact p.Prime] {S P : Subgroup E}
    (hS : ChF.IsSylowOf p S P) {x : E} (hxP : x ∈ P) {k : ℕ} (hk : orderOf x = p ^ k) :
    ∃ a ∈ P, a⁻¹ * x * a ∈ S := by
  classical
  obtain ⟨hSP, hSp, hSi⟩ := hS
  let x' : ↥P := ⟨x, hxP⟩
  have hx'k : orderOf x' = p ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_mk x hxP
  have hH : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hx'k])
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  let A : Subgroup ↥P := S.subgroupOf P
  have hAp : IsPGroup p A := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
  have hAi : ¬ p ∣ A.index := hSi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P (hAp.toSylow hAi) Q
  have hxQ : x' ∈ (Q : Subgroup ↥P) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨t, ht, hteq⟩ := hxQ
  refine ⟨(g : E), g.2, ?_⟩
  have h1 : ((g : E) * (t : E) * (g : E)⁻¹) = x := by
    have := congrArg Subtype.val hteq
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have h2 : (g : E)⁻¹ * x * (g : E) = (t : E) := by
    rw [← h1]
    group
  rw [h2]
  exact ht

theorem burnsideF411_oPPrime_le_sylow [Finite E] {p : ℕ} [Fact p.Prime] {S B Gp : Subgroup E}
    (hS : ChF.IsSylowOf p S Gp) (hSB : S ≤ B) (hBGp : B ≤ Gp)
    (hBN : B ≤ Subgroup.normalizer (S : Set E)) : oPPrime p B ≤ S := by
  rw [oPPrime, Subgroup.closure_le]
  rintro x ⟨hxB, k, hk⟩
  have hZ : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hZN : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set E) :=
    (Subgroup.zpowers_le).mpr (hBN hxB)
  have hp : IsPGroup p (S ⊔ Subgroup.zpowers x : Subgroup E) :=
    IsPGroup.to_sup_of_normal_left' hS.2.1 hZ hZN
  have hle : S ⊔ Subgroup.zpowers x ≤ Gp :=
    sup_le hS.1 ((Subgroup.zpowers_le).mpr (hBGp hxB))
  have heq := burnsideF411_eq_of_isSylowOf hS le_sup_left hle hp
  have : x ∈ S ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [heq] at this

theorem burnsideF411_rankOne_of_trans [Finite E] {p : ℕ} [Fact p.Prime] {Gp B P : Subgroup E}
    (hBP : B ≤ P) (hPGp : P ≤ Gp)
    (htr : ∀ a₁ ∈ P, ∀ a₂ ∈ P, a₁ ∉ B → a₂ ∉ B → ∃ s ∈ oPPrime p B, a₂⁻¹ * s * a₁ ∈ B)
    {S : Subgroup E} (hS : ChF.IsSylowOf p S Gp) (hSB : S ≤ B)
    (hBN : B ≤ Subgroup.normalizer (S : Set E)) {Y : Subgroup E} (hSY : S ≤ Y) (hYP : Y ≤ P)
    (hYB : ¬ Y ≤ B) : oPPrime p P ≤ Y := by
  have hOB : oPPrime p B ≤ S := burnsideF411_oPPrime_le_sylow hS hSB (hBP.trans hPGp) hBN
  obtain ⟨y, hyY, hyB⟩ := Set.not_subset.mp hYB
  have hSP : ChF.IsSylowOf p S P := burnsideF411_isSylowOf_of_le hS (hSB.trans hBP) hPGp
  rw [oPPrime, Subgroup.closure_le]
  rintro x ⟨hxP, k, hk⟩
  obtain ⟨a, haP, hxa⟩ := burnsideF411_exists_conj_mem_sylow hSP hxP hk
  by_cases haB : a ∈ B
  · have hx : x ∈ S := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hBN haB) _).mp hxa
      have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
      rwa [e] at h1
    exact hSY hx
  · obtain ⟨s, hs, hb⟩ := htr y (hYP hyY) a haP hyB haB
    have hsY : s ∈ Y := hSY (hOB hs)
    have ht : (a⁻¹ * s * y)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * s * y) ∈ S := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hBN (B.inv_mem hb)) _).mp hxa
      rwa [inv_inv] at h1
    have e : x = s * y * ((a⁻¹ * s * y)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * s * y)) * y⁻¹ * s⁻¹ := by
      group
    rw [e]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hsY hyY) (hSY ht)) (Y.inv_mem hyY))
      (Y.inv_mem hsY)

end Sylow


theorem burnsideF411_rankOne_of_F45 (h45 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    burnsideF411_RankOne p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) ∧
      burnsideF411_RankOne p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₂) := by
  haveI : Finite E := hyp.finite
  have hp : p.Prime := burnsideF4a_prime_of_isGenLie hyp.model
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨S₀, hS₀, hB⟩, -, -, hmax⟩ := burnsideF4j_parabolics hcompat hyp
  obtain ⟨hBP₁, hP₁Gp, -, -⟩ := (hmax (Gp ⊓ M₁)).mpr (Or.inl rfl)
  obtain ⟨hBP₂, hP₂Gp, -, -⟩ := (hmax (Gp ⊓ M₂)).mpr (Or.inr rfl)
  have hyp' := burnsideF4j_restrict hcompat hyp
  have F' := h45 κ p f ↥Gp ⊤ ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp) hyp'
    (incl ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp)) rfl
  have C6 := F'.2.2.2.2.2.1 rfl
  have TrA₁ := burnsideF411_trans_of_c6_xv hp hyp'.gen (C6 _ _ CosetGeom.adj_γ₀_γ₁).2.2.1
  have TrA₂ := burnsideF411_trans_of_c6_lv hp hyp'.gen (C6 _ _ CosetGeom.adj_γ₀_γ₁.symm).2.2.1
  have hOmap : ∀ s ∈ oPPrime p ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp),
      (s : E) ∈ oPPrime p (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro s hs
    have h1 := burnsideF45_oPPrime_map_le hp Gp.subtype _ ⟨s, hs, rfl⟩
    refine burnsideF411_oPPrime_mono p ?_ h1
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨hy1.1, hy1.2, hy2.2⟩
  have TrE₁ : ∀ a₁ ∈ Gp ⊓ M₁, ∀ a₂ ∈ Gp ⊓ M₁, a₁ ∉ Gp ⊓ (M₁ ⊓ M₂) → a₂ ∉ Gp ⊓ (M₁ ⊓ M₂) →
      ∃ s ∈ oPPrime p (Gp ⊓ (M₁ ⊓ M₂)), a₂⁻¹ * s * a₁ ∈ Gp ⊓ (M₁ ⊓ M₂) := by
    intro a₁ ha₁ a₂ ha₂ hn₁ hn₂
    obtain ⟨s, hs, hsa⟩ := TrA₁ ⟨a₁, ha₁.1⟩ ha₁ ⟨a₂, ha₂.1⟩ ha₂
      (fun h => hn₁ ⟨ha₁.1, ha₁.2, h.2⟩) (fun h => hn₂ ⟨ha₂.1, ha₂.2, h.2⟩)
    refine ⟨s, hOmap s hs, ?_⟩
    have hsB : (s : E) ∈ Gp ⊓ (M₁ ⊓ M₂) := burnsideF411_oPPrime_le p _ (hOmap s hs)
    have h2 : a₂⁻¹ * (s : E) * a₁ ∈ Gp ⊓ M₂ := hsa
    exact ⟨h2.1, M₁.mul_mem (M₁.mul_mem (M₁.inv_mem ha₂.2) hsB.2.1) ha₁.2, h2.2⟩
  have TrE₂ : ∀ a₁ ∈ Gp ⊓ M₂, ∀ a₂ ∈ Gp ⊓ M₂, a₁ ∉ Gp ⊓ (M₁ ⊓ M₂) → a₂ ∉ Gp ⊓ (M₁ ⊓ M₂) →
      ∃ s ∈ oPPrime p (Gp ⊓ (M₁ ⊓ M₂)), a₂⁻¹ * s * a₁ ∈ Gp ⊓ (M₁ ⊓ M₂) := by
    intro a₁ ha₁ a₂ ha₂ hn₁ hn₂
    obtain ⟨s, hs, hsa⟩ := TrA₂ ⟨a₁, ha₁.1⟩ ha₁ ⟨a₂, ha₂.1⟩ ha₂
      (fun h => hn₁ ⟨ha₁.1, h.2, ha₁.2⟩) (fun h => hn₂ ⟨ha₂.1, h.2, ha₂.2⟩)
    refine ⟨s, hOmap s hs, ?_⟩
    have hsB : (s : E) ∈ Gp ⊓ (M₁ ⊓ M₂) := burnsideF411_oPPrime_le p _ (hOmap s hs)
    have h2 : a₂⁻¹ * (s : E) * a₁ ∈ Gp ⊓ M₁ := hsa
    exact ⟨h2.1, h2.2, M₂.mul_mem (M₂.mul_mem (M₂.inv_mem ha₂.2) hsB.2.2) ha₁.2⟩
  have hBN : ∀ S : Subgroup E, ChF.IsSylowOf p S Gp → S ≤ Gp ⊓ (M₁ ⊓ M₂) →
      Gp ⊓ (M₁ ⊓ M₂) ≤ Subgroup.normalizer (S : Set E) := by
    intro S hS hSB
    have hSN : S ≤ Subgroup.normalizer (S₀ : Set E) := fun x hx => (hB ▸ hSB hx).2
    have hp' : IsPGroup p (S₀ ⊔ S : Subgroup E) :=
      IsPGroup.to_sup_of_normal_left' hS₀.2.1 hS.2.1 hSN
    have hle : S₀ ⊔ S ≤ Gp := sup_le hS₀.1 hS.1
    have e1 := burnsideF411_eq_of_isSylowOf hS₀ le_sup_left hle hp'
    have e2 := burnsideF411_eq_of_isSylowOf hS le_sup_right hle hp'
    have hSS : S = S₀ := e2.symm.trans e1
    rw [hSS, hB]
    exact inf_le_right
  exact ⟨fun S hS hSB Y hSY hYP hYB => burnsideF411_rankOne_of_trans hBP₁ hP₁Gp TrE₁ hS hSB
      (hBN S hS hSB) hSY hYP hYB,
    fun S hS hSB Y hSY hYP hYB => burnsideF411_rankOne_of_trans hBP₂ hP₂Gp TrE₂ hS hSB
      (hBN S hS hSB) hSY hYP hYB⟩

end CFSG.ASVolI
