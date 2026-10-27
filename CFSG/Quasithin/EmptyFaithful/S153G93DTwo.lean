module

public import CFSG.Quasithin.EmptyFaithful.S153G93DFacTwo
public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.Quasithin.Background.B69Red
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.Quasithin.EmptyFaithful.S153G93DCases

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

@[expose] def D37Core : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U] (X L₁ L₂ : Subgroup (MulAut U)) (s : MulAut U),
    SmithD37.Core X L₁ L₂ s → (∃ a b : ↥L₁, a * b ≠ b * a) →
      (∃ n, IsPSL 2 2 n ↥L₁ ∧ Omega4PlusModule (L₁ ⊔ L₂) n) ∨
        (IsPSL 3 2 1 ↥L₁ ∧ TensorNatL32 (L₁ ⊔ L₂))

section Helpers

variable {G : Type*} [Group G]

theorem le_normalizer_of_comm {L M : Subgroup G} (h : ∀ x ∈ L, ∀ y ∈ M, x * y = y * x) :
    M ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : y * x * y⁻¹ = x := by
      have := h x hx y hy
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [this]
        _ = x := by group
    rw [e]
    exact hx
  · intro hx
    have h1 := h _ hx y⁻¹ (M.inv_mem hy)
    have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    have e2 : y⁻¹ * (y * x * y⁻¹) * y = y * x * y⁻¹ := by
      calc y⁻¹ * (y * x * y⁻¹) * y = (y * x * y⁻¹) * y⁻¹ * y := by rw [← h1]
        _ = y * x * y⁻¹ := by group
    rw [e, e2]
    exact hx

theorem le_normalizer_of_normalizes {H K : Subgroup G}
    (hK : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨hK g hg k, fun h => ?_⟩
  have := hK g⁻¹ (H.inv_mem hg) _ h
  have e : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
  rwa [e] at this

theorem exists_ne_one_of_sylow_simple [Finite G] {L S : Subgroup G} (hS : IsSylowTwoOf S L)
    [hL : IsSimpleGroup ↥L] (hnc : ∃ x y : ↥L, x * y ≠ y * x) : ∃ x ∈ S, x ≠ 1 := by
  by_contra hall
  push Not at hall
  have hbot : S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hall x hx
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnc).1
  have h2 := hS.2.2
  rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h2
  exact h2 (even_iff_two_dvd.mp heven)

end Helpers

section TwoDataG

variable {W : Type} [CommGroup W] [Finite W] {H K T' L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem TwoDataG.a_normalizes (hd : TwoDataG H K T' L₁ L₂ t) (hKH : K ≤ H)
    (hKnorm : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hT' : IsSylowTwoOf T' H) {a : MulAut W}
    (haH : a ∈ H) (hcT' : ∀ x ∈ T', x * a = a * x) :
    (L₁.map (MulAut.conj a).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj a).toMonoidHom = L₂) ∧
      IsSylowTwoOf (T' ⊓ K ⊓ L₁) L₁ ∧ IsSylowTwoOf (T' ⊓ K ⊓ L₂) L₂ := by
  have hKn : H ≤ Subgroup.normalizer (K : Set (MulAut W)) := le_normalizer_of_normalizes hKnorm
  have hS : IsSylowTwoOf (T' ⊓ K) K := A4.isSylowTwoOf_inf_normal hT' hKH hKn
  have hL₁K : L₁ ≤ K := hd.sup ▸ le_sup_left
  have hL₂K : L₂ ≤ K := hd.sup ▸ le_sup_right
  have hKL₁ : K ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    rw [hd.sup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_comm hd.comm)
  have hKL₂ : K ≤ Subgroup.normalizer (L₂ : Set (MulAut W)) := by
    rw [hd.sup]
    exact sup_le (le_normalizer_of_comm fun x hx y hy => (hd.comm y hy x hx).symm)
      Subgroup.le_normalizer
  have hS₁ : IsSylowTwoOf (T' ⊓ K ⊓ L₁) L₁ := A4.isSylowTwoOf_inf_normal hS hL₁K hKL₁
  have hS₂ : IsSylowTwoOf (T' ⊓ K ⊓ L₂) L₂ := A4.isSylowTwoOf_inf_normal hS hL₂K hKL₂
  have := hd.simple₁
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_sylow_simple hS₁ hd.nab₁
  rcases hd.perm a haH with h | ⟨h1, -⟩
  · exact ⟨h, hS₁, hS₂⟩
  · exfalso
    have hxT : x ∈ T' := hx.1.1
    have hxa : a * x * a⁻¹ = x := by
      have := hcT' x hxT
      calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [this]
        _ = x := by group
    have hxL₁ : x ∈ L₁ := hx.2
    have hmem : a * x * a⁻¹ ∈ L₁.map (MulAut.conj a).toMonoidHom := ⟨x, hxL₁, rfl⟩
    rw [h1, hxa] at hmem
    have hx12 : x ∈ L₁ ⊓ L₂ := ⟨hxL₁, hmem⟩
    rw [hd.inf, Subgroup.mem_bot] at hx12
    exact hx1 hx12

theorem core_of_twoDataG (hA21 : AsA21SQTKSection) (hq : G64.IsQuotientOfSQTKCat ↥H) (hKH : K ≤ H)
    (hKnorm : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hT' : IsSylowTwoOf T' H)
    (hd : TwoDataG H K T' L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1) (hbig : 2 ^ 6 ≤ Nat.card W)
    (hirr : IsIrrOn153 K ⊤) (hqhat : qhatOf (K ⊔ T') ≤ ((2 : ℚ) : WithTop ℚ)) :
    SmithD37.Core (K ⊔ T') L₁ L₂ t := by
  have hL₁K : L₁ ≤ K := hd.sup ▸ le_sup_left
  have hL₂K : L₂ ≤ K := hd.sup ▸ le_sup_right
  have hKX : K ≤ K ⊔ T' := le_sup_left
  have hTX : T' ≤ K ⊔ T' := le_sup_right
  have hXH : K ⊔ T' ≤ H := sup_le hKH hT'.1
  have hKn : H ≤ Subgroup.normalizer (K : Set (MulAut W)) := le_normalizer_of_normalizes hKnorm
  obtain ⟨Y, _, _, φ, hY, hφ⟩ : ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : Y →* ↥H),
      SQTKGroup Y ∧ Function.Surjective φ := by
    obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := hq
    exact ⟨Y, inferInstance, inferInstance,
      e.symm.toMonoidHom.comp (QuotientGroup.mk' N),
      ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp hY.1, hY.2⟩,
      e.symm.surjective.comp (QuotientGroup.mk'_surjective N)⟩
  have hnt : Nontrivial W := by
    have : 1 < Nat.card W := lt_of_lt_of_le (by norm_num) hbig
    exact Finite.one_lt_card_iff_nontrivial.mp this
  refine ⟨hexp, hnt, hd.a38, hd.simple₁, B69.sqtk_subgroup hA21 hY φ hφ (hL₁K.trans hKH) hd.quasi₁,
    hd.comm, hd.inf, hL₁K.trans hKX, hL₂K.trans hKX, hTX hd.tT, hd.swap₁, hd.swap₂,
    fun x hx => hd.perm x (hXH hx), ?_, ?_, ?_, hqhat⟩
  · intro x hx
    obtain ⟨e, he⟩ := exists_pow_mem_of_sup hT'.2.1 (hT'.1.trans hKn) x hx
    exact ⟨e, hd.sup ▸ he⟩
  · exact S153EB6.pCoreOf_two_eq_bot_of_irr hexp hKX fun B hB => hirr.2.2 B le_top hB
  · intro J hJ
    exact hirr.2.2 J le_top (fun k hk u hu => hJ k (hd.sup ▸ hk) u hu)

theorem twoCtx_of_twoDataG (hd : TwoDataG H K T' L₁ L₂ t) (hKH : K ≤ H)
    (hKnorm : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hT' : IsSylowTwoOf T' H)
    (hexp : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn153 K ⊤) (hbig : 2 ^ 6 ≤ Nat.card W)
    {a : MulAut W} (haH : a ∈ H) (hcT' : ∀ x ∈ T', x * a = a * x)
    (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hrk : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) :
    TwoCtx W K L₁ L₂ a (T' ⊓ K) := by
  obtain ⟨⟨hLa₁, hLa₂⟩, hS₁, hS₂⟩ := hd.a_normalizes hKH hKnorm hT' haH hcT'
  have hKn : H ≤ Subgroup.normalizer (K : Set (MulAut W)) := le_normalizer_of_normalizes hKnorm
  have hS : IsSylowTwoOf (T' ⊓ K) K := A4.isSylowTwoOf_inf_normal hT' hKH hKn
  refine ⟨⟨hexp, hirr, hbig, haN, ha1, ha2, hrk, hS, fun x hx => hcT' x hx.1⟩, hd.simple₁,
    hd.simple₂, hd.nab₁, hd.nab₂, hd.comm, hd.sup, hd.inf, ?_, ?_, hS₁, hS₂⟩
  · intro x hx
    have hmem : a * x * a⁻¹ ∈ L₁.map (MulAut.conj a).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hLa₁] at hmem
  · intro x hx
    have hmem : a * x * a⁻¹ ∈ L₂.map (MulAut.conj a).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hLa₂] at hmem

theorem two_false (hA21 : AsA21SQTKSection) (hD37 : D37Core) (h2 : TwoCases)
    (hq : G64.IsQuotientOfSQTKCat ↥H) (hKH : K ≤ H) (hKnorm : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hT' : IsSylowTwoOf T' H) (hd : TwoDataG H K T' L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hirr : IsIrrOn153 K ⊤) (hbig : 2 ^ 6 ≤ Nat.card W) {a : MulAut W} (haH : a ∈ H)
    (haT' : a ∈ T') (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hrk : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) (hcT' : ∀ x ∈ T', x * a = a * x) :
    False := by
  have hqhat : qhatOf (K ⊔ T') ≤ ((2 : ℚ) : WithTop ℚ) :=
    qhatOf_le_two hexp (Subgroup.mem_sup_right haT') ha1 ha2 hrk
  have hcore := core_of_twoDataG hA21 hq hKH hKnorm hT' hd hexp hbig hirr hqhat
  have hctx := twoCtx_of_twoDataG hd hKH hKnorm hT' hexp hirr hbig haH hcT' haN ha1 ha2 hrk
  rcases hD37 W (K ⊔ T') L₁ L₂ t hcore hd.nab₁ with ⟨n, hPSL, hOm⟩ | ⟨hPSL, hTen⟩
  · refine h2.omega W K L₁ L₂ (T' ⊓ K) a hctx ⟨n, hPSL, ?_⟩
    rw [hd.sup]
    exact hOm
  · refine h2.tensor W K L₁ L₂ (T' ⊓ K) a hctx ⟨hPSL, ?_⟩
    rw [hd.sup]
    exact hTen

end TwoDataG

end S153G93D

end CFSG.Quasithin
