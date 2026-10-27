module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndex
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexCoset

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inner

variable {H : Type*} [Group H]

theorem ggSix_mul_conj_mul_inv (σ : MulAut H) (g : H) :
    σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
  ext h
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem ggSix_conj_range_normal : (MulAut.conj : H →* MulAut H).range.Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ σ
  exact ⟨σ g, (ggSix_mul_conj_mul_inv σ g).symm⟩

end Inner

@[expose] def GGGoodOuterAut {G : Type*} [Group G] (G₀ : Subgroup G) (r : G₀)
    (σ : MulAut G₀) : Prop :=
  (∀ Q : Subgroup G₀, (∀ q ∈ Q, σ q = q) → IsPGroup 2 Q →
      (∀ y : G₀, σ y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥) ∧
    ∃ g : G₀, σ (g * r * g⁻¹) = g * r * g⁻¹ ∧
      ∃ a : G₀, σ a = a ∧ a * (g * r * g⁻¹) = g * r * g⁻¹ * a ∧ a ≠ 1 ∧ Odd (orderOf a)

section Bridge

variable {G : Type*} [Group G] [Finite G]

theorem ggSix_exists_good_involution_of_aut {G₀ X : Subgroup G}
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) (hGX : G₀ ≤ X)
    (hXN : X ≤ Subgroup.normalizer (G₀ : Set G)) (heven : Even (G₀.relIndex X)) {r : G₀}
    {I C : Subgroup (MulAut G₀)} (hI : I.Normal)
    (hKI : (MulAut.conj : G₀ →* MulAut G₀).range ≤ I)
    (hodd : Odd ((MulAut.conj : G₀ →* MulAut G₀).range.relIndex I))
    (hIC : ∀ σ : MulAut G₀, ∃ i ∈ I, ∃ c ∈ C, σ = i * c) (hIC' : I ⊓ C = ⊥)
    (hgood : ∀ c ∈ C, c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ I, GGGoodOuterAut G₀ r (e * c * e⁻¹)) :
    ∃ s ∈ X, s ∉ G₀ ∧ orderOf s = 2 ∧
      (∀ Q : Subgroup G, Q ≤ G₀ ⊓ Subgroup.centralizer {s} → IsPGroup 2 Q →
        G₀ ⊓ Subgroup.centralizer {s} ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥) ∧
      ∃ g ∈ G₀, s * (g * (r : G) * g⁻¹) = g * r * g⁻¹ * s ∧
        ∃ a ∈ G₀, a * s = s * a ∧ a * (g * (r : G) * g⁻¹) = g * r * g⁻¹ * a ∧ a ≠ 1 ∧
          Odd (orderOf a) := by
  classical
  set N := Subgroup.normalizer (G₀ : Set G)
  set φ := G₀.normalizerMonoidHom
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC]
    ext x
    simp
  have hφapp : ∀ (m : N) (h : G₀), ((φ m h : G₀) : G) = (m : G) * h * (m : G)⁻¹ :=
    fun _ _ => rfl
  set K := (MulAut.conj : G₀ →* MulAut G₀).range
  have : K.Normal := ggSix_conj_range_normal
  have hKmap : (G₀.subgroupOf N).map φ = K := by
    ext σ
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      ext h
      rw [MulAut.conj_apply, hφapp]
      rfl
    · rintro ⟨g, rfl⟩
      refine ⟨⟨g, Subgroup.le_normalizer g.2⟩, g.2, ?_⟩
      ext h
      rw [MulAut.conj_apply, hφapp]
      rfl
  set X' := (X.subgroupOf N).map φ
  have hKX : K ≤ X' := by
    rw [← hKmap]
    exact Subgroup.map_mono fun m hm => hGX hm
  have heven' : Even (K.relIndex X') := by
    rw [← hKmap, Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.relIndex_subgroupOf hXN]
    exact heven
  obtain ⟨σ, hσX, hσ2, hσI, e, heI, c, hc, hc2, hσ⟩ :=
    ggSix_exists_conj_involution_of_even hI hKI hodd hIC hIC' hKX heven'
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hσI
    rw [hσ, mul_one, mul_inv_cancel]
    exact I.one_mem
  have hgd := hgood c hc hc2 hc1 e heI
  rw [← hσ] at hgd
  obtain ⟨m, hmX, rfl⟩ := hσX
  have hσapp : ∀ h : G₀, ((φ m h : G₀) : G) = (m : G) * h * (m : G)⁻¹ := hφapp m
  have hfix : ∀ h : G₀, φ m h = h ↔ (h : G) * m = m * h := by
    intro h
    constructor
    · intro hh
      have := congrArg Subtype.val hh
      rw [hσapp] at this
      calc (h : G) * m = (m : G) * h * (m : G)⁻¹ * m := by rw [this]
        _ = m * h := by group
    · intro hh
      apply Subtype.ext
      rw [hσapp, ← hh, mul_inv_cancel_right]
  refine ⟨m, hmX, ?_, ?_, ?_, ?_⟩
  ·
    intro hmG
    apply hσI
    apply hKI
    rw [← hKmap]
    exact ⟨m, hmG, rfl⟩
  ·
    rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφ m, hσ2]
  ·
    intro Q hQ hQ2 hQN
    have hQ' := hgd.1 (Q.subgroupOf G₀) ?_ (hQ2.comap_of_injective G₀.subtype
      G₀.subtype_injective) ?_
    · rw [Subgroup.eq_bot_iff_forall]
      intro q hq
      have hq' : (⟨q, (hQ hq).1⟩ : G₀) ∈ Q.subgroupOf G₀ := hq
      rw [hQ', Subgroup.mem_bot] at hq'
      exact congrArg Subtype.val hq'
    · intro q hq
      rw [hfix]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hQ hq).2
    · intro y hy q hq
      have hyC : (y : G) ∈ G₀ ⊓ Subgroup.centralizer {(m : G)} :=
        ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ((hfix y).mp hy)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQN hyC) q).mp hq
  ·
    obtain ⟨g, hg, a, ha, hagr, ha1, haodd⟩ := hgd.2
    have hg' := (hfix _).mp hg
    have ha' := (hfix _).mp ha
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hg'
    refine ⟨g, g.2, hg'.symm, a, a.2, ha', ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hagr
      simpa using this
    · intro h1
      exact ha1 (Subtype.ext h1)
    · rwa [Subgroup.orderOf_coe]

end Bridge

section Inputs

@[expose] def GGAutStructureInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank → ψ.range = G₀ →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → commutator ↥G₀ = ⊤ →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → Subgroup.centralizer (G₀ : Set G) = ⊥ →
    (∃ (p : ℕ) (Bs : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
      Bs ≤ Subgroup.normalizer (G₀ : Set G) ∧ ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
    ¬ (t = .F4 ∧ Odd f) →
    ∀ r : G₀, GGRootInvolution (ggU t n f).D t ψ (r : G) →
      ∃ I C : Subgroup (MulAut G₀), I.Normal ∧ (MulAut.conj : G₀ →* MulAut G₀).range ≤ I ∧
        Odd ((MulAut.conj : G₀ →* MulAut G₀).range.relIndex I) ∧
        (∀ σ : MulAut G₀, ∃ i ∈ I, ∃ c ∈ C, σ = i * c) ∧ I ⊓ C = ⊥ ∧
        ∀ c ∈ C, c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ I, GGGoodOuterAut G₀ r (e * c * e⁻¹)

theorem ggOuterInvolutionInput_of_aut (h : GGAutStructureInput) : GGOuterInvolutionInput := by
  intro G _ _ t n f ψ G₀ hadm hrank hrange hker hperf hlie hC hBs hF X hGX hXN heven r hr
  have hrG₀ : r ∈ G₀ := by
    obtain ⟨-, γ, -, u, hru⟩ := hr
    exact hrange ▸ ggRootSub_le_range ψ γ u hru
  obtain ⟨I, C, hI, hKI, hodd, hIC, hIC', hgood⟩ :=
    h G t n f ψ G₀ hadm hrank hrange hker hperf hlie hC hBs hF ⟨r, hrG₀⟩ hr
  exact ggSix_exists_good_involution_of_aut hC hGX hXN heven hI hKI hodd hIC hIC' hgood

theorem ggSixStepThreeCInput_of_aut (h : GGAutStructureInput)
    (hF4 : GGSixStepThreeCFourInput) : GGSixStepThreeCInput :=
  ggSixStepThreeCInput_of_inputs (ggOuterInvolutionInput_of_aut h) hF4

end Inputs

end CFSG.StandardType
