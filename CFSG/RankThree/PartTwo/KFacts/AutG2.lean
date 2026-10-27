module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsSep
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.G2FieldFourEvenSimplePairs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (K : Type) [Field K]

@[expose] noncomputable def g2FieldHom : (K ≃+* K) →* MulAut (adjointGroup Tag.G2 K) where
  toFun σ := exactNormalAut Tag.G2 K 1 σ 0
  map_one' := exactNormalAut_one_one_zero
  map_mul' σ σ' := (exactNormalAut_one_zero_mul σ σ').symm

variable {K}

theorem coe_g2FieldHom (σ : K ≃+* K) (h : adjointGroup Tag.G2 K) :
    (g2FieldHom K σ h : ModGL Tag.G2 K) =
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) := by
  change (exactNormalAut Tag.G2 K 1 σ 0 h : ModGL Tag.G2 K) = _
  rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]

theorem forall_eq_iff_eq_conj_mul_g2FieldHom (α : MulAut (adjointGroup Tag.G2 K))
    (g : adjointGroup Tag.G2 K) (σ : K ≃+* K) :
    (∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) * (g : ModGL Tag.G2 K)⁻¹) ↔
      α = MulAut.conj g * g2FieldHom K σ := by
  constructor
  · intro h
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_g2FieldHom, Subgroup.coe_inv]
  · rintro rfl h
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, coe_g2FieldHom,
      Subgroup.coe_inv]

theorem even_G2_exists_exactNormalAut_zero_eq [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {β : MulAut (adjointGroup Tag.G2 K)} (hβ : β ∈ unipotentPairAut Tag.G2 K) :
    ∃ a σ, β = exactNormalAut Tag.G2 K a σ 0 := by
  have hβ' : β ∈ rootPairAut Tag.G2 K := mem_rootPairAut.2 fun i =>
    ⟨(even_G2_opposite_Sylow_stabilizer_fixes_simple_pairs K hK hβ i).1,
      (even_G2_opposite_Sylow_stabilizer_fixes_simple_pairs K hK hβ i).2⟩
  obtain ⟨p, hp, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter Tag.G2 K).1 β hβ'
  refine ⟨p.1, p.2, mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_⟩
  · rw [(hp i).1, exactNormalAut_zero_adjX]
  · rw [(hp i).2.1, exactNormalAut_zero_adjY]

theorem g2_automorphism_normal_form [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    (∀ α : MulAut (adjointGroup Tag.G2 K), ∃ (g : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      α = MulAut.conj g * g2FieldHom K σ) ∧
    ∀ σ : K ≃+* K, IsInnerAut (g2FieldHom K σ) → σ = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP K p := finite_field_prime_power_characteristic hp f.pos hK
  have hchar : ringChar K = p := ringChar.eq K p
  obtain ⟨hNF, Θ, hΘ, -, hker, -⟩ : (∀ α : MulAut (adjointGroup Tag.G2 K),
      ∃! gσ : adjointGroup Tag.G2 K × (K ≃+* K),
        ∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) = (gσ.1 : ModGL Tag.G2 K) *
          Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL Tag.G2 K) *
            (gσ.1 : ModGL Tag.G2 K)⁻¹) ∧
      ∃ Θ : MulAut (adjointGroup Tag.G2 K) →* (K ≃+* K),
        (∀ (α : MulAut (adjointGroup Tag.G2 K)) (g : adjointGroup Tag.G2 K) (σ : K ≃+* K),
          (∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
            Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) *
              (g : ModGL Tag.G2 K)⁻¹) → Θ α = σ) ∧
        Function.Surjective Θ ∧
        Θ.ker = (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range ∧
        True := by
    by_cases hp2 : p = 2
    · subst hp2
      have hdC : ∀ a : Fin Tag.G2.rank → Kˣ, rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 K :=
        fun a => by
          obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) K
          exact (hrest B hB a).2.2.1
      obtain ⟨h1, Θ, h2, h3, h4, -⟩ := inner_field_automorphism_normal_form_of_params
        Nat.prime_two f.pos hK (fun β hβ => even_G2_exists_exactNormalAut_zero_eq hK4 hβ) hdC
      exact ⟨h1, Θ, h2, h3, h4, trivial⟩
    · obtain ⟨h1, Θ, h2, h3, h4, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp
        hp2 f.pos K hK Tag.G2 (Or.inr ⟨rfl, fun h => hK3 (hchar.trans h)⟩)
      exact ⟨h1, Θ, h2, h3, h4, trivial⟩
  refine ⟨fun α => ?_, fun σ hσ => ?_⟩
  · obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
    exact ⟨g, σ, (forall_eq_iff_eq_conj_mul_g2FieldHom α g σ).mp hgσ⟩
  · have h1 : Θ (g2FieldHom K σ) = σ :=
      hΘ _ 1 σ ((forall_eq_iff_eq_conj_mul_g2FieldHom _ 1 σ).mpr (by rw [map_one, one_mul]))
    have h2 : g2FieldHom K σ ∈ Θ.ker := by rw [hker]; exact hσ
    rw [MonoidHom.mem_ker, h1] at h2
    exact h2

variable (K) in
@[expose] noncomputable def stdPinnedG2 : PinnedAut (adjointGroup Tag.G2 K) where
  inndiag := (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range
  inn_le := le_rfl
  field := (g2FieldHom K).range
  graph := ∅

section Pinned

variable [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
include hK3 hK4

theorem stdPinnedG2_stable : (stdPinnedG2 K).Stable := by
  obtain ⟨hdec, -⟩ := g2_automorphism_normal_form hK3 hK4
  have hcomm : ∀ σ τ : K ≃+* K,
      g2FieldHom K σ * g2FieldHom K τ = g2FieldHom K τ * g2FieldHom K σ := fun σ τ => by
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hd
    exact ⟨α y, (mul_mulAutConj_mul_inv α y).symm⟩
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨g, σ, rfl⟩ := hdec α
    refine ⟨g2FieldHom K τ, ⟨τ, rfl⟩, h1, MulAut.conj g, ⟨g, rfl⟩, ?_⟩
    calc MulAut.conj g * g2FieldHom K σ * g2FieldHom K τ * (MulAut.conj g * g2FieldHom K σ)⁻¹ =
        MulAut.conj g * (g2FieldHom K σ * g2FieldHom K τ) * (g2FieldHom K σ)⁻¹ *
          (MulAut.conj g)⁻¹ := by group
      _ = MulAut.conj g * g2FieldHom K τ * (MulAut.conj g)⁻¹ := by rw [hcomm]; group
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

theorem stdPinnedG2_separated : (stdPinnedG2 K).Separated := by
  obtain ⟨-, hfaith⟩ := g2_automorphism_normal_form hK3 hK4
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro φ - _ ⟨g, rfl⟩
    exact ⟨φ g, (mul_mulAutConj_mul_inv φ g).symm⟩
  · rintro _ ⟨σ, rfl⟩ hmem
    rw [hfaith σ hmem, map_one]

end Pinned

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (K) in
@[expose] def InducesKindG2 (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K,
    InducesKind L (stdPinnedG2 K) e x k

variable [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
include hK3 hK4

theorem inducesKindG2_iff (e : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K) (x : G)
    (k : AutKind) : InducesKindG2 K L x k ↔ InducesKind L (stdPinnedG2 K) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L (stdPinnedG2_stable hK3 hK4) e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

theorem inducesKindG2_unique {x : G} {k₁ k₂ : AutKind} (h₁ : InducesKindG2 K L x k₁)
    (h₂ : InducesKindG2 K L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedG2_separated hK3 hK4) h₁
    ((inducesKindG2_iff L hK3 hK4 e x k₂).mp h₂)

end Induced

end CFSG.RankThree.PartTwo.KFacts
