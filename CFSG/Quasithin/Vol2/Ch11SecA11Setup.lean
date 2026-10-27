module

public import CFSG.Quasithin.Vol2.Ch11SecA11Point
public import CFSG.Quasithin.Vol2.Ch11SecA11Comp
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp1111 (T : Subgroup G) (i : ℕ) (Vi V₀ : Subgroup G) : Prop :=
  (i = 1 ∧ V₀ ≠ ⊥ ∧ V₀ ≤ Vi ∧ QuasithinUnique.IsSylowTwoOf
      (T ⊓ Subgroup.normalizer (V₀ : Set G)) (Subgroup.normalizer (V₀ : Set G))) ∨
    (i = 2 ∧ V₀ = Vi)

omit [Finite G] in
theorem eq_of_le_sup_of_perfect [Finite G] {B K S : Subgroup G} (hBK : B ≤ K)
    (hK : ⁅K, K⁆ = K) (hS : IsPGroup 2 S) (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hKS : K ≤ B ⊔ S) : K = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : (B.subgroupOf (B ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSB)
  set φ := QuotientGroup.mk' (B.subgroupOf (B ⊔ S)) with hφ
  have hS' : IsPGroup 2 ↥(S.subgroupOf (B ⊔ S)) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hrange : (S.subgroupOf (B ⊔ S)).map φ = ⊤ := by
    have h1 : B.subgroupOf (B ⊔ S) ⊔ S.subgroupOf (B ⊔ S) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self _
    have h2 : (B.subgroupOf (B ⊔ S)).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk']
    rw [← Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective _), ← h1,
      Subgroup.map_sup, h2, bot_sup_eq]
  have hQ : IsPGroup 2 (↥(B ⊔ S) ⧸ B.subgroupOf (B ⊔ S)) := by
    have h3 : IsPGroup 2 ↥((S.subgroupOf (B ⊔ S)).map φ) := hS'.map φ
    rw [hrange] at h3
    exact h3.of_equiv Subgroup.topEquiv
  have := hQ.isNilpotent
  have hK' : ⁅K.subgroupOf (B ⊔ S), K.subgroupOf (B ⊔ S)⁆ = K.subgroupOf (B ⊔ S) := by
    apply Subgroup.map_injective (B ⊔ S).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKS, hK]
  have hKφ : ⁅(K.subgroupOf (B ⊔ S)).map φ, (K.subgroupOf (B ⊔ S)).map φ⁆ =
      (K.subgroupOf (B ⊔ S)).map φ := by
    rw [← Subgroup.map_commutator, hK']
  have hbot := eq_bot_of_perfect_of_le_solvable
    (le_top (a := (K.subgroupOf (B ⊔ S)).map φ)) hKφ
  refine le_antisymm (fun k hk => ?_) hBK
  have hkN : k ∈ B ⊔ S := hKS hk
  have h1 : φ ⟨k, hkN⟩ ∈ (K.subgroupOf (B ⊔ S)).map φ := ⟨⟨k, hkN⟩, hk, rfl⟩
  rw [hbot, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

variable {T L I : Subgroup G} {n i : ℕ} {Vi V₀ : Subgroup G}

namespace Hyp1111

omit [Finite G] in
theorem i_cases (hc : Hyp1111 T i Vi V₀) : i = 1 ∨ i = 2 := by
  rcases hc with ⟨hi, -⟩ | ⟨hi, -⟩
  · exact Or.inl hi
  · exact Or.inr hi

theorem sylow (h : Hyp11 G T L I n) (hU : IsVi T L I n i Vi) (hc : Hyp1111 T i Vi V₀) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₀ : Set G))
      (Subgroup.normalizer (V₀ : Set G)) := by
  rcases hc with ⟨-, -, -, hS⟩ | ⟨-, rfl⟩
  · exact hS
  · rw [inf_eq_left.mpr (IsVi.le_normalizer hU)]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (IsVi.le_normalizer hU)

theorem ne_bot (h : Hyp11 G T L I n) (hU : IsVi T L I n i Vi) (hc : Hyp1111 T i Vi V₀) :
    V₀ ≠ ⊥ := by
  rcases hc with ⟨-, hne, -⟩ | ⟨hi, rfl⟩
  · exact hne
  · exact IsVi.ne_bot h hU (by omega)

omit [Finite G] in
theorem le (hc : Hyp1111 T i Vi V₀) : V₀ ≤ Vi := by
  rcases hc with ⟨-, -, hle, -⟩ | ⟨-, rfl⟩
  · exact hle
  · exact le_rfl

theorem pCoreOf_ne_bot (h : Hyp11 G T L I n) (hU : IsVi T L I n i Vi)
    (hc : Hyp1111 T i Vi V₀) : pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) ≠ ⊥ := by
  have hp : IsPGroup 2 V₀ := (isPGroup_fsuV h).to_le (hc.le.trans (IsVi.le_fsuV hU))
  have hle : V₀ ≤ pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp
  intro hbot
  exact hc.ne_bot h hU (eq_bot_iff.mpr (hbot ▸ hle))

theorem lOf_le (hF : Facts11) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n i Vi) (hc : Hyp1111 T i Vi V₀) :
    LOf L Vi ≤ Subgroup.normalizer (V₀ : Set G) := by
  rcases hc with ⟨rfl, -, hle, -⟩ | ⟨-, rfl⟩
  · exact (lOf_one_le_centralizer hF h1102 h hU).trans ((Subgroup.centralizer_le hle).trans
      (Subgroup.centralizer_le_normalizer _))
  · exact (perfectCore_le _).trans inf_le_right

end Hyp1111

omit [Finite G] in
theorem T_le_normalizer_lOf {U : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    T ≤ Subgroup.normalizer (LOf L U : Set G) := by
  refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
  exact (le_inf hTL (hTU.trans Subgroup.le_normalizer)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem lOf_mem_lFamily (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n i Vi) (hi : i = 1 ∨ i = 2) {S : Subgroup G} (hST : S ≤ T) :
    LOf L Vi ∈ lFamily S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h hi hU
  have hQ := isQuasisimple_of_mulEquiv_SL2 h.one_lt hK e
  have hSB : S ≤ Subgroup.normalizer (LOf L Vi : Set G) :=
    hST.trans (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hU))
  have hne : LOf L Vi ≠ ⊥ := by
    intro hbot
    obtain ⟨-, -, a, b, hab⟩ := hQ
    have : Subsingleton ↥(LOf L Vi) := by
      rw [hbot]
      infer_instance
    exact hab (Subsingleton.elim _ _)
  have hnormal : ((LOf L Vi).subgroupOf (LOf L Vi ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSB)
  exact mem_cComp_of_quasisimple hne (perfectCore_perfect _) hQ
    (IsSubnormal.step le_sup_left hnormal (IsSubnormal.refl _))

end CFSG.Quasithin.Vol2.Ch11.SecA
