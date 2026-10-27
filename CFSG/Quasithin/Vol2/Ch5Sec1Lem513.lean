module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318T

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_3_qhat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    ∀ hV : IsCh5Module T L V, thompsonJ T ≤ Subgroup.centralizer (V : Set G) →
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    qhatInt (L ⊔ T) V hV.isTwoReducedIn.2.2.1 ≤ 2 →
      IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨
      (n = 2 ∧ IsBarS5 L T V ∧ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T)) ∨
      IsNatQuotCh5 L ⁅V, L⁆ n ∨
      IsOrthCh5 L V n

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem exists_isHStar (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) :
    ∃ H : Subgroup G, IsHStar T M H := by
  obtain ⟨⟨-, -, huniq⟩, -, hH, -, -⟩ :=
    (h331 G T h.simple h.nonabelian h.qtke h.sylow).2 L h.maximal h.isQuasisimple
  rw [h.conjClosure_eq] at huniq hH
  have hM : M = Subgroup.normalizer (L : Set G) := huniq M h.maxTwoLocal h.sup_le_M
  rw [← hM] at hH
  exact hH

theorem T_le_normalizer_inf_centralizer (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V) :
    T ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hV.isTwoReducedIn.2.1
  have hTL := h.T_le_normalizer
  have key : ∀ t ∈ T, ∀ c ∈ V ⊓ Subgroup.centralizer (L : Set G),
      t * c * t⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    intro t ht c hc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) c).mp hc.1, ?_⟩
    show t * c * t⁻¹ ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : t⁻¹ * l * t ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l).mp hl
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
    calc l * (t * c * t⁻¹) = t * ((t⁻¹ * l * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * l * t)) * t⁻¹ := by rw [hcomm]
      _ = t * c * t⁻¹ * l := by group
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key t ht c, fun hc => ?_⟩
  simpa [mul_assoc] using key t⁻¹ (T.inv_mem ht) _ hc

theorem module_inf_centralizer_eq_bot (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    (hZ : centerOf (L ⊔ T) = ⊥) : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hC
  by_contra hne
  have hred := hV.isTwoReducedIn
  have hV2 : IsPGroup 2 V := by
    intro v
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_one] using hred.2.2.1.2 v v.2
  have hC2 : IsPGroup 2 C := hV2.to_le inf_le_left
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := h.T_le_normalizer_inf_centralizer hV
  have hS2 : IsPGroup 2 ↥(T ⊔ C) := h.sylow.1.to_sup_of_normal_right' hC2 hTC
  have hfix := inf_centralizer_ne_bot_of_normalizes hS2 le_sup_right
    (sup_le hTC Subgroup.le_normalizer) hne
  apply hfix
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨⟨hcV, hcL⟩, hcS⟩ := hc
  have hcT : c ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hcS
  have hcLT : c ∈ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := by
      have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := fun l hl =>
        Subgroup.mem_centralizer_iff.mpr fun w hw => by
          rw [Set.mem_singleton_iff.mp hw]
          exact (Subgroup.mem_centralizer_iff.mp hcL l hl).symm
      have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := fun t ht =>
        Subgroup.mem_centralizer_iff.mpr fun w hw => by
          rw [Set.mem_singleton_iff.mp hw]
          exact (Subgroup.mem_centralizer_iff.mp hcT t ht).symm
      exact sup_le hLc hTc hx
    exact (Subgroup.mem_centralizer_iff.mp hxc c (Set.mem_singleton c)).symm
  have hcZ : c ∈ centerOf (L ⊔ T) := ⟨hred.1 hcV, hcLT⟩
  rw [hZ] at hcZ
  exact hcZ

theorem lemma_5_1_3 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h316 : Theorem316Statement) (h317 : AS317Sylow) (h512 : Stmt5_1_2) (hq : Stmt5_1_3_qhat)
    (hV : IsCh5Module T L V) :
    IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨
      (n = 2 ∧ IsBarS5 L T V ∧ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T)) ∨
      IsNatQuotCh5 L ⁅V, L⁆ n ∨
      IsOrthCh5 L V n ∨
      (IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆) := by
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  ·
    obtain ⟨H, hH⟩ := h.exists_isHStar h331
    have h318 := h.hyp318 h331 hV hH
    have hZ : centerOf (L ⊔ T) = ⊥ := by
      rcases theorem318_three hC58 h317 h.simple h.nonabelian h.qtke h.sylow h318 with
        ⟨hJ', -⟩ | ⟨-, -, hZ⟩
      · exact absurd (le_inf (thompsonJ_le_self T) hJ) hJ'
      · exact hZ
    have hq2 := theorem318_one_of_316 h316 h.simple h.nonabelian h.qtke h.sylow h318
    rcases hq G T M L V n h hV hJ (h.module_inf_centralizer_eq_bot hV hZ) hq2 with
      h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  ·
    rcases h512 G T M L V n h hV with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩
    · exact absurd (h1.trans inf_le_right) hJ
    · exact Or.inr (Or.inr (Or.inl h2.commutator))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))

end Hyp5_0_1

theorem stmt5_1_3_of (h331 : Stmt3_3_1) (hC58 : TheoremC58) (h316 : Theorem316Statement)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2) (hq : Stmt5_1_3_qhat) : Stmt5_1_3 :=
  fun _ _ _ _ _ _ _ _ h hV => h.lemma_5_1_3 h331 hC58 h316 h317 h512 hq hV

end CFSG.Quasithin.H13
