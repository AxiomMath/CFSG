module

public import CFSG.Quasithin.Vol2.Ch11SecB23Two
public import CFSG.Quasithin.Vol2.Ch11SecDSetup
public import CFSG.Quasithin.Vol2.Ch11SecAVi2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped IsMulCommutative Pointwise

section General

variable {G : Type} [Group G]

theorem normalizer_sectionCentralizer {X K : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (sectionCentralizer X K : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (K : Set G),
      ∀ c ∈ sectionCentralizer X K, g * c * g⁻¹ ∈ sectionCentralizer X K := by
    rintro g ⟨hgX, hgK⟩ c ⟨hcX, hcK, hc⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgX hcX) (inv_mem hgX),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgK hcK) (inv_mem hgK), fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgX) x).mp hx
      simpa using this
    have h1 := hc _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp hgK _).mp h1
    have e : g * (c * (g⁻¹ * x * g) * c⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ =
        g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  exact le_normalizer_of_forall key ⟨hgX, hgK⟩

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lOf_eq_of_cComp {V₁ K : Subgroup G} (hL1C : LOf L V₁ ≤ Subgroup.centralizer (V₁ : Set G))
    (hL1 : LOf L V₁ ≠ ⊥)
    (hCM : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLK : LOf L V₁ ≤ K) (hK : quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G))) :
    LOf L V₁ = K := by
  obtain ⟨-, -, hKsn, hmin⟩ := hK
  have hKN : K ≤ Subgroup.normalizer (V₁ : Set G) := A3.subnormal_le hKsn
  have hmin' : ∀ K' : Subgroup G, K' ≤ K → K' ≠ ⊥ → ⁅K', K'⁆ = K' →
      CFSG.Open.IsSubnormal K' (Subgroup.normalizer (V₁ : Set G)) → K' = K := by
    intro K' hK'K hK' hp hsn
    by_contra hne
    exact hmin K' (lt_of_le_of_ne hK'K hne) hK' hp hsn
  have hCN : K ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (V₁ : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hKN)
  have hK0 : perfectCore (K ⊓ Subgroup.centralizer (V₁ : Set G)) = K := by
    refine hmin' _ ((perfectCore_le _).trans inf_le_left) ?_ (perfectCore_perfect _) ?_
    · intro h
      apply hL1
      rw [eq_bot_iff, ← h]
      exact le_perfectCore_of_perfect (le_inf hLK hL1C) (perfectCore_perfect _)
    · exact CFSG.Open.IsSubnormal.step (perfectCore_le _) (perfectCore_normal _)
        (CFSG.Open.IsSubnormal.step inf_le_left
          ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hCN) hKsn)
  have hKC : K ≤ Subgroup.centralizer (V₁ : Set G) := by
    rw [← hK0]; exact (perfectCore_le _).trans inf_le_right
  have hKL1 : K ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    (B2F.le_normalizer_inf (hKC.trans hCM) (hKN.trans Subgroup.le_normalizer)).trans
      (normalizer_le_normalizer_perfectCore _)
  exact hmin' _ hLK hL1 (perfectCore_perfect _)
    (CFSG.Open.IsSubnormal.step hLK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKL1) hKsn)

theorem normalizer_le_of_centralizer_le (hF : PointFacts) (hNF : NatFacts)
    (h112 : ASInputs.AS_A_1_12) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1112 : Stmt11_1_2) (h1115 : Stmt11_1_5) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁)
    (hCM : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · intro y hy
    have hy' : y ∈ (Subgroup.centralizer (V₁ : Set G) : Set G) *
        ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
          Set G) := by
      rw [← normalizer_eq_mul hF h112 h331 h1102 hyp hV₁ hC]; exact hy
    obtain ⟨c, hc, m, hm, rfl⟩ := Set.mem_mul.mp hy'
    exact Subgroup.mul_mem _ (hCM hc) hm.1
  have hR1M : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    refine (h1115 G T L I n V₁ hyp hV₁).resolve_right fun h => hC (le_bot_iff.mp ?_)
    rw [← h.2.2.1]
    exact inf_le_inf_right _ (SecA.fsuV_le_T hyp)
  set N₁ := Subgroup.normalizer (V₁ : Set G)
  set L₁ := LOf L V₁
  set R₁ := ROf T L V₁
  have hL1C := lOf_le_centralizer hF h1102 hyp hV₁
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (h1110 G T L I n hyp).2.1 1 (Or.inl rfl) V₁ hV₁
  have hn : 1 ≤ n := by have := hyp.one_lt; omega
  have hL1 : L₁ ≠ ⊥ := by
    intro h
    have h1 : ∀ x : ↥L₁, x = 1 := fun x => by
      have hx : (x : G) ∈ (⊥ : Subgroup G) := h ▸ x.2
      exact Subtype.ext (Subgroup.mem_bot.mp hx)
    let u : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
    have hu : u ≠ 1 := by
      intro hu1
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu1
      simp [u] at this
    apply hu
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm u)
    have h2 : e.symm u = 1 := by rw [← hx, h1 x, QuotientGroup.mk_one]
    simpa using congrArg e h2
  obtain ⟨-, V₂, -, -, hV₂, -⟩ := SecA.exists_isVi hNF h1102 hyp
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX hyp
  obtain ⟨K₁, hLK, hKC, hNK, -, -⟩ :=
    h1112 G T L I n 1 V₁ V₁ V₂ X hyp (Or.inl rfl) hV₁ hV₁ hV₂ hX
  have hL1eq := lOf_eq_of_cComp hL1C hL1 hCM hLK hKC
  have hNL1 : N₁ ≤ Subgroup.normalizer (L₁ : Set G) := by
    have h := hNK
    rw [← hL1eq] at h
    exact h
  set C := Subgroup.centralizer (V₁ : Set G) ⊓ sectionCentralizer L₁ (pCoreOf 2 L₁) with hCdef
  have hCN : N₁ ≤ Subgroup.normalizer (C : Set G) :=
    B2F.le_normalizer_inf (B2F.le_normalizer_centralizer le_rfl) fun g hg =>
      normalizer_sectionCentralizer (hNL1 hg)
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hNL1 hg))
  have hCle : C ≤ N₁ := inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  have hTN₁ : QuasithinUnique.IsSylowTwoOf T N₁ :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (IsVi.le_normalizer hV₁)
  have hTC := B6.isSylowTwoOf_inf_normal hTN₁ hCle hCN
  have hTL1 := T_le_normalizer_lOf hyp hV₁
  have hLTN : L₁ ⊔ T ≤ Subgroup.normalizer (L₁ : Set G) := sup_le Subgroup.le_normalizer hTL1
  have hRT : R₁ ≤ T :=
    B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow
      le_sup_right)
  have hRC : R₁ ≤ C := by
    refine le_inf (rOf_le_centralizer hF h1102 hyp hV₁) fun r hr => ?_
    have hrN : r ∈ Subgroup.normalizer (L₁ : Set G) := hTL1 (hRT hr)
    exact ⟨hrN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrN,
      fun l hl => commutator_rOf_mem hyp hV₁ hr hl⟩
  have hD2 : IsPGroup 2 ↥(C ⊓ (L₁ ⊔ T)) := by
    intro d
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hyp.fsu.sylow.1 hLTN (sup_comm T L₁) d d.2.2
    have hdC : (d : G) ^ 2 ^ k ∈ C := Subgroup.pow_mem _ d.2.1 _
    have hO : (d : G) ^ 2 ^ k ∈ pCoreOf 2 L₁ :=
      inf_sectionCentralizer_le hK hn e ⟨hk, hdC.2⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁ ⟨_, hO⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((d : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hj']
  have hDR : C ⊓ (L₁ ⊔ T) ≤ R₁ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ hD2
    have hLTN₁ : L₁ ⊔ T ≤ N₁ := sup_le ((perfectCore_le _).trans inf_le_right)
      (IsVi.le_normalizer hV₁)
    exact B2F.le_normalizer_inf (hLTN₁.trans hCN) Subgroup.le_normalizer
  have hReq : T ⊓ C = R₁ :=
    le_antisymm ((le_inf inf_le_right (inf_le_left.trans le_sup_right)).trans hDR)
      (le_inf hRT hRC)
  rw [hReq] at hTC
  exact (B6.frattini_two hCle hCN hTC).trans
    (sup_le (inf_le_left.trans hCM) (inf_le_right.trans hR1M))

theorem stmt11_2_3_of (hF : PointFacts) (hNF : NatFacts) (h112 : ASInputs.AS_A_1_12)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h1115 : Stmt11_1_5) : Stmt11_2_3 := by
  intro G _ _ T L I n V₁ hyp hV₁
  exact ⟨normalizer_eq_mul hF h112 h331 h1102 hyp hV₁,
    normalizer_le_of_centralizer_le hF hNF h112 h331 h1102 h1110 h1112 h1115 hyp hV₁⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
