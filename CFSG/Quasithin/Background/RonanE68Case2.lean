module

public import CFSG.Quasithin.Background.RonanE68Two
public import CFSG.Quasithin.Background.RonanE68A6
public import CFSG.Quasithin.Background.ONanE68A6

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE68

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.E68Proof
  CFSG.Assembly.LowTwoRank

section A6

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem card_sylow_two_a6 {P : Subgroup G} (hS : IsSylowTwoOf P L)
    (e : ↥L ≃* alternatingGroup (Fin 6)) : Nat.card ↥P = 8 := by
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hL360 : Nat.card ↥L = 360 := by rw [Nat.card_congr e.toEquiv, h360]
  have hcard : Nat.card ↥L = Nat.card ↥P * (P.subgroupOf L).index := by
    rw [← Subgroup.card_mul_index (P.subgroupOf L)]
    exact congrArg (· * _) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv)
  obtain ⟨a, ha⟩ := hS.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ (P.subgroupOf L).index := hS.2.2
  rw [ha, hL360] at hcard
  have hpos : 0 < (P.subgroupOf L).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0] at hidx
    exact hidx (dvd_zero 2))
  have ha9 : a < 9 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 9 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ a ≤ 360 := by
      rw [hcard]
      exact Nat.le_mul_of_pos_right _ hpos
    norm_num at h1
    omega
  rw [ha]
  interval_cases a <;> simp at hcard ⊢ <;> omega

theorem rootClause_a6 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (e : ↥L ≃* alternatingGroup (Fin 6))
    (hmq : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1)
    (hPlt : L ⊓ M < L)
    (hPmax : ∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) :
    E6.IsMarkedSp4Root 1 (autSubInduced L (L ⊔ V)) (autSubInduced L V) := by
  classical
  have hV := h.isElemAbelian
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set P₀ : Subgroup G := Q ⊓ L with hP₀def
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hS : IsSylowTwoOf P₀ L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  obtain ⟨hN, hmax⟩ := a6_borel hq hS e
  obtain ⟨-, hres, -⟩ := sandwich h hU hL
  have hPX : P₀ ≤ L ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans h.centralizer_le))
  have hXP : L ⊓ M ≠ P₀ := by
    intro hXP
    have hker : IsPGroup 2 e.toMonoidHom.ker := isPGroup_two_ker_of_injective _ e.injective
    obtain ⟨-, P₁, P₂, h1, h1', -⟩ := CFSG.QuasithinUnique.Borel252.borelFacts_of_data hq hS
      CFSG.QuasithinUnique.Borel252.A6.borelData_A6 e.toMonoidHom e.surjective hker
    rw [hN] at h1
    rcases hPmax P₁ (hXP.le.trans h1.le) h1'.le with h3 | h3
    · exact h1.ne (h3.trans hXP).symm
    · exact h1'.ne h3
  have hresX := twoPrimeResidual_eq_self_of_ne hS hN hmax hPX hPlt hXP
  have hXC : L ⊓ M ≤ L ⊓ Subgroup.centralizer (V : Set G) := hresX.ge.trans hres
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hC2 : C.relIndex V = 2 := by
    rw [E3.relIndex_eq_two_pow h.isPGroup_V C, hmq]
    norm_num
  obtain ⟨v, hvV, hvC⟩ : ∃ v ∈ V, v ∉ C := by
    by_contra hall
    push Not at hall
    have h1 : C.relIndex V = 1 := Subgroup.relIndex_eq_one.2 fun x hx => hall x hx
    omega
  have hvL : ¬ ∀ x ∈ L, x * v = v * x := fun hall =>
    hvC ⟨hvV, Subgroup.mem_centralizer_iff.2 hall⟩
  have hdich : ∀ w ∈ V, (∀ x ∈ L, x * w = w * x) ∨ (∀ x ∈ L, x * (v⁻¹ * w) = (v⁻¹ * w) * x) := by
    intro w hw
    rcases mem_or_mem_of_relIndex_two hC2 hvV hw hvC with h1 | h1
    · exact Or.inl fun x hx => Subgroup.mem_centralizer_iff.1 h1.2 x hx
    · exact Or.inr fun x hx => Subgroup.mem_centralizer_iff.1 h1.2 x hx
  have hV2 : ∀ w ∈ V, w * w = 1 := fun w hw => by
    have := F7.isElemAbelian_pow_eq_one hV hw
    rwa [pow_two] at this
  have hXC' : ∀ x ∈ L ⊓ M, ∀ w ∈ V, x * w = w * x := fun x hx w hw =>
    (Subgroup.mem_centralizer_iff.1 (hXC hx).2 w hw).symm
  have hP8 : Nat.card ↥P₀ = 8 := card_sylow_two_a6 hS e
  have hdvd : Nat.card ↥P₀ ∣ Nat.card ↥(L ⊓ M) := Subgroup.card_dvd_of_le hPX
  have hlt : 8 < Nat.card ↥(L ⊓ M) := by
    rw [hP8] at hdvd
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun heq => hXP ?_
    exact (Subgroup.eq_of_le_of_card_ge hPX (by rw [hP8, ← heq])).symm
  rw [hP8] at hdvd
  exact rootClause_a6_core e hVN hV2 hvV hvL hdich inf_le_left hXC' hdvd hlt

end A6

section Case2

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem case2P_of_case2 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (h2 : E68Case2 h.isElemAbelian T M U L) : Case2P T M V U L := by
  obtain ⟨n, hn1, hmodel, hle, hdec, hcases⟩ := h2
  refine ⟨n, hn1, hmodel, hle, hdec, ?_⟩
  rcases hcases with ha | ⟨hPS, hPlt, hPmax, hmq, -⟩
  · exact Or.inl ha
  · right
    refine ⟨hPS, hPlt, hPmax, ?_, hmq⟩
    rcases hmodel with ⟨hn2, hm⟩ | ⟨rfl, ⟨e⟩⟩
    · exact rootClause_sp4 h hU hL hn2 hm (hdec (by omega)) hPS hPlt hPmax hmq
    · exact rootClause_a6 h hU hL e hmq hPlt hPmax

end Case2

end CFSG.Quasithin.RonanE68
