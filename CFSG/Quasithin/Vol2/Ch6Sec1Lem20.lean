module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem isInHS_sup (h : Hyp6116 G T M L V n) :
    IsInHS T M L V (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIN : Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.centralizer_le_normalizer _
  have hTI : T ≤ Subgroup.normalizer
      ((Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) :=
    h.toHyp611Nat.T_le_normalizer_ZS.trans (F7.normalizer_le_normalizer_centralizer _)
  have hZO : ch6ZS T L V ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((inf_le_left.trans h.toHyp611.le_T).trans le_sup_right)
      (sup_le hIN h.toHyp611Nat.T_le_normalizer_ZS)
      ((B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left)
  refine ⟨⟨le_sup_right, fun h0 => h.toHyp611Nat.ZS_ne_bot ?_⟩,
    fun hle => h.not_le (le_sup_left.trans hle), ?_⟩
  · rw [← le_bot_iff, ← h0]; exact hZO
  · exact oTwoUpper_le_of_pow_mem fun x hx => exists_pow_mem_of_le_normalizer h.sylow.1 hTI hx

theorem exists_isInHS_isHStar (h : Hyp6116 G T M L V n) :
    ∃ H : Subgroup G, IsInHS T M L V H ∧ IsHStar T M H := by
  have hIT := h.isInHS_sup
  let S : Set (Subgroup G) := {Y | InH T Y ∧
    Y ≤ Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T ∧ ¬ Y ≤ M}
  have hS : (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) ∈ S := ⟨hIT.1, le_rfl, hIT.2.1⟩
  obtain ⟨H, hHS, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min S ⟨_, hS⟩
  have hO2 : oTwoUpper H ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have hTI : T ≤ Subgroup.normalizer
        ((Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) :=
      h.toHyp611Nat.T_le_normalizer_ZS.trans (F7.normalizer_le_normalizer_centralizer _)
    exact oTwoUpper_le_of_pow_mem fun x hx =>
      exists_pow_mem_of_le_normalizer h.sylow.1 hTI (hHS.2.1 hx)
  refine ⟨H, ⟨hHS.1, hHS.2.2, hO2⟩, hHS.1, hHS.2.2, fun Y hY hYH hYM => ?_⟩
  by_contra hne
  exact hmin Y ⟨hY, hYH.trans hHS.2.1, hYM⟩ (lt_of_le_of_ne hYH hne)

theorem lemma_6_1_20_one (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
        pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
      ⁅conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)),
        pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G))⁆ ≤ ch6ZS T L V := by
  have h17 := (stmt6_1_17 h432 G T M L V n h _ h.isInHS_sup).2.1
  rw [inf_eq_right.mpr le_sup_left] at h17
  have hU : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) :=
    conjClosure_mono le_rfl le_sup_left
  exact ⟨hU.trans h17.2.1, (Subgroup.commutator_mono hU le_rfl).trans h17.2.2⟩

theorem lemma_6_1_20_two (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) :
    ¬ IsMulCommutative ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH, hHs⟩ := h.exists_isInHS_isHStar
  by_cases hodd : Odd (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V)
  · exact (h6119 G T M L V n h ⟨H, hH, hHs, hodd⟩).2
  have heven : Even (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V) := Nat.not_odd_iff_even.mp hodd
  have hyp := h.amalgamHypV h432 hH
  have hV1 : V ≠ ⊥ := h.toHyp611.ne_bot
  have hN : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV1
  obtain ⟨hne, hle, hVγG₁, -⟩ := commutator_V_Vv_of_even hyp hV1 heven hγ.dist_eq hγ.not_le
  have hvt := vtype_eq_false_of_even hyp.gen (by rw [hγ.dist_eq]; exact heven)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  have hVγ : Vv V γ = conjSub (g : G) V := by rw [hg, Vv_smul_γ₀ hN]
  rw [hVγ] at hne hle hVγG₁
  have hW2 : IsPGroup 2 (conjSub (g : G) V) :=
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).map _
  obtain ⟨x, hx, hxle⟩ := F7.isSylowTwoOf_exists_conj_le h.toHyp611.isSylowIn_T hVγG₁ hW2
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hN hx
  have hxV : conjSub x⁻¹ V = V := conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hxN)
  have hWT : conjSub (x⁻¹ * (g : G)) V ≤ T := by
    rw [conjSub_mul]
    have := conjSub_mono x⁻¹ hxle
    rwa [conjSub_conjSub_inv] at this
  have hne' : ⁅V, conjSub (x⁻¹ * (g : G)) V⁆ ≠ ⊥ := by
    intro h0
    apply hne
    have e : conjSub x (conjSub (x⁻¹ * (g : G)) V) = conjSub (g : G) V := by
      rw [← conjSub_mul, mul_inv_cancel_left]
    have := congrArg (conjSub x) h0
    rw [conjSub_commutator', e, conjSub_eq_of_mem_normalizer' hxN] at this
    rw [this]
    unfold conjSub
    exact Subgroup.map_bot _
  have hle' : ⁅V, conjSub (x⁻¹ * (g : G)) V⁆ ≤ V ⊓ conjSub (x⁻¹ * (g : G)) V := by
    have := conjSub_mono x⁻¹ hle
    rwa [conjSub_commutator', conjSub_inf, hxV, ← conjSub_mul] at this
  have heq : conjSubgroup V (x⁻¹ * (g : G))⁻¹ = conjSub (x⁻¹ * (g : G)) V := by
    unfold conjSubgroup conjSub
    rw [inv_inv]
  rw [← heq] at hWT hne' hle'
  obtain ⟨-, -, c, hc, hcW⟩ := h6111 G T M L V n h.toHyp611Nat _ hWT hne' hle'
  rw [hcW] at hne'
  intro hab
  apply hne'
  have hVU : V ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) := le_conjClosure V _
  have hVcU : conjSubgroup V c ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
    Hyp6116.conjSub_le_conjClosure (Subgroup.inv_mem _ hc)
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  exact congrArg Subtype.val (hab.is_comm.comm ⟨w, hVcU hw⟩ ⟨v, hVU hv⟩)

theorem lemma_6_1_20_three (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    ∀ x ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)),
      x ∉ Subgroup.centralizer
        ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) : Subgroup G) : Set G) →
      ⁅conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)), Subgroup.zpowers x⁆ =
        ch6ZS T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hxC
  obtain ⟨hUO, hUOZ⟩ := h.lemma_6_1_20_one h432
  have hxO := hUO hx
  refine le_antisymm ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxO)).trans hUOZ)
    ?_
  obtain ⟨i, hi, v, hv, hiv⟩ : ∃ i ∈ Subgroup.centralizer (ch6ZS T L V : Set G), ∃ v ∈ V,
      i * v * i⁻¹ * x ≠ x * (i * v * i⁻¹) := by
    by_contra hall
    push Not at hall
    apply hxC
    have hle : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
        Subgroup.centralizer ({x} : Set G) :=
      CFSG.Quasithin.conjClosure_le fun i hi v hv =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hall i hi v hv)
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hu))
  have hx' : i⁻¹ * x * i ∈ ch6S T L V := by
    have h1 : i⁻¹ * x * i ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.inv_mem _ hi)) x).mp hxO
      simpa using this
    exact F7.isSylowTwoOf_pCoreOf_le h.toHyp611Nat.isSylowIn_S h1
  have hx'V : i⁻¹ * x * i ∉ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hiv
    have := Subgroup.mem_centralizer_iff.mp hc v hv
    calc i * v * i⁻¹ * x = i * (v * (i⁻¹ * x * i)) * i⁻¹ := by group
      _ = i * ((i⁻¹ * x * i) * v) * i⁻¹ := by rw [this]
      _ = x * (i * v * i⁻¹) := by group
  have h1 := h.toHyp611Nat.commutator_zpowers_eq hx' hx'V
  have hiZ : conjSub i (ch6ZS T L V) = ch6ZS T L V :=
    conjSub_eq_of_mem_normalizer' (Subgroup.centralizer_le_normalizer _ hi)
  have h2 := congrArg (conjSub i) h1
  rw [conjSub_commutator', conjSub_zpowers, hiZ] at h2
  have e : i * (i⁻¹ * x * i) * i⁻¹ = x := by group
  rw [e] at h2
  exact h2.ge.trans (Subgroup.commutator_mono (Hyp6116.conjSub_le_conjClosure hi) le_rfl)

end Hyp6116

end CFSG.Quasithin.H13
