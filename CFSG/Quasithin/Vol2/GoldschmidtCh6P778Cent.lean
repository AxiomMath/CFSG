module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4AI
public import CFSG.Quasithin.Background.GoldschmidtE6TwentySixCent
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.H13

section CaseAi

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement MatrixGroups Matrix

theorem ch6P778Cent {G : Type} [Group G] [Finite G] {T H S : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) (hn : E1.nParam H ≤ 1) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hSyl : IsSylowIn 2 S (S ⊔ oTwoUpper H)) : E5.CentGen 1 (S ⊔ oTwoUpper H) S := by
  have hTH' : IsSylowIn 2 T H := isSylowTwoOf_of_isSylowTwo hT hTH
  have hres : twoResidual H = oTwoUpper H := F6.twoResidual_eq_oTwoUpper H
  have hYH : S ⊔ oTwoUpper H ≤ H := sup_le (hST.trans hTH) (oTwoUpper_le H)
  have hTY : T ≤ Subgroup.normalizer ((S ⊔ oTwoUpper H : Subgroup G) : Set G) := by
    intro g hg
    have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTS hg)
    have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_oTwoUpper H (hTH hg))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]
  have hHY : H ≤ Subgroup.normalizer ((S ⊔ oTwoUpper H : Subgroup G) : Set G) := by
    calc H = T ⊔ oTwoUpper H := (hres ▸ sup_twoResidual_eq hTH').symm
      _ ≤ _ := sup_le hTY (le_sup_right.trans Subgroup.le_normalizer)
  have h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ S ⊔ oTwoUpper H := fun x hx => by
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H x hx
    exact ⟨k, Subgroup.mem_sup_right (hres ▸ hk)⟩
  exact E5.genCent_of_inE hTH' hYH hHY h2 hSyl (E5.inf_eq_of_isSylowIn hT.1 hSyl hST)
    ((E1.nParam_le_iff Nat.one_pos).1 (by exact_mod_cast hn))

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp611

theorem not_le_normalizer_inf_ch6C (h432 : Stmt4_3_2) (hH11 : Ch6InH11)
    (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) (hr : 1 < rParam V) {M₁ K₁ : Subgroup G}
    (hM₁ : quasithinIsMaxTwoLocal M₁) (hXT : xFiveCh6 T L ⊔ T ≤ M₁) (hK₁M₁ : K₁ ≤ M₁)
    (hK₁M : ¬ K₁ ≤ M) :
    ¬ xFiveCh6 T L ≤ Subgroup.normalizer ((T ⊓ conjClosure K₁ T : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQS, hST, hSL⟩ := h.pCoreOf_xFive_props_ch6 horth
  set S := pCoreOf 2 (xFiveCh6 T L ⊔ T) with hSdef
  set K₀ := conjClosure K₁ T with hK₀def
  have hV := h.isElemAbelian
  have hVQ : V ≤ ch6Q T V := fun v hv =>
    ⟨h.le_T hv, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (B2F.isElemAbelian_comm hV hw hv)⟩
  have hJ := h.thompsonJk_one_le_ch6 hH11 horth (hVQ.trans hQS) hST hSL
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTM₁ : T ≤ M₁ := le_sup_right.trans hXT
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun t ht =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (xFiveCh6 T L ⊔ T)
      (Subgroup.mem_sup_right ht)
  have hTK₀ : T ≤ Subgroup.normalizer (K₀ : Set G) := le_normalizer_conjClosure K₁ T
  have hK₀M₁ : K₀ ≤ M₁ := conjClosure_le fun t ht k hk =>
    M₁.mul_mem (M₁.mul_mem (hTM₁ ht) (hK₁M₁ hk)) (M₁.inv_mem (hTM₁ ht))
  have hInH : InH T (K₀ ⊔ T) := by
    refine ⟨le_sup_right, fun h0 => pCoreOf_ne_bot_of_isTwoLocal hM₁.1 (le_bot_iff.mp ?_)⟩
    rw [← h0]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf hTM₁)).trans le_sup_right)
      ((sup_le hK₀M₁ hTM₁).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
  have hnotM : ¬ K₀ ⊔ T ≤ M := fun hle =>
    hK₁M ((le_conjClosure K₁ T).trans (le_sup_left.trans hle))
  obtain ⟨HS, hHS, hHSle⟩ := exists_isHStar_le_ch6 hInH hnotM
  have hn : E1.nParam HS ≤ 1 := by rw [h.nParam_eq_one HS hHS]
  obtain ⟨hNV, hNQ⟩ := h.normalizer_le_and_isUniqueM_ch6 h432
  have hnotSyl : ¬ IsSylowIn 2 S (S ⊔ oTwoUpper HS) := by
    intro hSyl
    have hG := ch6P778Cent h.sylow hHS.1.1 hn hST hTS hSyl
    have := ch6InE626_ofC G T V M (S ⊔ oTwoUpper HS) S 1 h.sylow h.ne_bot hV h.le_T
      h.T_le_normalizer hNV hNQ one_pos hG hQS hST (by exact_mod_cast hr) hJ
    apply hHS.2.1
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (h.toHyp5_0_1.isSylowTwoOf hHS.1.1)]
    exact sup_le (le_sup_right.trans this.1) h.T_le
  intro hXN
  have hPS : T ⊓ K₀ ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
      (sup_le hXN fun t ht => mem_normalizer_inf_ch6 (Subgroup.le_normalizer ht) (hTK₀ ht))
      (h.sylow.1.to_le inf_le_left)
  have hSK₀ : S ≤ Subgroup.normalizer (K₀ : Set G) := hST.trans hTK₀
  have hinf : S ⊓ K₀ = T ⊓ K₀ := le_antisymm (inf_le_inf_right K₀ hST) (le_inf hPS inf_le_right)
  have hsylK₀ : IsSylowTwoOf (T ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal (h.toHyp5_0_1.isSylowTwoOf (le_sup_right : T ≤ K₀ ⊔ T))
      le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
  have hodd : ¬ 2 ∣ S.relIndex (S ⊔ K₀) := by
    rw [relIndex_sup_eq_inf_ch6 hSK₀, hinf]
    exact hsylK₀.2.2
  have hO2 : oTwoUpper HS ≤ K₀ := by
    have h1 : oTwoUpper HS ≤ oTwoUpper (K₀ ⊔ T) :=
      Subgroup.closure_mono fun x hx => ⟨hHSle hx.1, hx.2⟩
    refine h1.trans (oTwoUpper_le_of_normal_sup_ch6 le_sup_left ?_ h.sylow.1 le_sup_right le_rfl)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTK₀)
  apply hnotSyl
  refine ⟨le_sup_left, hS2, fun h2 => hodd ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex S (S ⊔ oTwoUpper HS) (S ⊔ K₀) le_sup_left
    (sup_le_sup_left hO2 S)
  exact h2.trans (Dvd.intro _ hmul)

end Hyp611

end CaseAi

end CFSG.Quasithin.H13
