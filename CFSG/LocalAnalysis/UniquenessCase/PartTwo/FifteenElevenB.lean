module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Eleven_n_le {V M : Subgroup G} {i : ℕ} {g : G} {A B : Subgroup G} {v : G}
    (hcfg : Cfg11 V M i g A B v) :
    E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ≤ i + 1 := by
  have hB : B ≤ conjSubgroup V g ⊓ centralizer ({v} : Set G) := by
    refine le_inf (hcfg.B_le.trans hcfg.A_le) fun b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have := hcfg.comm_B b hb
    calc v * b = b * v * b⁻¹ * v⁻¹ * (v * b) := by rw [this, one_mul]
      _ = b * v := by group
  have h1 := E3.mQuot_mono (V := conjSubgroup V g) hB
  have h2 := E3.mQuot_add hcfg.B_le hcfg.A_le
  have h3 := hcfg.mQuot_A
  have h4 := hcfg.mQuot_B
  omega

theorem s15_Eleven_sq {V : Subgroup G} (hV : IsElemAbelian 2 V) {v : G} (hv : v ∈ V) :
    v * v = 1 := by
  have := hV.2 v hv
  rwa [pow_two] at this

theorem s15_Eleven_supp_card_ge (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (g : G) {S : Set (Subgroup G)}
    (hS : S ⊆ wConjG D.M V₀ V hV L g) {z : G} (hz : z ∈ sSup S) (hz1 : z ≠ 1)
    (hbad : ¬ centralizer ({z} : Set G) ≤ conjSubgroup D.M g) :
    2 ≤ S.ncard ∧ (3 ≤ s15 D.M V₀ V hV L → s15 D.M V₀ V hV L - 1 ≤ S.ncard) := by
  have hfin : S.Finite := Set.toFinite S
  have hXV : ∀ X ∈ wConj D.M V₀ V hV L, X ≤ V := by
    rintro X ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  constructor
  · by_contra hlt
    have hle : S.ncard ≤ 1 := by omega
    rcases Nat.lt_or_ge S.ncard 1 with h0 | h1
    · have hS0 : S = ∅ := (Set.ncard_eq_zero hfin).1 (by omega)
      subst hS0
      rw [sSup_empty, Subgroup.mem_bot] at hz
      exact hz1 hz
    · obtain ⟨Y, rfl⟩ := Set.ncard_eq_one.1 (by omega : S.ncard = 1)
      rw [sSup_singleton] at hz
      obtain ⟨X, hX, rfl⟩ := mem_wConjG.1 (hS (Set.mem_singleton Y))
      exact hbad (s15_Glue3_centralizer_le_conj D h hV hX g hz hz1)
  · intro hs3
    by_contra hlt
    have hcard : (wConjG D.M V₀ V hV L g).ncard = s15 D.M V₀ V hV L :=
      s15_Glue3_wConjG_ncard D h.hyp151 hV g
    have hdiff : 1 < (wConjG D.M V₀ V hV L g \ S).ncard := by
      rw [Set.ncard_diff hS]
      omega
    obtain ⟨Y₁, Y₂, hY₁, hY₂, hY₁₂⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hdiff
    obtain ⟨X₁, ⟨x₁, hx₁, rfl⟩, rfl⟩ := mem_wConjG.1 hY₁.1
    obtain ⟨X₂, ⟨x₂, hx₂, rfl⟩, rfl⟩ := mem_wConjG.1 hY₂.1
    have hx₁₂ : conjSubgroup (wSub V₀ V hV L) x₁ ≠
        conjSubgroup (wSub V₀ V hV L) x₂ := by
      intro heq
      exact hY₁₂ (congrArg (fun X => conjSubgroup X g) heq)
    have hSU : sSup S ≤ conjSubgroup (⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) x₁ ∧ X ≠ conjSubgroup (wSub V₀ V hV L) x₂}, X) g := by
      refine sSup_le fun Y hY => ?_
      obtain ⟨X, hX, rfl⟩ := mem_wConjG.1 (hS hY)
      refine E3.conjSubgroup_mono_left g (le_iSup₂_of_le X ⟨hX, ?_, ?_⟩ le_rfl)
      · intro hXeq
        rw [hXeq] at hY
        exact hY₁.2 hY
      · intro hXeq
        rw [hXeq] at hY
        exact hY₂.2 hY
    have hzU := hSU hz
    have hUV : (⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) x₁ ∧ X ≠ conjSubgroup (wSub V₀ V hV L) x₂}, X) ≤ V :=
      iSup₂_le fun X hX => hXV X hX.1
    have hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
      refine ⟨1, ?_⟩
      have := (E3.isElemAbelian_conjSubgroup hV g).2 z (E3.conjSubgroup_mono_left g hUV hzU)
      simpa using this
    have hK : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
      UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
    have hu := uniqueMax_conjSubgroup_of_mem (g := g) (M := D.M)
      (fun w hw hw1 => h.unique₂ x₁ hx₁ x₂ hx₂ hx₁₂ w (Subgroup.mem_sup_right hw) hw1) hzU hz1
    exact hbad (centralizer_le_of_uniqueMax hK hz1 hz2 hu).1

theorem s15_Eleven_support_of_wClos (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥)
    (hW : E3.wClos V 0 D.M ≤ centralizer (V : Set G))
    (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    {i : ℕ} {g : G} {A B : Subgroup G} {v : G}
    (hcfg : Cfg11 V D.M i g A B v) (hvg : v ∈ conjSubgroup D.M g) :
    2 ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard ∧
      (3 ≤ s15 D.M V₀ V hV L →
        s15 D.M V₀ V hV L - 1 ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard) ∧
      (suppAct (wConjG D.M V₀ V hV L g) v).ncard ≤
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ∧
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ≤ i + 1 := by
  have hY := E3.isElemAbelian_conjSubgroup hV g
  have hind := s15_Glue3_wConjG_indep D h.hyp151 hV hL hV1 g
  have hspan := s15_Glue3_wConjG_sSup D h1217 h.hyp151 hV hL g
  have hγ : ∀ X ∈ wConjG D.M V₀ V hV L g, rk ↥X = gamma15 D.M V₀ V hV L :=
    fun X hX => s15_Glue3_wConjG_rk D h.hyp151 hV hV1 g hX
  have ht : v * v = 1 := s15_Eleven_sq hV hcfg.v_mem
  have hperm : ∀ X ∈ wConjG D.M V₀ V hV L g, conjSubgroup X v ∈ wConjG D.M V₀ V hV L g :=
    fun X hX => s15_Glue3_wConjG_perm D hV hvg hX
  have hcard := s15_Support_ncard_act_le hY hind hspan hγ (two_le_gamma15 D h.hyp151 hV hL) ht hperm
  obtain ⟨a, haA, ha⟩ := hcfg.comm_A
  have hmem : a * v * a⁻¹ * v⁻¹ ∈ sSup (suppAct (wConjG D.M V₀ V hV L g) v) := by
    rw [sSup_eq_iSup]
    exact s15_Support_comm_mem hY hspan ht hperm (hcfg.A_le haA)
  have hsub : suppAct (wConjG D.M V₀ V hV L g) v ⊆ wConjG D.M V₀ V hV L g := fun X hX => hX.1
  obtain ⟨h2, h3⟩ := s15_Eleven_supp_card_ge D h hV g hsub hmem ha
    (s15_Eleven_not_centralizer_le_of_wClos D h hV hW hcfg haA)
  exact ⟨h2, h3, hcard, s15_Eleven_n_le hcfg⟩

theorem s15_Eleven_support (D : Data G) (h1217 : R1217 D) (h159 : R15_9 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hV1 : v1Sub D.M V₀ V hV L = ⊥) {i : ℕ} {g : G} {A B : Subgroup G} {v : G}
    (hcfg : Cfg11 V D.M i g A B v) (hvg : v ∈ conjSubgroup D.M g) :
    2 ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard ∧
      (3 ≤ s15 D.M V₀ V hV L →
        s15 D.M V₀ V hV L - 1 ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard) ∧
      (suppAct (wConjG D.M V₀ V hV L g) v).ncard ≤
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ∧
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ≤ i + 1 :=
  s15_Eleven_support_of_wClos D h1217 h hV hL (h159 V₀ V L h hL) hV1 hcfg hvg

theorem s15_Eleven_cases {s i c n : ℕ} (hev : Even s) (hspos : 0 < s) (hi : i ≤ 2) (h2 : 2 ≤ c)
    (h3 : 3 ≤ s → s - 1 ≤ c) (hcn : c ≤ n) (hn : n ≤ i + 1) :
    s = 2 ∨ (s = 4 ∧ i = 2 ∧ c = 3 ∧ n = 3) := by
  obtain ⟨k, hk⟩ := hev
  by_cases hs2 : s = 2
  · exact Or.inl hs2
  · right
    have hs4 : 4 ≤ s := by omega
    have h3' := h3 (by omega)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
