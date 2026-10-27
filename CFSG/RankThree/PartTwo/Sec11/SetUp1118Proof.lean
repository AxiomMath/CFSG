module

public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofList
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofChoice
public import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofChoice
public import CFSG.RankThree.PartTwo.Sec11.DataExistsR

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace SetUp1118Proof

section Elementary

variable {G : Type*} [Group G]

theorem not_mem_closure_of_mem_closure_pair {a c d e : G} (hac : a * c = c * a)
    (ha3 : a ^ 3 = 1) (hacd : a ∉ Subgroup.closure ({c, d} : Set G))
    (he : e ∈ Subgroup.closure ({a, c} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    e ∉ Subgroup.closure ({c, d} : Set G) := by
  obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hac he
  intro hcd
  by_cases h3 : (3 : ℤ) ∣ m
  · apply hec
    rw [ActOnA.zpow_eq_one_of_dvd ha3 h3, one_mul]
    exact Subgroup.zpow_mem_zpowers c n
  · apply hacd
    refine ActOnA.mem_of_zpow_mem ha3 ?_ h3
    have e1 : a ^ m = a ^ m * c ^ n * (c ^ n)⁻¹ := by group
    rw [e1]
    exact Subgroup.mul_mem _ hcd
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n))

end Elementary

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem commute_r_a_of_zpowers_eq {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c) : r * a = a * r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le
  have hrR : r ∈ R := (Item1116Proof.mem_R h).1
  obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨r, hrR⟩
  have hrk : r ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hrc : r * c = c * r := Sec12.commute_of_conj_mem_zpowers hc3
    ((Subgroup.mem_normalizer_iff.mp (hRH hrR) c).mp (Subgroup.mem_zpowers c)) hrk
  have hcr : Subgroup.zpowers c ≤ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hrc.symm)
  have hle : Subgroup.closure ({r, s} : Set G) ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact hcr (hsc ▸ Subgroup.mem_zpowers y)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle h.a_mem_closure)).symm

theorem commute_s_a_of_field (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h11131 : Item11131) (h11133 : Item11133Field) {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hf : KFacts.InducesStdKind Y c .field) :
    s * a = a * s := by
  by_contra hsa
  obtain ⟨r₁, h₁, hr₁a⟩ := rank3II_11_11_choose h (h.closure_rs_le_normalizer h45 h113) hsa
  by_cases hcl : Subgroup.closure ({r₁, s} : Set G) = Subgroup.closure {a, s}
  ·
    have hRa : R = Subgroup.closure {a, x, s} := by
      rw [h₁.R_eq]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy | hy <;> rw [hy]
        · have hr : r₁ ∈ Subgroup.closure ({a, s} : Set G) := by
            rw [← hcl]
            exact Subgroup.subset_closure (by simp)
          refine (Subgroup.closure_le _).mpr ?_ hr
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hz | hz <;> rw [hz] <;> exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy | hy <;> rw [hy]
        · have ha : a ∈ Subgroup.closure ({r₁, s} : Set G) := by
            rw [hcl]
            exact Subgroup.subset_closure (by simp)
          refine (Subgroup.closure_le _).mpr ?_ ha
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hz | hz <;> rw [hz] <;> exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
    have h₂ : Sec11Data G A c L a R Y d x s a g :=
      { h₁ with R_eq := hRa, a_mem_closure := Subgroup.subset_closure (by simp) }
    have hag : a * g = g * a :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
    exact Item1115Proof.false_of_mem_zpowers h45 h113 h117 h₂ (Subgroup.mem_zpowers a) hag hsa
  ·
    obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure
      (Item1115Proof.mem_normalizer_zpowers_s h45 h₁ (Item1116Proof.mem_R h₁).1) h₁.a_mem_closure
    have hsj : s ^ j ∈ Subgroup.zpowers c := by
      rw [h11131 G A c L a R Y d x s r₁ g h₁ hf]
      refine Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem_zpowers s j, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hsj' : s ^ j = (r₁ ^ i)⁻¹ * a := by rw [hij]; group
      have hra : Commute r₁ a := hr₁a
      have hc : (r₁ ^ i)⁻¹ * a = a * (r₁ ^ i)⁻¹ := ((hra.zpow_left i).inv_left).eq
      rw [hsj']
      calc (r₁ ^ i)⁻¹ * a * a = a * (r₁ ^ i)⁻¹ * a := by rw [hc]
        _ = a * ((r₁ ^ i)⁻¹ * a) := mul_assoc _ _ _
    have he : r₁ ^ i ∈ Subgroup.closure ({a, c} : Set G) := by
      have e1 : r₁ ^ i = a * (s ^ j)⁻¹ := by rw [hij]; group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsj))
    have hec : r₁ ^ i ∉ Subgroup.zpowers c := by
      intro hm
      apply h.a_not_mem_zpowers
      rw [hij]
      exact Subgroup.mul_mem _ hm hsj
    exact Item1115Proof.not_yNotField h45 h113 h₁ hf hsa he hec
      (h11133 G A c L a R Y d x s r₁ g h₁ hf hr₁a hcl _ ⟨Subgroup.zpow_mem_zpowers r₁ i, he⟩ hec)

theorem exists_not_field (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h11131 : Item11131) (h11133 : Item11133Field) (h1117 : Item1117) {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hx : 9 < orderOf x) :
    ∃ (a₁ : G) (Y₁ : Subgroup G), Sec11Std G A c L a₁ R Y₁ ∧ a₁ ∈ A ∧
      a₁ ∉ Subgroup.closure ({c, d} : Set G) ∧ ¬ KFacts.InducesStdKind Y₁ c .field := by
  obtain ⟨-, hacd, -⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  by_cases hf : KFacts.InducesStdKind Y c .field
  · have hsa := commute_s_a_of_field h45 h113 h117 h11131 h11133 h hf
    have hsc : Subgroup.zpowers s = Subgroup.zpowers c := by
      rw [h11131 G A c L a R Y d x s r g h hf, inf_of_le_left (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hsa))]
    have hra := commute_r_a_of_zpowers_eq h hsc
    have hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} := by
      intro hrs
      have := (h1117 G A c L a R Y d x s r g h hsc hrs).2
      omega
    obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure
      (Item1115Proof.mem_normalizer_zpowers_s h45 h (Item1116Proof.mem_R h).1) h.a_mem_closure
    have hsj : s ^ j ∈ Subgroup.zpowers c := hsc ▸ Subgroup.zpow_mem_zpowers s j
    have he : r ^ i ∈ Subgroup.closure ({a, c} : Set G) := by
      have e1 : r ^ i = a * (s ^ j)⁻¹ := by rw [hij]; group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsj))
    have hec : r ^ i ∉ Subgroup.zpowers c := by
      intro hm
      apply h.a_not_mem_zpowers
      rw [hij]
      exact Subgroup.mul_mem _ hm hsj
    have hnfe := h11133 G A c L a R Y d x s r g h hf hra hrs _
      ⟨Subgroup.zpow_mem_zpowers r i, he⟩ hec
    have hAe := h.mem_partTwoF.1
    have hac : a * c = c * a :=
      congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, h.a_mem⟩ ⟨c, h.mem_A⟩)
    have heA : r ^ i ∈ A := by
      refine (Subgroup.closure_le A).mpr ?_ he
      rintro y (rfl | rfl)
      exacts [h.a_mem, h.mem_A]
    have hecd := not_mem_closure_of_mem_closure_pair hac (hAe.2 a h.a_mem) hacd he hec
    obtain ⟨Ye, hYe, hKYe, hnfYe⟩ := hnfe
    exact ⟨r ^ i, Ye, h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hYe hKYe, heA,
      hecd, hnfYe⟩
  · exact ⟨a, Y, h.toSec11Std, h.a_mem, hacd, hf⟩

end SetUp1118Proof

theorem setUp1118_of_res5 (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h11131 : Item11131) (h11133 : Item11133Field)
    (h1117 : Item1117) (hD4 : KFact1118Triality46) (hinv : KFact1118Inverter) :
    SetUp1118 := by
  intro G _ _ A c L a R Y d x s r g h hx
  obtain ⟨a₁, Y₁, hstd₁, ha₁A, ha₁cd, hnf₁⟩ :=
    SetUp1118Proof.exists_not_field h45 h113 h117 h11131 h11133 h1117 h hx
  have hA₁ := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha₁A ha₁cd
  obtain ⟨a₂, Y₂, g₂, hstd₂, ha₂A, ha₂cd, hg₂3, hg₂YW, hg₂R, hg₂H, hg₂c, hnf₂⟩ :=
    Item1117Proof.exists_choice_g_not_field h45 h113 h117 h119 hstd₁ h.inf_eq hA₁ hnf₁
  have hA₂ := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha₂A ha₂cd
  obtain ⟨r₂, hRr₂, har₂⟩ :=
    hstd₂.exists_eq_closure h45 h.inf_eq hA₂ h.inf_L_eq h.inf_centralizer_eq
  have hdata₂ : Sec11Data G A c L a₂ R Y₂ d x s r₂ g₂ :=
    { toSec11Std := hstd₂
      inf_eq := h.inf_eq
      closure_eq := hA₂
      inf_L_eq := h.inf_L_eq
      inf_centralizer_eq := h.inf_centralizer_eq
      R_eq := hRr₂
      a_mem_closure := har₂
      pow_eq_one := hg₂3
      g_mem := hg₂YW
      g_mem_normalizer := hg₂R
      g_not_mem := hg₂H
      conj_mem := hg₂c }
  have hlist₂ := SetUp1118Proof.isList_of_not_field h45 h46 h119 hD4 hdata₂ hnf₂ hx
  obtain ⟨g₀, t₀, hg₀, hg₀3, hg₀ne, ht₀, ht₀g⟩ :=
    hinv G A c L a₂ R Y₂ d x s r₂ g₂ hdata₂ hnf₂ hlist₂
  obtain ⟨a₃, Y₃, g₃, t₃, hstd₃, ha₃A, ha₃cd, hg₃YW, hg₃R, hg₃H, hg₃c, hg₃3, ht₃, ht₃g, hnf₃⟩ :=
    SetUp1118Proof.exists_choice_of_inverts h45 h113 h117 h119 hstd₂ h.inf_eq hA₂ hnf₂ hg₀ hg₀3
      hg₀ne ht₀ ht₀g
  have hA₃ := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha₃A ha₃cd
  obtain ⟨r₃, hRr₃, har₃⟩ :=
    hstd₃.exists_eq_closure h45 h.inf_eq hA₃ h.inf_L_eq h.inf_centralizer_eq
  have hdata₃ : Sec11Data G A c L a₃ R Y₃ d x s r₃ g₃ :=
    { toSec11Std := hstd₃
      inf_eq := h.inf_eq
      closure_eq := hA₃
      inf_L_eq := h.inf_L_eq
      inf_centralizer_eq := h.inf_centralizer_eq
      R_eq := hRr₃
      a_mem_closure := har₃
      pow_eq_one := ⟨1, by rw [pow_one, ← hg₃3, pow_orderOf_eq_one]⟩
      g_mem := hg₃YW
      g_mem_normalizer := hg₃R
      g_not_mem := hg₃H
      conj_mem := hg₃c }
  exact ⟨a₃, Y₃, r₃, g₃,
    { toSec11Data := hdata₃
      orderOf_x_gt := hx
      isList := SetUp1118Proof.isList_of_not_field h45 h46 h119 hD4 hdata₃ hnf₃ hx
      not_field := hnf₃
      orderOf_g := hg₃3
      exists_inverts := ⟨t₃, ht₃, ht₃g⟩ }⟩

end CFSG.RankThree.PartTwo.Sec11
