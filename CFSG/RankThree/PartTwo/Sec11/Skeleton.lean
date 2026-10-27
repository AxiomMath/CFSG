module

public import CFSG.RankThree.PartTwo.Sec11.SetUp11
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.KFacts.K71bFieldOrderThree
import CFSG.RankThree.PartTwo.Sec11.Item1133Proof
import CFSG.RankThree.PartTwo.Sec11.Item1125Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1113
public import CFSG.RankThree.PartTwo.Sec11.LaterSteps

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem Sec11Std.change_a (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {a' : G}
    (ha'A : a' ∈ A) (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 a') (hKY' : sec11K L a' ≤ Y') :
    Sec11Std G A c L a' R Y' := by
  obtain ⟨hxN, hx3, -, -, -⟩ := basic_facts_of_conj h45 h hdL hA ha'A ha'cd
  have hout := not_isInnerAut_of_not_mem_closure h.toHyp91 hdL hA ha'A ha'cd hxN
  have hfield := KFacts.inducesStdKind_field_of_isList1016 h.isList1016 hx3 ⟨hxN, hout⟩
  have ha'1 : a' ≠ 1 := fun h1 => ha'cd (h1 ▸ Subgroup.one_mem _)
  exact { h with
    a_mem := ha'A
    a_ne_one := ha'1
    inducesStdKind := Or.inl hfield
    mem_thetaComponentsAt_Y := hY'
    sec11K_le := hKY' }

theorem Sec11Std.closure_eq_of_not_mem {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) {a' : G} (ha'A : a' ∈ A)
    (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) : A = Subgroup.closure {c, a', d} := by
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hdA : d ∈ A := by
    have : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    exact this.1
  obtain ⟨hca, -, hd1⟩ := h.not_mem_facts hdL hA
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr hc hdc
    have hcomm : c * a = a * c :=
      congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le hcomm (hexp c h.mem_A) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  have e := closure_triple_eq hexp h.card_eq h.mem_A hdA ha'A h.ne_one hdc ha'cd
  rw [← e]
  congr 1
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

omit [Finite G] in
theorem le_R_of_hyp91 {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    [Finite G] (h : Sec9.Hyp91 G A c L a R) : A ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (A : Set G) with hK
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAK : A ≤ K := by
    refine le_inf (fun y hy => Subgroup.centralizer_le_normalizer _ ?_) Subgroup.le_normalizer
    rw [← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy c h.mem_A)
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hN : (Subgroup.comap K.subtype A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr inf_le_right
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf
  have hle := @IsPGroup.le_sylow_of_normal 3 K _ _ hN (hA3.comap_subtype (K := K)) Q
  intro y hy
  have h1 : (⟨y, hAK hy⟩ : K) ∈ (Q : Subgroup K) := hle (Subgroup.mem_subgroupOf.mpr hy)
  have h2 : y ∈ (Q : Subgroup K).map K.subtype := ⟨_, h1, rfl⟩
  rw [hQ] at h2
  exact h2.1

@[expose] def Choose1128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g a' : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} → orderOf x = 9 →
      a' ∈ A → a' ∉ Subgroup.closure {c, d} →
      ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {a', d} → YNotField c L a' →
        ∃ (Y' : Subgroup G) (g' : G), Y' ∈ thetaComponentsAt 3 a' ∧ sec11K L a' ≤ Y' ∧
          ¬ KFacts.InducesStdKind Y' c .field ∧ (∃ k : ℕ, g' ^ 3 ^ k = 1) ∧
          g' ∈ Y' ⊓ Subgroup.normalizer (A : Set G) ∧ g' ∈ Subgroup.normalizer (R : Set G) ∧
          g' ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
          g' * c * g'⁻¹ ∈ Subgroup.closure {c, d} ∧ sec11P R g' = sec11P R g

theorem item1128_of (h45 : Sec4.Item4_5) (h1116 : Item1116) (h1117 : Item1117) (h1118 : Item1118)
    (hch : Choose1128) : Item1128 := by
  intro G _ _ A c L a R Y d x s r g h
  have hx9 := h1118 G A c L a R Y d x s r g h
  have hsr : Subgroup.zpowers s = Subgroup.zpowers c ∧
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} := by
    by_contra hne
    have := h1116 G A c L a R Y d x s r g h (by tauto)
    omega
  obtain ⟨⟨a', ha'A, ha'cd, hPP, hnf⟩, -⟩ := h1117 G A c L a R Y d x s r g h hsr.1 hsr.2
  obtain ⟨Y', g', hY', hKY', hnf', hg3, hgYW, hgR, hgH, hgc, hP⟩ :=
    hch G A c L a R Y d x s r g a' h hsr.1 hsr.2 hx9 ha'A ha'cd hPP hnf
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq ha'A ha'cd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha'A ha'cd
  have hAR := le_R_of_hyp91 h.toHyp91
  have hd : d ∈ A ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.mem_zpowers d
  have hdx : d ∈ Subgroup.zpowers x := by
    rw [← h.inf_L_eq]
    exact ⟨hAR hd.1, hd.2⟩
  have hcs := h.c_mem_zpowers_s
  have hxR : x ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have hsR : s ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  set T := Subgroup.closure ({a', x, s} : Set G) with hT
  have hxT : x ∈ T := Subgroup.subset_closure (by simp)
  have hsT : s ∈ T := Subgroup.subset_closure (by simp)
  have hAT : A ≤ T := by
    rw [hA', Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.zpowers_le.mpr hsT hcs
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr hxT hdx
  have hRT : R = T := by
    apply le_antisymm
    · rw [h.R_eq, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · have hr : y ∈ Subgroup.closure ({a, s} : Set G) := by
          rw [← hsr.2]
          exact Subgroup.subset_closure (by simp)
        refine (Subgroup.closure_le _).mpr ?_ hr
        rintro z (rfl | rfl)
        · exact hAT h.a_mem
        · exact hsT
      · exact hxT
      · exact hsT
    · rw [hT, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · exact hAR ha'A
      · exact hxR
      · exact hsR
  have hdata : Sec11Data G A c L a' R Y' d x s a' g' :=
    { toSec11Std := hstd
      inf_eq := h.inf_eq
      closure_eq := hA'
      inf_L_eq := h.inf_L_eq
      inf_centralizer_eq := h.inf_centralizer_eq
      R_eq := hRT
      a_mem_closure := Subgroup.subset_closure (by simp)
      pow_eq_one := hg3
      g_mem := hgYW
      g_mem_normalizer := hgR
      g_not_mem := hgH
      conj_mem := hgc }
  refine ⟨a', Y', x, s, a', g', { hdata with
    zpowers_s_eq := hsr.1
    closure_eq_closure := rfl
    orderOf_x := hx9
    commutator_eq := by rw [hP]; exact hPP
    not_field := hnf'
    g_comm := ?_ }⟩
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt hY'
  exact Subgroup.mem_centralizer_singleton_iff.mp (hYC hgYW.1)

@[expose] def Inverter1118 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      ∃ (a' : G) (Y' : Subgroup G) (r' g' : G), Sec11Big G A c L a' R Y' d x s r' g' ∧
        sec11P R g' = sec11P R g ∧
        ∃ j ∈ Subgroup.centralizer {g'} ⊓ Subgroup.normalizer (Subgroup.zpowers a' : Set G) ⊓
            Subgroup.normalizer ((sec11P R g' : Subgroup G) : Set G),
          ∀ y ∈ Subgroup.closure ({s ^ 3, x ^ 9} : Set G), j * y * j⁻¹ = y⁻¹

theorem sec11BigNever_of
    (h113 : Item113) (h117 : Item117) (h1117 : Item1117)
    (h1119 : Item1119) (h1123 : Item1123) (h1125 : Item1125) (hinv : Inverter1118) :
    Sec11BigNever := by
  intro G _ _ A c L a R Y d x s r g hbig
  obtain ⟨c₁, L₁, a₁, R₁, Y₁, x₁, s₁, r₁, g₁, hbig₁, hcdN⟩ :=
    h1119 G A c L a R Y d x s r g hbig
  have hNd := hbig₁.toSec11Data.normalizer_sec11P_le_normalizer_zpowers_d h113 h117 hcdN
  obtain ⟨a₂, Y₂, r₂, g₂, hbig₂, hP, j, hj, hjinv⟩ :=
    hinv G A c₁ L₁ a₁ R₁ Y₁ d x₁ s₁ r₁ g₁ hbig₁ hcdN hNd
  rw [← hP] at hcdN hNd
  have hrs := h1123 G A c₁ L₁ a₂ R₁ Y₂ d x₁ s₁ r₂ g₂ hbig₂
  have hsc : Subgroup.zpowers s₁ ≠ Subgroup.zpowers c₁ := by
    intro hsc
    have h9 := (h1117 G A c₁ L₁ a₂ R₁ Y₂ d x₁ s₁ r₂ g₂ hbig₂.toSec11Data hsc hrs).2
    have h9' := hbig₂.orderOf_x_gt
    omega
  exact h1125 G A c₁ L₁ a₂ R₁ Y₂ d x₁ s₁ r₂ g₂ hbig₂ hcdN hNd hsc hrs ⟨j, hj, hjinv⟩

theorem sec11Never_of_steps
    (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hex : Sec11DataExists) (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118)
    (h1119 : Item1119) (h1123 : Item1123) (hinv : Inverter1118) (hch : Choose1128)
    (h1132 : Item1132) : Sec11Never :=
  sec11Never_of hex
    (item1128_of h45 h1116 h1117 (item1118_of h1116 h1117 hset
      (sec11BigNever_of h113 h117 h1117 h1119 h1123 (item1125_of h45 h113) hinv)) hch)
    h1132 item1133

theorem hyp91Never_of_steps (h1016 : Sec10.Item1016) (h97 : Sec9.Item97) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h113 : Item113) (h117 : Item117) (hex : Sec11DataExists)
    (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118) (h1119 : Item1119)
    (h1123 : Item1123) (hinv : Inverter1118) (hch : Choose1128) (h1132 : Item1132) :
    Hyp91Never :=
  hyp91Never_of_item1016 h1016 (setUp11_of h97 h45 h48)
    (sec11Never_of_steps h45 h113 h117 hex h1116 h1117 hset h1119 h1123 hinv hch h1132)

theorem item1134_of_steps (h812 : Sec8.Item812) (h1016 : Sec10.Item1016) (h97 : Sec9.Item97)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113) (h117 : Item117)
    (hex : Sec11DataExists) (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118)
    (h1119 : Item1119) (h1123 : Item1123) (hinv : Inverter1118) (hch : Choose1128)
    (h1132 : Item1132) : Item1134 :=
  item1134_of_item45 h812
    (hyp91Never_of_steps h1016 h97 h45 h48 h113 h117 hex h1116 h1117 hset h1119 h1123 hinv hch
      h1132) h45

end CFSG.RankThree.PartTwo.Sec11
