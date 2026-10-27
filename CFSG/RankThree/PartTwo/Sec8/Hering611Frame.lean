module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs
public import CFSG.RankThree.PartTwo.Sec8.Hering611Setup
public import CFSG.RankThree.PartTwo.Sec8.Hering611Lift
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofField
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

@[expose] def stabV {M : Type*} [Group M] (V : Subgroup M) : Subgroup (MulAut M) where
  carrier := {σ | ∀ v, v ∈ V ↔ σ v ∈ V}
  mul_mem' := by
    intro σ τ hσ hτ v
    rw [hτ v, hσ (τ v)]
    rfl
  one_mem' := fun v => Iff.rfl
  inv_mem' := by
    intro σ hσ v
    rw [hσ (σ⁻¹ v)]
    simp

theorem eq_one_of_mem_zpowers_of_isInnerAut {M : Type*} [Group M] {τ σ : MulAut M}
    (hτ3 : τ ^ 3 = 1) (hout : ¬ IsInnerAut τ) (hσ : σ ∈ Subgroup.zpowers τ)
    (hin : IsInnerAut σ) : σ = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have hk : τ ^ k = τ ^ (k % 3) := by
    have : τ ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hτ3]
    exact zpow_eq_zpow_emod k this
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · rw [hk, h, zpow_zero]
  · exfalso
    rw [hk, h, zpow_one] at hin
    exact hout hin
  · exfalso
    rw [hk, h] at hin
    apply hout
    have h2 : τ = (τ ^ (2 : ℤ)) ^ (2 : ℕ) := by
      rw [← zpow_natCast, ← zpow_mul]
      have : τ ^ (4 : ℤ) = τ := by
        rw [show (4 : ℤ) = ((3 : ℕ) : ℤ) + 1 by norm_num, zpow_add, zpow_natCast, hτ3, one_mul,
          zpow_one]
      simpa using this.symm
    rw [h2]
    exact (MulAut.conj : M →* MulAut M).range.pow_mem hin 2


structure EV611 {G : Type} [Group G] [Finite G] (A : Subgroup G) (c a : G) (L E : Subgroup G)
    (V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Prop where
  E_le : E ≤ A
  E_elem : CFSG.Assembly.IsElemAbelian 3 E
  E_card : Nat.card E = 27
  c_mem : c ∈ E
  a_mem : a ∈ E
  a_not_mem : a ∉ Subgroup.zpowers c
  H_le : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ E
  H_card : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers a : Subgroup G) = 9
  V_elem : CFSG.Assembly.IsElemAbelian 2 V
  V_card : Nat.card V = 4
  V_inv : ∀ (g : G) (_ : g ∈ E) (hgN : g ∈ Subgroup.normalizer (L : Set G)), ∀ v ∈ V,
    actHom L ⟨g, hgN⟩ v ∈ V
  a_fix : ∀ (haN : a ∈ Subgroup.normalizer (L : Set G)), ∀ v ∈ V, actHom L ⟨a, haN⟩ v = v
  b_move : ∃ b ∈ E, ∃ v0 ∈ V, ∀ hbN : b ∈ Subgroup.normalizer (L : Set G),
    actHom L ⟨b, hbN⟩ v0 ≠ v0

section Frame


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem exists_EV (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (h9 : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = 9) :
    ∃ (E : Subgroup G) (V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)), EV611 A c a L E V ∧
      ∀ d' ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a, d' ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d' .field := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hbA, x, V, hx1, hx3, hbx, hVe, hV4, hVa, hxV, v0, hv0V, hv0⟩ :=
    exists_xV h h81 hAN e₁ h9
  have hAF := h.mem_partTwoF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  have hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hset := Sec13.sectionCentralizer_eq_inf hAN
    rw [h.sectionCentralizer_eq] at hset
    exact SetLike.coe_injective hset.symm
  set ρ : A →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (actHom L).comp (Subgroup.inclusion hAN) with hρ
  have hρapp : ∀ (g : G) (hg : g ∈ A),
      ρ ⟨g, hg⟩ = thetaQuotMulAut L (compAction L ⟨g, hAN hg⟩) := fun g hg => rfl
  have hρc : ρ ⟨c, h.mem_A⟩ = 1 := by
    have hcC : c ∈ thetaQuotCentralizer L := by
      have : c ∈ A ⊓ thetaQuotCentralizer L := by rw [hCA]; exact Subgroup.mem_zpowers c
      exact this.2
    obtain ⟨y, hy, hyc⟩ := hcC
    have hy' : y = ⟨c, hAN h.mem_A⟩ := Subtype.ext hyc
    rw [hρapp, ← hy']
    exact MonoidHom.mem_ker.mp hy
  have hρa : ρ ⟨a, h.a_mem⟩ = thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) := rfl
  have hVa' : ∀ v ∈ V, ρ ⟨a, h.a_mem⟩ v = v := hVa
  have hρb : ρ ⟨b, hbA⟩ = MulAut.conj x := by rw [hρapp]; exact hbx
  have hτ3 : ρ ⟨a, h.a_mem⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, h.a_mem⟩ : A) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hτout : ¬ IsInnerAut (ρ ⟨a, h.a_mem⟩) := h.not_isInnerAut_induced
  have hac : a ∉ Subgroup.zpowers c := by
    intro hac
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hac
    apply hτout
    have : (⟨a, h.a_mem⟩ : A) = (⟨c, h.mem_A⟩ : A) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow, hρc, one_zpow]
    exact ⟨1, map_one _⟩
  have hHA : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr h.a_mem)
  obtain ⟨hHe, hHcard⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3)
    (isElemAbelian_zpowers hc3) hac ha3 (fun u hu => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (show Commute c a from hcomm c h.mem_A a h.a_mem) i).eq)
  have hH9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers a : Subgroup G) = 9 := by
    rw [hHcard, Nat.card_zpowers, orderOf_eq_prime hc3 h.ne_one]
  have hHρ : ∀ (g : G) (hg : g ∈ A), g ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a →
      ρ ⟨g, hg⟩ ∈ Subgroup.zpowers (ρ ⟨a, h.a_mem⟩) := by
    set S1 : Subgroup G := ((Subgroup.zpowers (ρ ⟨a, h.a_mem⟩)).comap ρ).map A.subtype with hS1
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ S1 := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact ⟨⟨c, h.mem_A⟩, Subgroup.mem_comap.mpr (by rw [hρc]; exact Subgroup.one_mem _), rfl⟩
      · exact ⟨⟨a, h.a_mem⟩, Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _), rfl⟩
    intro g hg hgH
    obtain ⟨y, hy, hyg⟩ := hle hgH
    have hy' : y = ⟨g, hg⟩ := Subtype.ext hyg
    rw [← hy']
    exact Subgroup.mem_comap.mp hy
  have hbH : b ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers a := by
    intro hbH
    have hy2 := hHρ b hbA hbH
    rw [hρb] at hy2
    have h1 := eq_one_of_mem_zpowers_of_isInnerAut hτ3 hτout hy2 (isInnerAut_conj x)
    exact hx1 h1
  set E : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b with hE
  obtain ⟨hEe, hEcard⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3) hHe hbH hb3
    (fun u hu => hcomm u (hHA hu) b hbA)
  have hE27 : Nat.card E = 27 := by rw [hE, hEcard, hH9]
  have hEA : E ≤ A := sup_le hHA (Subgroup.zpowers_le.mpr hbA)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans hAN
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEe
  have hcE : c ∈ E :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have haE : a ∈ E :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hbE : b ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hstabE : ∀ (g : G) (hg : g ∈ A), g ∈ E → ρ ⟨g, hg⟩ ∈ stabV V := by
    have hle : E ≤ ((stabV V).comap ρ).map A.subtype := by
      refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
        (Subgroup.zpowers_le.mpr ?_)
      · exact ⟨⟨c, h.mem_A⟩, Subgroup.mem_comap.mpr (by rw [hρc]; exact Subgroup.one_mem _), rfl⟩
      · refine ⟨⟨a, h.a_mem⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
        intro v
        constructor
        · intro hv
          rw [hVa' v hv]
          exact hv
        · intro hv
          have h1 := hVa' _ hv
          have h2 : ρ ⟨a, h.a_mem⟩ (ρ ⟨a, h.a_mem⟩ v) = ρ ⟨a, h.a_mem⟩ v := h1
          have h3 := (ρ ⟨a, h.a_mem⟩).injective h2
          rw [← h3]
          exact hv
      · refine ⟨⟨b, hbA⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
        rw [hρb]
        intro v
        constructor
        · intro hv
          exact hxV v hv
        · intro hv
          simp only [MulAut.conj_apply] at hv
          have h1 := hxV _ hv
          have h2 := hxV _ h1
          have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
          have h3 : v = x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ := by
            calc v = (x * (x * x)) * v * (x * (x * x))⁻¹ := by rw [hx3']; simp
              _ = x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ := by group
          rw [h3]
          exact h2
    intro g hg hgE
    obtain ⟨y, hy, hyg⟩ := hle hgE
    have : y = ⟨g, hg⟩ := Subtype.ext hyg
    rw [← this]
    exact hy
  have hinv : ∀ (g : G) (hg : g ∈ E), ∀ v ∈ V, actHom L ⟨g, hEN hg⟩ v ∈ V := by
    intro g hg v hv
    exact ((hstabE g (hEA hg) hg) v).mp hv
  have hfield : ∀ d' ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a, d' ∉ Subgroup.zpowers c →
      KFacts.InducesStdKind L d' .field := by
    intro d' hd'H hd'c
    have hd'A : d' ∈ A := hHA hd'H
    have hd'3 : d' ^ 3 = 1 := hAe.2 d' hd'A
    have hρd : ρ ⟨d', hd'A⟩ ∈ Subgroup.zpowers (ρ ⟨a, h.a_mem⟩) := hHρ d' hd'A hd'H
    have hnin : ¬ IsInnerAut (ρ ⟨d', hd'A⟩) := by
      intro hin
      have h1 := eq_one_of_mem_zpowers_of_isInnerAut hτ3 hτout hρd hin
      apply hd'c
      rw [← hCA]
      exact ⟨hd'A, ⟨⟨d', hAN hd'A⟩, h1, rfl⟩⟩
    exact .psl2 (GaloisField 3 (3 * 2))
      ⟨e₁.trans (projSLEquivPSL _),
        inducesKind_field_of_pow_three L hd'3 ⟨hAN hd'A, hnin⟩ _⟩
  refine ⟨E, V, ⟨hEA, hEe, hE27, hcE, haE, hac, le_sup_left, hH9, hVe, hV4,
    fun g hg hgN v hv => hinv g hg v hv, fun haN v hv => hVa v hv,
    b, hbE, v0, hv0V, fun hbN hbad => hv0 ?_⟩, hfield⟩
  have h1 : ρ ⟨b, hbA⟩ v0 = v0 := hbad
  rw [hρb] at h1
  exact h1

theorem exists_frame (h45 : Sec4.Item4_5) (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (h9 : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = 9)
    {E : Subgroup G} {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (D : EV611 A c a L E V)
    (hfH : ∀ d' ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a, d' ∉ Subgroup.zpowers c →
      KFacts.InducesStdKind L d' .field) :
    ∃ T : Subgroup G, Frame611 G A c L E T a ∧
      ∀ d' ∈ E ⊓ Subgroup.centralizer (T : Set G), d' ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d' .field := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAF := h.mem_partTwoF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hset := Sec13.sectionCentralizer_eq_inf hAN
    rw [h.sectionCentralizer_eq] at hset
    exact SetLike.coe_injective hset.symm
  have hEA := D.E_le
  have hEe := D.E_elem
  have hE27 := D.E_card
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans hAN
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEe
  have hcE := D.c_mem
  have haE := D.a_mem
  have hac := D.a_not_mem
  have hV4 := D.V_card
  have hVe := D.V_elem
  have hH9 := D.H_card
  have hinv : ∀ (g : G) (hg : g ∈ E), ∀ v ∈ V, actHom L ⟨g, hEN hg⟩ v ∈ V :=
    fun g hg v hv => D.V_inv g hg (hEN hg) v hv
  obtain ⟨b, hbE, v0, hv0V, hbmv⟩ := D.b_move
  have hAFa : A ∈ partTwoF G := hAF
  have hθodd := Sec6.Res611Res3.odd_card_theta h.evenRank_eq hAe (by omega : 81 ≤ Nat.card A) hAN
  obtain ⟨T, hTL, hT2, hTcard, hET, hTθ, hTV, hTsurj⟩ :=
    exists_invariant_lift hθodd hE3 hEN hV4 hinv
  have hTinj : ∀ t₁ t₂ : L, (t₁ : G) ∈ T → (t₂ : G) ∈ T → qL L t₁ = qL L t₂ → t₁ = t₂ := by
    intro t₁ t₂ h1 h2 h12
    have hker : t₁⁻¹ * t₂ ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq).mp h12
    have hmem : ((t₁⁻¹ * t₂ : L) : G) ∈ T ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
      ⟨T.mul_mem (T.inv_mem h1) h2, ⟨_, hker, rfl⟩⟩
    rw [hTθ, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp (Subtype.ext hmem)
  have hT1 : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hTcard
    omega
  have hTe : CFSG.Assembly.IsElemAbelian 2 T := by
    refine ⟨⟨⟨fun t₁ t₂ => ?_⟩⟩, fun t ht => ?_⟩
    · apply Subtype.ext
      set l₁ : L := ⟨t₁, hTL t₁.2⟩ with hl₁
      set l₂ : L := ⟨t₂, hTL t₂.2⟩ with hl₂
      have : l₁ * l₂ = l₂ * l₁ :=
        hTinj _ _ (T.mul_mem t₁.2 t₂.2) (T.mul_mem t₂.2 t₁.2) (by
          rw [map_mul, map_mul]
          exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨qL L l₁, hTV l₁ t₁.2⟩
            ⟨qL L l₂, hTV l₂ t₂.2⟩))
      exact congrArg (fun l : L => (l : G)) this
    · set l : L := ⟨t, hTL ht⟩ with hl
      have hl2 : l ^ 2 = 1 :=
        hTinj _ _ (by simpa using T.pow_mem ht 2) T.one_mem (by
          rw [map_pow, map_one]
          exact hVe.2 _ (hTV l ht))
      simpa using congrArg Subtype.val hl2
  have hTfour : T ∈ fourGroups E := by
    refine ⟨(mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT2, hET⟩, hTe, hTcard⟩
  obtain ⟨t0, ht0T, ht0q⟩ := hTsurj v0 hv0V
  have hbmove : b * (t0 : G) * b⁻¹ ≠ t0 := by
    intro hbt
    apply hbmv (hEN hbE)
    have h1 : compAction L ⟨b, hEN hbE⟩ t0 = t0 := Subtype.ext hbt
    have h2 : qL L (compAction L ⟨b, hEN hbE⟩ t0) = qL L t0 := by rw [h1]
    have h3 : actHom L ⟨b, hEN hbE⟩ (qL L t0) = qL L t0 := h2
    rw [ht0q] at h3
    exact h3
  have hYT : ⁅T, E⁆ ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.mp hET
  have hTE : T = ⁅T, E⁆ := by
    refine le_antisymm ?_ ?_
    swap
    · exact hYT
    set Y := ⁅T, E⁆ with hY
    have hidem : ⁅Y, E⁆ = Y :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
        Nat.prime_three E T hE3 (by rw [hTcard]; norm_num) hET
    have hY1 : Y ≠ ⊥ := by
      intro hbot
      have hmem : ⁅(t0 : G), b⁆ ∈ Y := Subgroup.commutator_mem_commutator ht0T hbE
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      apply hbmove
      exact mul_inv_eq_iff_eq_mul.mpr hmem.symm
    have hYN : E ≤ Subgroup.normalizer (Y : Set G) :=
      Sec6.Res611Field.le_normalizer_commutator_of hET (fun g hg => Subgroup.le_normalizer hg)
    have hYcard : Nat.card Y ∣ 4 := by
      rw [← hTcard]
      exact Subgroup.card_dvd_of_le hYT
    by_contra hYT'
    have hYlt : ¬ Nat.card Y = 4 := by
      intro h4
      exact hYT' (Subgroup.eq_of_le_of_card_ge hYT (by rw [h4, hTcard])).ge
    have hY2 : Nat.card Y = 2 := by
      obtain ⟨i, hi, hiY⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show Nat.card Y ∣ 2 ^ 2 by simpa using hYcard)
      interval_cases i
      · exact absurd (Subgroup.card_eq_one.mp (by simpa using hiY)) hY1
      · simpa using hiY
      · exact absurd (by simpa using hiY) hYlt
    obtain ⟨y0, hy0, huniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hY2
    have hEcent : E ≤ Subgroup.centralizer (Y : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hgy : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hYN hg) y).mp hy
      by_cases hy1 : y = 1
      · rw [hy1]; simp
      · have h1 : (⟨y, hy⟩ : Y) = y0 := huniq _ (fun h1 => hy1 (congrArg Subtype.val h1))
        have h2 : (⟨g * y * g⁻¹, hgy⟩ : Y) = y0 := huniq _ (fun h1 => by
          have := congrArg Subtype.val h1
          simp only [OneMemClass.coe_one] at this
          apply hy1
          have h3 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
          rw [h3, this]; group)
        have h4 : g * y * g⁻¹ = y := congrArg Subtype.val (h2.trans h1.symm)
        calc y * g = (g * y * g⁻¹) * g := by rw [h4]
          _ = g * y := by group
    have hYbot : ⁅Y, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hEcent
    exact hY1 (by rw [← hidem, hYbot])
  have haT : a ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hat : a * t * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hET haE) t).mp ht
    set l : L := ⟨t, hTL ht⟩ with hl
    set l' : L := compAction L ⟨a, hAN h.a_mem⟩ l with hl'
    have hl'T : (l' : G) ∈ T := hat
    have hql : qL L l' = qL L l := D.a_fix (hAN h.a_mem) _ (hTV l ht)
    have : l' = l := hTinj _ _ hl'T ht hql
    have h5 : a * t * a⁻¹ = t := congrArg Subtype.val this
    calc t * a = (a * t * a⁻¹) * a := by rw [h5]
      _ = a * t := by group
  have hEmem : E ∈ partTwoE G := ⟨hEe, hE27, T, hT1, hT2, hET⟩
  have hnotE : A ∉ partTwoE G := fun hA => by
    have := hA.2.1
    omega
  have hAS : A ∈ partTwoS G :=
    h.toTheoremFourHyp.partTwoF_diff_partTwoE_subset ⟨hAF, hnotE⟩
  have hEcoll : E ∈ collectionIn (partTwoE G) A := ⟨hEmem, hEA⟩
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_thetaComponentsAt
  have hL0 : L ∈ lZero E := by
    refine ⟨mem_thetaComponentFamily_iff.mpr ⟨c, hcE, h.ne_one, hLc⟩, T,
      (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hTL, hT2, hET⟩, ?_⟩
    rw [← hTE]
    intro hle
    apply hT1
    rw [eq_bot_iff, ← hTθ]
    exact le_inf le_rfl hle
  have hLs : L ∈ lZeroStarAt A c :=
    Sec6.mem_lZeroStarAt_of_inf_le_zpowers h45 h.toPartTwoStanding hAS hEcoll hcE h.ne_one hLc
      hL0 hCA.le
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hcT : c ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hTL ht))
  have hHle : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ E ⊓ Subgroup.centralizer (T : Set G) :=
    le_inf D.H_le (sup_le (Subgroup.zpowers_le.mpr hcT)
      (Subgroup.zpowers_le.mpr haT))
  have hC9 : Nat.card (E ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) = 9 :=
    Sec6.card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hEmem)
      ⟨hTfour, hTE⟩
  have hCH : Subgroup.zpowers c ⊔ Subgroup.zpowers a = E ⊓ Subgroup.centralizer (T : Set G) :=
    Subgroup.eq_of_le_of_card_ge hHle (by rw [hC9, hH9])
  have hfield : ∀ d' ∈ E ⊓ Subgroup.centralizer (T : Set G), d' ∉ Subgroup.zpowers c →
      KFacts.InducesStdKind L d' .field := by
    intro d' hd' hd'c
    exact hfH d' (by rw [hCH]; exact hd') hd'c
  refine ⟨T, ?_, hfield⟩
  exact
    { standing := h.toPartTwoStanding
      mem_S := hAS
      card_A := h81
      c_mem := h.mem_A
      c_ne_one := h.ne_one
      mem_L := hLs
      cent_L := hCA
      iso_L := ⟨e₁⟩
      mem_E := hEcoll
      c_mem_E := hcE
      mem_lZero := hL0
      mem_T := ⟨hTfour, hTE⟩
      T_le_L := hTL
      T_theta := hTθ
      d_mem := ⟨haE, haT⟩
      d_not_mem := hac
      d_field := hfH a (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) hac
      inner_nine := h9 }

theorem exists_frame_all (h45 : Sec4.Item4_5) (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (h9 : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = 9) :
    ∃ E T : Subgroup G, Frame611 G A c L E T a ∧
      ∀ d' ∈ E ⊓ Subgroup.centralizer (T : Set G), d' ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d' .field := by
  obtain ⟨E, V, D, hfH⟩ := exists_EV h h81 hAN e₁ h9
  obtain ⟨T, hF, hfield⟩ := exists_frame h45 h h81 hAN e₁ h9 D hfH
  exact ⟨E, T, hF, hfield⟩

end Frame

end CFSG.RankThree.PartTwo.Sec8.Hering611
