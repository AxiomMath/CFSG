module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.ClassicalInvolution.TwoGroupCase.TwoGroupTI
public import CFSG.ClassicalInvolution.TwoGroupCase.TightPairDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open
open scoped MatrixGroups

section Tight

variable {G : Type} [Group G]

@[expose] def IsTightlyEmbedded (K : Subgroup G) : Prop :=
  Even (Nat.card ↥K) ∧ ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
    Odd (Nat.card ↥(K ⊓ CFSG.conjugate K g))

@[expose] def IsTightlyEmbeddedIn (T S : Subgroup G) : Prop :=
  T ≤ S ∧ Even (Nat.card ↥T) ∧ ∀ s ∈ S, s ∉ Subgroup.normalizer (T : Set G) →
    Odd (Nat.card ↥(T ⊓ CFSG.conjugate T s))

@[expose] def IsTIIn (T S : Subgroup G) : Prop :=
  T ≤ S ∧ ∀ s ∈ S, s ∉ Subgroup.normalizer (T : Set G) → T ⊓ CFSG.conjugate T s = ⊥

@[expose] def IsTIUnder (Q M : Subgroup G) : Prop :=
  ∀ m ∈ M, CFSG.conjugate Q m ≠ Q → Q ⊓ CFSG.conjugate Q m = ⊥

@[expose] def IsSylowTwoIn (Q M : Subgroup G) : Prop :=
  Q ≤ M ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ (Q.subgroupOf M).index

@[expose] def IsSpecialGroup (W : Subgroup G) : Prop :=
  frattiniOf W = centerOf W ∧ ⁅W, W⁆ = centerOf W

structure HypI7 (K H Q S : Subgroup G) : Prop where
  tight : IsTightlyEmbedded K
  Q_ne_bot : Q ≠ ⊥
  Q_sylow : IsSylowTwoIn Q (H ⊓ K)
  S_le : S ≤ H
  S_two : IsPGroup 2 S
  Q_le_S : Q ≤ S

end Tight

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    Q = S ⊓ K ∧
    (∀ g ∈ H, Q ≠ CFSG.conjugate Q g → CFSG.conjugate Q g ≤ S → Q ⊓ CFSG.conjugate Q g = ⊥) ∧
    (Q ≤ S ∧ IsTIUnder Q (Subgroup.normalizer (S : Set G))) ∧
    (∀ T : Subgroup G, T ≠ ⊥ → IsTIIn T S → IsTightlyEmbeddedIn T S) ∧
    (∀ X : Subgroup G, X ≠ ⊥ → X ≤ Q →
      Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      S ⊓ Subgroup.normalizer (X : Set G) ≤ S ⊓ Subgroup.normalizer (Q : Set G))

section BurnsideIa

private theorem burnsideIa_setup_of_hyp {G : Type} [Group G] {K H Q S : Subgroup G}
    (h : CFSG.ASVolI.ChIJK.HypI7 K H Q S) :
    CFSG.QuasithinUnique.Tight.Setup K H Q S :=
  ⟨h.tight, h.Q_sylow, h.Q_ne_bot, h.S_two, h.S_le, h.Q_le_S⟩

end BurnsideIa

open CFSG.ASVolI.ChIJK in
theorem as_I_7_2 : I_7_2 := by
  intro G _ _ K H Q S h
  have hs := burnsideIa_setup_of_hyp h
  refine ⟨hs.eq_inf.symm, ?_, ?_, ?_, ?_⟩
  · intro g hg hne hQS
    exact hs.inf_conjugate_eq_bot hg hQS hne.symm
  · refine ⟨h.Q_le_S, ?_⟩
    intro m hm hne
    by_contra hbot
    have hX2 : IsPGroup 2 (Q ⊓ CFSG.conjugate Q m : Subgroup G) :=
      hs.two.to_le (inf_le_left.trans h.Q_le_S)
    have hXK : Q ⊓ CFSG.conjugate Q m ≤ K ⊓ CFSG.conjugate K m :=
      le_inf (inf_le_left.trans hs.Q_le_K)
        (inf_le_right.trans (CFSG.QuasithinUnique.BenderBranch.conjugate_mono hs.Q_le_K m))
    have hmK : m ∈ Subgroup.normalizer (K : Set G) :=
      CFSG.QuasithinUnique.Tight.mem_normalizer_of_two_subgroup hs.tight hX2 hbot hXK
    have hK' : CFSG.conjugate K m = K :=
      CFSG.QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hmK
    have hS' : CFSG.conjugate S m = S :=
      CFSG.QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hm
    have hQle : CFSG.conjugate Q m ≤ S ⊓ K :=
      le_inf ((CFSG.QuasithinUnique.BenderBranch.conjugate_mono h.Q_le_S m).trans hS'.le)
        ((CFSG.QuasithinUnique.BenderBranch.conjugate_mono hs.Q_le_K m).trans hK'.le)
    rw [hs.eq_inf] at hQle
    have hcard : Nat.card ↥Q ≤ Nat.card ↥(CFSG.conjugate Q m) :=
      (CFSG.QuasithinUnique.BenderBranch.card_conjugate Q m).symm.le
    exact hne (Subgroup.eq_of_le_of_card_ge hQle hcard)
  · intro T hT hTI
    obtain ⟨hTS, hTI'⟩ := hTI
    have hT2 : IsPGroup 2 T := hs.two.to_le hTS
    have hev : Even (Nat.card ↥T) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases hT2.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hT
      · exact even_iff_two_dvd.mpr h1
    unfold IsTightlyEmbeddedIn
    refine ⟨hTS, hev, fun s hs' hns => ?_⟩
    rw [hTI' s hs' hns, Subgroup.card_bot]
    exact odd_one
  · intro X hX1 hXQ
    obtain ⟨h1, h2⟩ := hs.normalizer_le hXQ hX1
    exact ⟨h1, le_inf inf_le_left h2⟩

@[expose] def I_7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    Q.relIndex S ≤ Nat.card ↥Q → IsNormalIn Q S

open CFSG.ASVolI.ChIJK in
theorem as_I_7_3 : I_7_3 := by
  intro G _ _ K H Q S h hrel
  have hs := burnsideIa_setup_of_hyp h
  have hidx : Q.relIndex S * Nat.card ↥Q = Nat.card ↥S := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := S)
    rwa [inf_eq_left.mpr h.Q_le_S] at this
  have hcard : Nat.card ↥S ≤ Nat.card ↥Q ^ 2 := by
    rw [← hidx, sq]
    exact Nat.mul_le_mul_right _ hrel
  have hN : S ≤ Subgroup.normalizer (Q : Set G) := hs.normal_of_card_le hcard
  unfold IsNormalIn
  exact ⟨h.Q_le_S, Subgroup.normal_subgroupOf_of_le_normalizer hN⟩

@[expose] def I_7_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    ∀ g ∈ H, Q ≠ CFSG.conjugate Q g →
      CFSG.conjugate Q g ≤ S ⊓ Subgroup.normalizer (Q : Set G) →
      IsDirectProductOf Q (CFSG.conjugate Q g) (Q ⊔ CFSG.conjugate Q g)

open CFSG.ASVolI.ChIJK in
theorem as_I_7_4 : I_7_4 := by
  intro G _ _ K H Q S h g hg hne hQg
  have hs := burnsideIa_setup_of_hyp h
  have hcomm := hs.commute_of_conj hg hne.symm hQg
  have hbot := hs.inf_conjugate_eq_bot hg (hQg.trans inf_le_left) hne.symm
  unfold IsDirectProductOf
  exact ⟨hcomm, hbot, rfl⟩

@[expose] def I_7_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    frattiniOf Q ≠ ⊥ →
      ∀ h ∈ H, ∀ k ∈ H, CFSG.conjugate Q h ≤ S → CFSG.conjugate Q k ≤ S →
        CFSG.conjugate Q h ≠ CFSG.conjugate Q k →
        IsDirectProductOf (CFSG.conjugate Q h) (CFSG.conjugate Q k)
          (CFSG.conjugate Q h ⊔ CFSG.conjugate Q k)

section BurnsideIb

private theorem burnsideIb_isSylow2Of {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (h : ChIJK.IsSylowTwoIn Q M) : CFSG.ClassicalInvolution.IsSylow2Of Q M := by
  obtain ⟨hQM, hQ2, hidx⟩ := h
  refine CFSG.ClassicalInvolution.isSylow2Of_of_card hQM hQ2 ?_
  have h1 := Subgroup.card_mul_index (Q.subgroupOf M)
  have h2 : Nat.card (Q.subgroupOf M) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  rw [h2] at h1
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hidx0 : (Q.subgroupOf M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hf : (Nat.card M).factorization 2 = k + ((Q.subgroupOf M).index).factorization 2 := by
    rw [← h1, hk, Nat.factorization_mul (pow_ne_zero k two_ne_zero) hidx0]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have hz : ((Q.subgroupOf M).index).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hidx
  rw [hf, hz, add_zero, hk]

private theorem burnsideIb_isSylowTwoIn {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (h : CFSG.ClassicalInvolution.IsSylow2Of Q M) : ChIJK.IsSylowTwoIn Q M := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hc := h.card_eq
  have h1 := Subgroup.card_mul_index (Q.subgroupOf M)
  have h2 : Nat.card (Q.subgroupOf M) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  rw [h2, hc] at h1
  have hidx0 : (Q.subgroupOf M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hf : ((2 ^ (Nat.card M).factorization 2) * (Q.subgroupOf M).index).factorization 2 =
      (Nat.card M).factorization 2 := by rw [h1]
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hidx0] at hf
  simp [Nat.Prime.factorization_self Nat.prime_two] at hf
  intro hdvd
  have : 0 < ((Q.subgroupOf M).index).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hidx0 hdvd
  omega

private theorem burnsideIb_tightData {G : Type} [Group G] [Finite G] {K H Q S : Subgroup G}
    (h : ChIJK.HypI7 K H Q S) : CFSG.ClassicalInvolution.TightData K H Q S := by
  refine ⟨?_, burnsideIb_isSylow2Of h.Q_sylow, h.Q_ne_bot, h.S_two, h.S_le, h.Q_le_S⟩
  intro g hg
  have hg' : g⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h' =>
    hg (by simpa using Subgroup.inv_mem _ h')
  have := h.tight.2 g⁻¹ hg'
  simpa [CFSG.conjugate] using this

private theorem burnsideIb_exists_mul_self_ne_one {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hΦ : ChIJK.frattiniOf Q ≠ ⊥) : ∃ x ∈ Q, x * x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hΦ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  haveI : CFSG.IsElementaryAbelian 2 Q :=
    { is_comm := ⟨fun a b => Subtype.ext
        (CFSG.ClassicalInvolution.commute_of_mul_self_eq_one (hcon a a.2) (hcon b b.2)
          (hcon _ (Q.mul_mem a.2 b.2)))⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
        rw [pow_two]
        exact Subtype.ext (hcon x x.2) }
  unfold ChIJK.frattiniOf
  rw [CFSG.frattini_eq_bot_of_isElementaryAbelian (R := Q) (p := 2)]
  simp



private theorem burnsideIb_card_le_mul {G : Type} [Group G] [Finite G] {A B S₁ : Subgroup G}
    (hAB : A ≤ B) (f : G → G) (hf : ∀ b ∈ B, f b ∈ S₁)
    (hiff : ∀ a ∈ B, ∀ b ∈ B, f a = f b ↔ a⁻¹ * b ∈ A) :
    Nat.card B ≤ Nat.card A * Nat.card S₁ ∧
      (Nat.card B = Nat.card A * Nat.card S₁ → ∀ s ∈ S₁, ∃ b ∈ B, f b = s) := by
  classical
  let A' : Subgroup B := A.subgroupOf B
  let φ : B ⧸ A' → S₁ := Quotient.lift (fun b : B => (⟨f b, hf b b.2⟩ : S₁)) (by
    intro a b hab
    have h0 : a⁻¹ * b ∈ A' := QuotientGroup.leftRel_apply.mp hab
    have h1 : (a : G)⁻¹ * b ∈ A := h0
    exact Subtype.ext ((hiff a a.2 b b.2).mpr h1))
  have hφ : Function.Injective φ := by
    intro x y hxy
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    have h1 : f a = f b := congrArg Subtype.val hxy
    have h2 : (a : G)⁻¹ * b ∈ A := (hiff a a.2 b b.2).mp h1
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (show a⁻¹ * b ∈ A' from h2))
  have hcard : Nat.card B = Nat.card (B ⧸ A') * Nat.card A := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A'
    have h2 : Nat.card A' = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
    rw [h2] at h1
    exact h1
  have hle : Nat.card (B ⧸ A') ≤ Nat.card S₁ := Nat.card_le_card_of_injective φ hφ
  refine ⟨?_, fun heq s hs => ?_⟩
  · rw [hcard, mul_comm]
    exact Nat.mul_le_mul_left _ hle
  · have hge : Nat.card S₁ ≤ Nat.card (B ⧸ A') := by
      rw [hcard, mul_comm] at heq
      exact (Nat.le_of_mul_le_mul_left heq.ge Nat.card_pos)
    have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le hge
    obtain ⟨y, hy⟩ := hbij.2 ⟨s, hs⟩
    induction y using Quotient.inductionOn with | _ b => ?_
    exact ⟨b, b.2, congrArg Subtype.val hy⟩

private theorem burnsideIb_commutator_mem {G : Type} [Group G] {M A B : Subgroup G} (hAM : A ≤ M)
    (hB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B) (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hMBA : ∀ m ∈ M, ∃ b ∈ B, ∃ a ∈ A, m = b * a) :
    ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ B := by
  intro m₁ hm₁ m₂ hm₂
  obtain ⟨b₁, hb₁, a₁, ha₁, rfl⟩ := hMBA m₁ hm₁
  obtain ⟨b₂, hb₂, a₂, ha₂, rfl⟩ := hMBA m₂ hm₂
  have hν₁ : b₁ * (a₁ * b₂ * a₁⁻¹) ∈ B := B.mul_mem hb₁ (hB a₁ (hAM ha₁) b₂ hb₂)
  have hν₂ : b₂ * (a₂ * b₁ * a₂⁻¹) ∈ B := B.mul_mem hb₂ (hB a₂ (hAM ha₂) b₁ hb₁)
  have hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 := by rw [hA a₁ ha₁ a₂ ha₂]; group
  have e : (b₁ * a₁) * (b₂ * a₂) * (b₁ * a₁)⁻¹ * (b₂ * a₂)⁻¹ =
      (b₁ * (a₁ * b₂ * a₁⁻¹)) * (b₂ * (a₂ * b₁ * a₂⁻¹))⁻¹ := by
    calc (b₁ * a₁) * (b₂ * a₂) * (b₁ * a₁)⁻¹ * (b₂ * a₂)⁻¹
        = (b₁ * (a₁ * b₂ * a₁⁻¹)) * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (b₂ * (a₂ * b₁ * a₂⁻¹))⁻¹ := by
          group
      _ = (b₁ * (a₁ * b₂ * a₁⁻¹)) * (b₂ * (a₂ * b₁ * a₂⁻¹))⁻¹ := by rw [hcomm, mul_one]
  rw [e]
  exact B.mul_mem hν₁ (B.inv_mem hν₂)

private theorem burnsideIb_le_or_le {G : Type} [Group G] {E N N' : Subgroup G}
    (h : ∀ e ∈ E, e ∈ N ∨ e ∈ N') : E ≤ N ∨ E ≤ N' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, huE, huN⟩ := SetLike.not_le_iff_exists.mp hcon.1
  obtain ⟨v, hvE, hvN'⟩ := SetLike.not_le_iff_exists.mp hcon.2
  have huN' : u ∈ N' := (h u huE).resolve_left huN
  have hvN : v ∈ N := (h v hvE).resolve_right hvN'
  rcases h (u * v) (E.mul_mem huE hvE) with h1 | h1
  · exact huN (by simpa using N.mul_mem h1 (N.inv_mem hvN))
  · exact hvN' (by simpa using N'.mul_mem (N'.inv_mem huN') h1)

private theorem burnsideIb_card_le_two_mul {G : Type} [Group G] [Finite G] {E J : Subgroup G}
    (hJE : J ≤ E) (w : G) (hw : ∀ y ∈ E, y ∈ J ∨ w⁻¹ * y ∈ J) (hwE : w ∈ E) :
    Nat.card E ≤ 2 * Nat.card J := by
  classical
  let f : E → Bool × J := fun y =>
    if hy : (y : G) ∈ J then (false, ⟨y, hy⟩)
    else (true, ⟨w⁻¹ * y, (hw y y.2).resolve_left hy⟩)
  have hf : Function.Injective f := by
    intro y y' hyy
    by_cases hy : (y : G) ∈ J <;> by_cases hy' : (y' : G) ∈ J
    · simp only [f, hy, hy', dif_pos] at hyy
      have h3 := congrArg Subtype.val (Prod.mk.inj hyy).2
      exact Subtype.ext h3
    · simp [f, hy, hy'] at hyy
    · simp [f, hy, hy'] at hyy
    · simp only [f, hy, hy', dif_neg, not_false_eq_true] at hyy
      have h3 := congrArg Subtype.val (Prod.mk.inj hyy).2
      exact Subtype.ext (mul_left_cancel h3)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at this
  simpa [mul_comm] using this

private theorem burnsideIb_centerOf_eq {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)
    (h1 : ∀ z ∈ T, ∀ m ∈ M, z * m = m * z)
    (h2 : ∀ z ∈ M, (∀ m ∈ M, z * m = m * z) → z ∈ T) : ChIJK.centerOf M = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine h2 y y.2 fun m hm => ?_
    have := Subgroup.mem_center_iff.mp hy ⟨m, hm⟩
    exact (congrArg Subtype.val this).symm
  · intro hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hTM hx⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact Subtype.ext (h1 x hx g g.2).symm

private theorem burnsideIb_commutator_eq {G : Type} [Group G] {M T : Subgroup G}
    (h1 : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ T)
    (h2 : ∀ s ∈ T, ∃ m₁ ∈ M, ∃ m₂ ∈ M, m₁ * m₂ * m₁⁻¹ * m₂⁻¹ = s) : ⁅M, M⁆ = T := by
  refine le_antisymm (Subgroup.commutator_le.mpr h1) fun s hs => ?_
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := h2 s hs
  exact Subgroup.commutator_mem_commutator hm₁ hm₂

private theorem burnsideIb_frattiniOf_eq {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hM : IsPGroup 2 M) (hTM : T ≤ M)
    (h1 : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ T) (h2 : ∀ m ∈ M, m * m ∈ T)
    (h3 : ∀ s ∈ T, ∃ m₁ ∈ M, ∃ m₂ ∈ M, m₁ * m₂ * m₁⁻¹ * m₂⁻¹ = s) :
    ChIJK.frattiniOf M = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 M) := ⟨hM⟩
  have hcomm : _root_.commutator ↥M ≤ T.subgroupOf M := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun a _ b _ => h1 a a.2 b b.2
  have hfr : frattini ↥M = T.subgroupOf M := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := M) (p := 2)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · exact hcomm hx
      · have h4 : (y : G) * y ∈ T := h2 y y.2
        show ((y ^ 2 : M) : G) ∈ T
        rw [pow_two]
        exact h4
    · intro s hs
      obtain ⟨m₁, hm₁, m₂, hm₂, hmm⟩ := h3 s hs
      refine Subgroup.subset_closure (Or.inl ?_)
      have h4 : (⟨m₁, hm₁⟩ : M) * ⟨m₂, hm₂⟩ * (⟨m₁, hm₁⟩ : M)⁻¹ * (⟨m₂, hm₂⟩ : M)⁻¹ ∈
          (⁅(⊤ : Subgroup M), ⊤⁆ : Subgroup M) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have h5 : (⟨m₁, hm₁⟩ : M) * ⟨m₂, hm₂⟩ * (⟨m₁, hm₁⟩ : M)⁻¹ * (⟨m₂, hm₂⟩ : M)⁻¹ =
          ⟨s, hTM hs⟩ := Subtype.ext hmm
      rw [h5] at h4
      show (⟨s, hTM hs⟩ : M) ∈ _root_.commutator ↥M
      rw [_root_.commutator_def]
      exact h4
  unfold ChIJK.frattiniOf
  rw [hfr]
  exact Subgroup.map_subgroupOf_eq_of_le hTM

abbrev burnsideIb_N {G : Type} [Group G] (S X : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.normalizer (X : Set G)

abbrev burnsideIb_M {G : Type} [Group G] (S R : Subgroup G) : Subgroup G :=
  burnsideIb_N S (burnsideIb_N S R)

abbrev burnsideIb_P {G : Type} [Group G] (S R : Subgroup G) : Subgroup G :=
  burnsideIb_N S (burnsideIb_M S R)

structure burnsideIb_EAData {G : Type} [Group G] (S S₀ R : Subgroup G) : Prop where
  two : IsPGroup 2 S
  S₀_le : S₀ ≤ S
  S₀_norm : ∀ s ∈ S, ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀
  R_le : R ≤ S
  R_inf : S₀ ⊓ R = ⊥
  S_eq : ∀ s ∈ S, ∃ a ∈ S₀, ∃ r ∈ R, s = a * r
  R_comm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r
  R_exp : ∀ r ∈ R, r * r = 1
  four_le : 4 ≤ Nat.card R
  N_comm : ∀ a ∈ burnsideIb_N S R, ∀ b ∈ burnsideIb_N S R, a * b = b * a
  N_exp : ∀ a ∈ burnsideIb_N S R, a * a = 1
  N_card : Nat.card (burnsideIb_N S R) = Nat.card R * Nat.card R
  S₁_card : Nat.card (S₀ ⊓ burnsideIb_N S R : Subgroup G) = Nat.card R
  cent : ∀ r ∈ R, r ≠ 1 → ∀ g ∈ S, g * r = r * g → g ∈ Subgroup.normalizer (R : Set G)

namespace burnsideIb_EAData

variable {G : Type} [Group G] {S S₀ R : Subgroup G} (h : burnsideIb_EAData S S₀ R)
include h

private theorem R_le_N : R ≤ burnsideIb_N S R := le_inf h.R_le Subgroup.le_normalizer

private theorem S₁_inf_R : (S₀ ⊓ burnsideIb_N S R) ⊓ R = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← h.R_inf]
  exact inf_le_inf inf_le_left le_rfl

private theorem R_ne_one : ∃ r ∈ R, r ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card R = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
    rw [hcon a a.2, hcon b b.2]
  have := h.four_le
  omega

private theorem mem_N_of_commute {r g : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hg : g ∈ S) (hc : g * r
    = r * g) :
    g ∈ burnsideIb_N S R := ⟨hg, h.cent r hr hr1 g hg hc⟩

private theorem N_comm_R {r g : G} (hr : r ∈ R) (hg : g ∈ burnsideIb_N S R) : g * r = r * g :=
  h.N_comm g hg r (h.R_le_N hr)

open CFSG.ClassicalInvolution in
private theorem N_eq_mul [Finite G] :
    ∀ a ∈ burnsideIb_N S R, ∃ s ∈ S₀ ⊓ burnsideIb_N S R, ∃ r ∈ R, a = s * r :=
  exists_mul_of_natCard_eq inf_le_right h.R_le_N h.S₁_inf_R (by rw [h.N_card, h.S₁_card])

private theorem N_le_M : burnsideIb_N S R ≤ burnsideIb_N S (burnsideIb_N S R) :=
  le_inf inf_le_left Subgroup.le_normalizer

private theorem conj_mem_N {m n : G} (hm : m ∈ burnsideIb_N S (burnsideIb_N S R))
    (hn : n ∈ burnsideIb_N S R) : m * n * m⁻¹ ∈ burnsideIb_N S R :=
  (Subgroup.mem_normalizer_iff.mp hm.2 n).mp hn

private theorem f_mem {m r : G} (hm : m ∈ burnsideIb_N S (burnsideIb_N S R)) (hr : r ∈ R) :
    r⁻¹ * (m * r * m⁻¹) ∈ S₀ ⊓ burnsideIb_N S R := by
  have hrN : r ∈ burnsideIb_N S R := h.R_le_N hr
  have h1 : m * r * m⁻¹ ∈ burnsideIb_N S R := h.conj_mem_N hm hrN
  refine ⟨?_, (burnsideIb_N S R).mul_mem ((burnsideIb_N S R).inv_mem hrN) h1⟩
  obtain ⟨a, ha, ρ, hρ, hmeq⟩ := h.S_eq m hm.1
  have e : r⁻¹ * (m * r * m⁻¹) = (r⁻¹ * a * r) * a⁻¹ := by
    have hc : ρ * r = r * ρ := h.R_comm ρ hρ r hr
    rw [hmeq]
    calc r⁻¹ * (a * ρ * r * (a * ρ)⁻¹) = r⁻¹ * (a * (ρ * r) * ρ⁻¹ * a⁻¹) := by group
      _ = r⁻¹ * (a * (r * ρ) * ρ⁻¹ * a⁻¹) := by rw [hc]
      _ = (r⁻¹ * a * r) * a⁻¹ := by group
  rw [e]
  refine S₀.mul_mem ?_ (S₀.inv_mem ha)
  have := h.S₀_norm r⁻¹ (S.inv_mem (h.R_le hr)) a ha
  simpa using this

private theorem f_eq_iff {m m' r : G} (hm : m ∈ burnsideIb_N S (burnsideIb_N S R))
    (hm' : m' ∈ burnsideIb_N S (burnsideIb_N S R)) (hr : r ∈ R) (hr1 : r ≠ 1) :
    r⁻¹ * (m * r * m⁻¹) = r⁻¹ * (m' * r * m'⁻¹) ↔ m⁻¹ * m' ∈ burnsideIb_N S R := by
  constructor
  · intro heq
    have h1 : m * r * m⁻¹ = m' * r * m'⁻¹ := mul_left_cancel heq
    have h2 : (m⁻¹ * m') * r = r * (m⁻¹ * m') := by
      calc (m⁻¹ * m') * r = m⁻¹ * (m' * r * m'⁻¹) * m' := by group
        _ = m⁻¹ * (m * r * m⁻¹) * m' := by rw [h1]
        _ = r * (m⁻¹ * m') := by group
    exact h.mem_N_of_commute hr hr1 (S.mul_mem (S.inv_mem hm.1) hm'.1) h2
  · intro hn
    have hc : (m⁻¹ * m') * r = r * (m⁻¹ * m') := h.N_comm_R hr hn
    have : m' * r * m'⁻¹ = m * r * m⁻¹ := by
      calc m' * r * m'⁻¹ = m * ((m⁻¹ * m') * r * (m⁻¹ * m')⁻¹) * m⁻¹ := by group
        _ = m * r * m⁻¹ := by rw [hc]; group
    rw [this]

private theorem card_M_le [Finite G] {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    Nat.card (burnsideIb_N S (burnsideIb_N S R)) ≤ Nat.card R * Nat.card R * Nat.card R ∧
      (Nat.card (burnsideIb_N S (burnsideIb_N S R)) = Nat.card R * Nat.card R * Nat.card R →
        ∀ s ∈ S₀ ⊓ burnsideIb_N S R, ∃ m ∈ burnsideIb_N S (burnsideIb_N S R),
          r⁻¹ * (m * r * m⁻¹) = s) := by
  have key := burnsideIb_card_le_mul (A := burnsideIb_N S R)
    (B := burnsideIb_N S (burnsideIb_N S R)) (S₁ := S₀ ⊓ burnsideIb_N S R) h.N_le_M
    (fun b => r⁻¹ * (b * r * b⁻¹)) (fun b hb => h.f_mem hb hr)
    (fun a ha b hb => h.f_eq_iff ha hb hr hr1)
  rw [h.N_card, h.S₁_card] at key
  exact key

private theorem exists_mem_M_not_mem_N [Finite G] (hS : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    ∃ m ∈ burnsideIb_N S (burnsideIb_N S R), m ∉ burnsideIb_N S R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : burnsideIb_N S R ≠ S := fun e => hS (e.symm.le.trans inf_le_right)
  obtain ⟨s, hsS, hsN, hsn⟩ :=
    CFSG.ClassicalInvolution.exists_mem_normalizer_not_mem h.two inf_le_left hne
  exact ⟨s, ⟨hsS, hsN⟩, hsn⟩

open CFSG.ClassicalInvolution in
private theorem inf_conj_eq_bot {m : G} (hm : m ∈ burnsideIb_N S (burnsideIb_N S R))
    (hmn : m ∉ burnsideIb_N S R) : R ⊓ conjSubgroup m R = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨haR, hamR⟩ := Subgroup.mem_inf.mp ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  rw [mem_conjSubgroup_iff] at hamR
  set r : G := m⁻¹ * a * m with hr
  have hrR : r ∈ R := hamR
  have har : a = m * r * m⁻¹ := by rw [hr]; group
  have hr1 : r ≠ 1 := by
    intro e
    apply ha1
    rw [har, e]
    group
  have h1 := h.f_mem hm hrR
  rw [← har] at h1
  have h2 : r⁻¹ * a ∈ R := R.mul_mem (R.inv_mem hrR) haR
  have h3 : r⁻¹ * a ∈ (S₀ ⊓ burnsideIb_N S R) ⊓ R := ⟨h1, h2⟩
  rw [h.S₁_inf_R, Subgroup.mem_bot] at h3
  have h4 : a = r := by
    have := congrArg (r * ·) h3
    simpa using this
  apply hmn
  have h5 : m * r * m⁻¹ = r := by rw [← har]; exact h4
  have h6 : m * r = r * m := by
    calc m * r = (m * r * m⁻¹) * m := by group
      _ = r * m := by rw [h5]
  exact h.mem_N_of_commute hrR hr1 hm.1 h6

open CFSG.ClassicalInvolution in
private theorem sup_conj_eq_N [Finite G] {m : G} (hm : m ∈ burnsideIb_N S (burnsideIb_N S R))
    (hmn : m ∉ burnsideIb_N S R) : R ⊔ conjSubgroup m R = burnsideIb_N S R := by
  have hle : R ⊔ conjSubgroup m R ≤ burnsideIb_N S R := by
    refine sup_le h.R_le_N ?_
    have h1 := conjSubgroup_mono (g := m) (h.R_le_N)
    rwa [conjSubgroup_eq_self_iff.mpr hm.2] at h1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hinj : Function.Injective
      (fun p : R × conjSubgroup m R => (⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
        ↥(R ⊔ conjSubgroup m R))) := by
    intro p p' hpp
    exact mul_injective_of_inf_eq_bot (h.inf_conj_eq_bot hm hmn) (congrArg Subtype.val hpp)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, card_conjSubgroup, ← h.N_card] at hcard
  exact hcard

open CFSG.ClassicalInvolution in
private theorem N_le_W [Finite G] (hS : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    burnsideIb_N S R ≤ ⨆ s ∈ S, conjSubgroup s R := by
  obtain ⟨m, hm, hmn⟩ := h.exists_mem_M_not_mem_N hS
  rw [← h.sup_conj_eq_N hm hmn]
  refine sup_le ?_ ?_
  · have := le_iSup₂ (f := fun s (_ : s ∈ S) => conjSubgroup s R) 1 S.one_mem
    rwa [conjSubgroup_one] at this
  · exact le_iSup₂ (f := fun s (_ : s ∈ S) => conjSubgroup s R) m hm.1

open CFSG.ClassicalInvolution in
private theorem conj_W_le {y : G} (hy : y ∈ S) :
    conjSubgroup y (⨆ s ∈ S, conjSubgroup s R) ≤ ⨆ s ∈ S, conjSubgroup s R := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun s hs => ?_
  rw [← Subgroup.map_le_iff_le_comap, conjSubgroup, ← conjSubgroup]
  have e : conjSubgroup y (conjSubgroup s R) = conjSubgroup (y * s) R := conjSubgroup_conjSubgroup y s R
  rw [e]
  exact le_iSup₂ (f := fun s (_ : s ∈ S) => conjSubgroup s R) (y * s) (S.mul_mem hy hs)

open CFSG.ClassicalInvolution in
private theorem conj_N_comm (y : G) {a b : G} (ha : a ∈ conjSubgroup y (burnsideIb_N S R))
    (hb : b ∈ conjSubgroup y (burnsideIb_N S R)) : a * b = b * a := by
  rw [mem_conjSubgroup_iff] at ha hb
  have := h.N_comm _ ha _ hb
  calc a * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [this]
    _ = b * a := by group

open CFSG.ClassicalInvolution in
private theorem conj_N_exp (y : G) {a : G} (ha : a ∈ conjSubgroup y (burnsideIb_N S R)) : a * a
    = 1 := by
  rw [mem_conjSubgroup_iff] at ha
  have := h.N_exp _ ha
  calc a * a = y * ((y⁻¹ * a * y) * (y⁻¹ * a * y)) * y⁻¹ := by group
    _ = 1 := by rw [this]; group

open CFSG.ClassicalInvolution in
private theorem N'_le_M {x : G} (hxP : x ∈ burnsideIb_P S R) :
    conjSubgroup x (burnsideIb_N S R) ≤ burnsideIb_M S R := by
  have h1 := conjSubgroup_mono (g := x) h.N_le_M
  rwa [conjSubgroup_eq_self_iff.mpr hxP.2] at h1

open CFSG.ClassicalInvolution in
private theorem N'_ne {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R) :
    conjSubgroup x (burnsideIb_N S R) ≠ burnsideIb_N S R := fun e =>
  hxn ⟨hxP.1, conjSubgroup_eq_self_iff.mp e⟩

open CFSG.ClassicalInvolution in
private theorem card_N' (x : G) :
    Nat.card (conjSubgroup x (burnsideIb_N S R)) = Nat.card R * Nat.card R := by
  rw [card_conjSubgroup, h.N_card]

open CFSG.ClassicalInvolution in
private theorem I_inf_R [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M
    S R) :
    burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨hI, haR⟩ := Subgroup.mem_inf.mp ha
  have haN' : a ∈ conjSubgroup x (burnsideIb_N S R) := (Subgroup.mem_inf.mp hI).2
  rw [Subgroup.mem_bot]
  by_contra ha1
  have hle : conjSubgroup x (burnsideIb_N S R) ≤ burnsideIb_N S R := by
    intro b hb
    exact h.mem_N_of_commute haR ha1 (h.N'_le_M hxP hb).1 (h.conj_N_comm x hb haN')
  exact h.N'_ne hxP hxn (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_N' x, h.N_card]))

open CFSG.ClassicalInvolution in
private theorem card_I_le [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R) :
    Nat.card (burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) : Subgroup G) ≤ Nat.card R := by
  have hinj : Function.Injective
      (fun p : (burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) : Subgroup G) × R =>
        (⟨(p.1 : G) * p.2, (burnsideIb_N S R).mul_mem (Subgroup.mem_inf.mp p.1.2).1
          (h.R_le_N p.2.2)⟩ : ↥(burnsideIb_N S R))) := by
    intro p p' hpp
    exact mul_injective_of_inf_eq_bot (h.I_inf_R hxP hxn) (congrArg Subtype.val hpp)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, h.N_card] at hcard
  exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos

open CFSG.ClassicalInvolution in
private theorem card_M_eq [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R) :
    Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R ∧
      Nat.card (burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) : Subgroup G) =
        Nat.card R := by
  obtain ⟨r, hr, hr1⟩ := h.R_ne_one
  have h7 := (h.card_M_le hr hr1).1
  have hi := h.card_I_le hxP hxn
  have hN'M := h.N'_le_M hxP
  have hIM : burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) ≤ burnsideIb_M S R :=
    inf_le_left.trans h.N_le_M
  have hqpos : 0 < Nat.card R := Nat.card_pos
  have hapos : 0 < Nat.card (burnsideIb_M S R) := Nat.card_pos
  have E1 := Subgroup.relIndex_mul_card (burnsideIb_N S R) (burnsideIb_M S R)
  rw [inf_eq_left.mpr h.N_le_M, h.N_card] at E1
  have E2 := Subgroup.relIndex_mul_card (conjSubgroup x (burnsideIb_N S R)) (burnsideIb_M S R)
  rw [inf_eq_left.mpr hN'M, h.card_N' x] at E2
  have E3 := Subgroup.relIndex_mul_card
    (burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R)) (burnsideIb_M S R)
  rw [inf_eq_left.mpr hIM] at E3
  have hineq := Subgroup.relIndex_inf_le (H := burnsideIb_N S R)
    (K := conjSubgroup x (burnsideIb_N S R)) (L := burnsideIb_M S R)
  set q := Nat.card R with hq
  set a := Nat.card (burnsideIb_M S R) with ha
  set i := Nat.card (burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) : Subgroup G) with hi'
  set t := (burnsideIb_N S R).relIndex (burnsideIb_M S R) with ht
  set t' := (conjSubgroup x (burnsideIb_N S R)).relIndex (burnsideIb_M S R) with ht'
  set rI := (burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R)).relIndex
    (burnsideIb_M S R) with hrI
  have htt : t = t' := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hqpos hqpos) (E1.trans E2.symm)
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, zero_mul] at E1
      omega
    · exact h0
  have hqt : q ≤ t := by
    have h1 : a ≤ t * t * q := by
      calc a = rI * i := E3.symm
        _ ≤ (t * t') * i := Nat.mul_le_mul_right _ hineq
        _ = t * t * i := by rw [← htt]
        _ ≤ t * t * q := Nat.mul_le_mul_left _ hi
    have h2 : (t * q) * q ≤ (t * q) * t := by
      calc (t * q) * q = t * (q * q) := by ring
        _ = a := E1
        _ ≤ t * t * q := h1
        _ = (t * q) * t := by ring
    exact Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos htpos hqpos)
  have htq : t ≤ q := by
    have h2 : t * (q * q) ≤ q * (q * q) := by
      calc t * (q * q) = a := E1
        _ ≤ q * q * q := h7
        _ = q * (q * q) := by ring
    exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hqpos hqpos)
  have htq' : t = q := le_antisymm htq hqt
  have ha' : a = q * q * q := by
    rw [← E1, htq']
    ring
  refine ⟨ha', le_antisymm hi ?_⟩
  have h1 : q * q * q ≤ q * q * i := by
    calc q * q * q = a := ha'.symm
      _ = rI * i := E3.symm
      _ ≤ (t * t') * i := Nat.mul_le_mul_right _ hineq
      _ = q * q * i := by rw [← htt, htq']
  exact Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hqpos hqpos)

open CFSG.ClassicalInvolution in
private theorem cent_N [Finite G]
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R)
    {a g : G} (ha : a ∈ burnsideIb_N S R) (haS₁ : a ∉ S₀ ⊓ burnsideIb_N S R) (hg : g ∈ S)
    (hc : g * a = a * g) : g ∈ burnsideIb_N S R := by
  obtain ⟨s, hs, r, hr, hasr⟩ := h.N_eq_mul a ha
  have hr1 : r ≠ 1 := by
    intro e
    apply haS₁
    rw [hasr, e, mul_one]
    exact hs
  have hsr : s * r = r * s := h.N_comm_R hr hs.2
  obtain ⟨m, hm, hms⟩ := (h.card_M_le hr hr1).2 hM s hs
  have hmr : m * r * m⁻¹ = a := by
    have e1 : m * r * m⁻¹ = r * s := by
      have := congrArg (r * ·) hms
      simpa [mul_assoc] using this
    rw [e1, hasr, hsr]
  have hg' : m⁻¹ * g * m ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hm.1) hg) hm.1
  have hcomm : (m⁻¹ * g * m) * r = r * (m⁻¹ * g * m) := by
    calc (m⁻¹ * g * m) * r = m⁻¹ * (g * (m * r * m⁻¹)) * m := by group
      _ = m⁻¹ * (g * a) * m := by rw [hmr]
      _ = m⁻¹ * (a * g) * m := by rw [hc]
      _ = m⁻¹ * ((m * r * m⁻¹) * g) * m := by rw [hmr]
      _ = r * (m⁻¹ * g * m) := by group
  have hN := h.mem_N_of_commute hr hr1 hg' hcomm
  have := h.conj_mem_N hm hN
  have e2 : m * (m⁻¹ * g * m) * m⁻¹ = g := by group
  rwa [e2] at this

open CFSG.ClassicalInvolution in
private theorem I_eq [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) = S₀ ⊓ burnsideIb_N S R := by
  have hle : burnsideIb_N S R ⊓ conjSubgroup x (burnsideIb_N S R) ≤ S₀ ⊓ burnsideIb_N S R := by
    intro a ha
    obtain ⟨haN, haN'⟩ := Subgroup.mem_inf.mp ha
    by_contra haS₁
    have hle' : conjSubgroup x (burnsideIb_N S R) ≤ burnsideIb_N S R := by
      intro b hb
      exact h.cent_N hM haN haS₁ (h.N'_le_M hxP hb).1 (h.conj_N_comm x hb haN')
    exact h.N'_ne hxP hxn (Subgroup.eq_of_le_of_card_ge hle' (by rw [h.card_N' x, h.N_card]))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h.S₁_card, (h.card_M_eq hxP hxn).2]

open CFSG.ClassicalInvolution in
private theorem conj_S₁ [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    conjSubgroup x (S₀ ⊓ burnsideIb_N S R) = S₀ ⊓ burnsideIb_N S R := by
  have hle : S₀ ⊓ burnsideIb_N S R ≤ conjSubgroup x (S₀ ⊓ burnsideIb_N S R) := by
    intro s hs
    rw [mem_conjSubgroup_iff]
    have hs' : s ∈ conjSubgroup x (burnsideIb_N S R) := by
      rw [← h.I_eq hxP hxn hM] at hs
      exact (Subgroup.mem_inf.mp hs).2
    refine ⟨?_, ?_⟩
    · have := h.S₀_norm x⁻¹ (S.inv_mem hxP.1) s hs.1
      simpa using this
    · exact mem_conjSubgroup_iff.mp hs'
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm

open CFSG.ClassicalInvolution in
private theorem cent_N' [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R)
    {a g : G} (ha : a ∈ conjSubgroup x (burnsideIb_N S R)) (haS₁ : a ∉ S₀ ⊓ burnsideIb_N S R)
    (hg : g ∈ S) (hc : g * a = a * g) : g ∈ conjSubgroup x (burnsideIb_N S R) := by
  have ha₀ : x⁻¹ * a * x ∈ burnsideIb_N S R := mem_conjSubgroup_iff.mp ha
  have ha₀S : x⁻¹ * a * x ∉ S₀ ⊓ burnsideIb_N S R := by
    intro hmem
    apply haS₁
    have : a ∈ conjSubgroup x (S₀ ⊓ burnsideIb_N S R) := mem_conjSubgroup_iff.mpr hmem
    rwa [h.conj_S₁ hxP hxn hM] at this
  have hcomm : (x⁻¹ * g * x) * (x⁻¹ * a * x) = (x⁻¹ * a * x) * (x⁻¹ * g * x) := by
    calc (x⁻¹ * g * x) * (x⁻¹ * a * x) = x⁻¹ * (g * a) * x := by group
      _ = x⁻¹ * (a * g) * x := by rw [hc]
      _ = (x⁻¹ * a * x) * (x⁻¹ * g * x) := by group
  have hg' := h.cent_N hM ha₀ ha₀S (S.mul_mem (S.mul_mem (S.inv_mem hxP.1) hg) hxP.1) hcomm
  exact mem_conjSubgroup_iff.mpr hg'

open CFSG.ClassicalInvolution in
private theorem f_surj_N' [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R)
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    ∀ s ∈ S₀ ⊓ burnsideIb_N S R, ∃ n' ∈ conjSubgroup x (burnsideIb_N S R),
      r⁻¹ * (n' * r * n'⁻¹) = s := by
  have hN'M := h.N'_le_M hxP
  have hI := h.I_eq hxP hxn hM
  have hAB : S₀ ⊓ burnsideIb_N S R ≤ conjSubgroup x (burnsideIb_N S R) := by
    rw [← hI]
    exact inf_le_right
  have key := burnsideIb_card_le_mul (A := S₀ ⊓ burnsideIb_N S R)
    (B := conjSubgroup x (burnsideIb_N S R)) (S₁ := S₀ ⊓ burnsideIb_N S R) hAB
    (fun b => r⁻¹ * (b * r * b⁻¹)) (fun b hb => h.f_mem (hN'M hb) hr) (by
      intro a ha b hb
      rw [h.f_eq_iff (hN'M ha) (hN'M hb) hr hr1]
      have hab : a⁻¹ * b ∈ conjSubgroup x (burnsideIb_N S R) :=
        (conjSubgroup x (burnsideIb_N S R)).mul_mem
          ((conjSubgroup x (burnsideIb_N S R)).inv_mem ha) hb
      constructor
      · intro hN
        rw [← hI]
        exact ⟨hN, hab⟩
      · intro hS₁
        exact hS₁.2)
  rw [h.card_N' x, h.S₁_card] at key
  exact key.2 rfl

open CFSG.ClassicalInvolution in
private theorem M_eq_mul [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    ∀ m ∈ burnsideIb_M S R, ∃ a ∈ burnsideIb_N S R,
      ∃ n' ∈ conjSubgroup x (burnsideIb_N S R), m = a * n' := by
  intro m hm
  obtain ⟨r, hr, hr1⟩ := h.R_ne_one
  have hN'M := h.N'_le_M hxP
  obtain ⟨n', hn', hfn'⟩ := h.f_surj_N' hxP hxn hM hr hr1 _ (h.f_mem hm hr)
  have hν : n'⁻¹ * m ∈ burnsideIb_N S R :=
    (h.f_eq_iff (hN'M hn') hm hr hr1).mp hfn'
  have hn'M : n' ∈ burnsideIb_M S R := hN'M hn'
  refine ⟨n' * (n'⁻¹ * m) * n'⁻¹, h.conj_mem_N hn'M hν, n', hn', ?_⟩
  group

open CFSG.ClassicalInvolution in
private theorem S₁_central [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R)
    {s m : G} (hs : s ∈ S₀ ⊓ burnsideIb_N S R) (hm : m ∈ burnsideIb_M S R) : s * m = m * s := by
  obtain ⟨a, ha, n', hn', rfl⟩ := h.M_eq_mul hxP hxn hM m hm
  have hsN' : s ∈ conjSubgroup x (burnsideIb_N S R) := by
    rw [← h.I_eq hxP hxn hM] at hs
    exact (Subgroup.mem_inf.mp hs).2
  rw [← mul_assoc, h.N_comm s hs.2 a ha, mul_assoc, h.conj_N_comm x hsN' hn', mul_assoc]

open CFSG.ClassicalInvolution in
private theorem conj_mem_N' {x : G} (hxP : x ∈ burnsideIb_P S R) {m b : G}
    (hm : m ∈ burnsideIb_M S R) (hb : b ∈ conjSubgroup x (burnsideIb_N S R)) :
    m * b * m⁻¹ ∈ conjSubgroup x (burnsideIb_N S R) := by
  rw [mem_conjSubgroup_iff] at hb ⊢
  have hxinv : x⁻¹ ∈ Subgroup.normalizer ((burnsideIb_M S R : Subgroup G) : Set G) :=
    (Subgroup.normalizer _).inv_mem hxP.2
  have hxm : x⁻¹ * m * x ∈ burnsideIb_M S R := by
    have := (Subgroup.mem_normalizer_iff.mp hxinv m).mp hm
    simpa using this
  have := h.conj_mem_N hxm hb
  have e : x⁻¹ * (m * b * m⁻¹) * x = (x⁻¹ * m * x) * (x⁻¹ * b * x) * (x⁻¹ * m * x)⁻¹ := by group
  rw [e]
  exact this

open CFSG.ClassicalInvolution in
private theorem comm_mem [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    ∀ m₁ ∈ burnsideIb_M S R, ∀ m₂ ∈ burnsideIb_M S R,
      m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ S₀ ⊓ burnsideIb_N S R := by
  intro m₁ hm₁ m₂ hm₂
  have hN'M := h.N'_le_M hxP
  have h1 : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ burnsideIb_N S R :=
    burnsideIb_commutator_mem (A := conjSubgroup x (burnsideIb_N S R)) hN'M
      (fun m hm b hb => h.conj_mem_N hm hb)
      (fun a ha a' ha' => h.conj_N_comm x ha ha')
      (fun m hm => by
        obtain ⟨a, ha, n', hn', rfl⟩ := h.M_eq_mul hxP hxn hM m hm
        exact ⟨a, ha, n', hn', rfl⟩) m₁ hm₁ m₂ hm₂
  have h2 : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ conjSubgroup x (burnsideIb_N S R) :=
    burnsideIb_commutator_mem (A := burnsideIb_N S R) h.N_le_M
      (fun m hm b hb => h.conj_mem_N' hxP hm hb)
      (fun a ha a' ha' => h.N_comm a ha a' ha')
      (fun m hm => by
        obtain ⟨a, ha, n', hn', rfl⟩ := h.M_eq_mul hxP hxn hM m hm
        refine ⟨n', hn', n'⁻¹ * a * n', ?_, by group⟩
        have := h.conj_mem_N ((burnsideIb_M S R).inv_mem (hN'M hn')) ha
        simpa using this) m₁ hm₁ m₂ hm₂
  rw [← h.I_eq hxP hxn hM]
  exact ⟨h1, h2⟩

open CFSG.ClassicalInvolution in
private theorem mul_self_eq {x a n' : G} (ha : a ∈ burnsideIb_N S R)
    (hn' : n' ∈ conjSubgroup x (burnsideIb_N S R))
    (hcN : n' * a * n'⁻¹ * a⁻¹ ∈ burnsideIb_N S R) :
    a * n' * (a * n') = n' * a * n'⁻¹ * a⁻¹ := by
  have e1 : n' * n' = 1 := h.conj_N_exp x hn'
  have e2 : a * a = 1 := h.N_exp a ha
  set c := n' * a * n'⁻¹ * a⁻¹ with hc
  have e3 : a * c = c * a := h.N_comm a ha c hcN
  have e4 : n' * a * n'⁻¹ = c * a := by rw [hc]; group
  calc a * n' * (a * n') = a * (n' * a * n'⁻¹) * (n' * n') := by group
    _ = a * (c * a) * 1 := by rw [e4, e1]
    _ = (a * c) * a := by group
    _ = (c * a) * a := by rw [e3]
    _ = c * (a * a) := by group
    _ = c := by rw [e2, mul_one]

open CFSG.ClassicalInvolution in
private theorem sq_mem [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    ∀ m ∈ burnsideIb_M S R, m * m ∈ S₀ ⊓ burnsideIb_N S R := by
  intro m hm
  obtain ⟨a, ha, n', hn', rfl⟩ := h.M_eq_mul hxP hxn hM m hm
  have hcS₁ : n' * a * n'⁻¹ * a⁻¹ ∈ S₀ ⊓ burnsideIb_N S R :=
    h.comm_mem hxP hxn hM n' (h.N'_le_M hxP hn') a (h.N_le_M ha)
  rw [h.mul_self_eq ha hn' hcS₁.2]
  exact hcS₁

open CFSG.ClassicalInvolution in
private theorem invol_mem [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    ∀ m ∈ burnsideIb_M S R, m * m = 1 →
      m ∈ burnsideIb_N S R ∨ m ∈ conjSubgroup x (burnsideIb_N S R) := by
  intro m hm hmm
  obtain ⟨a, ha, n', hn', rfl⟩ := h.M_eq_mul hxP hxn hM m hm
  have hI := h.I_eq hxP hxn hM
  have hn'M := h.N'_le_M hxP hn'
  by_cases haS : a ∈ S₀ ⊓ burnsideIb_N S R
  · right
    have : a ∈ conjSubgroup x (burnsideIb_N S R) := by
      rw [← hI] at haS
      exact (Subgroup.mem_inf.mp haS).2
    exact (conjSubgroup x (burnsideIb_N S R)).mul_mem this hn'
  by_cases hnS : n' ∈ S₀ ⊓ burnsideIb_N S R
  · left
    exact (burnsideIb_N S R).mul_mem ha hnS.2
  exfalso
  have hcS₁ : n' * a * n'⁻¹ * a⁻¹ ∈ S₀ ⊓ burnsideIb_N S R :=
    h.comm_mem hxP hxn hM n' hn'M a (h.N_le_M ha)
  have h1 : n' * a * n'⁻¹ * a⁻¹ = 1 := by
    rw [← h.mul_self_eq ha hn' hcS₁.2]
    exact hmm
  have h2 : n' * a = a * n' := by
    have := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp this
  have hn'N : n' ∈ burnsideIb_N S R := h.cent_N hM ha haS hn'M.1 h2
  apply hnS
  rw [← hI]
  exact ⟨hn'N, hn'⟩

open CFSG.ClassicalInvolution in
private theorem central_mem [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) {z : G}
    (hz : z ∈ burnsideIb_M S R) (hc : ∀ m ∈ burnsideIb_M S R, z * m = m * z) :
    z ∈ S₀ ⊓ burnsideIb_N S R := by
  obtain ⟨r, hr, hr1⟩ := h.R_ne_one
  have hzN : z ∈ burnsideIb_N S R :=
    h.mem_N_of_commute hr hr1 hz.1 (hc r (h.N_le_M (h.R_le_N hr)))
  have hr' : x * r * x⁻¹ ∈ conjSubgroup x (burnsideIb_N S R) :=
    mem_conjSubgroup_of_mem (h.R_le_N hr)
  have hcomm : z * (x * r * x⁻¹) = (x * r * x⁻¹) * z := hc _ (h.N'_le_M hxP hr')
  have hzN' : x⁻¹ * z * x ∈ burnsideIb_N S R := by
    refine h.mem_N_of_commute hr hr1 (S.mul_mem (S.mul_mem (S.inv_mem hxP.1) hz.1) hxP.1) ?_
    calc (x⁻¹ * z * x) * r = x⁻¹ * (z * (x * r * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * r * x⁻¹) * z) * x := by rw [hcomm]
      _ = r * (x⁻¹ * z * x) := by group
  rw [← h.I_eq hxP hxn hM]
  exact ⟨hzN, mem_conjSubgroup_iff.mpr hzN'⟩

open CFSG.ClassicalInvolution in
private theorem P_cases [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    ∀ y ∈ burnsideIb_P S R, y ∈ burnsideIb_M S R ∨ x⁻¹ * y ∈ burnsideIb_M S R := by
  intro y hy
  have hEM : conjSubgroup y (burnsideIb_N S R) ≤ burnsideIb_M S R := by
    have h1 := conjSubgroup_mono (g := y) h.N_le_M
    rwa [conjSubgroup_eq_self_iff.mpr hy.2] at h1
  have hinv : ∀ e ∈ conjSubgroup y (burnsideIb_N S R),
      e ∈ burnsideIb_N S R ∨ e ∈ conjSubgroup x (burnsideIb_N S R) := fun e he =>
    h.invol_mem hxP hxn hM e (hEM he) (h.conj_N_exp y he)
  rcases burnsideIb_le_or_le hinv with hEN | hEN'
  · left
    have hE : conjSubgroup y (burnsideIb_N S R) = burnsideIb_N S R :=
      Subgroup.eq_of_le_of_card_ge hEN (by rw [card_conjSubgroup])
    exact ⟨hy.1, conjSubgroup_eq_self_iff.mp hE⟩
  · right
    have hE : conjSubgroup y (burnsideIb_N S R) = conjSubgroup x (burnsideIb_N S R) :=
      Subgroup.eq_of_le_of_card_ge hEN' (by rw [card_conjSubgroup, card_conjSubgroup])
    have : conjSubgroup (x⁻¹ * y) (burnsideIb_N S R) = burnsideIb_N S R := by
      rw [← conjSubgroup_conjSubgroup, hE, conjSubgroup_inv_conjSubgroup]
    exact ⟨S.mul_mem (S.inv_mem hxP.1) hy.1, conjSubgroup_eq_self_iff.mp this⟩

open CFSG.ClassicalInvolution in
private theorem S_le_normalizer_M [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R)
    (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    S ≤ Subgroup.normalizer (burnsideIb_M S R : Set G) := by
  by_contra hS
  have hPne : burnsideIb_P S R ≠ S := fun e => hS (e.symm.le.trans inf_le_right)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzS, hzP, hzn⟩ := exists_mem_normalizer_not_mem h.two
    (inf_le_left : burnsideIb_P S R ≤ S) hPne
  have hMP : burnsideIb_M S R ≤ burnsideIb_P S R := le_inf inf_le_left Subgroup.le_normalizer
  have hEP : conjSubgroup z (burnsideIb_N S R) ≤ burnsideIb_P S R := by
    have h1 := conjSubgroup_mono (g := z) (h.N_le_M.trans hMP)
    rwa [conjSubgroup_eq_self_iff.mpr hzP] at h1
  have hES : conjSubgroup z (burnsideIb_N S R) ≤ S := hEP.trans inf_le_left
  have hN'M := h.N'_le_M hxP
  have hq4 := h.four_le
  have hcardE : Nat.card (conjSubgroup z (burnsideIb_N S R)) ≤
      2 * Nat.card (conjSubgroup z (burnsideIb_N S R) ⊓ burnsideIb_M S R : Subgroup G) := by
    by_cases hEM : conjSubgroup z (burnsideIb_N S R) ≤ burnsideIb_M S R
    · rw [inf_eq_left.mpr hEM]
      omega
    · obtain ⟨w, hwE, hwM⟩ := SetLike.not_le_iff_exists.mp hEM
      have hxw : x⁻¹ * w ∈ burnsideIb_M S R :=
        ((h.P_cases hxP hxn hM w (hEP hwE)).resolve_left hwM)
      refine burnsideIb_card_le_two_mul inf_le_left w (fun y hy => ?_) hwE
      rcases h.P_cases hxP hxn hM y (hEP hy) with hyM | hyM
      · exact Or.inl ⟨hy, hyM⟩
      · refine Or.inr ⟨(conjSubgroup z (burnsideIb_N S R)).mul_mem
          ((conjSubgroup z (burnsideIb_N S R)).inv_mem hwE) hy, ?_⟩
        have := (burnsideIb_M S R).mul_mem ((burnsideIb_M S R).inv_mem hxw) hyM
        simpa [mul_assoc] using this
  rw [h.card_N' z] at hcardE
  set E := conjSubgroup z (burnsideIb_N S R) with hE
  have hJq : Nat.card R < Nat.card (E ⊓ burnsideIb_M S R : Subgroup G) := by
    by_contra hcon
    push Not at hcon
    have : Nat.card R * Nat.card R ≤ 2 * Nat.card R := hcardE.trans (Nat.mul_le_mul_left _ hcon)
    have := Nat.le_of_mul_le_mul_right this Nat.card_pos
    omega
  have hinv : ∀ e ∈ E ⊓ burnsideIb_M S R,
      e ∈ burnsideIb_N S R ∨ e ∈ conjSubgroup x (burnsideIb_N S R) := fun e he =>
    h.invol_mem hxP hxn hM e he.2 (h.conj_N_exp z he.1)
  have hE_card : Nat.card (burnsideIb_N S R) ≤ Nat.card E := by rw [h.card_N' z, h.N_card]
  have hEN'_card : Nat.card (conjSubgroup x (burnsideIb_N S R)) ≤ Nat.card E := by
    rw [h.card_N' z, h.card_N' x]
  rcases burnsideIb_le_or_le hinv with hJN | hJN'
  ·
    have hnot : ¬ (E ⊓ burnsideIb_M S R) ≤ S₀ ⊓ burnsideIb_N S R := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [h.S₁_card] at this
      omega
    obtain ⟨a, haJ, haS₁⟩ := SetLike.not_le_iff_exists.mp hnot
    have hEN : E ≤ burnsideIb_N S R := fun g hg =>
      h.cent_N hM (hJN haJ) haS₁ (hES hg) (h.conj_N_comm z hg haJ.1)
    have hEeq : E = burnsideIb_N S R := Subgroup.eq_of_le_of_card_ge hEN hE_card
    exact hzn (hMP ⟨hzS, conjSubgroup_eq_self_iff.mp hEeq⟩)
  ·
    have hnot : ¬ (E ⊓ burnsideIb_M S R) ≤ S₀ ⊓ burnsideIb_N S R := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [h.S₁_card] at this
      omega
    obtain ⟨a, haJ, haS₁⟩ := SetLike.not_le_iff_exists.mp hnot
    have hEN : E ≤ conjSubgroup x (burnsideIb_N S R) := fun g hg =>
      h.cent_N' hxP hxn hM (hJN' haJ) haS₁ (hES hg) (h.conj_N_comm z hg haJ.1)
    have hEeq : E = conjSubgroup x (burnsideIb_N S R) :=
      Subgroup.eq_of_le_of_card_ge hEN hEN'_card
    have hxz : conjSubgroup (x⁻¹ * z) (burnsideIb_N S R) = burnsideIb_N S R := by
      rw [← conjSubgroup_conjSubgroup, ← hE, hEeq, conjSubgroup_inv_conjSubgroup]
    have hxzM : x⁻¹ * z ∈ burnsideIb_M S R :=
      ⟨S.mul_mem (S.inv_mem hxP.1) hzS, conjSubgroup_eq_self_iff.mp hxz⟩
    have : x * (x⁻¹ * z) ∈ burnsideIb_P S R :=
      (burnsideIb_P S R).mul_mem hxP (hMP hxzM)
    exact hzn (by simpa using this)

open CFSG.ClassicalInvolution in
private theorem relIndex_M [Finite G] {x : G} (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉
    burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    (burnsideIb_M S R).relIndex S = 2 := by
  have hS := h.S_le_normalizer_M hxP hxn hM
  have hx2 : x * x ∈ burnsideIb_M S R := by
    rcases h.P_cases hxP hxn hM (x * x)
      ⟨S.mul_mem hxP.1 hxP.1, hS (S.mul_mem hxP.1 hxP.1)⟩ with h1 | h1
    · exact h1
    · exfalso
      apply hxn
      simpa using h1
  have hxinv : x⁻¹ ∈ Subgroup.normalizer ((burnsideIb_M S R : Subgroup G) : Set G) :=
    (Subgroup.normalizer _).inv_mem hxP.2
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hxP.1⟩, fun b => ?_⟩
  by_cases hb : (b : G) ∈ burnsideIb_M S R
  · right
    refine ⟨hb, fun hba => hxn ?_⟩
    have hba' : (b : G) * x ∈ burnsideIb_M S R := hba
    have := (burnsideIb_M S R).mul_mem ((burnsideIb_M S R).inv_mem hb) hba'
    simpa using this
  · left
    refine ⟨?_, hb⟩
    have hm₁ : x⁻¹ * (b : G) ∈ burnsideIb_M S R :=
      (h.P_cases hxP hxn hM b ⟨b.2, hS b.2⟩).resolve_left hb
    have hm₂ : x⁻¹ * (x⁻¹ * (b : G)) * x ∈ burnsideIb_M S R := by
      have := (Subgroup.mem_normalizer_iff.mp hxinv _).mp hm₁
      simpa using this
    have e : (b : G) * x = (x * x) * (x⁻¹ * (x⁻¹ * (b : G)) * x) := by group
    show (b : G) * x ∈ burnsideIb_M S R
    rw [e]
    exact (burnsideIb_M S R).mul_mem hx2 hm₂

open CFSG.ClassicalInvolution in
private theorem W_eq_M [Finite G] (hS : ¬ S ≤ Subgroup.normalizer (R : Set G)) {x : G}
    (hxP : x ∈ burnsideIb_P S R) (hxn : x ∉ burnsideIb_M S R)
    (hM : Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R) :
    (⨆ s ∈ S, conjSubgroup s R) = burnsideIb_M S R := by
  have hSN := h.S_le_normalizer_M hxP hxn hM
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    have h1 := conjSubgroup_mono (g := s) (h.R_le_N.trans h.N_le_M)
    rwa [conjSubgroup_eq_self_iff.mpr (hSN hs)] at h1
  · intro m hm
    obtain ⟨a, ha, n', hn', rfl⟩ := h.M_eq_mul hxP hxn hM m hm
    have hNW := h.N_le_W hS
    refine (⨆ s ∈ S, conjSubgroup s R).mul_mem (hNW ha) ?_
    have : conjSubgroup x (burnsideIb_N S R) ≤ conjSubgroup x (⨆ s ∈ S, conjSubgroup s R) :=
      conjSubgroup_mono hNW
    exact h.conj_W_le hxP.1 (this hn')

open CFSG.ClassicalInvolution in
private theorem case_II [Finite G] (hS : ¬ S ≤ Subgroup.normalizer (R : Set G))
    (hN : ¬ S ≤ Subgroup.normalizer (burnsideIb_N S R : Set G)) :
    S ≤ Subgroup.normalizer (burnsideIb_M S R : Set G) ∧
    (⨆ s ∈ S, conjSubgroup s R) = burnsideIb_M S R ∧
    Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R ∧
    ChIJK.centerOf (burnsideIb_M S R) = S₀ ⊓ burnsideIb_N S R ∧
    ⁅burnsideIb_M S R, burnsideIb_M S R⁆ = S₀ ⊓ burnsideIb_N S R ∧
    ChIJK.frattiniOf (burnsideIb_M S R) = S₀ ⊓ burnsideIb_N S R ∧
    (burnsideIb_M S R).relIndex S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMS : burnsideIb_M S R ≠ S := fun e => hN (e.symm.le.trans inf_le_right)
  obtain ⟨x, hxS, hxM, hxn⟩ := exists_mem_normalizer_not_mem h.two
    (inf_le_left : burnsideIb_M S R ≤ S) hMS
  have hxP : x ∈ burnsideIb_P S R := ⟨hxS, hxM⟩
  have hM := (h.card_M_eq hxP hxn).1
  obtain ⟨r, hr, hr1⟩ := h.R_ne_one
  have hTM : S₀ ⊓ burnsideIb_N S R ≤ burnsideIb_M S R := inf_le_right.trans h.N_le_M
  have hcomm := h.comm_mem hxP hxn hM
  have hsurj : ∀ s ∈ S₀ ⊓ burnsideIb_N S R, ∃ m₁ ∈ burnsideIb_M S R, ∃ m₂ ∈ burnsideIb_M S R,
      m₁ * m₂ * m₁⁻¹ * m₂⁻¹ = s := by
    intro s hs
    obtain ⟨n', hn', hfn'⟩ := h.f_surj_N' hxP hxn hM hr hr1 s hs
    refine ⟨r⁻¹, (burnsideIb_M S R).inv_mem (h.N_le_M (h.R_le_N hr)), n', h.N'_le_M hxP hn', ?_⟩
    rw [← hfn']
    group
  refine ⟨h.S_le_normalizer_M hxP hxn hM, h.W_eq_M hS hxP hxn hM, hM, ?_, ?_, ?_,
    h.relIndex_M hxP hxn hM⟩
  · exact burnsideIb_centerOf_eq hTM (fun z hz m hm => h.S₁_central hxP hxn hM hz hm)
      (fun z hz hc => h.central_mem hxP hxn hM hz hc)
  · exact burnsideIb_commutator_eq hcomm hsurj
  · exact burnsideIb_frattiniOf_eq (h.two.to_le inf_le_left) hTM hcomm (h.sq_mem hxP hxn hM) hsurj

open CFSG.ClassicalInvolution in
private theorem case_I [Finite G] (hS : ¬ S ≤ Subgroup.normalizer (R : Set G))
    (hN : S ≤ Subgroup.normalizer (burnsideIb_N S R : Set G)) :
    (⨆ s ∈ S, conjSubgroup s R) = burnsideIb_N S R := by
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    have h1 := conjSubgroup_mono (g := s) h.R_le_N
    rwa [conjSubgroup_eq_self_iff.mpr (hN hs)] at h1
  · exact h.N_le_W hS

open CFSG.ClassicalInvolution in
private theorem main [Finite G] (hS : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    (∀ s ∈ S, ∀ u ∈ S₀ ⊓ burnsideIb_N S R, s * u * s⁻¹ ∈ S₀ ⊓ burnsideIb_N S R) ∧
    ((S ≤ Subgroup.normalizer (burnsideIb_N S R : Set G) ∧
        (⨆ s ∈ S, conjSubgroup s R) = burnsideIb_N S R) ∨
      (S ≤ Subgroup.normalizer (burnsideIb_M S R : Set G) ∧
        (⨆ s ∈ S, conjSubgroup s R) = burnsideIb_M S R ∧
        Nat.card (burnsideIb_M S R) = Nat.card R * Nat.card R * Nat.card R ∧
        ChIJK.centerOf (burnsideIb_M S R) = S₀ ⊓ burnsideIb_N S R ∧
        ⁅burnsideIb_M S R, burnsideIb_M S R⁆ = S₀ ⊓ burnsideIb_N S R ∧
        ChIJK.frattiniOf (burnsideIb_M S R) = S₀ ⊓ burnsideIb_N S R ∧
        (burnsideIb_M S R).relIndex S = 2)) := by
  by_cases hN : S ≤ Subgroup.normalizer (burnsideIb_N S R : Set G)
  · refine ⟨fun s hs u hu => ⟨h.S₀_norm s hs u hu.1, ?_⟩, Or.inl ⟨hN, h.case_I hS hN⟩⟩
    exact (Subgroup.mem_normalizer_iff.mp (hN hs) u).mp hu.2
  · have hII := h.case_II hS hN
    refine ⟨?_, Or.inr hII⟩
    obtain ⟨x, hxS, hxM, hxn⟩ : ∃ x ∈ S, x ∈ Subgroup.normalizer (burnsideIb_M S R : Set G) ∧
        x ∉ burnsideIb_M S R := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hMS : burnsideIb_M S R ≠ S := fun e => hN (e.symm.le.trans inf_le_right)
      exact exists_mem_normalizer_not_mem h.two (inf_le_left : burnsideIb_M S R ≤ S) hMS
    have hxP : x ∈ burnsideIb_P S R := ⟨hxS, hxM⟩
    have hM := hII.2.2.1
    intro s hs u hu
    have hsM : s ∈ Subgroup.normalizer (burnsideIb_M S R : Set G) := hII.1 hs
    have hu' : u ∈ burnsideIb_M S R := inf_le_right.trans h.N_le_M hu
    refine h.central_mem hxP hxn hM ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.mp hsM u).mp hu'
    · intro m hm
      have hsinv : s⁻¹ ∈ Subgroup.normalizer (burnsideIb_M S R : Set G) :=
        (Subgroup.normalizer _).inv_mem hsM
      have hm' : s⁻¹ * m * s ∈ burnsideIb_M S R := by
        have := (Subgroup.mem_normalizer_iff.mp hsinv m).mp hm
        simpa using this
      have hc := h.S₁_central hxP hxn hM hu hm'
      calc s * u * s⁻¹ * m = s * (u * (s⁻¹ * m * s)) * s⁻¹ := by group
        _ = s * ((s⁻¹ * m * s) * u) * s⁻¹ := by rw [hc]
        _ = m * (s * u * s⁻¹) := by group

end burnsideIb_EAData

open CFSG.ClassicalInvolution in
private theorem burnsideIb_conjClosure_eq {G : Type} [Group G] (R S : Subgroup G) :
    ChIJK.conjClosure R S = ⨆ s ∈ S, conjSubgroup s R := by
  unfold ChIJK.conjClosure
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    exact le_iSup₂ (f := fun s (_ : s ∈ S) => conjSubgroup s R) y⁻¹ (S.inv_mem hy)
  · refine iSup₂_le fun s hs => ?_
    have e : conjSubgroup s R = CFSG.conjugate R s⁻¹ := by
      unfold CFSG.conjugate
      rw [inv_inv]
    rw [e]
    exact le_iSup₂ (f := fun y (_ : y ∈ S) => CFSG.conjugate R y) s⁻¹ (S.inv_mem hs)

open CFSG.ClassicalInvolution in
private theorem burnsideIb_S₁_exp {G : Type} [Group G] [Finite G] {K : Subgroup G} {g : G}
    {R S : Subgroup G} (d : PairData K g R S) (hR1 : R ≠ ⊥) (hexp : ∀ r ∈ R, r * r = 1) :
    ∀ s ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G), s * s = 1 := by
  obtain ⟨e⟩ := d.nonempty_mulEquiv_S₁ hR1
  intro s hs
  have h1 : ((e ⟨s, hs⟩ : R) : G) * (e ⟨s, hs⟩ : R) = 1 := hexp _ (e ⟨s, hs⟩).2
  have h2 : e (⟨s, hs⟩ * ⟨s, hs⟩) = 1 := by
    rw [map_mul]
    exact Subtype.ext h1
  have h3 : (⟨s, hs⟩ * ⟨s, hs⟩ : ↥(S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G))) = 1 := by
    apply e.injective
    rw [h2, map_one]
  exact congrArg Subtype.val h3

open CFSG.ClassicalInvolution in
private theorem burnsideIb_eaData_of_pairData {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {g : G}
    {R S : Subgroup G} (d : PairData K g R S) (hR1 : R ≠ ⊥) (hexp : ∀ r ∈ R, r * r = 1)
    (hR2 : Nat.card R ≠ 2) : burnsideIb_EAData S (S ⊓ conjSubgroup g K) R := by
  have hS₁exp := burnsideIb_S₁_exp d hR1 hexp
  have hNexp : ∀ a ∈ S ⊓ Subgroup.normalizer (R : Set G), a * a = 1 := by
    intro a ha
    obtain ⟨s, hs, r, hr, rfl⟩ := exists_mul_of_mem_normalizer d.R_le_normalizer d.le d.S_le ha.1 ha.2
    have hc : s * r = r * s := d.S₁_commute s hs r hr
    calc s * r * (s * r) = s * (r * s) * r := by group
      _ = s * (s * r) * r := by rw [← hc]
      _ = (s * s) * (r * r) := by group
      _ = 1 := by rw [hS₁exp s hs, hexp r hr, one_mul]
  have hR2' : 4 ≤ Nat.card R := by
    obtain ⟨n, hn⟩ := d.R_two.exists_card_eq
    rcases n with _ | _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hR1
    · exact absurd (by simpa using hn) hR2
    · rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS₁eq : (S ⊓ conjSubgroup g K) ⊓ burnsideIb_N S R =
      S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  refine ⟨d.S_two, inf_le_left, ?_, d.le, ?_, ?_, ?_, hexp, hR2', ?_, hNexp, ?_, ?_, ?_⟩
  · intro s hs x hx
    refine ⟨S.mul_mem (S.mul_mem hs hx.1) (S.inv_mem hs), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (d.le_normalizer_sup (d.S_le hs)) x).mp hx.2
  · exact le_bot_iff.mp ((inf_le_inf inf_le_right le_rfl).trans d.inf_eq_bot.le)
  · intro s hs
    exact exists_mul_of_mem d.R_le_normalizer d.le d.S_le hs
  · intro r hr r' hr'
    exact commute_of_mul_self_eq_one (hexp r hr) (hexp r' hr') (hexp _ (R.mul_mem hr hr'))
  · intro a ha b hb
    exact commute_of_mul_self_eq_one (hNexp a ha) (hNexp b hb) (hNexp _ ((S ⊓ Subgroup.normalizer (R : Set G)).mul_mem ha hb))
  · rw [natCard_normalizer_eq d.R_le_normalizer d.inf_eq_bot d.le d.S_le, d.card_S₁ hR1]
  · rw [hS₁eq]
    exact d.card_S₁ hR1
  · intro r hr hr1 g' hg' hc
    refine (d.tightData hR1).normalizer_inf_le (X := Subgroup.zpowers r)
      (Subgroup.zpowers_le.mpr hr) (Subgroup.zpowers_eq_bot.not.mpr hr1) hg' ?_
    refine mem_normalizer_of_commute fun v hv => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute g' r from hc) k).eq

private theorem burnsideIb_S₁_eq {G : Type} [Group G] (S K' R : Subgroup G) :
    (S ⊓ K') ⊓ burnsideIb_N S R = S ⊓ K' ⊓ Subgroup.normalizer (R : Set G) := by
  ext x
  simp only [Subgroup.mem_inf]
  tauto

open CFSG.ClassicalInvolution in
private theorem burnsideIb_five_a {G : Type} [Group G] [Finite G] {K : Subgroup G} {g : G}
    {R S : Subgroup G} (d : PairData K g R S) (hR1 : R ≠ ⊥) (hR2 : Nat.card R = 2)
    (hS : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    Nat.card ↥R = 2 ∧ ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* SemidihedralGroup n))) := by
  refine ⟨hR2, ?_⟩
  rcases d.isDihedral_or_semidihedral_of_card_two hR1 hR2 with h4 | ⟨m', -, hD | ⟨hm', hSD⟩⟩
  · exfalso
    apply hS
    obtain ⟨-, hN4, -⟩ := d.card_two_structure hR1 hR2
    have : S ⊓ Subgroup.normalizer (R : Set G) = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hN4, h4])
    exact this.symm.le.trans inf_le_right
  · exact Or.inl ⟨m' + 2, by omega, hD⟩
  · exact Or.inr ⟨m' + 3, by omega, hSD⟩

open CFSG.ClassicalInvolution in
private theorem burnsideIb_five_b {G : Type} [Group G] [Finite G] {K : Subgroup G} {g : G}
    {R S : Subgroup G} (d : PairData K g R S) (hR1 : R ≠ ⊥)
    (hW : ChIJK.conjClosure R S = S ⊓ Subgroup.normalizer (R : Set G)) :
    ChIJK.conjClosure R S = R ⊔ (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)) ∧
      ChIJK.IsDirectProductOf R (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G))
        (ChIJK.conjClosure R S) ∧
      Nonempty (↥(ChIJK.conjClosure R S) ≃* (↥R × ↥R)) := by
  have hsup : ChIJK.conjClosure R S =
      R ⊔ (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)) := by
    rw [hW, d.normalizer_eq_sup, sup_comm]
  refine ⟨hsup, ?_, ?_⟩
  · unfold ChIJK.IsDirectProductOf
    refine ⟨fun a ha b hb => (d.S₁_commute b hb a ha).symm, ?_, hsup.symm⟩
    rw [inf_comm]
    exact d.S₁_inf_R
  · rw [hW]
    obtain ⟨e₁⟩ := nonempty_mulEquiv_prod (M := S ⊓ Subgroup.normalizer (R : Set G))
      (A := S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)) (B := R)
      (fun y hy => ⟨hy.1.1, hy.2⟩) (fun y hy => ⟨d.le hy, Subgroup.le_normalizer hy⟩)
      d.S₁_inf_R d.S₁_commute fun m hm =>
        exists_mul_of_mem_normalizer d.R_le_normalizer d.le d.S_le hm.1 hm.2
    obtain ⟨e₂⟩ := d.nonempty_mulEquiv_S₁ hR1
    exact ⟨e₁.trans (MulEquiv.prodCongr e₂ (MulEquiv.refl R))⟩

open CFSG.ClassicalInvolution in
private theorem burnsideIb_normal_S₁ {G : Type} [Group G] [Finite G] {K : Subgroup G} {g : G}
    {R S : Subgroup G} (d : PairData K g R S) (hR1 : R ≠ ⊥) :
    S ⊓ conjSubgroup g K ≤ Subgroup.normalizer
      ((S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
  by_cases hS : S ≤ Subgroup.normalizer (R : Set G)
  · rw [d.S₁_eq_S₀_iff.mpr hS]
    exact Subgroup.le_normalizer
  by_cases hΦ : ∃ r ∈ R, r * r ≠ 1
  · exact d.S₁_normal hR1 (Or.inl hΦ)
  by_cases hR2 : Nat.card R = 2
  · exact d.S₁_normal hR1 (Or.inr hR2)
  push Not at hΦ
  have hEA := burnsideIb_eaData_of_pairData d hR1 hΦ hR2
  have hmain := (hEA.main hS).1
  rw [← burnsideIb_S₁_eq]
  exact le_normalizer_of_conj_mem fun t ht u hu => hmain t ht.1 u hu

open CFSG.ClassicalInvolution in
private theorem burnsideIb_five {G : Type} [Group G] [Finite G] {K : Subgroup G} {g : G}
    {R S : Subgroup G} (d : PairData K g R S) (hR1 : R ≠ ⊥)
    (hlt : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K) :
    (Nat.card ↥R = 2 ∧ ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
        (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* SemidihedralGroup n)))) ∨
      (ChIJK.conjClosure R S = R ⊔ (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)) ∧
        ChIJK.IsDirectProductOf R (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G))
          (ChIJK.conjClosure R S) ∧
        Nonempty (↥(ChIJK.conjClosure R S) ≃* (↥R × ↥R))) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsElemAbelian 2 R ∧ Nat.card ↥R = 2 ^ n ∧
        ChIJK.IsSpecialGroup (ChIJK.conjClosure R S) ∧
        Nat.card ↥(ChIJK.conjClosure R S) = 2 ^ (3 * n) ∧
        ChIJK.centerOf (ChIJK.conjClosure R S) =
          S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ∧
        (ChIJK.conjClosure R S).relIndex S = 2) := by
  have hS : ¬ S ≤ Subgroup.normalizer (R : Set G) := d.S₁_lt_iff.mp hlt
  by_cases hΦ : ∃ r ∈ R, r * r ≠ 1
  · right
    left
    obtain ⟨hW, -⟩ := d.normalClosure_eq_normalizer hR1 hΦ hlt
    exact burnsideIb_five_b d hR1 (by rw [burnsideIb_conjClosure_eq]; exact hW)
  by_cases hR2 : Nat.card R = 2
  · left
    exact burnsideIb_five_a d hR1 hR2 hS
  push Not at hΦ
  right
  have hEA := burnsideIb_eaData_of_pairData d hR1 hΦ hR2
  obtain ⟨-, hcase⟩ := hEA.main hS
  rcases hcase with ⟨hNS, hW⟩ | ⟨hMS, hW, hcard, hcenter, hcomm, hfr, hrel⟩
  · left
    exact burnsideIb_five_b d hR1 (by rw [burnsideIb_conjClosure_eq]; exact hW)
  · right
    rw [burnsideIb_conjClosure_eq, hW]
    obtain ⟨n, hn⟩ := d.R_two.exists_card_eq
    rw [burnsideIb_S₁_eq] at hcenter hcomm hfr
    have h4 : 4 ≤ 2 ^ n := hn ▸ hEA.four_le
    have hn2 : 2 ≤ n := by
      by_contra hn2
      push Not at hn2
      interval_cases n <;> simp at h4
    refine ⟨n, hn2, ⟨⟨⟨fun a b => Subtype.ext (hEA.R_comm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩, hn,
      ⟨hfr.trans hcenter.symm, hcomm.trans hcenter.symm⟩, ?_, hcenter, hrel⟩
    · rw [pow_two]
      exact hEA.R_exp x hx
    · rw [hcard, hn]
      ring

end BurnsideIb

theorem as_I_7_5 : I_7_5 := by
  intro G _ _ K H Q S hyp hΦ h hh k hk hhS hkS hne
  have d := burnsideIb_tightData hyp
  have hΦ' := burnsideIb_exists_mul_self_ne_one hyp.Q_sylow.2.1 hΦ
  have key := d.commute_conj hΦ' (H.inv_mem hh) (H.inv_mem hk) hhS hkS hne
  unfold ChIJK.IsDirectProductOf
  exact ⟨fun a ha b hb => key.2 a ha b hb, key.1, rfl⟩

@[expose] def I_7_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    ∀ g ∈ H, Q ≠ CFSG.conjugate Q g → CFSG.conjugate Q g ≤ S →
      CFSG.conjugate Q g ⊓ Subgroup.normalizer (Q : Set G) ≠ ⊥ →
      IsDirectProductOf Q (CFSG.conjugate Q g) (Q ⊔ CFSG.conjugate Q g)

theorem as_I_7_6 : I_7_6 := by
  intro G _ _ K H Q S hyp g hg hne hgS hN
  have d := burnsideIb_tightData hyp
  have key := d.commute_of_inf_normalizer_ne_bot (g := g⁻¹) (H.inv_mem hg)
    (fun e => hne e.symm) hgS hN
  unfold ChIJK.IsDirectProductOf
  exact ⟨fun a ha b hb => key.2 a ha b hb, key.1, rfl⟩

@[expose] def I_7_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTightlyEmbedded K →
    ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
    ∀ R : Subgroup G, R ≠ ⊥ →
      IsSylowTwoIn R (K ⊓ Subgroup.normalizer (CFSG.conjugate K g : Set G)) →
      ∀ S : Subgroup G, R ≤ S → IsSylowTwoIn S (CFSG.conjugate K g ⊔ R) →
        (IsDirectProductOf (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G)) R
            (S ⊓ Subgroup.normalizer (R : Set G)) ∧
          S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) =
            S ⊓ CFSG.conjugate K g ⊓ Subgroup.centralizer (R : Set G)) ∧
        Nonempty (↥(S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G)) ≃* ↥R) ∧
        IsSylowTwoIn (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G))
          (CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G)) ∧
        (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) < S ⊓ CFSG.conjugate K g →
          ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
        (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) < S ⊓ CFSG.conjugate K g →
          (Nat.card ↥R = 2 ∧
            ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
              (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* SemidihedralGroup n)))) ∨
          (conjClosure R S = R ⊔ (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G)) ∧
            IsDirectProductOf R (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G))
              (conjClosure R S) ∧ Nonempty (↥(conjClosure R S) ≃* (↥R × ↥R))) ∨
          (∃ n : ℕ, 2 ≤ n ∧ IsElemAbelian 2 R ∧ Nat.card ↥R = 2 ^ n ∧
            IsSpecialGroup (conjClosure R S) ∧ Nat.card ↥(conjClosure R S) = 2 ^ (3 * n) ∧
            centerOf (conjClosure R S) =
              S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) ∧
            (conjClosure R S).relIndex S = 2)) ∧
        IsNormalIn (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G))
          (S ⊓ CFSG.conjugate K g)

theorem as_I_7_7 : I_7_7 := by
  intro G _ _ K hK g hg R hR1 hRsyl S hRS hSsyl
  have hK' : CFSG.Open.classicalInvolutionTightlyEmbedded K := by
    intro x hx
    have hx' : x⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h' =>
      hx (by simpa using Subgroup.inv_mem _ h')
    have := hK.2 x⁻¹ hx'
    simpa [CFSG.conjugate] using this
  have hg' : g⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h' =>
    hg (by simpa using Subgroup.inv_mem _ h')
  have d : CFSG.ClassicalInvolution.PairData K g⁻¹ R S :=
    ⟨hK', hg', burnsideIb_isSylow2Of hRsyl, burnsideIb_isSylow2Of hSsyl, hRS⟩
  refine ⟨⟨?_, d.S₁_eq_centralizer⟩, d.nonempty_mulEquiv_S₁ hR1,
    burnsideIb_isSylowTwoIn (d.sylow_S₁ hR1), fun hlt => d.commute_of_S₁_lt hR1 hlt,
    fun hlt => burnsideIb_five d hR1 hlt, ?_⟩
  · unfold ChIJK.IsDirectProductOf
    exact ⟨d.S₁_commute, d.S₁_inf_R, d.normalizer_eq_sup.symm⟩
  · exact ⟨inf_le_left, (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (burnsideIb_normal_S₁ d hR1)⟩

end CFSG.ASVolI
