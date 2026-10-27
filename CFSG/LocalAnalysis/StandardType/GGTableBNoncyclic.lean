module

public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def LargeEvenLabelAll (lab : LargeEvenLabel) (P : LargeEvenRawCont) : Prop :=
  ∀ Q : LargeEvenRawCont, CFSG.StandardType.LargeEvenRawDatum lab Q →
    CFSG.StandardType.LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ P R I F

namespace Legacy
abbrev LargeEvenLabelAll := CFSG.StandardType.LargeEvenLabelAll
end Legacy

namespace Canonical
@[expose] def LargeEvenLabelAll (lab : LargeEvenLabel) (P : LargeEvenRawCont) : Prop :=
  ∀ Q : LargeEvenRawCont, CFSG.Assembly.LargeEvenRawDatum lab Q →
    CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ P R I F
end Canonical

theorem largeEvenLabelAll_and {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P) (h' : LargeEvenLabelAll lab P') :
    LargeEvenLabelAll lab fun R _ I F => P R I F ∧ P' R I F := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨⟨hq, hp⟩, hp'⟩ => ⟨hq, hp, hp'⟩) (h' _ (h Q hQ))

theorem largeEvenMarking_and_labelAll {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {S : LargeEvenLabel → Prop} {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab P')
    (hS : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → S lab)
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have hraw' := hall lab hlab (hS lab R I F θ hP) _ hraw
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP'⟩

instance ggInnNormal (R : Type*) [Group R] : (MulAut.conj : R →* MulAut R).range.Normal where
  conj_mem := by
    rintro _ ⟨r, rfl⟩ φ
    refine ⟨φ r, ?_⟩
    ext s
    simp [MulAut.conj_apply]

@[expose] def GGOutdiagCyclic (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∃ φ₀ : MulAut R,
    I ⊆ ((MulAut.conj : R →* MulAut R).range ⊔ Subgroup.zpowers φ₀ : Subgroup (MulAut R))

theorem ggOutdiagCyclic_of_subset_inn {R : Type} [Group R] {I : Set (MulAut R)}
    (h : I ⊆ (MulAut.conj : R →* MulAut R).range) : GGOutdiagCyclic R I :=
  ⟨1, fun _ hφ => Subgroup.mem_sup_left (h hφ)⟩

theorem mulAut_conj_injective {R : Type*} [Group R] (hR : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hc : r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut R => φ g) hr
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * r = r * g * r⁻¹ * r := by rw [this]
      _ = r * g := by group
  rw [hR] at hc
  exact (Subgroup.mem_bot.mp hc)

section Core

variable {G : Type} [Group G] [Finite G]

theorem map_sup_zpowers_le {M : Type*} [Group M] (N : Subgroup M) [N.Normal] (φ₀ : M) :
    (N ⊔ Subgroup.zpowers φ₀).map (QuotientGroup.mk' N) ≤
      Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  refine sup_le ?_ le_rfl
  rintro _ ⟨n, hn, rfl⟩
  have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [h1]
  exact one_mem _

theorem exists_noncyclic_quot_of_outdiag {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤) {R : Type} [Group R]
    (hR : Subgroup.center R = ⊥) (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hO : GGOutdiagCyclic R I) (hB : p ^ 4 ≤ Nat.card B) :
    ∃ F : Subgroup R, IsPGroup p F ∧ ¬ IsCyclic F := by
  have := Fact.mk hp
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  obtain ⟨φ₀, hφ₀⟩ := hO
  set β := ggBeta L θ hBN with hβ
  have : Finite β.range := Finite.of_surjective _ β.rangeRestrict_surjective
  set N := (MulAut.conj : R →* MulAut R).range with hN
  set χ := (QuotientGroup.mk' N).comp β with hχdef
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hS.1.1.2 b b.2)
  have hχ : χ.range ≤ Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
    rintro _ ⟨b, rfl⟩
    exact map_sup_zpowers_le N φ₀ ⟨β b, hφ₀ (ggBeta_mem L θ hBN h3 b), rfl⟩
  have : Finite χ.range := Finite.of_surjective _ χ.rangeRestrict_surjective
  have hcχ : IsCyclic χ.range := by
    let e := Subgroup.subgroupOfEquivOfLe hχ
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hcardχ : Nat.card χ.range ≤ p := by
    refine card_le_of_isCyclic hp.pos hcχ ?_
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, hBp, map_one]
  set β₀ := β.comp χ.ker.subtype with hβ₀
  have hβ₀N : β₀.range ≤ N := by
    rintro _ ⟨k, rfl⟩
    have hk : χ k = 1 := k.2
    exact (QuotientGroup.eq_one_iff _).mp hk
  have hkerβ : Nat.card β.ker = p := by
    have h1 := card_range_mul_card_ker β
    have h2 := card_range_ggBeta_mul L θ hp hS hL hBN
    have hpos : 0 < Nat.card β.range := Nat.card_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hkerβ₀ : Nat.card β₀.ker ≤ p := by
    rw [← hkerβ]
    refine Nat.card_le_card_of_injective
      (fun k : β₀.ker => (⟨((k : χ.ker) : B), MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp k.2)⟩ :
        β.ker)) ?_
    intro k k' h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : β.ker => (z : B)) h))
  set F := β₀.range.comap (MulAut.conj : R →* MulAut R) with hF
  have hinj := mulAut_conj_injective hR
  have hFcard : Nat.card F = Nat.card β₀.range := by
    have h := Subgroup.map_comap_eq (MulAut.conj : R →* MulAut R) β₀.range
    rw [← hN, inf_eq_right.mpr hβ₀N] at h
    rw [← h]
    exact Nat.card_congr (F.equivMapOfInjective _ hinj).toEquiv
  have hFexp : ∀ r ∈ F, r ^ p = 1 := by
    intro r hr
    obtain ⟨k, hk⟩ := hr
    apply hinj
    rw [map_pow, ← hk, ← map_pow]
    have : k ^ p = 1 := Subtype.ext (by simpa using hBp (k : B))
    rw [this, map_one, map_one]
  refine ⟨F, fun r => ⟨1, Subtype.ext (by simpa using hFexp r r.2)⟩,
    not_isCyclic_of_card hp.one_lt hFexp ?_⟩
  rw [hFcard]
  have h1 := card_range_mul_card_ker χ
  have h2 := card_range_mul_card_ker β₀
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have key : p ^ 4 ≤ p ^ 2 * Nat.card β₀.range := by
    calc p ^ 4 ≤ Nat.card B := hB
      _ = Nat.card χ.range * Nat.card χ.ker := h1.symm
      _ ≤ p * Nat.card χ.ker := Nat.mul_le_mul_right _ hcardχ
      _ = p * (Nat.card β₀.range * Nat.card β₀.ker) := by rw [h2]
      _ ≤ p * (Nat.card β₀.range * p) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hkerβ₀)
      _ = p ^ 2 * Nat.card β₀.range := by ring
  have : p ^ 4 = p ^ 2 * p ^ 2 := by ring
  rw [this] at key
  exact Nat.le_of_mul_le_mul_left key hp0

end Core

section Input

variable {G : Type} [Group G] [Finite G]

theorem pow_four_le_card_of_bmax {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : LargeEvenIsBmax p B) (h4 : 4 ≤ LargeEvenTwoLocalRank p G) : p ^ 4 ≤ Nat.card B := by
  rw [hB.2.1]
  exact Nat.pow_le_pow_right hp.pos h4

omit [Finite G] in
theorem center_eq_bot_of_simple_nonabelian {R : Type*} [Group R] [IsSimpleGroup R]
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ Subgroup.center R := by
      rw [h]
      exact Subgroup.mem_top b
    exact hab ((Subgroup.mem_center_iff.mp hb) a)

theorem exists_noncyclic_of_marking_outdiag {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (h4 : 4 ≤ LargeEvenTwoLocalRank p G)
    (hM : LargeEvenMarking L fun _ R _ I _ θ => (B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      GGOutdiagCyclic R I) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  have := Fact.mk hp
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨hBN, h3⟩, hO⟩ := largeEvenRawDatum_exists hraw
  have := hs
  obtain ⟨F', hF', hnc⟩ := exists_noncyclic_quot_of_outdiag hp hS hL
    (center_eq_bot_of_simple_nonabelian hna) θ hBN h3 hO (pow_four_le_card_of_bmax hp hS.1 h4)
  exact exists_noncyclic_of_noncyclic_quot (θ.toMonoidHom.comp (QuotientGroup.mk' _))
    (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hF' hnc

@[expose] def GGLNoncyclicInputOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L →
    LargeEvenMarking L (fun lab _ _ I _ θ => S lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S

theorem ggLNoncyclicInputOn_of_labels {S : LargeEvenLabel → Prop}
    (h : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I) :
    GGLNoncyclicInputOn S := by
  intro G _ _ p B x L hT hM
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hM' := largeEvenMarking_and_labelAll h (fun _ _ _ _ _ _ hP => hP.1) hM
  exact exists_noncyclic_of_marking_outdiag hβ.1 hS hβ.2.2.2
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1.2.2, h.2⟩) hM')

theorem ggLNoncyclicInput_of_labels
    (h : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I) :
    GGLNoncyclicInput := by
  intro G _ _ p B x L hT
  have hon := ggLNoncyclicInputOn_of_labels (S := fun _ => True) (fun lab hlab _ => h lab hlab)
  exact hon G p B x L hT
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hT.2.2.2.2.2.2.2.1)

end Input

end CFSG.StandardType
