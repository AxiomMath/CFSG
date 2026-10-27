module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {W : Type} [CommGroup W]

@[expose] def S16C11RF3 (L₀ : Subgroup (MulAut W)) (J : Subgroup W) : Prop :=
  ∀ T₀ : Subgroup (MulAut W), T₀ ≤ L₀ → IsPGroup 2 ↥T₀ → ¬ 2 ∣ T₀.relIndex L₀ →
    ∃ X₀ : Subgroup (MulAut W), X₀ ≤ L₀ ∧ T₀ ≤ X₀ ∧ T₀.relIndex X₀ = 3 ∧
      ∃ y ∈ J, (∀ t ∈ T₀, t y = y) ∧ ∃ g ∈ X₀, g y ≠ y

@[expose] def S16C11Pairs (L : Subgroup (MulAut W)) (J : Subgroup W) (T₁ : Subgroup (MulAut W))
    (N : ℕ) : Set (W × Subgroup (MulAut W)) :=
  {p | p.1 ∈ J ∧ (∀ t ∈ T₁, t p.1 = p.1) ∧ {z : W | ∃ l ∈ L, l p.1 = z}.ncard ≤ N ∧
    p.2 ≤ L ∧ T₁ ≤ p.2 ∧ T₁.relIndex p.2 = 3 ∧ ∃ g ∈ p.2, g p.1 ≠ p.1}

@[expose] def S16C11RF3Odd (L : Subgroup (MulAut W)) (J : Subgroup W) : Prop :=
  ∃ (N : ℕ) (T₁ : Subgroup (MulAut W)), T₁ ≤ L ∧ IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.relIndex L ∧
    Odd (S16C11Pairs L J T₁ N).ncard

theorem s16c11_mem_of_fix_of_relIndex_three {T₀ X₀ : Subgroup (MulAut W)} {y : W}
    (hTX : T₀ ≤ X₀) (h3 : T₀.relIndex X₀ = 3) (hfix : ∀ t ∈ T₀, t y = y)
    (hmov : ∃ g ∈ X₀, g y ≠ y) {x : MulAut W} (hx : x ∈ X₀) (hxy : x y = y) : x ∈ T₀ := by
  set S : Subgroup (MulAut W) := X₀ ⊓ MulAction.stabilizer (MulAut W) y with hS
  have hTS : T₀ ≤ S := fun t ht =>
    Subgroup.mem_inf.2 ⟨hTX ht, MulAction.mem_stabilizer_iff.2 (hfix t ht)⟩
  have hSX : S ≤ X₀ := inf_le_left
  have hxS : x ∈ S := Subgroup.mem_inf.2 ⟨hx, MulAction.mem_stabilizer_iff.2 hxy⟩
  have hne : ¬ X₀ ≤ S := by
    intro h
    obtain ⟨g, hg, hgy⟩ := hmov
    exact hgy (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (h hg)).2)
  have hmul := Subgroup.relIndex_mul_relIndex T₀ S X₀ hTS hSX
  rw [h3] at hmul
  have h1 : S.relIndex X₀ ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.1 h)
  have hd : S.relIndex X₀ ∣ 3 := ⟨T₀.relIndex S, by rw [← hmul, mul_comm]⟩
  have h2 : S.relIndex X₀ = 3 := ((Nat.dvd_prime Nat.prime_three).1 hd).resolve_left h1
  rw [h2] at hmul
  have h4 : T₀.relIndex S = 1 := by omega
  exact Subgroup.relIndex_eq_one.1 h4 hxS

theorem s16c11_relIndex_sup_pair {H : Type*} [Group H] [Finite H] {T₀ X : Subgroup H}
    (hN : T₀ ≤ normalizer (X : Set H)) (h3 : (T₀ ⊓ X).relIndex X = 3) :
    T₀.relIndex (T₀ ⊔ X) = 3 := by
  rw [(CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hN).1]
  exact h3

private lemma s16c11_case2gen_orbit_conj (L : Subgroup (MulAut W)) {t : MulAut W}
    (hconj : ∀ x ∈ L, MulAut.conj t x ∈ L) (hconj' : ∀ x ∈ L, MulAut.conj t⁻¹ x ∈ L)
    (y : W) :
    {z : W | ∃ l ∈ L, l (t y) = z} = t '' {z : W | ∃ l ∈ L, l y = z} := by
  ext z
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨(MulAut.conj t⁻¹ l) y, ⟨MulAut.conj t⁻¹ l, hconj' l hl, rfl⟩, ?_⟩
    rw [MulAut.conj_apply]
    simp [MulAut.mul_apply]
  · rintro ⟨w, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨MulAut.conj t l, hconj l hl, by simp [MulAut.conj_apply]⟩

private lemma s16c11_case2gen_conj_comp (l : MulAut W) :
    (MulAut.conj l).toMonoidHom.comp (MulAut.conj l⁻¹).toMonoidHom = MonoidHom.id (MulAut W) := by
  apply MonoidHom.ext
  intro x
  show MulAut.conj l (MulAut.conj l⁻¹ x) = x
  simp only [MulAut.conj_apply]
  group

private lemma s16c11_case2gen_conj_comp' (l : MulAut W) :
    (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom = MonoidHom.id (MulAut W) := by
  apply MonoidHom.ext
  intro x
  show MulAut.conj l⁻¹ (MulAut.conj l x) = x
  simp only [MulAut.conj_apply]
  group

private lemma s16c11_case2gen_map_conj_mul (a b : MulAut W) :
    (MulAut.conj (a * b)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
  rw [map_mul]
  apply MonoidHom.ext
  intro x
  rfl

private lemma s16c11_case2gen_map_conj_one (K : Subgroup (MulAut W)) :
    K.map (MulAut.conj (1 : MulAut W)).toMonoidHom = K := by
  have h : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
    apply MonoidHom.ext
    intro x
    simp [MulAut.conj_apply]
  rw [h, Subgroup.map_id]

private lemma s16c11_case2gen_mem_pairs_conj {L T₁ : Subgroup (MulAut W)} {J : Subgroup W}
    {N : ℕ} {l : MulAut W} (hl : l ∈ L) (hJ : ∀ x ∈ L, ∀ y ∈ J, x y ∈ J)
    {p : W × Subgroup (MulAut W)} (hp : p ∈ S16C11Pairs L J T₁ N) :
    (l p.1, p.2.map (MulAut.conj l).toMonoidHom) ∈
      S16C11Pairs L J (T₁.map (MulAut.conj l).toMonoidHom) N := by
  obtain ⟨hyJ, hfix, horb, hXL, hT₁X, hidx, hmov⟩ := hp
  refine ⟨hJ l hl p.1 hyJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    simp [MulAut.conj_apply, hfix s hs]
  · have hconj : ∀ x ∈ L, MulAut.conj l x ∈ L := fun x hx =>
      by simpa [MulAut.conj_apply] using L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    have hconj' : ∀ x ∈ L, MulAut.conj l⁻¹ x ∈ L := fun x hx =>
      by simpa [MulAut.conj_apply] using L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
    rw [s16c11_case2gen_orbit_conj L hconj hconj' p.1,
      Set.ncard_image_of_injective _ l.injective]
    exact horb
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    simpa [MulAut.conj_apply] using L.mul_mem (L.mul_mem hl (hXL hg)) (L.inv_mem hl)
  · exact Subgroup.map_mono hT₁X
  · rw [Subgroup.relIndex_map_map_of_injective T₁ p.2 (MulAut.conj l).injective, hidx]
  · obtain ⟨g, hg, hgy⟩ := hmov
    refine ⟨(MulAut.conj l).toMonoidHom g, Subgroup.mem_map_of_mem _ hg, ?_⟩
    exact fun h => hgy (l.injective (by simpa [MulAut.conj_apply] using h))

private lemma s16c11_case2gen_mem_pairs_smul [Finite W] {L L₀ T₀ : Subgroup (MulAut W)}
    {J : Subgroup W} {N : ℕ} (hL : ∀ x ∈ L₀, L.map (MulAut.conj x).toMonoidHom = L)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (hT₀ : T₀ ≤ L₀) {t : MulAut W} (ht : t ∈ T₀)
    {p : W × Subgroup (MulAut W)} (hp : p ∈ S16C11Pairs L J (T₀ ⊓ L) N) :
    (t p.1, p.2.map (MulAut.conj t).toMonoidHom) ∈ S16C11Pairs L J (T₀ ⊓ L) N := by
  obtain ⟨hyJ, hfix, horb, hXL, hT₁X, hidx, hmov⟩ := hp
  have htL₀ : t ∈ L₀ := hT₀ ht
  have hnorm : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hL t htL₀)
  have hnorm' : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hL t⁻¹ (L₀.inv_mem htL₀))
  have hconj : ∀ x ∈ L, MulAut.conj t x ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx
  have hconj' : ∀ x ∈ L, MulAut.conj t⁻¹ x ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hnorm' x).1 hx
  have hT₁conj : (T₀ ⊓ L).map (MulAut.conj t).toMonoidHom = T₀ ⊓ L := by
    refine le_antisymm ?_ ?_
    · intro s hs
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
      refine ⟨T₀.mul_mem (T₀.mul_mem ht hx.1) (T₀.inv_mem ht), ?_⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx.2
    · intro s hs
      refine ⟨MulAut.conj t⁻¹ s, ⟨T₀.mul_mem (T₀.mul_mem (T₀.inv_mem ht) hs.1) ht,
        (Subgroup.mem_normalizer_iff''.1 hnorm s).1 hs.2⟩, ?_⟩
      change MulAut.conj t (t⁻¹ * s * t) = s
      simp only [MulAut.conj_apply]
      group
  refine ⟨hJ t htL₀ p.1 hyJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hmem : t⁻¹ * s * t ∈ T₀ ⊓ L :=
      ⟨T₀.mul_mem (T₀.mul_mem (T₀.inv_mem ht) hs.1) ht,
        (Subgroup.mem_normalizer_iff''.1 hnorm s).1 hs.2⟩
    have hfx := hfix (t⁻¹ * s * t) hmem
    have hst : s * t = t * (t⁻¹ * s * t) := by group
    calc s (t p.1) = (s * t) p.1 := rfl
      _ = (t * (t⁻¹ * s * t)) p.1 := by rw [hst]
      _ = t ((t⁻¹ * s * t) p.1) := rfl
      _ = t p.1 := by rw [hfx]
  · rw [s16c11_case2gen_orbit_conj L hconj hconj' p.1,
      Set.ncard_image_of_injective _ t.injective]
    exact horb
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    exact hconj g (hXL hg)
  · rw [← hT₁conj]
    exact Subgroup.map_mono hT₁X
  · rw [← hT₁conj, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective, hidx]
  · obtain ⟨g, hg, hgy⟩ := hmov
    refine ⟨MulAut.conj t g, Subgroup.mem_map_of_mem _ hg, fun h => hgy ?_⟩
    exact t.injective (by simpa [MulAut.conj_apply] using h)

theorem s16c11_exists_fixed_pair [Finite W] {L L₀ T₀ : Subgroup (MulAut W)} {J : Subgroup W}
    {N : ℕ} (hL : ∀ x ∈ L₀, L.map (MulAut.conj x).toMonoidHom = L)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (hT₀ : T₀ ≤ L₀) (hT₀p : IsPGroup 2 ↥T₀)
    (hodd : Odd (S16C11Pairs L J (T₀ ⊓ L) N).ncard) :
    ∃ p ∈ S16C11Pairs L J (T₀ ⊓ L) N,
      ∀ t ∈ T₀, t p.1 = p.1 ∧ p.2.map (MulAut.conj t).toMonoidHom = p.2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun e : MulAut W => (e : W → W))
      (fun e₁ e₂ h => MulEquiv.ext (congrFun h))
  letI smulInst : SMul ↥T₀ ↥(S16C11Pairs L J (T₀ ⊓ L) N) :=
    ⟨fun t p => ⟨(t.1 p.1.1, p.1.2.map (MulAut.conj t.1).toMonoidHom),
      s16c11_case2gen_mem_pairs_smul hL hJ hT₀ t.2 p.2⟩⟩
  letI : MulAction ↥T₀ ↥(S16C11Pairs L J (T₀ ⊓ L) N) :=
    { toSMul := smulInst
      one_smul := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · show p.1.2.map (MulAut.conj (1 : MulAut W)).toMonoidHom = p.1.2
          rw [s16c11_case2gen_map_conj_one]
      mul_smul := by
        intro t₁ t₂ p
        apply Subtype.ext
        apply Prod.ext
        · show ((t₁ * t₂ : ↥T₀).1) p.1.1 = t₁.1 (t₂.1 p.1.1)
          rw [show ((t₁ * t₂ : ↥T₀).1) = t₁.1 * t₂.1 from rfl, MulAut.mul_apply]
        · show p.1.2.map (MulAut.conj ((t₁ * t₂ : ↥T₀).1)).toMonoidHom =
            (p.1.2.map (MulAut.conj t₂.1).toMonoidHom).map (MulAut.conj t₁.1).toMonoidHom
          rw [Subgroup.map_map]
          rw [show ((t₁ * t₂ : ↥T₀).1) = t₁.1 * t₂.1 from rfl,
            s16c11_case2gen_map_conj_mul] }
  have hodd' : Odd (Nat.card ↥(S16C11Pairs L J (T₀ ⊓ L) N)) := by
    rwa [Nat.card_coe_set_eq]
  have hnotdvd : ¬ 2 ∣ Nat.card ↥(S16C11Pairs L J (T₀ ⊓ L) N) := fun h =>
    (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h)
  obtain ⟨q, hq⟩ := hT₀p.nonempty_fixed_point_of_prime_not_dvd_card
    ↥(S16C11Pairs L J (T₀ ⊓ L) N) hnotdvd
  refine ⟨q.1, q.2, fun t ht => ?_⟩
  have hfixq : (⟨t, ht⟩ : ↥T₀) • q = q := (MulAction.mem_fixedPoints).1 hq ⟨t, ht⟩
  exact Prod.ext_iff.1 (congrArg Subtype.val hfixq)

theorem s16c11_odd_pairs_conj [Finite W] {L T₁ : Subgroup (MulAut W)} {J : Subgroup W} {N : ℕ}
    {l : MulAut W} (hl : l ∈ L) (hJ : ∀ x ∈ L, ∀ y ∈ J, x y ∈ J)
    (h : Odd (S16C11Pairs L J T₁ N).ncard) :
    Odd (S16C11Pairs L J (T₁.map (MulAut.conj l).toMonoidHom) N).ncard := by
  have hcard : (S16C11Pairs L J T₁ N).ncard =
      (S16C11Pairs L J (T₁.map (MulAut.conj l).toMonoidHom) N).ncard := by
    refine Set.ncard_congr
      (fun p _ => (l p.1, p.2.map (MulAut.conj l).toMonoidHom)) ?_ ?_ ?_
    · intro p hp
      exact s16c11_case2gen_mem_pairs_conj hl hJ hp
    · intro p q hp hq heq
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 heq
      exact Prod.ext (l.injective h1) (Subgroup.map_injective (MulAut.conj l).injective h2)
    · intro q hq
      have hT : (T₁.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = T₁ := by
        rw [Subgroup.map_map, s16c11_case2gen_conj_comp', Subgroup.map_id]
      have hmem : (l⁻¹ q.1, q.2.map (MulAut.conj l⁻¹).toMonoidHom) ∈
          S16C11Pairs L J T₁ N := by
        have h' := s16c11_case2gen_mem_pairs_conj (T₁ := T₁.map (MulAut.conj l).toMonoidHom)
          (l := l⁻¹) (L.inv_mem hl) hJ hq
        rwa [hT] at h'
      refine ⟨(l⁻¹ q.1, q.2.map (MulAut.conj l⁻¹).toMonoidHom), hmem, ?_⟩
      apply Prod.ext
      · show l (l⁻¹ q.1) = q.1
        simp
      · show (q.2.map (MulAut.conj l⁻¹).toMonoidHom).map (MulAut.conj l).toMonoidHom = q.2
        rw [Subgroup.map_map, s16c11_case2gen_conj_comp, Subgroup.map_id]
  rw [hcard] at h
  exact h

theorem s16c11_rf3_of_rf3Odd [Finite W] {L L₀ : Subgroup (MulAut W)} {J : Subgroup W}
    (hLL₀ : L ≤ L₀) (hL : ∀ x ∈ L₀, L.map (MulAut.conj x).toMonoidHom = L)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (h : S16C11RF3Odd L J) : S16C11RF3 L₀ J := by
  obtain ⟨N, T₁', hT₁'L, hT₁'p, hT₁'i, hodd'⟩ := h
  intro T₀ hT₀ hT₀p hT₀i
  have hnorm : L₀ ≤ normalizer (L : Set (MulAut W)) := fun x hx =>
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hL x hx)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ : CFSG.ABGLocalTools.IsSylowOf 2 T₀ L₀ :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hT₀, hT₀p, hT₀i⟩
  have hS₁ : CFSG.ABGLocalTools.IsSylowOf 2 (T₀ ⊓ L) L := hS₀.inf_of_le_normalizer hLL₀ hnorm
  have hS₁' : CFSG.ABGLocalTools.IsSylowOf 2 T₁' L :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hT₁'L, hT₁'p, hT₁'i⟩
  obtain ⟨k, hkL, hk⟩ := hS₁'.exists_mem_conj hS₁
  have hconj : T₀ ⊓ L = T₁'.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hk x, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨k⁻¹ * x * k, hx, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨z, hz, rfl⟩
      convert hz using 1
      simp [MulAut.conj_apply]
      group
  have hodd : Odd (S16C11Pairs L J (T₀ ⊓ L) N).ncard := by
    rw [hconj]
    exact s16c11_odd_pairs_conj hkL (fun x hx y hy => hJ x (hLL₀ hx) y hy) hodd'
  obtain ⟨⟨y, X⟩, hp, hfix⟩ := s16c11_exists_fixed_pair hL hJ hT₀ hT₀p hodd
  obtain ⟨hyJ, -, -, hXL, hT₁X, hidx, g, hgX, hgy⟩ := hp
  have hNX : T₀ ≤ normalizer (X : Set (MulAut W)) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix t ht).2
  have hinf : T₀ ⊓ X = T₀ ⊓ L :=
    le_antisymm (inf_le_inf_left _ hXL) (le_inf inf_le_left hT₁X)
  refine ⟨T₀ ⊔ X, sup_le hT₀ (hXL.trans hLL₀), le_sup_left, ?_, y, hyJ,
    fun t ht => (hfix t ht).1, g, (le_sup_right : X ≤ T₀ ⊔ X) hgX, hgy⟩
  exact s16c11_relIndex_sup_pair hNX (by rw [hinf]; exact hidx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
