module

public import CFSG.RankThree.GF2n.Parrott.CaseIICentreSylow
public import CFSG.RankThree.GF2n.Parrott.Section4Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Parrott.CaseIIIndex
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.Section4EInv
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34Instance

import all CFSG.RankThree.GF2n.Parrott.CaseIIDouble

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.GF2n.Parrott.CaseIIDouble
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

local notation "C2" => Multiplicative (ZMod 2)

variable {K : Type} [Group K] [Finite K] {w : K}

omit [Finite K] in
theorem normalizer_prod_top (L : Subgroup K) :
    Subgroup.normalizer ((L.prod (⊤ : Subgroup C2) :
      Subgroup (D2 K)) : Set (D2 K)) =
      (Subgroup.normalizer (L : Set K)).prod (⊤ : Subgroup C2) := by
  ext ⟨k, c⟩
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_prod]
  constructor
  · intro hk
    refine ⟨Subgroup.mem_normalizer_iff.mpr fun a => ?_, Subgroup.mem_top c⟩
    have := hk (a, 1)
    simpa [Subgroup.mem_prod] using this
  · rintro ⟨hk, -⟩ ⟨a, b⟩
    have := Subgroup.mem_normalizer_iff.mp hk a
    simp only [Subgroup.mem_prod, Subgroup.mem_top, and_true]
    simpa using this

omit [Finite K] in
theorem centralizer_prod_top (F : Subgroup K) :
    Subgroup.centralizer ((F.prod (⊤ : Subgroup C2) :
      Subgroup (D2 K)) : Set (D2 K)) =
      (Subgroup.centralizer (F : Set K)).prod (⊤ : Subgroup C2) := by
  ext ⟨k, c⟩
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_prod, Subgroup.mem_centralizer_iff]
  constructor
  · intro hk
    refine ⟨fun a ha => ?_, Subgroup.mem_top c⟩
    have := hk (a, 1) (by simpa [Subgroup.mem_prod] using ha)
    simpa [Prod.ext_iff] using this
  · rintro ⟨hk, -⟩ ⟨a, b⟩ hab
    have ha : a ∈ F := (Subgroup.mem_prod.mp hab).1
    have := hk a ha
    refine Prod.ext (by simpa using this) ?_
    exact mul_comm _ _

omit [Finite K] in
theorem card_prod_top (L : Subgroup K) :
    Nat.card (L.prod (⊤ : Subgroup C2)) = Nat.card L * 2 := by
  rw [Nat.card_congr (Subgroup.prodEquiv L ⊤).toEquiv, Nat.card_prod, Subgroup.card_top]
  simp

omit [Finite K] in
theorem prod_top_inf (A B : Subgroup K) :
    A.prod (⊤ : Subgroup C2) ⊓ B.prod (⊤ : Subgroup C2)
      = (A ⊓ B).prod (⊤ : Subgroup C2) := by
  ext ⟨k, c⟩
  simp [Subgroup.mem_prod]

omit [Finite K] in
theorem prod_top_sup (A B : Subgroup K) :
    A.prod (⊤ : Subgroup C2) ⊔ B.prod (⊤ : Subgroup C2)
      = (A ⊔ B).prod (⊤ : Subgroup C2) := by
  simp only [Subgroup.prod_top]
  exact Subgroup.comap_sup_eq (MonoidHom.fst K C2) A B
    (fun k => ⟨(k, 1), rfl⟩)

omit [Finite K] in
theorem isElemAbelian_prod_top {E : Subgroup K} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.prod (⊤ : Subgroup C2)) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    refine Prod.ext ?_ (mul_comm _ _)
    exact hE.comm (Subgroup.mem_prod.mp x.2).1 (Subgroup.mem_prod.mp y.2).1
  · refine Prod.ext ?_ ?_
    · simpa using hE.2 _ (Subgroup.mem_prod.mp hx).1
    · change x.2 ^ 2 = 1
      have h : x.2 ^ 2 = 1 := by
        have := pow_card_eq_one' (G := C2) (x := x.2)
        simpa using this
      exact h

theorem isParrottE_prod_top (h : Tim79a.ParrottHypA w) {E : Subgroup K}
    (hEH : E ≤ H w) (hEHJ : E ≤ ⁅H w, H w⁆ ⊔ J w) (hwE : w ∈ E) (hE2 : IsElemAbelian 2 E)
    (hcard : Nat.card E = 2 ^ 9) (hcardJ : Nat.card ↥(E ⊓ J w) = 2 ^ 5)
    (hECE : E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K))
    (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920) :
    IsParrottE (zz w) (E.prod (⊤ : Subgroup C2)) := by
  refine ⟨?_, ?_, ?_, isElemAbelian_prod_top hE2, ?_, ?_, ?_, ?_⟩
  · rw [H_zz]
    exact Subgroup.prod_mono hEH le_rfl
  · rw [H_zz, J_zz, Subgroup.commutator_prod_prod]
    have htop : ⁅(⊤ : Subgroup C2),
        (⊤ : Subgroup C2)⁆ = ⊥ :=
      Subgroup.commutator_self_eq_bot_iff.mpr (by infer_instance)
    rw [htop]
    rintro ⟨e, c⟩ hec
    have he : e ∈ E := (Subgroup.mem_prod.mp hec).1
    have h1 : ((e, 1) : D2 K) ∈ ⁅H w, H w⁆.prod (⊥ : Subgroup C2) ⊔
        (J w).prod (⊤ : Subgroup C2) := by
      have hinl : ∀ L : Subgroup K, L.map (MonoidHom.inl K C2) ≤
          L.prod (⊥ : Subgroup C2) := by
        intro L
        rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem _⟩
      have h0 := Subgroup.mem_map_of_mem (MonoidHom.inl K C2) (hEHJ he)
      rw [Subgroup.map_sup] at h0
      exact sup_le_sup (hinl _) ((hinl _).trans (Subgroup.prod_mono le_rfl le_top)) h0
    have h2 : ((1, c) : D2 K) ∈ ⁅H w, H w⁆.prod (⊥ : Subgroup C2) ⊔
        (J w).prod (⊤ : Subgroup C2) :=
      Subgroup.mem_sup_right (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top c⟩)
    have h4 : ((e, 1) * (1, c) : D2 K) = (e, c) := by simp
    rw [← h4]
    exact Subgroup.mul_mem _ h1 h2
  · rw [centerIn_J_zz, centerIn_J_eq_zpowers_A h]
    exact Subgroup.prod_mono (Subgroup.zpowers_le.mpr hwE) le_rfl
  · rw [card_prod_top, hcard]
    norm_num
  · rw [J_zz, prod_top_inf, card_prod_top, hcardJ]
    norm_num
  · rw [H_zz, J_zz, prod_top_inf, centralizer_prod_top, prod_top_inf]
    exact congrArg (fun L : Subgroup K => L.prod (⊤ : Subgroup C2)) hECE
  · rw [normalizer_prod_top, H_zz, prod_top_inf,
      relIndex_prod_top_eq (le_inf Subgroup.le_normalizer hEH), hrel]

omit [Finite K] in
theorem isElemAbelian_of_generated {E : Subgroup K} (hwE : w ∈ E) (hEH : E ≤ H w)
    (hgen : ∀ x ∈ E, x ∈ Subgroup.closure
      {y : K | ∃ n ∈ Subgroup.normalizer (E : Set K), y = n * w * n⁻¹}) (hw2 : w * w = 1) :
    IsElemAbelian 2 E := by
  have hmemE : ∀ n ∈ Subgroup.normalizer (E : Set K), n * w * n⁻¹ ∈ E := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp hn w).mp hwE
  have hcomm : ∀ x ∈ E, x * w = w * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hEH hx)
  have hclosure : IsElemAbelian 2 (Subgroup.closure
      {y : K | ∃ n ∈ Subgroup.normalizer (E : Set K), y = n * w * n⁻¹}) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro _ ⟨n₁, hn₁, rfl⟩ _ ⟨n₂, hn₂, rfl⟩
      have hm : n₂⁻¹ * n₁ ∈ Subgroup.normalizer (E : Set K) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₂) hn₁
      have h1 := hcomm _ (hmemE _ hm)
      calc n₁ * w * n₁⁻¹ * (n₂ * w * n₂⁻¹)
          = n₂ * ((n₂⁻¹ * n₁) * w * (n₂⁻¹ * n₁)⁻¹ * w) * n₂⁻¹ := by group
        _ = n₂ * (w * ((n₂⁻¹ * n₁) * w * (n₂⁻¹ * n₁)⁻¹)) * n₂⁻¹ := by rw [h1]
        _ = n₂ * w * n₂⁻¹ * (n₁ * w * n₁⁻¹) := by group
    · rintro _ ⟨n, hn, rfl⟩
      calc (n * w * n⁻¹) ^ 2 = n * (w * w) * n⁻¹ := by rw [pow_two]; group
        _ = 1 := by rw [hw2]; group
  exact hclosure.mono hgen

omit [Finite K] in
private theorem zz_eq_mk (w : K) : zz w = ((w, 1) : D2 K) := rfl

omit [Finite K] in
theorem commutator_mk_mk (r s : K) (c d : C2) :
    ⁅((r, c) : D2 K), ((s, d) : D2 K)⁆ = ((⁅r, s⁆, 1) : D2 K) := by
  refine Prod.ext (by simp [commutatorElement_def]) ?_
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm c d)

omit [Finite K] in
private theorem mem_conjugate_iff' (S : Subgroup K) (g x : K) :
    x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ S
    rw [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    exact hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group⟩

private theorem hJ_prod (hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j) :
    ∀ j ∈ J (zz w), j ∉ Subgroup.zpowers (zz w) → ¬ IsConj (zz w) j := by
  rintro ⟨j, c⟩ hj hjz hjc
  rw [J_zz, Subgroup.mem_prod] at hj
  obtain ⟨g, hg⟩ := isConj_iff.mp hjc
  rw [zz_eq_mk] at hg
  have hc1 : c = 1 := by
    have := congrArg Prod.snd hg
    simpa using this.symm
  have hjw : g.1 * w * g.1⁻¹ = j := by
    have := congrArg Prod.fst hg
    simpa using this
  refine hJ j hj.1 (fun hjw' => hjz ?_) (isConj_iff.mpr ⟨g.1, hjw⟩)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hjw'
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [zz_eq_mk, hc1]; simp [← hk]⟩

private theorem centerIn_J_eq_centerIn_H (h : Tim79a.ParrottHypA w) :
    centerIn (J w) = centerIn (H w) := by
  apply le_antisymm
  · rw [centerIn_J_eq_zpowers_A h]
    exact Subgroup.zpowers_le.mpr ⟨J_le_H (z_mem_J_A h), z_centralizes_H_A⟩
  · intro x hx
    have hxJ : x ∈ J w := h.centralizer_le ⟨hx.1, Subgroup.centralizer_le J_le_H hx.2⟩
    exact ⟨hxJ, Subgroup.centralizer_le J_le_H hx.2⟩

omit [Finite K] in
private theorem centerIn_prod_top (L : Subgroup K) :
    centerIn (L.prod (⊤ : Subgroup C2)) =
      (centerIn L).prod (⊤ : Subgroup C2) := by
  rw [centerIn, centralizer_prod_top, prod_top_inf, centerIn]

private theorem centerIn_J_zz_eq_centerIn_H_zz (h : Tim79a.ParrottHypA w) :
    centerIn (J (zz w)) = centerIn (H (zz w)) := by
  rw [centerIn_J_zz, H_zz, centerIn_prod_top, centerIn_J_eq_centerIn_H h]

private theorem hweak_prod {E : Subgroup K}
    (hweak : ∀ T : Subgroup K, IsSylowOf 2 T (H w) → E ≤ T →
      ∀ g : K, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) :
    ∀ T₂ : Subgroup (D2 K), IsSylowOf 2 T₂ (H (zz w)) →
      E.prod (⊤ : Subgroup C2) ≤ T₂ →
      ∀ g : D2 K, CFSG.conjugate (E.prod (⊤ : Subgroup C2)) g ≤ T₂ →
        CFSG.conjugate (E.prod (⊤ : Subgroup C2)) g =
          E.prod (⊤ : Subgroup C2) := by
  intro T₂ hT₂ hET g hg
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H w)
  have hT₂' : IsSylowOf 2 (T.prod (⊤ : Subgroup C2)) (H (zz w)) := by
    rw [H_zz]
    exact isSylowOf_prod_top hT
  obtain ⟨k, -, hk⟩ := hT₂.exists_mem_conj hT₂'
  have hc : ∀ c : C2, ((1, c) : D2 K) ∈ T₂ := by
    intro c
    have h1 := (hk (1, c)).mp (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top c⟩)
    have h2 : k⁻¹ * ((1, c) : D2 K) * k = (1, c) := by
      refine Prod.ext (by simp) ?_
      simp [mul_comm]
    rwa [h2] at h1
  have hmem : ∀ (a : K) (c : C2), ((a, c) : D2 K) ∈ T₂ ↔ ((a, 1) : D2 K) ∈ T₂ := by
    intro a c
    have h1 : ((a, c) : D2 K) = (a, 1) * (1, c) := by simp
    constructor
    · intro hac
      have h2 : ((a, 1) : D2 K) = (a, c) * (1, c)⁻¹ := by simp
      rw [h2]
      exact T₂.mul_mem hac (T₂.inv_mem (hc c))
    · intro ha
      rw [h1]
      exact T₂.mul_mem ha (hc c)
  set T' : Subgroup K := T₂.comap (MonoidHom.inl K C2) with hT'
  have hT₂eq : T₂ = T'.prod (⊤ : Subgroup C2) := by
    ext ⟨a, c⟩
    rw [Subgroup.mem_prod, hmem a c, hT', Subgroup.mem_comap]
    simp
  have hT'S : IsSylowOf 2 T' (H w) := by
    have h1 := (isSylowOf_iff (p := 2)).mp hT₂
    rw [isSylowOf_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have := h1.1 ha
      rw [H_zz, Subgroup.mem_prod] at this
      exact this.1
    · exact h1.2.1.comap_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab)
    · have h3 := h1.2.2
      rw [hT₂eq, H_zz] at h3
      have hT'H : T' ≤ H w := by
        intro a ha
        have := h1.1 ha
        rw [H_zz, Subgroup.mem_prod] at this
        exact this.1
      rwa [relIndex_prod_top_eq hT'H] at h3
  have hET' : E ≤ T' := fun e he => by
    show ((e, 1) : D2 K) ∈ T₂
    exact hET (Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top 1⟩)
  obtain ⟨g₁, c⟩ := g
  have hcj : CFSG.conjugate E g₁ ≤ T' := by
    intro x hx
    rw [mem_conjugate_iff'] at hx
    have h1 : ((x, 1) : D2 K) ∈ CFSG.conjugate (E.prod (⊤ : Subgroup C2))
        (g₁, c) := by
      rw [mem_conjugate_iff']
      · exact Subgroup.mem_prod.mpr ⟨by simpa using hx, Subgroup.mem_top _⟩
    exact hg h1
  have hEq := hweak T' hT'S hET' g₁ hcj
  ext ⟨x, d⟩
  rw [mem_conjugate_iff', Subgroup.mem_prod, Subgroup.mem_prod]
  have e1 : ((g₁, c) * (x, d) * (g₁, c)⁻¹ : D2 K) = (g₁ * x * g₁⁻¹, d) := by
    refine Prod.ext (by simp) ?_
    simp
  rw [e1]
  simp only [Subgroup.mem_top, and_true]
  rw [← mem_conjugate_iff' E g₁ x, hEq]

section Double

variable (h : Tim79a.ParrottHypA w) {E : Subgroup K}
  (hEH : E ≤ H w) (hEHJ : E ≤ ⁅H w, H w⁆ ⊔ J w) (hwE : w ∈ E) (hE2 : IsElemAbelian 2 E)
  (hcard : Nat.card E = 2 ^ 9) (hcardJ : Nat.card ↥(E ⊓ J w) = 2 ^ 5)
  (hECE : E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K))
  (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920)

include h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel

private theorem kp_J_le_normalizer : J w ≤ Subgroup.normalizer (E : Set K) := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  intro j hj
  have hj2 : ((j, 1) : D2 K) ∈ J (zz w) := by
    rw [J_zz]
    exact Subgroup.mem_prod.mpr ⟨hj, Subgroup.mem_top 1⟩
  have h1 := J_le_normalizer_of_isParrottE (parrottHyp_zz h) hE hj2
  rw [normalizer_prod_top, Subgroup.mem_prod] at h1
  exact h1.1

private theorem kp_relIndex_sup_J : E.relIndex (J w ⊔ E) = 16 := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have h1 := relIndex_sup_J_of_isParrottE (parrottHyp_zz h) hE
  rw [J_zz, prod_top_sup, relIndex_prod_top_eq le_sup_right] at h1
  exact h1

private theorem kp_commutator_mem {r s : K} (hr : r ∈ J w ⊔ E) (hs : s ∈ J w ⊔ E) :
    ⁅r, s⁆ ∈ E := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have hr2 : ((r, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hr, Subgroup.mem_top 1⟩
  have hs2 : ((s, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hs, Subgroup.mem_top 1⟩
  have h1 := commutator_mem_of_mem_J_sup (parrottHyp_zz h) hE hr2 hs2
  rw [commutator_mk_mk, Subgroup.mem_prod] at h1
  exact h1.1

private theorem kp_mul_self_mem {r : K} (hr : r ∈ J w ⊔ E) : r * r ∈ E := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have hr2 : ((r, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hr, Subgroup.mem_top 1⟩
  have h1 := mul_self_mem_of_mem_J_sup (parrottHyp_zz h) hE hr2
  have e : ((r, 1) : D2 K) * (r, 1) = (r * r, 1) := by simp
  rw [e, Subgroup.mem_prod] at h1
  exact h1.1

private theorem kp_exists_commutator_eq_w {r : K} (hr : r ∈ J w ⊔ E) (hrE : r ∉ E) :
    ∃ e ∈ E, ⁅r, e⁆ = w := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have hr2 : ((r, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hr, Subgroup.mem_top 1⟩
  have hrE2 : ((r, 1) : D2 K) ∉ E.prod (⊤ : Subgroup C2) := fun hh =>
    hrE (Subgroup.mem_prod.mp hh).1
  obtain ⟨⟨e, c⟩, hec, hcomm⟩ := exists_commutator_eq_z (parrottHyp_zz h) hE hr2 hrE2
  refine ⟨e, (Subgroup.mem_prod.mp hec).1, ?_⟩
  rw [commutator_mk_mk, zz_eq_mk] at hcomm
  exact congrArg Prod.fst hcomm

private theorem kp_commutator_eq_w_of_isConj
    (hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    {r e : K} (hr : r ∈ J w ⊔ E) (he : e ∈ E) (hc : IsConj w ⁅r, e⁆) : ⁅r, e⁆ = w := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have hr2 : ((r, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hr, Subgroup.mem_top 1⟩
  have he2 : ((e, 1) : D2 K) ∈ E.prod (⊤ : Subgroup C2) :=
    Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top 1⟩
  have hJ2 := hJ_prod hJ
  have hc2 : IsConj (zz w) ⁅((r, 1) : D2 K), (e, 1)⁆ := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    refine isConj_iff.mpr ⟨(g, 1), ?_⟩
    rw [commutator_mk_mk, zz_eq_mk]
    refine Prod.ext ?_ (by simp)
    simpa using hg
  have h1 := commutator_eq_z_of_isConj (parrottHyp_zz h) hE hJ2 hr2 he2 hc2
  rw [commutator_mk_mk, zz_eq_mk] at h1
  exact congrArg Prod.fst h1

private theorem kp_exists_perm_five
    (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hweak : ∀ T : Subgroup K, IsSylowOf 2 T (H w) → E ≤ T →
      ∀ g : K, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) :
    ∃ π : ↥(Subgroup.normalizer (E : Set K) ⊓ H w) →* Equiv.Perm (Fin 5),
      Function.Surjective π ∧
        π.ker = (J w ⊔ E).subgroupOf (Subgroup.normalizer (E : Set K) ⊓ H w) := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have : ((J (zz w)).subgroupOf (H (zz w))).Normal := J_subgroupOf_normal (zz w)
  obtain ⟨π₂, hπ₂s, hπ₂k⟩ := exists_perm_five_of_isParrottE (quotientDataZZ D)
    (parrottHyp_zz h) hE (hweak_prod hweak)
  have hN₂ : Subgroup.normalizer ((E.prod (⊤ : Subgroup C2) :
      Subgroup (D2 K)) : Set (D2 K)) ⊓ H (zz w) =
      (Subgroup.normalizer (E : Set K) ⊓ H w).prod (⊤ : Subgroup C2) := by
    rw [normalizer_prod_top, H_zz, prod_top_inf]
  let φ : ↥(Subgroup.normalizer (E : Set K) ⊓ H w) →*
      ↥(Subgroup.normalizer ((E.prod (⊤ : Subgroup C2) :
        Subgroup (D2 K)) : Set (D2 K)) ⊓ H (zz w)) :=
    ((MonoidHom.inl K C2).comp
      (Subgroup.normalizer (E : Set K) ⊓ H w).subtype).codRestrict _ (fun n => by
        rw [hN₂]
        exact Subgroup.mem_prod.mpr ⟨n.2, Subgroup.mem_top 1⟩)
  have hker : ∀ (c : C2) (hm : ((1, c) : D2 K) ∈
      Subgroup.normalizer ((E.prod (⊤ : Subgroup C2) :
        Subgroup (D2 K)) : Set (D2 K)) ⊓ H (zz w)),
      π₂ ⟨(1, c), hm⟩ = 1 := by
    intro c hm
    have : (⟨(1, c), hm⟩ : ↥(Subgroup.normalizer ((E.prod (⊤ : Subgroup C2) :
        Subgroup (D2 K)) : Set (D2 K)) ⊓ H (zz w))) ∈ π₂.ker := by
      rw [hπ₂k, Subgroup.mem_subgroupOf]
      show ((1, c) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2)
      exact Subgroup.mem_sup_left (by
        rw [J_zz]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top c⟩)
    exact this
  refine ⟨π₂.comp φ, ?_, ?_⟩
  · intro σ
    obtain ⟨x, hx⟩ := hπ₂s σ
    obtain ⟨⟨n, c⟩, hxmem⟩ := x
    have hnN : n ∈ Subgroup.normalizer (E : Set K) ⊓ H w := by
      have := hxmem
      rw [hN₂, Subgroup.mem_prod] at this
      exact this.1
    have hcm : ((1, c) : D2 K) ∈ Subgroup.normalizer ((E.prod (⊤ : Subgroup C2) :
        Subgroup (D2 K)) : Set (D2 K)) ⊓ H (zz w) := by
      rw [hN₂]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top c⟩
    refine ⟨⟨n, hnN⟩, ?_⟩
    have hxe : (⟨(n, c), hxmem⟩ : ↥(Subgroup.normalizer ((E.prod (⊤ : Subgroup C2) :
        Subgroup (D2 K)) : Set (D2 K)) ⊓ H (zz w))) = φ ⟨n, hnN⟩ * ⟨(1, c), hcm⟩ := by
      refine Subtype.ext (Prod.ext ?_ ?_) <;> simp [φ]
    rw [MonoidHom.comp_apply, ← hx, hxe, map_mul, hker c hcm, mul_one]
  · ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπ₂k,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show ((n : K), (1 : C2)) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) ↔ _
    rw [J_zz, prod_top_sup, Subgroup.mem_prod]
    simp

private theorem kp_odd_relIndex
    (D : QuotientData (z := w) (J_subgroupOf_normal w)) :
    Odd ((Subgroup.normalizer (E : Set K) ⊓ H w).relIndex (Subgroup.normalizer (E : Set K))) := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have : ((J (zz w)).subgroupOf (H (zz w))).Normal := J_subgroupOf_normal (zz w)
  have h1 := odd_relIndex_of_isParrottE (quotientDataZZ D) (parrottHyp_zz h)
    (centerIn_J_zz_eq_centerIn_H_zz h) hE
  rw [normalizer_prod_top, H_zz, prod_top_inf,
    relIndex_prod_top_eq (inf_le_left : Subgroup.normalizer (E : Set K) ⊓ H w ≤ _)] at h1
  exact h1

private theorem kp_transitive
    (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hIII : ¬ ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hweak : ∀ T : Subgroup K, IsSylowOf 2 T (H w) → E ≤ T →
      ∀ g : K, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) :
    ∀ r ∈ J w ⊔ E, ∀ s ∈ J w ⊔ E, r ∉ E → s ∉ E →
      ∃ g ∈ Subgroup.normalizer (E : Set K) ⊓ H w, g * r * g⁻¹ * s⁻¹ ∈ E := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have : ((J (zz w)).subgroupOf (H (zz w))).Normal := J_subgroupOf_normal (zz w)
  have hIII2 : ¬ ParrottEqualityBranch (z := zz w) (D := quotientDataZZ D) (parrottHyp_zz h) :=
    fun hb => hIII ((parrottEqualityBranch_zz_iff (parrottHyp_zz h) D).mp hb)
  have h1 := transitive_on_J_sup_of_isParrottE (quotientDataZZ D) (parrottHyp_zz h) hIII2 hE
    (hweak_prod hweak)
  intro r hr s hs hrE hsE
  have hr2 : ((r, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hr, Subgroup.mem_top 1⟩
  have hs2 : ((s, 1) : D2 K) ∈ J (zz w) ⊔ E.prod (⊤ : Subgroup C2) := by
    rw [J_zz, prod_top_sup]
    exact Subgroup.mem_prod.mpr ⟨hs, Subgroup.mem_top 1⟩
  obtain ⟨⟨g, c⟩, hgm, hg⟩ := h1 _ hr2 _ hs2 (fun hh => hrE (Subgroup.mem_prod.mp hh).1)
    (fun hh => hsE (Subgroup.mem_prod.mp hh).1)
  rw [normalizer_prod_top, H_zz, prod_top_inf, Subgroup.mem_prod] at hgm
  refine ⟨g, hgm.1, ?_⟩
  have e1 : ((g, c) * (r, 1) * (g, c)⁻¹ * (s, 1)⁻¹ : D2 K) = (g * r * g⁻¹ * s⁻¹, 1) := by
    refine Prod.ext (by simp) ?_
    simp
  rw [e1, Subgroup.mem_prod] at hg
  exact hg.1

end Double

section Index

private theorem card_H_A (h : Tim79a.ParrottHypA w) :
    Nat.card (H w) = 2 ^ 9 * 51840 := by
  have h1 := card_H (parrottHyp_zz h)
  rw [H_zz, card_prod_top] at h1
  omega

theorem relIndex_inf_commutator_of_hypA
    (h : Tim79a.ParrottHypA w)
    (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hIII : ¬ ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    {E : Subgroup K} (hEH : E ≤ H w) (hEHJ : E ≤ ⁅H w, H w⁆ ⊔ J w) (hcard : Nat.card E = 2 ^ 9)
    (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920) :
    (Subgroup.normalizer (E : Set K) ⊓ ⁅H w, H w⁆).relIndex
      (Subgroup.normalizer (E : Set K) ⊓ H w) = 2 ∧ E ≤ ⁅H w, H w⁆ := by
  have hJH := J_le_commutator_of_not_equalityBranch_A h D hIII
  have hH2 := relIndex_commutator_of_not_equalityBranch_A h D hIII
  have hEH' : E ≤ ⁅H w, H w⁆ := hEHJ.trans (sup_le le_rfl hJH)
  refine ⟨?_, hEH'⟩
  have hHH' : ⁅H w, H w⁆ ≤ H w := le_sup_left.trans commutator_sup_centerIn_le_H
  have hEM : E ≤ Subgroup.normalizer (E : Set K) ⊓ H w := le_inf Subgroup.le_normalizer hEH
  have hcardM : Nat.card ↥(Subgroup.normalizer (E : Set K) ⊓ H w) = 983040 := by
    have h1 := Subgroup.relIndex_mul_card E (Subgroup.normalizer (E : Set K) ⊓ H w)
    rw [inf_eq_left.mpr hEM, hrel, hcard] at h1
    omega
  have hcardH' : Nat.card ↥(⁅H w, H w⁆ : Subgroup K) = 13271040 := by
    have h1 := Subgroup.relIndex_mul_card ⁅H w, H w⁆ (H w)
    rw [inf_eq_left.mpr hHH', hH2, card_H_A h] at h1
    omega
  have hMnot : ¬ Subgroup.normalizer (E : Set K) ⊓ H w ≤ ⁅H w, H w⁆ := by
    intro hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hcardM, hcardH'] at h1
    norm_num at h1
  have hrewrite : (Subgroup.normalizer (E : Set K) ⊓ ⁅H w, H w⁆).relIndex
      (Subgroup.normalizer (E : Set K) ⊓ H w) = (⁅H w, H w⁆).relIndex
      (Subgroup.normalizer (E : Set K) ⊓ H w) := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.normalizer (E : Set K) ⊓ ⁅H w, H w⁆)
        (Subgroup.normalizer (E : Set K) ⊓ H w),
      ← Subgroup.inf_relIndex_right ⁅H w, H w⁆ (Subgroup.normalizer (E : Set K) ⊓ H w)]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hrewrite]
  have hle2 : (⁅H w, H w⁆).relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) ≤
      (⁅H w, H w⁆).relIndex (H w) :=
    Subgroup.relIndex_le_of_le_right inf_le_right (by rw [hH2]; norm_num)
  have hne1 : (⁅H w, H w⁆).relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) ≠ 1 := fun h1 =>
    hMnot (Subgroup.relIndex_eq_one.mp h1)
  have hne0 : (⁅H w, H w⁆).relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

end Index

section Final

theorem not_equalityBranch_of_theorem1_A
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    (h : Tim79a.ParrottHypA w) (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hnot : ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤)) :
    ¬ ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂ := by
  intro hb
  have h2 := parrottHyp_zz h
  have hb2 : ParrottEqualityBranch (z := zz w) (D := quotientDataZZ D) h2 :=
    (parrottEqualityBranch_zz_iff h2 D).mpr hb
  have h3 := hThm1 (D2 K) (zz w) h2 (J_subgroupOf_normal (zz w)) (quotientDataZZ D) hb2
  exact hnot ((H_zz_sup_pPrimeCore_eq_top_iff w).mp h3)

theorem hL345_Kprime_of_lemma34
    (h : Tim79a.ParrottHypA w)
    (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hIII : ¬ ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    {E : Subgroup K} (hEH : E ≤ H w) (hEHJ : E ≤ ⁅H w, H w⁆ ⊔ J w) (hwE : w ∈ E)
    (hcard : Nat.card E = 2 ^ 9) (hcardJ : Nat.card ↥(E ⊓ J w) = 2 ^ 5)
    (hECE : E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K))
    (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920)
    (hgen : ∀ x ∈ E, x ∈ Subgroup.closure
      {y : K | ∃ n ∈ Subgroup.normalizer (E : Set K), y = n * w * n⁻¹})
    (hweak : ∀ T : Subgroup K, IsSylowOf 2 T (H w) → E ≤ T →
      ∀ g : K, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    (hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    (hfus : ∃ e ∈ E, e ≠ w ∧ ∃ n ∈ Subgroup.normalizer (E : Set K), n * w * n⁻¹ = e) :
    ∃ K' : Subgroup K, E ≤ K' ∧ K'.relIndex (Subgroup.normalizer (E : Set K)) = 2 ∧
      Subgroup.normalizer (E : Set K) ⊓ ⁅H w, H w⁆ ≤ K' ∧
      ¬ (Subgroup.normalizer (E : Set K) ⊓ H w ≤ K') ∧
      ((E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
         ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) := by
  have hw2 : w * w = 1 := by
    have h1 := pow_orderOf_eq_one w
    rwa [orderOf_z_A h, pow_two] at h1
  have hE2 : IsElemAbelian 2 E := isElemAbelian_of_generated hwE hEH hgen hw2
  have hJN := kp_J_le_normalizer h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  obtain ⟨K', hEK, hKi, hKM, hKq, -, huniq⟩ := lemma34_generic w E (J w ⊔ E)
    (Subgroup.normalizer (E : Set K) ⊓ H w) rfl hE2 le_sup_right
    (sup_le (le_inf hJN J_le_H) (le_inf Subgroup.le_normalizer hEH))
    (kp_relIndex_sup_J h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel)
    (fun r hr s hs => kp_commutator_mem h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel hr hs)
    (fun r hr => kp_mul_self_mem h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel hr)
    (kp_exists_perm_five h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel D hweak)
    (kp_transitive h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel D hIII hweak)
    (fun r hr hrE => kp_exists_commutator_eq_w h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel hr hrE)
    (fun r hr e he hc =>
      kp_commutator_eq_w_of_isConj h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel hJ hr he hc)
    (kp_odd_relIndex h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel D) hfus
  obtain ⟨hL2, hEH'⟩ := relIndex_inf_commutator_of_hypA h D hIII hEH hEHJ hcard hrel
  have hLM : Subgroup.normalizer (E : Set K) ⊓ ⁅H w, H w⁆ ≤
      Subgroup.normalizer (E : Set K) ⊓ H w :=
    inf_le_inf_left _ (le_sup_left.trans commutator_sup_centerIn_le_H)
  have hEq := huniq _ (le_inf Subgroup.le_normalizer hEH') hLM hL2
  refine ⟨K', hEK, hKi, ?_, hKM, hKq⟩
  rw [hEq]
  exact inf_le_left

end Final

end CFSG.RankThree.GF2n.Parrott
