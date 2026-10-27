module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSNormA
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

section TypeA

variable {E : Type*} [Group E]

structure VertexA (A Q : Subgroup E) : Prop where
  le : Q ≤ A
  normal : ∀ g ∈ A, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  card_A : Nat.card A = 24
  card_Q : Nat.card Q = 4
  exp : ∀ q ∈ Q, q * q = 1
  cent : ∀ g ∈ A, (∀ q ∈ Q, g * q = q * g) → g ∈ Q

theorem VertexA.exists_iso {A Q : Subgroup E} (h : VertexA A Q) :
    ∃ ψ : ↥A ≃* Perm (Fin 4), ∀ (x : E) (hx : x ∈ A), x ∈ Q ↔ ψ ⟨x, hx⟩ ∈ V4 := by
  classical
  have _ : Finite A := Nat.finite_of_card_ne_zero (by rw [h.card_A]; norm_num)
  let Q' : Subgroup ↥A := Q.subgroupOf A
  have hnorm : Q'.Normal := ⟨fun n hn g => by
    have := h.normal g.1 g.2 n.1 hn
    exact this⟩
  have hQ' : Nat.card Q' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, h.card_Q]
  have hQe : ∀ q ∈ Q', q * q = 1 := fun q hq => Subtype.ext (h.exp q.1 hq)
  have hC : ∀ g : ↥A, (∀ q ∈ Q', g * q = q * g) → g ∈ Q' := by
    intro g hg
    refine h.cent g.1 g.2 fun q hq => ?_
    have := hg ⟨q, h.le hq⟩ hq
    exact congrArg Subtype.val this
  obtain ⟨ψ, hψ⟩ := vertex_four Q' hQ' hQe hC h.card_A
  refine ⟨ψ, fun x hx => ⟨fun hxQ => hψ ⟨x, hx⟩ hxQ, fun hxV => ?_⟩⟩
  have hle : Q'.map ψ.toMonoidHom ≤ V4 := by
    rintro _ ⟨q, hq, rfl⟩
    exact hψ q hq
  have hcard : Nat.card V4 ≤ Nat.card (Q'.map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective, hQ', card_V4]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hmem : ψ ⟨x, hx⟩ ∈ Q'.map ψ.toMonoidHom := by rw [heq]; exact hxV
  obtain ⟨q, hq, hqx⟩ := hmem
  have hqeq : q = ⟨x, hx⟩ := ψ.injective hqx
  have hq' : (⟨x, hx⟩ : ↥A) ∈ Q' := hqeq ▸ hq
  exact hq'

abbrev TypeA (A₁ A₂ : Subgroup E) : Prop :=
  ∃ Q₁ Q₂ : Subgroup E, VertexA A₁ Q₁ ∧ VertexA A₂ Q₂ ∧ Q₁ ≤ A₂ ∧ Q₁ ≠ Q₂ ∧
    Nat.card ↥(A₁ ⊓ A₂) = 8

theorem TypeA.normA {A₁ A₂ : Subgroup E} (h : TypeA A₁ A₂) : Nonempty (NormA A₁ A₂) := by
  obtain ⟨Q₁, Q₂, V₁, V₂, hQ₁A₂, hne, hT⟩ := h
  obtain ⟨ψ₁, hψ₁⟩ := V₁.exists_iso
  obtain ⟨ψ₂, hψ₂⟩ := V₂.exists_iso
  have hnle : ¬ Q₁ ≤ Q₂ := by
    intro hle
    apply hne
    have : Finite Q₂ := Nat.finite_of_card_ne_zero (by rw [V₂.card_Q]; norm_num)
    apply Subgroup.eq_of_le_of_card_ge (H := Q₁) (K := Q₂) hle
    rw [V₁.card_Q, V₂.card_Q]
  obtain ⟨y, hyQ₁, hyQ₂⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hy₁ : y ∈ A₁ := V₁.le hyQ₁
  have hy₂ : y ∈ A₂ := hQ₁A₂ hyQ₁
  have hout : ∃ (y : E) (h₁ : y ∈ A₁) (h₂ : y ∈ A₂), ψ₁ ⟨y, h₁⟩ ∈ V4 ∧ ψ₂ ⟨y, h₂⟩ ∉ V4 :=
    ⟨y, hy₁, hy₂, (hψ₁ y hy₁).1 hyQ₁, fun hv => hyQ₂ ((hψ₂ y hy₂).2 hv)⟩
  obtain ⟨a, b, ha₁, ha₂, hb₁, hb₂, ψ₁', ψ₂', h₁a, h₁b, h₂a, h₂b, hw⟩ :=
    normalize_A A₁ A₂ hT ψ₁ ψ₂ hout
  exact ⟨⟨a, b, ha₁, ha₂, hb₁, hb₂, ψ₁', ψ₂', h₁a, h₁b, h₂a, h₂b, hw⟩⟩

theorem TypeA.isAmalgamIso {E' : Type*} [Group E'] {A₁ A₂ : Subgroup E} {B₁ B₂ : Subgroup E'}
    (h : TypeA A₁ A₂) (h' : TypeA B₁ B₂) : CFSG.Quasithin.F6.IsAmalgamIso A₁ A₂ B₁ B₂ := by
  obtain ⟨N⟩ := h.normA
  obtain ⟨N'⟩ := h'.normA
  exact N.isAmalgamIso N'

end TypeA

section VertexMk

variable {E : Type*} [Group E]

theorem VertexA.mk' {A : Subgroup E} (Q' : Subgroup ↥A) [Q'.Normal] (hA : Nat.card ↥A = 24)
    (hQ : Nat.card Q' = 4) (hexp : ∀ q ∈ Q', q * q = 1)
    (hC : ∀ g : ↥A, (∀ q ∈ Q', g * q = q * g) → g ∈ Q') :
    VertexA A (Q'.map A.subtype) where
  le := Subgroup.map_subtype_le Q'
  normal := fun g hg q hq => by
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨⟨g, hg⟩ * q' * ⟨g, hg⟩⁻¹, (inferInstance : Q'.Normal).conj_mem q' hq' ⟨g, hg⟩, rfl⟩
  card_A := hA
  card_Q := by rw [Subgroup.card_map_of_injective A.subtype_injective]; exact hQ
  exp := fun q hq => by
    obtain ⟨q', hq', rfl⟩ := hq
    exact congrArg Subtype.val (hexp q' hq')
  cent := fun g hg hgc => by
    refine ⟨⟨g, hg⟩, hC ⟨g, hg⟩ (fun q hq => ?_), rfl⟩
    exact Subtype.ext (hgc q.1 ⟨q, hq, rfl⟩)

end VertexMk

section DSide

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {E : Type*} [Group E] [Finite E] {A₁ A₂ : Subgroup E}

omit [Finite E] in
theorem charTwo_cent {X : Subgroup E} (h : CharTwo X) :
    ∀ g : ↥X, (∀ q ∈ CFSG.Open.pCore 2 ↥X, g * q = q * g) → g ∈ CFSG.Open.pCore 2 ↥X := by
  intro g hg
  have hmem : (g : E) ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set E) := by
    refine ⟨g.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro e ⟨p, hp, rfl⟩
    exact (congrArg Subtype.val (hg p hp)).symm
  obtain ⟨p, hp, hpg⟩ := h hmem
  have : p = g := Subtype.ext hpg
  rwa [← this]

theorem card_vertex_left (h : IsGoldschmidtTriple A₁ A₂) :
    Nat.card ↥A₁ = 3 * Nat.card ↥(A₁ ⊓ A₂) := by
  have h1 := Subgroup.relIndex_mul_card (A₁ ⊓ A₂) A₁
  rw [h.relIndex_inf_left, inf_eq_left.2 (inf_le_left : A₁ ⊓ A₂ ≤ A₁)] at h1
  exact h1.symm

omit [Finite E] in
theorem card_pCore_mul_six (h : IsGoldschmidtTriple A₁ A₂) :
    Nat.card (CFSG.Open.pCore 2 ↥A₁) * 6 = Nat.card ↥A₁ := by
  obtain ⟨e⟩ := h.quotient₁
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥A₁)
  rw [Nat.card_congr e.toEquiv, gold_card_perm_fin_three] at h1
  rw [h1]; ring

theorem pCore_le_inf (h : IsGoldschmidtTriple A₁ A₂) :
    ∀ q ∈ CFSG.Open.pCore 2 ↥A₁, (q : E) ∈ A₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := h.sylow
  have hTle : (T : Subgroup E) ≤ A₁ := hT ▸ inf_le_left
  intro q hq
  have h1 := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥A₁) 2).le_sylow_of_normal
    (T.subtype hTle) hq
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, hT] at h1
  exact h1.2

theorem pCoreOf_ne (h : IsGoldschmidtAmalgam A₁ A₂)
    (hne : Nat.card (CFSG.Open.pCore 2 ↥A₁) ≠ 1) : pCoreOf 2 A₁ ≠ pCoreOf 2 A₂ := by
  intro heq
  have hle : pCoreOf 2 A₁ ≤ A₁ ⊓ A₂ := by
    rintro x ⟨q, hq, rfl⟩
    exact ⟨q.2, pCore_le_inf h.toIsGoldschmidtTriple q hq⟩
  have hn₁ : A₁ ≤ Subgroup.normalizer (pCoreOf 2 A₁ : Set E) := le_normalizer_pCoreOf 2 A₁
  have hn₂ : A₂ ≤ Subgroup.normalizer (pCoreOf 2 A₁ : Set E) := heq ▸ le_normalizer_pCoreOf 2 A₂
  have htop : ∀ g : E, g ∈ Subgroup.normalizer (pCoreOf 2 A₁ : Set E) := fun g =>
    sup_le hn₁ hn₂ (h.gen ▸ Subgroup.mem_top g)
  have hnormal : (pCoreOf 2 A₁).Normal :=
    ⟨fun n hn g => ((Subgroup.mem_normalizer_iff.1 (htop g)) n).1 hn⟩
  have h2 : pCoreOf 2 A₁ ≤ CFSG.Open.pCore 2 E :=
    h.toIsGoldschmidtTriple.le_pCore_of_normal_le_inf hle
  rw [h.pCore_eq_bot, le_bot_iff] at h2
  apply hne
  have h3 : Nat.card (pCoreOf 2 A₁) = 1 := Subgroup.card_eq_one.2 h2
  unfold pCoreOf at h3
  rwa [Subgroup.card_map_of_injective A₁.subtype_injective] at h3

theorem typeA_of_amalgam (h : IsGoldschmidtAmalgam A₁ A₂) (c₁ : CharTwo A₁) (c₂ : CharTwo A₂)
    (hT : Nat.card ↥(A₁ ⊓ A₂) = 8) : TypeA A₁ A₂ := by
  have hcard : ∀ {B₁ B₂ : Subgroup E}, IsGoldschmidtTriple B₁ B₂ → Nat.card ↥(B₁ ⊓ B₂) = 8 →
      Nat.card ↥B₁ = 24 ∧ Nat.card (CFSG.Open.pCore 2 ↥B₁) = 4 := by
    intro B₁ B₂ hB hT
    have h24 : Nat.card ↥B₁ = 24 := by rw [card_vertex_left hB, hT]
    have h6 := card_pCore_mul_six hB
    refine ⟨h24, ?_⟩
    omega
  have hvertex : ∀ {B₁ B₂ : Subgroup E}, IsGoldschmidtTriple B₁ B₂ → CharTwo B₁ →
      Nat.card ↥(B₁ ⊓ B₂) = 8 → VertexA B₁ (pCoreOf 2 B₁) := by
    intro B₁ B₂ hB cB hT
    obtain ⟨h24, hQ4⟩ := hcard hB hT
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : (CFSG.Open.pCore 2 ↥B₁).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have : Finite ↥B₁ := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
    have hC := charTwo_cent cB
    have hexp := exp_two_of_card_four (CFSG.Open.pCore 2 ↥B₁) hQ4 (by rw [h24]; norm_num) hC
    exact VertexA.mk' (CFSG.Open.pCore 2 ↥B₁) h24 hQ4 hexp hC
  have hT₂ : Nat.card ↥(A₂ ⊓ A₁) = 8 := by rw [inf_comm]; exact hT
  obtain ⟨_, hQ4⟩ := hcard h.toIsGoldschmidtTriple hT
  refine ⟨pCoreOf 2 A₁, pCoreOf 2 A₂, hvertex h.toIsGoldschmidtTriple c₁ hT,
    hvertex h.toIsGoldschmidtTriple.symm c₂ hT₂, ?_, pCoreOf_ne h (by rw [hQ4]; norm_num), hT⟩
  rintro x ⟨q, hq, rfl⟩
  exact pCore_le_inf h.toIsGoldschmidtTriple q hq

end DSide

end CFSG.Quasithin.F6.GoldAmS
