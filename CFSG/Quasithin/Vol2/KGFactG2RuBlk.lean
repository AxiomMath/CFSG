module

public import CFSG.Quasithin.Background.C2Blocks
import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Conj

variable {G : Type*} [Group G]

theorem map_conj_eq {H : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj y).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hy h).1 hh
  · intro hx
    refine ⟨y⁻¹ * x * y, (Subgroup.mem_normalizer_iff.1 hy _).2 ?_, ?_⟩
    · simpa [mul_assoc] using hx
    · simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_of_map {H : Subgroup G} {y : G}
    (h : H.map (MulAut.conj y).toMonoidHom = H) : y ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : y * x * y⁻¹ ∈ H.map (MulAut.conj y).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨x', hx', he⟩ := hx
    have : x' = x := by
      simpa [MulAut.conj_apply] using he
    rwa [← this]

theorem map_conj_commutator (H₁ H₂ : Subgroup G) (y : G) :
    ⁅H₁, H₂⁆.map (MulAut.conj y).toMonoidHom =
      ⁅H₁.map (MulAut.conj y).toMonoidHom, H₂.map (MulAut.conj y).toMonoidHom⁆ :=
  Subgroup.map_commutator _ _ _

theorem commutator_mem_normalizer {H₁ H₂ : Subgroup G} {y : G}
    (h₁ : y ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : y ∈ Subgroup.normalizer (H₂ : Set G)) :
    y ∈ Subgroup.normalizer (((⁅H₁, H₂⁆ : Subgroup G)) : Set G) :=
  mem_normalizer_of_map (by rw [map_conj_commutator, map_conj_eq h₁, map_conj_eq h₂])

theorem inf_mem_normalizer {H₁ H₂ : Subgroup G} {y : G}
    (h₁ : y ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : y ∈ Subgroup.normalizer (H₂ : Set G)) :
    y ∈ Subgroup.normalizer (↑(H₁ ⊓ H₂) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h₁ h₂ ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h₁ x, h₂ x]

theorem sup_mem_normalizer {H₁ H₂ : Subgroup G} {y : G}
    (h₁ : y ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : y ∈ Subgroup.normalizer (H₂ : Set G)) :
    y ∈ Subgroup.normalizer (↑(H₁ ⊔ H₂) : Set G) :=
  mem_normalizer_of_map (by rw [Subgroup.map_sup, map_conj_eq h₁, map_conj_eq h₂])

theorem centralizer_mem_normalizer {H : Subgroup G} {y : G}
    (h : y ∈ Subgroup.normalizer (H : Set G)) :
    y ∈ Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h' hh'
    have h1 := hx (y⁻¹ * h' * y) ((Subgroup.mem_normalizer_iff.1 h _).2 (by
      simpa [mul_assoc] using hh'))
    calc h' * (y * x * y⁻¹) = y * (y⁻¹ * h' * y * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * h' * y)) * y⁻¹ := by rw [h1]
      _ = y * x * y⁻¹ * h' := by group
  · intro hx h' hh'
    have h1 := hx (y * h' * y⁻¹) ((Subgroup.mem_normalizer_iff.1 h _).1 hh')
    have : y * (h' * x) * y⁻¹ = y * (x * h') * y⁻¹ := by
      calc y * (h' * x) * y⁻¹ = y * h' * y⁻¹ * (y * x * y⁻¹) := by group
        _ = y * x * y⁻¹ * (y * h' * y⁻¹) := h1
        _ = y * (x * h') * y⁻¹ := by group
    simpa using this

end Conj

section Block

variable {G : Type*} [Group G] {B : Subgroup G}

theorem blockQ_le (B : Subgroup G) : blockQ B ≤ B := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem blockU_le (B : Subgroup G) : blockU B ≤ B := by
  rw [blockU, Subgroup.commutator_le]
  intro q hq b hb
  rw [commutatorElement_def]
  exact B.mul_mem (B.mul_mem (B.mul_mem (blockQ_le B hq) hb) (B.inv_mem (blockQ_le B hq)))
    (B.inv_mem hb)

theorem blockZ_le_blockU (B : Subgroup G) : blockZ B ≤ blockU B := inf_le_left

theorem blockU_le_blockQ (hB : IsShort2 B) : blockU B ≤ blockQ B := fun _ hx =>
  (hB.2.2.1.1 hx).1

theorem blockU_comm (hB : IsShort2 B) {x y : G} (hx : x ∈ blockU B) (hy : y ∈ blockU B) :
    x * y = y * x :=
  Subgroup.mem_centralizer_iff.1 (hB.2.2.1.1 hy).2 x (blockU_le_blockQ hB hx)

theorem blockU_sq (hB : IsShort2 B) {x : G} (hx : x ∈ blockU B) : x * x = 1 := by
  rw [← sq]
  exact hB.2.2.1.2 x hx

theorem normalizer_blockQ {y : G} (hy : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer (blockQ B : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B hy

theorem normalizer_blockU {y : G} (hy : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer (blockU B : Set G) :=
  commutator_mem_normalizer (normalizer_blockQ hy) hy

theorem normalizer_blockZ {y : G} (hy : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer (blockZ B : Set G) :=
  inf_mem_normalizer (normalizer_blockU hy) (centralizer_mem_normalizer hy)

theorem le_normalizer_blockU (B : Subgroup G) : B ≤ Subgroup.normalizer (blockU B : Set G) :=
  fun _ hy => normalizer_blockU (Subgroup.le_normalizer hy)

theorem le_normalizer_blockZ (B : Subgroup G) : B ≤ Subgroup.normalizer (blockZ B : Set G) :=
  fun _ hy => normalizer_blockZ (Subgroup.le_normalizer hy)

theorem blockZ_comm {z b : G} (hz : z ∈ blockZ B) (hb : b ∈ B) : z * b = b * z :=
  (Subgroup.mem_centralizer_iff.1 hz.2 b hb).symm

end Block

section Perfect

variable {G : Type} [Group G] [Finite G] {B : Subgroup G}

theorem commutator_top_eq_top {X : Type*} [Group X] [IsSimpleGroup X] {a b : X}
    (hab : a * b ≠ b * a) : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
  have hn : (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).Normal :=
    Subgroup.commutator_normal (⊤ : Subgroup X) (⊤ : Subgroup X)
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    apply hab
    have : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
      Subgroup.commutator_mem_commutator trivial trivial
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem exists_noncomm_of_card {X : Type*} [Group X] [IsSimpleGroup X] (hX : Nat.card X = 6048) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [hX]; norm_num)
  have hN : (Subgroup.zpowers g).Normal :=
    ⟨fun n hn x => by rw [h x n, mul_inv_cancel_right]; exact hn⟩
  rcases hN.eq_bot_or_eq_top with h1 | h1
  · have : g = 1 := by
      rw [← Subgroup.mem_bot, ← h1]
      exact Subgroup.mem_zpowers g
    rw [this, orderOf_one] at hg
    norm_num at hg
  · have := Nat.card_zpowers g
    rw [h1, Subgroup.card_top, hX, hg] at this
    norm_num at this

omit [Finite G] in
theorem commutator_eq_self (hB : IsG2Block B) : ⁅B, B⁆ = B := by
  obtain ⟨hS, hPSU, -⟩ := hB
  have : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) :=
    SBc11.isSimpleGroup_of_list (Or.inr (Or.inr hPSU))
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_card (SBc11.card_of_isPSU_three_three hPSU)
  have hcomm := commutator_top_eq_top hab
  set N : Subgroup ↥B := ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ with hNdef
  have hNn : N.Normal := Subgroup.commutator_normal ⊤ ⊤
  have hmap : N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) = ⊤ := by
    rw [hNdef, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hcomm
  have hsup : N ⊔ CFSG.pCore 2 ↥B = ⊤ := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥B), ← Subgroup.comap_map_eq, hmap,
      Subgroup.comap_top]
  have hP : (CFSG.pCore 2 ↥B).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : (N ⊔ CFSG.pCore 2 ↥B).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hp : IsPGroup 2 (↥B ⧸ N) := by
    have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥B).map (QuotientGroup.mk' N)) :=
      (CFSG.pCore_isPGroup).map _
    rw [hP] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have hN : N = ⊤ := hS.1 N hp
  calc ⁅B, B⁆ = (⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ : Subgroup ↥B).map B.subtype := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = B := by
        rw [← hNdef, hN, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Perfect

section Order

variable {G : Type} [Group G] {B : Subgroup G}

theorem card_eq (hB : IsG2Block B) : Nat.card B = 6048 * Nat.card (blockQ B) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  rw [SBc11.card_of_isPSU_three_three hB.2.1] at h1
  have h2 : Nat.card (blockQ B) = Nat.card (CFSG.pCore 2 ↥B) := by
    rw [blockQ, pCoreOf]
    exact Nat.card_congr ((CFSG.Open.pCore 2 ↥B).equivMapOfInjective _
      B.subtype_injective).toEquiv.symm
  rw [h2]
  exact h1

theorem card_blockU (hB : IsG2Block B) : Nat.card (blockU B) = 64 * Nat.card (blockZ B) := by
  have h := ((blockZ B).subgroupOf (blockU B)).card_mul_index
  rw [hB.2.2.1] at h
  have hc : Nat.card ((blockZ B).subgroupOf (blockU B)) = Nat.card (blockZ B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockZ_le_blockU B)).toEquiv
  rw [hc] at h
  rw [← h]
  ring

end Order

section Card

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_normal' (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

end Card

section Invariant

variable {G : Type} [Group G] [Finite G] {B W : Subgroup G}

omit [Finite G] in
theorem sup_blockZ_eq (hB : IsShort2 B) (hWU : W ≤ blockU B)
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) :
    W ⊔ blockZ B = blockZ B ∨ W ⊔ blockZ B = blockU B :=
  hB.2.2.2.2.2 _ le_sup_right (sup_le hWU (blockZ_le_blockU B))
    fun _ hy => sup_mem_normalizer (hBW hy) (le_normalizer_blockZ B hy)

omit [Finite G] in
theorem commutator_le_left (hBW : B ≤ Subgroup.normalizer (W : Set G)) : ⁅W, B⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro w hw b hb
  rw [commutatorElement_def, show w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) by group]
  exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.1 (hBW hb) _).1 (W.inv_mem hw))

theorem commutator_eq_of_inf (hB : IsG2Block B) (hWU : W ≤ blockU B)
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hWZ : W ⊓ blockZ B = ⊥)
    (hW : Nat.card W = 64) : ⁅W, B⁆ = W := by
  have hle := commutator_le_left hBW
  have hBC : B ≤ Subgroup.normalizer ((⁅W, B⁆ : Subgroup G) : Set G) := fun _ hy =>
    commutator_mem_normalizer (hBW hy) (Subgroup.le_normalizer hy)
  rcases sup_blockZ_eq hB.1 (hle.trans hWU) hBC with h | h
  · exfalso
    have hbot : ⁅W, B⁆ = ⊥ := by
      rw [eq_bot_iff, ← hWZ]
      exact le_inf hle (h ▸ le_sup_left)
    have hWZ' : W ≤ blockZ B := by
      refine le_inf hWU ?_
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
      exact hbot
    have : W = ⊥ := by
      rw [eq_bot_iff, ← hWZ]
      exact le_inf le_rfl hWZ'
    rw [this, Subgroup.card_bot] at hW
    norm_num at hW
  · have hc := Subgroup.card_le_of_le (le_of_eq h.symm)
    have hcard := card_blockU hB
    have hmul : Nat.card ↥(⁅W, B⁆ ⊔ blockZ B) * Nat.card ↥(⁅W, B⁆ ⊓ blockZ B) =
        Nat.card ↥⁅W, B⁆ * Nat.card (blockZ B) := by
      have hN : blockZ B ≤ Subgroup.normalizer ((⁅W, B⁆ : Subgroup G) : Set G) := fun _ hz =>
        hBC (blockU_le B (blockZ_le_blockU B hz))
      exact card_sup_mul_card_inf_le_normalizer hN
    have hinf : ⁅W, B⁆ ⊓ blockZ B = ⊥ := by
      rw [eq_bot_iff, ← hWZ]
      exact inf_le_inf_right _ hle
    rw [hinf, Subgroup.card_bot, mul_one] at hmul
    have hZ : 0 < Nat.card (blockZ B) := Nat.card_pos
    have h64 : 64 ≤ Nat.card ↥⁅W, B⁆ := by
      by_contra hlt
      push Not at hlt
      have : Nat.card (blockU B) < 64 * Nat.card (blockZ B) := by
        calc Nat.card (blockU B) ≤ Nat.card ↥(⁅W, B⁆ ⊔ blockZ B) := hc
          _ = Nat.card ↥⁅W, B⁆ * Nat.card (blockZ B) := hmul
          _ < 64 * Nat.card (blockZ B) := Nat.mul_lt_mul_of_pos_right hlt hZ
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hW]; exact h64)

end Invariant

end CFSG.Quasithin.H13.Ch4.G2Ru
