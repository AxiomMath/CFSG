module

public import CFSG.Quasithin.Vol2.KGFactG2RuBlk

public section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G Q : Type} [Group G] [Group Q] {K : Subgroup G} (ψ : ↥K →* Q)

@[expose] def img (X : Subgroup G) : Subgroup Q := (X.subgroupOf K).map ψ

theorem mem_img_of_mem {X : Subgroup G} {x : G} (hx : x ∈ X) (hxK : x ∈ K) :
    ψ ⟨x, hxK⟩ ∈ img ψ X :=
  ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem exists_of_mem_img {X : Subgroup G} {q : Q} (hq : q ∈ img ψ X) :
    ∃ x ∈ X, ∃ hx : x ∈ K, ψ ⟨x, hx⟩ = q := by
  obtain ⟨⟨x, hxK⟩, hx, rfl⟩ := hq
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, hxK, rfl⟩

theorem img_mono {X Y : Subgroup G} (h : X ≤ Y) : img ψ X ≤ img ψ Y :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem img_le_range (X : Subgroup G) : img ψ X ≤ ψ.range := Subgroup.map_le_range _ _

@[expose] def zK (K : Subgroup G) : Subgroup G := (Subgroup.center ↥K).map K.subtype

theorem mem_zK {K : Subgroup G} {z : G} :
    z ∈ zK K ↔ ∃ hz : z ∈ K, (⟨z, hz⟩ : ↥K) ∈ Subgroup.center ↥K := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hz, h⟩
    exact ⟨_, h, rfl⟩

theorem zK_le (K : Subgroup G) : zK K ≤ K := fun _ hz => (mem_zK.1 hz).1

theorem zK_comm {K : Subgroup G} {z k : G} (hz : z ∈ zK K) (hk : k ∈ K) : z * k = k * z := by
  obtain ⟨hzK, hc⟩ := mem_zK.1 hz
  have := Subgroup.mem_center_iff.1 hc ⟨k, hk⟩
  exact (congrArg Subtype.val this).symm

variable {ψ}

theorem mem_zK_of_ker (hker : ψ.ker = Subgroup.center ↥K) {k : ↥K} (hk : ψ k = 1) :
    (k : G) ∈ zK K :=
  mem_zK.2 ⟨k.2, by rw [← hker]; exact hk⟩

theorem ker_of_mem_zK (hker : ψ.ker = Subgroup.center ↥K) {k : ↥K} (hk : (k : G) ∈ zK K) :
    ψ k = 1 := by
  obtain ⟨hz, hc⟩ := mem_zK.1 hk
  rw [← MonoidHom.mem_ker, hker]
  exact hc

theorem mem_zK_of_eq (hker : ψ.ker = Subgroup.center ↥K) {a b : ↥K} (h : ψ a = ψ b) :
    (a : G)⁻¹ * b ∈ zK K := by
  have : ψ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  exact mem_zK_of_ker hker this

theorem card_img_mul [Finite G] (hker : ψ.ker = Subgroup.center ↥K) {X : Subgroup G}
    (hXK : X ≤ K) : Nat.card (img ψ X) * Nat.card ↥(X ⊓ zK K) = Nat.card X := by
  set f : ↥X →* Q := ψ.comp (Subgroup.inclusion hXK) with hf
  have hrange : f.range = img ψ X := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_img_of_mem ψ x.2 (hXK x.2)
    · intro hq
      obtain ⟨x, hx, hxK, rfl⟩ := exists_of_mem_img ψ hq
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker' : f.ker = (zK K).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact mem_zK_of_ker hker h
    · intro h
      exact ker_of_mem_zK hker (k := Subgroup.inclusion hXK x) h
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker'] at h1
  have h2 : Nat.card ((zK K).subgroupOf X) = Nat.card ↥(X ⊓ zK K) := by
    rw [← Subgroup.inf_subgroupOf_left (zK K) X]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, mul_comm] at h1
  exact h1

theorem card_img_of_inf [Finite G] (hker : ψ.ker = Subgroup.center ↥K) {X : Subgroup G}
    (hXK : X ≤ K) (h : X ⊓ zK K = ⊥) : Nat.card (img ψ X) = Nat.card X := by
  have := card_img_mul hker hXK
  rwa [h, Subgroup.card_bot, mul_one] at this

theorem eq_of_img_eq (hker : ψ.ker = Subgroup.center ↥K) {X : Subgroup G} (h : X ⊓ zK K = ⊥)
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) (haK : a ∈ K) (hbK : b ∈ K)
    (hab : ψ ⟨a, haK⟩ = ψ ⟨b, hbK⟩) : a = b := by
  have h1 := mem_zK_of_eq hker hab
  have h2 : a⁻¹ * b ∈ X ⊓ zK K := ⟨X.mul_mem (X.inv_mem ha) hb, h1⟩
  rw [h, Subgroup.mem_bot] at h2
  calc a = a * (a⁻¹ * b) := by rw [h2, mul_one]
    _ = b := by group

theorem map_mem_normalizer_img {X : Subgroup G} {k : ↥K}
    (hk : (k : G) ∈ Subgroup.normalizer (X : Set G)) :
    ψ k ∈ Subgroup.normalizer (img ψ X : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    obtain ⟨y, hy, hyK, rfl⟩ := exists_of_mem_img ψ hq
    have hm := mem_img_of_mem ψ ((Subgroup.mem_normalizer_iff.1 hk y).1 hy)
      (K.mul_mem (K.mul_mem k.2 hyK) (K.inv_mem k.2))
    convert hm using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · intro hq
    obtain ⟨y, hy, hyK, he⟩ := exists_of_mem_img ψ hq
    have hy' : (k : G)⁻¹ * y * k ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 hk ((k : G)⁻¹ * y * k)).2 (by
        simpa [mul_assoc] using hy)
      exact this
    have hm := mem_img_of_mem ψ hy' (K.mul_mem (K.mul_mem (K.inv_mem k.2) hyK) k.2)
    convert hm using 1
    have : q = (ψ k)⁻¹ * ψ ⟨y, hyK⟩ * ψ k := by rw [he]; group
    rw [this, ← map_inv, ← map_mul, ← map_mul]
    rfl

variable {B : Subgroup G}

theorem blockU_inf_zK_le (hBK : B ≤ K) : blockU B ⊓ zK K ≤ blockZ B := fun _ hz =>
  ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun _ hb => (zK_comm hz.2 (hBK hb)).symm⟩

theorem inf_zK_le_blockQ (hBK : B ≤ K) (hB : IsShort2 B) : B ⊓ zK K ≤ blockQ B := fun _ hz =>
  hB.2.1 ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun _ hq =>
    (zK_comm hz.2 (hBK (blockQ_le B hq))).symm⟩

theorem card_img_blockU [Finite G] (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K)
    (hB : IsG2Block B) : 64 ≤ Nat.card (img ψ (blockU B)) := by
  have h1 := card_img_mul hker ((blockU_le B).trans hBK)
  have h2 := card_blockU hB
  have h3 : Nat.card ↥(blockU B ⊓ zK K) ≤ Nat.card (blockZ B) :=
    Subgroup.card_le_of_le (blockU_inf_zK_le hBK)
  have h4 : 0 < Nat.card ↥(blockU B ⊓ zK K) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card (img ψ (blockU B)) * Nat.card ↥(blockU B ⊓ zK K) <
      64 * Nat.card (blockZ B) :=
    calc Nat.card (img ψ (blockU B)) * Nat.card ↥(blockU B ⊓ zK K) <
          64 * Nat.card ↥(blockU B ⊓ zK K) := Nat.mul_lt_mul_of_pos_right hlt h4
      _ ≤ 64 * Nat.card (blockZ B) := Nat.mul_le_mul_left _ h3
  omega

theorem card_img_block [Finite G] (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K)
    (hB : IsG2Block B) : 387072 ≤ Nat.card (img ψ B) := by
  have h1 := card_img_mul hker hBK
  have h2 := card_eq hB
  have hU := card_blockU hB
  set D := B ⊓ zK K with hD
  have hDN : D ≤ Subgroup.normalizer (blockU B : Set G) := fun z hz =>
    le_normalizer_blockU B hz.1
  have hsup := card_sup_mul_card_inf_le_normalizer hDN
  have hle : blockU B ⊔ D ≤ blockQ B := sup_le (blockU_le_blockQ hB.1) (inf_zK_le_blockQ hBK hB.1)
  have hinf : Nat.card ↥(blockU B ⊓ D) ≤ Nat.card (blockZ B) := Subgroup.card_le_of_le
    (le_trans (inf_le_inf_left _ inf_le_right) (blockU_inf_zK_le hBK))
  have hQ := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card ↥(blockU B ⊓ D) := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have h64 : 64 * Nat.card D ≤ Nat.card (blockQ B) := by
    have e1 : Nat.card (blockU B) * Nat.card D ≤
        Nat.card (blockQ B) * Nat.card (blockZ B) := by
      rw [← hsup]
      exact Nat.mul_le_mul hQ hinf
    rw [hU] at e1
    have hZ : 0 < Nat.card (blockZ B) := Nat.card_pos
    have : 64 * Nat.card D * Nat.card (blockZ B) ≤ Nat.card (blockQ B) * Nat.card (blockZ B) := by
      calc 64 * Nat.card D * Nat.card (blockZ B) = 64 * Nat.card (blockZ B) * Nat.card D := by
            ring
        _ ≤ _ := e1
    exact Nat.le_of_mul_le_mul_right this hZ
  have : 387072 * Nat.card D ≤ Nat.card (img ψ B) * Nat.card D := by
    rw [h1, h2]
    calc 387072 * Nat.card D = 6048 * (64 * Nat.card D) := by ring
      _ ≤ 6048 * Nat.card (blockQ B) := Nat.mul_le_mul_left _ h64
  exact Nat.le_of_mul_le_mul_right this hDpos

theorem lift_normalizer_block [Finite G] (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K)
    (hperf : ⁅B, B⁆ = B) {k : ↥K}
    (hk : ψ k ∈ Subgroup.normalizer (img ψ B : Set Q)) :
    (k : G) ∈ Subgroup.normalizer (B : Set G) := by
  have hdec : ∀ b ∈ B, ∃ c ∈ B, ∃ z ∈ zK K, (k : G) * b * (k : G)⁻¹ = c * z := by
    intro b hb
    have hm : ψ (k * ⟨b, hBK hb⟩ * k⁻¹) ∈ img ψ B := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hk _).1 (mem_img_of_mem ψ hb (hBK hb))
    obtain ⟨c, hc, hcK, he⟩ := exists_of_mem_img ψ hm
    refine ⟨c, hc, _, mem_zK_of_eq hker he, ?_⟩
    simp
  set B' := B.map (MulAut.conj (k : G)).toMonoidHom with hB'
  have hle : B' ≤ B := by
    have hB'perf : ⁅B', B'⁆ = B' := by
      rw [hB', ← map_conj_commutator, hperf]
    rw [← hB'perf, Subgroup.commutator_le]
    rintro _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩
    obtain ⟨c₁, hc₁, z₁, hz₁, e₁⟩ := hdec b₁ hb₁
    obtain ⟨c₂, hc₂, z₂, hz₂, e₂⟩ := hdec b₂ hb₂
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e₁, e₂]
    have h1 : ⁅c₁ * z₁, c₂ * z₂⁆ = ⁅c₁, c₂⁆ := by
      have hz₁c₂ := zK_comm hz₁ (hBK hc₂)
      have hz₂c₁ := zK_comm hz₂ (hBK hc₁)
      have hz₁z₂ := zK_comm hz₁ (zK_le K hz₂)
      rw [commutatorElement_def, commutatorElement_def]
      calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
            c₁ * (z₁ * c₂) * (z₂ * z₁⁻¹) * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * (c₂ * z₁) * (z₁⁻¹ * z₂) * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by
            rw [hz₁c₂, show z₂ * z₁⁻¹ = z₁⁻¹ * z₂ by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hz₁z₂, inv_mul_cancel_left]]
        _ = c₁ * c₂ * (z₂ * c₁⁻¹) * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * c₂ * (c₁⁻¹ * z₂) * z₂⁻¹ * c₂⁻¹ := by
            rw [show z₂ * c₁⁻¹ = c₁⁻¹ * z₂ by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, hz₂c₁, inv_mul_cancel_left]]
        _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by group
    rw [h1]
    exact hperf ▸ Subgroup.commutator_mem_commutator hc₁ hc₂
  have hcard : Nat.card B ≤ Nat.card B' := by
    rw [hB']
    exact (Nat.card_congr (B.equivMapOfInjective (MulAut.conj (k : G)).toMonoidHom
      (by exact (MulAut.conj (k : G)).injective)).toEquiv).le
  exact mem_normalizer_of_map (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem lift_normalizer_W [Finite G] (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K)
    {W : Subgroup G} (hWU : W ≤ blockU B) (hBW : B ≤ Subgroup.normalizer (W : Set G))
    (hWB : ⁅W, B⁆ = W) {k : ↥K} (hkB : (k : G) ∈ Subgroup.normalizer (B : Set G))
    (hk : ψ k ∈ Subgroup.normalizer (img ψ W : Set Q)) :
    (k : G) ∈ Subgroup.normalizer (W : Set G) := by
  have hWK : W ≤ K := hWU.trans ((blockU_le B).trans hBK)
  have hdec : ∀ w ∈ W, ∃ w₁ ∈ W, ∃ z ∈ blockZ B, (k : G) * w * (k : G)⁻¹ = w₁ * z := by
    intro w hw
    have hm : ψ (k * ⟨w, hWK hw⟩ * k⁻¹) ∈ img ψ W := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hk _).1 (mem_img_of_mem ψ hw (hWK hw))
    obtain ⟨w₁, hw₁, hw₁K, he⟩ := exists_of_mem_img ψ hm
    have hz := mem_zK_of_eq hker he
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hz
    have hkU : (k : G) * w * (k : G)⁻¹ ∈ blockU B :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_blockU hkB) w).1 (hWU hw)
    refine ⟨w₁, hw₁, w₁⁻¹ * ((k : G) * w * (k : G)⁻¹), blockU_inf_zK_le hBK ⟨?_, hz⟩, ?_⟩
    · exact (blockU B).mul_mem ((blockU B).inv_mem (hWU hw₁)) hkU
    · group
  set W' := W.map (MulAut.conj (k : G)).toMonoidHom with hW'
  have hW'B : ⁅W', B⁆ = W' := by
    rw [hW', ← map_conj_eq hkB, ← map_conj_commutator, hWB]
  have hle : W' ≤ W := by
    rw [← hW'B, Subgroup.commutator_le]
    rintro _ ⟨w, hw, rfl⟩ b hb
    obtain ⟨w₁, hw₁, z, hz, e⟩ := hdec w hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e]
    have hzb : z * b = b * z := blockZ_comm hz hb
    have h1 : ⁅w₁ * z, b⁆ = ⁅w₁, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc w₁ * z * b * (w₁ * z)⁻¹ * b⁻¹ = w₁ * (z * b) * z⁻¹ * w₁⁻¹ * b⁻¹ := by group
        _ = w₁ * (b * z) * z⁻¹ * w₁⁻¹ * b⁻¹ := by rw [hzb]
        _ = w₁ * b * w₁⁻¹ * b⁻¹ := by group
    rw [h1]
    exact commutator_le_left hBW (Subgroup.commutator_mem_commutator hw₁ hb)
  have hcard : Nat.card W ≤ Nat.card W' := by
    rw [hW']
    exact (Nat.card_congr (W.equivMapOfInjective (MulAut.conj (k : G)).toMonoidHom
      (by exact (MulAut.conj (k : G)).injective)).toEquiv).le
  exact mem_normalizer_of_map (Subgroup.eq_of_le_of_card_ge hle hcard)

end CFSG.Quasithin.H13.Ch4.G2Ru
