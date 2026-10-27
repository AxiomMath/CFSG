module

public import CFSG.Quasithin.Vol2.KGFactG2RuLift

public section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement IsMulCommutative

@[expose] def aE {M : Type*} [Monoid M] (a : ℕ → M) (e : ℕ) : M :=
  a 0 ^ (e % 2) * (a 1 ^ (e / 2 % 2) * a 2 ^ (e / 4 % 2))

structure G2RuModel {Q : Type} [Group Q] (P T W V : Subgroup Q) (x : Q) (ns : List Q)
    (a : ℕ → Q) : Prop where
  T_le : T ≤ P
  sylow : ∀ X : Subgroup Q, X ≤ P → IsPGroup 2 X →
    ∃ g ∈ P, X.map (MulAut.conj g).toMonoidHom ≤ T
  W_le : W ≤ T
  W_sq : ∀ w ∈ W, w * w = 1
  card_W : Nat.card W ≤ 64
  e64 : ∀ E : Subgroup Q, E ≤ T → (∀ e ∈ E, e * e = 1) → 64 ≤ Nat.card E →
    ∃ s ∈ T, E ≤ W.map (MulAut.conj s).toMonoidHom
  card_N : Nat.card ↥(P ⊓ Subgroup.normalizer (W : Set Q)) ≤ 774144
  V_le : V ≤ W
  card_V : Nat.card V = 8
  T_V : ∀ s ∈ T, s ∈ Subgroup.normalizer (W : Set Q) → s ∈ Subgroup.normalizer (V : Set Q)
  x_mem : x ∈ P
  x_comm : ∀ v ∈ V, x * v = v * x
  x_not : x ∉ Subgroup.normalizer (W : Set Q)
  n_mem : ∀ n ∈ ns, n ∈ P ∧ n ∈ Subgroup.normalizer (W : Set Q) ∧
    n ∈ Subgroup.normalizer (V : Set Q) ∧ n * x * n⁻¹ * x⁻¹ ∈ Subgroup.normalizer (W : Set Q)
  n_gen : V ≤ Subgroup.closure {u | ∃ v ∈ V, ∃ n ∈ ns, u = v * (n⁻¹ * v * n)}
  a_mem : ∀ i < 3, a i ∈ P ⊓ Subgroup.normalizer (W : Set Q)
  a_V : ∀ i < 3, ∀ v ∈ V, a i * v = v * a i
  a_sq : ∀ i < 3, ∀ w ∈ W, a i * a i * w * (a i * a i)⁻¹ = w
  a_comm : ∀ i < 3, ∀ j < 3, ∀ w ∈ W,
    a i * a j * w * (a i * a j)⁻¹ = a j * a i * w * (a j * a i)⁻¹
  a_ne : ∀ e < 8, ∀ e' < 8, e ≠ e' →
    ∃ w ∈ W, aE a e * w * (aE a e)⁻¹ ≠ aE a e' * w * (aE a e')⁻¹

section ConjQ

variable {Q : Type} [Group Q]

theorem mem_map_conj {X : Subgroup Q} {g y : Q} :
    y ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ X := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem map_conj_map (X : Subgroup Q) (a b : Q) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  ext y
  rw [mem_map_conj, mem_map_conj, mem_map_conj, mul_inv_rev]
  simp only [mul_assoc]

theorem card_map_conj (X : Subgroup Q) (g : Q) :
    Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
  (Nat.card_congr (X.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (by exact (MulAut.conj g).injective)).toEquiv).symm

theorem mem_normalizer_map_conj {X : Subgroup Q} {g q : Q} :
    q ∈ Subgroup.normalizer (X.map (MulAut.conj g).toMonoidHom : Set Q) ↔
      g⁻¹ * q * g ∈ Subgroup.normalizer (X : Set Q) := by
  simp only [Subgroup.mem_normalizer_iff, mem_map_conj]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    simp only [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
    rw [this]
    constructor <;> intro h' <;> simpa [mul_assoc] using h'
  · intro h y
    rw [h (g⁻¹ * y * g)]
    constructor <;> intro h' <;> simpa [mul_assoc] using h'

end ConjQ

section Steps

variable {Q : Type} [Group Q] [Finite Q] {P T W V : Subgroup Q} {x : Q} {ns : List Q}
  {a : ℕ → Q} {G : Type} [Group G] [Finite G] {K : Subgroup G} {ψ : ↥K →* Q}
  {B : Subgroup G}

omit [Finite Q] [Finite G] in
theorem img_blockU_sq (hB : IsG2Block B) {q : Q} (hq : q ∈ img ψ (blockU B)) : q * q = 1 := by
  obtain ⟨u, hu, huK, rfl⟩ := exists_of_mem_img ψ hq
  rw [← map_mul]
  have : (⟨u, huK⟩ : ↥K) * ⟨u, huK⟩ = 1 := Subtype.ext (blockU_sq hB.1 hu)
  rw [this, map_one]

omit [Finite Q] in
theorem isPGroup_of_sq {H : Subgroup Q} (h : ∀ q ∈ H, q * q = 1) : IsPGroup 2 H := by
  intro q
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_one, sq] using h q q.2

theorem exists_conj_model (hM : G2RuModel P T W V x ns a) (hrange : ψ.range = P)
    (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K) (hB : IsG2Block B) {S' : Subgroup G}
    (hS'B : S' ≤ B) (hS'2 : IsPGroup 2 S') :
    ∃ g ∈ P, (img ψ (blockU B)).map (MulAut.conj g).toMonoidHom = W ∧
      (img ψ S').map (MulAut.conj g).toMonoidHom ≤ T ∧ Nat.card (img ψ (blockU B)) = 64 := by
  set U := img ψ (blockU B) with hU
  set S₁ := img ψ S' with hS₁
  have hUP : U ≤ P := hrange ▸ img_le_range ψ _
  have hS₁P : S₁ ≤ P := hrange ▸ img_le_range ψ _
  have hU2 : IsPGroup 2 U := isPGroup_of_sq fun q hq => img_blockU_sq hB hq
  have hS₁2 : IsPGroup 2 S₁ :=
    (hS'2.comap_of_injective K.subtype K.subtype_injective).map ψ
  have hS₁U : S₁ ≤ Subgroup.normalizer (U : Set Q) := by
    intro q hq
    obtain ⟨s, hs, hsK, rfl⟩ := exists_of_mem_img ψ hq
    exact map_mem_normalizer_img (k := ⟨s, hsK⟩) (le_normalizer_blockU B (hS'B hs))
  have hsup2 := IsPGroup.to_sup_of_normal_right' hS₁2 hU2 hS₁U
  obtain ⟨h, hhP, hle⟩ := hM.sylow _ (sup_le hS₁P hUP) hsup2
  have hET : U.map (MulAut.conj h).toMonoidHom ≤ T :=
    (Subgroup.map_mono le_sup_right).trans hle
  have hE2 : ∀ e ∈ U.map (MulAut.conj h).toMonoidHom, e * e = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, img_blockU_sq hB hu, map_one]
  have hU64 : 64 ≤ Nat.card U := card_img_blockU hker hBK hB
  obtain ⟨s, hsT, hEs⟩ := hM.e64 _ hET hE2 (by rw [card_map_conj]; exact hU64)
  refine ⟨s⁻¹ * h, P.mul_mem (P.inv_mem (hM.T_le hsT)) hhP, ?_, ?_, ?_⟩
  · have hle' : U.map (MulAut.conj (s⁻¹ * h)).toMonoidHom ≤ W := by
      rw [← map_conj_map]
      intro y hy
      have := Subgroup.map_mono hEs hy
      rw [map_conj_map, inv_mul_cancel] at this
      simpa using this
    refine Subgroup.eq_of_le_of_card_ge hle' ?_
    rw [card_map_conj]
    exact hM.card_W.trans hU64
  · rw [← map_conj_map]
    intro y hy
    rw [mem_map_conj, inv_inv] at hy
    have h1 : s * y * s⁻¹ ∈ T := hle (Subgroup.map_mono le_sup_left hy)
    have : y = s⁻¹ * (s * y * s⁻¹) * s := by group
    rw [this]
    exact T.mul_mem (T.mul_mem (T.inv_mem hsT) h1) hsT
  · have hle'' : Nat.card U ≤ 64 := by
      have := Subgroup.card_le_of_le hEs
      rw [card_map_conj, card_map_conj] at this
      exact this.trans hM.card_W
    omega

omit [Finite Q] in
theorem blockU_inf_zK_eq (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K) (hB : IsG2Block B)
    (h64 : Nat.card (img ψ (blockU B)) = 64) : blockU B ⊓ zK K = blockZ B := by
  have h1 := card_img_mul hker ((blockU_le B).trans hBK)
  rw [h64, card_blockU hB] at h1
  refine Subgroup.eq_of_le_of_card_ge (blockU_inf_zK_le hBK) ?_
  omega

theorem normal_model (hM : G2RuModel P T W V x ns a) (hrange : ψ.range = P)
    (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K) (hB : IsG2Block B) {g : Q} (hgP : g ∈ P)
    (hgU : (img ψ (blockU B)).map (MulAut.conj g).toMonoidHom = W) {q : Q}
    (hq : q ∈ P ⊓ Subgroup.normalizer (W : Set Q)) :
    q ∈ Subgroup.normalizer ((img ψ B).map (MulAut.conj g).toMonoidHom : Set Q) := by
  set H := (img ψ B).map (MulAut.conj g).toMonoidHom with hH
  set N := P ⊓ Subgroup.normalizer (W : Set Q) with hN
  have hHN : H ≤ N := by
    intro y hy
    rw [hH, mem_map_conj] at hy
    obtain ⟨b, hb, hbK, he⟩ := exists_of_mem_img ψ hy
    have hbP : ψ ⟨b, hbK⟩ ∈ P := hrange ▸ ⟨_, rfl⟩
    have hyP : y = g * ψ ⟨b, hbK⟩ * g⁻¹ := by rw [he]; group
    refine Subgroup.mem_inf.2 ⟨hyP ▸ P.mul_mem (P.mul_mem hgP hbP) (P.inv_mem hgP), ?_⟩
    rw [← hgU, mem_normalizer_map_conj, hyP, show g⁻¹ * (g * ψ ⟨b, hbK⟩ * g⁻¹) * g =
      ψ ⟨b, hbK⟩ by group]
    exact map_mem_normalizer_img (k := ⟨b, hbK⟩) (le_normalizer_blockU B hb)
  set H' := H.subgroupOf N with hH'
  have hcH' : Nat.card H' = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
  have hcH : 387072 ≤ Nat.card H := by
    rw [hH, card_map_conj]
    exact card_img_block hker hBK hB
  have hidx : H'.index ≤ 2 := by
    have h1 := H'.card_mul_index
    have h2 : Nat.card N ≤ 774144 := hM.card_N
    have hpos : 0 < Nat.card H' := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card H' * 3 ≤ Nat.card H' * H'.index := Nat.mul_le_mul_left _ hlt
    rw [h1] at this
    omega
  have hnorm : H'.Normal := by
    have hpos : 0 < H'.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases (by omega : H'.index = 1 ∨ H'.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := hnorm.conj_mem ⟨y, hHN hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨q, hq⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro hy
    have hqN : q⁻¹ ∈ N := N.inv_mem hq
    have := hnorm.conj_mem ⟨q * y * q⁻¹, hHN hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨q⁻¹, hqN⟩
    have h2 := Subgroup.mem_subgroupOf.1 this
    simpa [mul_assoc] using h2

theorem lift_model (hM : G2RuModel P T W V x ns a) (hrange : ψ.range = P)
    (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K) (hB : IsG2Block B) {g : Q} (hgP : g ∈ P)
    (hgU : (img ψ (blockU B)).map (MulAut.conj g).toMonoidHom = W) {q : Q}
    (hq : q ∈ P ⊓ Subgroup.normalizer (W : Set Q)) {k : ↥K} (hk : ψ k = g⁻¹ * q * g) :
    (k : G) ∈ Subgroup.normalizer (B : Set G) ∧
      ψ k ∈ Subgroup.normalizer (img ψ (blockU B) : Set Q) := by
  refine ⟨lift_normalizer_block hker hBK (commutator_eq_self hB) ?_, ?_⟩
  · rw [hk, ← mem_normalizer_map_conj]
    exact normal_model hM hrange hker hBK hB hgP hgU hq
  · rw [hk, ← mem_normalizer_map_conj, hgU]
    exact hq.2

omit [Finite Q] [Finite G] in
theorem exists_preimage (hrange : ψ.range = P) {q : Q} (hq : q ∈ P) : ∃ k : ↥K, ψ k = q := by
  rw [← hrange] at hq
  exact hq

end Steps

end CFSG.Quasithin.H13.Ch4.G2Ru
