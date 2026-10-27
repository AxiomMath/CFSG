module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2Aut
public import CFSG.RankThree.PartOne.S12.Sec1511Y2W
public import CFSG.RankThree.PartOne.S12.Sec1511Y1

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

variable {G : Type} [Group G]

theorem omegaOne_map_of_injective {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    (p : ℕ) (K : Subgroup G) : omegaOne p (K.map f) = (omegaOne p K).map f := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, hf (by rw [map_pow, hy, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, hxp, map_one]⟩

theorem omegaOne_le (p : ℕ) (K : Subgroup G) : omegaOne p K ≤ K :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem omegaOne_subgroupOf (p : ℕ) {K Y' : Subgroup G} (hK : K ≤ Y') :
    omegaOne p (K.subgroupOf Y') = (omegaOne p K).subgroupOf Y' := by
  apply Subgroup.map_injective Y'.subtype_injective
  rw [← omegaOne_map_of_injective Y'.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hK,
    Subgroup.map_subgroupOf_eq_of_le ((omegaOne_le p K).trans hK)]

theorem y2Cfg_of_y1Out [Finite G] {p : ℕ} {E N Y' P : Subgroup G} (hS : Setting p E N)
    (hp5 : 5 ≤ p) (hY1 : Y1Out p E N Y' P) :
    Y2Cfg p ((N ⊓ Y').subgroupOf Y') (P.subgroupOf Y') ((P ⊓ E).subgroupOf Y') := by
  have hp := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPY : P ≤ Y' := hY1.syl.1
  have hBY : P ⊓ E ≤ Y' := inf_le_left.trans hPY
  refine ⟨hp, hp5, ?_, ?_, ?_, ?_, hY1.spe, ?_⟩
  · refine ⟨le_top, hY1.syl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm, ?_⟩
    rw [Subgroup.relIndex_top_right]
    simpa [Subgroup.relIndex] using hY1.syl.2.2
  · rw [omegaOne_subgroupOf p hPY, hY1.omega]
  · have := hS.Eel
    have h1 : IsElementaryAbelian p ↥(P ⊓ E) := elemAbelian_of_le hS.Eel inf_le_right
    exact IsElementaryAbelian.subgroupOf hBY
  · have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv
    rw [this]
    exact hY1.card
  · intro V hVn hVp
    have hV1 : V.map Y'.subtype ≤ Y' := Subgroup.map_subtype_le V
    have hV2 : ∀ y ∈ Y', ∀ v ∈ V.map Y'.subtype, y * v * y⁻¹ ∈ V.map Y'.subtype := by
      intro y hy v hv
      obtain ⟨v', hv', rfl⟩ := hv
      exact ⟨⟨y, hy⟩ * v' * ⟨y, hy⟩⁻¹, hVn.conj_mem v' hv' ⟨y, hy⟩, rfl⟩
    have hV3 : ¬ p ∣ Nat.card ↥(V.map Y'.subtype) := by
      rwa [Subgroup.card_map_of_injective Y'.subtype_injective]
    have hVN := hY1.coprime _ hV1 hV2 hV3
    intro v hv
    exact Subgroup.mem_subgroupOf.2 ⟨hVN ⟨v, hv, rfl⟩, v.2⟩

theorem y2Aut_of_weyl [Finite G] (hKW : KFW4Plane) {p : ℕ} {E N Y' P : Subgroup G}
    (hS : Setting p E N) (hp5 : 5 ≤ p) (hY1 : Y1Out p E N Y' P)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hS4 : Nat.card ↥(P ⊓ E) = p ^ 2 →
      Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∧ Nat.card ↥E = p ^ 3) :
    Y2Aut p ((P ⊓ E).subgroupOf Y') := by
  have hp := hS.prime
  have hPY : P ≤ Y' := hY1.syl.1
  have hBE : P ⊓ E ≤ E := inf_le_right
  have hBY : P ⊓ E ≤ Y' := inf_le_left.trans hPY
  have hB1 : P ⊓ E ≠ ⊥ := fun h => hY1.noncyc (by rw [h]; infer_instance)
  have hcard : Nat.card ↥((P ⊓ E).subgroupOf Y') = Nat.card ↥(P ⊓ E) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv
  have hN : ∀ n : ↥Y', n ∈ Subgroup.normalizer (((P ⊓ E).subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') →
      (n : G) ∈ Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G) := by
    intro n hn
    have := mem_normalizer_map_subtype hn
    rwa [Subgroup.map_subgroupOf_eq_of_le hBY] at this
  have hC : ∀ n : ↥Y', (n : G) ∈ Subgroup.centralizer ((P ⊓ E : Subgroup G) : Set G) →
      n ∈ Subgroup.centralizer (((P ⊓ E).subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hn (b : G) (Subgroup.mem_subgroupOf.1 hb)
  have hC' : ∀ n : ↥Y', n ∈ Subgroup.centralizer (((P ⊓ E).subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') →
      (n : G) ∈ Subgroup.centralizer ((P ⊓ E : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hn ⟨b, hBY hb⟩
      (Subgroup.mem_subgroupOf.2 hb))
  have hS45 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (↥W₀ ≃* Equiv.Perm (Fin 5)) := by
    obtain ⟨-, -, h, -, -, -⟩ := hW
    exact h
  have hord6 : ∀ u ∈ W₀, orderOf u ≤ 6 := by
    rcases hS45 with h4 | h5
    · obtain ⟨e⟩ := h4
      exact fun u hu => (hord_perm4 e u hu).trans (by norm_num)
    · obtain ⟨e⟩ := h5
      exact hord_perm5 e
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, hm1, hm6, hnm⟩ := aut_ord hp hS.Eel hJ hBE hB1 hW hord6 (hN n hn)
    exact ⟨m, hm1, hm6, hC _ (by rw [Subgroup.coe_pow]; exact hnm)⟩
  · intro hB2 n hn
    obtain ⟨hW4, hE3⟩ := hS4 (by rw [← hcard]; exact hB2)
    obtain ⟨e⟩ := hW4
    obtain ⟨m, hm1, hm4, hnm⟩ := aut_ord hp hS.Eel hJ hBE hB1 hW (hord_perm4 e) (hN n hn)
    exact ⟨m, hm1, hm4, hC _ (by rw [Subgroup.coe_pow]; exact hnm)⟩
  · intro hB25 F hFN hFne
    have hB25' : Nat.card ↥(P ⊓ E) = 25 := by rw [← hcard]; exact hB25
    have hBp2 : Nat.card ↥(P ⊓ E) = p ^ 2 := by
      rcases hY1.card with h | h
      · exact h
      · exfalso
        have h125 : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
        omega
    have hp25 : p = 5 := by
      have h1 : p ^ 2 = 25 := by rw [← hBp2]; exact hB25'
      have h2 : p ≤ 5 := by
        by_contra h
        push Not at h
        nlinarith
      omega
    obtain ⟨hW4, hE3⟩ := hS4 hBp2
    have hbound := aut_count hKW hp hp5 hS.Eel hJ hE3 hBE hBp2 hW hW4
      (F.map ⟨Subtype.val, Subtype.val_injective⟩)
      (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
        exact hN y (hFN y hy))
      (by
        intro x hx y hy hxy hxy'
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
        have hab : a ≠ b := fun h => hxy (by rw [h])
        exact hFne a ha b hb hab (hC (a⁻¹ * b) (by simpa using hxy')))
    rw [Finset.card_map] at hbound
    have h32 : (p - 1) * 8 = 32 := by rw [hp25]
    omega

structure Y2Out (p : ℕ) (N Y' P B O : Subgroup G) : Prop where
  p5 : p = 5
  card : Nat.card ↥B = 25
  PB : P = B
  O_le : O ≤ Y'
  O_norm : ∀ y ∈ Y', ∀ o ∈ O, y * o * y⁻¹ ∈ O
  O_cop : ¬ p ∣ Nat.card ↥O
  O_N : O ≤ N
  two : ∀ V : Subgroup G, V ≤ Y' → IsPGroup 2 ↥V → B ≤ Subgroup.normalizer (V : Set G) → V ≤ O
  simple5 : ¬ HasNonabSimpleSection 5 ↥(N ⊓ Y')
  three : ∃ n ∈ Y', n ∈ Subgroup.normalizer (B : Set G) ∧ n ^ 3 ∈ Subgroup.centralizer (B : Set G) ∧
    n ∉ Subgroup.centralizer (B : Set G)

end Sec1511

end CFSG.RankThree.PartOne
