module

public import CFSG.Quasithin.Vol2.Asc94.Defs
public import CFSG.Sporadic.He

public section

namespace CFSG.Quasithin.A94

@[expose] def He_order : Prop :=
  ∀ X : Subgroup CFSG.Blueprint.NativeSporadic.He, 2 ^ 10 * 3 ^ 2 * 5 * 7 ∣ Nat.card X → X = ⊤

private theorem card_gl_four_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, Fin.prod_univ_four, ZMod.card]
  rfl

private theorem dvd_card_of_surj {G : Type} [Group G] (E N : Subgroup G) (hEN : E ≤ N)
    (hEC : E ≤ Subgroup.centralizer (E : Set G)) (hE16 : Nat.card E = 16)
    (φ : N →* GL (Fin 4) (ZMod 2)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf N) :
    2 ^ 10 * 3 ^ 2 * 5 * 7 ∣ Nat.card N := by
  have hK : E.subgroupOf N ≤ φ.ker := by
    rw [hφk]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hEC hx
  have hE' : Nat.card (E.subgroupOf N) = 16 := by
    have h1 := Subgroup.card_map_of_injective (f := N.subtype) (K := E.subgroupOf N)
      N.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEN, hE16] at h1
    exact h1.symm
  have h16 : 16 ∣ Nat.card φ.ker := by
    have h1 := Subgroup.card_dvd_of_le hK
    rwa [hE'] at h1
  have hidx : φ.ker.index = 20160 := by
    rw [Subgroup.index_ker, (MonoidHom.range_eq_top).2 hφs, Subgroup.card_top,
      card_gl_four_two]
  have hcardN : Nat.card N = Nat.card φ.ker * 20160 := by
    rw [← hidx, Subgroup.card_mul_index]
  rw [hcardN, show 2 ^ 10 * 3 ^ 2 * 5 * 7 = 16 * 20160 by norm_num]
  exact Nat.mul_dvd_mul h16 (dvd_refl _)

private theorem eq_top_of_transfer {G H : Type} [Group G] [gH : Group H]
    (e : @MulEquiv G H _ (@Semigroup.toMul H (@Monoid.toSemigroup H
      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H gH))))) (n : ℕ)
    (P : ∀ X : Subgroup H, n ∣ Nat.card X → X = ⊤) (N : Subgroup G) (hN : n ∣ Nat.card N) :
    N = ⊤ := by
  have hYcard : Nat.card (N.map e.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
  have hY : N.map e.toMonoidHom = ⊤ := P _ (by rw [hYcard]; exact hN)
  rw [eq_top_iff]
  intro g _
  have hg : e.toMonoidHom g ∈ N.map e.toMonoidHom := by
    rw [hY]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hg
  have hxg' : x = g := e.injective hxg
  rw [← hxg']
  exact hx

private theorem false_of_normal_card {G H : Type} [Group G] [gH : Group H] [IsSimpleGroup H]
    (e : @MulEquiv G H _ (@Semigroup.toMul H (@Monoid.toSemigroup H
      (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H gH))))) (E : Subgroup G)
    (hE : E.Normal) (hcard : Nat.card E = 16) (hH : Nat.card H ≠ 16) : False := by
  have hmap : (E.map e.toMonoidHom).Normal := hE.map e.toMonoidHom e.surjective
  have hc : Nat.card (E.map e.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.map e.toMonoidHom) with h0 | h1
  · rw [h0, Subgroup.card_bot] at hc
    norm_num at hc
  · rw [h1, Subgroup.card_top] at hc
    exact hH hc

theorem heNoE16_of_order (h : He_order) :
    CFSG.Quasithin.A94.HeNoE16 := by
  rintro G _ _ ⟨E, hEab, hE16, φ, hφs, hφk⟩ ⟨e⟩
  have hEC : E ≤ Subgroup.centralizer (E : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hEab.1.is_comm.comm (⟨y, hy⟩ : E) ⟨x, hx⟩)
  have hdvd : 2 ^ 10 * 3 ^ 2 * 5 * 7 ∣ Nat.card (Subgroup.normalizer (E : Set G)) :=
    dvd_card_of_surj E (Subgroup.normalizer (E : Set G)) Subgroup.le_normalizer hEC hE16 φ hφs
      hφk
  have hNtop : Subgroup.normalizer (E : Set G) = ⊤ :=
    eq_top_of_transfer (G := G) (H := CFSG.Blueprint.NativeSporadic.He) (gH := inferInstance) e
      (2 ^ 10 * 3 ^ 2 * 5 * 7) h _ hdvd
  have hEnorm : E.Normal := Subgroup.normalizer_eq_top_iff.1 hNtop
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.He :=
    CFSG.Sporadic.He.fam_he_simplicity.2.2
  refine false_of_normal_card (G := G) (H := CFSG.Blueprint.NativeSporadic.He)
    (gH := inferInstance) e E hEnorm hE16 ?_
  rw [CFSG.Sporadic.He.fam_he_order.1]
  norm_num

end CFSG.Quasithin.A94
