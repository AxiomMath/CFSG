module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

theorem exists_two_subgroup_acting {Y : Type} [Group Y] [Finite Y] {b₁ b₂ h₁ h₂ : Y}
    (hb₁ : b₁ ^ 3 = 1) (hb₂ : b₂ ^ 3 = 1) (hbc : b₁ * b₂ = b₂ * b₁)
    (r11 : h₁ * b₁ * h₁⁻¹ = b₂⁻¹) (r12 : h₁ * b₂ * h₁⁻¹ = b₁)
    (r21 : h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹) (r22 : h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂) :
    ∃ (P : Subgroup Y) (u₁ u₂ : Y), IsPGroup 2 P ∧ u₁ ∈ P ∧ u₂ ∈ P ∧
      (∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), ∀ u ∈ P,
        u * b * u⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set Y)) ∧
      (∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), u₁ * b * u₁⁻¹ = h₁ * b * h₁⁻¹) ∧
      (∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), u₂ * b * u₂⁻¹ = h₂ * b * h₂⁻¹) := by
  set B := Subgroup.closure ({b₁, b₂} : Set Y) with hB
  have c11 : MulAut.conj h₁ b₁ = b₂⁻¹ := by rw [MulAut.conj_apply, r11]
  have c12 : MulAut.conj h₁ b₂ = b₁ := by rw [MulAut.conj_apply, r12]
  have c21 : MulAut.conj h₂ b₁ = b₁⁻¹ * b₂⁻¹ := by rw [MulAut.conj_apply, r21]
  have c22 : MulAut.conj h₂ b₂ = b₁⁻¹ * b₂ := by rw [MulAut.conj_apply, r22]
  have hext : ∀ w w' : Y, MulAut.conj w b₁ = MulAut.conj w' b₁ →
      MulAut.conj w b₂ = MulAut.conj w' b₂ → ∀ b ∈ B, MulAut.conj w b = MulAut.conj w' b := by
    intro w w' e₁ e₂ b hb
    refine MonoidHom.eqOn_closure (f := (MulAut.conj w : Y →* Y))
      (g := (MulAut.conj w' : Y →* Y)) ?_ hb
    rintro _ (rfl | rfl)
    · exact e₁
    · exact e₂
  have hN : ∀ h : Y, MulAut.conj h b₁ ∈ B → MulAut.conj h b₂ ∈ B →
      h ∈ Subgroup.normalizer (B : Set Y) := by
    intro h e₁ e₂
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : B.map (MulAut.conj h : Y →* Y) ≤ B := by
      rw [hB, MonoidHom.map_closure, Subgroup.closure_le, Set.image_pair]
      rintro _ (rfl | rfl)
      · exact e₁
      · exact e₂
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  have hb₁B : b₁ ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb₂B : b₂ ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hh₁ : h₁ ∈ Subgroup.normalizer (B : Set Y) :=
    hN h₁ (c11 ▸ inv_mem hb₂B) (c12 ▸ hb₁B)
  have hh₂ : h₂ ∈ Subgroup.normalizer (B : Set Y) :=
    hN h₂ (c21 ▸ mul_mem (inv_mem hb₁B) (inv_mem hb₂B)) (c22 ▸ mul_mem (inv_mem hb₁B) hb₂B)
  set N := Subgroup.normalizer (B : Set Y)
  set f := B.normalizerMonoidHom
  set n₁ : N := ⟨h₁, hh₁⟩
  set n₂ : N := ⟨h₂, hh₂⟩
  have hf : ∀ (n : N) (b : B), (f n b : Y) = MulAut.conj (n : Y) b := fun _ _ => rfl
  have hfeq : ∀ n n' : N, (∀ b ∈ B, MulAut.conj (n : Y) b = MulAut.conj (n' : Y) b) →
      f n = f n' := by
    intro n n' h
    ext b
    rw [hf, hf]
    exact h b b.2
  have e₁ : b₁ * b₁ = b₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three', hb₁])
  have e₂ : b₂ * b₂ = b₂⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three', hb₂])
  have hx : f n₁ ^ 4 = 1 := by
    rw [← map_pow, ← map_one f]
    refine hfeq _ _ (hext _ _ ?_ ?_) <;>
      simp only [n₁, Subgroup.coe_mul, Subgroup.coe_one, pow_succ, pow_zero, one_mul, map_mul,
        map_one, map_inv, MulAut.mul_apply, MulAut.one_apply, c11, c12, inv_inv]
  have hy : f n₂ ^ 2 = f n₁ ^ 2 := by
    rw [← map_pow, ← map_pow]
    refine hfeq _ _ (hext _ _ ?_ ?_) <;>
      simp only [n₁, n₂, Subgroup.coe_mul, pow_succ, pow_zero, one_mul, map_mul, map_inv,
        MulAut.mul_apply, c11, c12, c21, c22, inv_inv, mul_inv_rev]
    · rw [← hbc, mul_assoc, mul_inv_cancel_left, e₁]
    · rw [mul_assoc, mul_inv_cancel_left, e₂]
  have hyx' : f n₂ * f n₁ = f n₁ ^ 3 * f n₂ := by
    rw [← map_mul, ← map_pow, ← map_mul]
    refine hfeq _ _ (hext _ _ ?_ ?_) <;>
      simp only [n₁, n₂, Subgroup.coe_mul, pow_succ, pow_zero, one_mul, map_mul, map_inv,
        MulAut.mul_apply, c11, c12, c21, c22, inv_inv, mul_inv_rev]
    rw [← mul_inv_rev, ← mul_inv_rev, hbc]
  have hyx : f n₂ * f n₁ * (f n₂)⁻¹ = (f n₁)⁻¹ := by
    rw [hyx', mul_inv_cancel_right, eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx
  set T : Subgroup N := Subgroup.closure {n₁, n₂}
  set g : T →* MulAut B := f.comp T.subtype
  have hrange : g.range = Subgroup.closure {f n₁, f n₂} := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_pair]
  have h2 : IsPGroup 2 g.range := by
    set φ := CFSG.Semidihedral.Local.normalFormHom (m := 2) hx hy hyx
    have hQ : IsPGroup 2 (QuaternionGroup 2) :=
      IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]; rfl)
    refine (hQ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).to_le ?_
    rw [hrange, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨QuaternionGroup.a 1, pow_one _⟩
    · exact ⟨QuaternionGroup.xa 0, mul_one _⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 T) := inferInstance
  have htop := ((P₀.mapSurjective g.rangeRestrict_surjective).is_maximal'
    (h2.of_equiv Subgroup.topEquiv.symm) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  have hlift : ∀ t : T, ∃ u ∈ (P₀ : Subgroup T), g u = g t := by
    intro t
    have hmem : g.rangeRestrict t ∈ (P₀ : Subgroup T).map g.rangeRestrict := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨u, hu, hut⟩ := hmem
    exact ⟨u, hu, congrArg Subtype.val hut⟩
  obtain ⟨v₁, hv₁, hgv₁⟩ := hlift ⟨n₁, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  obtain ⟨v₂, hv₂, hgv₂⟩ := hlift ⟨n₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  refine ⟨(P₀ : Subgroup T).map (N.subtype.comp T.subtype), ((v₁ : N) : Y), ((v₂ : N) : Y),
    P₀.isPGroup'.map _, ⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, rfl⟩, ?_, ?_, ?_⟩
  · rintro b hb _ ⟨v, -, rfl⟩
    exact ((Subgroup.mem_normalizer_iff.mp (v : N).2) b).mp hb
  · intro b hb
    exact congrArg (fun σ : MulAut B => (σ ⟨b, hb⟩ : Y)) hgv₁
  · intro b hb
    exact congrArg (fun σ : MulAut B => (σ ⟨b, hb⟩ : Y)) hgv₂

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
