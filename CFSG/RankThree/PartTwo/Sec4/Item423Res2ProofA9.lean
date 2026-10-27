module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA9Perm

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv Equiv.Perm Item434AltPerm

theorem A0_nine_le : A0 9 ≤ alternatingGroup (Fin 9) := by
  have hf := wFacts_nine.toA0Facts
  intro x hx
  obtain ⟨v, rfl⟩ := (mem_A0 hf).mp hx
  have h1 : sign (c1 9) = 1 := by
    rw [c1, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  have h2 : sign (c2 9) = 1 := by
    rw [c2, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  have h3 : sign (c3 9) = 1 := by
    rw [c3, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  rw [mem_alternatingGroup, vecPerm, Perm.sign_mul, Perm.sign_mul, map_pow, map_pow, map_pow, h1,
    h2, h3]
  simp

theorem card_W_nine : Nat.card (W 9) = 3 ^ (Nat.card (Perm (Fin 9))).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact card_eq_of_isPGroup_of_le (isPGroup_W wFacts_nine)
    (by rw [factorization_nine]; exact le_card_W wFacts_nine)

theorem exists_conj_le_W {D : Subgroup (alternatingGroup (Fin 9))} (hD9 : Nat.card D = 9)
    (hmax : ∀ E : Subgroup (alternatingGroup (Fin 9)), CFSG.Assembly.IsElemAbelian 3 E →
      D ≤ E → E ≤ D) :
    ∃ g : Perm (Fin 9),
      ((D.map (alternatingGroup (Fin 9)).subtype).map (MulAut.conj g⁻¹).toMonoidHom ≤ W 9) ∧
      ¬ ((D.map (alternatingGroup (Fin 9)).subtype).map (MulAut.conj g⁻¹).toMonoidHom ≤ A0 9) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D' := D.map (alternatingGroup (Fin 9)).subtype with hD'
  have hD'p : IsPGroup 3 D' := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hD', Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective, hD9]
    norm_num
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_card card_W_nine hD'p
  refine ⟨g, map_conj_inv_le hg, fun hA => ?_⟩
  set E' := (A0 9).map (MulAut.conj g).toMonoidHom with hE'
  have hE'A : E' ≤ alternatingGroup (Fin 9) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxA := A0_nine_le hx
    exact (inferInstance : (alternatingGroup (Fin 9)).Normal).conj_mem x hxA g
  have hDE : D' ≤ E' := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hA
    rwa [map_conj_map_conj_inv] at h1
  set E := E'.comap (alternatingGroup (Fin 9)).subtype with hE
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := by
    have hA0 := isElemAbelian_A0 wFacts_nine.toA0Facts
    have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
      isElemAbelian_map' _ ⟨hA0.1, hA0.2⟩
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hE'e.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
      exact h
    · have h := hE'e.2 _ hx
      exact h
  have hDE' : D ≤ E := fun x hx => hDE ⟨x, hx, rfl⟩
  have hED := hmax E hEe hDE'
  have hcard : Nat.card E = 27 := by
    have h1 : E.map (alternatingGroup (Fin 9)).subtype = E' := by
      rw [hE, Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.mpr hE'A
    rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective, h1, hE',
      Subgroup.card_map_of_injective (MulAut.conj g).injective, card_A0 wFacts_nine.toA0Facts]
  have := Subgroup.card_le_of_le hED
  rw [hcard, hD9] at this
  norm_num at this

noncomputable def autNineEquiv : Perm (Fin 9) ≃* MulAut (alternatingGroup (Fin 9)) :=
  MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num))

theorem autNineEquiv_coe (d : alternatingGroup (Fin 9)) :
    autNineEquiv (d : Perm (Fin 9)) = MulAut.conj d := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change ((MulAut.conjNormal (d : Perm (Fin 9)) x : alternatingGroup (Fin 9)) : Perm (Fin 9)) = _
  rw [MulAut.conjNormal_apply]
  rfl

theorem noSignalizer_alt9 {D : Subgroup (alternatingGroup (Fin 9))}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hmax : ∀ E : Subgroup (alternatingGroup (Fin 9)), CFSG.Assembly.IsElemAbelian 3 E →
      D ≤ E → E ≤ D)
    (Q : Subgroup (MulAut (alternatingGroup (Fin 9)))) (hQ : ¬ 3 ∣ Nat.card Q)
    (hN : D.map (MulAut.conj : alternatingGroup (Fin 9) →* MulAut (alternatingGroup (Fin 9))) ≤
      Subgroup.normalizer (Q : Set (MulAut (alternatingGroup (Fin 9))))) : Q = ⊥ := by
  obtain ⟨g, hgW, hgA⟩ := exists_conj_le_W hD9 hmax
  set D' := D.map (alternatingGroup (Fin 9)).subtype with hD'
  set D₂ := D'.map (MulAut.conj g⁻¹).toMonoidHom with hD₂
  set Q' := (Q.map autNineEquiv.symm.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'3 : ¬ 3 ∣ Nat.card Q' := by
    rwa [hQ', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective autNineEquiv.symm.injective]
  have hD₂e : CFSG.Assembly.IsElemAbelian 3 D₂ := isElemAbelian_map' _ (isElemAbelian_map' _ hD)
  have hD₂9 : Nat.card D₂ = 9 := by
    rw [hD₂, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD',
      Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective, hD9]
  have hND : D₂ ≤ Subgroup.normalizer (Q' : Set (Perm (Fin 9))) := by
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hx
    have hdN := hN ⟨d, hd, rfl⟩
    have hq' : MulAut.conj d * q * (MulAut.conj d)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hdN q).mp hq
    have hd' : autNineEquiv.symm (MulAut.conj d) = (d : Perm (Fin 9)) := by
      rw [← autNineEquiv_coe, MulEquiv.symm_apply_apply]
    refine ⟨autNineEquiv.symm (MulAut.conj d * q * (MulAut.conj d)⁻¹),
      ⟨_, hq', rfl⟩, ?_⟩
    change MulAut.conj g⁻¹ (autNineEquiv.symm (MulAut.conj d * q * (MulAut.conj d)⁻¹)) =
      MulAut.conj g⁻¹ (d : Perm (Fin 9)) * MulAut.conj g⁻¹ (autNineEquiv.symm q) *
        (MulAut.conj g⁻¹ (d : Perm (Fin 9)))⁻¹
    simp only [map_mul, map_inv, hd']
  have hQ'bot := eq_bot_of_le_W_of_not_le_A0 hgW hgA hD₂e hD₂9 hQ'3 hND
  rw [hQ', Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective,
    Subgroup.map_eq_bot_iff_of_injective _ autNineEquiv.symm.injective] at hQ'bot
  exact hQ'bot

theorem alphaVanishes_alt9 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 9))
    {D : Subgroup X} (hD : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D)
    (hD9 : Nat.card D = 9) : AlphaVanishes X D := by
  set D₁ := D.map e.toMonoidHom with hD₁
  have hD₁e : CFSG.Assembly.IsElemAbelian 3 D₁ := isElemAbelian_map' _ hD.prop
  have hD₁9 : Nat.card D₁ = 9 := by rw [hD₁, Subgroup.card_map_of_injective e.injective, hD9]
  have hmax : ∀ E : Subgroup (alternatingGroup (Fin 9)), CFSG.Assembly.IsElemAbelian 3 E →
      D₁ ≤ E → E ≤ D₁ := by
    intro E hE hDE
    have hEe : CFSG.Assembly.IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      isElemAbelian_map' _ hE
    have hDE' : D ≤ E.map e.symm.toMonoidHom := by
      intro x hx
      exact ⟨e x, hDE ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have h1 := hD.2 hEe hDE'
    intro y hy
    refine ⟨e.symm y, h1 ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩
  refine alphaVanishes_of_mulEquiv e (alphaVanishes_of_noSignalizer
    (alternatingGroup.center_eq_bot (by simp)) (fun a ha b hb =>
      congrArg Subtype.val (hD₁e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) ?_
    (noSignalizer_alt9 hD₁e hD₁9 hmax))
  intro hb
  rw [← hD₁] at hb
  rw [hb, Subgroup.card_bot] at hD₁9
  norm_num at hD₁9

theorem census423_of_alt9 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 9)) :
    Census423 X :=
  census423_of_alphaVanishes fun _ hD hD9 => alphaVanishes_alt9 e hD hD9

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
