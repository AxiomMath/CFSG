module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThreeHolds
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CorFourTwoMore TableBExc.E6Three E6TwoTB

namespace E6PlusThreeTB

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Frame


theorem exists_conj_map_eq_frame_range (D : ExcFrames.E6QPlusThree.E6QPlusThreeFrame K)
    {A : Subgroup (adjointGroup .E6 K)} (hA : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A) :
    ∃ c : adjointGroup .E6 K, A.map (MulAut.conj c).toMonoidHom = D.frame.range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  obtain ⟨P, hP⟩ := D.exists_sylow_le
  obtain ⟨c, -, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow (p := 3)
    (H := adjointGroup .E6 K) ⊤ P le_top A le_top (CFSG.Open.IsElemAbelian.isPGroup hA)
  have hA₁ : IsElemAbelian 3 (A.map (MulAut.conj c).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hA _
  have hcard : Nat.card (A.map (MulAut.conj c).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hA₁N : A.map (MulAut.conj c).toMonoidHom ≤ D.N := hc.trans hP
  let φ : A.map (MulAut.conj c).toMonoidHom →* WeylGroup .F4 :=
    D.weyl.comp (Subgroup.inclusion hA₁N)
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have hlt := ExcFrames.card_lt_of_weylHom (τ := Tag.F4) (p := 3)
      (NoOffExc.ggWeylNoOffender_F4 Nat.prime_three (by norm_num))
      D.frame D.frame_injective (A := A.map (MulAut.conj c).toMonoidHom) hA₁ φ
      (fun a s => D.conj_frame (Subgroup.inclusion hA₁N a) s)
      (fun a ha => D.mem_frame_range_of_weyl_eq_one (Subgroup.inclusion hA₁N a) ha
        (hA₁.2 (a : adjointGroup .E6 K) a.2)) hne
    change Nat.card (A.map (MulAut.conj c).toMonoidHom) < 3 ^ 4 at hlt
    omega
  have hle : A.map (MulAut.conj c).toMonoidHom ≤ D.frame.range := by
    intro a ha
    have hmem : φ ⟨a, ha⟩ ∈ φ.range := ⟨⟨a, ha⟩, rfl⟩
    rw [hbot] at hmem
    have hφa : φ ⟨a, ha⟩ = 1 := by simpa using hmem
    exact D.mem_frame_range_of_weyl_eq_one ⟨a, hA₁N ha⟩ hφa (hA₁.2 a ha)
  have hframe : Nat.card D.frame.range = 3 ^ 4 := by
    rw [← Subgroup.map_top D.frame, Subgroup.card_map_of_injective D.frame_injective,
      Subgroup.card_top, Nat.card_eq_fintype_card]
    change Fintype.card (Fin 4 → ZMod 3) = 3 ^ 4
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  exact ⟨c, Subgroup.eq_of_le_of_card_ge hle (by omega)⟩

end Frame

section Main


theorem ggTorusIrredSecElt_adjoint_E6_plusThree (h3 : 3 ∣ Nat.card K + 1) :
    GGTorusIrredSecElt 3 4 (adjointGroup .E6 K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨D⟩ := ExcFrames.E6QPlusThree.nonempty_e6QPlusThreeFrame h3
  have hB : IsElemAbelian 3 (torusE6Two (K := K) h2).range := by
    rw [← Subgroup.map_top (torusE6Two (K := K) h2)]
    refine CFSG.Open.IsElemAbelian.map ⟨inferInstance, fun x _ => ?_⟩ _
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hB4 : 3 ^ 4 ≤ Nat.card (torusE6Two (K := K) h2).range := by
    rw [← Subgroup.map_top (torusE6Two (K := K) h2),
      Subgroup.card_map_of_injective (torusE6Two_injective h2), Subgroup.card_top,
      Nat.card_eq_fintype_card]
    change 3 ^ 4 ≤ Fintype.card (Fin 4 → ZMod 3)
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hback : ∀ (c : adjointGroup .E6 K) (H : Subgroup (adjointGroup .E6 K)),
      (H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = H := by
    intro c H
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E6 K) := by
      refine MonoidHom.ext fun x => ?_
      show MulAut.conj c⁻¹ (MulAut.conj c x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  obtain ⟨c', hc'⟩ := exists_conj_map_eq_frame_range D hB hB4
  intro E hE h4 _
  obtain ⟨c, hc⟩ := exists_conj_map_eq_frame_range D hE h4
  show SecEltAt 3 E
  refine SecEltAt.of_map (MulAut.conj c) ?_
  rw [hc]
  refine SecEltAt.of_map (MulAut.conj c'⁻¹) ?_
  rw [← hc', hback]
  exact secEltAt_torus h2

theorem ggTorusIrred_E6_plusThree (h3 : 3 ∣ Nat.card K + 1) :
    GGTorusIrred 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have hn3 : ¬ 3 ∣ Nat.card K - 1 := by
    intro h
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    have hsub : 3 ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub h3 h
    have h2 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h2] at hsub
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) hsub
  have hcube : ∀ s : Kˣ, ∃ u : Kˣ, u ^ 3 = s := by
    intro s
    have h1 : orderOf s ∣ Nat.card K - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard s
    have hcop : Nat.Coprime 3 (orderOf s) :=
      Nat.Coprime.coprime_dvd_right h1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    exact ⟨s ^ m, by rw [← pow_mul, mul_comm, pow_mul, hm]⟩
  exact ggTorusIrred_of_irredSecElt Nat.prime_three
    (TableBExc.idImage_subset_inn_of_top .E6 K
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE6_adj hcube))
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (ggTorusIrredSecElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggTorusIrredSecElt_adjoint_E6_plusThree h3))

end Main

end E6PlusThreeTB

@[expose] def GGE6PlusThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

section Label


theorem largeEvenLabelAll_torusIrred_e6PlusThree {p : ℕ} {lab : LargeEvenLabel}
    (h : GGE6PlusThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p 4 R ∧ GGTorusIrred p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, rfl, h3⟩ := h
  dsimp only at htag h3
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', TableBExc.E6Three.ggTorusLift_E6_two,
    E6PlusThreeTB.ggTorusIrred_E6_plusThree (by rw [hK]; exact h3)⟩

end Label

end CFSG.StandardType

end
