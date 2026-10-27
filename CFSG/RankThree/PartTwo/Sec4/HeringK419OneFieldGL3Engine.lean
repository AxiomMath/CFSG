module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSL2
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldBlock
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldDiag

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix
open scoped _root_.Classical

section Engine


theorem class_facts_three {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 3)
    {E' : Type} (μ : ι → E') (hnc : ¬ ∀ i j, μ i = μ j) :
    (∀ i, Fintype.card {j // μ j = μ i} ≤ 2) ∧ ∃ i₀, Fintype.card {j // μ j = μ i₀} = 1 := by
  have hcardsum : ∀ i, Fintype.card {j // μ j = μ i} + Fintype.card {j // ¬ μ j = μ i} = 3 := by
    intro i
    rw [Fintype.card_subtype_compl, ← hι]
    have := Fintype.card_subtype_le (fun j => μ j = μ i)
    omega
  have hbound : ∀ i, Fintype.card {j // μ j = μ i} ≤ 2 := by
    intro i
    by_contra hcon
    push Not at hcon
    apply hnc
    have h0 : Fintype.card {j // ¬ μ j = μ i} = 0 := by have := hcardsum i; omega
    have hall : ∀ j, μ j = μ i := by
      intro j
      by_contra hj
      have : Nonempty {j // ¬ μ j = μ i} := ⟨⟨j, hj⟩⟩
      have := Fintype.card_pos (α := {j // ¬ μ j = μ i})
      omega
    intro a b
    rw [hall a, hall b]
  refine ⟨hbound, ?_⟩
  by_contra hcon
  push Not at hcon
  have hpos : ∀ i, 0 < Fintype.card {j // μ j = μ i} := fun i =>
    Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  have hge2 : ∀ i, Fintype.card {j // μ j = μ i} = 2 := fun i => by
    have := hcon i
    have := hbound i
    have := hpos i
    omega
  obtain ⟨i₀⟩ : Nonempty ι := by
    apply Fintype.card_pos_iff.mp
    omega
  have hT : Fintype.card {j // ¬ μ j = μ i₀} = 1 := by have := hcardsum i₀; have := hge2 i₀; omega
  obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.mp hT
  have hSk : 1 < Fintype.card {j // μ j = μ k} := by have := hge2 k; omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Fintype.one_lt_card_iff_nontrivial.mp hSk |>.exists_pair_ne
  have hex : ∃ j, μ j = μ k ∧ j ≠ k := by
    by_cases hak : a = k
    · exact ⟨b, hb, fun h => hab (by subst hak; subst h; rfl)⟩
    · exact ⟨a, ha, hak⟩
  obtain ⟨j, hj, hjk⟩ := hex
  have hjT : ¬ μ j = μ i₀ := by rw [hj]; exact k.2
  have := hk ⟨j, hjT⟩
  exact hjk (congrArg Subtype.val this)

theorem not_isType419_of_commute_gl3 {E : Type} [Field E] [Finite E] (h3 : (3 : E) ≠ 0)
    {P : Type} [Group P] (hP : commutator P = ⊤) (ρ : P →* GL (Fin 3) E)
    (hρ : Function.Injective ρ) {K : Type} [Group K]
    (hK : IsType419 K) (hs : IsSimpleGroup K) (hZ : Subgroup.center K = ⊥)
    (π : P →* K) (hπ : Function.Surjective π)
    (hker : ∀ p : P, π p = 1 →
      ∃ z : Eˣ, ρ p = Matrix.GeneralLinearGroup.scalar (Fin 3) z)
    (A : GL (Fin 3) E) (c : Eˣ)
    (hA3 : ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) ^ 3 =
      (c : E) • (1 : Matrix (Fin 3) (Fin 3) E))
    (hAn : ∀ b : E, ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) ≠
      b • (1 : Matrix (Fin 3) (Fin 3) E))
    (hcomm : ∀ p : P, ρ p * A = A * ρ p) : False := by
  have hnc := Item419Res3.exists_noncommuting_isType419 hK hZ
  obtain ⟨E', hF', hfin', φ, μ, M, hchar, hMinj, hblock, hμ3, -, -, -, hconst, hMscal⟩ :=
    exists_blockDiagonalization h3 (K := P) ρ A c hA3 hcomm
  letI : Field E' := hF'
  haveI : Finite E' := hfin'
  have hnc' : ¬ ∀ i j, μ i = μ j := fun hc => by
    obtain ⟨b, hb⟩ := hconst hc
    exact hAn b hb
  obtain ⟨hbound, i₀, hi₀⟩ := class_facts_three (by simp) μ hnc'
  have hdet : ∀ p : P, (blk μ M hblock (μ i₀) p).det = 1 := by
    intro p
    have h0 := eq_one_of_perfect hP
      ((Matrix.detMonoidHom : Matrix {j // μ j = μ i₀} {j // μ j = μ i₀} E' →* E').comp
        (blk μ M hblock (μ i₀))).toHomUnits p
    have h1 := congrArg Units.val h0
    simpa using h1
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    obtain ⟨z, hz⟩ := hker p hp
    have hz' : ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
        (z : E) • (1 : Matrix (Fin 3) (Fin 3) E) := by
      rw [hz, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
    have hMp := hMscal p z hz'
    haveI : Subsingleton {j // μ j = μ i₀} := Fintype.card_le_one_iff_subsingleton.mp hi₀.le
    haveI : Unique {j // μ j = μ i₀} := uniqueOfSubsingleton (⟨i₀, rfl⟩ : {j // μ j = μ i₀})
    have hd := hdet p
    rw [Matrix.det_unique] at hd
    have hent : blk μ M hblock (μ i₀) p default default = M p i₀ i₀ := by
      have h1 : (default : {j // μ j = μ i₀}) = ⟨i₀, rfl⟩ := Subsingleton.elim _ _
      rw [h1]
      rfl
    rw [hent, hMp] at hd
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hd
    have hz1 : z = 1 := Units.ext (φ.injective (by rw [hd, Units.val_one, map_one]))
    rw [Subgroup.mem_bot]
    apply hρ
    rw [hz, hz1, map_one, map_one]
  let eKP : K ≃* P := (MulEquiv.ofBijective π ⟨hπinj, hπ⟩).symm
  let M' : K →* Matrix (Fin 3) (Fin 3) E' := M.comp eKP.toMonoidHom
  have hM'inj : Function.Injective M' := fun k₁ k₂ h =>
    eKP.injective (hρ (hMinj _ _ h))
  obtain ⟨f, hf⟩ := exists_injective_slTwo_of_blockDiagonal μ hs hnc M' hM'inj
    (fun k i j hij => hblock _ i j hij) hbound
  exact Item419Res3.not_isType419_of_injective_slTwo_field hK hs hZ f hf

end Engine

end CFSG.RankThree.PartTwo.Sec4.HeringOF
