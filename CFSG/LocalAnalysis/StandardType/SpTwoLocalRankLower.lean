module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.StandardType

namespace SpRank

open CFSG.Assembly
open CFSG.Open (StatedSp)

variable {G : Type} [Group G] [Finite G]

theorem le_largeEvenTwoLocalRank_of_normalizes {H : Type} [Group H] (χ : H →* G)
    (hχ : Function.Injective χ) {q r : ℕ} (hq : q.Prime) {E U : Subgroup H}
    (hE : IsElemAbelian q E) (hc : Nat.card E = q ^ r) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set H)) : r ≤ LargeEvenTwoLocalRank q G := by
  have hUne : U.map χ ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hχ]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map χ : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hle : E.map χ ≤ Subgroup.normalizer ((U.map χ : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn := Subgroup.mem_normalizer_iff.mp (hEU he)
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, (hn u).mp hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u', hu', hyu⟩
      have hy : y = χ (e⁻¹ * u' * e) := by
        simp only [map_mul, map_inv, hyu]
        group
      refine ⟨_, ?_, hy.symm⟩
      exact (hn (e⁻¹ * u' * e)).mpr (by
        rw [show e * (e⁻¹ * u' * e) * e⁻¹ = u' by group]
        exact hu')
  refine TableB.le_twoLocalRank hq.one_lt hTL (TableB.le_pRank_of_le hq.one_lt hle
    (TableB.isElemAbelian_map hE χ) ?_)
  rw [Subgroup.card_map_of_injective hχ, hc]

theorem le_largeEvenTwoLocalRank_statedSp {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) (hn : 1 ≤ n)
    (ψ : StatedSp n F →* G) (hψ : Function.Injective ψ) : n ≤ LargeEvenTwoLocalRank p G := by
  have hcard4 : 4 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    have hne : Nat.card F - 1 ≠ 0 := by omega
    have hple : p ≤ Nat.card F - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hpq
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    omega
  have hperf : commutator (StatedSp n F) = ⊤ :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple n F hn
      (Or.inl (Or.inr hcard4))).1.commutator_eq_top
  have hker : (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
      (StatedSp n F))).ker ≤ Subgroup.center (StatedSp n F) := by
    rw [QuotientGroup.ker_mk', CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    exact bot_le
  obtain ⟨U, E, hU, hU2, hEU, hE, hEc, -⟩ :=
    TableBSymp.ggTorusLift_symplectic (K := F) (m := n) hp hp2 hpq hn
      (↥(StatedSp n F))
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)))
      (QuotientGroup.mk'_surjective _) hker hperf
  exact le_largeEvenTwoLocalRank_of_normalizes ψ hψ hp hE hEc hU hU2 hEU

theorem generalLinearGroup_map_injective {R S : Type*} [CommRing R] [CommRing S] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) f) := by
  have hmap : Function.Injective (RingHom.mapMatrix (m := ι) f) := by
    intro M N h
    funext i j
    exact hf (congrFun (congrArg (fun X => X i) h) j)
  exact Units.map_injective hmap

theorem pred_le_largeEvenTwoLocalRank_three_statedSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 3 ≤ n) (ψ : StatedSp n F →* G) (hψ : Function.Injective ψ) :
    n - 1 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hk2 : 2 ≤ k := by omega
  have hperf : commutator (StatedSp (k + 1) (ZMod 2)) = ⊤ :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (k + 1) (ZMod 2) (by omega)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, by omega⟩))).1.commutator_eq_top
  have hker : (QuotientGroup.mk' ((CFSG.Open.StatedScalars
      (Fin (k + 1) ⊕ Fin (k + 1)) (ZMod 2)).subgroupOf (StatedSp (k + 1) (ZMod 2)))).ker ≤
      Subgroup.center (StatedSp (k + 1) (ZMod 2)) := by
    rw [QuotientGroup.ker_mk', CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    exact bot_le
  obtain ⟨U, E, hU, hU2, hEU, hE, hEc, -⟩ :=
    TwoThree.ggTorusLift_sp_two (K := ZMod 2) (k := k) (Nat.card_zmod 2)
      (↥(StatedSp (k + 1) (ZMod 2)))
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars
        (Fin (k + 1) ⊕ Fin (k + 1)) (ZMod 2)).subgroupOf (StatedSp (k + 1) (ZMod 2))))
      (QuotientGroup.mk'_surjective _) hker hperf
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have hφ : Function.Injective φ := ZMod.castHom_injective (n := 2) (R := F)
  let fGL : Matrix.GeneralLinearGroup (Fin (k + 1) ⊕ Fin (k + 1)) (ZMod 2) →*
      Matrix.GeneralLinearGroup (Fin (k + 1) ⊕ Fin (k + 1)) F :=
    Matrix.GeneralLinearGroup.map φ
  let ι : ↥(StatedSp (k + 1) (ZMod 2)) →* ↥(StatedSp (k + 1) F) :=
    { toFun := fun g => ⟨fGL (g : Matrix.GeneralLinearGroup (Fin (k + 1) ⊕ Fin (k + 1))
          (ZMod 2)), CFSG.Open.StatedAPI.map_mem_statedSp φ g.2⟩
      map_one' := Subtype.ext (map_one fGL)
      map_mul' := fun a b => Subtype.ext (map_mul fGL
        (a : Matrix.GeneralLinearGroup (Fin (k + 1) ⊕ Fin (k + 1)) (ZMod 2))
        (b : Matrix.GeneralLinearGroup (Fin (k + 1) ⊕ Fin (k + 1)) (ZMod 2))) }
  have hι_inj : Function.Injective ι := by
    intro a b hab
    exact Subtype.ext (generalLinearGroup_map_injective φ hφ (congrArg Subtype.val hab))
  exact le_largeEvenTwoLocalRank_of_normalizes (ψ.comp ι) (hψ.comp hι_inj) Nat.prime_three
    hE hEc hU hU2 hEU

end SpRank

end CFSG.StandardType
