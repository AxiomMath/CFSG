module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FModel

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def ClassOneDichotomy {G : Type} [Group G] [Finite G] (Y : Subgroup G) (c d : G) :
    Prop :=
  (Nonempty (imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))
      ≃* projSL 2 (GaloisField 2 3)) ∧
    (Nat.card ↥(barCentralizer (Subgroup.zpowers c) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y)).factorization 3 = 2) ∨
  (¬ Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 3)) ∧
    (Nat.card ↥(barCentralizer (Subgroup.zpowers c) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y)).factorization 3 = 3)

namespace Hering88N

theorem classOne_of_model {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hd3 : d ^ 3 = 1)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    {M : Type} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥)
    {H : Type} [Group H] [Finite H] (ι : H →* M) (hι : Function.Injective ι)
    (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* M) (φ : MulAut M)
    (hφ : KFacts.inducedAutHom Y E ⟨c, hcN⟩ = φ) (hrange : ∀ z, z ∈ ι.range ↔ φ z = z)
    (P_S P_L : H → Prop)
    (hcls : ∀ w₀ : H, w₀ ^ 3 = 1 → w₀ ≠ 1 →
      ∃ c₀ : H, P_S (c₀ * w₀ * c₀⁻¹) ∨ P_L (c₀ * w₀ * c₀⁻¹))
    (hL : ∀ y : H, P_L y → y ^ 3 = 1 → y ≠ 1 →
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({ι y} : Set M)) ≃*
        projSL 2 (GaloisField 2 3)) ∧
      (Nat.card (Subgroup.centralizer ({y} : Set H))).factorization 3 = 2)
    (hS : ∀ y : H, P_S y → y ^ 3 = 1 → y ≠ 1 →
      ¬ Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({ι y} : Set M)) ≃*
        projSL 2 (GaloisField 2 3)) ∧
      (Nat.card (Subgroup.centralizer ({y} : Set H))).factorization 3 = 3) :
    ClassOneDichotomy Y c d := by
  classical
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  have hdin₁ : KFacts.IsInnerAut (KFacts.inducedAutHom Y E ⟨d, hdN⟩) := by
    rw [KFacts.inducedAutHom_apply, KFacts.isInnerAut_congr]
    exact hdin
  obtain ⟨w, hw, hw3, hw1, -⟩ := Item8KFacts3.exists_conj_residual E hZ hdN hd3 hdin₁ hdne
  have hcomm : KFacts.inducedAutHom Y E ⟨c, hcN⟩ * KFacts.inducedAutHom Y E ⟨d, hdN⟩ =
      KFacts.inducedAutHom Y E ⟨d, hdN⟩ * KFacts.inducedAutHom Y E ⟨c, hcN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hcd)
  have hfix : φ w = w := by
    rw [hφ, ← hw] at hcomm
    have h1 := KFacts.mul_mulAutConj_mul_inv φ w
    rw [hcomm, mul_inv_cancel_right] at h1
    exact (hinj h1).symm
  obtain ⟨w₀, hw₀⟩ := (hrange w).mpr hfix
  have hw₀3 : w₀ ^ 3 = 1 := by
    apply hι
    rw [map_pow, hw₀, hw3, map_one]
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    apply hw1
    rw [← hw₀, map_one]
  obtain ⟨c₀, hc₀⟩ := hcls w₀ hw₀3 hw₀1
  set y₀ : H := c₀ * w₀ * c₀⁻¹ with hy₀
  have hy₀3 : y₀ ^ 3 = 1 := by
    rw [hy₀, conj_pow, hw₀3]
    group
  have hy₀1 : y₀ ≠ 1 := fun h => hw₀1 (by
    have : w₀ = c₀⁻¹ * y₀ * c₀ := by rw [hy₀]; group
    rw [this, h]
    group)
  clear_value y₀
  have hιc : φ (ι c₀) = ι c₀ := (hrange _).mp ⟨c₀, rfl⟩
  set E₂ : Y ⧸ aschbacherSolvableCore 3 Y ≃* M := E.trans (MulAut.conj (ι c₀)) with hE₂
  have hα₂ : KFacts.inducedAutHom Y E₂ ⟨c, hcN⟩ = φ := by
    rw [hE₂, Item8KFacts3.inducedAutHom_trans_conj, hφ]
    exact Hering88F.conj_mul_mul_conj_inv_of_fixed _ hιc
  have hdin₂ : KFacts.IsInnerAut (KFacts.inducedAutHom Y E₂ ⟨d, hdN⟩) := by
    rw [KFacts.inducedAutHom_apply, KFacts.isInnerAut_congr]
    exact hdin
  obtain ⟨w', hw', hw'3, hw'1, ⟨eW⟩⟩ := Item8KFacts3.exists_conj_residual E₂ hZ hdN hd3 hdin₂ hdne
  have hw'eq : w' = ι y₀ := by
    apply hinj
    rw [hw', hE₂, Item8KFacts3.inducedAutHom_trans_conj, ← hw, hy₀]
    simp only [map_mul, map_inv, hw₀]
  have hHmap : (barCentralizer (Subgroup.zpowers c) Y).map E₂.toMonoidHom = ι.range :=
    KFacts.map_barCentralizer_eq hcN E₂ ι.range (fun z => by
      rw [hα₂]
      exact hrange z)
  have hCmap : (barCentralizer (Subgroup.zpowers d) Y).map E₂.toMonoidHom =
      Subgroup.centralizer ({w'} : Set M) :=
    KFacts.map_barCentralizer_eq hdN E₂ _ (fun z => by
      rw [← hw', MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
        mul_inv_eq_iff_eq_mul]
      exact eq_comm)
  set N := Subgroup.centralizer ({y₀} : Set H) with hN
  have hS1 : ι.range ⊓ Subgroup.centralizer ({w'} : Set M) = N.map ι := by
    ext x
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩
      have hx' : ι n ∈ Subgroup.centralizer ({w'} : Set M) := hx
      refine ⟨n, ?_, rfl⟩
      show n ∈ N
      rw [hN, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hx'
      apply hι
      rw [map_mul, map_mul, ← hw'eq]
      exact hx'
    · rintro ⟨n, hn, rfl⟩
      have hn' : n ∈ Subgroup.centralizer ({y₀} : Set H) := hn
      refine ⟨⟨n, rfl⟩, ?_⟩
      show ι n ∈ Subgroup.centralizer ({w'} : Set M)
      rw [Subgroup.mem_centralizer_singleton_iff] at hn' ⊢
      rw [hw'eq, ← map_mul, ← map_mul, hn']
  have hZmap : (barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y).map
      E₂.toMonoidHom = N.map ι := by
    rw [Subgroup.map_inf_eq _ _ _ E₂.injective, hHmap, hCmap, hS1]
  have hcard : Nat.card ↥(barCentralizer (Subgroup.zpowers c) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y) = Nat.card N := by
    rw [← Subgroup.card_map_of_injective (f := E₂.toMonoidHom) E₂.injective, hZmap,
      Subgroup.card_map_of_injective hι]
  subst hw'eq
  rcases hc₀ with hSy | hLy
  ·
    right
    obtain ⟨hne, h3⟩ := hS y₀ hSy hy₀3 hy₀1
    refine ⟨fun ⟨e⟩ => hne ⟨eW.symm.trans e⟩, ?_⟩
    rw [hcard]
    exact h3
  ·
    left
    obtain ⟨⟨e⟩, h3⟩ := hL y₀ hLy hy₀3 hy₀1
    refine ⟨⟨eW.trans e⟩, ?_⟩
    rw [hcard]
    exact h3

end Hering88N

end CFSG.RankThree.PartTwo.Sec8

end
