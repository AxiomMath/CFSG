module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeA1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeM1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeM2A
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeM2B

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

private theorem qtwoDB3_m2_diag_conjTr_mul (hF0 : Nat.card F0 = 4) (c : Fin m → F0ˣ) :
    CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hcard : Fintype.card F0 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF0
  have h3 : ∀ i : Fin m, (c i : F0) ^ 3 = 1 := by
    intro i
    have h := FiniteField.pow_card_sub_one_eq_one (c i : F0) (c i).ne_zero
    rw [hcard] at h
    simpa using h
  have hval : ((qTwoChartTwoThree_diag c : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun i => (c i : F0)) := rfl
  rw [hval, CFSG.LieType.Steinberg.conjTr_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 from rfl]
  rw [show (c i : F0) ^ 2 * (c i : F0) = (c i : F0) ^ 3 by ring, h3 i]

private theorem qtwoDB3_m2_diag_mem_uU (h : UnitaryFieldData 2 1 F0)
    (hF0 : Nat.card F0 = 4) (c : Fin m → F0ˣ) : qTwoChartTwoThree_diag c ∈ uU h m := by
  rw [mem_uU]
  have hbar : (h.bar : F0 → F0) =
      fun x => CFSG.LieType.BorelTits.unitaryInvolution F0 2 1 x := by
    funext x
    rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hbar]
  simpa [CFSG.LieType.Universal.Unitary.conjTr] using qtwoDB3_m2_diag_conjTr_mul hF0 c

theorem qtwoDB3_core (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m) {ψ : Su F0 2 1 m →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) {B T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hBL : B ≤ Subgroup.normalizer (ψ.range : Set G))
    (hTL : T ≤ Subgroup.normalizer (ψ.range : Set G)) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hind : ∀ b ∈ B, ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ b c)
    (hnt : ∃ t ∈ T, ∃ b ∈ B, ⁅t, b⁆ ∉ Subgroup.centralizer (ψ.range : Set G)) :
    ∃ i j : Fin m, i ≠ j ∧
      ∀ b ∈ B, ∀ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ b c → c i = c j := by
  classical
  by_contra hcon
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  have h : UnitaryFieldData 2 1 F0 := ⟨Nat.prime_two, le_refl 1, by rw [hF0]; norm_num⟩
  let N : Subgroup G := Subgroup.normalizer (ψ.range : Set G)
  have hBLN : B ≤ N := hBL
  have hTLN : T ≤ N := hTL
  obtain ⟨Φ, hΦker, hΦact⟩ := qtwoDB3_exists_aut hK hm hker
  let Dh : Subgroup (Fin m → F0ˣ) :=
    { carrier := {c | ∃ b ∈ B, qTwoChartTwoThree_induces ψ b c}
      mul_mem' := by
        rintro c c' ⟨b, hb, hbc⟩ ⟨b', hb', hb'c'⟩
        exact ⟨b * b', B.mul_mem hb hb', qtwoDB3_ind_mul hbc hb'c'⟩
      one_mem' := ⟨1, B.one_mem, qtwoDB3_ind_one⟩
      inv_mem' := by
        rintro c ⟨b, hb, hbc⟩
        exact ⟨b⁻¹, B.inv_mem hb, qtwoDB3_ind_inv hbc⟩ }
  have hdist : ∀ i j : Fin m, i ≠ j → ∃ c ∈ Dh, c i ≠ c j := by
    intro i j hij
    by_contra hno
    apply hcon
    refine ⟨i, j, hij, ?_⟩
    intro b hb c hbc
    by_contra hne
    exact hno ⟨c, ⟨b, hb, hbc⟩, hne⟩
  let P : Type := StatedProj (StatedSU m (2 ^ 1) F0)
  let Tb : Subgroup (MulAut P) := (T.subgroupOf N).map Φ
  let Bb : Subgroup (MulAut P) := (B.subgroupOf N).map Φ
  let Kb : Subgroup (MulAut P) := ⁅Tb, Bb⁆
  let R : Subgroup (MulAut P) := (uConjAut h (by omega : 1 ≤ m)).range
  have hTsub2 : IsPGroup 2 (T.subgroupOf N) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTLN).symm
  have hTb2 : IsPGroup 2 Tb := hTsub2.map Φ
  have hstep3 : ∀ (b : G) (hb : b ∈ B) (c : Fin m → F0ˣ),
      qTwoChartTwoThree_induces ψ b c →
      ∀ A : uU h m, (A : GL (Fin m) F0) = qTwoChartTwoThree_diag c →
        Φ ⟨b, hBLN hb⟩ = uConjAut h (by omega : 1 ≤ m) A := by
    intro b hb c hc A hA
    ext x
    obtain ⟨g, rfl⟩ := projH_surjective x
    obtain ⟨u, rfl⟩ := (CFSG.GH74.L5U5.suEquiv hK m).surjective g
    obtain ⟨u', hu'mat, hu'ψ⟩ := hc u
    rw [hΦact ⟨b, hBLN hb⟩ u u' hu'ψ, uConjAut_proj]
    have heq : (CFSG.GH74.L5U5.suEquiv hK m u') =
        ⟨(A : GL (Fin m) F0) *
          ((CFSG.GH74.L5U5.suEquiv hK m u : ↥(StatedSU m (2 ^ 1) F0)) :
            GL (Fin m) F0) *
          (A : GL (Fin m) F0)⁻¹,
          uConjSU_mem h A (CFSG.GH74.L5U5.suEquiv hK m u)⟩ := by
      apply Subtype.ext
      rw [CFSG.GH74.L5U5.coe_suEquiv]
      show (u' : GL (Fin m) F0) = (A : GL (Fin m) F0) *
        ((CFSG.GH74.L5U5.suEquiv hK m u : ↥(StatedSU m (2 ^ 1) F0)) :
          GL (Fin m) F0) *
        (A : GL (Fin m) F0)⁻¹
      rw [hu'mat, hA, CFSG.GH74.L5U5.coe_suEquiv]
    rw [heq]
  have hBb_norm_Tb : Bb ≤ Subgroup.normalizer (Tb : Set (MulAut P)) := by
    rw [Subgroup.le_normalizer_iff]
    intro hx hxmem hy hymem
    obtain ⟨x, hxN, rfl⟩ := hxmem
    obtain ⟨y, hyN, rfl⟩ := hymem
    refine Subgroup.mem_map.2 ⟨x * y * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((x * y * x⁻¹ : ↥N) : G) = (x : G) * (y : G) * (x : G)⁻¹ := rfl
    rw [hcoe]
    have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.1 hxN
    have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.1 hyN
    exact (Subgroup.le_normalizer_iff.1 hBT) (x : G) hxB (y : G) hyT
  have hKTb : Kb ≤ Tb := by
    change ⁅Tb, Bb⁆ ≤ Tb
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := Bb) (K := Tb)).1 hBb_norm_Tb
  have hKb2 : IsPGroup 2 Kb := hTb2.to_le hKTb
  have hKb1 : Kb ≠ ⊥ := by
    intro hbot
    obtain ⟨t, ht, b, hb, hcomm⟩ := hnt
    let tN : ↥N := ⟨t, hTLN ht⟩
    let bN : ↥N := ⟨b, hBLN hb⟩
    have htTb : Φ tN ∈ Tb :=
      Subgroup.mem_map.2 ⟨tN, by show (tN : G) ∈ T; simpa [tN] using ht, rfl⟩
    have hbBb : Φ bN ∈ Bb :=
      Subgroup.mem_map.2 ⟨bN, by show (bN : G) ∈ B; simpa [bN] using hb, rfl⟩
    have hgen : ⁅Φ tN, Φ bN⁆ ∈ Kb := Subgroup.commutator_mem_commutator htTb hbBb
    have hne : ⁅Φ tN, Φ bN⁆ ≠ 1 := by
      rw [← map_commutatorElement]
      intro h1
      have hmem : ((⁅tN, bN⁆ : ↥N) : G) ∈ Subgroup.centralizer (ψ.range : Set G) :=
        (hΦker (⁅tN, bN⁆)).1 h1
      have hcoe : ((⁅tN, bN⁆ : ↥N) : G) = ⁅t, b⁆ := rfl
      exact hcomm (hcoe ▸ hmem)
    rw [hbot] at hgen
    exact hne (Subgroup.mem_bot.1 hgen)
  have hBb_le_R : Bb ≤ R := by
    intro hx hxmem
    obtain ⟨x, hxN, rfl⟩ := hxmem
    have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.1 hxN
    obtain ⟨c, hc⟩ := hind (x : G) hxB
    have hxeq : x = (⟨(x : G), hBLN hxB⟩ : ↥N) := Subtype.ext rfl
    rw [hxeq]
    refine ⟨⟨qTwoChartTwoThree_diag c, qtwoDB3_m2_diag_mem_uU h hF0 c⟩, ?_⟩
    exact (hstep3 (x : G) hxB c hc
      ⟨qTwoChartTwoThree_diag c, qtwoDB3_m2_diag_mem_uU h hF0 c⟩ rfl).symm
  have hKb_le_R : Kb ≤ R := by
    change ⁅Tb, Bb⁆ ≤ R
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact qtwoDB3_range_normal h hm x y (hBb_le_R hy)
  have hDh : ∀ c ∈ Dh, ∀ A : uU h m,
      (A : GL (Fin m) F0) = qTwoChartTwoThree_diag c →
      uConjAut h (by omega : 1 ≤ m) A ∈ Subgroup.normalizer (Kb : Set (MulAut P)) := by
    intro c hc A hA
    obtain ⟨b, hb, hbc⟩ := hc
    rw [← hstep3 b hb c hbc A hA]
    exact Subgroup.normalizer_commutator_ge_right Tb Bb
      (Subgroup.mem_map.2 ⟨⟨b, hBLN hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩)
  obtain ⟨U, hU1, hU2, hUu, hUnorm⟩ :=
    qtwoDB3_exists_U h hF0 hm Kb hKb2 hKb1 hKb_le_R Dh hDh
  exact qtwoDB3_borelTits hF0 (by omega : 2 ≤ m) Dh hdist U hU1 hU2 hUu hUnorm

end CFSG.StandardType.QTwo

end
