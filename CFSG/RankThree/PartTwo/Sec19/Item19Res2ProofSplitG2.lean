module

public import CFSG.RankThree.PartTwo.Sec19.KS1919G2P
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitG2Outer
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitG2Two
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Item19Res2Proof

theorem exists_fixed_E27_of_inner {Y : Type} [Group Y] [Finite Y]
    (hZ : Subgroup.center Y = ⊥) (E : Subgroup (MulAut Y))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (F : Subgroup (MulAut Y))
    (hFE : F ≤ E) (hFinn : F ≤ (MulAut.conj : Y →* MulAut Y).range) (hF9 : Nat.card F = 9)
    {c : MulAut Y} (hcE : c ∈ E) (hcF : c ∉ F)
    (hcI : c ∈ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ B : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27 ∧ ∀ y ∈ B, c y = y := by
  set I := (MulAut.conj : Y →* MulAut Y).range with hI
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcen : g ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 := congrArg (fun φ : MulAut Y => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc h * g = g * h * g⁻¹ * g := by rw [h1]
        _ = g * h := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set E' := E ⊓ I with hE'
  have hFE' : F ≤ E' := le_inf hFE hFinn
  have hcE' : c ∈ E' := ⟨hcE, hcI⟩
  have hdvd1 : Nat.card E' ∣ 27 := hE27 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hdvd2 : 9 ∣ Nat.card E' := hF9 ▸ Subgroup.card_dvd_of_le hFE'
  have hne9 : Nat.card E' ≠ 9 := by
    intro h9
    have : F = E' := Subgroup.eq_of_le_of_card_ge hFE' (by rw [h9, hF9])
    exact hcF (this ▸ hcE')
  have h27 : Nat.card E' = 27 := by
    obtain ⟨k, hk⟩ := hdvd2
    have hk27 : 9 * k ≤ 27 := hk ▸ Nat.le_of_dvd (by norm_num) hdvd1
    rw [hk] at hdvd1 hne9 ⊢
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> first | rfl | omega
  refine ⟨E'.comap MulAut.conj, ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun a ha => hinj ?_⟩,
    ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hcomm _ a.2.1 _ b.2.1
  · rw [map_pow, map_one]
    exact hE.2 _ ha.1
  · have hmap := Subgroup.map_comap_eq_self (show E' ≤ I from inf_le_right)
    rw [← h27]
    conv_rhs => rw [← hmap]
    rw [Subgroup.card_map_of_injective hinj]
  · intro y hy
    obtain ⟨y₀, rfl⟩ := hcI
    have h1 : MulAut.conj y₀ * MulAut.conj y = MulAut.conj y * MulAut.conj y₀ :=
      hcomm _ hcE _ hy.1
    rw [← map_mul, ← map_mul] at h1
    have h2 := hinj h1
    rw [MulAut.conj_apply, h2, mul_inv_cancel_right]

theorem center_eq_bot_of_isoGTwoEven
    {Y : Type} [Group Y] {n : ℕ} (hY : Sec8.IsoGTwoEven Y n) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := hY
  rw [eq_bot_iff]
  intro y hy
  have hey : e y ∈ Subgroup.center
      (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := Subgroup.mem_center_iff.mp hy (e.symm z)
    have h2 := congrArg e h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hey
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hey, map_one])

theorem ks1919SplitAut_g2
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 1 ≤ n)
    (hY : Sec8.IsoGTwoEven Y n) (E : Subgroup (MulAut Y))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (F : Subgroup (MulAut Y))
    (hFE : F ≤ E) (hFinn : F ≤ (MulAut.conj : Y →* MulAut Y).range) (hF9 : Nat.card F = 9)
    (c : MulAut Y) (hcE : c ∈ E) (hcF : c ∉ F) (P : Subgroup Y) (hP : IsProperParabolic P) :
    ¬ ∀ y : Y, c y = y → y ∈ P := by
  intro hfixP
  have hc3 : c ^ 3 = 1 := hE.2 c hcE
  by_cases hcI : c ∈ (MulAut.conj : Y →* MulAut Y).range
  · obtain ⟨B, hBe, hB27, hBfix⟩ := exists_fixed_E27_of_inner
      (center_eq_bot_of_isoGTwoEven hY) E hE hE27 F hFE hFinn hF9 hcE hcF hcI
    have hBP : B ≤ P := fun y hy => hfixP y (hBfix y hy)
    have hle := ks1919G2P Y n hY P hP B hBP
      (fun x hx y hy => congrArg Subtype.val (hBe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hBe.2
    omega
  · rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
    · exact hcI (inner_of_pow_three_of_g2Two hY hc3)
    · exact not_forall_fixed_mem_of_outer_iso hn2 hY hc3 hcI hP hfixP

end Item19Res2Proof

end CFSG.RankThree.PartTwo.Sec19
