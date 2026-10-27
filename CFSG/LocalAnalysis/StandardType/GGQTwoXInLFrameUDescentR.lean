module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUniLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniLift
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniPSU2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem ggQTUdR_exists_unitaryInvolution {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2) :
    ∃ τ : K ≃+* K, (∀ x, τ (τ x) = x) ∧ ∀ x, τ x = x ^ 2 ^ m := by
  have h := unitaryFieldData_of_card hm hK
  let τ : K ≃+* K := RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun y => ⟨h.bar y, h.bar_bar y⟩⟩
  exact ⟨τ, fun x => h.bar_bar x, fun x => h.bar_apply x⟩

private theorem ggQTUdR_label_eq_of_iso {lab : LargeEvenLabel} {a n : ℕ}
    (h : GGLabelIso lab ⟨.twA, a, n⟩)
    (htag : lab.tag = .twE6 ∨ lab.tag = .twA) : lab = ⟨.twA, a, n⟩ := by
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · obtain ⟨-, hB | hB, -, -⟩ := h
    · cases hB
    · cases hB
  · obtain ⟨-, h2⟩ := h; cases h2
  · obtain ⟨-, h2⟩ := h; cases h2
  · obtain ⟨h1, -⟩ := h
    rcases htag with h' | h'
    · rw [h1] at h'; cases h'
    · rw [h1] at h'; cases h'
  · obtain ⟨-, h2⟩ := h; cases h2
  · obtain ⟨h1, -⟩ := h
    rcases htag with h' | h'
    · rw [h1] at h'; cases h'
    · rw [h1] at h'; cases h'
  · obtain ⟨h2, -⟩ := h; cases h2

private theorem ggQTUdR_false_of_iso_A {lab : LargeEvenLabel} {b n : ℕ}
    (htag : lab.tag = .twE6 ∨ lab.tag = .twA)
    (h : GGLabelIso lab ⟨.A, b, n⟩) : False := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h] at htag
    rcases htag with h' | h' <;> cases h'
  · obtain ⟨-, hB | hB, -, -⟩ := h
    · cases hB
    · cases hB
  · obtain ⟨h1, -⟩ := h
    rcases htag with h' | h'
    · rw [h1] at h'; cases h'
    · rw [h1] at h'; cases h'
  · obtain ⟨-, h2⟩ := h; cases h2
  · obtain ⟨-, h2⟩ := h; cases h2
  · obtain ⟨-, h2⟩ := h; cases h2
  · obtain ⟨h1, -⟩ := h
    rcases htag with h' | h'
    · rw [h1] at h'; cases h'
    · rw [h1] at h'; cases h'
  · obtain ⟨h2, -⟩ := h; cases h2

theorem ggQTwoXInLU_descentR
    {N m : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2) (hN : 3 ≤ N)
    (hNq : (N, 2 ^ m) ≠ (3, 2))
    {u : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hu : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))
      (LargeEvenGUSet (Fin N) K (2 ^ m)))
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    {J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (htag : lab.tag = .twE6 ∨ (lab.tag = .twA ∧ 5 ≤ lab.rank))
    (hJlab : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    m = 1 ∧ lab.tag = .twA ∧ lab.rank + 2 ≤ N := by
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst hm0
    norm_num at hK
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨τ, hτ, hτQ⟩ := ggQTUdR_exists_unitaryInvolution (m := m) hm hK
  obtain ⟨s, hsN, hs_held, hs_proj⟩ :=
    q1CentUni_exists_lift (d := N) (m := m) hK hm τ hτ hτQ hu
  have hsp : TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m)) ⟨s, hsN⟩ ^ 3 = 1 := by
    rw [← hs_proj]
    exact hu3
  have hsp_scal : s ^ 3 ∈ LargeEvenScalars (Fin N) K :=
    q1CentUni_pow_mem_scalars (d := N) (m := m) hK hm hN hNq hsN hsp
  have hso : Odd (orderOf s) :=
    q1CentUni_odd_orderOf (d := N) (m := m) hK hm (p := 3) (by norm_num) hsp_scal
  have hJc : CFSG.Open.IsComponentOf J
      (ggAutFixedSubgroup (TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m)) ⟨s, hsN⟩)) := by
    rw [← hs_proj]
    exact hJ
  obtain ⟨C, hC, hCSU, hJeq⟩ :=
    q1TorUni_component_lift (d := N) (m := m) (K := K) τ hτ hτQ s hs_held hsN J hJc
  have hblock :=
    q2Uni_blockType (N := N) (m := m) hK τ hτ hτQ s hs_held hso C hC hCSU J hJeq
  rcases hblock with
    ⟨a, k, D, iD, hD, hk, ha2, hak, hne2, hne3, ⟨iso⟩⟩ |
    ⟨b, k, D, iD, hDFin, hk, hb2, hbk, hDcard, ⟨iso⟩⟩
  ·
    letI : Field D := iD
    letI : Finite D := hD.finite
    rcases Nat.lt_or_ge a 3 with ha3 | ha3
    ·
      exfalso
      obtain rfl : a = 2 := by omega
      have hmk2 : 2 ≤ m * k := by
        have hmk_pos : 0 < m * k := Nat.mul_pos (by omega) (by omega)
        by_contra h
        exact hne2 ⟨rfl, by omega⟩
      haveI : CharP D 2 := hD.charP
      obtain ⟨F, iF, hFfin, hFcard, ⟨e⟩⟩ := TablePThreeKG.psu2_equiv_psl2 (K := D) hD.card_eq_sq
      have hΛA : LargeEvenInLambda2 ⟨.A, 1, m * k⟩ := by
        dsimp only [LargeEvenInLambda2]
        exact ⟨by omega, by omega, fun _ => hmk2⟩
      have hHasA : GGHasLabel ⟨.A, 1, m * k⟩ (↥J ⧸ Subgroup.center ↥J) := by
        dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
        exact ⟨F, iF, hFfin, hFcard, ⟨iso.trans e⟩⟩
      exact ggQTUdR_false_of_iso_A
        (by rcases htag with h | ⟨h, -⟩
            · exact Or.inl h
            · exact Or.inr h)
        (ggLabelRigidInput_holds lab ⟨.A, 1, m * k⟩
          (↥J ⧸ Subgroup.center ↥J) hΛ hΛA hJlab hHasA)
    have hΛ' : LargeEvenInLambda2 ⟨.twA, a - 1, m * k⟩ := by
      dsimp only [LargeEvenInLambda2]
      refine ⟨?_, ?_, ?_⟩
      · have hm_le_mk : m ≤ m * k := Nat.le_mul_of_pos_right m (by omega : 0 < k)
        omega
      · have ha_le_ak : a ≤ a * k := Nat.le_mul_of_pos_right a (by omega : 0 < k)
        omega
      · intro h
        have ha3 : a = 3 := by omega
        have hmk_ne : m * k ≠ 1 := fun h1 => hne3 ⟨ha3, h1⟩
        have hmk_pos : 0 < m * k := Nat.mul_pos (by omega) (by omega)
        omega
    have hHas' : GGHasLabel ⟨.twA, a - 1, m * k⟩ (↥J ⧸ Subgroup.center ↥J) := by
      dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
      refine ⟨D, iD, hD.finite, hD.card_eq_sq, ?_⟩
      rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
      exact ⟨iso⟩
    have hlab : lab = ⟨.twA, a - 1, m * k⟩ :=
      ggQTUdR_label_eq_of_iso
        (ggLabelRigidInput_holds lab ⟨.twA, a - 1, m * k⟩
          (↥J ⧸ Subgroup.center ↥J) hΛ hΛ' hJlab hHas')
        (by rcases htag with h | ⟨h, -⟩
            · exact Or.inl h
            · exact Or.inr h)
    have hmk1 : m * k = 1 := by
      have h := congrArg LargeEvenLabel.n hlab
      rw [hn] at h
      simpa using h.symm
    have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right hmk1
    have hk1 : k = 1 := Nat.eq_one_of_mul_eq_one_left hmk1
    have haN : a ≠ N := by
      intro haN
      have hHasJ : GGHasLabel ⟨.twA, N - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
        have h := hHas'
        rw [haN] at h
        simpa [hmk1] using h
      have hHasR : GGHasLabel ⟨.twA, N - 1, 1⟩
          (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) := by
        subst hm1
        dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
        refine ⟨K, inferInstance, inferInstance, ?_, ?_⟩
        · exact hK
        · rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
          exact ⟨MulEquiv.refl _⟩
      obtain ⟨e⟩ := nonempty_mulEquiv_of_ggHasLabel hHasJ hHasR
      have hcardQ : Nat.card (↥J ⧸ Subgroup.center ↥J) =
          Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) :=
        Nat.card_congr e.toEquiv
      have hcardQJ : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥J :=
        Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_quotient_dvd_card _)
      have hcardJR : Nat.card ↥J ≤
          Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) :=
        Subgroup.card_le_card_group J
      have hcardJ : Nat.card ↥J =
          Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) := by omega
      have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J hcardJ
      have hfix : ggAutFixedSubgroup u = ⊤ :=
        top_le_iff.mp (by rw [← hJtop]; exact hJ.1)
      apply hu1
      apply MulEquiv.ext
      intro r
      have hr : r ∈ ggAutFixedSubgroup u := by rw [hfix]; exact Subgroup.mem_top r
      simpa using (mem_ggAutFixedSubgroup u r).mp hr
    refine ⟨hm1, ?_, ?_⟩
    · rw [hlab]
    · have hale : a ≤ N := by
        have ha_le_ak : a ≤ a * k := Nat.le_mul_of_pos_right a (by omega : 0 < k)
        omega
      rw [hlab]
      have ha_lt_N : a < N := lt_of_le_of_ne hale haN
      show a - 1 + 2 ≤ N
      omega
  ·
    letI : Field D := iD
    letI : Finite D := hDFin
    have hΛA : LargeEvenInLambda2 ⟨.A, b - 1, 2 * (m * k)⟩ := by
      dsimp only [LargeEvenInLambda2]
      refine ⟨?_, ?_, ?_⟩
      · have hmk_pos : 0 < m * k := Nat.mul_pos (by omega) (by omega)
        have h2 : 2 ≤ 2 * (m * k) := Nat.le_mul_of_pos_right 2 hmk_pos
        omega
      · omega
      · intro h
        have hb : b = 2 := by omega
        have hmk_pos : 0 < m * k := Nat.mul_pos (by omega) (by omega)
        have h2 : 2 ≤ 2 * (m * k) := Nat.le_mul_of_pos_right 2 hmk_pos
        omega
    have hHasA : GGHasLabel ⟨.A, b - 1, 2 * (m * k)⟩ (↥J ⧸ Subgroup.center ↥J) := by
      have hmod : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL ((b - 1) + 1) 2
          (2 * (m * k)) := by
        refine ⟨?_, D, inferInstance, inferInstance, hDcard, ?_⟩
        · have hmk_pos : 0 < m * k := Nat.mul_pos (by omega) (by omega)
          have h2 : 2 ≤ 2 * (m * k) := Nat.le_mul_of_pos_right 2 hmk_pos
          refine ⟨Nat.prime_two, by omega, ?_⟩
          have h4 : 4 ≤ 2 ^ (2 * (m * k)) := by
            have h1 : 2 ≤ 2 * (m * k) := by
              exact Nat.le_mul_of_pos_right 2 hmk_pos
            have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h1
            norm_num at this ⊢
            exact this
          refine ⟨by omega, ?_, ?_⟩
          · rintro h
            exact absurd (congrArg Prod.snd h) (by omega)
          · rintro h
            exact absurd (congrArg Prod.snd h) (by omega)
        · rw [Nat.sub_add_cancel (by omega : 1 ≤ b)]
          exact ⟨iso⟩
      exact ggHasLabel_typeA (n := b - 1) (f := 2 * (m * k)) hmod
    exact (ggQTUdR_false_of_iso_A
      (by rcases htag with h | ⟨h, -⟩
          · exact Or.inl h
          · exact Or.inr h)
      (ggLabelRigidInput_holds lab ⟨.A, b - 1, 2 * (m * k)⟩
        (↥J ⧸ Subgroup.center ↥J) hΛ hΛA hJlab hHasA)).elim

end CFSG.StandardType

end
