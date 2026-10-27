module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Tau
public import CFSG.GH74.KGroups.Generic6

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45 L0S B0 P1 P2 xY Xs Xs_eq lattice D1_mem_P1 D1_not_mem_P2
  D2_mem_P2 D2_not_mem_P1 Dj normal_two_group_trivial)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 f45 exists_model)
open scoped Pointwise

theorem centralizer_Yh_trivial {r : Ah}
    (hr : ∀ y ∈ Yh, r * y = y * r) : r = 1 := by
  obtain ⟨M, hMP, hMA⟩ := exists_model (K := ↥QP45.originalSubgroup) (MulEquiv.refl _)
  have h1 : (r : P45) ∈ M.A := by rw [hMA]; exact r.2
  have h2 : (r : P45) = 1 := by
    refine M.centralizer_trivial h1 fun x hx => ?_
    rw [hMP] at hx
    have hxA : x ∈ QA45.originalSubgroup := Xs_le_A (Xs_eq ▸ hx)
    have := hr ⟨x, hxA⟩ ((mem_Yh_iff _).2 hx)
    exact congrArg Subtype.val this
  exact Subtype.ext h2

theorem Yh_normal : Yh.Normal :=
  Subgroup.normal_of_index_eq_two index_Yh

theorem normal_two_group_trivial_A
    {R : Subgroup Ah} (hR : R.Normal) (hp : IsPGroup 2 R) : R = ⊥ := by
  have := Yh_normal
  have hRY : (R ⊓ Yh).comap incl = ⊥ := by
    have hn : ((R ⊓ Yh).comap incl).Normal := Subgroup.Normal.comap inferInstance incl
    exact normal_two_group_trivial hn
      (IsPGroup.comap_of_injective (hp.to_le inf_le_left) incl incl_injective)
  have hinf : R ⊓ Yh = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl g).1 hg.2
    have : y ∈ (R ⊓ Yh).comap incl := hg
    rw [hRY, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  refine eq_bot_iff.2 fun r hr => ?_
  have hcomm : ∀ y ∈ Yh, r * y = y * r := by
    intro y hy
    have h1 : r * (y * r⁻¹ * y⁻¹) ∈ R := R.mul_mem hr (hR.conj_mem _ (R.inv_mem hr) y)
    have h2 : (r * y * r⁻¹) * y⁻¹ ∈ Yh :=
      Yh.mul_mem ((inferInstance : Yh.Normal).conj_mem y hy r) (Yh.inv_mem hy)
    have h3 : r * (y * r⁻¹ * y⁻¹) ∈ R ⊓ Yh := ⟨h1, by simpa [mul_assoc] using h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    calc r * y = r * y * r⁻¹ * y⁻¹ * y * r := by group
      _ = y * r := by
        have : r * y * r⁻¹ * y⁻¹ = 1 := by simpa [mul_assoc] using h3
        rw [this]; group
  exact (Subgroup.mem_bot).2 (centralizer_Yh_trivial hcomm)

theorem not_isTwoLocal_top_A :
    ¬ IsTwoLocal (⊤ : Subgroup Ah) := by
  rintro ⟨R, hR, hp, h⟩
  exact hR (normal_two_group_trivial_A (Subgroup.normalizer_eq_top_iff.1 h.symm) hp)

theorem lattice_Bh
    {H : Subgroup Ah} (hB : Bh ≤ H) : H = Bh ∨ H = P1h ∨ H = P2h ∨ H = ⊤ := by
  have hf : fhatA ∈ H := hB fhatA_mem_Bh
  have hK : B0 ≤ H.comap incl := by
    rw [← comap_Bh]
    exact Subgroup.comap_mono hB
  rcases lattice hK with h | h | h | h
  · exact Or.inl (eq_of_comap_eq hf fhatA_mem_Bh (h.trans comap_Bh.symm))
  · exact Or.inr (Or.inl (eq_of_comap_eq hf fhatA_mem_P1h (h.trans comap_P1h.symm)))
  · exact Or.inr (Or.inr (Or.inl (eq_of_comap_eq hf fhatA_mem_P2h (h.trans comap_P2h.symm))))
  · exact Or.inr (Or.inr (Or.inr (eq_of_comap_eq hf (Subgroup.mem_top _) (by rw [h]; rfl))))

theorem P1h_not_le_P2h : ¬ P1h ≤ P2h := fun h => by
  have h1 : incl (Dj 1) ∈ P1h := by rw [← Subgroup.mem_comap, comap_P1h]; exact D1_mem_P1
  have h2 := h h1
  rw [← Subgroup.mem_comap, comap_P2h] at h2
  exact D1_not_mem_P2 h2

theorem P2h_not_le_P1h : ¬ P2h ≤ P1h := fun h => by
  have h1 : incl (Dj 2) ∈ P2h := by rw [← Subgroup.mem_comap, comap_P2h]; exact D2_mem_P2
  have h2 := h h1
  rw [← Subgroup.mem_comap, comap_P1h] at h2
  exact D2_not_mem_P1 h2

theorem P1h_ne_P2h : P1h ≠ P2h := fun h =>
  P1h_not_le_P2h h.le

theorem Bh_le_P1h : Bh ≤ P1h := inf_le_left

theorem Bh_le_P2h : Bh ≤ P2h := inf_le_right

theorem P1h_le_normalizer_xA :
    P1h ≤ Subgroup.normalizer ((Subgroup.zpowers xA : Subgroup Ah) : Set Ah) := by
  intro g hg
  have hc : g * xA = xA * g := (mul_xA_comm_iff g).2 hg
  have hconj : g * xA * g⁻¹ = xA := by rw [hc]; simp
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ g' : Ah, g' * xA * g'⁻¹ = xA → ∀ h : Ah, h ∈ Subgroup.zpowers xA →
      g' * h * g'⁻¹ ∈ Subgroup.zpowers xA := by
    intro g' hg' h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [show g' * xA ^ n * g'⁻¹ = (g' * xA * g'⁻¹) ^ n by simp [conj_zpow], hg']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers xA) n
  constructor
  · exact key g hconj h
  · intro hh
    have hconj' : g⁻¹ * xA * g = xA := by
      calc g⁻¹ * xA * g = g⁻¹ * (xA * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * xA) := by rw [hc]
        _ = xA := by rw [← mul_assoc]; simp
    have := key g⁻¹ (by simpa using hconj') _ hh
    simpa [mul_assoc] using this

theorem xA_isPGroup : IsPGroup 2 (Subgroup.zpowers xA) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : xA ^ 2 = 1 := by rw [pow_two]; exact xA_sq
  exact IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hx2 xA_ne_one]; norm_num)

theorem normalizer_xA :
    Subgroup.normalizer ((Subgroup.zpowers xA : Subgroup Ah) : Set Ah) = P1h := by
  have hP1 := P1h_le_normalizer_xA
  rcases lattice_Bh (Bh_le_P1h.trans hP1) with h | h | h | h
  · exact absurd ((h ▸ hP1 : P1h ≤ Bh).trans Bh_le_P2h) P1h_not_le_P2h
  · exact h
  · exact absurd (h ▸ hP1 : P1h ≤ P2h) P1h_not_le_P2h
  · exfalso
    have hnorm : (Subgroup.zpowers xA).Normal := Subgroup.normalizer_eq_top_iff.1 h
    have := normal_two_group_trivial_A hnorm xA_isPGroup
    have h1 : xA ∈ (⊥ : Subgroup Ah) := this ▸ Subgroup.mem_zpowers xA
    exact xA_ne_one (Subgroup.mem_bot.1 h1)

theorem P1h_isTwoLocal :
    IsTwoLocal P1h :=
  ⟨Subgroup.zpowers xA, fun h => by
    have h1 : xA ∈ (⊥ : Subgroup Ah) := h ▸ Subgroup.mem_zpowers xA
    exact xA_ne_one (Subgroup.mem_bot.1 h1), xA_isPGroup, normalizer_xA.symm⟩

theorem normalizer_VA :
    Subgroup.normalizer (VA : Set Ah) = P2h := by
  have hP2 : P2h ≤ Subgroup.normalizer (VA : Set Ah) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => P2h_conj_VA hg hh, fun hh => by
      have := P2h_conj_VA (P2h.inv_mem hg) hh
      simpa [mul_assoc] using this⟩
  rcases lattice_Bh (Bh_le_P2h.trans hP2) with h | h | h | h
  · exact absurd ((h ▸ hP2 : P2h ≤ Bh).trans Bh_le_P1h) P2h_not_le_P1h
  · exact absurd (h ▸ hP2 : P2h ≤ P1h) P2h_not_le_P1h
  · exact h
  · exfalso
    have hnorm : VA.Normal := Subgroup.normalizer_eq_top_iff.1 h
    exact VA_ne_bot (normal_two_group_trivial_A hnorm VA_isPGroup)

theorem P2h_isTwoLocal :
    IsTwoLocal P2h :=
  ⟨VA, VA_ne_bot, VA_isPGroup, normalizer_VA.symm⟩

theorem isMaximalTwoLocal_P1h :
    IsMaximalTwoLocal P1h := by
  refine ⟨P1h_isTwoLocal, fun M hM hle => ?_⟩
  rcases lattice_Bh (Bh_le_P1h.trans hle) with h | h | h | h
  · exact absurd ((h ▸ hle : P1h ≤ Bh).trans Bh_le_P2h) P1h_not_le_P2h
  · exact h
  · exact absurd (h ▸ hle : P1h ≤ P2h) P1h_not_le_P2h
  · exact absurd (h ▸ hM) not_isTwoLocal_top_A

theorem isMaximalTwoLocal_P2h :
    IsMaximalTwoLocal P2h := by
  refine ⟨P2h_isTwoLocal, fun M hM hle => ?_⟩
  rcases lattice_Bh (Bh_le_P2h.trans hle) with h | h | h | h
  · exact absurd ((h ▸ hle : P2h ≤ Bh).trans Bh_le_P1h) P2h_not_le_P1h
  · exact absurd (h ▸ hle : P2h ≤ P1h) P2h_not_le_P1h
  · exact h
  · exact absurd (h ▸ hM) not_isTwoLocal_top_A

end CFSG.Quasithin.H13.F431.U42Aut
