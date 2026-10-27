module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem false_of_twoLocal_rank_four148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {T E : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 4)
    (hTE : E ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  have h1 := CFSG.LocalAnalysis.GLTheoremA.le_evenRank_of_quotient (G := ↥(Y ⊔ A))
    (N := ker148 A Y) Nat.prime_three (by norm_num) Main148.not_three_dvd_card_ker148 hT hT2 hE
    hEcard hTE
  have h2 := evenRank_subgroup_le (Y ⊔ A)
  have h3 := h.evenRank_eq
  omega

private theorem exists_mul_of_mem_sup_comm {H : Type*} [Group H] {S T : Subgroup H}
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : H} (hx : x ∈ S ⊔ T) :
    ∃ y ∈ S, ∃ z ∈ T, y * z = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, S.one_mem, 1, T.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := ihx
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := ihy
    have h := hcomm y2 hy2 z1 hz1
    refine ⟨y1 * y2, S.mul_mem hy1 hy2, z1 * z2, T.mul_mem hz1 hz2, ?_⟩
    calc y1 * y2 * (z1 * z2) = y1 * (y2 * z1) * z2 := by simp only [mul_assoc]
      _ = y1 * (z1 * y2) * z2 := by rw [h]
      _ = y1 * z1 * (y2 * z2) := by simp only [mul_assoc]
  | inv x _ ih =>
    obtain ⟨y, hy, z, hz, rfl⟩ := ih
    refine ⟨y⁻¹, S.inv_mem hy, z⁻¹, T.inv_mem hz, ?_⟩
    rw [hcomm y hy z hz, mul_inv_rev]

private theorem le_normalizer_of_le_centralizer' {H : Type*} [Group H] {S T : Subgroup H}
    (h : S ≤ Subgroup.centralizer (T : Set H)) : S ≤ Subgroup.normalizer (T : Set H) := by
  intro x hx
  have hc : ∀ x ∈ S, ∀ z ∈ T, x * z * x⁻¹ = z := fun x hx z hz => by
    rw [← (Subgroup.mem_centralizer_iff.mp (h hx) z hz), mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hc x hx y hy]
    exact hy
  · intro hy
    have h1 := hc x⁻¹ (S.inv_mem hx) _ hy
    rw [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
    rw [h1]
    exact hy

theorem false_of_commuting_rank_two148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J D T E₁ E₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hDJ : D ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) (hJD : J ⊓ D = ⊥)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hE₁J : E₁ ≤ J)
    (hE₁T : E₁ ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hE₁ : CFSG.Open.IsElemAbelian 3 E₁) (hE₁9 : Nat.card E₁ = 9) (hE₂D : E₂ ≤ D)
    (hE₂ : CFSG.Open.IsElemAbelian 3 E₂) (hE₂9 : Nat.card E₂ = 9) : False := by
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hDJ (hE₂D hy)) x (hE₁J hx)
  have hc₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc₂ : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEc : ∀ x ∈ E₁ ⊔ E₂, ∀ y ∈ E₁ ⊔ E₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_comm hcomm hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup_comm hcomm hy
    have h1 : x₂ * y₁ = y₁ * x₂ := (hcomm y₁ hy₁ x₂ hx₂).symm
    have h2 : y₂ * x₁ = x₁ * y₂ := (hcomm x₁ hx₁ y₂ hy₂).symm
    calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by simp only [mul_assoc]
      _ = x₁ * (y₁ * x₂) * y₂ := by rw [h1]
      _ = (x₁ * y₁) * (x₂ * y₂) := by simp only [mul_assoc]
      _ = (y₁ * x₁) * (y₂ * x₂) := by rw [hc₁ x₁ hx₁ y₁ hy₁, hc₂ x₂ hx₂ y₂ hy₂]
      _ = y₁ * (x₁ * y₂) * x₂ := by simp only [mul_assoc]
      _ = y₁ * (y₂ * x₁) * x₂ := by rw [h2]
      _ = y₁ * y₂ * (x₁ * x₂) := by simp only [mul_assoc]
  have hE : CFSG.Open.IsElemAbelian 3 (E₁ ⊔ E₂) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hEc x.1 x.2 y.1 y.2)⟩⟩, fun x hx => ?_⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_comm hcomm hx
    rw [(Commute.mul_pow (hcomm x₁ hx₁ x₂ hx₂) 3), hE₁.2 x₁ hx₁, hE₂.2 x₂ hx₂, one_mul]
  have hN : E₁ ≤ Subgroup.normalizer (E₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine le_normalizer_of_le_centralizer' fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hcomm x hx z hz).symm
  have hinf : E₁ ⊓ E₂ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hE₁J hE₂D).trans hJD.le)
  have hcard := Sec6.card_sup_mul_card_inf hN
  rw [hinf, Subgroup.card_bot, mul_one, hE₁9, hE₂9] at hcard
  have hE₂T : E₂ ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_normalizer_of_le_centralizer' (hE₂D.trans (hDJ.trans (Subgroup.centralizer_le hTJ)))
  exact false_of_twoLocal_rank_four148 h hT hT2 hE (by rw [hcard]; norm_num)
    (sup_le hE₁T hE₂T)

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
