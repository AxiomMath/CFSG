module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwoLocal
import CFSG.RankThree.PartTwo.Sec14.Ronan148JProd
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
import CFSG.RankThree.PartTwo.Sec4.Ronan148VON
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.HardMathSupport.Solomon.Coordinator.T112TTONTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Sporadic.Bridge.ONSurj

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem false_of_commuting_twoLocal148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J T E₁ E₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hE₁J : E₁ ≤ J)
    (hE₁T : E₁ ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hE₁ : CFSG.Open.IsElemAbelian 3 E₁)
    (hE₂C : E₂ ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hE₂ : CFSG.Open.IsElemAbelian 3 E₂) (hint : E₁ ⊓ E₂ = ⊥)
    (hcard : Nat.card E₁ * Nat.card E₂ = 81) : False := by
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hE₂C hy) x (hE₁J hx)
  have hc₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc₂ : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmem : ∀ x ∈ E₁ ⊔ E₂, ∃ x₁ ∈ E₁, ∃ x₂ ∈ E₂, x = x₁ * x₂ := by
    intro x hx
    rw [← Ronan148J.commProdHom_range hcomm] at hx
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨x₁, x₁.2, x₂, x₂.2, Ronan148J.commProdHom_apply hcomm _⟩
  have hE : CFSG.Open.IsElemAbelian 3 (E₁ ⊔ E₂) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := hmem x.1 x.2
      obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := hmem y.1 y.2
      change (x : ↥(Y ⊔ A) ⧸ ker148 A Y) * y = y * x
      rw [hx, hy]
      have h1 : x₂ * y₁ = y₁ * x₂ := (hcomm y₁ hy₁ x₂ hx₂).symm
      have h2 : y₂ * x₁ = x₁ * y₂ := (hcomm x₁ hx₁ y₂ hy₂).symm
      calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by simp only [mul_assoc]
        _ = x₁ * (y₁ * x₂) * y₂ := by rw [h1]
        _ = (x₁ * y₁) * (x₂ * y₂) := by simp only [mul_assoc]
        _ = (y₁ * x₁) * (y₂ * x₂) := by rw [hc₁ x₁ hx₁ y₁ hy₁, hc₂ x₂ hx₂ y₂ hy₂]
        _ = y₁ * (x₁ * y₂) * x₂ := by simp only [mul_assoc]
        _ = y₁ * (y₂ * x₁) * x₂ := by rw [h2]
        _ = y₁ * y₂ * (x₁ * x₂) := by simp only [mul_assoc]
    · obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hmem x hx
      rw [(Commute.mul_pow (hcomm x₁ hx₁ x₂ hx₂) 3), hE₁.2 x₁ hx₁, hE₂.2 x₂ hx₂, one_mul]
  have hN : E₁ ≤ Subgroup.normalizer (E₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (hcomm x hx z hz).symm)
  have hcard' := Sec6.card_sup_mul_card_inf hN
  rw [hint, Subgroup.card_bot, mul_one, hcard] at hcard'
  have hE₂T : E₂ ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ ((Subgroup.centralizer_le hTJ) (hE₂C hx))
  exact false_of_twoLocal_rank_four148 h hT hT2 hE (by rw [hcard']; norm_num)
    (sup_le hE₁T hE₂T)

theorem map_conj_eq_of_twoLocal148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J T E₁ F : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hJ : IsComponent J) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hE₁J : E₁ ≤ J)
    (hE₁T : E₁ ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hE₁ : CFSG.Open.IsElemAbelian 3 E₁) (hFJ : F ≤ J) (hF : CFSG.Open.IsElemAbelian 3 F)
    (hFZ : F ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥)
    (hcard : Nat.card E₁ * Nat.card F = 81) (x : ↥(Y ⊔ A) ⧸ ker148 A Y) :
    J.map (MulAut.conj x).toMonoidHom = J := by
  by_contra hne
  set D := J.map (MulAut.conj x).toMonoidHom with hD
  have hDc : IsComponent D := Res2LBal.isComponent_conj hJ x
  have hDC : D ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun y hy =>
    Res2LBal.mem_centralizer_of_mem_of_ne hJ hDc (fun h' => hne h'.symm) hy
  set E₂ := F.map (MulAut.conj x).toMonoidHom with hE₂
  have hE₂D : E₂ ≤ D := Subgroup.map_mono hFJ
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hint : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy₁, hy₂⟩
    obtain ⟨f, hf, rfl⟩ := hy₂
    have hfC : f ∈ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hc := Subgroup.mem_centralizer_iff.mp (hDC (Res2LBal.conj_mem_map hj x))
        ((MulAut.conj x).toMonoidHom f) (hE₁J hy₁)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
      have : x * (f * j) * x⁻¹ = x * (j * f) * x⁻¹ := by
        calc x * (f * j) * x⁻¹ = x * f * x⁻¹ * (x * j * x⁻¹) := by group
          _ = x * j * x⁻¹ * (x * f * x⁻¹) := hc
          _ = x * (j * f) * x⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel this)).symm
    have : f ∈ F ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := ⟨hf, hfC⟩
    rw [hFZ, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  exact false_of_commuting_twoLocal148 h hT hT2 hTJ hE₁J hE₁T hE₁ (hE₂D.trans hDC)
    (CFSG.SectionRank.isElemAbelian_map hF _) hint
    (by rw [Subgroup.card_map_of_injective hinj]; exact hcard)

theorem exists_twoLocal_rank_three_of_tripleCover_ON
    {X : Type} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) (hXp : Group.IsPerfect X) :
    ∃ T E : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 27 ∧ E ≤ Subgroup.normalizer (T : Set X) := by
  obtain ⟨hZ, ⟨e⟩⟩ := hX
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have hK : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON X :=
    ⟨Group.isPerfect_def.mp hXp, hZ, ⟨e.trans b⟩⟩
  have h3 := CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_TON_twoLocal_holds X hK
  obtain ⟨E, T, hE, hEc, hT2, hT, hET⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.D4XF.exists_E27_of_three_le_twoLocalPrimeRank h3
  exact ⟨T, E, hT, hT2, hE, by rw [hEc]; norm_num, hET⟩

theorem map_conj_eq_of_tripleCover_ON148
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G} [(ker148 A Y).Normal]
    {J : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hJ : IsComponent J)
    (hJON : Sec4.IsTripleCover ↥J CFSG.Blueprint.NativeSporadic.ON)
    (x : ↥(Y ⊔ A) ⧸ ker148 A Y) : J.map (MulAut.conj x).toMonoidHom = J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, E, hT, hT2, hE, hEc, hET⟩ :=
    exists_twoLocal_rank_three_of_tripleCover_ON hJON hJ.1.1
  obtain ⟨u, hu3, huZ⟩ := Sec4.Ronan148V.exists_noncentral_of_isTripleCover_ON hJON
  have hinj : Function.Injective J.subtype := J.subtype_injective
  have hu1 : u ≠ 1 := fun h1 => huZ (h1 ▸ Subgroup.one_mem _)
  have hu1' : (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hu3' : (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hu3
  have hFJ : Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ≤ J :=
    Subgroup.zpowers_le.mpr u.2
  have hF : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
      change (a : ↥(Y ⊔ A) ⧸ ker148 A Y) * b = b * a
      rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3', one_zpow]
  have hFc : Nat.card (Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3' hu1']
  have hFZ : Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ⊓
      Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ⊓
        Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ∣ 3 :=
      hFc ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ⊓
          Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
            Subgroup.zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y)) (by rw [hFc, h1])
      have huC : (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈
          Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
        (heq.symm ▸ Subgroup.mem_zpowers (u : ↥(Y ⊔ A) ⧸ ker148 A Y)).2
      apply huZ
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp huC g g.2)
  refine map_conj_eq_of_twoLocal148 h hJ ((Subgroup.map_eq_bot_iff_of_injective T hinj).not.mpr hT)
    (hT2.map _) (Subgroup.map_subtype_le T) (Subgroup.map_subtype_le E)
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _))
    (CFSG.SectionRank.isElemAbelian_map hE _) hFJ hF hFZ ?_ x
  rw [Subgroup.card_map_of_injective hinj, hEc, hFc]

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
