module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ToralFinishPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart7

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ToralFinish
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.PartOne.KE
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.StandardType.F4ExplicitPos.ToralBlocks
open CFSG.StandardType.F4ExplicitPos.ToralDescent

theorem isToralSubgroup_F4_of_card_le_sq
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (ModGL Tag.F4 L)}
    (hA : A ≤ adjointGroup Tag.F4 L) (hfin : Finite A) (hel : IsElemAbelian p A)
    (hcard : Nat.card A ≤ p ^ 2) : IsToralSubgroup Tag.F4 L A := by
  by_cases hp3 : p = 3
  ·
    subst p
    have : Fact (Nat.Prime 3) := ⟨hp⟩
    have : Finite A := hfin
    have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hisP : IsPGroup 3 A := by
      intro y
      have hy : y ^ 3 = 1 := Subtype.ext (by simpa using hel.2 y y.2)
      have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy
      rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
      · exact ⟨0, by rw [pow_zero, pow_one]; exact orderOf_eq_one_iff.mp h⟩
      · exact ⟨1, by rw [pow_one]; exact hy⟩
    obtain ⟨k, hk⟩ : ∃ k, Nat.card A = 3 ^ k := IsPGroup.iff_card.1 hisP
    have hk2 : k ≤ 2 := by
      have h := hcard
      rw [hk] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
    have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkcases with rfl | rfl | rfl
    ·
      have hbot : A = ⊥ := by
        apply Subgroup.card_eq_one.mp
        simpa using hk
      refine ⟨1, Subgroup.one_mem _, fun x hx => ?_⟩
      have hx1 : x = 1 := by
        have : x ∈ (⊥ : Subgroup (ModGL Tag.F4 L)) := hbot ▸ hx
        exact Subgroup.mem_bot.mp this
      simp [hx1]
    ·
      have hcardp : Nat.card A = 3 := by simpa using hk
      have hAne : A ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcardp
        exact (by norm_num : (3 : ℕ) ≠ 1) hcardp.symm
      obtain ⟨⟨x, hxA⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
      have hx : x ∈ adjointGroup Tag.F4 L := hA hxA
      have hxp : x ^ 3 = 1 := hel.2 x hxA
      have hgen : Subgroup.zpowers x = A := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxA) ?_
        simp [hcardp, Nat.card_zpowers, orderOf_eq_prime hxp (fun h => hx1 (Subtype.ext h))]
      obtain ⟨g, hg, hgx⟩ := exists_conj_torusGroup_of_pow_eq_one_three_F4 (L := L) halg hx hxp
      refine ⟨g, hg, fun y hy => ?_⟩
      have hle : Subgroup.zpowers x ≤
          (torusGroup Tag.F4 L).comap (MulAut.conj g⁻¹).toMonoidHom :=
        Subgroup.zpowers_le.2 (by simpa [MulAut.conj_apply] using hgx)
      rw [hgen] at hle
      exact hle hy
    ·
      have hcard2 : Nat.card A = 3 ^ 2 := hk
      have hstab : ∀ a : Fin Tag.F4.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
          rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := fun a ha =>
        (ThreeExact.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three_without13604
          (K := L) a ha).le
      obtain ⟨C, hC, hCA⟩ :=
        exists_conj_le_torusGroup_of_plane_three_F4 (L := L) halg hstab hA hcomm hel.2 hcard2
      exact ⟨C⁻¹, inv_mem hC, fun x hx => by simpa using hCA x hx⟩
  ·
    have h3p : 3 < p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    exact isToralSubgroup_of_not_dvd_weyl_F4 (L := L) halg hp hp2
      (not_dvd_card_weylGroup_F4 hp h3p) hA hfin hel

end CFSG.StandardType.F4ExplicitPos.ToralFinish

end

end
