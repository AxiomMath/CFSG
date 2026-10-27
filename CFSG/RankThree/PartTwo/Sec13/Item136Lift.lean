module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

section Lift

variable {H : Type*} [Group H] [Finite H]

theorem exists_isPGroup_le_map_eq {M : Subgroup H}
    {B : Subgroup (H ⧸ aschbacherSolvableCore 3 H)} (hB : IsPGroup 3 B)
    (hBM : B ≤ M.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)))
    {E : Subgroup H} (hE : IsPGroup 3 E) (hEM : E ≤ M)
    (hEB : E.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≤ B) :
    ∃ S : Subgroup H, E ≤ S ∧ S ≤ M ∧ IsPGroup 3 S ∧
      S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) = B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H)
  set Y := M ⊓ B.comap π
  have hEY : E ≤ Y := le_inf hEM (Subgroup.map_le_iff_le_comap.mp hEB)
  have hE' : IsPGroup 3 (E.subgroupOf Y) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEY).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  refine ⟨(Q : Subgroup Y).map Y.subtype, ?_, ?_, Q.isPGroup'.map _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hEY hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2.1
  · apply le_antisymm
    · rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact y.2.2
    · intro b hb
      let ψ : Y →* B := (π.comp Y.subtype).codRestrict B (fun y => y.2.2)
      have hψ : Function.Surjective ψ := by
        rintro ⟨b, hb⟩
        obtain ⟨h, hh, rfl⟩ := hBM hb
        exact ⟨⟨h, hh, hb⟩, rfl⟩
      have hBtop : IsPGroup 3 (⊤ : Subgroup B) := hB.of_equiv Subgroup.topEquiv.symm
      have htop := ((Q.mapSurjective hψ).is_maximal' hBtop le_top).symm
      rw [Sylow.coe_mapSurjective] at htop
      have hmem : (⟨b, hb⟩ : B) ∈ (Q : Subgroup Y).map ψ := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyb⟩ := hmem
      exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyb⟩

theorem card_map_eq_of_injOn {M M' : Type*} [Group M] [Group M'] (f : M →* M')
    {S : Subgroup M} (h : Set.InjOn f S) : Nat.card (S.map f) = Nat.card S := by
  have := Nat.card_image_of_injOn h
  rw [← Subgroup.coe_map] at this
  exact this

theorem exists_elemAbelian_map_eq {M : Subgroup H}
    {B : Subgroup (H ⧸ aschbacherSolvableCore 3 H)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBM : B ≤ M.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) :
    ∃ S : Subgroup H, S ≤ M ∧ CFSG.Assembly.IsElemAbelian 3 S ∧ Nat.card S = Nat.card B ∧
      S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) = B := by
  have hBp : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hB.2 b b.2)⟩
  obtain ⟨S, -, hSM, hS3, hSB⟩ := exists_isPGroup_le_map_eq hBp hBM IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => by
    have := hB.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hmemB : ∀ s ∈ S, QuotientGroup.mk' (aschbacherSolvableCore 3 H) s ∈ B := fun s hs =>
    hSB ▸ Subgroup.mem_map_of_mem _ hs
  refine ⟨S, hSM, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun s hs => ?_⟩, ?_, hSB⟩
  · refine hinj (S.mul_mem a.2 b.2) (S.mul_mem b.2 a.2) ?_
    simp only [Subgroup.coe_mul, map_mul]
    exact hBc _ (hmemB _ a.2) _ (hmemB _ b.2)
  · refine hinj (S.pow_mem hs 3) S.one_mem ?_
    rw [map_pow, hB.2 _ (hmemB s hs), map_one]
  · rw [← hSB, card_map_eq_of_injOn _ hinj]

end Lift

end CFSG.RankThree.PartTwo.Sec13
