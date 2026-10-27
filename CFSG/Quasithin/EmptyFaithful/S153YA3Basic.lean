module

public import CFSG.Quasithin.EmptyFaithful.S153YGSet
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs

public section

namespace CFSG.Quasithin.YG.DoubleA3

open CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G} {s : G}

structure A3A3 {G : Type} [Group G] [Finite G] (H S L : Subgroup G) (s : G) : Prop where
  cs : WGen H S L
  a3 : IsAltType L 3
  s_mem : s ∈ S
  s_ne : conjR L s ≠ L
  join : conjJoin S L = L ⊔ conjR L s
  comm : ⁅L, conjR L s⁆ = ⊥


namespace A3A3

theorem isShort (h : A3A3 H S L s) : IsShort2 L := h.cs.block.1.1

theorem isA4 (h : A3A3 H S L s) : IsA4Block L (blockU L) :=
  IsA4Block.of_alt3 h.isShort h.a3

theorem isA4s (h : A3A3 H S L s) : IsA4Block (conjR L s) (blockU2 L s) :=
  h.isA4.conj s

theorem comm_elem (h : A3A3 H S L s) : ∀ a ∈ L, ∀ b ∈ conjR L s, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.comm
  exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm

theorem inf_Ls (h : A3A3 H S L s) : L ⊓ conjR L s = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgL, hgLs⟩
  have := h.isA4.center_L g hgL (fun l hl => (h.comm_elem l hl g hgLs).symm)
  rw [this]; exact one_mem _

theorem center_L0 (h : A3A3 H S L s) :
    ∀ g ∈ conjJoin S L, (∀ l ∈ conjJoin S L, g * l = l * g) → g = 1 := by
  intro g hg hc
  rw [h.join] at hg hc
  have hg' : g ∈ ((L ⊔ conjR L s : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L (conjR L s)
    (C5.le_normalizer_of_commute h.comm_elem)] at hg'
  obtain ⟨a, ha, b, hb, hab0⟩ := hg'
  have hab : a * b = g := hab0
  have ha1 : a = 1 := h.isA4.center_L a ha (fun l hl => by
    have h1 := hc l (mem_sup_left hl)
    have h2 : b * l = l * b := (h.comm_elem l hl b hb).symm
    have h3 : a * l * b = l * a * b := by
      calc a * l * b = a * (l * b) := by group
        _ = a * (b * l) := by rw [h2]
        _ = g * l := by rw [← hab]; group
        _ = l * g := h1
        _ = l * a * b := by rw [← hab]; group
    exact mul_right_cancel h3)
  have hb1 : b = 1 := h.isA4s.center_L b hb (fun l hl => by
    have h1 := hc l (mem_sup_right hl)
    have h2 : a * l = l * a := h.comm_elem a ha l hl
    have h3 : a * (b * l) = a * (l * b) := by
      calc a * (b * l) = g * l := by rw [← hab]; group
        _ = l * g := h1
        _ = l * a * b := by rw [← hab]; group
        _ = (a * l) * b := by rw [h2]
        _ = a * (l * b) := by group
    exact mul_left_cancel h3)
  rw [← hab, ha1, hb1, one_mul]

theorem V_isPGroup (h : A3A3 H S L s) : IsPGroup 2 ↥(blockU L ⊔ blockU2 L s) := by
  have hA := h.isA4
  have hAs := h.isA4s
  have hUU : ∀ a ∈ blockU L, ∀ b ∈ blockU2 L s, a * b = b * a := fun a ha b hb =>
    h.comm_elem a (hA.le ha) b (hAs.le hb)
  have hUN : blockU L ≤ normalizer (blockU2 L s : Set G) := C5.le_normalizer_of_commute hUU
  intro g
  have hg : (g : G) ∈ ((blockU L ⊔ blockU2 L s : Subgroup G) : Set G) := g.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (blockU L) (blockU2 L s) hUN] at hg
  obtain ⟨a, ha, b, hb, hab0⟩ := hg
  have hab : a * b = (g : G) := hab0
  refine ⟨1, Subtype.ext ?_⟩
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.sq_U a ha
  have hb2 : b * b = 1 := by simpa [pow_two] using hAs.sq_U b hb
  have hba : b * a = a * b := (hUU a ha b hb).symm
  have : (g : G) ^ 2 = 1 := by
    rw [← hab, pow_two]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  simpa using this

theorem le_normalizer_V (h : A3A3 H S L s) :
    conjJoin S L ≤ normalizer ((blockU L ⊔ blockU2 L s : Subgroup G) : Set G) := by
  have hA := h.isA4
  have hAs := h.isA4s
  have hUL : blockU L ≤ L := hA.le
  have hULs : blockU2 L s ≤ conjR L s := hAs.le
  rw [h.join]
  refine sup_le ?_ ?_
  · intro g hg
    exact C1.mem_normalizer_sup (C1.le_normalizer_blockU L hg)
      (C5.le_normalizer_of_commute (fun u hu a ha => h.comm_elem u hu a (hULs ha)) hg)
  · intro g hg
    have hgN : g ∈ normalizer (blockU2 L s : Set G) := by
      have := C5.conjSubgroup_mono (C1.le_normalizer_blockU L) s
      rw [C5.conjSubgroup_normalizer] at this
      exact this hg
    exact C1.mem_normalizer_sup
      (C5.le_normalizer_of_commute (fun u hu a ha => (h.comm_elem a (hUL ha) u hu).symm) hg) hgN

theorem isSylowTwoOf_V (h : A3A3 H S L s) :
    IsSylowTwoOf (blockU L ⊔ blockU2 L s) (conjJoin S L) := by
  have hA := h.isA4
  have hAs := h.isA4s
  have hUL : blockU L ≤ L := hA.le
  have hULs : blockU2 L s ≤ conjR L s := hAs.le
  have hUU : ∀ a ∈ blockU L, ∀ b ∈ blockU2 L s, a * b = b * a := fun a ha b hb =>
    h.comm_elem a (hUL ha) b (hULs hb)
  have hUN : blockU L ≤ normalizer (blockU2 L s : Set G) := C5.le_normalizer_of_commute hUU
  have hVL0 : blockU L ⊔ blockU2 L s ≤ conjJoin S L := by
    rw [h.join]; exact sup_le (hUL.trans le_sup_left) (hULs.trans le_sup_right)
  have hbot : blockU L ⊓ blockU2 L s = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hUL hULs).trans (le_of_eq h.inf_Ls))
  have hcardL0 : Nat.card ↥(conjJoin S L) = 144 := by
    rw [h.join]
    have := C5.card_sup_mul_card_inf_of_le_normalizer (C5.le_normalizer_of_commute h.comm_elem)
    rw [h.inf_Ls, Subgroup.card_bot, mul_one, hA.card_L, hAs.card_L] at this
    omega
  have hcardV : Nat.card ↥(blockU L ⊔ blockU2 L s) = 16 := by
    have := C5.card_sup_mul_card_inf_of_le_normalizer hUN
    rw [hbot, Subgroup.card_bot, mul_one, hA.card_U, hAs.card_U] at this
    omega
  refine ⟨hVL0, h.V_isPGroup, ?_⟩
  have hrel := C5.card_eq_card_mul_relIndex hVL0
  rw [hcardL0, hcardV] at hrel
  have hr : (blockU L ⊔ blockU2 L s).relIndex (conjJoin S L) = 9 := by omega
  show ¬ 2 ∣ (blockU L ⊔ blockU2 L s).relIndex (conjJoin S L)
  rw [hr]; omega

theorem blockU0_eq (h : A3A3 H S L s) (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L)) :
    blockU0 S L = blockU L ⊔ blockU2 L s := by
  have hVL0 : blockU L ⊔ blockU2 L s ≤ conjJoin S L := h.isSylowTwoOf_V.le
  have hVp : blockU L ⊔ blockU2 L s ≤ pCoreOf 2 (conjJoin S L) :=
    le_pCoreOf_of_normalizes hVL0 h.le_normalizer_V h.V_isPGroup
  have hle : pCoreOf 2 (conjJoin S L) ≤ blockU L ⊔ blockU2 L s :=
    h.isSylowTwoOf_V.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  rw [hU0]; exact le_antisymm hle hVp

theorem conjJoin_ne (h : A3A3 H S L s) : conjJoin S L ≠ L := by
  intro hj
  apply h.s_ne
  have hLs : conjR L s ≤ L := by
    calc conjR L s ≤ L ⊔ conjR L s := le_sup_right
      _ = conjJoin S L := h.join.symm
      _ = L := hj
  exact Subgroup.eq_of_le_of_card_ge hLs (C5.card_conjSubgroup L s).symm.le

theorem inf_S_L0 (h : A3A3 H S L s) (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hU0S : blockU0 S L ≤ S) : S ⊓ conjJoin S L = blockU0 S L := by
  have hsyl : IsSylowTwoOf (blockU0 S L) (conjJoin S L) := by
    rw [h.blockU0_eq hU0]; exact h.isSylowTwoOf_V
  have hL0 : blockU0 S L ≤ conjJoin S L := hsyl.le
  have h2 : IsPGroup 2 ↥(S ⊓ conjJoin S L) := h.cs.sylow.isPGroup.to_le inf_le_left
  exact hsyl.eq_of_le (le_inf hU0S hL0) inf_le_right h2

end A3A3

theorem exists_A3A3 (hcs : WGen H S L) (h3 : IsAltType L 3)
    (hne : conjJoin S L ≠ L) : ∃ s : G, A3A3 H S L s := by
  obtain ⟨t, htS, htne, htjoin, htcomm⟩ := hcs.blocks.resolve_left hne
  have hct : conjR L t⁻¹ = L.map (MulAut.conj t).toMonoidHom := by simp [conjR]
  exact ⟨t⁻¹, hcs, h3, S.inv_mem htS, by rw [hct]; exact htne, by rw [hct]; exact htjoin,
    by rw [hct]; exact htcomm⟩

end CFSG.Quasithin.YG.DoubleA3
