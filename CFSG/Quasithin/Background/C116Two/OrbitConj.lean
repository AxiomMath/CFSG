module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def orbitW (A L : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, blockU (conjByElt a L)

@[expose] noncomputable def orbitC (A L : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, blockZ (conjByElt a L)

@[expose] def orbitBlocks (A L : Subgroup G) : Set (Subgroup G) :=
  {L' | ∃ a ∈ A, L' = conjByElt a L}

theorem blockQ_conjByElt (a : G) (L : Subgroup G) :
    blockQ (conjByElt a L) = conjByElt a (blockQ L) := by
  unfold blockQ conjByElt
  exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj a) L

theorem blockU_conjByElt (a : G) (L : Subgroup G) :
    blockU (conjByElt a L) = conjByElt a (blockU L) := by
  unfold blockU
  rw [blockQ_conjByElt]
  unfold conjByElt
  rw [Subgroup.map_commutator]

theorem centralizer_conjByElt (a : G) (L : Subgroup G) :
    Subgroup.centralizer (conjByElt a L : Set G) =
      conjByElt a (Subgroup.centralizer (L : Set G)) := by
  ext x
  rw [mem_conjByElt, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [SetLike.mem_coe, mem_conjByElt]
  constructor
  · intro hyp h' hh'
    have hk : a⁻¹ * (a * h' * a⁻¹) * a ∈ L := by
      rw [show a⁻¹ * (a * h' * a⁻¹) * a = h' by group]
      exact hh'
    have hk2 := hyp (a * h' * a⁻¹) hk
    calc h' * (a⁻¹ * x * a) = a⁻¹ * (a * h' * a⁻¹ * x) * a := by group
      _ = a⁻¹ * (x * (a * h' * a⁻¹)) * a := by rw [hk2]
      _ = a⁻¹ * x * a * h' := by group
  · intro hyp h hh
    have hk := hyp (a⁻¹ * h * a) hh
    calc h * x = a * ((a⁻¹ * h * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * x * a) * (a⁻¹ * h * a)) * a⁻¹ := by rw [hk]
      _ = x * h := by group

theorem blockZ_conjByElt (a : G) (L : Subgroup G) :
    blockZ (conjByElt a L) = conjByElt a (blockZ L) := by
  have hinj : Function.Injective (MulAut.conj a).toMonoidHom := (MulAut.conj a).injective
  unfold blockZ
  rw [blockU_conjByElt, centralizer_conjByElt]
  unfold conjByElt
  rw [Subgroup.map_inf _ _ _ hinj]

theorem card_conjByElt (a : G) (K : Subgroup G) :
    Nat.card ↥(conjByElt a K) = Nat.card ↥K := by
  have hinj : Function.Injective (MulAut.conj a).toMonoidHom := (MulAut.conj a).injective
  unfold conjByElt
  exact Subgroup.card_map_of_injective hinj

theorem card_blockU_conjByElt (a : G) (L : Subgroup G) :
    Nat.card ↥(blockU (conjByElt a L)) = Nat.card ↥(blockU L) := by
  rw [blockU_conjByElt, card_conjByElt]

theorem card_blockZ_conjByElt (a : G) (L : Subgroup G) :
    Nat.card ↥(blockZ (conjByElt a L)) = Nat.card ↥(blockZ L) := by
  rw [blockZ_conjByElt, card_conjByElt]

theorem conjByElt_one (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  simp [mem_conjByElt]

theorem conjByElt_mul (b a : G) (K : Subgroup G) :
    conjByElt b (conjByElt a K) = conjByElt (b * a) K := by
  ext x
  simp only [mem_conjByElt, mul_inv_rev, mul_assoc]

theorem conjByElt_inv_conjByElt (a : G) (K : Subgroup G) :
    conjByElt a⁻¹ (conjByElt a K) = K := by
  rw [conjByElt_mul, inv_mul_cancel, conjByElt_one]

theorem conjByElt_mem_orbitBlocks {A : Subgroup G} {a : G} (ha : a ∈ A) (L : Subgroup G) :
    conjByElt a L ∈ orbitBlocks A L :=
  ⟨a, ha, rfl⟩

theorem orbitW_eq_iSup (A L : Subgroup G) :
    orbitW A L = ⨆ i : ↥(orbitBlocks A L), blockU (i : Subgroup G) := by
  apply le_antisymm
  · unfold orbitW
    refine iSup₂_le fun a ha => ?_
    exact le_iSup_of_le (⟨conjByElt a L, conjByElt_mem_orbitBlocks ha L⟩ : ↥(orbitBlocks A L))
      le_rfl
  · refine iSup_le fun i => ?_
    obtain ⟨a, ha, hi⟩ := i.2
    unfold orbitW
    exact le_iSup₂_of_le a ha (le_of_eq (congrArg blockU hi))

theorem orbitC_eq_iSup (A L : Subgroup G) :
    orbitC A L = ⨆ i : ↥(orbitBlocks A L), blockZ (i : Subgroup G) := by
  apply le_antisymm
  · unfold orbitC
    refine iSup₂_le fun a ha => ?_
    exact le_iSup_of_le (⟨conjByElt a L, conjByElt_mem_orbitBlocks ha L⟩ : ↥(orbitBlocks A L))
      le_rfl
  · refine iSup_le fun i => ?_
    obtain ⟨a, ha, hi⟩ := i.2
    unfold orbitC
    exact le_iSup₂_of_le a ha (le_of_eq (congrArg blockZ hi))

theorem blockU_le_left (L : Subgroup G) : blockU L ≤ L := by
  unfold blockU
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have hqL : q ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hq
  simp only [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hqL hl) (L.inv_mem hqL)) (L.inv_mem hl)

theorem blockU_le_orbitW (A L : Subgroup G) : blockU L ≤ orbitW A L := by
  unfold orbitW
  exact le_iSup₂_of_le (1 : G) A.one_mem (le_of_eq (by rw [conjByElt_one]))

theorem conjByElt_eq_self_iff_normalizer (g : G) (L : Subgroup G) :
    conjByElt g L = L ↔ g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hc x
    have key : g * x * g⁻¹ ∈ conjByElt g L ↔ x ∈ L := by
      rw [mem_conjByElt]
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]
    rw [hc] at key
    exact key.symm
  · intro hn
    ext x
    rw [mem_conjByElt]
    have h1 := hn (g⁻¹ * x * g)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h1
    exact h1

theorem conjByElt_eq_iff (a a' : G) (L : Subgroup G) :
    conjByElt a L = conjByElt a' L ↔ a'⁻¹ * a ∈ Subgroup.normalizer (L : Set G) := by
  rw [← conjByElt_eq_self_iff_normalizer (a'⁻¹ * a) L]
  constructor
  · intro h
    rw [← conjByElt_mul, h, conjByElt_mul, inv_mul_cancel, conjByElt_one]
  · intro h
    have h2 : conjByElt a' (conjByElt (a'⁻¹ * a) L) = conjByElt a' L := by rw [h]
    have e : a' * (a'⁻¹ * a) = a := by group
    rw [conjByElt_mul, e] at h2
    exact h2

theorem mem_subgroupOf_inf_normalizer_iff (A L : Subgroup G) (a b : ↥A) :
    a⁻¹ * b ∈ (A ⊓ Subgroup.normalizer (L : Set G)).subgroupOf A ↔
      conjByElt (a : G) L = conjByElt (b : G) L := by
  rw [conjByElt_eq_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · rintro ⟨-, h⟩
    have h' := (Subgroup.normalizer (L : Set G)).inv_mem h
    rwa [mul_inv_rev, inv_inv] at h'
  · intro h
    have h' := (Subgroup.normalizer (L : Set G)).inv_mem h
    rw [mul_inv_rev, inv_inv] at h'
    exact ⟨A.mul_mem (A.inv_mem a.2) b.2, h'⟩

theorem card_orbitBlocks (A L : Subgroup G) :
    Nat.card ↥(orbitBlocks A L) = (A ⊓ Subgroup.normalizer (L : Set G)).relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  let F : ↥A → ↥(orbitBlocks A L) :=
    fun a => ⟨conjByElt (a : G) L, conjByElt_mem_orbitBlocks a.2 L⟩
  let f : ↥A ⧸ ((A ⊓ Subgroup.normalizer (L : Set G)).subgroupOf A) → ↥(orbitBlocks A L) :=
    Quotient.lift F fun a b hab =>
      Subtype.ext ((mem_subgroupOf_inf_normalizer_iff A L a b).1 (QuotientGroup.leftRel_apply.1 hab))
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun i => ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have hab : conjByElt (a : G) L = conjByElt (b : G) L := congrArg Subtype.val hxy
      rw [QuotientGroup.eq]
      exact (mem_subgroupOf_inf_normalizer_iff A L a b).2 hab
    · obtain ⟨a, ha, hi⟩ := i.2
      exact ⟨QuotientGroup.mk (⟨a, ha⟩ : ↥A), Subtype.ext hi.symm⟩
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

end CFSG.Quasithin.C116Two
