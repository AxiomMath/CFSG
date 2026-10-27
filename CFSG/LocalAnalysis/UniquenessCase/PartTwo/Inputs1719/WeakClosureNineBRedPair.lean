module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNRedKer
public import CFSG.Adapters.LieModelSimple
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.NG915

open Subgroup

variable {Z : Type*} [Group Z]

theorem map_conj_inv_eq {B C : Subgroup Z} {a : Z} (h : B.map (MulAut.conj a).toMonoidHom = C) :
    C.map (MulAut.conj a⁻¹).toMonoidHom = B := by
  rw [← h]
  exact CFSG.RankThree.map_conj_inv_map_conj B a

section FixSwap

variable {L1b L2b : Subgroup Z}

theorem fixSwap_mul {a b : Z}
    (ha : (L1b.map (MulAut.conj a).toMonoidHom = L1b ∧ L2b.map (MulAut.conj a).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj a).toMonoidHom = L2b ∧ L2b.map (MulAut.conj a).toMonoidHom = L1b))
    (hb : (L1b.map (MulAut.conj b).toMonoidHom = L1b ∧ L2b.map (MulAut.conj b).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj b).toMonoidHom = L2b ∧ L2b.map (MulAut.conj b).toMonoidHom = L1b)) :
    (L1b.map (MulAut.conj (a * b)).toMonoidHom = L1b ∧
        L2b.map (MulAut.conj (a * b)).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj (a * b)).toMonoidHom = L2b ∧
        L2b.map (MulAut.conj (a * b)).toMonoidHom = L1b) := by
  rw [CFSG.LieType.Chevalley.map_conj_mul, CFSG.LieType.Chevalley.map_conj_mul]
  rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> rw [hb1, hb2] <;>
    rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rw [ha1, ha2] <;> tauto

theorem fixSwap_inv {a : Z}
    (ha : (L1b.map (MulAut.conj a).toMonoidHom = L1b ∧ L2b.map (MulAut.conj a).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj a).toMonoidHom = L2b ∧ L2b.map (MulAut.conj a).toMonoidHom = L1b)) :
    (L1b.map (MulAut.conj a⁻¹).toMonoidHom = L1b ∧
        L2b.map (MulAut.conj a⁻¹).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj a⁻¹).toMonoidHom = L2b ∧
        L2b.map (MulAut.conj a⁻¹).toMonoidHom = L1b) := by
  rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
  · exact Or.inl ⟨map_conj_inv_eq ha1, map_conj_inv_eq ha2⟩
  · exact Or.inr ⟨map_conj_inv_eq ha2, map_conj_inv_eq ha1⟩

theorem fixSwap_of_mem_left (hcomm : ⁅L1b, L2b⁆ = ⊥) {l : Z} (hl : l ∈ L1b) :
    L1b.map (MulAut.conj l).toMonoidHom = L1b ∧ L2b.map (MulAut.conj l).toMonoidHom = L2b := by
  refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl), ?_⟩
  have hc : l ∈ centralizer (L2b : Set Z) := commutator_eq_bot_iff_le_centralizer.mp hcomm hl
  have hfix : ∀ y ∈ L2b, (MulAut.conj l).toMonoidHom y = y := fun y hy => by
    have h := mem_centralizer_iff.mp hc y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hfix y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem fixSwap_of_mem_right {Tb : Subgroup Z} (hne : L1b ≠ L2b) {t₀ : Z} (ht₀ : t₀ ∈ Tb)
    (hconj : L2b = L1b.map (MulAut.conj t₀).toMonoidHom)
    (hperm : ∀ t ∈ Tb, L1b.map (MulAut.conj t).toMonoidHom = L1b ∨
      L1b.map (MulAut.conj t).toMonoidHom = L2b) {t : Z} (ht : t ∈ Tb) :
    (L1b.map (MulAut.conj t).toMonoidHom = L1b ∧ L2b.map (MulAut.conj t).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj t).toMonoidHom = L2b ∧ L2b.map (MulAut.conj t).toMonoidHom = L1b) := by
  have h2 : L2b.map (MulAut.conj t).toMonoidHom = L1b ∨
      L2b.map (MulAut.conj t).toMonoidHom = L2b := by
    rw [hconj, ← CFSG.LieType.Chevalley.map_conj_mul, ← hconj]
    exact hperm _ (Tb.mul_mem ht ht₀)
  rcases hperm t ht with h1 | h1
  · refine Or.inl ⟨h1, h2.resolve_left fun h => hne ?_⟩
    exact Subgroup.map_injective (MulAut.conj t).injective (h1.trans h.symm)
  · refine Or.inr ⟨h1, h2.resolve_right fun h => hne ?_⟩
    exact Subgroup.map_injective (MulAut.conj t).injective (h1.trans h.symm)

theorem fixSwap_of_sup_eq_top {Tb : Subgroup Z} (hsup : L1b ⊔ Tb = ⊤)
    (hcomm : ⁅L1b, L2b⁆ = ⊥) (hne : L1b ≠ L2b) {t₀ : Z} (ht₀ : t₀ ∈ Tb)
    (hconj : L2b = L1b.map (MulAut.conj t₀).toMonoidHom)
    (hperm : ∀ t ∈ Tb, L1b.map (MulAut.conj t).toMonoidHom = L1b ∨
      L1b.map (MulAut.conj t).toMonoidHom = L2b) (z : Z) :
    (L1b.map (MulAut.conj z).toMonoidHom = L1b ∧ L2b.map (MulAut.conj z).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj z).toMonoidHom = L2b ∧ L2b.map (MulAut.conj z).toMonoidHom = L1b) := by
  let S : Subgroup Z :=
    { carrier := {z | (L1b.map (MulAut.conj z).toMonoidHom = L1b ∧
          L2b.map (MulAut.conj z).toMonoidHom = L2b) ∨
        (L1b.map (MulAut.conj z).toMonoidHom = L2b ∧ L2b.map (MulAut.conj z).toMonoidHom = L1b)}
      one_mem' := Or.inl ⟨by ext; simp, by ext; simp⟩
      mul_mem' := fun ha hb => fixSwap_mul ha hb
      inv_mem' := fun ha => fixSwap_inv ha }
  have hle : L1b ⊔ Tb ≤ S :=
    sup_le (fun l hl => Or.inl (fixSwap_of_mem_left hcomm hl))
      (fun t ht => fixSwap_of_mem_right hne ht₀ hconj hperm ht)
  rw [hsup] at hle
  exact hle (mem_top z)

theorem map_conj_eq_or_eq
    (hfs : ∀ z : Z, (L1b.map (MulAut.conj z).toMonoidHom = L1b ∧
        L2b.map (MulAut.conj z).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj z).toMonoidHom = L2b ∧ L2b.map (MulAut.conj z).toMonoidHom = L1b))
    (z : Z) {B : Subgroup Z} (hB : B = L1b ∨ B = L2b) :
    B.map (MulAut.conj z).toMonoidHom = L1b ∨ B.map (MulAut.conj z).toMonoidHom = L2b := by
  rcases hB with hB | hB <;> rw [hB]
  · rcases hfs z with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rcases hfs z with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2

theorem normal_sup_of_fixSwap
    (hfs : ∀ z : Z, (L1b.map (MulAut.conj z).toMonoidHom = L1b ∧
        L2b.map (MulAut.conj z).toMonoidHom = L2b) ∨
      (L1b.map (MulAut.conj z).toMonoidHom = L2b ∧ L2b.map (MulAut.conj z).toMonoidHom = L1b)) :
    (L1b ⊔ L2b).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : (L1b ⊔ L2b).map (MulAut.conj g).toMonoidHom = L1b ⊔ L2b := by
    rw [Subgroup.map_sup]
    rcases hfs g with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  rw [← h]
  exact ⟨n, hn, by simp⟩

end FixSwap

theorem centralizer_sup_eq_bot [Finite Z] {L1b L2b Tb : Subgroup Z} [(L1b ⊔ L2b).Normal]
    (hcomm : ⁅L1b, L2b⁆ = ⊥) (hZ1 : center L1b = ⊥) (hZ2 : center L2b = ⊥)
    (hTb : IsPGroup 2 Tb) (hsup : L1b ⊔ L2b ⊔ Tb = ⊤)
    (hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥) :
    centralizer ((L1b ⊔ L2b : Subgroup Z) : Set Z) = ⊥ := by
  have hle := NF914.centralizer_le_of_isPGroup_quotient hTb hsup hO2
  have hc12 : L1b ≤ centralizer (L2b : Set Z) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hn12 : L1b ≤ normalizer (L2b : Set Z) := hc12.trans (centralizer_le_normalizer _)
  have hcm : ∀ x ∈ L1b, ∀ y ∈ L2b, y * x = x * y := fun x hx y hy =>
    mem_centralizer_iff.mp (hc12 hx) y hy
  rw [eq_bot_iff]
  intro c hc
  have hc' : c ∈ ((L1b ⊔ L2b : Subgroup Z) : Set Z) := hle hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L1b L2b hn12] at hc'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hc'
  have hab : ∀ x ∈ L1b ⊔ L2b, x * (a * b) = a * b * x := fun x hx => mem_centralizer_iff.mp hc x hx
  have ha1 : a = 1 := by
    have hz : (⟨a, ha⟩ : L1b) ∈ center L1b := by
      rw [mem_center_iff]
      intro l
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have h1 := hab l (mem_sup_left l.2)
      have h2 := hcm l l.2 b hb
      calc (l : Z) * a = l * (a * b) * b⁻¹ := by group
        _ = a * b * l * b⁻¹ := by rw [h1]
        _ = a * (b * l) * b⁻¹ := by rw [mul_assoc a b]
        _ = a * (l * b) * b⁻¹ := by rw [h2]
        _ = a * l := by group
    rw [hZ1, mem_bot] at hz
    exact congrArg Subtype.val hz
  have hb1 : b = 1 := by
    have hz : (⟨b, hb⟩ : L2b) ∈ center L2b := by
      rw [mem_center_iff]
      intro m
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have h1 := hab m (mem_sup_right m.2)
      have h2 := hcm a ha m m.2
      calc (m : Z) * b = a⁻¹ * (a * m) * b := by group
        _ = a⁻¹ * (m * a) * b := by rw [h2]
        _ = a⁻¹ * (m * (a * b)) := by group
        _ = a⁻¹ * (a * b * m) := by rw [h1]
        _ = b * m := by group
    rw [hZ2, mem_bot] at hz
    exact congrArg Subtype.val hz
  rw [ha1, hb1, mul_one]
  exact one_mem _

theorem commutator_eq_bot_of_isComponent [Finite Z] {L1b L2b : Subgroup Z}
    (hcomp : CFSG.IsComponent L1b) {t₀ : Z} (hconj : L2b = L1b.map (MulAut.conj t₀).toMonoidHom)
    (hne : L1b ≠ L2b) : ⁅L1b, L2b⁆ = ⊥ := by
  subst hconj
  exact (CFSG.LocalCores.distinct_components_commute hcomp
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t₀) hcomp)).resolve_left hne

theorem centralizer_sup_eq_bot_of_isL3 {Y : Type} [Group Y] [Finite Y] {L1b L2b Tb : Subgroup Y}
    [(L1b ⊔ L2b).Normal] (hcomp : CFSG.IsComponent L1b) (hL3 : UC22.IsL3 ↥L1b 1) {t₀ : Y}
    (hconj : L2b = L1b.map (MulAut.conj t₀).toMonoidHom) (hcomm : ⁅L1b, L2b⁆ = ⊥)
    (hTb : IsPGroup 2 Tb) (hsup : L1b ⊔ L2b ⊔ Tb = ⊤)
    (hO2 : ∀ K : Subgroup Y, K.Normal → IsPGroup 2 K → K = ⊥) :
    centralizer ((L1b ⊔ L2b : Subgroup Y) : Set Y) = ⊥ := by
  have hs1 : IsSimpleGroup L1b :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  have hcomp2 : CFSG.IsComponent L2b := by
    rw [hconj]
    exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t₀) hcomp
  have hs2 : IsSimpleGroup L2b := by
    rw [hconj]
    exact (L1b.equivMapOfInjective _ (MulAut.conj t₀).injective).symm.isSimpleGroup
  exact centralizer_sup_eq_bot hcomm
    (CFSG.ComponentClassification.GSThmB.center_eq_bot_of_isSimpleGroup_of_isQuasisimple hcomp.1)
    (CFSG.ComponentClassification.GSThmB.center_eq_bot_of_isSimpleGroup_of_isQuasisimple
      hcomp2.1) hTb hsup hO2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.NG915
