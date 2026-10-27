module

public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.Q1327T.Transfer
import CFSG.RankThree.PartOne.Q1327S.Core

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem simple_nonab_of_model {K : Type} [Group K] {g : ℕ}
    (hmodel : StatedClassicalModel K .PSL 2 2 g) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a :=
  CFSG.RankThree.PartOne.Q1327S.simple_of_model hmodel

theorem inf_eq_bot_of_card_eq_prime {X : Type*} [Group X] [Finite X] {A B : Subgroup X} {q : ℕ}
    (hq : q.Prime) (hA : Nat.card A = q) (hB : Nat.card B = q) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  have hd : Nat.card ↥(A ⊓ B) ∣ q := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hq).1 hd with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    apply hne
    have e1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hA])
    have e2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hB])
    exact e1.symm.trans e2

variable {p g : ℕ} {Q : Type} [Group Q] [Finite Q] {Ē : Subgroup Q}

theorem Row8Conf.exists_T (h : Row8Conf p g Q Ē) :
    ∃ (c x : Q ⧸ Subgroup.center Q) (K : Subgroup (Q ⧸ Subgroup.center Q)),
      c ≠ 1 ∧ c ^ p = 1 ∧ K ≤ Subgroup.centralizer ({c} : Set (Q ⧸ Subgroup.center Q)) ∧
      StatedClassicalModel K .PSL 2 2 g ∧ x ∈ K ∧ orderOf x = p ∧
      IsElementaryAbelian p ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers x) ∧
      Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers x) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hEel := h.elem
  obtain ⟨c₀, hc₀E, hc₀1, Kb, x₀, hKbc, -, hmodel, hxK, hxo, hgen⟩ := h.conf
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hinj : ∀ e ∈ Ē, π e = 1 → e = 1 := by
    intro e he h1
    have hz : e ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff e).1 h1
    have hmem : e ∈ Ē ⊓ Subgroup.center Q := ⟨he, hz⟩
    rw [h.inf_center_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hxE : x₀ ∈ Ē := by
    rw [hgen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x₀)
  have hx1 : x₀ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hxo
    exact h.prime.ne_one hxo.symm
  obtain ⟨hKsimple, hKne⟩ := simple_nonab_of_model hmodel
  have hinjK : Function.Injective (π.subgroupMap Kb) :=
    injective_subgroupMap_of_simple Kb hKsimple hKne π (by
      rw [hπ, QuotientGroup.ker_mk']
      infer_instance)
  let eKK : ↥Kb ≃* ↥(Kb.map π) :=
    MulEquiv.ofBijective (π.subgroupMap Kb) ⟨hinjK, π.subgroupMap_surjective Kb⟩
  refine ⟨π c₀, π x₀, Kb.map π, fun h1 => hc₀1 (hinj c₀ hc₀E h1), ?_, ?_,
    Equivariance.statedClassicalModel_of_mulEquiv eKK hmodel,
    Subgroup.mem_map_of_mem _ hxK, ?_, ?_, ?_⟩
  · rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Ē) c₀ hc₀E, map_one]
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hKbc hk))
  · refine orderOf_eq_prime ?_ (fun h1 => hx1 (hinj x₀ hxE h1))
    rw [← map_pow]
    have : x₀ ^ p = 1 := by
      have := pow_orderOf_eq_one x₀
      rwa [hxo] at this
    rw [this, map_one]
  · have hEq : Subgroup.zpowers (π c₀) ⊔ Subgroup.zpowers (π x₀) = Ē.map π := by
      rw [hgen, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rw [hEq]
    exact IsElementaryAbelian.map π
  · have hEq : Subgroup.zpowers (π c₀) ⊔ Subgroup.zpowers (π x₀) = Ē.map π := by
      rw [hgen, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rw [hEq]
    have hinj' : Function.Injective (π.comp Ē.subtype) := by
      rw [injective_iff_map_eq_one]
      intro e he
      exact Subtype.ext (hinj e e.2 he)
    have hrange : Ē.map π = (π.comp Ē.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← h.card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm

end CFSG.RankThree.PartOne.Q1327T
