module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Second

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
@[expose] def IsRootB (M B E : Subgroup G) : Prop := ∃ m ∈ M, E = conjSubgroup m B

omit [Finite G] in
structure IsClique101 (M Q Z B X : Subgroup G) : Prop where
  Z_le : Z ≤ X
  le_Q : X ≤ Q
  cover : ∀ x ∈ X, x ∉ Z → ∃ E, IsRootB M B E ∧ x ∈ E ∧ E ≤ X
  le_QB : ∀ E, IsRootB M B E → E ≤ X → X ≤ QB E

omit [Finite G] in
@[expose] def IsMaxClique101 (M Q Z B X : Subgroup G) : Prop :=
  IsClique101 M Q Z B X ∧ ∀ Y : Subgroup G, IsClique101 M Q Z B Y → Nat.card Y ≤ Nat.card X

omit [Finite G] in
@[expose] def IsSaturated101 (M Q Z B X : Subgroup G) : Prop :=
  ∀ C, IsRootB M B C → C ≤ X → ∀ D, IsRootB M B D → D ≤ Q ⊓ QB C → D ≤ X

omit [Finite G] in
theorem IsRootB.self : IsRootB M B B :=
  ⟨1, M.one_mem, (conjSubgroup_one B).symm⟩

omit [Finite G] in
theorem IsRootB.conj {E : Subgroup G} (hE : IsRootB M B E) {g : G} (hg : g ∈ M) :
    IsRootB M B (conjSubgroup g E) := by
  obtain ⟨m, hm, rfl⟩ := hE
  exact ⟨g * m, M.mul_mem hg hm, (conjSubgroup_mul g m B).symm⟩

omit [Finite G] in
theorem IsRootB.exists_conj {D E : Subgroup G} (hD : IsRootB M B D) (hE : IsRootB M B E) :
    ∃ g ∈ M, D = conjSubgroup g E := by
  obtain ⟨d, hd, rfl⟩ := hD
  obtain ⟨e, he, rfl⟩ := hE
  refine ⟨d * e⁻¹, M.mul_mem hd (M.inv_mem he), ?_⟩
  rw [← conjSubgroup_mul, inv_mul_cancel_right]

theorem Ctx.conj_sup_Z_of_mem_Q (hc : Ctx M Q Z B) {p : G} (hp : p ∈ Q) :
    conjSubgroup p (B ⊔ Z) = B ⊔ Z := by
  have hle : conjSubgroup p (B ⊔ Z) ≤ B ⊔ Z := by
    rw [conjSubgroup_sup', hc.conj_Z_eq (hc.hyp.Q_normal.1 hp)]
    refine sup_le (fun x hx => ?_) le_sup_right
    have hb : p⁻¹ * x * p ∈ B := mem_conjSubgroup.mp hx
    have hZ : ⁅p, p⁻¹ * x * p⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hp (hc.le hb)
    rw [show x = ⁅p, p⁻¹ * x * p⁆ * (p⁻¹ * x * p) by rw [commutatorElement_def]; group]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right hZ) (Subgroup.mem_sup_left hb)
  exact Subgroup.eq_of_le_of_card_ge hle (card_conjSubgroup p _).ge

theorem Ctx.conj_inf_QB_of_mem_Q (hc : Ctx M Q Z B) {p : G} (hp : p ∈ Q) :
    Q ⊓ QB (conjSubgroup p B) = Q ⊓ QB B := by
  have hle : conjSubgroup p (Q ⊓ QB B) ≤ Q ⊓ QB B := by
    intro x hx
    have hx' : p⁻¹ * x * p ∈ Q ⊓ QB B := mem_conjSubgroup.mp hx
    rw [show x = p * (p⁻¹ * x * p) * p⁻¹ by group]
    exact hc.conj_mem_inf hp hx'
  have heq := Subgroup.eq_of_le_of_card_ge hle (card_conjSubgroup p _).ge
  rw [QB_conj, ← hc.conj_Q_eq (hc.hyp.Q_normal.1 hp), ← conjSubgroup_inf,
    hc.conj_Q_eq (hc.hyp.Q_normal.1 hp), heq]

theorem IsRootB.ctx (hc : Ctx M Q Z B) {E : Subgroup G} (hE : IsRootB M B E) : Ctx M Q Z E := by
  obtain ⟨m, hm, rfl⟩ := hE
  exact hc.conj_of_mem hm

theorem IsRootB.sec10 {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {E : Subgroup G}
    (hE : IsRootB M B E) : Sec10Hyp (hE.ctx hc) n := by
  obtain ⟨m, hm, rfl⟩ := hE
  exact H.conj_of_mem hm

end CFSG.RankThree.GF2n.Stroth80
