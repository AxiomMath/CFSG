
module

public import CFSG.Sporadic.Schreier.J4SInvCheckBase
public import CFSG.Sporadic.Schreier.J4SProfileNodeBase
public import CFSG.Sporadic.Schreier.J4SLocalNodesBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SInvData
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.PairClasses
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ImagePairs

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

@[expose] def genElt (g : ℕ) : J := if g = 0 then vS else kgen (g - 1)

theorem genElt_mem {g : ℕ} (hg : g < 5) : genElt g ∈ S0 := by
  unfold genElt
  split_ifs with h
  · exact vS_mem_S0
  · exact kgen_mem_S0 ⟨g - 1, by omega⟩

section Generic

variable {G : Type*} [Group G]

theorem forest_conj_root (S : Subgroup G) (nf : ℕ → ℕ → G) (gen : ℕ → G)
    (fN fE fP fG : ℕ → ℕ) (gN : ℕ → ℕ → ℕ → ℕ) (gE : ℕ → ℕ → ℕ) (IsRoot : ℕ → Prop) (M : ℕ)
    (hgen : ∀ g < 5, gen g ∈ S)
    (hconj : ∀ g < 5, ∀ p < M,
      gen g * nf (fN p) (fE p) * (gen g)⁻¹ = nf (gN g (fN p) (fE p)) (gE g (fE p)))
    (hrec : ∀ j < M, (fP j = j ∧ IsRoot j) ∨ (fP j < j ∧ fG j < 5 ∧
      gN (fG j) (fN (fP j)) (fE (fP j)) = fN j ∧ gE (fG j) (fE (fP j)) = fE j)) :
    ∀ j < M, ∃ r < M, IsRoot r ∧ ∃ s ∈ S, s * nf (fN j) (fE j) * s⁻¹ = nf (fN r) (fE r) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases hrec j hj with ⟨-, hroot⟩ | ⟨hp, hg, hmapN, hmapE⟩
    · exact ⟨j, hj, hroot, 1, S.one_mem, by group⟩
    · obtain ⟨r, hr, hroot, s, hs, hconj'⟩ := ih (fP j) hp (hp.trans hj)
      have e1 := hconj (fG j) hg (fP j) (hp.trans hj)
      rw [hmapN, hmapE] at e1
      refine ⟨r, hr, hroot, s * (gen (fG j))⁻¹, S.mul_mem hs (S.inv_mem (hgen _ hg)), ?_⟩
      rw [← e1, ← hconj']
      group

theorem fusion_of_forest (S : Subgroup G) (nf : ℕ → ℕ → G) (gen : ℕ → G)
    (fN fE fP fG : ℕ → ℕ) (gN : ℕ → ℕ → ℕ → ℕ) (gE : ℕ → ℕ → ℕ) (IsRoot : ℕ → Prop) (M : ℕ)
    (T₁ T₂ : G) (hS : ∀ t : G, orderOf t = 2 → ∃ g : G, g * t * g⁻¹ ∈ S)
    (hnf : ∀ t ∈ S, orderOf t = 2 → ∃ j < M, t = nf (fN j) (fE j))
    (hgen : ∀ g < 5, gen g ∈ S)
    (hconj : ∀ g < 5, ∀ p < M,
      gen g * nf (fN p) (fE p) * (gen g)⁻¹ = nf (gN g (fN p) (fE p)) (gE g (fE p)))
    (hrec : ∀ j < M, (fP j = j ∧ IsRoot j) ∨ (fP j < j ∧ fG j < 5 ∧
      gN (fG j) (fN (fP j)) (fE (fP j)) = fN j ∧ gE (fG j) (fE (fP j)) = fE j))
    (hroot : ∀ r < M, IsRoot r →
      ∃ c : G, c * nf (fN r) (fE r) * c⁻¹ = T₁ ∨ c * nf (fN r) (fE r) * c⁻¹ = T₂)
    (t : G) (ht : orderOf t = 2) : ∃ g : G, g * t * g⁻¹ = T₁ ∨ g * t * g⁻¹ = T₂ := by
  obtain ⟨g₁, hg₁⟩ := hS t ht
  have ho : orderOf (g₁ * t * g₁⁻¹) = 2 := by
    rw [show g₁ * t * g₁⁻¹ = MulAut.conj g₁ t by rw [MulAut.conj_apply], MulEquiv.orderOf_eq, ht]
  obtain ⟨j, hj, hnfj⟩ := hnf _ hg₁ ho
  obtain ⟨r, hr, hroot', s, -, hs⟩ := forest_conj_root S nf gen fN fE fP fG gN gE IsRoot M hgen
    hconj hrec j hj
  obtain ⟨c, hc⟩ := hroot r hr hroot'
  refine ⟨c * s * g₁, ?_⟩
  have e1 : c * s * g₁ * t * (c * s * g₁)⁻¹ = c * (s * (g₁ * t * g₁⁻¹) * s⁻¹) * c⁻¹ := by group
  rw [e1, hnfj, hs]
  exact hc

end Generic

theorem ambIdx_spec {n e : ℕ} (h : ambIdx n e < 77) :
    (ambHead[ambIdx n e]!)[0]! = n ∧ (ambHead[ambIdx n e]!)[1]! = e := by
  unfold ambIdx at h ⊢
  cases hf : (List.range 77).find? (fun i => (ambHead[i]!)[0]! == n && (ambHead[i]!)[1]! == e)
    with
  | none => rw [hf, Option.getD_none] at h; omega
  | some i =>
    rw [Option.getD_some]
    have := List.find?_some hf
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at this
    exact this

theorem KPairs_eq {i : ℕ} (hi : i < 4) : KPairs[i]! = wordP Xn Yn fiveGenWords[i]! := by
  rw [KPairs, getElem!_pos _ i (by simpa using hi), List.getElem_toArray]
  interval_cases i
  · rw [List.getElem_cons_zero]
  · rw [List.getElem_cons_succ, List.getElem_cons_zero]
  · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_zero]
  · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
      List.getElem_cons_zero]

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {t : G} (ht : IsPGroup p (Subgroup.zpowers t)) :
    ∃ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := ht.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have h1 : (P : Subgroup G) = (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  rw [h1]
  exact ⟨t, hQ (Subgroup.mem_zpowers t), by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

end CFSG.Sporadic.J4Schreier
